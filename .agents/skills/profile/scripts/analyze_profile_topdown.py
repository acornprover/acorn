#!/usr/bin/env python3
"""
Generate a top-down call tree from a Firefox Profiler JSON file.

Usage: python3 analyze_profile_topdown.py profile.json.gz

This produces a tree showing where time is spent, drilling down into
any component that accounts for >= 10% of total time.
"""

import json
import gzip
import sys
from collections import defaultdict
from pathlib import Path


def load_json(path: Path) -> dict:
    """Load a JSON file (gzip or plain)."""
    try:
        with gzip.open(path, "rt", encoding="utf-8") as f:
            return json.load(f)
    except gzip.BadGzipFile:
        pass
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def load_symbols(profile_path: Path) -> dict | None:
    """Load symbols file if it exists."""
    syms_path = Path(str(profile_path) + ".syms.json")
    if not syms_path.exists():
        base = str(profile_path)
        if base.endswith(".gz"):
            syms_path = Path(base[:-3] + ".syms.json")
    if syms_path.exists():
        try:
            with open(syms_path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return None


def build_symbol_lookup(syms: dict) -> dict:
    """Build (debug_id, address) -> symbol_name lookup."""
    if not syms:
        return {}
    string_table = syms.get("string_table", [])
    lookup = {}
    for lib in syms.get("data", []):
        debug_id = lib.get("debug_id", "").upper().replace("-", "")
        for sym in lib.get("symbol_table", []):
            rva = sym.get("rva", 0)
            size = sym.get("size", 1)
            name_idx = sym.get("symbol", 0)
            if name_idx < len(string_table):
                # Store for range (limit to prevent huge ranges)
                for addr in range(rva, min(rva + size, rva + 50000)):
                    lookup[(debug_id, addr)] = string_table[name_idx]
    return lookup


def extract_stacks(profile: dict, sym_lookup: dict) -> list:
    """Extract all call stacks from the profile."""
    thread = profile["threads"][0]
    samples = thread.get("samples", {})
    stack_indices = samples.get("stack", [])
    stack_table = thread.get("stackTable", {})
    frame_indices_st = stack_table.get("frame", [])
    prefix_indices = stack_table.get("prefix", [])
    frame_table = thread.get("frameTable", {})
    func_indices_ft = frame_table.get("func", [])
    func_table = thread.get("funcTable", {})
    name_indices = func_table.get("name", [])
    resource_indices = func_table.get("resource", [])
    resource_table = thread.get("resourceTable", {})
    lib_indices = resource_table.get("lib", [])
    strings = thread.get("stringArray", [])
    libs = profile.get("libs", [])

    def get_func_name(frame_idx):
        if frame_idx >= len(func_indices_ft):
            return "?"
        func_idx = func_indices_ft[frame_idx]
        if func_idx >= len(name_indices):
            return "?"
        name_idx = name_indices[func_idx]
        raw_name = strings[name_idx] if name_idx < len(strings) else "?"

        # Try to resolve hex address using symbols
        if raw_name.startswith("0x") and sym_lookup:
            try:
                addr = int(raw_name, 16)
                if func_idx < len(resource_indices):
                    res_idx = resource_indices[func_idx]
                    if res_idx is not None and res_idx >= 0 and res_idx < len(lib_indices):
                        lib_idx = lib_indices[res_idx]
                        if lib_idx is not None and lib_idx >= 0 and lib_idx < len(libs):
                            lib_info = libs[lib_idx]
                            breakpad_id = lib_info.get("breakpadId", "").upper().replace("-", "")
                            if breakpad_id.endswith("0") and len(breakpad_id) == 33:
                                breakpad_id = breakpad_id[:-1]
                            if (breakpad_id, addr) in sym_lookup:
                                return sym_lookup[(breakpad_id, addr)]
            except (ValueError, KeyError, IndexError):
                pass
        return raw_name

    all_stacks = []
    for stack_idx in stack_indices:
        if stack_idx is None:
            continue
        stack = []
        current = stack_idx
        while current is not None and current >= 0:
            if current >= len(frame_indices_st):
                break
            frame_idx = frame_indices_st[current]
            name = get_func_name(frame_idx)
            stack.append(name)
            current = prefix_indices[current] if current < len(prefix_indices) else None
        stack.reverse()
        all_stacks.append(stack)

    return all_stacks


def simplify_name(name: str) -> str:
    """Simplify a Rust function name for display."""
    if "::" in name:
        parts = name.split("::")
        # Look for known module names
        for i, p in enumerate(parts):
            if p in ("acorn", "alloc", "core", "std"):
                if i + 2 < len(parts):
                    return parts[i + 1] + "::" + parts[i + 2]
        return "::".join(parts[-2:])
    return name


def categorize_sample(stack: list) -> list:
    """Categorize a stack into a list of logical phases."""
    # Key functions that represent logical phases
    key_patterns = [
        ("Verifier::run", "Verifier::run"),
        ("Verifier::new", "Verifier::new"),
        ("Builder::build", "Builder::build"),
        ("Builder::verify_module", "Builder::verify_module"),
        ("Builder::verify_node", "Builder::verify_node"),
        ("verify_goal", "verify_goal"),
        ("Processor::check_cert", "Processor::check_cert"),
        ("Processor::add_fact", "Processor::add_fact"),
        ("Checker::check_cert", "Checker::check_cert"),
        ("Checker::check_concrete_proof", "Checker::check_concrete_proof"),
        ("Checker::insert_clause", "Checker::insert_clause"),
        ("Checker::insert_goal", "Checker::insert_goal"),
        ("Certificate::to_concrete_proof", "Certificate::to_concrete_proof"),
        ("Normalizer::normalize", "Normalizer::normalize"),
        ("Normalizer::denormalize", "Normalizer::denormalize"),
        ("make_mut", "Rc::make_mut"),
        ("drop_slow", "Rc::drop_slow"),
        ("Clone>::clone", "cloning"),
    ]

    result = []
    for name in stack:
        for pattern, label in key_patterns:
            if pattern in name:
                if not result or result[-1] != label:
                    result.append(label)
                break
    return result


def build_tree(all_stacks: list, total: int, min_pct: float = 5.0) -> list:
    """Build a tree structure from categorized stacks."""

    def get_children(parent_path: list) -> dict:
        """Get direct children counts for a given path."""
        children = defaultdict(int)
        parent_len = len(parent_path)

        for stack in all_stacks:
            cat = categorize_sample(stack)
            # Check if this stack matches the parent path
            if len(cat) > parent_len and cat[:parent_len] == parent_path:
                child = cat[parent_len]
                children[child] += 1

        return children

    def build_subtree(path: list, prefix: str) -> list:
        """Recursively build tree lines with box-drawing characters."""
        lines = []
        children = get_children(path)

        # Filter and sort by count descending
        visible_children = [(c, cnt) for c, cnt in children.items() if 100.0 * cnt / total >= min_pct]
        visible_children.sort(key=lambda x: -x[1])

        for i, (child, count) in enumerate(visible_children):
            pct = 100.0 * count / total
            is_last = i == len(visible_children) - 1

            # Connector for this line
            connector = "└── " if is_last else "├── "
            lines.append(f"{prefix}{connector}{pct:3.0f}%  {child}")

            # Recurse if >= 10%
            if pct >= 10:
                child_path = path + [child]
                # Prefix for children: add vertical line if not last, else spaces
                child_prefix = prefix + ("    " if is_last else "│   ")
                child_lines = build_subtree(child_path, child_prefix)
                lines.extend(child_lines)

        return lines

    return build_subtree([], "")


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 analyze_profile_topdown.py <profile.json.gz>", file=sys.stderr)
        sys.exit(1)

    profile_path = Path(sys.argv[1])

    try:
        profile = load_json(profile_path)
    except Exception as e:
        print(f"Error loading profile: {e}", file=sys.stderr)
        sys.exit(1)

    syms = load_symbols(profile_path)
    sym_lookup = build_symbol_lookup(syms)

    if syms:
        print(f"Using symbols from {profile_path}.syms.json", file=sys.stderr)

    all_stacks = extract_stacks(profile, sym_lookup)
    total = len(all_stacks)

    print(f"Total samples: {total}")
    print()
    print("Top-Down Breakdown")
    print("=" * 60)
    print()

    lines = build_tree(all_stacks, total)
    for line in lines:
        print(line)


if __name__ == "__main__":
    main()
