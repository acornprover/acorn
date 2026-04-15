#!/usr/bin/env python3
"""
Analyze Firefox Profiler JSON output and produce text-based profiling summary.

Usage: python3 analyze_profile.py profile.json.gz

This parses the Firefox Profiler format (used by samply) and outputs:
- Top functions by self-time (time spent in the function itself)
- Top functions by inclusive time (time spent in function + callees)

When a .syms.json file exists alongside the profile (created with
samply --unstable-presymbolicate), it uses that for proper symbol names.
"""

import bisect
import gzip
import json
import sys
from collections import defaultdict
from pathlib import Path


def load_json(path: Path) -> dict:
    """Load a JSON file (gzip or plain)."""
    # Try gzip first
    try:
        with gzip.open(path, "rt", encoding="utf-8") as f:
            return json.load(f)
    except gzip.BadGzipFile:
        pass

    # Fall back to plain JSON
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def load_symbols(profile_path: Path) -> dict | None:
    """Load symbols file if it exists."""
    # Try profile.json.syms.json or profile.json.gz.syms.json
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


class Symbolizer:
    """Handles address-to-symbol resolution using the .syms.json file."""

    def __init__(self, syms_data: dict):
        self.string_table = syms_data.get("string_table", [])
        self.libs = {}

        # Build lookup structure for each library
        for lib in syms_data.get("data", []):
            debug_id = lib.get("debug_id", "")
            symbol_table = lib.get("symbol_table", [])

            # Sort symbols by rva for binary search
            sorted_symbols = sorted(symbol_table, key=lambda x: x.get("rva", 0))
            rvas = [s.get("rva", 0) for s in sorted_symbols]

            self.libs[debug_id] = {
                "name": lib.get("debug_name", "unknown"),
                "symbols": sorted_symbols,
                "rvas": rvas,
            }

    def get_symbol_name(self, debug_id: str, address: int) -> str | None:
        """Look up symbol name for an address in a library."""
        lib = self.libs.get(debug_id)
        if not lib:
            return None

        rvas = lib["rvas"]
        symbols = lib["symbols"]

        if not rvas:
            return None

        # Binary search for the symbol containing this address
        idx = bisect.bisect_right(rvas, address) - 1
        if idx < 0:
            return None

        sym = symbols[idx]
        sym_rva = sym.get("rva", 0)
        sym_size = sym.get("size", 0)

        # Check if address is within this symbol
        if sym_rva <= address < sym_rva + sym_size:
            sym_idx = sym.get("symbol", 0)
            if sym_idx < len(self.string_table):
                return self.string_table[sym_idx]

        return None


def normalize_debug_id(debug_id: str) -> str:
    """Normalize debug ID to uppercase without dashes or trailing 0."""
    # Remove dashes and convert to uppercase
    normalized = debug_id.upper().replace("-", "")
    # Remove trailing 0 if present (breakpad format has it, samply doesn't)
    if len(normalized) == 33 and normalized.endswith("0"):
        normalized = normalized[:-1]
    return normalized


def get_frame_name(thread: dict, frame_idx: int, profile: dict, symbolizer: Symbolizer | None) -> str:
    """Get the function name for a frame index."""
    frame_table = thread.get("frameTable", {})
    func_table = thread.get("funcTable", {})
    # Firefox profiler uses "stringArray" (newer format) or "stringTable" (older format)
    string_table = thread.get("stringArray", thread.get("stringTable", []))

    # Get the raw name and func_idx from profile
    raw_name = None
    func_idx = None
    if "func" in frame_table:
        func_indices = frame_table["func"]
        if frame_idx < len(func_indices):
            func_idx = func_indices[frame_idx]
            if "name" in func_table:
                name_indices = func_table["name"]
                if func_idx < len(name_indices):
                    name_idx = name_indices[func_idx]
                    if name_idx < len(string_table):
                        raw_name = string_table[name_idx]

    # If we have a symbolizer and the name looks like a hex address, try to resolve it
    if symbolizer and raw_name and raw_name.startswith("0x") and func_idx is not None:
        try:
            address = int(raw_name, 16)

            # Get the library info for this frame: func -> resource -> lib
            resource_indices = func_table.get("resource", [])
            resource_table = thread.get("resourceTable", {})
            lib_indices = resource_table.get("lib", [])
            libs = profile.get("libs", [])

            if func_idx < len(resource_indices):
                resource_idx = resource_indices[func_idx]
                if resource_idx is not None and resource_idx >= 0 and resource_idx < len(lib_indices):
                    lib_idx = lib_indices[resource_idx]
                    if lib_idx is not None and lib_idx >= 0 and lib_idx < len(libs):
                        lib_info = libs[lib_idx]
                        breakpad_id = lib_info.get("breakpadId", "")

                        if breakpad_id:
                            # Normalize the breakpad ID and find matching lib in symbolizer
                            normalized_id = normalize_debug_id(breakpad_id)
                            for lib_did in symbolizer.libs.keys():
                                if normalize_debug_id(lib_did) == normalized_id:
                                    sym_name = symbolizer.get_symbol_name(lib_did, address)
                                    if sym_name:
                                        return sym_name
                                    break
        except (ValueError, KeyError, IndexError):
            pass

    if raw_name:
        return raw_name

    return f"<frame {frame_idx}>"


def reconstruct_stack(thread: dict, stack_idx: int, profile: dict, symbolizer: Symbolizer | None) -> list:
    """Reconstruct full call stack from stack index.

    Returns list of function names from root to leaf.
    """
    stack_table = thread.get("stackTable", {})
    frame_indices = stack_table.get("frame", [])
    prefix_indices = stack_table.get("prefix", [])

    stack = []
    current = stack_idx

    # Follow prefix chain to reconstruct stack
    while current is not None and current >= 0:
        if current >= len(frame_indices):
            break
        frame_idx = frame_indices[current]
        func_name = get_frame_name(thread, frame_idx, profile, symbolizer)
        stack.append(func_name)

        if current >= len(prefix_indices):
            break
        current = prefix_indices[current]

    # Reverse to get root -> leaf order
    stack.reverse()
    return stack


def analyze_thread(thread: dict, profile: dict, symbolizer: Symbolizer | None) -> tuple:
    """Analyze a single thread's samples.

    Returns (self_time_counts, inclusive_time_counts, total_samples).
    """
    samples = thread.get("samples", {})
    stack_indices = samples.get("stack", [])
    weights = samples.get("weight", None)

    self_time = defaultdict(float)
    inclusive_time = defaultdict(float)
    total_weight = 0.0

    for i, stack_idx in enumerate(stack_indices):
        if stack_idx is None:
            continue

        weight = weights[i] if weights else 1.0
        if weight is None:
            weight = 1.0
        total_weight += weight

        stack = reconstruct_stack(thread, stack_idx, profile, symbolizer)
        if not stack:
            continue

        # Self time: only the leaf function
        self_time[stack[-1]] += weight

        # Inclusive time: all functions in the stack
        seen = set()
        for func in stack:
            if func not in seen:
                inclusive_time[func] += weight
                seen.add(func)

    return self_time, inclusive_time, total_weight


def analyze_profile(profile: dict, symbolizer: Symbolizer | None) -> tuple:
    """Analyze all threads in the profile.

    Returns (self_time_counts, inclusive_time_counts, total_samples).
    """
    total_self_time = defaultdict(float)
    total_inclusive_time = defaultdict(float)
    total_weight = 0.0

    threads = profile.get("threads", [])

    for thread in threads:
        thread_name = thread.get("name", "unknown")
        # Skip idle/system threads
        if thread_name in ("Gecko", "GeckoMain", "Compositor", "Timer"):
            continue

        self_time, inclusive_time, weight = analyze_thread(thread, profile, symbolizer)

        for func, time in self_time.items():
            total_self_time[func] += time
        for func, time in inclusive_time.items():
            total_inclusive_time[func] += time
        total_weight += weight

    return total_self_time, total_inclusive_time, total_weight


def format_results(
    self_time: dict,
    inclusive_time: dict,
    total: float,
    limit: int = 30,
    min_percent: float = 0.5,
) -> str:
    """Format results as text output."""
    if total == 0:
        return "No samples collected."

    lines = []

    # Self time
    lines.append("Top functions by self-time:")
    lines.append("-" * 70)
    sorted_self = sorted(self_time.items(), key=lambda x: -x[1])
    for func, time in sorted_self[:limit]:
        pct = 100.0 * time / total
        if pct < min_percent:
            break
        lines.append(f"  {pct:5.1f}%  {func}")

    lines.append("")

    # Inclusive time
    lines.append("Top functions by inclusive time:")
    lines.append("-" * 70)
    sorted_inclusive = sorted(inclusive_time.items(), key=lambda x: -x[1])
    for func, time in sorted_inclusive[:limit]:
        pct = 100.0 * time / total
        if pct < min_percent:
            break
        lines.append(f"  {pct:5.1f}%  {func}")

    lines.append("")
    lines.append(f"Total samples: {int(total)}")

    return "\n".join(lines)


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 analyze_profile.py <profile.json.gz>", file=sys.stderr)
        print("", file=sys.stderr)
        print("If a .syms.json file exists alongside the profile, it will be used", file=sys.stderr)
        print("for symbol resolution. Create it with: samply record --unstable-presymbolicate", file=sys.stderr)
        sys.exit(1)

    profile_path = Path(sys.argv[1])

    try:
        profile = load_json(profile_path)
    except Exception as e:
        print(f"Error loading profile: {e}", file=sys.stderr)
        sys.exit(1)

    # Try to load symbols file
    syms_data = load_symbols(profile_path)
    symbolizer = Symbolizer(syms_data) if syms_data else None

    if symbolizer:
        print(f"Using symbols from {profile_path}.syms.json", file=sys.stderr)

    self_time, inclusive_time, total = analyze_profile(profile, symbolizer)

    output = format_results(self_time, inclusive_time, total)
    print(output)


if __name__ == "__main__":
    main()
