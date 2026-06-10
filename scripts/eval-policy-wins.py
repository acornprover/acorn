#!/usr/bin/env python3
"""Summarize unique policy wins from an eval-suite run.

The eval suite runs every policy on the same benchmark-search universe. Each
policy log lists exactly the searches that timed out. From those failure sets we
can infer which searches each policy solved, without reading the much larger
trace files.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


FAILURE_RE = re.compile(r"^(?P<target>.+) could not be proved with skip=(?P<skip>\d+) \(.+\)$")
SEARCHES_RE = re.compile(r"^(?P<count>\d+) searches performed$")
SUCCEEDED_RE = re.compile(r"^(?P<ok>\d+)/(?P<total>\d+) benchmark searches succeeded$")
FAILURE_COUNT_RE = re.compile(r"^search failures: (?P<count>\d+) timeout$")


@dataclass(frozen=True)
class PolicyLog:
    policy: str
    path: Path
    total: int
    succeeded: int
    failures: frozenset[tuple[str, str]]
    reported_failures: int | None


def policy_name(path: Path) -> str:
    name = path.name
    if name.startswith("trace-") and name.endswith(".log"):
        return name[len("trace-") : -len(".log")]
    return path.stem


def parse_policy_log(path: Path) -> PolicyLog:
    policy = policy_name(path)
    failures: set[tuple[str, str]] = set()
    searches_performed: int | None = None
    succeeded: int | None = None
    succeeded_total: int | None = None
    reported_failures: int | None = None

    with path.open("r", encoding="utf-8") as f:
        for raw_line in f:
            line = raw_line.rstrip("\n")

            match = FAILURE_RE.match(line)
            if match:
                failures.add((match.group("target"), match.group("skip")))
                continue

            match = SEARCHES_RE.match(line)
            if match:
                searches_performed = int(match.group("count"))
                continue

            match = SUCCEEDED_RE.match(line)
            if match:
                succeeded = int(match.group("ok"))
                succeeded_total = int(match.group("total"))
                continue

            match = FAILURE_COUNT_RE.match(line)
            if match:
                reported_failures = int(match.group("count"))

    if searches_performed is None:
        raise ValueError(f"{path}: missing 'searches performed' line")
    if succeeded is None or succeeded_total is None:
        raise ValueError(f"{path}: missing benchmark success summary")
    if succeeded_total != searches_performed:
        raise ValueError(
            f"{path}: inconsistent totals: searches={searches_performed}, "
            f"success summary total={succeeded_total}"
        )
    if searches_performed - succeeded != len(failures):
        raise ValueError(
            f"{path}: parsed {len(failures)} failures, but summary implies "
            f"{searches_performed - succeeded}"
        )
    if reported_failures is not None and reported_failures != len(failures):
        raise ValueError(
            f"{path}: parsed {len(failures)} failures, but reported "
            f"{reported_failures}"
        )

    return PolicyLog(
        policy=policy,
        path=path,
        total=searches_performed,
        succeeded=succeeded,
        failures=frozenset(failures),
        reported_failures=reported_failures,
    )


def resolve_logs(paths: list[str]) -> list[Path]:
    if not paths:
        paths = ["tmp/acorn-eval-latest"]

    log_paths: list[Path] = []
    for raw_path in paths:
        path = Path(raw_path)
        if path.is_dir():
            logs_dir = path / "logs"
            if logs_dir.is_dir():
                log_paths.extend(sorted(logs_dir.glob("trace-*.log")))
            else:
                log_paths.extend(sorted(path.glob("trace-*.log")))
        else:
            log_paths.append(path)

    return log_paths


def pct(numerator: int, denominator: int) -> str:
    if denominator == 0:
        return "n/a"
    return f"{100.0 * numerator / denominator:.2f}%"


def print_table(rows: list[list[str]]) -> None:
    widths = [max(len(row[i]) for row in rows) for i in range(len(rows[0]))]
    for i, row in enumerate(rows):
        print("  ".join(cell.rjust(widths[j]) if j else cell.ljust(widths[j]) for j, cell in enumerate(row)))
        if i == 0:
            print("  ".join("-" * width for width in widths))


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Calculate policy success, unique wins, and overlap from eval-suite logs. "
            "By default, reads tmp/acorn-eval-latest."
        )
    )
    parser.add_argument(
        "paths",
        nargs="*",
        help="Eval suite directory, logs directory, or individual trace-*.log files.",
    )
    parser.add_argument(
        "--examples",
        type=int,
        default=0,
        help="Print up to N example unique wins per policy.",
    )
    args = parser.parse_args()

    log_paths = resolve_logs(args.paths)
    if not log_paths:
        print("No trace-*.log files found.", file=sys.stderr)
        return 1

    logs = [parse_policy_log(path) for path in log_paths]
    logs.sort(key=lambda log: log.policy)

    totals = {log.total for log in logs}
    if len(totals) != 1:
        for log in logs:
            print(f"{log.policy}: {log.total} searches", file=sys.stderr)
        print("Policy logs do not have the same search universe.", file=sys.stderr)
        return 1
    total = totals.pop()

    all_failures = set.intersection(*(set(log.failures) for log in logs))
    any_failure = set.union(*(set(log.failures) for log in logs))
    solved_by_any = total - len(all_failures)
    solved_by_all = total - len(any_failure)

    rows = [
        [
            "policy",
            "succeeded",
            "success %",
            "unique wins",
            "unique % all",
            "unique % successes",
            "failures",
        ]
    ]

    unique_by_policy: dict[str, set[tuple[str, str]]] = {}
    for log in logs:
        other_logs = [other for other in logs if other.policy != log.policy]
        if other_logs:
            failed_by_all_others = set.intersection(*(set(other.failures) for other in other_logs))
        else:
            failed_by_all_others = set()
        unique_wins = failed_by_all_others - set(log.failures)
        unique_by_policy[log.policy] = unique_wins
        rows.append(
            [
                log.policy,
                f"{log.succeeded}/{total}",
                pct(log.succeeded, total),
                str(len(unique_wins)),
                pct(len(unique_wins), total),
                pct(len(unique_wins), log.succeeded),
                str(len(log.failures)),
            ]
        )

    print(f"Policies: {', '.join(log.policy for log in logs)}")
    print(f"Searches: {total}")
    print(f"Solved by any policy: {solved_by_any}/{total} ({pct(solved_by_any, total)})")
    print(f"Solved by all policies: {solved_by_all}/{total} ({pct(solved_by_all, total)})")
    print(f"Solved by no policy: {len(all_failures)}/{total} ({pct(len(all_failures), total)})")
    print()
    print_table(rows)

    if args.examples > 0:
        print()
        for policy in sorted(unique_by_policy):
            examples = sorted(unique_by_policy[policy])[: args.examples]
            if not examples:
                continue
            print(f"{policy} unique examples:")
            for target, skip in examples:
                print(f"  {target} skip={skip}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
