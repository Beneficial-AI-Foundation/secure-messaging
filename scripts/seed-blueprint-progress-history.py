#!/usr/bin/env python3
"""Seed Blueprint progress history from current atom issues and git commits.

Historical points are estimates: an atom is counted as complete at a commit when
one of its linked GitHub issues had been closed by that commit date. The latest
point is replaced with exact status from the rendered Blueprint manifests.

This is a recovery tool for rebuilding history when no deployed artifact exists.
"""

import argparse
import importlib.util
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


DEFAULT_DOCS_DIR = Path("docs/SecureMessagingDocs")
DEFAULT_HISTORY = Path("docs/blueprint-progress-history.json")
DEFAULT_SITE_DIR = Path("_out/site/html-multi")
DEFAULT_REPO = "Beneficial-AI-Foundation/secure-messaging"
SCHEMA_VERSION = 1

ATOM_RE = re.compile(r":{3,}(definition|theorem)\s+\"([^\"]+)\"")
ISSUE_RE = re.compile(r"\{githubIssue\s+(\d+)\}")


@dataclass(frozen=True)
class AtomIssue:
    kind: str
    label: str
    issues: tuple[int, ...]


@dataclass(frozen=True)
class Commit:
    sha: str
    date: datetime
    raw_date: str
    subject: str


def parse_datetime(raw_date: str | None) -> datetime | None:
    if not raw_date:
        return None
    try:
        parsed = datetime.fromisoformat(raw_date.replace("Z", "+00:00"))
        return parsed if parsed.tzinfo is not None else parsed.replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def add_months(date: datetime, months: int) -> datetime:
    import calendar

    month_index = date.month - 1 + months
    year = date.year + month_index // 12
    month = month_index % 12 + 1
    day = min(date.day, calendar.monthrange(year, month)[1])
    return date.replace(year=year, month=month, day=day)


def run_git(args: list[str]) -> str:
    return subprocess.check_output(["git", *args], text=True).strip()


def load_aggregator():
    script = Path(__file__).with_name("aggregate-blueprint-status.py")
    spec = importlib.util.spec_from_file_location("aggregate_blueprint_status", script)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {script}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def parse_atom_issues(docs_dir: Path) -> list[AtomIssue]:
    atoms: list[AtomIssue] = []
    for path in sorted(docs_dir.rglob("*.lean")):
        lines = path.read_text().splitlines()
        index = 0
        while index < len(lines):
            match = ATOM_RE.search(lines[index])
            if match is None:
                index += 1
                continue

            kind, label = match.group(1), match.group(2)
            close_marker = "::::" if lines[index].lstrip().startswith("::::") else ":::"
            block = [lines[index]]
            index += 1
            while index < len(lines):
                block.append(lines[index])
                if lines[index].strip() == close_marker:
                    index += 1
                    break
                index += 1

            issues = tuple(sorted({int(issue) for issue in ISSUE_RE.findall("\n".join(block))}))
            atoms.append(AtomIssue(kind=kind, label=label, issues=issues))
    return atoms


def fetch_issues(repo: str, issues_json: Path | None) -> dict[int, dict]:
    if issues_json is not None:
        items = json.loads(issues_json.read_text())
    else:
        output = subprocess.check_output(
            [
                "gh",
                "issue",
                "list",
                "--repo",
                repo,
                "--state",
                "all",
                "--limit",
                "300",
                "--json",
                "number,title,state,createdAt,closedAt",
            ],
            text=True,
        )
        items = json.loads(output)
    return {int(item["number"]): item for item in items}


def load_commits() -> list[Commit]:
    output = run_git(["log", "--reverse", "--format=%H%x09%cI%x09%s"])
    commits: list[Commit] = []
    for line in output.splitlines():
        sha, raw_date, subject = line.split("\t", 2)
        parsed = parse_datetime(raw_date)
        if parsed is None:
            continue
        commits.append(Commit(sha=sha, date=parsed, raw_date=raw_date, subject=subject))
    return commits


def issue_closed_by(issues: tuple[int, ...], metadata: dict[int, dict], date: datetime) -> bool:
    for issue in issues:
        closed_at = parse_datetime(metadata.get(issue, {}).get("closedAt"))
        if closed_at is not None and closed_at <= date:
            return True
    return False


def estimated_snapshot(commit: Commit, atoms: list[AtomIssue], issues: dict[int, dict], totals: dict) -> dict:
    definition_specified = 0
    theorem_complete = 0
    for atom in atoms:
        if not atom.issues or not issue_closed_by(atom.issues, issues, commit.date):
            continue
        if atom.kind == "definition":
            definition_specified += 1
        elif atom.kind == "theorem":
            theorem_complete += 1

    return {
        "commit": commit.sha,
        "shortCommit": commit.sha[:7],
        "date": commit.raw_date,
        "subject": commit.subject,
        "source": "github-issue-closure-estimate",
        "estimated": True,
        "definitions": {
            "total": totals["definition"]["total"],
            "specified": definition_specified,
        },
        "theorems": {
            "total": totals["theorem"]["total"],
            "specified": theorem_complete,
            "verified": theorem_complete,
        },
    }


def exact_snapshot(site_dir: Path) -> dict:
    aggregator = load_aggregator()
    atoms = aggregator.load_atoms(site_dir)
    totals = aggregator.summarize(atoms)
    commit = run_git(["rev-parse", "HEAD"])
    date = run_git(["show", "-s", "--format=%cI", commit])
    subject = run_git(["show", "-s", "--format=%s", commit])
    return {
        "commit": commit,
        "shortCommit": commit[:7],
        "date": date,
        "subject": subject,
        "source": "rendered-blueprint-manifest",
        "estimated": False,
        "definitions": {
            "total": totals["definition"]["total"],
            "specified": totals["definition"]["specified"],
        },
        "theorems": {
            "total": totals["theorem"]["total"],
            "specified": totals["theorem"]["specified"],
            "verified": totals["theorem"]["verified"],
        },
    }


def exact_totals(site_dir: Path) -> dict:
    aggregator = load_aggregator()
    totals = aggregator.summarize(aggregator.load_atoms(site_dir))
    return {
        "definition": {
            "total": totals["definition"]["total"],
        },
        "theorem": {
            "total": totals["theorem"]["total"],
        },
    }


def write_json(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description="Seed Blueprint progress history from issue closure estimates.")
    parser.add_argument("--docs-dir", type=Path, default=DEFAULT_DOCS_DIR)
    parser.add_argument("--site-dir", type=Path, default=DEFAULT_SITE_DIR)
    parser.add_argument("--history", type=Path, default=DEFAULT_HISTORY)
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--issues-json", type=Path, help="Use a cached gh issue list JSON file.")
    parser.add_argument("--months", type=int, default=6, help="Chart horizon in months from the first commit.")
    args = parser.parse_args()

    commits = load_commits()
    if not commits:
        raise SystemExit("no git commits found")

    atoms = parse_atom_issues(args.docs_dir)
    issues = fetch_issues(args.repo, args.issues_json)
    totals = exact_totals(args.site_dir)
    snapshots = [estimated_snapshot(commit, atoms, issues, totals) for commit in commits]
    latest = exact_snapshot(args.site_dir)

    by_commit = {snapshot["commit"]: snapshot for snapshot in snapshots}
    by_commit[latest["commit"]] = latest
    ordered = sorted(by_commit.values(), key=lambda snapshot: snapshot.get("date", ""))

    project_start = commits[0].raw_date
    project_end = add_months(commits[0].date, args.months).isoformat()
    data = {
        "schemaVersion": SCHEMA_VERSION,
        "projectStart": project_start,
        "projectEnd": project_end,
        "historyBasis": "Historical points are estimated from current Blueprint atom-to-issue links and GitHub issue closure dates; the latest point is exact from rendered Blueprint manifests.",
        "updatedAt": datetime.now(timezone.utc).isoformat(),
        "snapshots": ordered,
    }
    write_json(args.history, data)


if __name__ == "__main__":
    main()