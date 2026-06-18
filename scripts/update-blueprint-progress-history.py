#!/usr/bin/env python3
"""Update Blueprint progress history from a rendered docs site.

The script reads a previous history JSON when one exists, computes the current
snapshot from rendered Blueprint manifests, merges that snapshot by commit, and
writes the merged JSON for the deployable site. Normal renders use --output;
--write-history is only for explicitly updating the input history file too.
"""

import argparse
import importlib.util
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


DEFAULT_HISTORY = Path("docs/blueprint-progress-history.json")
DEFAULT_SITE_DIR = Path("_out/site/html-multi")
DEFAULT_DOCS_DIR = Path("docs/SecureMessagingDocs")
DEFAULT_PROJECT_END = "2027-01-28"
SCHEMA_VERSION = 1


def load_aggregator():
    # Import the status aggregator next to this script without requiring a package.
    script = Path(__file__).with_name("aggregate-blueprint-status.py")
    spec = importlib.util.spec_from_file_location("aggregate_blueprint_status", script)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {script}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def git_output(args: list[str], fallback: str = "") -> str:
    # Run a git command and return a fallback if the command fails.
    try:
        return subprocess.check_output(["git", *args], text=True).strip()
    except (subprocess.CalledProcessError, OSError):
        return fallback


def load_history_document(path: Path) -> dict:
    # Missing history is valid: the render will start from the current snapshot.
    if not path.exists():
        return {"snapshots": []}
    try:
        data = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        return {"snapshots": []}
    # Accept a bare snapshot list as a minimal history document.
    if isinstance(data, list):
        return {"snapshots": data}
    return data if isinstance(data, dict) else {"snapshots": []}


def snapshot_date(commit: str | None, explicit_date: str | None) -> str:
    # Resolve the snapshot date from an override, git metadata, or the current time.
    if explicit_date:
        return explicit_date
    if commit:
        date = git_output(["show", "-s", "--format=%cI", commit])
        if date:
            return date
    return datetime.now(timezone.utc).isoformat()


def current_snapshot(site_dir: Path, docs_dir: Path, commit: str | None, date: str | None, subject: str | None) -> dict:
    aggregator = load_aggregator()
    atoms = aggregator.load_tracked_atoms(site_dir, docs_dir)
    totals = aggregator.summarize(atoms)
    # CI normally records the checked-out commit; overrides are useful for recovery.
    resolved_commit = commit or git_output(["rev-parse", "HEAD"], "working-tree")
    resolved_subject = subject or git_output(["show", "-s", "--format=%s", resolved_commit], "Working tree")
    return {
        "commit": resolved_commit,
        "shortCommit": resolved_commit[:7],
        "date": snapshot_date(resolved_commit, date),
        "subject": resolved_subject,
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


def sort_key(snapshot: dict) -> tuple[str, str]:
    # Sort snapshots deterministically by date, then commit.
    return (snapshot.get("date", ""), snapshot.get("commit", ""))


def merge_history(existing: dict, snapshot: dict) -> dict:
    # Key by commit so repeated renders replace the current snapshot instead of duplicating it.
    by_commit: dict[str, dict] = {}
    for entry in existing.get("snapshots", []):
        if not isinstance(entry, dict):
            continue
        commit = entry.get("commit")
        if isinstance(commit, str) and commit:
            by_commit[commit] = entry
    by_commit[snapshot["commit"]] = snapshot
    merged = {
        "schemaVersion": SCHEMA_VERSION,
        "projectEnd": existing.get("projectEnd", DEFAULT_PROJECT_END),
        "updatedAt": datetime.now(timezone.utc).isoformat(),
        "snapshots": sorted(by_commit.values(), key=sort_key),
    }
    for key in ("projectStart", "historyBasis"):
        if key in existing:
            merged[key] = existing[key]
    return merged


def write_json(path: Path, data: dict) -> None:
    # Write stable, pretty JSON for artifacts and optional local recovery files.
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def main() -> None:
    # Parse CLI options, merge the current snapshot, and write or print the result.
    parser = argparse.ArgumentParser(description="Update Blueprint progress history from a rendered site.")
    parser.add_argument("--site-dir", type=Path, default=DEFAULT_SITE_DIR)
    parser.add_argument("--docs-dir", type=Path, default=DEFAULT_DOCS_DIR)
    parser.add_argument("--history", type=Path, default=DEFAULT_HISTORY)
    parser.add_argument("--output", type=Path, help="Write the merged history to this path.")
    parser.add_argument("--write-history", action="store_true", help="Also update the input history file.")
    parser.add_argument("--commit", help="Commit SHA for the new snapshot; defaults to HEAD.")
    parser.add_argument("--date", help="ISO-8601 date for the new snapshot; defaults to the commit date.")
    parser.add_argument("--subject", help="Commit subject for the new snapshot; defaults to git metadata.")
    args = parser.parse_args()

    snapshot = current_snapshot(args.site_dir, args.docs_dir, args.commit, args.date, args.subject)
    merged = merge_history(load_history_document(args.history), snapshot)

    if args.write_history:
        write_json(args.history, merged)
    if args.output:
        write_json(args.output, merged)
    if not args.write_history and not args.output:
        print(json.dumps(merged, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()