#!/usr/bin/env python3
"""Append-only command and manual-span timing for the Frodo PR workflow."""
import argparse
import datetime
import fcntl
import json
import os
from pathlib import Path
import resource
import subprocess
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
DEFAULT = ROOT / '.formalising/fv-plans/FrodoPKE-and-FrodoKEM/timing/events.jsonl'


def append(path, event):
    path.parent.mkdir(parents=True, exist_ok=True)
    event['utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    event['timestamp'] = time.time()
    with path.open('a') as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        stream.write(json.dumps(event) + '\n')
        stream.flush()


def union_seconds(intervals):
    total = 0.0
    end = float('-inf')
    for start, stop in sorted(intervals):
        total += max(0, stop - max(start, end))
        end = max(end, stop)
    return total


def report(path):
    events = [json.loads(line) for line in path.read_text().splitlines() if line]
    starts = {e['id']: e for e in events if e['event'] == 'start'}
    stops = {e['id']: e for e in events if e['event'] == 'stop'}
    intervals = {}
    cpu = 0.0
    print('| Category | Stage | Elapsed seconds | CPU seconds | Outcome |')
    print('| --- | --- | ---: | ---: | --- |')
    for key, start in starts.items():
        stop = stops.get(key)
        if stop is None:
            print(f"Open span: {key} ({start['label']})")
            continue
        elapsed = stop.get('wall_s', stop['timestamp'] - start['timestamp'])
        measured_cpu = stop.get('cpu_s')
        cpu += measured_cpu or 0
        intervals.setdefault(start['category'], []).append(
            (start['timestamp'], stop['timestamp']))
        label = start['label'].replace('|', '/').replace('\n', ' ')
        cpu_text = 'unmeasured' if measured_cpu is None else f'{measured_cpu:.2f}'
        print(f"| {start['category']} | {label} | {elapsed:.2f} | "
              f"{cpu_text} | {stop.get('outcome', '')} |")
    print('\nElapsed coverage by category (overlap within each category removed):')
    for category, spans in intervals.items():
        print(f'- {category}: {union_seconds(spans):.2f} s')
    print(f'\nMeasured command CPU: {cpu:.2f} s (do not nest command wrappers).')
    active = [span for category, spans in intervals.items() if category != 'pause'
              for span in spans]
    print(f'Active span coverage, overlap removed: {union_seconds(active):.2f} s')
    print('Categories can overlap; do not add their totals. Gaps are unclassified.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ledger', type=Path, default=DEFAULT)
    sub = parser.add_subparsers(dest='action', required=True)
    for action in ('start', 'run'):
        p = sub.add_parser(action)
        p.add_argument('category', choices=['build', 'check', 'review', 'implementation',
                                          'setup', 'pr', 'pause'])
        p.add_argument('label')
        if action == 'run':
            p.add_argument('command', nargs=argparse.REMAINDER)
    p = sub.add_parser('stop')
    p.add_argument('id')
    p.add_argument('--outcome', default='complete')
    sub.add_parser('report')
    args = parser.parse_args()
    if args.action == 'report':
        report(args.ledger)
        return 0
    if args.action == 'stop':
        events = [json.loads(line) for line in args.ledger.read_text().splitlines()]
        if not any(e['event'] == 'start' and e['id'] == args.id for e in events):
            parser.error('unknown span ID')
        if any(e['event'] == 'stop' and e['id'] == args.id for e in events):
            parser.error('span already closed')
        append(args.ledger, dict(event='stop', id=args.id, outcome=args.outcome))
        return 0
    command = getattr(args, 'command', [])
    if command[:1] == ['--']:
        command = command[1:]
    if args.action == 'run' and not command:
        parser.error('run requires a command')
    key = uuid.uuid4().hex[:12]
    append(args.ledger, dict(event='start', id=key, category=args.category,
                            label=args.label, cwd=os.getcwd()))
    if args.action == 'start':
        print(key)
        return 0
    start = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    try:
        code = subprocess.call(command)
    except OSError as error:
        print(error)
        code = 127
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime
    append(args.ledger, dict(event='stop', id=key, wall_s=time.monotonic() - start,
                            cpu_s=cpu, peak_process_rss_kib=after.ru_maxrss,
                            exit_code=code, outcome=f'exit {code}'))
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
