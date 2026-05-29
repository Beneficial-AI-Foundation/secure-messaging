#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: ./scripts/build-blueprint.sh [OUTPUT_ROOT]

Build the SecureMessaging Verso blueprint documentation.

Defaults:
  OUTPUT_ROOT = docs/_out/site

Steps:
  1. Build the Verso doc Lean libraries (`SecureMessagingDocs`, `Main`).
     We deliberately do NOT build the `docs` executable; that links
     VCVio's post-quantum C/FFI sources and is unnecessary for rendering
     (see docs/README.md).
  2. Run `Main.lean` to render the static site into OUTPUT_ROOT.
EOF
}

case "${1:-}" in
  -h|--help)
    usage
    exit 0
    ;;
esac

if (( $# > 1 )); then
  usage >&2
  exit 1
fi

# Run from repo root
cd "$(dirname "$0")/.."

out_root="${1:-docs/_out/site}"
mkdir -p "$out_root"

echo "[build-blueprint] building Verso doc libraries"
lake -d docs build SecureMessagingDocs Main

echo "[build-blueprint] rendering blueprint -> ${out_root}"
lake -d docs env lean --run docs/Main.lean --output "$out_root"

echo "[build-blueprint] done"
echo "[build-blueprint] output:"
readlink -f "$out_root"
echo ""
echo "To serve the documentation locally:"
echo "  python3 -m http.server 8080 -d $out_root/html-multi"
echo ""
echo "Then open http://localhost:8080 in your browser."
