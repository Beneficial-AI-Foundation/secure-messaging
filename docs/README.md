# SecureMessaging Verso Documentation

Verso/Blueprint documentation for the `SecureMessaging` formalization.

The starting content explains how VCV-io encodes game-based security proofs
on top of polynomial functors, free monads, and probabilistic monads. Targeted
protocol-specific chapters are added alongside each formalization as it lands.

See [DIAGRAMS.md](DIAGRAMS.md) for the local convention on editable Verso
diagrams, including when to use HTML/SVG DOM output versus TikZ/TeX output.

## Build

From the repository root:

```bash
lake -d docs update
lake -d docs exe cache get
lake -d docs build SecureMessagingDocs Main
```

## Render

From the repository root:

```bash
lake -d docs env lean --run docs/Main.lean --output docs/_out/site
python3 -m http.server 8000 -d docs/_out/site/html-multi
```

Then open `http://localhost:8000`.

The docs import live VCV-io modules; if a Lean declaration in a referenced
module is renamed or removed, the documentation build should fail rather than
silently drift.

Avoid `lake -d docs build docs` on checkouts without the vendored native
sources of any dependency that links extern libraries. Building the executable
links the root package's extern libraries; `lake -d docs build SecureMessagingDocs Main`
and `lean --run` avoid that link step.
