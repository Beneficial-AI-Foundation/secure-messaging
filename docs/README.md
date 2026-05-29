# SecureMessaging Verso Documentation

Verso/Blueprint documentation for the `SecureMessaging` Lean library — a
formalization of common cryptographic building blocks used across two-party
secure-messaging stacks. The library's intended downstream consumer is a
future formalization of [libsignal](https://github.com/signalapp/libsignal),
Signal's secure-messaging stack, which centers on the Double Ratchet and now
also ships post-quantum components (the SPQR algorithm of Auerbach et al.,
USENIX '25, is one such PQ component and is built on the Triple Ratchet).

This site is split into a shared **Section 0 — Prerequisites** chapter,
covering the VCV-io polynomial-functor / free-monad / probabilistic-monad
stack that every protocol chapter in this library reuses, followed by
protocol-specific chapters added alongside each formalization as it lands.

See [DIAGRAMS.md](DIAGRAMS.md) for the local convention on editable Verso
diagrams, including when to use HTML/SVG DOM output versus TikZ/TeX output.

## Quick build

The build + render flow is wrapped in `scripts/build-blueprint.sh`. From
the repository root:

```bash
./scripts/build-blueprint.sh
python3 -m http.server 8080 -d docs/_out/site/html-multi
```

Then open `http://localhost:8080`. The sections below describe what the
wrapper does step by step, useful when debugging or running individual
stages.

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

## Adding a new chapter

Each protocol chapter lives in its own file under
`docs/SecureMessagingDocs/`. To add one:

1. Create `docs/SecureMessagingDocs/Doc<Name>.lean` with a chapter
   scaffold (see template below).
2. In `docs/SecureMessagingDocs/Contents.lean`:
   - add `import SecureMessagingDocs.Doc<Name>` near the top, and
   - add `{include 1 SecureMessagingDocs.Doc<Name>}` to the body where
     the chapter should appear.
3. Run `./scripts/build-blueprint.sh` to verify the chapter compiles
   and that every `(lean := "...")` reference resolves. The build fails
   if a referenced Lean declaration is missing or renamed, so this is
   also the cheapest way to catch drift between docs and code.

### Minimal chapter scaffold

```lean
/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import SecureMessagingDocs.BlueprintTriptych
-- Plus any SecureMessaging / VCVio modules whose declarations this
-- chapter references via `(lean := "X")`.

open Verso.Genre Manual
open Informal

#doc (Manual) "<Chapter title>" =>
%%%
tag := "<chapter_tag>"
%%%

Prose introduction to the chapter.

:::group "<group_tag>"
Short overview of what the group covers.
:::

:::definition "<def_tag>" (lean := "MyLeanDecl") (parent := "<group_tag>")
Description of the definition. The `(lean := ...)` reference must
resolve to a real declaration; the build fails otherwise.
:::
```

### Worked examples

* [`Prerequisites.lean`](SecureMessagingDocs/Prerequisites.lean) — the
  longest current chapter; uses `:::group`, `:::definition`, and the
  custom triptych and free-monad diagram blocks.
* [`BlueprintTriptych.lean`](SecureMessagingDocs/BlueprintTriptych.lean)
  — the local "Paper / Lean / Meaning" three-panel block extension.
  Used inside Prerequisites.lean for paper-vs-Lean cross-references.
* [`DIAGRAMS.md`](DIAGRAMS.md) — convention for adding new editable
  Verso diagrams (HTML/SVG plus TikZ) via `block_extension`.
