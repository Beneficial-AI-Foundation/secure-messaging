# Symbolic protocol verification: LeanDY and DYLean

The SimpleAuth protocol

```
A → B : A, B, Na
B → A : {Na, A}_SK(A,B)
```

formalized in two symbolic (Dolev–Yao) frameworks for Lean, and a tutorial comparing them.

| Path | Contents |
|---|---|
| `leandy-examples/` | Lake project: LeanDY's SimpleAuth (`LeanDYExamples/SimpleAuth.lean`) and its executable debug run (`LeanDYExamples/SimpleAuthDemo.lean`) |
| `dylean-examples/` | Lake project: the port of SimpleAuth to DYLean (`DYLeanExamples/SimpleAuth/`) |
| `dylean-simpleauth-workshop.html` | Tutorial: building and proving SimpleAuth in DYLean, compared step by step with LeanDY |
| `tools/generate_dylean_tutorial.py` | Regenerates the tutorial; every code excerpt is extracted from the sources |

## Why two separate Lake projects

Each framework pins its own Lean toolchain, different from the other's and from the root project's:

| Project | Toolchain | Depends on |
|---|---|---|
| repository root (`SecureMessaging`) | `v4.33.1` | VCVio, Mathlib |
| `leandy-examples` | `v4.24.0-rc1` | [LeanDY](https://github.com/SecPriv/leandy) at `e0705986`, and through it Mathlib (revision pinned by LeanDY) |
| `dylean-examples` | `v4.33.0` | [DYLean](https://github.com/BobDyLean/dylean) at `d58f33b`, no further dependencies |

A Lake project has a single toolchain, so each example is its own project, with its own
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.
The root `lakefile.toml` does not reference this folder, so the root build, `lake lint` and CI do not compile it.
The `.lake/` directories created here are ignored by the root `.gitignore`.
The Lean editor extension uses the nearest `lakefile.toml` and `lean-toolchain`,
so files in this folder are checked with their own toolchain.

Module names carry a prefix (`LeanDYExamples.`, `DYLeanExamples.`) because both frameworks ship example
libraries of their own; LeanDY's even contains a `Protocols.SimpleAuth`, the version before the
tuple-order fix.

## Building

DYLean (builds the DYLean library too, about 25 seconds):

```sh
cd symbolicTools/dylean-examples
lake build
```

LeanDY (the LeanDY library and the example take about 3 minutes once Mathlib is available):

```sh
cd symbolicTools/leandy-examples
lake exe cache get        # prebuilt Mathlib for the revision LeanDY pins (once; several GB)
lake build
lake env lean --run LeanDYExamples/SimpleAuthDemo.lean   # prints the honest run; ends with "done event emitted: true"
```

`lake exe cache get` overwrites Mathlib's build files with downloaded ones.
Do not run it over a Mathlib that was built locally (for example, a dependency directory copied from an
existing LeanDY checkout): the downloaded files then no longer match the local build records, and Lake
rebuilds Mathlib from source.

`leandy-examples/lake-manifest.json` lists LeanDY and, marked as inherited, LeanDY's own pinned
dependencies (Mathlib, Batteries, Aesop, ...). Run `lake update` there only if you intend to change them.

## Provenance

- `leandy-examples/LeanDYExamples/SimpleAuth.lean` and `SimpleAuthDemo.lean` come from LeanDY's
  `Protocols/` folder, including the tuple-order fix (commit `dd9753c`, LeanDY pull request #2) and
  explanatory comments. The only change is the demo's import, which follows the module rename.
- `dylean-examples/DYLeanExamples/SimpleAuth/` is new. DYLean has no symmetric encryption, so
  `SymEnc.lean` adds it, without modifying the DYLean library. The other files follow the layout of
  DYLean's own examples (`Specification`, `Proof`, `Instance`, `SecurityTheorems`, `SanityChecks`).

## Regenerating the tutorial

Library excerpts are read from the dependency checkouts, so build both projects first:

```sh
cd symbolicTools
(cd dylean-examples && lake build) && (cd leandy-examples && lake build)
python3 tools/generate_dylean_tutorial.py
```

The script stops with an error if an excerpt's line range no longer starts where expected,
so the tutorial cannot silently drift from the code.
