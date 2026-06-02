/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import VersoManual.Bibliography
import SMDocs.TexStub
import SecureMessaging.CKA.FromDDH.Correctness

/-!
# Capability stub: paper + Lean + proof, with live citations

The flagship showcase. It pairs cryptographic-paper notation (the KaTeX macros
from the TeX stub, reused here) with the REAL `SecureMessaging` declarations that
formalise it — `CKAScheme`, the DDH construction `ddhCKA`, and the correctness
theorem `ddhCKA.correctness` — rendered with hover/LSP. Because the page imports
the live library and both the `(lean := "...")` blueprint refs and the `#check`s
resolve against it, renaming any referenced declaration FAILS this build instead
of letting the prose silently drift.

It also demonstrates Verso-Blueprint's bibliography: `@[bib]` entries cited with
`{Informal.citet}` / `{Informal.citep}` and listed by `{blueprint_bibliography}`.
-/

open Verso.Genre Manual
open Informal

set_option doc.verso true

-- Bibliography entries — the papers this construction follows. Each is a
-- `Citable` value registered under a citation label by `@[bib]`; these are the
-- real references taken from the library's own docstrings.

@[bib "ACD19"]
def ACD19 : Verso.Genre.Manual.Bibliography.Citable := .inProceedings
  { title := inlines!"The Double Ratchet: Security Notions, Proofs, and Modularization for the Signal Protocol"
  , authors := #[inlines!"Joël Alwen", inlines!"Sandro Coretti", inlines!"Yevgeniy Dodis"]
  , year := 2019
  , booktitle := inlines!"EUROCRYPT 2019"
  , url := some "https://eprint.iacr.org/2018/1037" }

@[bib "TripleRatchet"]
def TripleRatchet : Verso.Genre.Manual.Bibliography.Citable := .inProceedings
  { title := inlines!"Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol"
  , authors := #[inlines!"Yevgeniy Dodis", inlines!"Daniel Jost", inlines!"Shuichi Katsumata", inlines!"Thomas Prest", inlines!"Sebastian Schmidt"]
  , year := 2025
  , booktitle := inlines!"EUROCRYPT 2025"
  , url := some "https://eprint.iacr.org/2025/078" }

@[bib "SPQR"]
def SPQR : Verso.Genre.Manual.Bibliography.Citable := .inProceedings
  { title := inlines!"How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols: A Quest for a More Efficient and Secure Post-Quantum Protocol"
  , authors := #[inlines!"Benedikt Auerbach", inlines!"Yevgeniy Dodis", inlines!"Daniel Jost", inlines!"Shuichi Katsumata", inlines!"Sebastian Schmidt"]
  , year := 2025
  , booktitle := inlines!"USENIX Security 2025"
  , url := some "https://eprint.iacr.org/2025/2267" }

#doc (Manual) "CKA from Diffie-Hellman" =>
%%%
tag := "cka_from_ddh"
%%%

_Continuous key agreement_ (CKA) is the public-key ratchet at the heart of a
secure-messaging protocol: two parties alternate sending and receiving, and every
exchange refreshes a shared epoch key. The construction below is the
Diffie-Hellman CKA of {Informal.citet ACD19}[] (Section 4.1); its syntax and
security model follow {Informal.citet TripleRatchet}[] (Definition 2.12). A
post-quantum successor is studied in {Informal.citet SPQR}[].

# The abstract interface

A CKA scheme bundles key generation, two initialisers, and per-party send/receive
algorithms. In the formalisation this is the Lean structure `CKAScheme` —
hover the name, or the `#check` below, to read its real type off the live library:

```lean "sig_cka_interface"
#check CKAScheme
```

:::definition "cka_interface" (lean := "CKAScheme")
A continuous key agreement scheme over initial-key space $`\mathit{IK}`, state
space $`\mathit{St}`, epoch-key space $`I`, message space $`\rho`, and
send-randomness space $`\mathit{Rand}`. Each send produces a fresh epoch key in
$`I`, a public message in $`\rho` for the peer, and the sender's next state.
:::

# The Diffie-Hellman construction

Work in a module $`\mathbf{Module}\ F\ G` with a fixed generator $`g \in G`. A
party is either ready to send (holding the peer's public value $`h \in G`) or
ready to receive (holding its own scalar $`x \in F`). A send samples a scalar and
publishes its public value:

$$`\mathsf{send}(h):\quad x \sample F,\quad I := x \cdot h,\quad \rho := x \cdot g`

so one alternation step of the ratchet reads

$$`\mathsf{Alice} \msgR{\rho \,=\, x \cdot g} \mathsf{Bob}`

and the receiver recovers the same epoch key as
$`x \cdot \rho = x \cdot (y \cdot g) = (x y)\cdot g`. The construction and its
phase-tagged party state are the Lean definitions `ddhCKA` and
`CKAState`:

```lean "sig_ddh_cka"
#check @ddhCKA
#check CKAState
```

:::definition "ddh_cka" (lean := "ddhCKA, CKAState")
{uses "cka_interface"}[]
The DDH instantiation `ddhCKA` of the CKA interface, with phase-tagged party
state `CKAState` (`sendReady h` / `recvReady x`). A send samples
$`x \sample F` and publishes $`x \cdot g`; a receive multiplies the incoming
public value by the held scalar.
:::

# Correctness

Both parties always derive the same epoch key, so the protocol is _perfectly_
correct: against any passive adversary the correctness experiment
`CKAScheme.correctnessExp` returns `true` with probability $`1`.

```lean "sig_correctness"
#check @ddhCKA.correctness
```

:::theorem "ddh_cka_correct" (lean := "ddhCKA.correctness")
{uses "ddh_cka"}[]
For every passive send/receive adversary, the DDH-CKA correctness experiment
returns `true` with probability $`1`:
$$`\Pr\bigl[\,\mathsf{correctnessExp}\,(\mathsf{ddhCKA}\ F\ G\ g)\ \mathcal{A} = \mathsf{true}\,\bigr] = 1.`
:::

The theorem is checked against the live proof: rename `ddhCKA.correctness`
in the library and this page stops building.
