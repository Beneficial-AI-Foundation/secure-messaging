/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.AEAD.Defs
public import SecureMessaging.FSAEAD.Defs
public import VCVio.CryptoFoundations.PRG

/-!
# FS-AEAD from AEAD and PRG

Formalization of the FS-AEAD construction of:

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — §4.2.2, Figure 6.

The PRG `G` maps a seed to a new seed and an AEAD key. A and B share a key `k = w₀` and
derive the same chain `(wⱼ, Kⱼ) ← G(wⱼ₋₁)`. Each party keeps only its current seed. A
sends its `j`-th message `mⱼ` with associated data `aⱼ` as `(j, eⱼ)`, where `eⱼ` is
encrypted under `Kⱼ` with the AEAD associated data `(j, aⱼ)`. B keeps its position `i_B`
in the chain, its current seed, and a dictionary `D` of the keys of the indices that it
skipped and has not received yet. In the example below, message 3 arrives first:

```text
A   w₀ ──G──▶ w₁ ──G──▶ w₂ ──G──▶ w₃        state (w₃, i_A = 3)
         │         │         │
         K₁        K₂        K₃             eⱼ ← Enc(Kⱼ, (j, aⱼ), mⱼ)
         ┊         ┊         │
      (1, e₁)   (2, e₂)   (3, e₃)           1 and 2 in transit
                             │
                             ▼              3 arrives first
B        K₁        K₂        K₃             K₁ = D[1], K₂ = D[2]
         │         │         │              K₃ decrypts (3, e₃)
    w₀ ──G──▶ w₁ ──G──▶ w₂ ──G──▶ w₃        state (w₃, i_B = 3, D)
```

[NOTATION]
- `W`: seed space of the PRG and key space of the FS-AEAD scheme.
- `Kae`, `Cae`: AEAD key and ciphertext spaces. `AD`, `M`: associated data and message
  spaces.
- `G` is `prg.gen : W → W × Kae`. `Enc` and `Dec` are `ae.encrypt` and `ae.decrypt`.
  The construction does not use `ae.keygen`, because `G` derives the AEAD keys.
- `w_A`, `i_A` and `w_B`, `i_B`, `D` are the fields of `SendState` and `RecvState`.

[CORRECTIONS TO ACD19]
1. `skip` stores `D[i_B] ← K`, not `D[u] ← K`. As printed, every skipped key goes to the
   entry `u` of the target index and overwrites the one before. No skipped key is stored
   at its own index, so B cannot find it when the skipped message arrives later, and
   out-of-order delivery fails correctness.
2. `FS-Rcv` rejects a ciphertext `(i, e)` with `D[i] = ⊥` and `i ≤ i_B`. As printed, such
   a miss calls `skip(i)`, which does nothing, and then derives `K_{i_B + 1}` under the
   name `i` and sets `i_B ← i`. Attack: A sends one message and B receives it, so both
   are at `w₁`. `O-Corr-A` reveals `w₁`. The adversary computes `(w₂, K₂) ← G(w₁)` and
   injects `(0, Enc(K₂, (0, a), m))`. B accepts it at index 0. Index 0 is not in `comp`,
   because `O-Corr-A` only adds the indices above `i_A = 1`, so the adversary wins.
   A's first index is 1, so the repair also rejects index 0 in the initial state.

[AMBIGUITIES RESOLVED]
- Figure 6 initialises `D[·] ← λ`, but `try-skipped` and `FS-Rcv` use `⊥` for an empty
  entry. We write `⊥` for both: `D` is a function `ℕ → Option Kae`, and `none` is `⊥`.
  `D` is a logical dictionary. It does not model the physical erasure of keys or a bound
  on the storage.

[ENCODING OF FIGURE 6]
- `error` is `none`, the rejection of `FSAEADScheme.rcv`. The prose before Figure 6
  says that `error` rolls the state back to where it was before the call to `FS-Rcv`.
  Returning `none` gives no new state, so the caller keeps the old one. This also undoes
  the `D[i] ← ⊥` of `try-skipped`.
- `skip(u)` runs `u - 1 - i_B` steps, by recursion on the number of steps (`skipSteps`)
  instead of a `while` loop.
-/

@[expose] public section

namespace FSAEADScheme

variable {W Kae Cae AD M : Type}

namespace FromAEADPRG

/-- Party A's state `v_A = (w_A, i_A)`. -/
-- ANCHOR: SendState
structure SendState (W : Type) where
  /-- `w_A`: current seed. -/
  w : W
  /-- `i_A`: number of messages sent. -/
  iA : ℕ
-- ANCHOR_END: SendState

/-- Party B's state `v_B = (w_B, i_B, D)`. -/
-- ANCHOR: RecvState
structure RecvState (W Kae : Type) where
  /-- `w_B`: current seed. -/
  w : W
  /-- `i_B`: B's position in the chain, so `w_B = w_{i_B}`. It is 0 initially. -/
  iB : ℕ
  /-- `D`: keys of the skipped indices that B has not received, with `none` for `⊥`. -/
  D : ℕ → Option Kae
-- ANCHOR_END: RecvState

/-! ## The algorithms -/

/-- `Init-A(k)`: `v_A ← (k, 0)`. -/
-- ANCHOR: initS
def initS (k : W) : SendState W := { w := k, iA := 0 }
-- ANCHOR_END: initS

/-- `Init-B(k)`: `v_B ← (k, 0, D)` with `D[j] = ⊥` for every `j`. -/
-- ANCHOR: initR
def initR (k : W) : RecvState W Kae := { w := k, iB := 0, D := fun _ => none }
-- ANCHOR_END: initR

/-- `FS-Send(v_A, a, m)`.
```text
i_A++
(w, K) ← G(w)
h ← (i_A, a)
e ← Enc(K, h, m)
return (i_A, e)
``` -/
-- ANCHOR: send
def send (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    (st : SendState W) (a : AD) (m : M) : SendState W × (ℕ × Cae) :=
  let iA := st.iA + 1
  let (w, K) := prg.gen st.w
  ({ w, iA }, (iA, ae.encrypt K (iA, a) m))
-- ANCHOR_END: send

/-- `n` iterations of the loop body of `skip`. `[…]` marks correction 1.
```text
i_B++
(w, K) ← G(w)
[D[i_B] ← K]
``` -/
-- ANCHOR: skipSteps
def skipSteps (prg : PRGScheme W (W × Kae)) : ℕ → RecvState W Kae → RecvState W Kae
  | 0, st => st
  | n + 1, st =>
    let iB := st.iB + 1
    let (w, K) := prg.gen st.w
    skipSteps prg n { w, iB, D := Function.update st.D iB (some K) }
-- ANCHOR_END: skipSteps

/-- `skip(u)`. `[…]` marks correction 1. The loop runs `u - 1 - i_B` times.
```text
while i_B < u − 1:
  i_B++; (w, K) ← G(w); [D[i_B] ← K]
``` -/
-- ANCHOR: skip
def skip (prg : PRGScheme W (W × Kae)) (u : ℕ) (st : RecvState W Kae) : RecvState W Kae :=
  skipSteps prg (u - 1 - st.iB) st
-- ANCHOR_END: skip

/-- `try-skipped(i)`: returns `D[i]` and sets `D[i] ← ⊥`. -/
-- ANCHOR: trySkipped
def trySkipped (st : RecvState W Kae) (i : ℕ) : Option Kae × RecvState W Kae :=
  (st.D i, { st with D := Function.update st.D i none })
-- ANCHOR_END: trySkipped

/-- `FS-Rcv(v_B, a, c)`, with `none` for `error`. `[…]` marks correction 2.
```text
(i, e) ← c
K ← try-skipped(i)
if K = ⊥:
  [if i ≤ i_B: error]
  skip(i)
  (w, K) ← G(w)
  i_B ← i
h ← (i, a)
m ← Dec(K, h, e)
if m = ⊥: error
return (i, m)
```
`try-skipped` runs before the test `i ≤ i_B`, so B accepts a delayed message at a skipped
index. On `error` the caller keeps `v_B`, which undoes the `D[i] ← ⊥` of `try-skipped`. -/
-- ANCHOR: rcv
def rcv (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    (st : RecvState W Kae) (a : AD) (c : ℕ × Cae) : Option (RecvState W Kae × ℕ × M) := do
  let (i, e) := c
  let (K?, st) := trySkipped st i
  let (st, K) ← match K? with
    | some K => some (st, K)
    | none => do
      if i ≤ st.iB then none
      let st := skip prg i st
      let (w, K) := prg.gen st.w
      some ({ st with w, iB := i }, K)
  let m ← ae.decrypt K (i, a) e
  return (st, i, m)
-- ANCHOR_END: rcv

end FromAEADPRG

open FromAEADPRG

/-- Let `ae` be an AEAD scheme with associated data `(i, a)` and `prg` a PRG
`G : W → W × Kae`. Then `fromAEADPRG ae prg` is the FS-AEAD scheme of [ACD19, Figure 6] with
key space `W`, with the corrections of the module header. -/
-- ANCHOR: fromAEADPRG
def fromAEADPRG (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) :
    FSAEADScheme W (SendState W) (RecvState W Kae) AD M (ℕ × Cae) where
  initS := FromAEADPRG.initS
  initR := FromAEADPRG.initR
  send := FromAEADPRG.send ae prg
  rcv := FromAEADPRG.rcv ae prg
-- ANCHOR_END: fromAEADPRG

end FSAEADScheme
