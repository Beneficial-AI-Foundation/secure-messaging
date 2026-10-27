/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.Defs
import SecureMessaging.FSAEAD.Defs
import VCVio.CryptoFoundations.PRG

/-!
# FS-AEAD from AEAD and PRG

Formalization of the FS-AEAD construction of:

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — §4.2.2, Figure 6.

The PRG `G` maps a seed to a new seed and an AEAD key. The sender A and the receiver B
share a key `k`, which is a seed. Starting from `k`, both apply `G` again and again, so
they derive the same chain `w₀ = k`, `(wⱼ, Kⱼ) ← G(wⱼ₋₁)` for `j ≥ 1`. Each step
overwrites the seed. To send its `i`-th message `m` with associated data `a`, A encrypts
`m` under `Kᵢ` with the AEAD associated data `(i, a)`, and sends `(i, e)`. B keeps its
position `i_B` in the chain, its current seed `w_{i_B}`, and a dictionary `D` of
the keys of the indices that it skipped and has not received yet.

The construction does not use `ae.keygen`, because the PRG derives the AEAD keys. As in
Figure 6, B accepts a forward jump of any length. libsignal rejects a counter more than
`MAX_FORWARD_JUMPS = 25_000` ahead of the chain index, except in a session with oneself.

[NOTATION]
- `W`: seed space of the PRG and key space of the FS-AEAD scheme.
- `Kae`, `Cae`: AEAD key and ciphertext spaces. `AD`, `M`: associated data and message
  spaces.
- `G` is `prg.gen : W → W × Kae`. `Enc` and `Dec` are `ae.encrypt` and `ae.decrypt`.
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

/-! ## The PRG chain -/

/-- The seed `w_j` of the chain from `w`:
```text
w_0 = w,   (w_j, K_j) = G(w_{j-1})   for j ≥ 1
``` -/
def chainState (prg : PRGScheme W (W × Kae)) (w : W) : ℕ → W
  | 0 => w
  | j + 1 => chainState prg (prg.gen w).1 j

/-- The key `K_j` of the chain from `w`, for `j ≥ 1`:
```text
(w_j, K_j) = G(w_{j-1})
```
The chain has no key at position 0. By truncated subtraction, `chainKey prg w 0` is
`K_1`, so do not use it. -/
def chainKey (prg : PRGScheme W (W × Kae)) (w : W) (j : ℕ) : Kae :=
  (prg.gen (chainState prg w (j - 1))).2

/-- Let `w_0, w_1, …` be the chain from `w`. Then `w_0 = w`. -/
@[simp]
theorem chainState_zero (prg : PRGScheme W (W × Kae)) (w : W) : chainState prg w 0 = w :=
  rfl

/-- Let `w_0, w_1, …` be the chain from `w`. Then for every `j`, `w_{j+1}` is the first
component of `G(w_j)`. -/
theorem chainState_succ (prg : PRGScheme W (W × Kae)) (w : W) (j : ℕ) :
    chainState prg w (j + 1) = (prg.gen (chainState prg w j)).1 := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih => exact ih (prg.gen w).1

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

/-- Let `(w', i', D')` be the state after `n` steps of `skip` from `(w_B, i_B, D)`. Then
`w' = w_n`, the `n`-th seed of the chain from `w_B`. -/
theorem skipSteps_w (prg : PRGScheme W (W × Kae)) (n : ℕ) (st : RecvState W Kae) :
    (skipSteps prg n st).w = chainState prg st.w n := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => exact ih _

/-- Let `(w', i', D')` be the state after `n` steps of `skip` from `(w_B, i_B, D)`. Then
`i' = i_B + n`. -/
theorem skipSteps_iB (prg : PRGScheme W (W × Kae)) (n : ℕ) (st : RecvState W Kae) :
    (skipSteps prg n st).iB = st.iB + n := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => simp only [skipSteps, ih]; omega

/-- Let `(w', i', D')` be the state after `n` steps of `skip` from `(w_B, i_B, D)`, and let
`K_1, K_2, …` be the keys of the chain from `w_B`. Then for every `j`:
```text
D'[j] = K_{j - i_B}   if i_B < j ≤ i_B + n
D'[j] = D[j]          otherwise
``` -/
theorem skipSteps_D (prg : PRGScheme W (W × Kae)) (n : ℕ) (st : RecvState W Kae) (j : ℕ) :
    (skipSteps prg n st).D j =
      if st.iB < j ∧ j ≤ st.iB + n then some (chainKey prg st.w (j - st.iB)) else st.D j := by
  induction n generalizing st with
  | zero => simp only [skipSteps]; split_ifs <;> first | rfl | omega
  | succ n ih =>
    simp only [skipSteps, ih, Function.update_apply]
    split_ifs <;> try first | rfl | omega
    · obtain ⟨k, hk₁, hk₂⟩ : ∃ k, j - (st.iB + 1) = k + 1 ∧ j - st.iB = k + 2 :=
        ⟨j - st.iB - 2, by omega, by omega⟩
      rw [hk₁, hk₂]
      rfl
    · rw [show j - st.iB = 1 by omega]
      rfl

/-- Let `i_B < u`, and let `(w', i', D')` be the result of `skip(u)` on `(w_B, i_B, D)`.
Then `i' = u - 1`, and `w'` is the `(u - 1 - i_B)`-th seed of the chain from `w_B`. -/
theorem skip_w_iB (prg : PRGScheme W (W × Kae)) (u : ℕ) (st : RecvState W Kae)
    (h : st.iB < u) :
    (skip prg u st).w = chainState prg st.w (u - 1 - st.iB) ∧ (skip prg u st).iB = u - 1 := by
  refine ⟨skipSteps_w prg _ st, ?_⟩
  simp only [skip, skipSteps_iB]
  omega

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

namespace FromAEADPRG.Toy

/-! ## Sanity checks on a toy instance

`W = Kae = ℕ` and `G(w) = (w + 1, w)`, so from `w₀ = 0` the key of position `j` is
`K_j = j - 1`, and all keys differ. The toy AEAD ciphertext carries the key, the header and
the message. `Dec` returns the message only if the key and the header match, so a wrong
derived or cached key fails. -/

/-- The toy AEAD ciphertext: key, header `(i, a)` and message. -/
abbrev ToyC := ℕ × (ℕ × ℕ) × ℕ

/-- The toy AEAD, which checks the key and the header. -/
def ae : AEADScheme ProbComp ℕ (ℕ × ℕ) ℕ ToyC where
  keygen := pure 0
  encrypt K h m := (K, h, m)
  decrypt K h e := if e.1 = K ∧ e.2.1 = h then some e.2.2 else none

/-- The toy PRG `G(w) = (w + 1, w)`. -/
def prg : PRGScheme ℕ (ℕ × ℕ) := ⟨fun w => (w + 1, w)⟩

/-- The toy FS-AEAD scheme, with `AD = M = ℕ`. -/
abbrev fs := fromAEADPRG ae prg

/-- A sends the messages `(a, m)` in order. -/
def sendAll (st : SendState ℕ) : List (ℕ × ℕ) → List (ℕ × ToyC)
  | [] => []
  | (a, m) :: ms => let (st', c) := fs.send st a m; c :: sendAll st' ms

/-- B receives the ciphertexts `(a, c)` in order. It keeps its state after a rejection and
records `none` for it. -/
def rcvAll (st : RecvState ℕ ℕ) : List (ℕ × ℕ × ToyC) → List (Option (ℕ × ℕ)) × RecvState ℕ ℕ
  | [] => ([], st)
  | (a, c) :: cs =>
    match fs.rcv st a c with
    | none => let r := rcvAll st cs; (none :: r.1, r.2)
    | some (st', i, m) => let r := rcvAll st' cs; (some (i, m) :: r.1, r.2)

/-- A's four ciphertexts from key 0: message `100 + j - 1` with associated data `10 + j - 1`
at index `j`. -/
def cts : List (ℕ × ToyC) := sendAll (fs.initS 0) [(10, 100), (11, 101), (12, 102), (13, 103)]

/-- A's `j`-th ciphertext, with its associated data. -/
def c (j : ℕ) : ℕ × ℕ × ToyC := (9 + j, cts[j - 1]!)

/-- The initial receiver state. -/
abbrev B₀ : RecvState ℕ ℕ := fs.initR 0

/-- A uses the key `K_j = j - 1` and the header `(j, a)`. -/
example : cts = [(1, 0, (1, 10), 100), (2, 1, (2, 11), 101), (3, 2, (3, 12), 102),
    (4, 3, (4, 13), 103)] := by decide

/-- Out-of-order delivery `4, 2, 1, 3`, then a replay of each, which B rejects. -/
example : (rcvAll B₀ [c 4, c 2, c 1, c 3, c 4, c 2, c 1, c 3]).1 =
    [some (4, 103), some (2, 101), some (1, 100), some (3, 102), none, none, none, none] := by
  decide

/-- Correction 1: after B receives message 4 first, `D[j] = K_j = j - 1` for the skipped
indices `j = 1, 2, 3`. -/
example : let st := (rcvAll B₀ [c 4]).2
    st.w = 4 ∧ st.iB = 4 ∧ st.D 0 = none ∧ st.D 1 = some 0 ∧ st.D 2 = some 1 ∧
      st.D 3 = some 2 ∧ st.D 4 = none ∧ st.D 5 = none := by decide

/-- After all four, the entries 0 to 7 of `D` are empty again. -/
example : let st := (rcvAll B₀ [c 4, c 2, c 1, c 3]).2
    st.w = 4 ∧ st.iB = 4 ∧ ∀ j < 8, st.D j = none := by decide

/-- A failed `Dec` under a key in `D` keeps the key, and the honest ciphertext at that index
is then accepted. -/
example : (rcvAll B₀ [c 2, (10, 1, 7, (1, 10), 100), c 1]).1 =
    [some (2, 101), none, some (1, 100)] := by decide

/-- A failed `Dec` after a forward skip rolls the skip back, and both the skipped and the
target honest ciphertexts are then accepted. -/
example : (rcvAll B₀ [(11, 2, 7, (2, 11), 101), c 2, c 1]).1 =
    [none, some (2, 101), some (1, 100)] := by decide

/-- A changed associated data and a changed outer index are both rejected. Both use the
key of their index, so only the AEAD header `(i, a)` differs. -/
example : (rcvAll B₀ [(99, (c 1).2), (10, 2, 1, (1, 10), 100), c 1]).1 =
    [none, none, some (1, 100)] := by decide

/-- Correction 2: B rejects a miss at index 0 and at an index up to `i_B`, even under the
next chain key `K_{i_B + 1}`. The second conjunct is the attack trace of the module header:
B is at `w₁`, and the adversary injects at index 0 under `K₂ = 1`. -/
example : (rcvAll B₀ [(10, 0, 0, (0, 10), 7)]).1 = [none] ∧
    (rcvAll B₀ [c 1, (10, 0, 1, (0, 10), 7), (10, 1, 1, (1, 10), 7)]).1 =
      [some (1, 100), none, none] ∧
    (rcvAll B₀ [c 2, c 1, (10, 1, 2, (1, 10), 7)]).1 =
      [some (2, 101), some (1, 100), none] := by decide

end FromAEADPRG.Toy

end FSAEADScheme
