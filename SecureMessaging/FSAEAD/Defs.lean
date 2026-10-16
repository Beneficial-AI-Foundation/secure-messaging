/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append
import ToVCVio.OracleComp.SimSemantics.UnifLift

/-!
# Forward-Secure Authenticated Encryption with Associated Data (FS-AEAD)

Formalization of FS-AEAD syntax and security following:

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Definition 14 (syntax), Figure 5 (security game), Definition 15 (security).

An FS-AEAD scheme is a deterministic, stateful, unidirectional channel from a sender A
to a receiver B, keyed by a pre-shared key. It must provide forward secrecy and
immediate decryption: ciphertexts may arrive out of order or not at all, and each one
is decrypted as soon as it arrives.

[SPACES]
- `K`: key space.
- `SS`, `SR`: sender and receiver state spaces.
- `AD`: associated data space.
- `M`: message space.
- `C`: ciphertext space.

[ALGORITHMS]
- `initS : K → SS`, `initR : K → SR`: `FS-Init-S`, `FS-Init-R`.
- `send : SS → AD → M → SS × C`: `(v', e) ← FS-Send(v, a, m)`.
- `rcv : SR → AD → C → Option (SR × ℕ × M)`: `(v', i, m) ← FS-Rcv(v, a, e)`, where `i`
  is the position of `m` in the sender's sequence.

The memory-management functions `FS-Stop` and `FS-Max` are omitted: ACD19 gives them no
formal requirement.

[DEVIATIONS FROM ACD19]
As printed, Figure 5 has two errors. Without D4, every scheme either accepts a forgery or
fails correctness. Without D2, the adversary wins against schemes that keep their state on a
rejection and report the index named in the rejected ciphertext. D2 and D4 correct the
errors. D1 fills a gap in Definition 14, D3 does not change who wins, and D5 halves the
advantage. Each deviation is marked `(Dn)` where it takes effect.

- (D1) Definition 14 has `FS-Rcv` always return `(v', i, m)` and does not say what happens
  on rejection; Figure 5 tests `m' ≠ ⊥`. Here `rcv` returns `none` on rejection, with no
  new state and no index, so a rejecting receiver keeps its state, as in the rollback on
  `error` in Figure 6.
- (D2) Figure 5's `inject-B` runs `delete(i')` even when `m' = ⊥`. Here a rejected
  injection has no effect on the records. Otherwise, if the scheme reports the index of a
  rejected ciphertext, rejected garbage for an honest index removes its record, and the
  honest ciphertext then counts as a forgery.
- (D3) On a rejection, Figure 5's `deliver-B` executes `win`, then `delete(i)`, and
  returns `(i', ⊥)`. Here it executes `win`, leaves the records and `v_B` alone, and
  returns `none`. The game outcome is the same, since the adversary has already won.
- (D4) Figure 5's `inject-B` counts a forgery for index `i'` as a win unless `i' ∈ comp`,
  and `comp` only holds indices that were already sent. So after `corr-A`, the adversary
  wins by computing A's next ciphertext from the revealed state and injecting it. Here,
  once A is corrupted, an index that A has not sent yet also counts as compromised,
  unless an earlier injection consumed it. Figure 5's `delete(i')` has no record to
  remove for such an index. Here the index goes into `preempted`, and when A later sends
  it, the record is dropped, as if it were deleted then. Without this, no correct scheme
  meets the game: B accepts the injected ciphertext for an index and must then decrypt
  A's honest ciphertext for the same index, so it also accepts a replay without any
  corruption. As in Figure 5, A can still send after `corr-A`, so the game still checks
  that accepted injections do not break the delivery of A's later messages.
- (D5) §2.1 defines the advantage of an indistinguishability game as
  `2 · |Pr[A wins] - 1/2|`. Here the advantage is `|Pr[A wins] - 1/2|`, half of that,
  matching `AEADScheme.guessAdvantage`.

[AMBIGUITIES RESOLVED]
- `deliver-B` requires `(i, a, m, e) ∈ trans` "for some `i, m`". If several in-transit
  records have the same `(a, e)`, the first one is used.
- `delete(i)` for an index that A has already sent but that has no record changes
  nothing.

[ENCODING OF FIGURE 5]
- The adversary wins if a `win` instruction is reached or if its final guess `b'`
  equals `b` (§2.1), so the experiment returns `won || b == b'`.
- `req` exits the oracle and undoes its actions (§2.1): the oracle returns `none` and
  leaves the game state unchanged.
- `end` disables all oracles (§2.1): `corr-B` sets `ended`, after which every oracle
  except the uniform-randomness oracle returns `none`.
- `chall` and `comp` store indices rather than whole records: indices are unique per
  record, so `(i, m) ∈ chall` amounts to `i ∈ chall`.
- The challenge oracle's `|m₀| = |m₁|` uses a length function `len : M → ℕ` passed to
  the game.
- The `flag = bad` branch of `record` is dropped: FS-AEAD is deterministic, so no
  oracle ever passes `bad`.
- As in `AEADScheme`, the adversary also has a uniform-randomness oracle.
-/

open ToVCVio OracleSpec OracleComp ENNReal

/-- A forward-secure AEAD scheme with key space `K`, sender state `SS`, receiver state
`SR`, associated-data space `AD`, message space `M` and ciphertext space `C`.
All algorithms are deterministic.

Definition 14 of [ACD19]. -/
-- ANCHOR: FSAEADScheme
structure FSAEADScheme (K SS SR AD M C : Type) where
  /-- `FS-Init-S`: the sender's initial state. -/
  initS : K → SS
  /-- `FS-Init-R`: the receiver's initial state. -/
  initR : K → SR
  /-- `FS-Send(v, a, m) = (v', e)`. -/
  send : SS → AD → M → SS × C
  /-- `FS-Rcv(v, a, e) = (v', i, m)`, or `none` if `e` is rejected.
  Deviation (D1): a rejection produces no new state and no index. -/
  rcv : SR → AD → C → Option (SR × ℕ × M)
-- ANCHOR_END: FSAEADScheme

namespace FSAEADScheme

variable {K SS SR AD M C : Type}

section Security

/-! ## Security game (Figure 5 of [ACD19]) -/

/-- State of the FS-AEAD security game. -/
-- ANCHOR: GameState
structure GameState (SS SR AD M C : Type) where
  /-- Sender state `v_A`. -/
  vA : SS
  /-- Receiver state `v_B`. -/
  vB : SR
  /-- Number of messages sent so far, `i_A`. -/
  iA : ℕ
  /-- Whether A has been corrupted. -/
  corrA : Bool
  /-- Set by `corr-B`, after which every oracle except the uniform-randomness oracle
  returns `none`. -/
  ended : Bool
  /-- Set when a `win` instruction is reached. -/
  won : Bool
  /-- Ciphertexts in transit, as records `(i, a, m, e)`. -/
  trans : List (ℕ × AD × M × C)
  /-- Indices of challenge ciphertexts in transit. -/
  chall : Finset ℕ
  /-- Indices of ciphertexts in transit that A sent while corrupted. -/
  comp : Finset ℕ
  /-- Indices that an injection consumed before A sent them.
  Deviation (D4): not in Figure 5. -/
  preempted : Finset ℕ
-- ANCHOR_END: GameState

namespace GameState

/-- The `init` procedure of Figure 5, after `k ←$ K`. -/
-- ANCHOR: gameStateInit
def init (fs : FSAEADScheme K SS SR AD M C) (k : K) : GameState SS SR AD M C where
  vA := fs.initS k
  vB := fs.initR k
  iA := 0
  corrA := false
  ended := false
  won := false
  trans := []
  chall := ∅
  comp := ∅
  preempted := ∅
-- ANCHOR_END: gameStateInit

/-- `record(flag, a, m, e)` of Figure 5, for the record at index `i_A`.
Deviation (D4): nothing is recorded if an injection already consumed `i_A`. -/
-- ANCHOR: gameStateRecord
def record (st : GameState SS SR AD M C) (isChall : Bool) (a : AD) (m : M) (e : C) :
    GameState SS SR AD M C :=
  if st.iA ∈ st.preempted then st else
  { st with
    trans := st.trans ++ [(st.iA, a, m, e)]
    chall := if isChall then insert st.iA st.chall else st.chall
    comp := if st.corrA then insert st.iA st.comp else st.comp }
-- ANCHOR_END: gameStateRecord

/-- `delete(i)` of Figure 5: remove the record with index `i` everywhere.
Deviation (D4): if A has not sent `i` yet, remember `i` so that its record is dropped
when A sends it. -/
-- ANCHOR: gameStateDelete
def delete (st : GameState SS SR AD M C) (i : ℕ) : GameState SS SR AD M C :=
  { st with
    trans := st.trans.filter (·.1 ≠ i)
    chall := st.chall.erase i
    comp := st.comp.erase i
    preempted := if st.iA < i then insert i st.preempted else st.preempted }
-- ANCHOR_END: gameStateDelete

/-- Whether a ciphertext for index `i` may legitimately be forged: A sent `i` while
corrupted and it is still in transit, or A is corrupted, has not sent `i` yet, and no
injection consumed `i`.
Deviation (D4): Figure 5 has only `i ∈ comp`. -/
-- ANCHOR: gameStateIsCompromised
def isCompromised (st : GameState SS SR AD M C) (i : ℕ) : Bool :=
  i ∈ st.comp || (st.corrA && st.iA < i && i ∉ st.preempted)
-- ANCHOR_END: gameStateIsCompromised

/-- The first in-transit record with associated data `a` and ciphertext `e`. Figure 5's
`deliver-B` takes such a record "for some `i, m`" and does not say which one if there
are several. -/
def findTrans [DecidableEq AD] [DecidableEq C] (st : GameState SS SR AD M C)
    (a : AD) (e : C) : Option (ℕ × AD × M × C) :=
  st.trans.find? fun r => r.2.1 = a ∧ r.2.2.2 = e

end GameState

/-- Oracle spec for the FS-AEAD security game: uniform randomness, then `transmit-A`,
`chall-A`, `corr-A`, `corr-B`, `deliver-B` and `inject-B`. Each of the last six answers
`none` when its `req` fails or after the game has ended. -/
-- ANCHOR: fsaeadSpec
abbrev fsaeadSpec (SS SR AD M C : Type) :=
  unifSpec
    + (AD × M →ₒ Option C)
    + (AD × M × M →ₒ Option C)
    + (Unit →ₒ Option SS)
    + (Unit →ₒ Option (SS × SR))
    + (AD × C →ₒ Option (ℕ × Option M))
    + (AD × C →ₒ Option (ℕ × M))
-- ANCHOR_END: fsaeadSpec

namespace fsaeadSpec

variable {SS SR AD M C : Type}

/-- Domain index selecting the uniform-randomness oracle. -/
@[match_pattern] abbrev OUnif (n : ℕ) : (fsaeadSpec SS SR AD M C).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inl n)))))
/-- Domain index selecting `transmit-A`. -/
@[match_pattern] abbrev OTransmitA (am : AD × M) : (fsaeadSpec SS SR AD M C).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inr am)))))
/-- Domain index selecting `chall-A`. -/
@[match_pattern] abbrev OChallA (amm : AD × M × M) : (fsaeadSpec SS SR AD M C).Domain :=
  .inl (.inl (.inl (.inl (.inr amm))))
/-- Domain index selecting `corr-A`. -/
@[match_pattern] abbrev OCorrA : (fsaeadSpec SS SR AD M C).Domain :=
  .inl (.inl (.inl (.inr ())))
/-- Domain index selecting `corr-B`. -/
@[match_pattern] abbrev OCorrB : (fsaeadSpec SS SR AD M C).Domain :=
  .inl (.inl (.inr ()))
/-- Domain index selecting `deliver-B`. -/
@[match_pattern] abbrev ODeliverB (ae : AD × C) : (fsaeadSpec SS SR AD M C).Domain :=
  .inl (.inr ae)
/-- Domain index selecting `inject-B`. -/
@[match_pattern] abbrev OInjectB (ae : AD × C) : (fsaeadSpec SS SR AD M C).Domain :=
  .inr ae

end fsaeadSpec

/-- An FS-AEAD adversary: a computation with access to the game oracles, outputting a
guess `b'` for the challenge bit. -/
-- ANCHOR: FSAEADAdversary
abbrev FSAEADAdversary (SS SR AD M C : Type) :=
  OracleComp (fsaeadSpec SS SR AD M C) Bool
-- ANCHOR_END: FSAEADAdversary

/-! ### Oracle implementations -/

/-- Game monad of the FS-AEAD security game. -/
abbrev GameM (SS SR AD M C : Type) := StateT (GameState SS SR AD M C) ProbComp

/-- Uniform-randomness oracle lifted to the game monad. -/
def oracleUnif (SS SR AD M C : Type) : QueryImpl unifSpec (GameM SS SR AD M C) :=
  unifLiftStateT (GameState SS SR AD M C) unifSpec

/-- **transmit-A(a, m)**. A sends `m`, and the ciphertext is recorded as a normal one.
```text
transmit-A(a, m):
  i_A++
  (v_A, e) ← FS-Send(v_A, a, m)
  record(good, a, m, e)
  return e
``` -/
-- ANCHOR: oracleTransmitA
def oracleTransmitA (fs : FSAEADScheme K SS SR AD M C) :
    QueryImpl (AD × M →ₒ Option C) (GameM SS SR AD M C) :=
  fun (a, m) => do
    let st ← get
    if st.ended then return none
    let (vA, e) := fs.send st.vA a m
    set ({ st with vA, iA := st.iA + 1 }.record false a m e)
    return some e
-- ANCHOR_END: oracleTransmitA

/-- **chall-A(a, m₀, m₁)**. A sends `m_b`, and the ciphertext is recorded as a challenge.
```text
chall-A(a, m₀, m₁):
  req ¬corrA and |m₀| = |m₁|
  i_A++
  (v_A, e) ← FS-Send(v_A, a, m_b)
  record(chall, a, m_b, e)
  return e
``` -/
-- ANCHOR: oracleChallA
def oracleChallA (fs : FSAEADScheme K SS SR AD M C) (len : M → ℕ) (b : Bool) :
    QueryImpl (AD × M × M →ₒ Option C) (GameM SS SR AD M C) :=
  fun (a, m₀, m₁) => do
    let st ← get
    if st.ended || st.corrA || len m₀ ≠ len m₁ then return none
    let m := if b then m₁ else m₀
    let (vA, e) := fs.send st.vA a m
    set ({ st with vA, iA := st.iA + 1 }.record true a m e)
    return some e
-- ANCHOR_END: oracleChallA

/-- **corr-A**. Reveals A's state. Every index that A has not sent yet and that no
injection consumed becomes compromised.
```text
corr-A:
  corrA ← true
  return v_A
``` -/
-- ANCHOR: oracleCorrA
def oracleCorrA (SS SR AD M C : Type) :
    QueryImpl (Unit →ₒ Option SS) (GameM SS SR AD M C) :=
  fun () => do
    let st ← get
    if st.ended then return none
    set { st with corrA := true }
    return some st.vA
-- ANCHOR_END: oracleCorrA

/-- **corr-B**. Reveals both states and ends the game.
```text
corr-B:
  req chall = ∅
  end
  return (v_A, v_B)
``` -/
-- ANCHOR: oracleCorrB
def oracleCorrB (SS SR AD M C : Type) :
    QueryImpl (Unit →ₒ Option (SS × SR)) (GameM SS SR AD M C) :=
  fun () => do
    let st ← get
    if st.ended || st.chall ≠ ∅ then return none
    set { st with ended := true }
    return some (st.vA, st.vB)
-- ANCHOR_END: oracleCorrB

/-- **deliver-B(a, e)**. Delivers an honest ciphertext. If B does not recover the recorded
index and message, the adversary wins. Challenge plaintexts are not returned.
```text
deliver-B(a, e):
  req (i, a, m, e) ∈ trans for some i, m   -- the first such record
  if FS-Rcv(v_B, a, e) rejects:
    win; return ⊥                          -- (D3) Figure 5 also runs delete(i)
  (v_B, i', m') ← FS-Rcv(v_B, a, e)
  if (i', m') ≠ (i, m): win
  if i ∈ chall: m' ← ⊥
  delete(i)
  return (i', m')
``` -/
-- ANCHOR: oracleDeliverB
def oracleDeliverB [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (fs : FSAEADScheme K SS SR AD M C) :
    QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM SS SR AD M C) :=
  fun (a, e) => do
    let st ← get
    if st.ended then return none
    let some (i, _, m, _) := st.findTrans a e | return none
    match fs.rcv st.vB a e with
    | none =>
      set { st with won := true }
      return none
    | some (vB, i', m') =>
      let won := st.won || !(decide (i' = i) && decide (m' = m))
      set ({ st with vB, won }.delete i)
      return some (i', if i ∈ st.chall then none else some m')
-- ANCHOR_END: oracleDeliverB

/-- **inject-B(a, e)**. Delivers any other ciphertext. If B accepts it for an index that is
not compromised, the adversary wins.
```text
inject-B(a, e):
  req (a, e) ∉ trans
  if FS-Rcv(v_B, a, e) rejects: return ⊥   -- (D2) Figure 5 runs delete(i')
  (v_B, i', m') ← FS-Rcv(v_B, a, e)
  if i' not compromised: win               -- (D4) Figure 5 has i' ∉ comp
  delete(i')                               -- (D4) remembered if i' not sent yet
  return (i', m')
``` -/
-- ANCHOR: oracleInjectB
def oracleInjectB [DecidableEq AD] [DecidableEq C] (fs : FSAEADScheme K SS SR AD M C) :
    QueryImpl (AD × C →ₒ Option (ℕ × M)) (GameM SS SR AD M C) :=
  fun (a, e) => do
    let st ← get
    if st.ended || (st.findTrans a e).isSome then return none
    let some (vB, i', m') := fs.rcv st.vB a e | return none
    let won := st.won || !st.isCompromised i'
    set ({ st with vB, won }.delete i')
    return some (i', m')
-- ANCHOR_END: oracleInjectB

/-- Complete oracle set for the FS-AEAD security game with challenge bit `b`. -/
-- ANCHOR: fsaeadSecurityImpl
def fsaeadSecurityImpl [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (fs : FSAEADScheme K SS SR AD M C) (len : M → ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec SS SR AD M C) (GameM SS SR AD M C) :=
  oracleUnif SS SR AD M C
    + oracleTransmitA fs
    + oracleChallA fs len b
    + oracleCorrA SS SR AD M C
    + oracleCorrB SS SR AD M C
    + oracleDeliverB fs
    + oracleInjectB fs
-- ANCHOR_END: fsaeadSecurityImpl

/-! ### Security experiment -/

/-- **FS-AEAD security experiment** (Figure 5 of [ACD19]).

`init`:   `k ←$ K; v_A ← FS-Init-S(k); v_B ← FS-Init-R(k); b ←$ {0, 1}`
`run`:    `b' ← A^{transmit-A, chall-A, corr-A, corr-B, deliver-B, inject-B}`
`output`: `true` if a `win` instruction was reached, otherwise `b' = b` -/
-- ANCHOR: securityExp
def securityExp [SampleableType K] [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (fs : FSAEADScheme K SS SR AD M C) (len : M → ℕ)
    (adversary : FSAEADAdversary SS SR AD M C) : ProbComp Bool := do
  let k ← $ᵗ K
  let b ← $ᵗ Bool
  let (b', st) ← (simulateQ (fsaeadSecurityImpl fs len b) adversary).run (.init fs k)
  return st.won || b == b'
-- ANCHOR_END: securityExp

/-- FS-AEAD advantage `Adv^{fs-aead}_{FS-AEAD}(A) = |Pr[securityExp = 1] - 1/2|`
(Definition 15 of [ACD19]).
Deviation (D5): ACD19 §2.1 scales the advantage of indistinguishability games by 2. -/
-- ANCHOR: advantage
noncomputable def advantage [SampleableType K] [DecidableEq AD] [DecidableEq M]
    [DecidableEq C] (fs : FSAEADScheme K SS SR AD M C) (len : M → ℕ)
    (adversary : FSAEADAdversary SS SR AD M C) : ℝ :=
  |(Pr[= true | securityExp fs len adversary]).toReal - 1 / 2|
-- ANCHOR_END: advantage

end Security

end FSAEADScheme
