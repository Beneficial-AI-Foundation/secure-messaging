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
- [Kli21] Tijana Klimović.
  *Modular Design of the Messaging Layer Security (MLS) Protocol.*
  Master's thesis, ETH Zürich, 2021
  — Appendix A.1 (attack on Figure 5 through a rejected injection).

An FS-AEAD scheme is a deterministic, stateful, unidirectional channel from a sender A
to a receiver B, keyed by a pre-shared key. It must provide forward secrecy and
immediate decryption: ciphertexts may arrive out of order or not at all, and each one
is decrypted as soon as it arrives.

[SPACES]
- `K`: key space.
- `StS`, `StR`: sender and receiver state spaces.
- `AD`: associated data space.
- `M`: message space.
- `C`: ciphertext space.

[ALGORITHMS]
- `initS : K → StS`, `initR : K → StR`: `FS-Init-S`, `FS-Init-R`.
- `send : StS → AD → M → StS × C`: `(v', e) ← FS-Send(v, a, m)`.
- `rcv : StR → AD → C → Option (StR × ℕ × M)`: `(v', i, m) ← FS-Rcv(v, a, e)`, where `i`
  is the position of `m` in the sender's sequence, or `none` on rejection.

[CORRECTIONS TO ACD19]
- Rejection in `FS-Rcv`: Definition 14 leaves the output of `FS-Rcv` on rejection
  unspecified. Here `rcv` returns `none` (no new state and no index), matching the
  state rollback of Figure 6 (§4.2.2). Consequently, a rejected `O-Inject-B` returns
  `none` without calling `delete` (otherwise rejected garbage for an in-transit index
  would erase its record [Kli21, Appendix A.1]), and a rejected `O-Deliver-B` sets `won`.
- Post-corruption unsent indices (marked `[…]` in the oracle pseudocode): once A is
  corrupted at counter `i_A^c`, the adversary knows A's state and can inject a
  ciphertext for an unsent index `i > i_A^c` before A sends it. In Figure 5, `comp`
  only holds indices already sent, so such an injection would count as a forgery, and
  `delete(i)` would run before A's record for `i` exists. Here:
  1. `O-Corr-A` adds all unsent indices `i > i_A^c` to `comp`, so injecting them does
     not count as a forgery, and `record` no longer adds to `comp`;
  2. when A later sends at index `i_A > i_A^c`, `record` does nothing if `corrA` holds
     and `i_A ∉ comp`, i.e. when an earlier injection already consumed index `i_A`.

[CONVENTIONS]
- Winning. A rejection in `deliver-B` gives no `(i', m')` to compare with `(i, m)`. This
  file counts the rejection as Figure 5's `(i', m') ≠ (i, m)`. `won` never returns to false.
  The game continues to run after a win, but the result stays a win. The proof in ACD19
  says that the game ends upon a win. That gives the same result, but not the same
  transcript or the same number of queries.
- Advantage. §2.1 defines the advantage of an indistinguishability game as
  `2 · |Pr[A wins] - 1/2|`. Here the advantage is `|Pr[A wins] - 1/2|`, half of that, as in
  the guess advantages of this project (`AEADScheme.guessAdvantage`, CKA, SCKA).

[AMBIGUITIES RESOLVED]
- `deliver-B` requires `(i, a, m, e) ∈ trans` "for some `i, m`". If several in-transit
  records have the same `(a, e)`, the one with the smallest index is used.
- `delete(i)` for an index that A has already sent but that has no record changes
  nothing.

[ENCODING OF FIGURE 5]
- `won` and `ended` stand for the §2.1 keywords `win` and `end`. `end` is a Lean keyword.
- The adversary wins if it reaches a winning condition or if its final guess `b'` equals
  `b` (§2.1), so the experiment returns `won || b == b'`.
- `req` exits the oracle and undoes its actions (§2.1). Here it is an explicit
  `if … : return ⊥` at the start of the oracle, which leaves the game state unchanged.
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

/-- A forward-secure AEAD scheme with key space `K`, sender state `StS`, receiver state
`StR`, associated-data space `AD`, message space `M` and ciphertext space `C`.
All algorithms are deterministic.

Definition 14 of [ACD19], with `rcv` returning `none` on rejection. -/
-- ANCHOR: FSAEADScheme
structure FSAEADScheme (K StS StR AD M C : Type) where
  /-- `FS-Init-S`: the sender's initial state. -/
  initS : K → StS
  /-- `FS-Init-R`: the receiver's initial state. -/
  initR : K → StR
  /-- `FS-Send(v, a, m) = (v', e)`. -/
  send : StS → AD → M → StS × C
  /-- `FS-Rcv(v, a, e) = (v', i, m)`, or `none` if `e` is rejected. -/
  rcv : StR → AD → C → Option (StR × ℕ × M)
-- ANCHOR_END: FSAEADScheme

namespace FSAEADScheme

variable {K StS StR AD M C : Type}

section Security

/-! ## Security game (Figure 5 of [ACD19]) -/

/-- State of the FS-AEAD security game. -/
-- ANCHOR: GameState
structure GameState (StS StR AD M C : Type) where
  /-- Sender state `v_A`. -/
  vA : StS
  /-- Receiver state `v_B`. -/
  vB : StR
  /-- Number of messages sent so far, `i_A`. -/
  iA : ℕ
  /-- Whether A has been corrupted. -/
  corrA : Bool
  /-- Set by `corr-B`, after which every oracle except the uniform-randomness oracle
  returns `none`. -/
  ended : Bool
  /-- Whether the adversary reached a winning condition. -/
  won : Bool
  /-- Ciphertexts in transit, as records `(i, a, m, e)`. -/
  trans : List (ℕ × AD × M × C)
  /-- Indices of challenge ciphertexts in transit. -/
  chall : Finset ℕ
  /-- Indices exposed by A's corruption and not yet received by B. -/
  comp : ℕ → Bool
-- ANCHOR_END: GameState

namespace GameState

/-- The `init` procedure of Figure 5, after `k ←$ K`. -/
-- ANCHOR: gameStateInit
def init (fs : FSAEADScheme K StS StR AD M C) (k : K) : GameState StS StR AD M C where
  vA := fs.initS k
  vB := fs.initR k
  iA := 0
  corrA := false
  ended := false
  won := false
  trans := []
  chall := ∅
  comp := fun _ => false
-- ANCHOR_END: gameStateInit

/-- `record(flag, a, m, e)` of Figure 5, for the record at index `i_A`.
Correction: nothing is recorded if A is corrupted and an injection already consumed `i_A`
(removing `i_A` from `comp`). Figure 5's `comp ← rec` is dropped: past the guard, either A
is not corrupted or `i_A` is already in `comp`. -/
-- ANCHOR: gameStateRecord
def record (st : GameState StS StR AD M C) (isChall : Bool) (a : AD) (m : M) (e : C) :
    GameState StS StR AD M C :=
  if st.corrA && !st.comp st.iA then st else
  { st with
    trans := st.trans ++ [(st.iA, a, m, e)]
    chall := if isChall then insert st.iA st.chall else st.chall }
-- ANCHOR_END: gameStateRecord

/-- `delete(i)` of Figure 5: remove the record with index `i` everywhere. -/
-- ANCHOR: gameStateDelete
def delete (st : GameState StS StR AD M C) (i : ℕ) : GameState StS StR AD M C :=
  { st with
    trans := st.trans.filter (·.1 ≠ i)
    chall := st.chall.erase i
    comp := fun j => j != i && st.comp j }
-- ANCHOR_END: gameStateDelete

/-- The in-transit record `(i, a, m, e)` with the smallest index `i`. `trans` is ordered by
index, so this is its first match. Figure 5's `deliver-B` takes such a record "for some
`i, m`" and does not say which one if there are several. -/
def findTrans [DecidableEq AD] [DecidableEq C] (st : GameState StS StR AD M C)
    (a : AD) (e : C) : Option (ℕ × AD × M × C) :=
  st.trans.find? fun r => r.2.1 = a ∧ r.2.2.2 = e

end GameState

/-- Oracle spec for the FS-AEAD security game: uniform randomness, then `O-Transmit-A`,
`O-Chall-A`, `O-Corr-A`, `O-Corr-B`, `O-Deliver-B` and `O-Inject-B`. Each of the last six answers
`none` when its guard fails or after the game has ended. -/
-- ANCHOR: fsaeadSpec
abbrev fsaeadSpec (StS StR AD M C : Type) :=
  unifSpec
    + (AD × M →ₒ Option C)
    + (AD × M × M →ₒ Option C)
    + (Unit →ₒ Option StS)
    + (Unit →ₒ Option (StS × StR))
    + (AD × C →ₒ Option (ℕ × Option M))
    + (AD × C →ₒ Option (ℕ × M))
-- ANCHOR_END: fsaeadSpec

namespace fsaeadSpec

variable {StS StR AD M C : Type}

/-- Domain index selecting the uniform-randomness oracle. -/
@[match_pattern] abbrev OUnif (n : ℕ) : (fsaeadSpec StS StR AD M C).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inl n)))))
/-- Domain index selecting `O-Transmit-A`. -/
@[match_pattern] abbrev OTransmitA (am : AD × M) : (fsaeadSpec StS StR AD M C).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inr am)))))
/-- Domain index selecting `O-Chall-A`. -/
@[match_pattern] abbrev OChallA (amm : AD × M × M) : (fsaeadSpec StS StR AD M C).Domain :=
  .inl (.inl (.inl (.inl (.inr amm))))
/-- Domain index selecting `O-Corr-A`. -/
@[match_pattern] abbrev OCorrA : (fsaeadSpec StS StR AD M C).Domain :=
  .inl (.inl (.inl (.inr ())))
/-- Domain index selecting `O-Corr-B`. -/
@[match_pattern] abbrev OCorrB : (fsaeadSpec StS StR AD M C).Domain :=
  .inl (.inl (.inr ()))
/-- Domain index selecting `O-Deliver-B`. -/
@[match_pattern] abbrev ODeliverB (ae : AD × C) : (fsaeadSpec StS StR AD M C).Domain :=
  .inl (.inr ae)
/-- Domain index selecting `O-Inject-B`. -/
@[match_pattern] abbrev OInjectB (ae : AD × C) : (fsaeadSpec StS StR AD M C).Domain :=
  .inr ae

end fsaeadSpec

/-- An FS-AEAD adversary: a computation with access to the game oracles, outputting a
guess `b'` for the challenge bit. -/
-- ANCHOR: FSAEADAdversary
abbrev FSAEADAdversary (StS StR AD M C : Type) :=
  OracleComp (fsaeadSpec StS StR AD M C) Bool
-- ANCHOR_END: FSAEADAdversary

/-! ### Oracle implementations -/

/-- Game monad of the FS-AEAD security game. -/
abbrev GameM (StS StR AD M C : Type) := StateT (GameState StS StR AD M C) ProbComp

/-- Uniform-randomness oracle lifted to the game monad. -/
def oracleUnif (StS StR AD M C : Type) : QueryImpl unifSpec (GameM StS StR AD M C) :=
  unifLiftStateT (GameState StS StR AD M C) unifSpec

/-- **O-Transmit-A(a, m)**. A sends `m`, and the ciphertext is recorded as a normal one.
```text
O-Transmit-A(a, m):
  if ended: return ⊥
  i_A++
  (v_A, e) ← FS-Send(v_A, a, m)
  record(good, a, m, e)
  return e
``` -/
-- ANCHOR: oracleTransmitA
def oracleTransmitA (fs : FSAEADScheme K StS StR AD M C) :
    QueryImpl (AD × M →ₒ Option C) (GameM StS StR AD M C) :=
  fun (a, m) => do
    let st ← get
    if st.ended then return none
    let (vA, e) := fs.send st.vA a m
    set ({ st with vA, iA := st.iA + 1 }.record false a m e)
    return some e
-- ANCHOR_END: oracleTransmitA

/-- **O-Chall-A(a, m₀, m₁)**. A sends `m_b`, and the ciphertext is recorded as a challenge.
```text
O-Chall-A(a, m₀, m₁):
  if ended or corrA or |m₀| ≠ |m₁|: return ⊥
  i_A++
  (v_A, e) ← FS-Send(v_A, a, m_b)
  record(chall, a, m_b, e)
  return e
``` -/
-- ANCHOR: oracleChallA
def oracleChallA (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (b : Bool) :
    QueryImpl (AD × M × M →ₒ Option C) (GameM StS StR AD M C) :=
  fun (a, m₀, m₁) => do
    let st ← get
    if st.ended || st.corrA || len m₀ ≠ len m₁ then return none
    let m := if b then m₁ else m₀
    let (vA, e) := fs.send st.vA a m
    set ({ st with vA, iA := st.iA + 1 }.record true a m e)
    return some e
-- ANCHOR_END: oracleChallA

/-- **O-Corr-A**. Reveals A's state. On the first corruption, every index that A has not
sent yet becomes compromised.
```text
O-Corr-A:
  if ended: return ⊥
  [if ¬corrA: comp ← {i | i > i_A}]
  corrA ← true
  return v_A
``` -/
-- ANCHOR: oracleCorrA
def oracleCorrA (StS StR AD M C : Type) :
    QueryImpl (Unit →ₒ Option StS) (GameM StS StR AD M C) :=
  fun () => do
    let st ← get
    if st.ended then return none
    let comp := if st.corrA then st.comp else fun i => decide (st.iA < i)
    set { st with corrA := true, comp }
    return some st.vA
-- ANCHOR_END: oracleCorrA

/-- **O-Corr-B**. Reveals both states and ends the game.
```text
O-Corr-B:
  if ended or chall ≠ ∅: return ⊥
  ended ← true
  return (v_A, v_B)
``` -/
-- ANCHOR: oracleCorrB
def oracleCorrB (StS StR AD M C : Type) :
    QueryImpl (Unit →ₒ Option (StS × StR)) (GameM StS StR AD M C) :=
  fun () => do
    let st ← get
    if st.ended || st.chall ≠ ∅ then return none
    set { st with ended := true }
    return some (st.vA, st.vB)
-- ANCHOR_END: oracleCorrB

/-- **O-Deliver-B(a, e)**. Delivers a ciphertext that A sent. If B does not recover the
recorded index and message, the adversary wins. Challenge plaintexts are not returned.
```text
O-Deliver-B(a, e):
  if ended: return ⊥
  req (i, a, m, e) ∈ trans, with the smallest such i
  r ← FS-Rcv(v_B, a, e)
  -- correctness failure: B rejects the honest ciphertext e
  if r = ⊥: won ← true; return ⊥
  (v_B, i', m') ← r
  -- correctness failure: B outputs a wrong index or message
  if (i', m') ≠ (i, m): won ← true
  if i ∈ chall: m' ← ⊥
  delete(i)
  return (i', m')
``` -/
-- ANCHOR: oracleDeliverB
def oracleDeliverB [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (fs : FSAEADScheme K StS StR AD M C) :
    QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C) :=
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

/-- **O-Inject-B(a, e)**. Delivers any other ciphertext. If B accepts it for an index that
is not compromised (`i' ∉ comp`), the adversary wins. `delete(i')` then removes `i'` from
`comp`, so a compromised index (whether in transit or not yet sent by A) can be consumed
at most once.
```text
O-Inject-B(a, e):
  if ended or (i, a, m, e) ∈ trans for some i, m: return ⊥
  r ← FS-Rcv(v_B, a, e)
  if r = ⊥: return ⊥
  (v_B, i', m') ← r
  -- authenticity failure: B accepts a forgery at an index that is not compromised
  if i' ∉ comp: won ← true
  delete(i')
  return (i', m')
``` -/
-- ANCHOR: oracleInjectB
def oracleInjectB [DecidableEq AD] [DecidableEq C]
    (fs : FSAEADScheme K StS StR AD M C) :
    QueryImpl (AD × C →ₒ Option (ℕ × M)) (GameM StS StR AD M C) :=
  fun (a, e) => do
    let st ← get
    if st.ended || (st.findTrans a e).isSome then return none
    let some (vB, i', m') := fs.rcv st.vB a e | return none
    let won := st.won || !st.comp i'
    set ({ st with vB, won }.delete i')
    return some (i', m')
-- ANCHOR_END: oracleInjectB

/-- Complete oracle set for the FS-AEAD security game with challenge bit `b`. -/
-- ANCHOR: fsaeadSecurityImpl
def fsaeadSecurityImpl [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec StS StR AD M C) (GameM StS StR AD M C) :=
  oracleUnif StS StR AD M C
    + oracleTransmitA fs
    + oracleChallA fs len b
    + oracleCorrA StS StR AD M C
    + oracleCorrB StS StR AD M C
    + oracleDeliverB fs
    + oracleInjectB fs
-- ANCHOR_END: fsaeadSecurityImpl

/-! ### Security experiment -/

/-- **FS-AEAD security experiment** (Figure 5 of [ACD19]).

`init`:   `k ←$ K; v_A ← FS-Init-S(k); v_B ← FS-Init-R(k); b ←$ {0, 1}`
`run`:    `b' ← A^{O-Transmit-A, O-Chall-A, O-Corr-A, O-Corr-B, O-Deliver-B, O-Inject-B}`
`output`: `true` if the adversary reached a winning condition, otherwise `b' = b` -/
-- ANCHOR: securityExp
def securityExp [SampleableType K] [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ)
    (adversary : FSAEADAdversary StS StR AD M C) : ProbComp Bool := do
  let k ← $ᵗ K
  let b ← $ᵗ Bool
  let (b', st) ← (simulateQ (fsaeadSecurityImpl fs len b) adversary).run (.init fs k)
  return st.won || b == b'
-- ANCHOR_END: securityExp

/-- FS-AEAD advantage `Adv^{fs-aead}_{FS-AEAD}(A) = |Pr[securityExp = 1] - 1/2|`
(Definition 15 of [ACD19]). ACD19 §2.1 scales the advantage of indistinguishability games
by 2. The guess advantages of this project leave the factor out. -/
-- ANCHOR: advantage
noncomputable def advantage [SampleableType K] [DecidableEq AD] [DecidableEq M]
    [DecidableEq C] (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ)
    (adversary : FSAEADAdversary StS StR AD M C) : ℝ :=
  |(Pr[= true | securityExp fs len adversary]).toReal - 1 / 2|
-- ANCHOR_END: advantage

end Security

end FSAEADScheme
