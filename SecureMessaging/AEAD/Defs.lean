/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.PreservesInv

/-!
# Authenticated Encryption with Associated Data (AEAD)

Formalization of AEAD syntax, correctness, and one-time
Indistinguishability under Chosen-Ciphertext Attack (IND-CCA) security following:

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Definition 1 (AEAD syntax), Figure 1 (one-time IND-CCA game), Definition 2
  (one-time CCA security).

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
  — Definition 2.5 (AEAD advantage convention used here).

An AEAD scheme is a pair of deterministic algorithms `(Enc, Dec)` providing both
confidentiality and integrity for messages, with additional unencrypted associated data
authenticated alongside the ciphertext.

[SPACES]
- `M`: message space.
- `AD`: associated data space.
- `K`: key space.
- `C`: ciphertext space.

[ALGORITHMS]
- `keygen : m K`.
  Samples a fresh symmetric key.
- `encrypt : K → AD → M → C`.
  Deterministic encryption: given key `K`, associated data `a`, and message `m`,
  produces ciphertext `e ← Enc(K, a, m)`.
- `decrypt : K → AD → C → Option M`.
  Deterministic decryption: given key `K`, associated data `a`, and ciphertext `e`,
  produces `some m` on success or `none` on authentication failure.

[CORRECTNESS]
An AEAD scheme is correct if for all keys `K`, associated data `a`, and messages `m`:

  `Dec(K, a, Enc(K, a, m)) = m`

[SECURITY — One-Time IND-CCA]
The game samples `K ←$ K`, `e* ← ⊥`, `b ←$ {0, 1}`, then the adversary
`A^{encrypt, decrypt}` interacts with:

- A **one-time encryption oracle** `encrypt(a, m)`:
  if `b = 0`, sets `e* ← Enc(K, a, m)`; else sets `e* ←$ C`; returns `e*`.
  This oracle may be called at most once (stated in Figure 1 caption).

- A **decryption oracle** `decrypt(a, e)`:
  `if e = e* or b = 1 return ⊥; return Dec(K, a, e)`.
  When `e* = ⊥` (pre-challenge), the check `e = e*` is trivially false.

The adversary wins if its guess `b'` satisfies `b' = b`.

-/

open OracleSpec OracleComp ENNReal

-- We use only `u` in universe (for the monad),
-- matching VCVio's crypto-foundations conventions. All type-space parameters (M, AD, K, C)
-- live at `Type` (= `Type 0`).
universe u

/-- An authenticated encryption with associated data (AEAD) scheme with
message space `M`, associated-data space `AD`, key space `K`, and ciphertext space `C`.

Definition 1 of [ACD19]. -/
-- ANCHOR: AEADScheme
structure AEADScheme (m : Type → Type u) [Monad m] (M AD K C : Type) where
  /-- Sample a fresh symmetric key. -/
  keygen : m K
  /-- Deterministic encryption: `Enc(K, a, m) = e`. -/
  encrypt : K → AD → M → C
  /-- Deterministic authenticated decryption: `Dec(K, a, e) = some m` or `none`. -/
  decrypt : K → AD → C → Option M
-- ANCHOR_END: AEADScheme

namespace AEADScheme

variable {m : Type → Type u} [Monad m] {M AD K C : Type}

/-- An AEAD scheme is correct if decryption always recovers the plaintext:
`∀ K a m, Dec(K, a, Enc(K, a, m)) = m`. -/
-- ANCHOR: Correct
def Correct (ae : AEADScheme m M AD K C) : Prop :=
  ∀ (k : K) (a : AD) (msg : M), ae.decrypt k a (ae.encrypt k a msg) = some msg
-- ANCHOR_END: Correct

section OneTime_CCA

/-! ## One-Time IND-CCA Security Game

The adversary `A` interacts with two stateful oracles:
- `encrypt(a, m)`: one-time encryption oracle.
- `decrypt(a, e)`: decryption oracle.

The game state is a single `Option C` value tracking the challenge ciphertext
(`none` = `encrypt` not yet called; `some e` = challenge ciphertext is `e`).
-/

variable {M AD K C : Type}

/-! ### Oracle spec -/

/-- Oracle spec for the AEAD one-time IND-CCA game (Figure 1 of [ACD19]).
The adversary has access to uniform randomness, a one-time encryption oracle,
and a decryption oracle. -/
-- ANCHOR: aeadOneTimeCCASpec
def aeadOneTimeCCASpec (AD M C : Type) :=
  unifSpec + (AD × M →ₒ Option C) + (AD × C →ₒ Option M)
-- ANCHOR_END: aeadOneTimeCCASpec

namespace aeadOneTimeCCASpec

variable {AD M C : Type}

/-- Domain index selecting the uniform-randomness oracle. -/
@[match_pattern] abbrev OUnif (n : ℕ) : (aeadOneTimeCCASpec AD M C).Domain :=
  .inl (.inl n)
/-- Domain index selecting the encryption oracle. -/
@[match_pattern] abbrev OEncrypt (am : AD × M) : (aeadOneTimeCCASpec AD M C).Domain :=
  .inl (.inr am)
/-- Domain index selecting the decryption oracle. -/
@[match_pattern] abbrev ODecrypt (ac : AD × C) : (aeadOneTimeCCASpec AD M C).Domain :=
  .inr ac

end aeadOneTimeCCASpec

/-! ### Adversary -/

/-- One-time IND-CCA adversary for an AEAD scheme: a single computation with
access to `encrypt` and `decrypt` oracles, outputting a guess bit `b'`.
Matches the adversary `A` in ACD19 Figure 1 + Definition 2. -/
-- ANCHOR: OneTime_CCA_Adversary
abbrev OneTime_CCA_Adversary (AD M C : Type) :=
  OracleComp (aeadOneTimeCCASpec AD M C) Bool
-- ANCHOR_END: OneTime_CCA_Adversary

/-! ### Oracle implementations -/

/-- Uniform-randomness oracle lifted to the game-state monad. -/
def oracleUnif (C : Type) :
    QueryImpl unifSpec (StateT (Option C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Option C) ProbComp)

/-- One-time encryption oracle `encrypt(a, m)` (Figure 1 of [ACD19], middle column).
First call: if `b = false`, sets `e* ← Enc(K, a, m)`;
            if `b = true`,  sets `e* ←$ C`.
            Returns `some e*`.
Subsequent calls: returns `none` (one-time oracle). -/
-- ANCHOR: oracleEncrypt
def oracleEncrypt [SampleableType C] (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) :
    QueryImpl (AD × M →ₒ Option C) (StateT (Option C) ProbComp) :=
  fun (a, m) => do
    match (← get) with
    | some _ => pure none
    | none =>
      let eStar ← if b
        then liftM ($ᵗ C : ProbComp C)
        else pure (ae.encrypt k a m)
      set (some eStar)
      return some eStar
-- ANCHOR_END: oracleEncrypt

/-- Decryption oracle `decrypt(a, e)` (Figure 1 of [ACD19], right column).
`if e = e* or b = 1 return ⊥; return Dec(K, a, e)`.
When `eStar = none` (pre-challenge), the `e = e*` check is trivially false. -/
-- ANCHOR: oracleDecrypt
def oracleDecrypt [DecidableEq C] (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) :
    QueryImpl (AD × C →ₒ Option M) (StateT (Option C) ProbComp) :=
  fun (a, e) => do
    if b || (← get) == some e then pure none
    else pure (ae.decrypt k a e)
-- ANCHOR_END: oracleDecrypt

/-- Complete oracle set for the one-time IND-CCA game (Figure 1 of [ACD19]). -/
-- ANCHOR: aeadSecurityImpl
def aeadSecurityImpl [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C) (b : Bool) (k : K) :
    QueryImpl (aeadOneTimeCCASpec AD M C) (StateT (Option C) ProbComp) :=
  oracleUnif C + oracleEncrypt ae b k + oracleDecrypt ae b k
-- ANCHOR_END: aeadSecurityImpl

/-! ### Security experiment -/

/-- **One-time IND-CCA experiment** (Figure 1 + Definition 2 of [ACD19]).

`init`:   `K ←$ K; e* ← ⊥; b ←$ {0, 1}`
`run`:    `b' ← A^{encrypt, decrypt}`
`output`: `b' = b` -/
-- ANCHOR: securityExp
def securityExp [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C) : ProbComp Bool := do
  let k ← ae.keygen
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (aeadSecurityImpl ae b k) adversary).run none
  return (b == b')
-- ANCHOR_END: securityExp

/-- One-time IND-CCA guess advantage: `|Pr[b' = b] - 1/2|`. -/
-- ANCHOR: guessAdvantage
noncomputable def guessAdvantage [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C) : ℝ :=
  |(Pr[= true | securityExp ae adversary]).toReal - 1 / 2|
-- ANCHOR_END: guessAdvantage

/-! ### Useful security game decomposition -/

/-- Security experiment with a fixed challenge bit `b` (not sampled uniformly).
The branch `b = false` is `AEAD_real`; the branch `b = true` is `AEAD_rand`.
Returns the adversary's raw guess `b'` (not `b == b'`). -/
def securityExpFixedBit [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C)
    (b : Bool) : ProbComp Bool := do
  let k ← ae.keygen
  let (b', _) ← (simulateQ (aeadSecurityImpl ae b k) adversary).run none
  return b'

/-- One-time IND-CCA distinguishing advantage:
`|Pr[AEAD_rand = 1] - Pr[AEAD_real = 1]|`.

Here `AEAD_real` is `securityExpFixedBit ae adversary false` and `AEAD_rand`
is `securityExpFixedBit ae adversary true`. -/
noncomputable def distAdvantage [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C) : ℝ :=
  |(Pr[= true | securityExpFixedBit ae adversary true]).toReal -
   (Pr[= true | securityExpFixedBit ae adversary false]).toReal|

/-- The single-game AEAD experiment can be decomposed as a uniform-bit branch over
the two fixed-bit experiments:

  `Pr[Exp^{ot-cca}(ae, A) = 1]`
    `= Pr[b ←$ {0,1}; b' ← (if b then AEAD_rand else AEAD_real); output (b = b')]`.

Here `AEAD_real` abbreviates `securityExpFixedBit ae adversary false`, and
`AEAD_rand` abbreviates `securityExpFixedBit ae adversary true`; each branch
returns the adversary's raw guess `b'`. Proved by swapping `b ← $ᵗ Bool` past
the key-generation step using `probEvent_bind_bind_swap`. -/
private lemma securityExp_probOutput_eq_branch [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C) :
    Pr[= true | securityExp ae adversary] =
    Pr[= true | do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then securityExpFixedBit ae adversary true
               else securityExpFixedBit ae adversary false
      pure (b == z)] := by
  unfold securityExp
  simp only [← probEvent_eq_eq_probOutput]
  rw [probEvent_bind_bind_swap]
  simp only [probEvent_eq_eq_probOutput]
  refine probOutput_bind_congr' ($ᵗ Bool) true ?_
  intro b; cases b <;> simp [securityExpFixedBit]

/-- The centered success probability of the single-bit experiment decomposes
as the difference of the random and real fixed-bit branches:
`Pr[Exp^{ot-cca} = 1] - 1/2 =
  (Pr[AEAD_rand = 1] - Pr[AEAD_real = 1]) / 2`.
Here `AEAD_rand` is `securityExpFixedBit ae adversary true`, and `AEAD_real`
is `securityExpFixedBit ae adversary false`; both return the adversary's
raw guess. -/
private lemma securityExp_toReal_sub_half [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C) :
    (Pr[= true | securityExp ae adversary]).toReal - 1 / 2 =
    ((Pr[= true | securityExpFixedBit ae adversary true]).toReal -
     (Pr[= true | securityExpFixedBit ae adversary false]).toReal) / 2 := by
  rw [show (Pr[= true | securityExp ae adversary]).toReal =
      (Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let z ← if b then securityExpFixedBit ae adversary true
                 else securityExpFixedBit ae adversary false
        pure (b == z)]).toReal from by
    congr 1; exact securityExp_probOutput_eq_branch ae adversary]
  exact probOutput_uniformBool_branch_toReal_sub_half
    (securityExpFixedBit ae adversary true)
    (securityExpFixedBit ae adversary false)

-- ANCHOR: guessAdvantage_eq_distAdvantage_div_two
/-- The guess advantage equals half the distinguishing advantage:
`guessAdvantage = distAdvantage / 2`. -/
lemma guessAdvantage_eq_distAdvantage_div_two [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C) :
    guessAdvantage ae adversary = distAdvantage ae adversary / 2 := by
  simp only [guessAdvantage, distAdvantage]
  rw [securityExp_toReal_sub_half, abs_div]
  congr 1
  exact abs_of_pos two_pos
-- ANCHOR_END: guessAdvantage_eq_distAdvantage_div_two

end OneTime_CCA

end AEADScheme
