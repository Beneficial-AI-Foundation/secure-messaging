/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import ToVCVio.EvalDist.Monad.Basic
import ToVCVio.OracleComp.SimSemantics.UnifLift

/-!
# Authenticated Encryption with Associated Data (AEAD)

Formalization of AEAD syntax, correctness, and one-time
Indistinguishability under Chosen-Ciphertext Attack (IND-CCA) security following:

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Definition 1 (AEAD syntax), Figure 1 (one-time IND-CCA game), Definition 2
  (one-time CCA security). ACD19 only defines this notion (AEAD is assumed as a
  primitive); the construction and proof are ours, following NRS14 — see
  `AEAD/FromEtM/Security`.

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
  — Definition 2.5 (AEAD advantage convention used here).

- [NRS14] Namprempre, Rogaway, Shrimpton.
  *Reconsidering Generic Composition.*
  EUROCRYPT 2014, https://eprint.iacr.org/2014/206

- [BS] Boneh, Shoup.
  *A Graduate Course in Applied Cryptography*, version 0.6, 2023.
  — Definition 9.10 (CCA security with associated data).

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
The game samples `K ←$ K`, `(a*, e*) ← ⊥`, `b ←$ {0, 1}`, then the adversary
`A^{encrypt, decrypt}` interacts with:

- A **one-time encryption oracle** `encrypt(a, m)`:
  sets `a* ← a`; if `b = 0`, sets `e* ← Enc(K, a, m)`; else sets `e* ←$ C`; returns `e*`.
  This oracle may be called at most once (stated in Figure 1 caption).

- A **decryption oracle** `decrypt(a, e)`:
  `if (a, e) = (a*, e*) or b = 1 return ⊥; return Dec(K, a, e)`.
  When no challenge has been issued, the check is trivially false.

The adversary wins if its guess `b'` satisfies `b' = b`.

[DEVIATIONS FROM ACD19]
The deviation is marked `Deviation (D1)` where it takes effect.

- (D1) The challenge is the pair `(a*, e*)`, not the ciphertext `e*` alone. Two oracle lines
  change:

  ```
             ACD19 Figure 1                    here
  encrypt    e* ← …                            a* ← a;  e* ← …
  decrypt    if e = e* or b = 1 return ⊥       if (a, e) = (a*, e*) or b = 1 return ⊥
  ```

  The game state is therefore `Option (AD × C)`, and `AD` needs decidable equality.

  Reason. The ACD19 guard `e = e*` refuses every decryption query `(a, e*)`, for every associated
  data `a`. The ACD19 game therefore never tests whether `e*` decrypts under associated data
  other than `a*`, so the ACD19 notion accepts schemes that ignore associated data. For example,
  let `AE = (Enc, Dec)` be secure in the ACD19 game, fix some associated data `ā`, and define
  `AE' = (Enc', Dec')` by `Enc'(K, a, m) = Enc(K, ā, m)` and `Dec'(K, a, e) = Dec(K, ā, e)`.

  1. `AE'` is secure in the ACD19 game. An adversary against `AE'` becomes an adversary against
     `AE` with the same advantage: it replaces the associated data of every query by `ā`.
  2. The FS-AEAD scheme of [ACD19] Figure 6, built on `AE'`, is insecure in the game of [ACD19]
     Figure 5. The adversary calls `transmit-A(a, m)` and receives `c = (1, e)`, where
     `e = Enc'(K, (1, a), m)`. Before `c` is delivered, it calls `inject-B(a', c)` with
     `a' ≠ a`. The pair `(a', c)` is not in `trans`, and `FS-Rcv` computes
     `Dec'(K, (1, a'), e) = Dec(K, ā, e) = m ≠ ⊥`. Epoch 1 is not in `comp`, so the adversary
     wins.

  Items 1 and 2 contradict Theorem 5 of [ACD19] as printed. With the guard
  `(a, e) = (a*, e*)`, `AE'` is insecure: the adversary encrypts `(a, m)`, receives `e*`, and
  queries `decrypt(a', e*)` with `a' ≠ a`. The query returns `m` if `b = 0` and `⊥` if `b = 1`.
  [NRS14] and Definition 9.10 of [BS] restrict decryption queries in the same way: only the
  exact pair returned by encryption is refused.

[WHY A PRF TAG, NOT JUST A MAC]
The game above is *real-or-random*: when `b = 1` the oracle returns a uniform random
ciphertext `e* ←$ C`, so the **whole** ciphertext — authentication tag included — must be
indistinguishable from uniform. MAC unforgeability cannot deliver this (an unforgeable tag
may still look non-uniform); pseudorandomness can. So the `AEAD/FromEtM` construction tags
with a PRF, not a MAC. The textbook "LoR ⇒ RoR" shortcut does not bridge the gap: it is for
random-*message* RoR, whereas ACD19 is random-*ciphertext* IND$, strictly stronger than LoR.

-/

open ToVCVio OracleSpec OracleComp ENNReal

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

The game state is a single `Option (AD × C)` value tracking the challenge
(`none` = `encrypt` not yet called; `some (a, e)` = the challenge was `e` under
associated data `a`).
-/

variable {M AD K C : Type}

/-! ### Oracle spec -/

/-- Oracle spec for the AEAD one-time IND-CCA game (Figure 1 of [ACD19]).
The adversary has access to uniform randomness, a one-time encryption oracle,
and a decryption oracle. -/
-- ANCHOR: aeadOneTimeCCASpec
abbrev aeadOneTimeCCASpec (AD M C : Type) :=
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
-- ANCHOR: OneTimeCCAAdversary
abbrev OneTimeCCAAdversary (AD M C : Type) :=
  OracleComp (aeadOneTimeCCASpec AD M C) Bool
-- ANCHOR_END: OneTimeCCAAdversary

/-- Structural bound on the number of decrypt-oracle queries made by a
one-time IND-CCA adversary. `decryptQueryBound adv q_d` asserts that `adv`
makes at most `q_d` queries to the decrypt oracle (index `.inr _` in
`aeadOneTimeCCASpec`), with no constraint on encryption or uniform-sampling
queries. Built on VCVio's `IsQueryBoundP`. -/
-- ANCHOR: decryptQueryBound
def decryptQueryBound (adv : OneTimeCCAAdversary AD M C)
    (q_d : ℕ) : Prop :=
  adv.IsQueryBoundP (· matches Sum.inr _) q_d
-- ANCHOR_END: decryptQueryBound

/-! ### Oracle implementations -/

/-- Uniform-randomness oracle lifted to the game-state monad. -/
def oracleUnif (AD C : Type) :
    QueryImpl unifSpec (StateT (Option (AD × C)) ProbComp) :=
  unifLiftStateT (Option (AD × C)) unifSpec

/-- One-time encryption oracle `encrypt(a, m)` (Figure 1 of [ACD19], middle column).
First call: if `b = false`, sets `e* ← Enc(K, a, m)`;
            if `b = true`,  sets `e* ←$ C`.
            Records `(a, e*)` and returns `some e*`.
Subsequent calls: returns `none` (one-time oracle). -/
-- ANCHOR: oracleEncrypt
def oracleEncrypt [SampleableType C] (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) :
    QueryImpl (AD × M →ₒ Option C) (StateT (Option (AD × C)) ProbComp) :=
  fun (a, m) => do
    match (← get) with
    | some _ => pure none
    | none =>
      let eStar ← if b
        then liftM ($ᵗ C : ProbComp C)
        else pure (ae.encrypt k a m)
      set (some (a, eStar))
      return some eStar
-- ANCHOR_END: oracleEncrypt

/-- Decryption oracle `decrypt(a, e)` (Figure 1 of [ACD19], right column, with the guard
on the pair): `if (a, e) = (a*, e*) or b = 1 return ⊥; return Dec(K, a, e)`.
Before the challenge the state is `none` and the guard is trivially false.
Deviation (D1): Figure 1 compares `e` only. -/
-- ANCHOR: oracleDecrypt
def oracleDecrypt [DecidableEq AD] [DecidableEq C] (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) :
    QueryImpl (AD × C →ₒ Option M) (StateT (Option (AD × C)) ProbComp) :=
  fun (a, e) => do
    let chal ← get
    if b || chal == some (a, e) then pure none
    else pure (ae.decrypt k a e)
-- ANCHOR_END: oracleDecrypt

/-- Complete oracle set for the one-time IND-CCA game (Figure 1 of [ACD19]). -/
-- ANCHOR: aeadSecurityImpl
def aeadSecurityImpl [SampleableType C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C) (b : Bool) (k : K) :
    QueryImpl (aeadOneTimeCCASpec AD M C) (StateT (Option (AD × C)) ProbComp) :=
  oracleUnif AD C + oracleEncrypt ae b k + oracleDecrypt ae b k
-- ANCHOR_END: aeadSecurityImpl

/-! ### Security experiment -/

/-- **One-time IND-CCA experiment** (Figure 1 + Definition 2 of [ACD19]).

`init`:   `K ←$ K; e* ← ⊥; b ←$ {0, 1}`
`run`:    `b' ← A^{encrypt, decrypt}`
`output`: `b' = b` -/
-- ANCHOR: securityExp
def securityExp [SampleableType C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) : ProbComp Bool := do
  let k ← ae.keygen
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (aeadSecurityImpl ae b k) adversary).run none
  return (b == b')
-- ANCHOR_END: securityExp

/-- One-time IND-CCA guess advantage: `|Pr[b' = b] - 1/2|`. -/
-- ANCHOR: guessAdvantage
noncomputable def guessAdvantage [SampleableType C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) : ℝ :=
  |(Pr{let x ← securityExp ae adversary}[x = true]).toReal - 1 / 2|
-- ANCHOR_END: guessAdvantage

/-! ### Useful security game decomposition -/

/-- Security experiment with a fixed challenge bit `b` (not sampled uniformly).
The branch `b = false` is `AEAD_real`; the branch `b = true` is `AEAD_rand`.
Returns the adversary's raw guess `b'` (not `b == b'`). -/
-- ANCHOR: securityExpFixedBit
def securityExpFixedBit [SampleableType C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C)
    (b : Bool) : ProbComp Bool := do
  let k ← ae.keygen
  let (b', _) ← (simulateQ (aeadSecurityImpl ae b k) adversary).run none
  return b'
-- ANCHOR_END: securityExpFixedBit

/-- One-time IND-CCA distinguishing advantage:
`|Pr[AEAD_rand = 1] - Pr[AEAD_real = 1]|`.

Here `AEAD_real` is `securityExpFixedBit ae adversary false` and `AEAD_rand`
is `securityExpFixedBit ae adversary true`. -/
-- ANCHOR: distAdvantage
noncomputable def distAdvantage [SampleableType C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) : ℝ :=
  |(Pr{let x ← securityExpFixedBit ae adversary true}[x = true]).toReal -
   (Pr{let x ← securityExpFixedBit ae adversary false}[x = true]).toReal|
-- ANCHOR_END: distAdvantage


/-- The single-game AEAD experiment is equal in distribution to a uniform-bit branch over
the two fixed-bit experiments:

  `Exp^{ot-cca}(ae, A) =ᵈ (b ←$ {0,1}; b' ← (if b then AEAD_rand else AEAD_real); output (b = b'))`.

Here `AEAD_real` abbreviates `securityExpFixedBit ae adversary false`, and
`AEAD_rand` abbreviates `securityExpFixedBit ae adversary true`; each branch
returns the adversary's raw guess `b'`. Proved by swapping `b ← $ᵗ Bool` past
the key-generation step using `OracleComp.EvalDistEq.bind_bind_swap`. -/
private lemma securityExp_evalDistEq_branch
    [SampleableType C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) :
    securityExp ae adversary =ᵈ (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then securityExpFixedBit ae adversary true
               else securityExpFixedBit ae adversary false
      pure (b == z)) := by
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun b => ?_
  cases b <;> simp only [securityExpFixedBit, bind_assoc, pure_bind] <;> exact EvalDistEq.refl _

/-- The centered success probability of the single-bit experiment decomposes
as the difference of the random and real fixed-bit branches:
`Pr[Exp^{ot-cca} = 1] - 1/2 =
  (Pr[AEAD_rand = 1] - Pr[AEAD_real = 1]) / 2`.
Here `AEAD_rand` is `securityExpFixedBit ae adversary true`, and `AEAD_real`
is `securityExpFixedBit ae adversary false`; both return the adversary's
raw guess. -/
private lemma securityExp_toReal_sub_half
    [SampleableType C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) :
    (Pr{let x ← securityExp ae adversary}[x = true]).toReal - 1 / 2 =
    ((Pr{let x ← securityExpFixedBit ae adversary true}[x = true]).toReal -
     (Pr{let x ← securityExpFixedBit ae adversary false}[x = true]).toReal) / 2 := by
  rw [(securityExp_evalDistEq_branch ae adversary).prEvent_eq]
  exact ToVCVio.prEvent_uniformBool_branch_toReal_sub_half
    (securityExpFixedBit ae adversary true)
    (securityExpFixedBit ae adversary false)

/-- The guess advantage equals half the distinguishing advantage:
`guessAdvantage = distAdvantage / 2`. -/
-- ANCHOR: guessAdvantage_eq_distAdvantage_div_two
lemma guessAdvantage_eq_distAdvantage_div_two
    [SampleableType C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) :
    guessAdvantage ae adversary = distAdvantage ae adversary / 2
-- ANCHOR_END: guessAdvantage_eq_distAdvantage_div_two
  := by
  simp only [guessAdvantage, distAdvantage]
  rw [securityExp_toReal_sub_half, abs_div]
  congr 1
  exact abs_of_pos two_pos

end OneTime_CCA

end AEADScheme
