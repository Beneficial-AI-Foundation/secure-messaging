/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append

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
  Note: Definition 1 of [ACD19] writes `Dec(K, a, e) = m` without an explicit
  failure case in the syntax, but implicitly expects `⊥` on invalid ciphertexts
  (see modeling note 3 below).

[CORRECTNESS]
An AEAD scheme is correct if for all keys `K`, associated data `a`, and messages `m`:

  `Dec(K, a, Enc(K, a, m)) = m`

[SECURITY — One-Time IND-CCA]
The security game (Figure 1 of [ACD19]) samples a hidden challenge bit
`b ←$ {0, 1}` and provides the adversary with:

- A **one-time encryption oracle** that returns either `Enc(K, a, m)` (if `b = 0`)
  or a uniformly random ciphertext from `C` (if `b = 1`).
- A **decryption oracle** that returns `Dec(K, a, e)` when `b = 0` and
  `e ≠ e*` (the challenge ciphertext), and `⊥` otherwise.

The adversary wins by outputting a guess `b'` such that `b' = b`.

**Important:** Unlike standard IND-CCA games (e.g., VCVio's `AsymmEncAlg.IND_CCA`),
the decrypt oracle in the `b = 1` (random) world returns `⊥` on **all** queries —
even those made *before* the challenge. This is faithful to Figure 1 of [ACD19],
which defines:

  `decrypt(a, e): if e = e* or b = 1 return ⊥; return Dec(K, a, e)`

We model the one-time encrypt constraint structurally via a **two-phase adversary**,
following VCVio's `AsymmEncAlg.IND_CCA_Adversary`:

- Phase 1 (`chooseMessage`): adversary picks `(a, m)` for the challenge.
- Phase 2 (`distinguish`): adversary receives challenge ciphertext `e*` and guesses `b`.

Both phases have access to the (b-gated) decrypt oracle. This two-phase structure
captures the same adversary power as the paper's single oracle interface: any
single-interface adversary that calls encrypt exactly once can be split into a
pre-challenge phase (producing the message) and a post-challenge phase
(distinguishing). The one-time encrypt constraint becomes syntactic rather than
enforced by game state.

## Modeling notes

1. **`keygen` is included in the scheme.** Definition 1 of [ACD19] defines
   `AE = (Enc, Dec)` without key generation. We include `keygen : m K` for
   self-containment (the security game requires it), matching VCVio conventions
   (`SymmEncAlg`, `MacAlg`, etc.).

2. **`b = true` ↔ paper's `b = 1`** (random ciphertext, no decrypt).

3. **`Option M` return on decrypt.** Definition 1 of [ACD19] writes
   `Dec(K, a, e) = m` without an explicit failure case in the syntax.
   However, the paper's own constructions and proofs implicitly treat `⊥` as
   a valid output of `Dec`: Figure 6 (FS-AEAD from AEAD) calls `Dec(K, h, e)`
   and checks `if m = ⊥ → error`, the security proof of Theorem 5 (Hybrid H3)
   relies on "injections are always rejected," and Definition 7 Property (A)
   requires `Rcv` state to be unchanged when `m = ⊥`.

4. **Deterministic algorithms.** All AEAD schemes in [ACD19] are deterministic;
   all randomness stems from the key `K`. Hence `encrypt` and `decrypt` are pure
   functions, not monadic. Only `keygen` lives in the monad `m`.

-/

open OracleSpec OracleComp ENNReal

-- Unlike CKA/Defs.lean which declares `universe u v`, we use only `u` (for the monad),
-- matching VCVio's crypto-foundations conventions. All type-space parameters (M, AD, K, C)
-- live at `Type` (= `Type 0`). The extra `v` in CKA is unused and can be added here later
-- if needed without breaking changes.
universe u

/-- An authenticated encryption with associated data (AEAD) scheme with
message space `M`, associated-data space `AD`, key space `K`, and ciphertext space `C`.

Definition 1 of [ACD19]. -/
structure AEADScheme (m : Type → Type u) [Monad m] (M AD K C : Type) where
  /-- Sample a fresh symmetric key. -/
  keygen : m K
  /-- Deterministic encryption: `Enc(K, a, m) = e`. -/
  encrypt : K → AD → M → C
  /-- Deterministic authenticated decryption: `Dec(K, a, e) = some m` or `none`. -/
  decrypt : K → AD → C → Option M

namespace AEADScheme

variable {m : Type → Type u} [Monad m] {M AD K C : Type}

/-- An AEAD scheme is correct if decryption always recovers the plaintext:
`∀ K a m, Dec(K, a, Enc(K, a, m)) = m`. -/
def Correct (ae : AEADScheme m M AD K C) : Prop :=
  ∀ (k : K) (a : AD) (msg : M), ae.decrypt k a (ae.encrypt k a msg) = some msg

section OT_CCA

/-! ## One-Time IND-CCA Security Game

Figure 1 and Definition 2 of [ACD19].

The adversary interacts with two oracles:
- A **one-time encryption oracle** (modeled structurally via the two-phase adversary).
- A **decryption oracle** `(AD × C →ₒ Option M)`, gated by the challenge bit `b`:
  - When `b = false` (real world): decrypts normally (post-challenge: rejects `e*`).
  - When `b = true` (random world): always returns `none`.

See the module docstring for a detailed discussion of why the decrypt oracle is
b-dependent, and how this differs from standard IND-CCA games.
-/

variable {M AD K C : Type}

/-- Oracle spec for the AEAD one-time IND-CCA game.
The adversary has access to uniform randomness and a decryption oracle. -/
def aeadOTCCASpec (AD C M : Type) := unifSpec + (AD × C →ₒ Option M)

namespace aeadOTCCASpec

variable {AD C M : Type}

@[match_pattern] abbrev OUnif (n : ℕ) : (aeadOTCCASpec AD C M).Domain :=
  .inl n
@[match_pattern] abbrev ODecrypt (ac : AD × C) : (aeadOTCCASpec AD C M).Domain :=
  .inr ac

end aeadOTCCASpec

/-- Two-phase one-time IND-CCA adversary for an AEAD scheme.

- `chooseMessage`: the adversary picks associated data `a` and message `m` for the
  challenge encryption, with access to the (b-gated) decrypt oracle.
  Returns `(a, m, state)`.
- `distinguish`: after receiving the challenge ciphertext `e*`, the adversary
  guesses the challenge bit `b`, with access to the (b-gated, e*-rejecting)
  decrypt oracle. Returns `b'`. -/
structure OT_CCA_Adversary (AD M C : Type) where
  /-- Internal adversary state passed between phases. -/
  State : Type
  /-- Phase 1: choose the challenge `(a, m)` pair. -/
  chooseMessage : OracleComp (aeadOTCCASpec AD C M) (AD × M × State)
  /-- Phase 2: given internal state and challenge ciphertext, guess the bit. -/
  distinguish : State → C → OracleComp (aeadOTCCASpec AD C M) Bool

/-! ### Decrypt oracle implementations

The decrypt oracle behavior depends on the challenge bit `b`:
- `b = false` (real world): decrypt normally.
- `b = true` (random world): always return `none`.

Post-challenge, the oracle additionally rejects queries on the challenge
ciphertext `cStar` (when `b = false`). -/

/-- Pre-challenge decryption oracle.
In the real world (`b = false`), decrypts using `ae.decrypt k a c`.
In the random world (`b = true`), returns `none` on all queries. -/
def preChallengeDecryptImpl (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) :
    QueryImpl (AD × C →ₒ Option M) ProbComp :=
  fun (a, c) => if b then pure none else pure (ae.decrypt k a c)

/-- Post-challenge decryption oracle.
In the real world (`b = false`), decrypts unless `c = cStar`.
In the random world (`b = true`), returns `none` on all queries. -/
def postChallengeDecryptImpl [DecidableEq C] (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) (cStar : C) :
    QueryImpl (AD × C →ₒ Option M) ProbComp :=
  fun (a, c) => if b || c == cStar then pure none else pure (ae.decrypt k a c)

/-- Pre-challenge oracle set: uniform randomness + b-gated decrypt. -/
def preChallengeImpl (ae : AEADScheme ProbComp M AD K C) (b : Bool) (k : K) :
    QueryImpl (aeadOTCCASpec AD C M) ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) +
    preChallengeDecryptImpl ae b k

/-- Post-challenge oracle set: uniform randomness + b-gated, e*-rejecting decrypt. -/
def postChallengeImpl [DecidableEq C] (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) (cStar : C) :
    QueryImpl (aeadOTCCASpec AD C M) ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) +
    postChallengeDecryptImpl ae b k cStar

/-! ### Security experiment -/

/-- **One-time IND-CCA experiment** `Exp^{ot-cca}(ae, A)`.

Figure 1 of [ACD19].

1. `k ← ae.keygen`
2. `b ← $ᵗ Bool` — challenge bit (`true` = random world)
3. `(a, m, st) ← A₁^{Dec_b}()` — adversary picks challenge
4. `e* ← if b then $ᵗ C else pure (ae.encrypt k a m)` — challenge ciphertext
5. `b' ← A₂^{Dec_{b,e*}}(st, e*)` — adversary guesses
6. `output (b = b')` -/
def securityExp [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OT_CCA_Adversary AD M C) : ProbComp Bool := do
  let k ← ae.keygen
  let b ← $ᵗ Bool
  let (a, msg, st) ← simulateQ (preChallengeImpl ae b k) adversary.chooseMessage
  let cStar ← if b then $ᵗ C else pure (ae.encrypt k a msg)
  let b' ← simulateQ (postChallengeImpl ae b k cStar)
    (adversary.distinguish st cStar)
  return (b == b')

/-- One-time IND-CCA advantage: `|Pr[Win] - 1/2|`.

Definition 2 of [ACD19]. -/
noncomputable def securityAdvantage [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OT_CCA_Adversary AD M C) : ℝ :=
  |(Pr[= true | securityExp ae adversary]).toReal - 1 / 2|

/-! ### Useful security game decomposition -/

/-- Security experiment with a fixed challenge bit `b` (not sampled uniformly).
The branch `b = false` is `AEAD_real`; the branch `b = true` is `AEAD_rand`.
Returns the adversary's raw guess `b'` (not `b == b'`). -/
def securityExpFixedBit [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OT_CCA_Adversary AD M C)
    (b : Bool) : ProbComp Bool := do
  let k ← ae.keygen
  let (a, msg, st) ← simulateQ (preChallengeImpl ae b k) adversary.chooseMessage
  let cStar ← if b then $ᵗ C else pure (ae.encrypt k a msg)
  let b' ← simulateQ (postChallengeImpl ae b k cStar)
    (adversary.distinguish st cStar)
  return b'

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
    (adversary : OT_CCA_Adversary AD M C) :
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
lemma securityExp_toReal_sub_half [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OT_CCA_Adversary AD M C) :
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

end OT_CCA

end AEADScheme
