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

universe u

/-- **Definition 1** ([ACD19]).
An **AEAD scheme** Π = (`keygen`, `encrypt`, `decrypt`) over spaces
(`M`, `AD`, `K`, `C`) consists of a probabilistic key-generation algorithm
and deterministic encryption/decryption algorithms. -/
structure AEADScheme (m : Type → Type u) [Monad m] (M AD K C : Type) where
  /-- `KeyGen() → K`. -/
  keygen : m K
  /-- `Enc(K, a, m) → e`. -/
  encrypt : K → AD → M → C
  /-- `Dec(K, a, e) → m | ⊥`. -/
  decrypt : K → AD → C → Option M
namespace AEADScheme

variable {m : Type → Type u} [Monad m] {M AD K C : Type}

/-- **Correctness** ([ACD19], Definition 1).
∀ k ∈ K, a ∈ AD, m ∈ M : `Dec(k, a, Enc(k, a, m)) = m`. -/
def Correct (ae : AEADScheme m M AD K C) : Prop :=
  ∀ (k : K) (a : AD) (msg : M), ae.decrypt k a (ae.encrypt k a msg) = some msg
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

/-- **Oracle interface** for the one-time IND-CCA game (Figure 1, [ACD19]).
The adversary 𝒜 has access to oracles `(unifSpec, Encrypt, Decrypt)`. -/
def aeadOneTimeCCASpec (AD M C : Type) :=
  unifSpec + (AD × M →ₒ Option C) + (AD × C →ₒ Option M)
namespace aeadOneTimeCCASpec

variable {AD M C : Type}

@[match_pattern] abbrev OUnif (n : ℕ) : (aeadOneTimeCCASpec AD M C).Domain :=
  .inl (.inl n)
@[match_pattern] abbrev OEncrypt (am : AD × M) : (aeadOneTimeCCASpec AD M C).Domain :=
  .inl (.inr am)
@[match_pattern] abbrev ODecrypt (ac : AD × C) : (aeadOneTimeCCASpec AD M C).Domain :=
  .inr ac

end aeadOneTimeCCASpec

/-! ### Adversary -/

/-- Adversary `𝒜` for the one-time IND-CCA game: a probabilistic
computation with oracle access to (`Encrypt`, `Decrypt`), outputting
a guess bit `b'` ∈ {0, 1} (Figure 1, [ACD19]). -/
abbrev OneTime_CCA_Adversary (AD M C : Type) :=
  OracleComp (aeadOneTimeCCASpec AD M C) Bool

/-! ### Oracle implementations -/

/-- Uniform-randomness oracle lifted to the game-state monad. -/
def oracleUnif (C : Type) :
    QueryImpl unifSpec (StateT (Option C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Option C) ProbComp)

/-- **Encrypt oracle** (Figure 1, [ACD19], middle column).

On first query `(a, m)`:
- if `b = 0`: `e* ← Enc(K, a, m)`
- if `b = 1`: `e* ←$ C`
- return `some e*`

On subsequent queries: return `none` (one-time). -/
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
/-- **Decrypt oracle** (Figure 1, [ACD19], right column).

On query `(a, e)`:
- if `e = e*` or `b = 1`: return `⊥`
- else: return `Dec(K, a, e)` -/
def oracleDecrypt [DecidableEq C] (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) :
    QueryImpl (AD × C →ₒ Option M) (StateT (Option C) ProbComp) :=
  fun (a, e) => do
    if b || (← get) == some e then pure none
    else pure (ae.decrypt k a e)
/-- Combined oracle implementation `𝒪_b = (unifSpec, Encrypt_b, Decrypt_b)` for the
one-time IND-CCA game (Figure 1, [ACD19]). -/
def aeadSecurityImpl [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C) (b : Bool) (k : K) :
    QueryImpl (aeadOneTimeCCASpec AD M C) (StateT (Option C) ProbComp) :=
  oracleUnif C + oracleEncrypt ae b k + oracleDecrypt ae b k

/-! ### Security experiment -/

/-- **Experiment** `Exp^{ot-cca}_{Π,𝒜}` (Figure 1 + Definition 2, [ACD19]).

1. `K ←$ KeyGen()`
2. `b ←$ {0, 1}`
3. `b' ← 𝒜^{Encrypt_b, Decrypt_b}()`  with `e* := ⊥`
4. return `⟦b' = b⟧` -/
def securityExp [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C) : ProbComp Bool := do
  let k ← ae.keygen
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (aeadSecurityImpl ae b k) adversary).run none
  return (b == b')
/-- **Guess advantage** (Definition 2, [ACD19]):
`Adv^{ot-cca}_{Π,𝒜} := |Pr[Exp^{ot-cca}_{Π,𝒜} = 1] − 1/2|`. -/
noncomputable def guessAdvantage [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C) : ℝ :=
  |(Pr[= true | securityExp ae adversary]).toReal - 1 / 2|

/-! ### Useful security game decomposition -/

/-- **Fixed-bit experiment.** `b = 0` gives `AEAD_real` (honest encryption);
`b = 1` gives `AEAD_rand` (random ciphertext). Returns `b'`, not `⟦b'=b⟧`. -/
def securityExpFixedBit [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C)
    (b : Bool) : ProbComp Bool := do
  let k ← ae.keygen
  let (b', _) ← (simulateQ (aeadSecurityImpl ae b k) adversary).run none
  return b'

/-- **Distinguishing advantage** (Definition 2.5, [TripleRatchet]):
`Δ_{Π,𝒜} := |Pr[AEAD_rand^𝒜 = 1] − Pr[AEAD_real^𝒜 = 1]|`. -/
noncomputable def distAdvantage [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C) : ℝ :=
  |(Pr[= true | securityExpFixedBit ae adversary true]).toReal -
   (Pr[= true | securityExpFixedBit ae adversary false]).toReal|

/-- **Branching lemma.** The single-game experiment decomposes as a uniform-bit branch:

`Pr[Exp^{ot-cca} = 1] = Pr[b ←$ {0,1}; b' ← (b ? AEAD_rand : AEAD_real); ⟦b=b'⟧]`.

Proved by commuting `b ← $ᵗ Bool` past `KeyGen` via `probEvent_bind_bind_swap`. -/
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

/-- **Centering lemma.**
`Pr[Exp^{ot-cca} = 1] − 1/2 = (Pr[AEAD_rand^𝒜 = 1] − Pr[AEAD_real^𝒜 = 1]) / 2`. -/
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

/-- **Theorem.** `Adv^{ot-cca}_{Π,𝒜} = Δ_{Π,𝒜} / 2`.
The guess advantage equals half the distinguishing advantage. -/
lemma guessAdvantage_eq_distAdvantage_div_two [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTime_CCA_Adversary AD M C) :
    guessAdvantage ae adversary = distAdvantage ae adversary / 2 := by
  simp only [guessAdvantage, distAdvantage]
  rw [securityExp_toReal_sub_half, abs_div]
  congr 1
  exact abs_of_pos two_pos
end OneTime_CCA

end AEADScheme
