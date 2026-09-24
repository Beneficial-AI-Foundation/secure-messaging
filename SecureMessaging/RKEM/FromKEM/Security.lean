/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.FromKEM.Construction
import ToVCVio.CryptoFoundations.KeyEncapMech
import ToVCVio.EvalDist.Monad.Basic

/-!
# RKEM from KEM — FS-IND-CPA Security

This file proves `RKEMScheme.FSINDCPASecure` for the generic RKEM-from-KEM construction of
`SecureMessaging.RKEM.FromKEM.Construction`: if the underlying KEM is IND-CPA-secure, the
construction is FS-IND-CPA-secure in the sense of [TripleRatchet, Def. 5.4], matching
[TripleRatchet]'s Theorem A.1.

The proof builds a reduction, `indCpaReduction`, from an FS-IND-CPA adversary against the
construction to an IND-CPA adversary against the underlying KEM: it independently samples the
extra key pairs the construction generates each round and hands everything to the RKEM-level
adversary, negating its guess to align the two games' conventions
(`probOutput_true_indCpaGame_eq_probOutput_true_securityExpACore`).

Combining the two equalities gives the per-party reduction bounds
`fsIndCpaAdvantageA_eq`/`fsIndCpaAdvantageB_eq`, each equal to the underlying KEM's IND-CPA
advantage against the corresponding reduction adversary, converted to the bias convention via
`/ 2` (see below). The top-level `FSINDCPASecure` then
assumes a uniform IND-CPA bound `ε` over every adversary of the underlying KEM (not just the two
specific reduction adversaries), giving the clean bound `ε / 2`.

The `/ 2` is a change of convention, not a loss: VCVio's `IND_CPA_Advantage` is the *distinguishing*
advantage `|Pr[true] - Pr[false]|`, exactly twice [TripleRatchet]'s Def. 5.4 *bias* advantage
`|Pr[true] - 1/2|` for a game that never fails, so dividing by `2` converts between the two
conventions without any loss of tightness (`IND_CPA_Advantage_eq_game_bias`,
`SPMF.boolBiasAdvantage_eq_two_mul_abs_sub_half`).
-/

open ToVCVio KEMScheme RKEMScheme

namespace kemRKEM

variable {K PK SK C : Type} [SampleableType K]

/-- `securityExpB` and `securityExpA` at the RKEM-from-KEM scheme literally coincide, the
construction treats both parties identically. -/
private lemma securityExpB_eq_securityExpA
    (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.securityExpB (scheme kem total) adversary =
      RKEMScheme.securityExpA (scheme kem total) adversary := rfl

/-- The KEM IND-CPA adversary built from an FS-IND-CPA adversary against the construction. The
challenge public key plays `B`'s updated key; `A`'s fresh pair and next-round pair are sampled
here, as the construction would, since neither depends on the challenge. The guess is negated
because `IND_CPA_Game` reads `b = true` as the real key and `securityExpA` reads it as the random
key; with the negation `probOutput_true_indCpaGame_eq_probOutput_true_securityExpACore` is an
equality of `Pr[= true]`. Negating a guess leaves `IND_CPA_Advantage` unchanged, so nothing is
lost. -/
-- ANCHOR: indCpaReduction
def indCpaReduction (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    kem.IND_CPA_Adversary where
  State := PK
  preChallenge := fun ekBHat => pure ekBHat
  postChallenge := fun ekBHat ct kb => do
    let (ekA, _dkA) ← kem.keygen
    let (ekAHat, dkAHat) ← kem.keygen
    let b' ← adversary () ekA ekAHat ekBHat (ekAHat, ct) dkAHat kb
    return !b'
-- ANCHOR_END: indCpaReduction

/-- A restatement of `securityExpA` that skips the decapsulation call entirely, rather than
performing it and throwing the result away. Serves as a convenient intermediate target for both
`probOutput_true_securityExpA_eq_probOutput_true_securityExpACore` and
`probOutput_true_indCpaGame_eq_probOutput_true_securityExpACore`. -/
private def securityExpACore (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k1 ← $ᵗ K
  let (ekA, _dkA) ← kem.keygen
  let (ekBHat, _dkBHat) ← kem.keygen
  let (ct, k0) ← kem.encaps ekBHat
  let (ekAHat, dkAHat) ← kem.keygen
  let b' ← adversary () ekA ekAHat ekBHat (ekAHat, ct) dkAHat (if b then k1 else k0)
  return b == b'

/-- `securityExpA` at the RKEM-from-KEM scheme succeeds exactly as often as `securityExpACore`:
unfolding `scheme`'s fields, the only difference is an extra decapsulation call
(`total.decapsTotal`) whose result is discarded, since decapsulation never fails and its output
plays no further role once its key pair has already been produced by `rencA`. -/
private lemma probOutput_true_securityExpA_eq_probOutput_true_securityExpACore
    (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    Pr[= true | RKEMScheme.securityExpA (scheme kem total) adversary] =
      Pr[= true | securityExpACore kem adversary] := by
  unfold RKEMScheme.securityExpA securityExpACore
  simp only [scheme, rkeygen, renc, rdec, pure_bind, bind_assoc]
  refine probOutput_bind_congr fun b _ => ?_
  refine probOutput_bind_congr fun k1 _ => ?_
  refine probOutput_bind_congr fun p _ => ?_
  obtain ⟨ekA, dkA⟩ := p
  refine probOutput_bind_congr fun q _ => ?_
  obtain ⟨ekBHat, dkBHat⟩ := q
  refine probOutput_bind_congr fun r _ => ?_
  obtain ⟨ct, k0⟩ := r
  refine probOutput_bind_congr fun s _ => ?_
  obtain ⟨ekSelfHat, dkSelfHat⟩ := s
  exact probOutput_bind_of_const' (total.decapsTotal dkBHat ct) fun _ _ => rfl

/-- The reduction's `IND_CPA_Game` and `securityExpACore` output `true` equally often. Both
sample the same randomness in different orders and read the challenge bit oppositely: the KEM
game hands out the real key on `true`, `securityExpA` the random one. -/
private lemma probOutput_true_indCpaGame_eq_probOutput_true_securityExpACore
    (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    Pr[= true | KEMScheme.IND_CPA_Game ProbCompRuntime.probComp (indCpaReduction kem adversary)] =
      Pr[= true | securityExpACore kem adversary] := by
  change Pr[= true | do
      let (pk, _sk) ← kem.keygen
      let st ← (indCpaReduction kem adversary).preChallenge pk
      let b ← ($ᵗ Bool : ProbComp Bool)
      let (cStar, kReal) ← kem.encaps pk
      let kRand ← ($ᵗ K : ProbComp K)
      let b' ← (indCpaReduction kem adversary).postChallenge st cStar (if b then kReal else kRand)
      pure (b == b')] = Pr[= true | securityExpACore kem adversary]
  simp only [indCpaReduction, securityExpACore, bind_assoc, pure_bind]
  conv_lhs => rw [probOutput_bind_bind_swap]
  have hcoin := probOutput_true_uniformBool_bind_not
    (fun b => do
      let a ← kem.keygen
      let __x ← kem.encaps a.1
      let kRand ← ($ᵗ K : ProbComp K)
      let x ← kem.keygen
      let x_1 ← kem.keygen
      adversary () x.1 x_1.1 a.1 (x_1.1, __x.1) x_1.2 (if b then __x.2 else kRand))
  simp only [bind_assoc] at hcoin
  rw [hcoin]
  refine probOutput_bind_congr fun b _ => ?_
  -- First, rewrite the `if (!b) ...` condition (an artifact of the coin-relabeling step) into
  -- the `if b ...` form `securityExpACore` uses.
  have hflip : Pr[= true | do
      let a ← kem.keygen
      let e ← kem.encaps a.1
      let kRand ← ($ᵗ K : ProbComp K)
      let ekA ← kem.keygen
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2
        (if (!b) then e.2 else kRand)
      pure (b == b')] =
    Pr[= true | do
      let a ← kem.keygen
      let e ← kem.encaps a.1
      let kRand ← ($ᵗ K : ProbComp K)
      let ekA ← kem.keygen
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2 (if b then kRand else e.2)
      pure (b == b')] := by
    cases b <;> rfl
  rw [hflip]
  -- Now reorder the shared randomness (`B`'s key + encapsulation, `A`'s next-round key, and the
  -- random key) to match `securityExpACore`'s sampling order, keeping `B`'s key and its
  -- encapsulation adjacent throughout (the encapsulation depends on the key).
  refine (probOutput_bind_congr fun a _ => probOutput_bind_bind_swap _ _ _ _).trans ?_
  refine (probOutput_bind_bind_swap _ _ _ _).trans ?_
  refine (probOutput_bind_congr fun kRand _ => probOutput_bind_congr fun a _ =>
    probOutput_bind_bind_swap _ _ _ _).trans ?_
  exact probOutput_bind_congr fun kRand _ => probOutput_bind_bind_swap _ _ _ _

/-- Reduction bound: the RKEM-from-KEM construction's `A`-side FS-IND-CPA advantage equals the
underlying KEM's IND-CPA advantage against the reduction adversary, converted from the
distinguishing to the bias convention (`/ 2`; see the module docstring). -/
theorem fsIndCpaAdvantageA_eq
    (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.fsIndCpaAdvantageA (scheme kem total) adversary =
      kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary) / 2 := by
  unfold RKEMScheme.fsIndCpaAdvantageA
  rw [probOutput_true_securityExpA_eq_probOutput_true_securityExpACore kem total adversary,
    ← probOutput_true_indCpaGame_eq_probOutput_true_securityExpACore kem adversary]
  have hnf : Pr[⊥ | KEMScheme.IND_CPA_Game ProbCompRuntime.probComp
      (indCpaReduction kem adversary)] = 0 := by
    change Pr[⊥ | do
        let (pk, _sk) ← kem.keygen
        let st ← (indCpaReduction kem adversary).preChallenge pk
        let b ← ($ᵗ Bool : ProbComp Bool)
        let (cStar, kReal) ← kem.encaps pk
        let kRand ← ($ᵗ K : ProbComp K)
        let b' ← (indCpaReduction kem adversary).postChallenge st cStar (if b then kReal else kRand)
        pure (b == b')] = 0
    exact NeverFail.probFailure_eq_zero
  have htotal : Pr[= true | KEMScheme.IND_CPA_Game ProbCompRuntime.probComp
      (indCpaReduction kem adversary)] +
      Pr[= false | KEMScheme.IND_CPA_Game ProbCompRuntime.probComp
        (indCpaReduction kem adversary)] = 1 := by
    rw [probOutput_true_add_false, hnf, tsub_zero]
  rw [IND_CPA_Advantage_eq_game_bias, SPMF.boolBiasAdvantage_eq_two_mul_abs_sub_half _ htotal]
  ring

/-- As `fsIndCpaAdvantageA_eq`, with the roles of `A` and `B` swapped: since the RKEM-from-KEM
construction treats both parties identically (`securityExpB_eq_securityExpA`), the same reduction
bound applies to the `B`-side advantage against the very same reduction adversary. The `/ 2` is a
convention conversion, not a loss; see the module docstring. -/
theorem fsIndCpaAdvantageB_eq
    (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.fsIndCpaAdvantageB (scheme kem total) adversary =
      kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary) / 2 := by
  unfold RKEMScheme.fsIndCpaAdvantageB
  rw [securityExpB_eq_securityExpA]
  exact fsIndCpaAdvantageA_eq kem total adversary

/-- **FS-IND-CPA security** (Def. 5.4) of the RKEM-from-KEM construction: if the underlying KEM is
`ε`-IND-CPA-secure, uniformly over every adversary, the construction is FS-IND-CPA-secure at
`ε / 2`. The `/ 2` is a convention conversion, not a loss; see the module docstring. -/
-- ANCHOR: FSINDCPASecure
theorem FSINDCPASecure (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (ε : ℝ)
    (hcpa : ∀ adv : kem.IND_CPA_Adversary,
      kem.IND_CPA_Advantage ProbCompRuntime.probComp adv ≤ ε)
    (adversaryA adversaryB : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.FSINDCPASecure (scheme kem total) adversaryA adversaryB (ε / 2)
-- ANCHOR_END: FSINDCPASecure
    := by
  unfold RKEMScheme.FSINDCPASecure RKEMScheme.fsIndCpaAdvantage
  rw [fsIndCpaAdvantageA_eq kem total adversaryA, fsIndCpaAdvantageB_eq kem total adversaryB]
  exact max_le (div_le_div_of_nonneg_right (hcpa _) zero_le_two)
    (div_le_div_of_nonneg_right (hcpa _) zero_le_two)

end kemRKEM
