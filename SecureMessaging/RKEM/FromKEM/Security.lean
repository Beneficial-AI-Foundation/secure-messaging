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
(`prEvent_true_indCpaGame_eq_prEvent_true_securityExpACore`).

Combining the two equalities gives the per-party reduction bounds
`fsIndCpaAdvantageA_eq`/`fsIndCpaAdvantageB_eq`, each equal to the underlying KEM's IND-CPA
advantage against the corresponding reduction adversary, converted to the bias convention via
`/ 2` (see below). The top-level `FSINDCPASecure` then
assumes a uniform IND-CPA bound `ε` over every adversary of the underlying KEM (not just the two
specific reduction adversaries), giving the clean bound `ε / 2`.

The `/ 2` is a change of convention, not a loss: VCVio's `IND_CPA_Advantage` is the *distinguishing*
advantage `|Pr[true] - Pr[false]|` (the game's `Measure.boolBias`, in `ℝ≥0∞`), exactly twice
[TripleRatchet]'s Def. 5.4 *bias* advantage `|Pr[true] - 1/2|` for a game that never fails, so
dividing its real value by `2` converts between the two conventions without any loss of tightness
(`IND_CPA_Advantage_eq_game_bias`,
`Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure`).
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

/-- The IND-CPA reduction `𝓑` built from an FS-IND-CPA adversary `𝓐`:

𝓑.preChallenge(êkB) := êkB
𝓑.postChallenge(êkB, ctB, Kb):
  (ekA, _)   ← KeyGen()
  (êkA, d̂kA) ← KeyGen()
  b'      ←$ 𝓐(ekA, êkA, êkB, (êkA, ctB), d̂kA, Kb)
  return ¬b'

`𝓑`'s own challenge key plays `B`'s updated key `êkB`; `A`'s fresh pair and next-round pair are
sampled independently, as the construction itself would, since neither depends on the challenge.
The final negation aligns conventions: `IND_CPA_Game` scores `b = true ↔ real key`, while
`securityExpA` scores `b = true ↔ random key`. With it, `Pr[IND_CPA_Game(𝓑) = true] =
Pr[securityExpACore(𝓐) = true]`. -/
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
`prEvent_true_securityExpA_eq_prEvent_true_securityExpACore` and
`prEvent_true_indCpaGame_eq_prEvent_true_securityExpACore`. -/
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
private lemma prEvent_true_securityExpA_eq_prEvent_true_securityExpACore
    (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    Pr{let x ← RKEMScheme.securityExpA (scheme kem total) adversary}[x = true] =
      Pr{let x ← securityExpACore kem adversary}[x = true] := by
  unfold RKEMScheme.securityExpA securityExpACore
  simp only [scheme, rkeygen, renc, rdec, pure_bind, bind_assoc]
  refine prEvent_bind_congr _ _ _ _ _ fun b => ?_
  refine prEvent_bind_congr _ _ _ _ _ fun k1 => ?_
  refine prEvent_bind_congr _ _ _ _ _ fun p => ?_
  obtain ⟨ekA, dkA⟩ := p
  refine prEvent_bind_congr _ _ _ _ _ fun q => ?_
  obtain ⟨ekBHat, dkBHat⟩ := q
  refine prEvent_bind_congr _ _ _ _ _ fun r => ?_
  obtain ⟨ct, k0⟩ := r
  refine prEvent_bind_congr _ _ _ _ _ fun s => ?_
  obtain ⟨ekSelfHat, dkSelfHat⟩ := s
  exact prEvent_bind_eq_of_forall_eq (total.decapsTotal dkBHat ct) (by simp) _ _ fun _ => rfl

/-- The reduction's `IND_CPA_Game` and `securityExpACore` output `true` equally often. Both
sample the same randomness in different orders and read the challenge bit oppositely: the KEM
game hands out the real key on `true`, `securityExpA` the random one. -/
private lemma prEvent_true_indCpaGame_eq_prEvent_true_securityExpACore
    (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    Pr{let x ← KEMScheme.IND_CPA_Game ProbCompRuntime.probComp
        (indCpaReduction kem adversary)}[x = true] =
      Pr{let x ← securityExpACore kem adversary}[x = true] := by
  change Pr{let x ← (do
      let (pk, _sk) ← kem.keygen
      let st ← (indCpaReduction kem adversary).preChallenge pk
      let b ← ($ᵗ Bool : ProbComp Bool)
      let (cStar, kReal) ← kem.encaps pk
      let kRand ← ($ᵗ K : ProbComp K)
      let b' ← (indCpaReduction kem adversary).postChallenge st cStar (if b then kReal else kRand)
      pure (b == b'))}[x = true] = Pr{let x ← securityExpACore kem adversary}[x = true]
  simp only [indCpaReduction, securityExpACore, bind_assoc, pure_bind]
  conv_lhs => rw [(OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq]
  have hcoin := prEvent_true_uniformBool_bind_not
    (fun b => do
      let a ← kem.keygen
      let __x ← kem.encaps a.1
      let kRand ← ($ᵗ K : ProbComp K)
      let x ← kem.keygen
      let x_1 ← kem.keygen
      adversary () x.1 x_1.1 a.1 (x_1.1, __x.1) x_1.2 (if b then __x.2 else kRand))
  simp only [bind_assoc] at hcoin
  rw [hcoin]
  refine prEvent_bind_congr _ _ _ _ _ fun b => ?_
  -- First, rewrite the `if (!b) ...` condition (an artifact of the coin-relabeling step) into
  -- the `if b ...` form `securityExpACore` uses.
  have hflip : Pr{let x ← (do
      let a ← kem.keygen
      let e ← kem.encaps a.1
      let kRand ← ($ᵗ K : ProbComp K)
      let ekA ← kem.keygen
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2
        (if (!b) then e.2 else kRand)
      pure (b == b'))}[x = true] =
    Pr{let x ← (do
      let a ← kem.keygen
      let e ← kem.encaps a.1
      let kRand ← ($ᵗ K : ProbComp K)
      let ekA ← kem.keygen
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2 (if b then kRand else e.2)
      pure (b == b'))}[x = true] := by
    cases b <;> rfl
  rw [hflip]
  -- Now reorder the shared randomness (`B`'s key + encapsulation, `A`'s next-round key, and the
  -- random key) to match `securityExpACore`'s sampling order, keeping `B`'s key and its
  -- encapsulation adjacent throughout (the encapsulation depends on the key).
  refine (prEvent_bind_congr _ _ _ _ _ fun a =>
    (OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _).trans ?_
  refine ((OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _).trans ?_
  refine (prEvent_bind_congr _ _ _ _ _ fun kRand => prEvent_bind_congr _ _ _ _ _ fun a =>
    (OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _).trans ?_
  exact prEvent_bind_congr _ _ _ _ _ fun kRand =>
    (OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _

/-- Reduction bound: the RKEM-from-KEM construction's `A`-side FS-IND-CPA advantage equals the
underlying KEM's IND-CPA advantage against the reduction adversary, converted from the
distinguishing to the bias convention (`/ 2`; see the module docstring). -/
theorem fsIndCpaAdvantageA_eq
    (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.fsIndCpaAdvantageA (scheme kem total) adversary =
      (kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary)).toReal /
        2 := by
  unfold RKEMScheme.fsIndCpaAdvantageA
  rw [prEvent_true_securityExpA_eq_prEvent_true_securityExpACore kem total adversary,
    ← prEvent_true_indCpaGame_eq_prEvent_true_securityExpACore kem adversary,
    IND_CPA_Advantage_eq_game_bias, ProbCompRuntime.probComp_evalDist,
    MeasureTheory.Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure,
    ENNReal.toReal_mul, ENNReal.absDiff_toReal (MeasureTheory.measure_ne_top _ _) (by simp),
    prEvent_eq_evalDist_singleton]
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_div, ENNReal.toReal_one]
  ring

/-- As `fsIndCpaAdvantageA_eq`, with the roles of `A` and `B` swapped: since the RKEM-from-KEM
construction treats both parties identically (`securityExpB_eq_securityExpA`), the same reduction
bound applies to the `B`-side advantage against the very same reduction adversary. The `/ 2` is a
convention conversion, not a loss; see the module docstring. -/
theorem fsIndCpaAdvantageB_eq
    (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.fsIndCpaAdvantageB (scheme kem total) adversary =
      (kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary)).toReal /
        2 := by
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
      (kem.IND_CPA_Advantage ProbCompRuntime.probComp adv).toReal ≤ ε)
    (adversaryA adversaryB : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.FSINDCPASecure (scheme kem total) adversaryA adversaryB (ε / 2)
-- ANCHOR_END: FSINDCPASecure
    := by
  unfold RKEMScheme.FSINDCPASecure RKEMScheme.fsIndCpaAdvantage
  rw [fsIndCpaAdvantageA_eq kem total adversaryA, fsIndCpaAdvantageB_eq kem total adversaryB]
  exact max_le (div_le_div_of_nonneg_right (hcpa _) zero_le_two)
    (div_le_div_of_nonneg_right (hcpa _) zero_le_two)

end kemRKEM
