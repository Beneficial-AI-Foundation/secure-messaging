/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.FromDDHNonFS.Construction
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.CryptoFoundations.SecExp.Measure

/-!
# RKEM from DDH (non-FS) — IND-CPA Security

This file proves that the non-forward-secure Diffie-Hellman RKEM `ddhRKEM.scheme gen` of
`SecureMessaging.RKEM.FromDDHNonFS.Construction` is IND-CPA secure (`RKEMScheme.INDCPASecure`)
under the DDH assumption, the non-forward-secure part of [TripleRatchet, Thm. A.4].

## Reduction

In the IND-CPA game for party `A`, the adversary sees `ekA = ek̂A = g^x`, `ek̂B = g^y`, the empty
ciphertext `ctB = ()`, and either the real key `K₀ = g^{xy}` or a uniform `K₁`. This view is a DDH
instance `(g, X, Y, T)` with `X = g^x`, `Y = g^y` and `T` real or random. The reduction
`ddhReduction` hands the IND-CPA adversary the view `(X, X, Y, (), T)` and returns its guess
unchanged; the reduction is tight, with equality of advantages (`indCpaAdvantageA_eq`,
`indCpaAdvantageB_eq`).

## Group hypothesis

`securityExpA` samples the random key `K₁ ←$ G` uniformly from the group, while the DDH
experiments sample `c ←$ F` and use `c • gen`. The two agree when `(· • gen : F → G)` is a
bijection, i.e. when `gen` generates `G = ⟨g⟩` of prime order `q = |F|`; this is the hypothesis
`hg : Function.Bijective (· • gen : F → G)`, the same as for `ddhCKA.security`.

## Advantage conventions

VCVio's `ddhAdvantage` is the *distinguishing* advantage
`|Pr[real = 1] - Pr[random = 1]|` (in `ℝ≥0∞`), while `indCpaAdvantageA` is [TripleRatchet]'s
Def. 5.4 *bias* advantage `|Pr[securityExpA = 1] - 1/2|`. For a game that never fails the first is
exactly twice the second, so dividing its real value by `2` converts between the two conventions
without any loss of tightness, as for `kemRKEM.fsIndCpaAdvantageA_eq`.

`securityExpA` hands out the random key on `b = true`, the opposite of the real/random branch order
in VCVio's `ddhGame`. The reduction does not negate the guess: the distinguishing advantage is
symmetric in its two experiments (`MeasureTheory.Measure.boolDist_comm`).

## Main results

The per-adversary equalities `indCpaAdvantageA_eq`/`indCpaAdvantageB_eq` carry the concrete
content. The corollary `INDCPASecure`, which assumes a DDH bound `ε` uniformly over every DDH
adversary and concludes `ε / 2`, mirrors `kemRKEM.FSINDCPASecure`.

[REFERENCES]

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
-/

open DiffieHellman RKEMScheme

namespace ddhRKEM

variable {F : Type} [Field F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

/-- DDH reduction 𝓑 built from an IND-CPA adversary 𝓐 against `scheme gen`: on a DDH instance
`(g, X, Y, T)` it hands 𝓐 the IND-CPA view `(ekA, ek̂A, ek̂B, ctB, Kb) := (X, X, Y, (), T)`
(`ek̂A = ekA` and `ctB = ()` in this scheme) and returns 𝓐's guess unchanged. -/
-- ANCHOR: ddhReduction
def ddhReduction (adversary : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    DiffieHellman.DDHAdversary F G :=
  fun _gen ekA ekBHat key => adversary () ekA ekA ekBHat () key
-- ANCHOR_END: ddhReduction

/-- The IND-CPA-A experiment at `scheme gen` is a uniform-bit branch between the random and the
real DDH experiments of the reduction: on `b = true` it hands out a uniform `K₁ ←$ G`, which `hg`
turns into `c • gen` for a uniform scalar `c`, and on `b = false` the real key `x • y • gen`. -/
private lemma prEvent_true_securityExpA_eq_branch (gen : G)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    Pr{let x ← (scheme (F := F) gen).securityExpA fun par ekA ekAHat ekBHat ctB _dkAHat kb =>
      adversary par ekA ekAHat ekBHat ctB kb}[x = true] =
    Pr{let x ← (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then ddhRandomExperiment gen (ddhReduction (F := F) adversary)
        else ddhRealExperiment gen (ddhReduction (F := F) adversary)
      pure (b == z))}[x = true] := by
  unfold RKEMScheme.securityExpA
  simp only [scheme, rkeygen, renc, rdec, pure_bind, bind_assoc]
  refine prEvent_bind_congr _ _ _ _ _ fun b => ?_
  cases b
  · -- Real branch: the uniform `K₁` is unused, and `x • y • gen = (x * y) • gen`.
    simp only [Bool.false_eq_true, ↓reduceIte, ddhRealExperiment, ddhReduction, bind_assoc,
      smul_smul]
    exact (OracleComp.EvalDistEq.bind_const _ _).prEvent_eq _
  · -- Random branch: move `K₁ ←$ G` innermost, then replace it by `c • gen` with `c ←$ F`.
    simp only [↓reduceIte, ddhRandomExperiment, ddhReduction, bind_assoc]
    refine ((OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _).trans ?_
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    refine ((OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _).trans ?_
    refine prEvent_bind_congr _ _ _ _ _ fun y => ?_
    have hswap := (SampleableType.map_uniformSample_evalDistEq_of_bijective hg).bind
      (f := fun k1 => do
        let b' ← adversary () (x • gen) (x • gen) (y • gen) () k1
        pure (true == b'))
      (g := fun k1 => do
        let b' ← adversary () (x • gen) (x • gen) (y • gen) () k1
        pure (true == b'))
      fun _ => EvalDistEq.refl _
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind] at hswap
    exact (hswap.prEvent_eq _).symm

/-- **Tight reduction, party `A`**: under `hg`, the IND-CPA-A advantage of `adversary` against
`scheme gen` equals the DDH advantage of `ddhReduction adversary`, converted from the
distinguishing to the bias convention (`/ 2`; see the module docstring). -/
-- ANCHOR: indCpaAdvantageA_eq
theorem indCpaAdvantageA_eq (gen : G) (hg : Function.Bijective (· • gen : F → G))
    (adversary : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    (scheme (F := F) gen).indCpaAdvantageA adversary =
      (ddhAdvantage gen (ddhReduction (F := F) adversary)).toReal / 2
-- ANCHOR_END: indCpaAdvantageA_eq
    := by
  unfold RKEMScheme.indCpaAdvantageA RKEMScheme.fsIndCpaAdvantageA ddhAdvantage
  rw [prEvent_true_securityExpA_eq_branch gen hg adversary, MeasureTheory.Measure.boolDist_comm,
    ← evalDist_boolBias_bind_uniformBool,
    MeasureTheory.Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure,
    ENNReal.toReal_mul, ENNReal.absDiff_toReal (MeasureTheory.measure_ne_top _ _) (by simp),
    prEvent_eq_evalDist_singleton]
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_div, ENNReal.toReal_one]
  ring

/-- `scheme gen` treats both parties identically, so its IND-CPA-B and IND-CPA-A advantages
coincide by definition. -/
private lemma indCpaAdvantageB_eq_indCpaAdvantageA (gen : G)
    (adversary : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    (scheme (F := F) gen).indCpaAdvantageB adversary =
      (scheme (F := F) gen).indCpaAdvantageA adversary := rfl

/-- **Tight reduction, party `B`**: as `indCpaAdvantageA_eq`, with the same reduction, since
`scheme gen` treats both parties identically. -/
theorem indCpaAdvantageB_eq (gen : G) (hg : Function.Bijective (· • gen : F → G))
    (adversary : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    (scheme (F := F) gen).indCpaAdvantageB adversary =
      (ddhAdvantage gen (ddhReduction (F := F) adversary)).toReal / 2 := by
  rw [indCpaAdvantageB_eq_indCpaAdvantageA, indCpaAdvantageA_eq gen hg]

/-- **IND-CPA security** ([TripleRatchet, Thm. A.4], non-forward-secure part): if every DDH
adversary has advantage at most `ε` and `(· • gen : F → G)` is bijective, `scheme gen` is
`ε / 2`-IND-CPA-secure against every pair of adversaries. The `/ 2` is a convention conversion,
not a loss; see the module docstring. -/
-- ANCHOR: INDCPASecure
theorem INDCPASecure (gen : G) (hg : Function.Bijective (· • gen : F → G)) (ε : ℝ)
    (hddh : ∀ adversary : DDHAdversary F G, (ddhAdvantage gen adversary).toReal ≤ ε)
    (adversaryA adversaryB : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    (scheme (F := F) gen).INDCPASecure adversaryA adversaryB (ε / 2)
-- ANCHOR_END: INDCPASecure
    := by
  unfold RKEMScheme.INDCPASecure RKEMScheme.indCpaAdvantage
  rw [indCpaAdvantageA_eq gen hg adversaryA, indCpaAdvantageB_eq gen hg adversaryB]
  exact max_le (div_le_div_of_nonneg_right (hddh _) zero_le_two)
    (div_le_div_of_nonneg_right (hddh _) zero_le_two)

end ddhRKEM
