/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.FromDDHNonFS.Construction
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import ToVCVio.EvalDist.Monad.Basic

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

`securityExpA` samples the random key `K₁ ←$ G` uniformly from the group, while the DDH game
samples `c ←$ F` and uses `c • gen`. The two agree when `(· • gen : F → G)` is a bijection, i.e.
when `gen` generates `G = ⟨g⟩` of prime order `q = |F|`; this is the hypothesis
`hg : Function.Bijective (· • gen : F → G)`, the same as for `ddhCKA.security`.

## Bit conventions

VCVio's `ddhExp` hands out the real triple on `bit = true`, while `securityExpA` hands out the
random key on `b = true`. The reduction does not negate the guess: the flipped convention only
changes the sign inside the absolute value. Both `ddhGuessAdvantage` and `indCpaAdvantageA` are
bias advantages `|Pr[·] - 1/2|`, so no factor `/ 2` appears.

## Main results

The per-adversary equalities `indCpaAdvantageA_eq`/`indCpaAdvantageB_eq` carry the concrete
content. The corollary `INDCPASecure`, which assumes a DDH bound `ε` uniformly over every DDH
adversary, mirrors `kemRKEM.FSINDCPASecure`.

[REFERENCES]

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
-/

open DiffieHellman RKEMScheme ToVCVio

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
real DDH games of the reduction: on `b = true` it hands out a uniform `K₁ ←$ G`, which `hg` turns
into `c • gen` for a uniform scalar `c`, and on `b = false` the real key `x • y • gen`. -/
private lemma probOutput_true_securityExpA_eq_branch (gen : G)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    Pr[= true | (scheme (F := F) gen).securityExpA fun par ekA ekAHat ekBHat ctB _dkAHat kb =>
      adversary par ekA ekAHat ekBHat ctB kb] =
    Pr[= true | do
      let b ← ($ᵗ Bool)
      let z ← if b then ddhExpRand gen (ddhReduction (F := F) adversary)
        else ddhExpReal gen (ddhReduction (F := F) adversary)
      pure (b == z)] := by
  unfold RKEMScheme.securityExpA
  simp only [scheme, rkeygen, renc, rdec, pure_bind, bind_assoc]
  refine probOutput_bind_congr' _ true fun b => ?_
  cases b
  · -- Real branch: the uniform `K₁` is unused, and `x • y • gen = (x * y) • gen`.
    simp only [Bool.false_eq_true, ↓reduceIte, ddhExpReal, ddhReduction, bind_assoc, smul_smul]
    exact probOutput_bind_of_const' ($ᵗ G) fun _ _ => rfl
  · -- Random branch: move `K₁ ←$ G` innermost, then replace it by `c • gen` with `c ←$ F`.
    simp only [↓reduceIte, ddhExpRand, ddhReduction, bind_assoc]
    rw [probOutput_bind_bind_swap]
    refine probOutput_bind_congr' _ true fun x => ?_
    rw [probOutput_bind_bind_swap]
    refine probOutput_bind_congr' _ true fun y => ?_
    exact (probOutput_bind_bijective_uniform_cross F (fun c => c • gen) hg
      (fun k1 => do
        let b' ← adversary () (x • gen) (x • gen) (y • gen) () k1
        pure (true == b')) true).symm

/-- `Pr[securityExpA = true] - 1/2` at `scheme gen`, in terms of the reduction's DDH games. -/
private lemma probOutput_true_securityExpA_sub_half (gen : G)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    (Pr[= true | (scheme (F := F) gen).securityExpA fun par ekA ekAHat ekBHat ctB _dkAHat kb =>
      adversary par ekA ekAHat ekBHat ctB kb]).toReal - 1 / 2 =
    ((Pr[= true | ddhExpRand gen (ddhReduction (F := F) adversary)]).toReal -
      (Pr[= true | ddhExpReal gen (ddhReduction (F := F) adversary)]).toReal) / 2 := by
  rw [probOutput_true_securityExpA_eq_branch gen hg adversary]
  exact probOutput_uniformBool_branch_toReal_sub_half _ _

/-- **Tight reduction, party `A`**: under `hg`, the IND-CPA-A advantage of `adversary` against
`scheme gen` equals the DDH advantage of `ddhReduction adversary`. -/
-- ANCHOR: indCpaAdvantageA_eq
theorem indCpaAdvantageA_eq (gen : G) (hg : Function.Bijective (· • gen : F → G))
    (adversary : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    (scheme (F := F) gen).indCpaAdvantageA adversary =
      ddhGuessAdvantage gen (ddhReduction (F := F) adversary)
-- ANCHOR_END: indCpaAdvantageA_eq
    := by
  unfold RKEMScheme.indCpaAdvantageA RKEMScheme.fsIndCpaAdvantageA ddhGuessAdvantage
  rw [probOutput_true_securityExpA_sub_half gen hg adversary, ddhExp_probOutput_sub_half,
    ← abs_neg, ← neg_div, neg_sub]

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
      ddhGuessAdvantage gen (ddhReduction (F := F) adversary) := by
  rw [indCpaAdvantageB_eq_indCpaAdvantageA, indCpaAdvantageA_eq gen hg]

/-- **IND-CPA security** ([TripleRatchet, Thm. A.4], non-forward-secure part): if every DDH
adversary has advantage at most `ε` and `(· • gen : F → G)` is bijective, `scheme gen` is
`ε`-IND-CPA-secure against every pair of adversaries. -/
-- ANCHOR: INDCPASecure
theorem INDCPASecure (gen : G) (hg : Function.Bijective (· • gen : F → G)) (ε : ℝ)
    (hddh : ∀ adversary : DDHAdversary F G, ddhGuessAdvantage gen adversary ≤ ε)
    (adversaryA adversaryB : RKEMScheme.INDCPAAdversary Unit G Unit G) :
    (scheme (F := F) gen).INDCPASecure adversaryA adversaryB ε
-- ANCHOR_END: INDCPASecure
    := by
  unfold RKEMScheme.INDCPASecure RKEMScheme.indCpaAdvantage
  rw [indCpaAdvantageA_eq gen hg adversaryA, indCpaAdvantageB_eq gen hg adversaryB]
  exact max_le (hddh _) (hddh _)

end ddhRKEM
