/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.FromKEM.Construction
import ToVCVio.CryptoFoundations.KeyEncapMech
import ToVCVio.EvalDist.Monad.Basic
import ToVCVio.EvalDist.TVDist

/-!
# RKEM from KEM — FS-IND-CPA Security

This file proves `RKEMScheme.FSINDCPASecure` for the generic RKEM-from-KEM construction of
`SecureMessaging.RKEM.FromKEM.Construction`: if the underlying KEM is IND-CPA-secure, the
construction is FS-IND-CPA-secure in the sense of [TripleRatchet, Def. 5.4].

The proof builds a reduction, `indCpaReduction`, from an FS-IND-CPA adversary against the
construction to an IND-CPA adversary against the underlying KEM: it independently samples the
extra key pairs the construction generates each round and hands everything to the RKEM-level
adversary, negating its guess to align the two games' conventions
(`probOutput_true_indCpaGame_eq_probOutput_true_idealSecurityExpA`). This reduction is exact except
for half the probability that the underlying KEM's decapsulation fails, bounded via a
total-variation-distance argument against an "idealized" experiment that never falls back to a
random bit on decapsulation failure (`tvDist_securityExpA_idealSecurityExpA_le`): the two
experiments agree exactly off the (rare) decapsulation-failure event, and even on that event they
only differ by a fresh coin flip versus an arbitrary `Bool`, which is at most `1/2` apart in
total-variation distance rather than the trivial `1`. Combining the two gives the per-party
reduction bounds `fsIndCpaAdvantageA_le`/`fsIndCpaAdvantageB_le`, and hence `fsIndCpaAdvantage_le`,
which states the same bound directly as `RKEMScheme.FSINDCPASecure`.

The top-level `FSINDCPASecure` repackages `fsIndCpaAdvantage_le` against a uniform IND-CPA bound
`ε` (assumed for every adversary of the underlying KEM, not just the specific reduction adversaries)
together with a `δ`-correctness hypothesis on the KEM, giving the clean bound `ε / 2 + δ / 2` that
matches Theorem A.1's statement. `FSINDCPASecure_of_perfectlyCorrect` further specializes this to
`ε / 2` when the underlying KEM is perfectly correct, so no correctness slack remains.

The `/ 2` in these bounds is not lossiness in the reduction: VCVio's `IND_CPA_Advantage` uses the
*distinguishing* convention `|Pr[true] - Pr[false]|`, twice [TripleRatchet]'s Def. 5.4 *bias*
convention `|Pr[true] - 1/2|`, so dividing by `2` exactly converts between the two conventions and
the reduction is tight in the advantage as `|Pr[true] − Pr[false]| = 2·|Pr[true] − 1/2|`.
-/

open ToVCVio KEMScheme RKEMScheme
open scoped NNReal ENNReal

namespace kemRKEM

variable {K PK SK C : Type} [SampleableType K]

/-- `securityExpB` and `securityExpA` at the RKEM-from-KEM scheme literally coincide, for the
same reason as the correctness experiments: the construction treats both parties identically. -/
private lemma securityExpB_eq_securityExpA
    (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.securityExpB (scheme kem) adversary =
      RKEMScheme.securityExpA (scheme kem) adversary := rfl

/-- The KEM IND-CPA adversary built from an FS-IND-CPA adversary against the RKEM-from-KEM
construction: independently sample `A`'s own fresh key pair and its next-round key pair (both
unrelated to the challenge), then hand everything to the RKEM-level adversary. The returned guess
is negated to align this reduction's "real ciphertext ↦ `true`" convention with the RKEM
experiment's "`true` ↦ random key" convention; this doesn't affect the resulting `IND_CPA`
advantage, which is invariant under negating the adversary's guess. -/
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

/-- The "idealized" FS-IND-CPA experiment that always invokes the adversary, never substituting
a fresh random bit for a decapsulation failure. -/
private def idealSecurityExpA (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k1 ← $ᵗ K
  let (ekA, _dkA) ← kem.keygen
  let (ekBHat, _dkBHat) ← kem.keygen
  let (ct, k0) ← kem.encaps ekBHat
  let (ekAHat, dkAHat) ← kem.keygen
  let b' ← adversary () ekA ekAHat ekBHat (ekAHat, ct) dkAHat (if b then k1 else k0)
  return b == b'

/-- The reduction's single-game IND-CPA experiment against `indCpaReduction` succeeds exactly as
often as the idealized FS-IND-CPA experiment returns `true`. The two games sample the same
underlying randomness (`A`'s fresh key, `B`'s key, the challenge encapsulation, `A`'s next-round
key, the challenge bit, and the random key) in different orders and with a flipped success
convention (`IND_CPA_Game`'s "real ciphertext ↦ `true`" versus `securityExpA`'s "`true` ↦ random
key"); this proof relabels the challenge coin by negation
(`probOutput_true_uniformBool_bind_not`) to absorb that flipped convention in one step, then
reorders the remaining independent samples to align the two games. -/
private lemma probOutput_true_indCpaGame_eq_probOutput_true_idealSecurityExpA
    (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    Pr[= true | KEMScheme.IND_CPA_Game ProbCompRuntime.probComp (indCpaReduction kem adversary)] =
      Pr[= true | idealSecurityExpA kem adversary] := by
  change Pr[= true | do
      let (pk, _sk) ← kem.keygen
      let st ← (indCpaReduction kem adversary).preChallenge pk
      let b ← ($ᵗ Bool : ProbComp Bool)
      let (cStar, kReal) ← kem.encaps pk
      let kRand ← ($ᵗ K : ProbComp K)
      let b' ← (indCpaReduction kem adversary).postChallenge st cStar (if b then kReal else kRand)
      pure (b == b')] = Pr[= true | idealSecurityExpA kem adversary]
  simp only [indCpaReduction, idealSecurityExpA, bind_assoc, pure_bind]
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
  -- the `if b ...` form `idealSecurityExpA` uses.
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
    refine probOutput_bind_congr fun a _ => ?_
    refine probOutput_bind_congr fun e _ => ?_
    refine probOutput_bind_congr fun kRand _ => ?_
    refine probOutput_bind_congr fun ekA _ => ?_
    refine probOutput_bind_congr fun ekAHat _ => ?_
    cases b <;> rfl
  rw [hflip]
  -- Now reorder the shared randomness (`B`'s key + encapsulation, `A`'s next-round key, and the
  -- random key) to match `idealSecurityExpA`'s sampling order, keeping `B`'s key and its
  -- encapsulation adjacent throughout (the encapsulation depends on the key).
  have s1 : Pr[= true | do
      let a ← kem.keygen
      let e ← kem.encaps a.1
      let kRand ← ($ᵗ K : ProbComp K)
      let ekA ← kem.keygen
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2 (if b then kRand else e.2)
      pure (b == b')] =
    Pr[= true | do
      let a ← kem.keygen
      let kRand ← ($ᵗ K : ProbComp K)
      let e ← kem.encaps a.1
      let ekA ← kem.keygen
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2 (if b then kRand else e.2)
      pure (b == b')] := by
    refine probOutput_bind_congr fun a _ => ?_
    exact probOutput_bind_bind_swap _ _ _ _
  rw [s1]
  have s2 : Pr[= true | do
      let a ← kem.keygen
      let kRand ← ($ᵗ K : ProbComp K)
      let e ← kem.encaps a.1
      let ekA ← kem.keygen
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2 (if b then kRand else e.2)
      pure (b == b')] =
    Pr[= true | do
      let kRand ← ($ᵗ K : ProbComp K)
      let a ← kem.keygen
      let e ← kem.encaps a.1
      let ekA ← kem.keygen
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2 (if b then kRand else e.2)
      pure (b == b')] :=
    probOutput_bind_bind_swap _ _ _ _
  rw [s2]
  have s3 : Pr[= true | do
      let kRand ← ($ᵗ K : ProbComp K)
      let a ← kem.keygen
      let e ← kem.encaps a.1
      let ekA ← kem.keygen
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2 (if b then kRand else e.2)
      pure (b == b')] =
    Pr[= true | do
      let kRand ← ($ᵗ K : ProbComp K)
      let a ← kem.keygen
      let ekA ← kem.keygen
      let e ← kem.encaps a.1
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2 (if b then kRand else e.2)
      pure (b == b')] := by
    refine probOutput_bind_congr fun kRand _ => ?_
    refine probOutput_bind_congr fun a _ => ?_
    exact probOutput_bind_bind_swap _ _ _ _
  rw [s3]
  have s4 : Pr[= true | do
      let kRand ← ($ᵗ K : ProbComp K)
      let a ← kem.keygen
      let ekA ← kem.keygen
      let e ← kem.encaps a.1
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2 (if b then kRand else e.2)
      pure (b == b')] =
    Pr[= true | do
      let kRand ← ($ᵗ K : ProbComp K)
      let ekA ← kem.keygen
      let a ← kem.keygen
      let e ← kem.encaps a.1
      let ekAHat ← kem.keygen
      let b' ← adversary () ekA.1 ekAHat.1 a.1 (ekAHat.1, e.1) ekAHat.2 (if b then kRand else e.2)
      pure (b == b')] := by
    refine probOutput_bind_congr fun kRand _ => ?_
    exact probOutput_bind_bind_swap _ _ _ _
  rw [s4]

/-- The real FS-IND-CPA experiment (`securityExpA`) and the idealized one (`idealSecurityExpA`,
which never substitutes a fresh random bit for a decapsulation failure) are within total-variation
distance `Pr[= false | kem.CorrectExp] / 2` of each other: the two only differ when the underlying
KEM's decapsulation fails, at the very end of the shared randomness (`B`'s key, the challenge
encapsulation, `A`'s next-round key, and the decapsulation itself). Since correctness holds only in
aggregate over this randomness (not for each fixed choice of `B`'s key/ciphertext), the bound is
proved by bundling all of it into one computation `mx` and applying a `1/2`-per-branch bad-event
bound (`ToVCVio.tvDist_bind_left_event_le_const`), with the "bad" event
being decapsulation failure: on that event the two continuations are a fresh coin flip versus some
`Bool`-valued computation, which (by `ToVCVio.tvDist_eq_abs_probOutput_true_sub`) are at most `1/2`
apart in total-variation distance, not the trivial `1` that a naive bad-event bound would give. -/
private lemma tvDist_securityExpA_idealSecurityExpA_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    ENNReal.ofReal (tvDist (RKEMScheme.securityExpA (scheme kem) adversary)
      (idealSecurityExpA kem adversary)) ≤ Pr[= false | kem.CorrectExp] / 2 := by
  unfold RKEMScheme.securityExpA idealSecurityExpA
  simp only [scheme, rkeygen, renc, rdec, pure_bind, bind_assoc]
  refine ofReal_tvDist_bind_left_le_const' _ _ _ _ fun b => ?_
  refine ofReal_tvDist_bind_left_le_const' _ _ _ _ fun k1 => ?_
  refine ofReal_tvDist_bind_left_le_const' _ _ _ _ fun ekAdkA => ?_
  -- Bundle the remaining shared randomness (B's key, the encapsulation, A's next key, and the
  -- decapsulation) into a single computation `mx`: the correctness bound only holds in aggregate
  -- over this randomness, not for each fixed choice of B's key/ciphertext, so none of it can be
  -- peeled off individually the way `b`, `k1`, `ekAdkA` were above.
  set mx : ProbComp (((PK × SK) × (C × K) × (PK × SK)) × Option K) := do
    let ekBdkB ← kem.keygen
    let ct_key ← kem.encaps ekBdkB.1
    let ekAHatdkAHat ← kem.keygen
    let res ← kem.decaps ekBdkB.2 ct_key.1
    pure ((ekBdkB, ct_key, ekAHatdkAHat), res) with hmx_def
  set F : ((PK × SK) × (C × K) × (PK × SK)) × Option K → ProbComp Bool := fun t =>
    (match t.2 with
      | none => (pure none : ProbComp (Option (K × PK)))
      | some k => pure (some (k, t.1.2.2.1))) >>= fun res =>
      match res with
      | none => ($ᵗ Bool : ProbComp Bool)
      | some (_, ekAHat) =>
          adversary () ekAdkA.1 ekAHat t.1.1.1 (t.1.2.2.1, t.1.2.1.1) t.1.2.2.2
            (if b then k1 else t.1.2.1.2) >>= fun b' => pure (b == b') with hF_def
  set G : ((PK × SK) × (C × K) × (PK × SK)) × Option K → ProbComp Bool := fun t =>
    adversary () ekAdkA.1 t.1.2.2.1 t.1.1.1 (t.1.2.2.1, t.1.2.1.1) t.1.2.2.2
      (if b then k1 else t.1.2.1.2) >>= fun b' => pure (b == b') with hG_def
  set my : ProbComp Bool := do
    let ekBdkB ← kem.keygen
    let ct_key ← kem.encaps ekBdkB.1
    let ekAHatdkAHat ← kem.keygen
    adversary () ekAdkA.1 ekAHatdkAHat.1 ekBdkB.1 (ekAHatdkAHat.1, ct_key.1) ekAHatdkAHat.2
      (if b then k1 else ct_key.2) >>= fun b' => pure (b == b') with hmy_def
  -- Replace the goal's original (un-tupled) computations with `mx >>= F` and `my`. This is
  -- proved via `evalDist`/`probOutput` congruence (peeling one shared bind at a time down to the
  -- point where each side's `match` scrutinee is a bound variable that can be cased on), rather
  -- than by asserting the goal's own term as a literal and rewriting: the latter is fragile here
  -- because re-typing `rdec`'s internal `match` produces a *different* (if computationally
  -- identical) compiled match auxiliary than the one already present in the goal from unfolding
  -- `rdec`/`securityExpA`, and those two auxiliaries are not `rfl`-equal until fully applied to a
  -- concrete constructor.
  trans (ENNReal.ofReal (tvDist (mx >>= F) my))
  · refine le_of_eq ?_
    congr 1
    unfold tvDist
    congr 1
    · rw [hmx_def, hF_def]
      refine evalDist_ext fun y => ?_
      simp only [bind_assoc, pure_bind]
      refine probOutput_bind_congr fun ekBdkB _ => ?_
      refine probOutput_bind_congr fun ct_key _ => ?_
      refine probOutput_bind_congr fun ekAHatdkAHat _ => ?_
      refine probOutput_bind_congr fun x_2 _ => ?_
      rcases x_2 with _ | k <;> rfl
  have hGdist : tvDist (mx >>= G) my = 0 := by
    rw [tvDist_eq_zero_iff, hmy_def, hmx_def, hG_def]
    simp only [bind_assoc, pure_bind]
    refine evalDist_bind_congr' kem.keygen fun ekBdkB => ?_
    refine evalDist_bind_congr' (kem.encaps ekBdkB.1) fun ct_key => ?_
    refine evalDist_bind_congr' kem.keygen fun ekAHatdkAHat => ?_
    exact evalDist_ext fun y =>
      probOutput_bind_of_const' (kem.decaps ekBdkB.2 ct_key.1) fun _ _ => rfl
  have htri := tvDist_triangle (mx >>= F) (mx >>= G) my
  rw [hGdist, add_zero] at htri
  refine (ENNReal.ofReal_le_ofReal htri).trans ?_
  -- The two continuations agree exactly off the bad event (decapsulation failure), and on the bad
  -- event `F t` is a fresh coin flip while `G t` is some `Bool`-valued computation, so their
  -- `tvDist` there is at most `1/2` (not the trivial `1`): this halves the naive bad-event bound.
  have h_eq : ∀ t : ((PK × SK) × (C × K) × (PK × SK)) × Option K, ¬ (t.2 = none) →
      𝒟[F t] = 𝒟[G t] := by
    rintro ⟨s, x2⟩ hx2
    rw [hF_def, hG_def]
    obtain ⟨k, rfl⟩ := Option.ne_none_iff_exists'.mp hx2
    rfl
  have h_le : ∀ t : ((PK × SK) × (C × K) × (PK × SK)) × Option K, t.2 = none →
      tvDist (F t) (G t) ≤ (1 / 2 : ℝ) := by
    intro t ht
    have hFt : F t = ($ᵗ Bool : ProbComp Bool) := by rw [hF_def]; simp [ht]
    rw [hFt, ToVCVio.tvDist_eq_abs_probOutput_true_sub]
    have h1 : (Pr[= true | ($ᵗ Bool : ProbComp Bool)]).toReal = 1 / 2 := by
      simp [probOutput_uniformSample, Fintype.card_bool]
    have h2 : (0 : ℝ) ≤ (Pr[= true | G t]).toReal := ENNReal.toReal_nonneg
    have h3 : (Pr[= true | G t]).toReal ≤ 1 := by
      have h := ENNReal.toReal_mono ENNReal.one_ne_top (probOutput_le_one (mx := G t) (x := true))
      rwa [ENNReal.toReal_one] at h
    rw [h1, abs_le]
    constructor <;> linarith
  have htv : tvDist (mx >>= F) (mx >>= G) ≤ (1 / 2 : ℝ) *
      Pr[fun t : ((PK × SK) × (C × K) × (PK × SK)) × Option K => t.2 = none | mx].toReal :=
    ToVCVio.tvDist_bind_left_event_le_const mx F G (fun t => t.2 = none) (1 / 2) (by norm_num)
      h_eq h_le
  have hbad_le : Pr[fun t : ((PK × SK) × (C × K) × (PK × SK)) × Option K => t.2 = none | mx] ≤
      Pr[= false | kem.CorrectExp] := by
    have hproj : Prod.snd <$> mx =
        (kem.keygen >>= fun ekBdkB => kem.encaps ekBdkB.1 >>= fun ct_key =>
          kem.keygen >>= fun _ => kem.decaps ekBdkB.2 ct_key.1 : ProbComp (Option K)) := by
      rw [hmx_def]
      simp
    have hmarg : Pr[fun t : ((PK × SK) × (C × K) × (PK × SK)) × Option K => t.2 = none | mx] =
        Pr[= (none : Option K) | kem.keygen >>= fun ekBdkB => kem.encaps ekBdkB.1 >>= fun ct_key =>
          kem.keygen >>= fun _ => kem.decaps ekBdkB.2 ct_key.1] := by
      rw [← hproj, probOutput_map]
    rw [hmarg]
    have hdrop : Pr[= (none : Option K) | kem.keygen >>= fun ekBdkB => kem.encaps ekBdkB.1 >>=
        fun ct_key => kem.keygen >>= fun _ => kem.decaps ekBdkB.2 ct_key.1] =
        Pr[= (none : Option K) | kem.keygen >>= fun ekBdkB => kem.encaps ekBdkB.1 >>=
          fun ct_key => kem.decaps ekBdkB.2 ct_key.1] := by
      refine probOutput_bind_congr fun ekBdkB _ => ?_
      refine probOutput_bind_congr fun ct_key _ => ?_
      exact probOutput_bind_of_const' kem.keygen fun _ _ => rfl
    rw [hdrop]
    exact probOutput_none_decaps_le_probOutput_false_CorrectExp kem
  refine (ENNReal.ofReal_le_ofReal htv).trans ?_
  rw [show (1 / 2 : ℝ) *
      Pr[fun t : ((PK × SK) × (C × K) × (PK × SK)) × Option K => t.2 = none | mx].toReal =
      Pr[fun t : ((PK × SK) × (C × K) × (PK × SK)) × Option K => t.2 = none | mx].toReal / 2 from
      by ring,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_toReal probEvent_ne_top,
    show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) from by norm_num]
  gcongr

/-- Reduction bound: the RKEM-from-KEM construction's `A`-side FS-IND-CPA advantage is bounded by
half the underlying KEM's IND-CPA advantage against the reduction adversary, plus half the
probability that the KEM's own correctness experiment returns `false`. (The first `/ 2` is not
lossiness: it converts VCVio's `IND_CPA_Advantage` distinguishing convention into Def. 5.4's bias
convention — see the module docstring. The second `/ 2` comes from the tightened
`tvDist_securityExpA_idealSecurityExpA_le`.) -/
theorem fsIndCpaAdvantageA_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.fsIndCpaAdvantageA (scheme kem) adversary ≤
      kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary) / 2 +
        (Pr[= false | kem.CorrectExp]).toReal / 2 := by
  unfold RKEMScheme.fsIndCpaAdvantageA
  have h1 : |(Pr[= true | RKEMScheme.securityExpA (scheme kem) adversary]).toReal -
      (Pr[= true | idealSecurityExpA kem adversary]).toReal| ≤
      (Pr[= false | kem.CorrectExp]).toReal / 2 := by
    have h := (abs_probOutput_toReal_sub_le_tvDist _ _).trans
      ((ENNReal.ofReal_le_iff_le_toReal (ENNReal.div_ne_top probOutput_ne_top two_ne_zero)).mp
        (tvDist_securityExpA_idealSecurityExpA_le kem adversary))
    rwa [ENNReal.toReal_div] at h
  rw [← probOutput_true_indCpaGame_eq_probOutput_true_idealSecurityExpA kem adversary] at h1
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
  have h3 : kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary) / 2 =
      |(Pr[= true | KEMScheme.IND_CPA_Game ProbCompRuntime.probComp
        (indCpaReduction kem adversary)]).toReal - 1 / 2| := by
    rw [IND_CPA_Advantage_eq_game_bias,
      SPMF.boolBiasAdvantage_eq_two_mul_abs_sub_half _ htotal]
    ring
  calc |(Pr[= true | RKEMScheme.securityExpA (scheme kem) adversary]).toReal - 1 / 2|
      ≤ |(Pr[= true | RKEMScheme.securityExpA (scheme kem) adversary]).toReal -
          (Pr[= true | KEMScheme.IND_CPA_Game ProbCompRuntime.probComp
            (indCpaReduction kem adversary)]).toReal| +
        |(Pr[= true | KEMScheme.IND_CPA_Game ProbCompRuntime.probComp
            (indCpaReduction kem adversary)]).toReal - 1 / 2| := abs_sub_le _ _ _
    _ ≤ (Pr[= false | kem.CorrectExp]).toReal / 2 +
        kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary) / 2 := by
        rw [← h3]; exact add_le_add h1 le_rfl
    _ = kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary) / 2 +
        (Pr[= false | kem.CorrectExp]).toReal / 2 := by ring

/-- As `fsIndCpaAdvantageA_le`, with the roles of `A` and `B` swapped: since the RKEM-from-KEM
construction treats both parties identically (`securityExpB_eq_securityExpA`), the same reduction
bound applies to the `B`-side advantage against the very same reduction adversary. (Same `/ 2`
convention-conversion caveat as `fsIndCpaAdvantageA_le`.) -/
theorem fsIndCpaAdvantageB_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.fsIndCpaAdvantageB (scheme kem) adversary ≤
      kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary) / 2 +
        (Pr[= false | kem.CorrectExp]).toReal / 2 := by
  unfold RKEMScheme.fsIndCpaAdvantageB
  rw [securityExpB_eq_securityExpA]
  exact fsIndCpaAdvantageA_le kem adversary

/-- **FS-IND-CPA security reduction bound** for the RKEM-from-KEM construction: against any pair
of adversaries, the construction is FS-IND-CPA-secure at the epsilon obtained by combining
`fsIndCpaAdvantageA_le` and `fsIndCpaAdvantageB_le` — half the worse of the two IND-CPA advantages
against the corresponding reduction adversaries, plus half the underlying KEM's own
correctness-failure probability. (Same `/ 2` caveats as `fsIndCpaAdvantageA_le` — see the module
docstring.) -/
theorem fsIndCpaAdvantage_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adversaryA adversaryB : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.FSINDCPASecure (scheme kem) adversaryA adversaryB
      (max
        (kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversaryA))
        (kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversaryB)) / 2 +
        (Pr[= false | kem.CorrectExp]).toReal / 2) := by
  unfold RKEMScheme.FSINDCPASecure RKEMScheme.fsIndCpaAdvantage
  set a := kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversaryA)
  set b := kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversaryB)
  set c := (Pr[= false | kem.CorrectExp]).toReal / 2
  have hmax : max a b / 2 + c = max (a / 2 + c) (b / 2 + c) := by
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (by gcongr)]
    · rw [max_eq_left h, max_eq_left (by gcongr)]
  rw [hmax]
  exact max_le_max (fsIndCpaAdvantageA_le kem adversaryA) (fsIndCpaAdvantageB_le kem adversaryB)

/-- **FS-IND-CPA security** of the RKEM-from-KEM construction: if the underlying KEM is
`ε`-IND-CPA-secure (uniformly over every adversary) and `δ`-correct, the construction is
FS-IND-CPA-secure at `ε / 2 + δ / 2`. (The first `/ 2` is the same convention conversion as in
`fsIndCpaAdvantageA_le`, not a lossy step — see the module docstring. The second `/ 2` comes from
the tightened `tvDist_securityExpA_idealSecurityExpA_le`.) -/
-- ANCHOR: FSINDCPASecure
theorem FSINDCPASecure [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (ε : ℝ) (δ : ℝ≥0)
    (hcpa : ∀ adv : kem.IND_CPA_Adversary,
      kem.IND_CPA_Advantage ProbCompRuntime.probComp adv ≤ ε)
    (hcorr : kem.deltaCorrect ProbCompRuntime.probComp δ)
    (adversaryA adversaryB : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.FSINDCPASecure (scheme kem) adversaryA adversaryB (ε / 2 + δ / 2)
-- ANCHOR_END: FSINDCPASecure
    := by
  have hfail : Pr[= false | kem.CorrectExp] ≤ (δ : ℝ≥0∞) :=
    calc Pr[= false | kem.CorrectExp]
        ≤ Pr[= false | kem.CorrectExp] + Pr[⊥ | kem.CorrectExp] := le_self_add
      _ = kem.correctnessError ProbCompRuntime.probComp :=
          (correctnessError_eq_probOutput_false_add_probFailure kem ProbCompRuntime.probComp).symm
      _ ≤ (δ : ℝ≥0∞) := hcorr
  have hfail_toReal : (Pr[= false | kem.CorrectExp]).toReal / 2 ≤ (δ : ℝ) / 2 := by
    have h := ENNReal.toReal_mono ENNReal.coe_ne_top hfail
    rw [ENNReal.coe_toReal] at h
    linarith
  unfold RKEMScheme.FSINDCPASecure RKEMScheme.fsIndCpaAdvantage
  refine max_le ((fsIndCpaAdvantageA_le kem adversaryA).trans ?_)
    ((fsIndCpaAdvantageB_le kem adversaryB).trans ?_)
  · exact add_le_add (by gcongr; exact hcpa _) hfail_toReal
  · exact add_le_add (by gcongr; exact hcpa _) hfail_toReal

/-- **FS-IND-CPA security** of the RKEM-from-KEM construction, as the perfectly-correct special
case of `FSINDCPASecure`: if the underlying KEM is `ε`-IND-CPA-secure (uniformly over every
adversary) and perfectly correct, the construction is FS-IND-CPA-secure at exactly `ε / 2`, with
no additive correctness slack (`δ = 0`). (The `/ 2` is the same convention conversion as in
`fsIndCpaAdvantageA_le`, not a lossy step.) -/
theorem FSINDCPASecure_of_perfectlyCorrect [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (ε : ℝ)
    (hcpa : ∀ adv : kem.IND_CPA_Adversary,
      kem.IND_CPA_Advantage ProbCompRuntime.probComp adv ≤ ε)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adversaryA adversaryB : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.FSINDCPASecure (scheme kem) adversaryA adversaryB (ε / 2) := by
  have hcorr : kem.deltaCorrect ProbCompRuntime.probComp 0 := by
    rw [KEMScheme.deltaCorrect,
      (correctnessError_eq_zero_iff_perfectlyCorrect kem ProbCompRuntime.probComp).mpr hkem]
  have h := FSINDCPASecure kem ε 0 hcpa hcorr adversaryA adversaryB
  rwa [NNReal.coe_zero, zero_div, add_zero] at h

end kemRKEM
