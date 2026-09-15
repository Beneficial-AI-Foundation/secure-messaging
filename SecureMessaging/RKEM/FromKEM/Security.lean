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
for the probability that the underlying KEM's decapsulation fails, which is bounded via a
total-variation-distance argument against an "idealized" experiment that never falls back to a
random bit on decapsulation failure (`tvDist_securityExpA_idealSecurityExpA_le`). Combining the two
gives the per-party reduction bounds `fsIndCpaAdvantageA_le`/`fsIndCpaAdvantageB_le`, and hence the
top-level `FSINDCPASecure`.
-/

open ToVCVio KEMScheme RKEMScheme

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
key"); this proof reorders the independent samples to align the two games, then shows the flipped
convention doesn't matter by handling the `b = true` and `b = false` cases separately (`h1`, `h2`)
and averaging. -/
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
  rw [probOutput_bind_uniformBool, probOutput_bind_uniformBool]
  simp only [reduceIte, Bool.false_eq_true, if_false]
  have h1 : Pr[= true | do
      let a ← kem.keygen
      let __x ← kem.encaps a.1
      let _ ← ($ᵗ K : ProbComp K)
      let x ← kem.keygen
      let x_1 ← kem.keygen
      let x' ← adversary () x.1 x_1.1 a.1 (x_1.1, __x.1) x_1.2 __x.2
      pure (true == !x')] =
    Pr[= true | do
      let _ ← ($ᵗ K : ProbComp K)
      let __x ← kem.keygen
      let __x_1 ← kem.keygen
      let __x_2 ← kem.encaps __x_1.1
      let __x_3 ← kem.keygen
      let b' ← adversary () __x.1 __x_3.1 __x_1.1 (__x_3.1, __x_2.1) __x_3.2 __x_2.2
      pure (false == b')] := by
    rw [probOutput_bind_of_const' ($ᵗ K : ProbComp K) fun _ _ => rfl]
    have hdrop : Pr[= true | do
        let a ← kem.keygen
        let e ← kem.encaps a.1
        let _ ← ($ᵗ K : ProbComp K)
        let x ← kem.keygen
        let x_1 ← kem.keygen
        let x' ← adversary () x.1 x_1.1 a.1 (x_1.1, e.1) x_1.2 e.2
        pure (true == !x')] =
      Pr[= true | do
        let a ← kem.keygen
        let e ← kem.encaps a.1
        let x ← kem.keygen
        let x_1 ← kem.keygen
        let x' ← adversary () x.1 x_1.1 a.1 (x_1.1, e.1) x_1.2 e.2
        pure (true == !x')] := by
      refine probOutput_bind_congr fun a _ => ?_
      refine probOutput_bind_congr fun e _ => ?_
      exact probOutput_bind_of_const' ($ᵗ K : ProbComp K) fun _ _ => rfl
    rw [hdrop]
    have hswap1 : Pr[= true | do
        let a ← kem.keygen
        let e ← kem.encaps a.1
        let x ← kem.keygen
        let x_1 ← kem.keygen
        let x' ← adversary () x.1 x_1.1 a.1 (x_1.1, e.1) x_1.2 e.2
        pure (true == !x')] =
      Pr[= true | do
        let a ← kem.keygen
        let x ← kem.keygen
        let e ← kem.encaps a.1
        let x_1 ← kem.keygen
        let x' ← adversary () x.1 x_1.1 a.1 (x_1.1, e.1) x_1.2 e.2
        pure (true == !x')] := by
      refine probOutput_bind_congr fun a _ => ?_
      exact probOutput_bind_bind_swap _ _ _ _
    rw [hswap1, probOutput_bind_bind_swap]
    refine probOutput_bind_congr fun b _ => ?_
    refine probOutput_bind_congr fun a _ => ?_
    refine probOutput_bind_congr fun e _ => ?_
    refine probOutput_bind_congr fun x_1 _ => ?_
    refine probOutput_bind_congr fun x' _ => ?_
    cases x' <;> rfl
  have h2 : Pr[= true | do
      let a ← kem.keygen
      let __x ← kem.encaps a.1
      let kRand ← ($ᵗ K : ProbComp K)
      let x ← kem.keygen
      let x_1 ← kem.keygen
      let x' ← adversary () x.1 x_1.1 a.1 (x_1.1, __x.1) x_1.2 kRand
      pure (false == !x')] =
    Pr[= true | do
      let k1 ← ($ᵗ K : ProbComp K)
      let __x ← kem.keygen
      let __x_1 ← kem.keygen
      let __x_2 ← kem.encaps __x_1.1
      let __x_3 ← kem.keygen
      let b' ← adversary () __x.1 __x_3.1 __x_1.1 (__x_3.1, __x_2.1) __x_3.2 k1
      pure (true == b')] := by
    have hswap2 : Pr[= true | do
        let a ← kem.keygen
        let e ← kem.encaps a.1
        let f ← ($ᵗ K : ProbComp K)
        let x ← kem.keygen
        let x_1 ← kem.keygen
        let x' ← adversary () x.1 x_1.1 a.1 (x_1.1, e.1) x_1.2 f
        pure (false == !x')] =
      Pr[= true | do
        let a ← kem.keygen
        let f ← ($ᵗ K : ProbComp K)
        let e ← kem.encaps a.1
        let x ← kem.keygen
        let x_1 ← kem.keygen
        let x' ← adversary () x.1 x_1.1 a.1 (x_1.1, e.1) x_1.2 f
        pure (false == !x')] := by
      refine probOutput_bind_congr fun a _ => ?_
      exact probOutput_bind_bind_swap _ _ _ _
    rw [hswap2, probOutput_bind_bind_swap]
    refine probOutput_bind_congr fun f _ => ?_
    have hswap3 : Pr[= true | do
        let a ← kem.keygen
        let e ← kem.encaps a.1
        let x ← kem.keygen
        let x_1 ← kem.keygen
        let x' ← adversary () x.1 x_1.1 a.1 (x_1.1, e.1) x_1.2 f
        pure (false == !x')] =
      Pr[= true | do
        let a ← kem.keygen
        let x ← kem.keygen
        let e ← kem.encaps a.1
        let x_1 ← kem.keygen
        let x' ← adversary () x.1 x_1.1 a.1 (x_1.1, e.1) x_1.2 f
        pure (false == !x')] := by
      refine probOutput_bind_congr fun a _ => ?_
      exact probOutput_bind_bind_swap _ _ _ _
    rw [hswap3, probOutput_bind_bind_swap]
    refine probOutput_bind_congr fun b _ => ?_
    refine probOutput_bind_congr fun a _ => ?_
    refine probOutput_bind_congr fun e _ => ?_
    refine probOutput_bind_congr fun x_1 _ => ?_
    refine probOutput_bind_congr fun x' _ => ?_
    cases x' <;> rfl
  rw [h1, h2, add_comm]

/-- The real FS-IND-CPA experiment (`securityExpA`) and the idealized one (`idealSecurityExpA`,
which never substitutes a fresh random bit for a decapsulation failure) are within total-variation
distance `Pr[= false | kem.CorrectExp]` of each other: the two only differ when the underlying
KEM's decapsulation fails, at the very end of the shared randomness (`B`'s key, the challenge
encapsulation, `A`'s next-round key, and the decapsulation itself). Since correctness holds only in
aggregate over this randomness (not for each fixed choice of `B`'s key/ciphertext), the bound is
proved by bundling all of it into one computation `mx` and applying the generic bad-event bound
`ofReal_tvDist_bind_left_event_le`, with the "bad" event being decapsulation failure. -/
private lemma tvDist_securityExpA_idealSecurityExpA_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    ENNReal.ofReal (tvDist (RKEMScheme.securityExpA (scheme kem) adversary)
      (idealSecurityExpA kem adversary)) ≤ Pr[= false | kem.CorrectExp] := by
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
  refine (ofReal_tvDist_bind_left_event_le mx F G (fun t => t.2 = none) ?_).trans ?_
  · rintro ⟨s, x2⟩ hx2
    rw [hF_def, hG_def]
    obtain ⟨k, rfl⟩ := Option.ne_none_iff_exists'.mp hx2
    rfl
  · have hproj : Prod.snd <$> mx =
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

/-- Reduction bound: the RKEM-from-KEM construction's `A`-side FS-IND-CPA advantage is bounded by
half the underlying KEM's IND-CPA advantage against the reduction adversary, plus the probability
that the KEM's own correctness experiment returns `false`. -/
theorem fsIndCpaAdvantageA_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.fsIndCpaAdvantageA (scheme kem) adversary ≤
      kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary) / 2 +
        (Pr[= false | kem.CorrectExp]).toReal := by
  unfold RKEMScheme.fsIndCpaAdvantageA
  have h1 : |(Pr[= true | RKEMScheme.securityExpA (scheme kem) adversary]).toReal -
      (Pr[= true | idealSecurityExpA kem adversary]).toReal| ≤
      (Pr[= false | kem.CorrectExp]).toReal :=
    (abs_probOutput_toReal_sub_le_tvDist _ _).trans
      ((ENNReal.ofReal_le_iff_le_toReal probOutput_ne_top).mp
        (tvDist_securityExpA_idealSecurityExpA_le kem adversary))
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
    _ ≤ (Pr[= false | kem.CorrectExp]).toReal +
        kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary) / 2 := by
        rw [← h3]; exact add_le_add h1 le_rfl
    _ = kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary) / 2 +
        (Pr[= false | kem.CorrectExp]).toReal := by ring

/-- As `fsIndCpaAdvantageA_le`, with the roles of `A` and `B` swapped: since the RKEM-from-KEM
construction treats both parties identically (`securityExpB_eq_securityExpA`), the same reduction
bound applies to the `B`-side advantage against the very same reduction adversary. -/
theorem fsIndCpaAdvantageB_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.fsIndCpaAdvantageB (scheme kem) adversary ≤
      kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversary) / 2 +
        (Pr[= false | kem.CorrectExp]).toReal := by
  unfold RKEMScheme.fsIndCpaAdvantageB
  rw [securityExpB_eq_securityExpA]
  exact fsIndCpaAdvantageA_le kem adversary

/-- **FS-IND-CPA security** (Def. 5.4) of the RKEM-from-KEM construction: against any pair of
adversaries, the construction is FS-IND-CPA-secure at the epsilon obtained by combining
`fsIndCpaAdvantageA_le` and `fsIndCpaAdvantageB_le` — half the worse of the two IND-CPA advantages
against the corresponding reduction adversaries, plus the underlying KEM's own
correctness-failure probability. -/
-- ANCHOR: FSINDCPASecure
theorem FSINDCPASecure [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (adversaryA adversaryB : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.FSINDCPASecure (scheme kem) adversaryA adversaryB
      (max
        (kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversaryA) / 2 +
          (Pr[= false | kem.CorrectExp]).toReal)
        (kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversaryB) / 2 +
          (Pr[= false | kem.CorrectExp]).toReal))
-- ANCHOR_END: FSINDCPASecure
    := by
  unfold RKEMScheme.FSINDCPASecure RKEMScheme.fsIndCpaAdvantage
  exact max_le_max (fsIndCpaAdvantageA_le kem adversaryA) (fsIndCpaAdvantageB_le kem adversaryB)

/-- **FS-IND-CPA security** of the RKEM-from-KEM construction, as the perfectly-correct special
case of `FSINDCPASecure`: if the underlying KEM is perfectly correct, its correctness-failure
probability vanishes, so the additive slack in `FSINDCPASecure`'s epsilon drops out and the
construction is FS-IND-CPA-secure at exactly half the worse of the two IND-CPA advantages against
the corresponding reduction adversaries. -/
theorem FSINDCPASecure_of_perfectlyCorrect [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adversaryA adversaryB : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.FSINDCPASecure (scheme kem) adversaryA adversaryB
      (max
        (kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversaryA) / 2)
        (kem.IND_CPA_Advantage ProbCompRuntime.probComp (indCpaReduction kem adversaryB) / 2)) := by
  have heq : kem.correctnessError ProbCompRuntime.probComp =
      Pr[= false | kem.CorrectExp] + Pr[⊥ | kem.CorrectExp] :=
    correctnessError_eq_probOutput_false_add_probFailure kem ProbCompRuntime.probComp
  have hzero' : kem.correctnessError ProbCompRuntime.probComp = 0 :=
    (correctnessError_eq_zero_iff_perfectlyCorrect kem ProbCompRuntime.probComp).mpr hkem
  have hzero : Pr[= false | kem.CorrectExp] = 0 :=
    le_antisymm
      (calc Pr[= false | kem.CorrectExp]
          ≤ Pr[= false | kem.CorrectExp] + Pr[⊥ | kem.CorrectExp] := le_self_add
        _ = kem.correctnessError ProbCompRuntime.probComp := heq.symm
        _ = 0 := hzero')
      bot_le
  have h := FSINDCPASecure kem adversaryA adversaryB
  rwa [hzero, ENNReal.toReal_zero, add_zero, add_zero] at h

end kemRKEM
