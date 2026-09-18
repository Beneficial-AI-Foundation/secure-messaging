/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Axu
import SecureMessaging.AEAD.FromGCM.Security.Games
import ToVCVio.CryptoFoundations.WegmanCarter
import ToVCVio.ProgramLogic.Relational.IdenticalUntilBad

/-!
# GCM: the authenticity hop (`game2` → `game3`)

Replaces the live-verification game `game2` by the always-reject game `game3`. The two agree
unless some decryption query carries a valid tag for a ciphertext the adversary was never
given. Such a forgery means the adversary hit the output of GHASH at the unknown key `H`,
which the almost-XOR-universal (AXU) bound `GhashIsAXU L ε` (`Axu.lean`) caps at `ε` per
query, so the hop costs `q_d · ε` (the Wegman–Carter forgery bound).

The GCM handlers are, by definition, the generic Wegman–Carter handler of
`ToVCVio/CryptoFoundations/WegmanCarter.lean` (`gcmInstImpl_eq_wcInstImpl` is `rfl`), and the
two games
are compared by the identical-until-bad principle: games whose oracles behave identically until
a flag is set differ by at most the probability of the flag
(`ToVCVio/ProgramLogic/Relational/IdenticalUntilBad.lean`).

A successful decryption in `game2` returns `C' ^^^ ks` and so leaks the keystream, which is why
the privacy hop (`PrivacyHop.lean`) comes after this one.

Main result: `game2_game3_le_auth`.
-/

namespace GCM

open OracleSpec OracleComp ENNReal AEADScheme ToVCVio
open AEADScheme.aeadOneTimeCCASpec
open OracleComp.ProgramLogic.Relational
open OracleComp.WegmanCarter

/-! ## Spec identification

`ToVCVio` cannot import `SecureMessaging`, so the one-time CCA spec is spelled inline there as
`wcSpec`; this `example` checks that it is `aeadOneTimeCCASpec`. -/
example (A M Cb : Type) :
    OracleComp.WegmanCarter.wcSpec A M Cb =
      AEADScheme.aeadOneTimeCCASpec A M (Cb × BitVec 128) := rfl

/-! ## The bridging lemma -/

/-- `gcmInstImpl` unfolds to the generic Wegman–Carter handler by definition. Nothing rewrites
with this: it pins the coupling at compile time, so a change to either handler that breaks
`probEvent_forge_gcmInst_le` is reported here first. -/
theorem gcmInstImpl_eq_wcInstImpl (L : ℕ) (h mask : BitVec 128) (ks : BitVec L)
    (b : Bool) :
    gcmInstImpl (L := L) (h, mask, ks) b =
      OracleComp.WegmanCarter.wcInstImpl
        (A := SupportedAAD) (M := BitVec L) (Cb := BitVec L)
        (K := BitVec 128) (D := SupportedAAD × BitVec L)
        (fun H p => ghash H (gcmEncode p.1 p.2)) id h mask
        (fun m => m ^^^ ks) (fun c => c ^^^ ks) b :=
  rfl

/-! ## The per-tuple forgery bound -/

/-- At a fixed keystream, with the GHASH key and the tag mask uniform, the always-reject
execution raises its `forged` flag with probability at most `q_d · ε`. This is the generic
`probEvent_wcInst_forge_le` itself, since `gcmInstImpl` is definitionally the Wegman–Carter
handler (`gcmInstImpl_eq_wcInstImpl`). -/
theorem probEvent_forge_gcmInst_le (L : ℕ) {ε : ℝ≥0∞} (haxu : GhashIsAXU L ε)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) (ks : BitVec L) :
    Pr[fun z : Bool × (Option (BitVec L × BitVec 128) × Bool) => z.2.2 = true |
        (do let h ← ($ᵗ (BitVec 128) : ProbComp _)
            let mask ← ($ᵗ (BitVec 128) : ProbComp _)
            (simulateQ (gcmInstImpl (h, mask, ks) false) adv).run (none, false))]
      ≤ (q_d : ℝ≥0∞) * ε :=
  -- `decryptQueryBound` and the generic bound spell the decrypt-index predicate with different
  -- matcher auxiliaries, hence the `isQueryBoundP_congr_pred` transport of `hq`.
  probEvent_wcInst_forge_le haxu (ghashAXU_eps_lower haxu) Function.injective_id
    (fun m => m ^^^ ks) (fun c => c ^^^ ks) adv q_d
    ((isQueryBoundP_congr_pred (fun queryIndex => by cases queryIndex <;> rfl)).mp hq)

/-! ### The flag-monotonicity helper -/

/-- Once the `forged` flag is set, no oracle of `gcmInstImpl a b` clears it, at either `b`. -/
private theorem gcmInstImpl_flag_mono (L : ℕ)
    (a : BitVec 128 × BitVec 128 × BitVec L) (b : Bool)
    (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128)).Domain)
    (p : Option (BitVec L × BitVec 128) × Bool) (hp : p.2 = true) :
    ∀ z ∈ support (((gcmInstImpl a b) t).run p), z.2.2 = true := by
  obtain ⟨ch, fg⟩ := p
  obtain rfl : fg = true := hp
  intro z hz
  rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩
  · -- OUnif: the lifted uniform oracle threads both state slots unchanged.
    simp only [add_apply_inl, gcmInstImpl, wcInstImpl, unifLiftStateT, QueryImpl.ofLift_eq_id',
      bind_pure_comp, beq_iff_eq, decide_eq_true_eq, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply, QueryImpl.id'_apply, StateT.run_monadLift,
      monadLift_self, support_map, support_liftM, OracleQuery.input_query,
      OracleQuery.cont_query, Set.range_id, Set.image_univ] at hz
    obtain ⟨w, hw⟩ := hz
    exact hw ▸ rfl
  · -- OEncrypt: one-shot; the flag is written back unchanged in both branches.
    obtain ⟨h, mask, ks⟩ := a
    cases ch <;>
      simp [gcmInstImpl, wcInstImpl, StateT.run_bind, StateT.run_get, StateT.run_set,
        StateT.run_pure, StateT.run_map] at hz <;>
      simp [hz]
  · -- ODecrypt: guard split, then `ok` split; `true || ok = true` in every branch.
    obtain ⟨h, mask, ks⟩ := a
    simp [gcmInstImpl, wcInstImpl, StateT.run_bind, StateT.run_get] at hz
    split_ifs at hz <;> simp_all

/-- The three conditions the identical-until-bad lemma
(`tvDist_simulateQ_le_probEvent_output_bad_base`) asks of the always-reject and live handlers:
on every transition that leaves the flag unset they agree exactly, and once the flag is set it
stays set on both. They hold because the two handlers differ only in what a decryption query
returns when the tag verifies, and that transition sets the flag. -/
theorem gcmInstImpl_identicalUntilBad (L : ℕ)
    (a : BitVec 128 × BitVec 128 × BitVec L) :
    (∀ (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
               (BitVec L × BitVec 128)).Domain)
        (s : Option (BitVec L × BitVec 128))
        (u : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
               (BitVec L × BitVec 128)).Range t)
        (s' : Option (BitVec L × BitVec 128)),
      Pr[= (u, (s', false)) | ((gcmInstImpl a false) t).run (s, false)] =
        Pr[= (u, (s', false)) | ((gcmInstImpl a true) t).run (s, false)])
    ∧ (∀ (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
                 (BitVec L × BitVec 128)).Domain)
          (p : Option (BitVec L × BitVec 128) × Bool), p.2 = true →
        ∀ z ∈ support (((gcmInstImpl a false) t).run p), z.2.2 = true)
    ∧ (∀ (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
                 (BitVec L × BitVec 128)).Domain)
          (p : Option (BitVec L × BitVec 128) × Bool), p.2 = true →
        ∀ z ∈ support (((gcmInstImpl a true) t).run p), z.2.2 = true) := by
  refine ⟨?_, fun t p hp => gcmInstImpl_flag_mono L a false t p hp,
    fun t p hp => gcmInstImpl_flag_mono L a true t p hp⟩
  rintro ((n | ⟨ad, m⟩) | ⟨ad, e⟩) s u s'
  · -- OUnif: `b` does not occur in this summand.
    rfl
  · -- OEncrypt: `b` does not occur in this summand.
    rfl
  · -- ODecrypt: under the guard both branches are `pure none` at an unchanged state; off
    -- the guard, `ok = false` makes both `pure none` at flag `false`, and `ok = true`
    -- makes both sides write flag `true`, so the observed `false`-flag transition has
    -- probability `0` on each side (this is the transition the two handlers differ on).
    obtain ⟨h, mask, ks⟩ := a
    by_cases hguard : s = some e
    · simp [gcmInstImpl, wcInstImpl, StateT.run_bind, StateT.run_get,
        StateT.run_pure, beq_iff_eq, hguard]
    · by_cases hok : (e.2 = ghash h (gcmEncode ad e.1) ^^^ mask) <;>
        simp [gcmInstImpl, wcInstImpl, StateT.run_bind, StateT.run_get, StateT.run_set,
          beq_iff_eq, hguard, hok]

/-- The identical-until-bad principle at a fixed tuple: the always-reject and the live runs are
within total-variation distance `Pr[forged]` of each other, where the flag is read on the
always-reject side. That side is the one `probEvent_forge_gcmInst_le` can bound, since it never
returns a decrypted ciphertext and so never leaks the keystream. -/
theorem gcmInst_tvDist_le_probEvent_forge (L : ℕ)
    (a : BitVec 128 × BitVec 128 × BitVec L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    tvDist ((simulateQ (gcmInstImpl a false) adv).run' (none, false))
        ((simulateQ (gcmInstImpl a true) adv).run' (none, false))
      ≤ Pr[fun z : Bool × (Option (BitVec L × BitVec 128) × Bool) => z.2.2 = true |
          (simulateQ (gcmInstImpl a false) adv).run (none, false)].toReal := by
  obtain ⟨h_agree_good, h_mono₁, h_mono₂⟩ := gcmInstImpl_identicalUntilBad L a
  exact tvDist_simulateQ_le_probEvent_output_bad_base (gcmInstImpl a false)
    (gcmInstImpl a true) adv none h_agree_good h_mono₁ h_mono₂

/-! ### Lifting the per-tuple bound across the tuple sample -/

/-- `gcmInst_tvDist_le_probEvent_forge` averaged over the uniform tuple draw. -/
private theorem tvDist_gcmInstFlat_le_probEvent_forge (L : ℕ)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    tvDist (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>=
              fun a => (simulateQ (gcmInstImpl a false) adv).run' (none, false))
        (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>=
              fun a => (simulateQ (gcmInstImpl a true) adv).run' (none, false))
      ≤ (Pr[fun z : Bool × (Option (BitVec L × BitVec 128) × Bool) => z.2.2 = true |
            (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>=
              fun a => (simulateQ (gcmInstImpl a false) adv).run (none, false))]).toReal := by
  refine le_trans (tvDist_bind_left_le _ _ _) ?_
  rw [probEvent_bind_eq_tsum]
  rw [ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top
    (ne_top_of_le_ne_top one_ne_top probOutput_le_one)
    (ne_top_of_le_ne_top one_ne_top probEvent_le_one))]
  refine Summable.tsum_le_tsum (fun a => ?_) Summable.of_finite Summable.of_finite
  rw [ENNReal.toReal_mul]
  exact mul_le_mul_of_nonneg_left (gcmInst_tvDist_le_probEvent_forge L a adv)
    ENNReal.toReal_nonneg

/-- The tuple draw split into three independent draws with the keystream outermost, the shape
`probEvent_forge_gcmInst_le` is stated in. -/
private theorem evalDist_gcmInstRun_ks_outer (L : ℕ)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    𝒟[($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>=
        fun a => (simulateQ (gcmInstImpl a false) adv).run (none, false)] =
      𝒟[($ᵗ (BitVec L) : ProbComp _) >>= fun ks =>
          (do let h ← ($ᵗ (BitVec 128) : ProbComp _)
              let mask ← ($ᵗ (BitVec 128) : ProbComp _)
              (simulateQ (gcmInstImpl (h, mask, ks) false) adv).run (none, false))] := by
  rw [uniformSample_prod_eq_bind (BitVec 128) (BitVec 128 × BitVec L)]
  simp only [bind_assoc, pure_bind]
  rw [uniformSample_prod_eq_bind (BitVec 128) (BitVec L)]
  simp only [bind_assoc, pure_bind]
  refine (evalDist_bind_congr' _ (fun h =>
      evalDist_bind_bind_swap ($ᵗ (BitVec 128) : ProbComp _)
        ($ᵗ (BitVec L) : ProbComp _)
        (fun mask ks =>
          (simulateQ (gcmInstImpl (h, mask, ks) false) adv).run (none, false)))).trans
    (evalDist_bind_bind_swap ($ᵗ (BitVec 128) : ProbComp _)
      ($ᵗ (BitVec L) : ProbComp _)
      (fun h ks =>
        (do let mask ← ($ᵗ (BitVec 128) : ProbComp _)
            (simulateQ (gcmInstImpl (h, mask, ks) false) adv).run (none, false))))

private theorem probEvent_forge_gcmInstFlat_le (L : ℕ) {ε : ℝ≥0∞} (haxu : GhashIsAXU L ε)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) :
    Pr[fun z : Bool × (Option (BitVec L × BitVec 128) × Bool) => z.2.2 = true |
        (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>=
          fun a => (simulateQ (gcmInstImpl a false) adv).run (none, false))]
      ≤ (q_d : ℝ≥0∞) * ε := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_gcmInstRun_ks_outer L adv)]
  exact probEvent_bind_le_of_forall_le fun ks _ =>
    probEvent_forge_gcmInst_le L haxu adv q_d hq ks

/-- The authenticity hop: `|Pr[game3] − Pr[game2]| ≤ q_d · ε`. Suppressing decryption is
noticed only if some decryption query forges a valid tag, and the AXU bound caps each attempt
at `ε`. `hε` lets the `ℝ≥0∞` bound be read in `ℝ`; it is free at the concrete
`ε = maxBlocks L / 2¹²⁸`. -/
theorem game2_game3_le_auth {K : Type} (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d)
    {ε : ℝ≥0∞} (hε : ε ≠ ⊤) (haxu : GhashIsAXU L ε) :
    |(Pr[= true | game3 prp L hL adv]).toReal -
      (Pr[= true | game2 prp L hL adv]).toReal| ≤ (q_d : ℝ) * ε.toReal := by
  -- The projections onto the instrumented games, consumed as `evalDist` equalities.
  have h3 : Pr[= true | game3 prp L hL adv] = Pr[= true | game3Flat prp L hL adv] :=
    (probOutput_congr rfl (game3Flat_eq_game3 prp L hL adv)).symm
  have h2 : Pr[= true | game2 prp L hL adv] = Pr[= true | game2Flat prp L hL adv] :=
    (probOutput_congr rfl (game2Flat_eq_game2 prp L hL adv)).symm
  rw [h3, h2]
  calc |(Pr[= true | game3Flat prp L hL adv]).toReal -
        (Pr[= true | game2Flat prp L hL adv]).toReal|
      ≤ tvDist (game3Flat prp L hL adv) (game2Flat prp L hL adv) :=
        abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ (Pr[fun z : Bool × (Option (BitVec L × BitVec 128) × Bool) => z.2.2 = true |
            (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>=
              fun a => (simulateQ (gcmInstImpl a false) adv).run (none, false))]).toReal :=
        tvDist_gcmInstFlat_le_probEvent_forge L adv
    _ ≤ ((q_d : ℝ≥0∞) * ε).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top q_d) hε)
          (probEvent_forge_gcmInstFlat_le L haxu adv q_d hq)
    _ = (q_d : ℝ) * ε.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

end GCM
