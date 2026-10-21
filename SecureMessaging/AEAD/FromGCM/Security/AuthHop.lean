/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Axu
import SecureMessaging.AEAD.FromGCM.Security.Games
import ToVCVio.CryptoFoundations.WegmanCarter.Security
import ToVCVio.ProgramLogic.Relational.IdenticalUntilBad

/-!
# GCM: the authenticity hop (`game2` → `game3`)

Replaces the live-verification game `game2` by the always-reject game `game3`. The two agree
unless some decryption query other than the challenge pair `(ad*, e*)` carries a valid tag.
After the challenge `(x, T)`, a forgery `(x', T')` needs GHASH at the unknown key `H`
to hit a chosen XOR difference, `ghash H x ⊕ ghash H x' = T ⊕ T'`; before it, a forgery
needs a guess of the tag. The almost-XOR-universal (AXU) bound `GhashIsAXU L ε` (`Axu.lean`)
caps both at `ε` per query, so the hop costs `q_d · ε`, the Wegman–Carter forgery bound.

The GCM handlers are, by definition, the generic Wegman–Carter handler of
`ToVCVio/CryptoFoundations/WegmanCarter/Defs.lean` (`gcmInstImpl_eq_wcInstImpl` is `rfl`), and
the two games are compared by the identical-until-bad principle: games whose oracles behave
identically until a flag is set differ by at most the probability of the flag
(`ToVCVio/ProgramLogic/Relational/IdenticalUntilBad.lean`).

A successful decryption in `game2` returns `C' ⊕ ks` and so leaks the keystream, which is why
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

/-- Let GHASH be `ε`-AXU, let `adv` make at most `q_d` decryption queries, let `ks` be a fixed
keystream and let `H` and `mask` be independent uniform 128-bit values. Then running `adv`
against the always-reject oracles raises the `forged` flag with probability at most `q_d · ε`. -/
theorem probEvent_forge_gcmInst_le (L : ℕ) {ε : ℝ≥0∞} (haxu : GhashIsAXU L ε)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) (ks : BitVec L) :
    Pr{let z ← (do
          let h ← ($ᵗ (BitVec 128) : ProbComp _)
          let mask ← ($ᵗ (BitVec 128) : ProbComp _)
          (simulateQ (gcmInstImpl (h, mask, ks) false) adv).run (none, false))}[z.2.2 = true]
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
    (p : Option (SupportedAAD × (BitVec L × BitVec 128)) × Bool) (hp : p.2 = true) :
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
      simp only [add_apply_inl, add_apply_inr, gcmInstImpl, wcInstImpl, id_eq, bind_pure_comp,
        Prod.mk.eta, beq_iff_eq, decide_eq_true_eq, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
        StateT.run_map, StateT.run_set, map_pure, support_pure, Set.mem_singleton_iff] at hz <;>
      simp only [add_apply_inl, add_apply_inr, hz]
  · -- ODecrypt: guard split, then `ok` split; `true || ok = true` in every branch.
    obtain ⟨h, mask, ks⟩ := a
    simp only [add_apply_inr, gcmInstImpl, wcInstImpl, id_eq, bind_pure_comp, Prod.mk.eta,
      beq_iff_eq, decide_eq_true_eq, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_get,
      pure_bind, Bool.true_or] at hz
    split_ifs at hz <;>
      simp_all only [Bool.not_eq_true, bind_pure_comp, StateT.run_pure, StateT.run_map,
        StateT.run_set, map_pure, support_pure, Set.mem_singleton_iff, add_apply_inr]

/-- The identical-until-bad conditions for a fixed `a = (H, mask, ks)`: the always-reject and
live handlers give every oracle call from an unset flag to an unset flag the same probability,
and on both handlers a set flag stays set. -/
theorem gcmInstImpl_identicalUntilBad (L : ℕ)
    (a : BitVec 128 × BitVec 128 × BitVec L) :
    (∀ (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
               (BitVec L × BitVec 128)).Domain)
        (s : Option (SupportedAAD × (BitVec L × BitVec 128)))
        (u : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
               (BitVec L × BitVec 128)).Range t)
        (s' : Option (SupportedAAD × (BitVec L × BitVec 128))),
      Pr{let x ← ((gcmInstImpl a false) t).run (s, false)}[x = (u, (s', false))] =
        Pr{let x ← ((gcmInstImpl a true) t).run (s, false)}[x = (u, (s', false))])
    ∧ (∀ (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
                 (BitVec L × BitVec 128)).Domain)
          (p : Option (SupportedAAD × (BitVec L × BitVec 128)) × Bool), p.2 = true →
        ∀ z ∈ support (((gcmInstImpl a false) t).run p), z.2.2 = true)
    ∧ (∀ (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
                 (BitVec L × BitVec 128)).Domain)
          (p : Option (SupportedAAD × (BitVec L × BitVec 128)) × Bool), p.2 = true →
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
    by_cases hguard : s = some (ad, e)
    · simp only [add_apply_inr, gcmInstImpl, wcInstImpl, id_eq, bind_pure_comp, Prod.mk.eta,
        beq_iff_eq, decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte, ite_self,
        QueryImpl.add_apply_inr, hguard, StateT.run_bind, StateT.run_get, pure_bind,
        StateT.run_pure]
    · by_cases hok : (e.2 = ghash h (gcmEncode ad e.1) ^^^ mask) <;>
        simp only [add_apply_inr, gcmInstImpl, wcInstImpl, id_eq, bind_pure_comp, Prod.mk.eta,
          beq_iff_eq, decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte, ite_self,
          QueryImpl.add_apply_inr, hok, decide_true, decide_false, Bool.or_true, Bool.or_false,
          StateT.run_bind, StateT.run_get, pure_bind, hguard, StateT.run_map, StateT.run_set,
          map_pure, Bool.true_eq_false, Prod.mk.injEq, and_false]

/-- For a fixed tuple `a`, the outputs of `adv` against the always-reject and the live oracles
have total-variation distance at most the probability that the always-reject run raises the
`forged` flag. -/
theorem gcmInst_measureTVDist_le_probEvent_forge (L : ℕ)
    (a : BitVec 128 × BitVec 128 × BitVec L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    measureTVDist ((simulateQ (gcmInstImpl a false) adv).run' (none, false))
        ((simulateQ (gcmInstImpl a true) adv).run' (none, false))
      ≤ Pr{let z ←
          (simulateQ (gcmInstImpl a false) adv).run (none, false)}[z.2.2 = true].toReal := by
  obtain ⟨h_agree_good, h_mono₁, h_mono₂⟩ := gcmInstImpl_identicalUntilBad L a
  exact measureTVDist_simulateQ_le_prEvent_output_bad_base (gcmInstImpl a false)
    (gcmInstImpl a true) adv none h_agree_good h_mono₁ h_mono₂

/-! ### Lifting the per-tuple bound across the tuple sample -/

/-- `gcmInst_measureTVDist_le_probEvent_forge` averaged over the uniform tuple draw. -/
private theorem measureTVDist_gcmInstFlat_le_probEvent_forge (L : ℕ)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    measureTVDist (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>=
              fun a => (simulateQ (gcmInstImpl a false) adv).run' (none, false))
        (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>=
              fun a => (simulateQ (gcmInstImpl a true) adv).run' (none, false))
      ≤ (Pr{let z ← (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>= fun a =>
              (simulateQ (gcmInstImpl a false) adv).run (none, false))}[z.2.2 = true]).toReal := by
  refine le_trans (measureTVDist_bind_left_le_tsum _ _ _) ?_
  rw [OracleComp.prEvent_bind_eq_tsum]
  rw [ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top
    (ne_top_of_le_ne_top one_ne_top (prEvent_le_one _))
    (ne_top_of_le_ne_top one_ne_top (prEvent_le_one _)))]
  refine Summable.tsum_le_tsum (fun a => ?_) Summable.of_finite Summable.of_finite
  rw [ENNReal.toReal_mul]
  exact mul_le_mul_of_nonneg_left (gcmInst_measureTVDist_le_probEvent_forge L a adv)
    ENNReal.toReal_nonneg

/-- Drawing the tuple `(H, mask, ks)` uniformly is the same as drawing `ks`, then `H`, then
`mask`, independently and uniformly. -/
private theorem evalDistEq_gcmInstRun_ks_outer (L : ℕ)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>=
        fun a => (simulateQ (gcmInstImpl a false) adv).run (none, false)) =ᵈ
      (($ᵗ (BitVec L) : ProbComp _) >>= fun ks =>
          (do let h ← ($ᵗ (BitVec 128) : ProbComp _)
              let mask ← ($ᵗ (BitVec 128) : ProbComp _)
              (simulateQ (gcmInstImpl (h, mask, ks) false) adv).run (none, false))) := by
  rw [SampleableType.uniformSample_prod_eq_bind (BitVec 128) (BitVec 128 × BitVec L)]
  simp only [bind_assoc, pure_bind]
  rw [SampleableType.uniformSample_prod_eq_bind (BitVec 128) (BitVec L)]
  simp only [bind_assoc, pure_bind]
  refine (EvalDistEq.bind_right _ (fun h =>
      EvalDistEq.bind_bind_swap ($ᵗ (BitVec 128) : ProbComp _)
        ($ᵗ (BitVec L) : ProbComp _)
        (fun mask ks =>
          (simulateQ (gcmInstImpl (h, mask, ks) false) adv).run (none, false)))).trans
    (EvalDistEq.bind_bind_swap ($ᵗ (BitVec 128) : ProbComp _)
      ($ᵗ (BitVec L) : ProbComp _)
      (fun h ks =>
        (do let mask ← ($ᵗ (BitVec 128) : ProbComp _)
            (simulateQ (gcmInstImpl (h, mask, ks) false) adv).run (none, false))))

private theorem probEvent_forge_gcmInstFlat_le (L : ℕ) {ε : ℝ≥0∞} (haxu : GhashIsAXU L ε)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d) :
    Pr{let z ← (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>=
          fun a => (simulateQ (gcmInstImpl a false) adv).run (none, false))}[z.2.2 = true]
      ≤ (q_d : ℝ≥0∞) * ε := by
  rw [(evalDistEq_gcmInstRun_ks_outer L adv).prEvent_eq]
  exact prEvent_bind_le_of_forall_le _ _ _ fun ks =>
    probEvent_forge_gcmInst_le L haxu adv q_d hq ks

/-- The authenticity hop. Let GHASH be `ε`-AXU with `ε` finite (`ε ≠ ⊤`), and let `adv` make
at most `q_d` decryption queries. Then `|Pr[game3 = 1] − Pr[game2 = 1]| ≤ q_d · ε`. -/
theorem game2_game3_le_auth {K : Type} (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128))
    (q_d : ℕ) (hq : AEADScheme.decryptQueryBound adv q_d)
    {ε : ℝ≥0∞} (hε : ε ≠ ⊤) (haxu : GhashIsAXU L ε) :
    |(Pr{let x ← game3 prp L hL adv}[x = true]).toReal -
      (Pr{let x ← game2 prp L hL adv}[x = true]).toReal| ≤ (q_d : ℝ) * ε.toReal := by
  -- The projections onto the instrumented games, consumed as `evalDist` equalities.
  have h3 :
      Pr{let x ← game3 prp L hL adv}[x = true] = Pr{let x ← game3Flat prp L hL adv}[x = true] :=
    ((game3Flat_eq_game3 prp L hL adv).prEvent_eq _).symm
  have h2 :
      Pr{let x ← game2 prp L hL adv}[x = true] = Pr{let x ← game2Flat prp L hL adv}[x = true] :=
    ((game2Flat_eq_game2 prp L hL adv).prEvent_eq _).symm
  rw [h3, h2]
  calc |(Pr{let x ← game3Flat prp L hL adv}[x = true]).toReal -
        (Pr{let x ← game2Flat prp L hL adv}[x = true]).toReal|
      ≤ measureTVDist (game3Flat prp L hL adv) (game2Flat prp L hL adv) :=
        abs_prEvent_toReal_sub_le_measureTVDist _ _ (· = true) Measurable.of_discrete
    _ ≤ (Pr{let z ← (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>=
              fun a =>
                (simulateQ (gcmInstImpl a false) adv).run (none, false))}[z.2.2 = true]).toReal :=
        measureTVDist_gcmInstFlat_le_probEvent_forge L adv
    _ ≤ ((q_d : ℝ≥0∞) * ε).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top q_d) hε)
          (probEvent_forge_gcmInstFlat_le L haxu adv q_d hq)
    _ = (q_d : ℝ) * ε.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

end GCM
