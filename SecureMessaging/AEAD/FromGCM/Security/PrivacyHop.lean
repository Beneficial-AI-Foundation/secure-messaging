/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Games
import ToVCVio.OracleComp.Constructions.BitVec
import ToVCVio.ProgramLogic.Relational.Basic

/-!
# GCM: the privacy hop (`game3` → `game4`)

Replaces the real challenge ciphertext by a uniform one. The hop is free: the challenge
`(C, T) = (m ^^^ ks, ghash H (gcmEncode ad C) ^^^ mask)` is built from one fresh uniform tuple
`(H, mask, ks)` that nothing else in `game3` reads, so `C` is a one-time pad of `m`, `T` is
masked by a fresh `mask`, and the pair is jointly uniform on `BitVec L × BitVec 128`; this is
`evalDist_gcmChallenge_uniform`. The two games are therefore equidistributed, `game3_eq_game4`,
proved by the per-query coupling `gcmPrivacy_step` under the state relation `gcmPrivacyRel`.
-/

namespace GCM

open OracleSpec OracleComp ENNReal AEADScheme ToVCVio
open AEADScheme.aeadOneTimeCCASpec
open OracleComp.ProgramLogic.Relational

/-! ## Joint uniformity of the GCM challenge -/

/-- The one-time GCM challenge built from a uniform tuple `(H, mask, ks)` is jointly uniform on
`BitVec L × BitVec 128`: for each `H`, `C = m ^^^ ks` is uniform because `ks` is, and `mask` is
independent of `C`, so `T` is uniform given `C`. The statement is against the single product
draw; uniformity of `C` and `T` separately would not suffice for the coupling. -/
theorem evalDist_gcmChallenge_uniform {L : ℕ} (ad : SupportedAAD) (m : BitVec L) :
    evalDist ((fun a : BitVec 128 × BitVec 128 × BitVec L =>
        (m ^^^ a.2.2, ghash a.1 (gcmEncode ad (m ^^^ a.2.2)) ^^^ a.2.1)) <$>
      ($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _))
      = evalDist ($ᵗ (BitVec L × BitVec 128) : ProbComp _) := by
  rw [uniformSample_prod_eq_bind (BitVec 128) (BitVec 128 × BitVec L),
    uniformSample_prod_eq_bind (BitVec 128) (BitVec L)]
  simp only [map_bind, map_pure, bind_assoc, pure_bind]
  refine (DeferredSampling.evalDist_bind_congr_left ($ᵗ BitVec 128 : ProbComp _) _
      (fun _ => ($ᵗ (BitVec L × BitVec 128) : ProbComp _)) (fun H => ?_)).trans
    (DeferredSampling.evalDist_bind_const_neverFails
      ($ᵗ BitVec 128 : ProbComp _) (probFailure_uniformSample _)
      ($ᵗ (BitVec L × BitVec 128) : ProbComp _))
  exact evalDist_pair_xor_uniform m (fun c => ghash H (gcmEncode ad c))

/-- Shape pin: the challenge map above is `gcmTupleImplReject`'s encryption body. -/
example {L : ℕ} (ad : SupportedAAD) (m : BitVec L)
    (a : BitVec 128 × BitVec 128 × BitVec L) :
    (let (h, mask, ks) := a
      let c := m ^^^ ks
      (c, ghash h (gcmEncode ad c) ^^^ mask)) =
      (m ^^^ a.2.2, ghash a.1 (gcmEncode ad (m ^^^ a.2.2)) ^^^ a.2.1) := rfl

/-- Shape pin: the right-hand side above is the draw `gcmRandRejectImpl` makes at its encryption
oracle. -/
example {L : ℕ} :
    (liftM ($ᵗ (BitVec L × BitVec 128) : ProbComp (BitVec L × BitVec 128)) :
      ProbComp (BitVec L × BitVec 128)) = ($ᵗ (BitVec L × BitVec 128) : ProbComp _) := rfl

/-! ## The state relation -/

/-- State relation for the privacy coupling: the challenge slots agree, and `game3`'s
lazy-sampling cache is populated exactly when the challenge is. The second conjunct excludes the
unreachable state where the cache holds a tuple but no challenge was issued; there the encryption
step would not couple, `game3` reusing the cached tuple while `game4` draws fresh. -/
def gcmPrivacyRel {L : ℕ} :
    (Option (BitVec L × BitVec 128) × Option (BitVec 128 × BitVec 128 × BitVec L)) →
      Option (BitVec L × BitVec 128) → Prop :=
  fun p ch₂ => p.1 = ch₂ ∧ p.2.isSome = p.1.isSome

/-! ## The three deterministic per-query cases -/

/-- `StateT.run_lift` in the beta-reduced shape the `consumeLazy` reductions leave behind. -/
private lemma stateT_liftM_apply {σ α : Type} (x : ProbComp α) (s : σ) :
    (liftM x : StateT σ ProbComp α) s = x >>= fun a => pure (a, s) := rfl

/-- `OUnif`: both sides forward the same uniform query and touch no state. -/
private lemma gcmPrivacy_step_unif {L : ℕ} (n : ℕ)
    (s₁ : Option (BitVec L × BitVec 128) × Option (BitVec 128 × BitVec 128 × BitVec L))
    (s₂ : Option (BitVec L × BitVec 128))
    (hs : gcmPrivacyRel s₁ s₂) :
    RelTriple
      ((consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _)
        (OUnif n : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
          (BitVec L × BitVec 128)).Domain)).run s₁)
      ((gcmRandRejectImpl (L := L) default
        (OUnif n : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
          (BitVec L × BitVec 128)).Domain)).run s₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ gcmPrivacyRel p₁.2 p₂.2) := by
  obtain ⟨ch, cache⟩ := s₁
  have hrun₁ : (consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _)
      (OUnif n : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run (ch, cache) =
      (fun u => (u, ch, cache)) <$>
        (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) := by
    simp [consumeLazy, StateT.run, gcmTupleImplReject, gcmGameSkeleton, oracleUnif,
      unifLiftStateT, stateT_liftM_apply]
  have hrun₂ : (gcmRandRejectImpl (L := L) default
      (OUnif n : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run s₂ =
      (fun u => (u, s₂)) <$> (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) := by
    simp [gcmRandRejectImpl, gcmGameSkeleton, oracleUnif, unifLiftStateT]
  rw [hrun₁, hrun₂]
  exact relTriple_map_map_of_pointwise _ _ _ (fun _ => ⟨rfl, hs⟩)

/-- `OEncrypt` at a populated challenge slot: the one-shot encryption oracle has already fired,
so both sides return `none` without drawing or writing state. -/
private lemma gcmPrivacy_step_encrypt_some {L : ℕ} (ad : SupportedAAD) (m : BitVec L)
    (e₀ : BitVec L × BitVec 128) (a : BitVec 128 × BitVec 128 × BitVec L) :
    RelTriple
      ((consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _)
        (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
          (BitVec L × BitVec 128)).Domain)).run (some e₀, some a))
      ((gcmRandRejectImpl (L := L) default
        (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
          (BitVec L × BitVec 128)).Domain)).run (some e₀))
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ gcmPrivacyRel p₁.2 p₂.2) := by
  -- Peel `consumeLazy` at a populated cache: the `| some a => pure a` branch, no draw.
  have hpeel : (consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _)
      (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run (some e₀, some a) =
      (gcmTupleImplReject a (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run (some e₀) >>=
        fun p => (pure (p.1, p.2, some a) : ProbComp _) := by
    simp only [consumeLazy, StateT.run]
    split_ifs <;> simp
  have hskel : (gcmTupleImplReject a (OEncrypt (ad, m) :
      (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128)).Domain)).run
      (some e₀) = (pure (none, some e₀) : ProbComp _) := by
    simp [gcmTupleImplReject, gcmGameSkeleton, StateT.run_bind, StateT.run_get,
      StateT.run_pure]
  have hrun₁ : (consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _)
      (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run (some e₀, some a) =
      (pure (none, some e₀, some a) : ProbComp _) := by
    rw [hpeel, hskel]; simp
  have hrun₂ : (gcmRandRejectImpl (L := L) default
      (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run (some e₀) =
      (pure (none, some e₀) : ProbComp _) := by
    simp [gcmRandRejectImpl, gcmGameSkeleton, StateT.run_bind, StateT.run_get,
      StateT.run_pure]
  rw [hrun₁, hrun₂]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl⟩

/-- `ODecrypt`: both sides always reject, whatever tuple `consumeLazy` feeds in, which is what
`gcmTupleImplReject_indep` supplies. -/
private lemma gcmPrivacy_step_decrypt {L : ℕ} (ad : SupportedAAD)
    (e : BitVec L × BitVec 128)
    (s₁ : Option (BitVec L × BitVec 128) × Option (BitVec 128 × BitVec 128 × BitVec L))
    (s₂ : Option (BitVec L × BitVec 128))
    (hs : gcmPrivacyRel s₁ s₂) :
    RelTriple
      ((consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _)
        (ODecrypt (ad, e) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
          (BitVec L × BitVec 128)).Domain)).run s₁)
      ((gcmRandRejectImpl (L := L) default
        (ODecrypt (ad, e) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
          (BitVec L × BitVec 128)).Domain)).run s₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ gcmPrivacyRel p₁.2 p₂.2) := by
  obtain ⟨ch, cache⟩ := s₁
  -- Peel `consumeLazy` at a non-hit query: the else-branch, tuple `cache.getD default`.
  have hpeel : (consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _)
      (ODecrypt (ad, e) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run (ch, cache) =
      (gcmTupleImplReject (cache.getD default)
        (ODecrypt (ad, e) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
          (BitVec L × BitVec 128)).Domain)).run ch >>=
        fun p => (pure (p.1, p.2, cache) : ProbComp _) := by
    simp [consumeLazy, StateT.run]
  have hskel : (gcmTupleImplReject (default : BitVec 128 × BitVec 128 × BitVec L)
      (ODecrypt (ad, e) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run ch = (pure (none, ch) : ProbComp _) := by
    by_cases hguard : ch = some e
    all_goals
      simp [gcmTupleImplReject, gcmGameSkeleton, beq_iff_eq, hguard]
  have hrun₁ : (consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _)
      (ODecrypt (ad, e) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run (ch, cache) =
      (pure (none, ch, cache) : ProbComp _) := by
    rw [hpeel, gcmTupleImplReject_indep
      (ODecrypt (ad, e) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain) ch (cache.getD default) default rfl, hskel]
    simp
  have hrun₂ : (gcmRandRejectImpl (L := L) default
      (ODecrypt (ad, e) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run s₂ =
      (pure (none, s₂) : ProbComp _) := by
    by_cases hguard : s₂ = some e
    all_goals
      simp [gcmRandRejectImpl, gcmGameSkeleton, beq_iff_eq, hguard]
  rw [hrun₁, hrun₂]
  exact relTriple_pure_pure ⟨rfl, hs⟩

/-! ## The one probabilistic per-query case -/

/-- `OEncrypt` at an empty challenge slot, the one probabilistic case: `game3` draws a fresh tuple
and computes the challenge from it, `game4` draws the challenge directly.
`evalDist_gcmChallenge_uniform` couples the two draws along the challenge map. -/
private lemma gcmPrivacy_step_encrypt_none {L : ℕ} (ad : SupportedAAD) (m : BitVec L) :
    RelTriple
      ((consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _)
        (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
          (BitVec L × BitVec 128)).Domain)).run (none, none))
      ((gcmRandRejectImpl (L := L) default
        (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
          (BitVec L × BitVec 128)).Domain)).run none)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ gcmPrivacyRel p₁.2 p₂.2) := by
  -- Peel `consumeLazy` at an empty cache: the `| none => $ᵗ τ` branch, a fresh tuple.
  have hpeel : (consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _)
      (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run (none, none) =
      (($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) >>= fun a =>
        (gcmTupleImplReject a (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
          (BitVec L × BitVec 128)).Domain)).run none >>=
          fun p => (pure (p.1, p.2, some a) : ProbComp _)) := by
    simp [consumeLazy, StateT.run]
  have hskel : ∀ a : BitVec 128 × BitVec 128 × BitVec L,
      (gcmTupleImplReject a (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run none =
      (pure (some (m ^^^ a.2.2, ghash a.1 (gcmEncode ad (m ^^^ a.2.2)) ^^^ a.2.1),
        some (m ^^^ a.2.2, ghash a.1 (gcmEncode ad (m ^^^ a.2.2)) ^^^ a.2.1)) : ProbComp _) :=
    fun a => by
      simp [gcmTupleImplReject, gcmGameSkeleton, StateT.run_bind, StateT.run_get,
        StateT.run_set]
  have hrun₁ : (consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _)
      (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run (none, none) =
      (fun a : BitVec 128 × BitVec 128 × BitVec L =>
        (some (m ^^^ a.2.2, ghash a.1 (gcmEncode ad (m ^^^ a.2.2)) ^^^ a.2.1),
          some (m ^^^ a.2.2, ghash a.1 (gcmEncode ad (m ^^^ a.2.2)) ^^^ a.2.1),
          some a)) <$> ($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _) := by
    rw [hpeel]
    simp only [hskel]
    simp
  have hrun₂ : (gcmRandRejectImpl (L := L) default
      (OEncrypt (ad, m) : (aeadOneTimeCCASpec SupportedAAD (BitVec L)
        (BitVec L × BitVec 128)).Domain)).run none =
      (fun e : BitVec L × BitVec 128 => (some e, some e)) <$>
        ($ᵗ (BitVec L × BitVec 128) : ProbComp _) := by
    simp [gcmRandRejectImpl, gcmGameSkeleton]
  have hgraph : RelTriple ($ᵗ (BitVec 128 × BitVec 128 × BitVec L) : ProbComp _)
      ($ᵗ (BitVec L × BitVec 128) : ProbComp _)
      (fun (a : BitVec 128 × BitVec 128 × BitVec L) (e : BitVec L × BitVec 128) =>
        (m ^^^ a.2.2, ghash a.1 (gcmEncode ad (m ^^^ a.2.2)) ^^^ a.2.1) = e) :=
    relTriple_graph_of_evalDist_map_eq _ (evalDist_gcmChallenge_uniform ad m)
  rw [hrun₁, hrun₂]
  exact relTriple_map (relTriple_post_mono hgraph (fun a e hae => by
    subst hae; exact ⟨rfl, rfl, rfl⟩))

/-! ## The per-query coupling -/

/-- The per-query coupling: from `gcmPrivacyRel`-related states, one step of `game3`'s handler
and one of `game4`'s return the same response and re-establish the relation. Only the encryption
query at an empty challenge slot is probabilistic; the other cases are bookkeeping. -/
theorem gcmPrivacy_step {L : ℕ}
    (t : (aeadOneTimeCCASpec SupportedAAD (BitVec L) (BitVec L × BitVec 128)).Domain)
    (s₁ : Option (BitVec L × BitVec 128) × Option (BitVec 128 × BitVec 128 × BitVec L))
    (s₂ : Option (BitVec L × BitVec 128))
    (hs : gcmPrivacyRel s₁ s₂) :
    RelTriple
      ((consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _) t).run s₁)
      ((gcmRandRejectImpl (L := L) default t).run s₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ gcmPrivacyRel p₁.2 p₂.2) := by
  obtain ⟨ch, cache⟩ := s₁
  have hch : ch = s₂ := hs.1
  have hcache : cache.isSome = ch.isSome := hs.2
  rcases t with (n | ⟨ad, m⟩) | ⟨ad, e⟩
  · exact gcmPrivacy_step_unif n (ch, cache) s₂ hs
  · -- `OEncrypt`: split on the challenge slot; the second conjunct forces the cache.
    subst hch
    cases ch with
    | none =>
      cases cache with
      | none => exact gcmPrivacy_step_encrypt_none ad m
      | some a => simp at hcache
    | some e₀ =>
      cases cache with
      | none => simp at hcache
      | some a => exact gcmPrivacy_step_encrypt_some ad m e₀ a
  · exact gcmPrivacy_step_decrypt ad e (ch, cache) s₂ hs

/-! ## The hop theorem -/

/-- The privacy hop: `game3` and `game4` are equidistributed, with no advantage term. The
coupling runs against the collapsed form of `game4` given by `game4_eq_plain`, so only the
`game3` side of `gcmPrivacyRel` carries a lazy-sampling cache. -/
theorem game3_eq_game4 {K : Type} (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    evalDist (game3 prp L hL adv) = evalDist (game4 prp L hL adv) := by
  rw [game4_eq_plain prp L hL adv]
  unfold game3
  -- Elaborating the coupling separately from its consumer keeps unification away from the
  -- unfolded game body (13 s → 1.5 s).
  have h := relTriple_simulateQ_run'
    (consumeLazy gcmTupleImplReject (fun t => t matches OEncrypt _))
    (gcmRandRejectImpl (L := L) default)
    gcmPrivacyRel
    adv
    (fun t s₁ s₂ hs => gcmPrivacy_step t s₁ s₂ hs)
    (none, none) none
    ⟨rfl, rfl⟩
  exact evalDist_eq_of_relTriple_eqRel h

theorem probOutput_game3_eq_game4 {K : Type} (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (hL : ValidMsgLength L)
    (adv : OneTimeCCAAdversary SupportedAAD (BitVec L) (BitVec L × BitVec 128)) :
    Pr[= true | game3 prp L hL adv] = Pr[= true | game4 prp L hL adv] :=
  probOutput_eq_of_evalDist_eq (game3_eq_game4 prp L hL adv) true

end GCM
