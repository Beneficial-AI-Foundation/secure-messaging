/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Chain.Lookup
public import SecureMessaging.FSAEAD.Security.History

/-!
# FS-AEAD from AEAD and PRG — game states on a chain

The game state `CState` for `fromAEADChain ae G`, and the tools that both the authenticity and the
confidentiality step use to move a game to another chain.

`normSt G k` replaces every seed and every key of a state by the value of the chain `G` from `k`
at its position. `SeedInv G k` says that A and B are on the chain `G` from `k`, and that A's
counter is the game counter. The oracles that both games share commute with `normSt` and keep
`SeedInv`.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type}

/-- The state of the FS-AEAD game for the construction. -/
abbrev CState (W Kae AD M Cae : Type) :=
  GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae)

/-! ## Normalization -/

/-- A's state with the seed of the chain `G` from `k` at its position. -/
@[simps]
def normS (G : ℕ → W → W × Kae) (k : W) (vA : SendState W) : SendState W :=
  { vA with w := chainState G k vA.iA }

/-- B's state with the seed and the keys of the chain `G` from `k` at their positions. -/
@[simps]
def normR (G : ℕ → W → W × Kae) (k : W) (vB : RecvState W Kae) : RecvState W Kae :=
  { vB with w := chainState G k vB.iB, D := fun q => (vB.D q).map fun _ => chainKey G k q }

/-- A game state with the seeds and the keys of the chain `G` from `k`. -/
@[simps]
def normSt (G : ℕ → W → W × Kae) (k : W) (st : CState W Kae AD M Cae) :
    CState W Kae AD M Cae :=
  { st with vA := normS G k st.vA, vB := normR G k st.vB }

/-- On the chain from `k`, `rcvKey` rejects index `i` if `D[i] = ⊥` and `i ≤ i_B`. Otherwise it
returns the key `K_i` and the state at position `max(i_B, i)`, with `D[i] = ⊥` and the keys of
the skipped positions `i_B < q < i`. -/
theorem rcvKey_eq_of_onChain (G : ℕ → W → W × Kae) {k : W} {st : RecvState W Kae}
    (hst : OnChain G k st) (i : ℕ) :
    rcvKey G st i = if st.D i = none ∧ i ≤ st.iB then none else
      some (⟨chainState G k (max st.iB i), max st.iB i, fun q => if q = i then none else
        if st.iB < q ∧ q < i then some (chainKey G k q) else st.D q⟩, chainKey G k i) := by
  split_ifs with h
  · exact (rcvKey_eq_none_iff G st i).2 h
  rcases hr : rcvKey G st i with _ | ⟨st', K⟩
  · exact absurd ((rcvKey_eq_none_iff G st i).1 hr) h
  obtain ⟨rfl, -, hon, hiB, hDi, hDj⟩ := rcvKey_some G hst hr
  obtain ⟨w', iB', D'⟩ := st'
  simp only at hon hiB hDi hDj
  subst hiB
  have hw := hon.w_eq
  simp only at hw
  subst hw
  congr
  funext q
  by_cases hq : q = i
  · rw [ite_eq_left hq]
    exact hq ▸ hDi
  · rw [ite_eq_right hq]
    exact hDj q hq

/-- `normR` puts B's state on the chain. -/
theorem onChain_normR (G : ℕ → W → W × Kae) (k : W) {G' : ℕ → W → W × Kae} {k' : W}
    {st : RecvState W Kae} (hst : OnChain G' k' st) : OnChain G k (normR G k st) where
  w_eq := rfl
  D_key j K h := by
    simp only [normR_D, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h
    rfl
  D_none j h := by simp only [normR_D, hst.D_none j h, Option.map_none]

/-- `normR` commutes with `rcvKey`: the key that `rcvKey` returns becomes the key of the chain
`G₂` from `k₂`. -/
theorem rcvKey_normR (G₁ G₂ : ℕ → W → W × Kae) {k₁ : W} (k₂ : W) {st : RecvState W Kae}
    (hst : OnChain G₁ k₁ st) (i : ℕ) :
    (rcvKey G₁ st i).map (Prod.map (normR G₂ k₂) fun _ => chainKey G₂ k₂ i) =
      rcvKey G₂ (normR G₂ k₂ st) i := by
  rw [rcvKey_eq_of_onChain G₁ hst, rcvKey_eq_of_onChain G₂ (onChain_normR G₂ k₂ hst)]
  simp only [normR_D, normR_iB, Option.map_eq_none_iff]
  split_ifs
  · rfl
  · simp only [Option.map_some, Prod.map_apply, normR, Option.some.injEq, Prod.mk.injEq,
      RecvState.mk.injEq, true_and, and_true]
    funext q
    split_ifs <;> rfl

/-- Let the chains `G₁` from `k₁` and `G₂` from `k₂` have the same keys. Then `normR` commutes
with `FS-Rcv`. -/
theorem rcv_normR (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G₁ G₂ : ℕ → W → W × Kae)
    {k₁ : W} (k₂ : W) {st : RecvState W Kae} (hst : OnChain G₁ k₁ st) (a : AD) (c : ℕ × Cae)
    (hkey : 1 ≤ c.1 → chainKey G₁ k₁ c.1 = chainKey G₂ k₂ c.1) :
    (rcv ae G₁ st a c).map (Prod.map (normR G₂ k₂) id) = rcv ae G₂ (normR G₂ k₂ st) a c := by
  obtain ⟨i, e⟩ := c
  have h := rcvKey_normR G₁ G₂ k₂ hst i
  rcases hr : rcvKey G₁ st i with _ | ⟨st', K⟩
  · rw [hr, Option.map_none] at h
    simp only [rcv, hr, ← h, Option.bind_eq_bind, Option.bind_none, Option.map_none]
  · obtain ⟨rfl, hi, -⟩ := rcvKey_some G₁ hst hr
    rw [hr, Option.map_some] at h
    simp only [rcv, hr, ← h, Option.bind_eq_bind, Option.bind_some, Prod.map_apply, hkey hi]
    rcases ae.decrypt (chainKey G₂ k₂ i) (i, a) e with _ | m <;> rfl

/-! ## The game invariant for a chain -/

/-- A and B are on the chain `G` from `k`, and A's counter is the game counter. -/
structure SeedInv (G : ℕ → W → W × Kae) (k : W) (st : CState W Kae AD M Cae) : Prop where
  vA_w : st.vA.w = chainState G k st.vA.iA
  vA_iA : st.vA.iA = st.iA
  vB : OnChain G k st.vB

/-- `record` commutes with `normSt`. -/
theorem normSt_record (G : ℕ → W → W × Kae) (k : W) (st : CState W Kae AD M Cae) (c : Bool)
    (a : AD) (m : M) (e : ℕ × Cae) :
    normSt G k (st.record c a m e) = (normSt G k st).record c a m e := by
  simp only [GameState.record, normSt_corrA, normSt_comp, normSt_iA]
  split_ifs <;> rfl

/-- `delete` commutes with `normSt`. -/
theorem normSt_delete (G : ℕ → W → W × Kae) (k : W) (st : CState W Kae AD M Cae) (i : ℕ) :
    normSt G k (st.delete i) = (normSt G k st).delete i := rfl

/-- A's step on the chain: `FS-Send` from a state on the chain `G₁` from `k₁`, followed by
`normS`, is `FS-Send` for `G₂` from the normalized state. -/
theorem send_normS (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G₁ G₂ : ℕ → W → W × Kae)
    {k₁ : W} (k₂ : W) {vA : SendState W}
    (hkey : chainKey G₁ k₁ (vA.iA + 1) = chainKey G₂ k₂ (vA.iA + 1))
    (hw : vA.w = chainState G₁ k₁ vA.iA) (a : AD) (m : M) :
    Prod.map (normS G₂ k₂) id (send ae G₁ vA a m) = send ae G₂ (normS G₂ k₂ vA) a m := by
  rw [send_eq, send_eq, hw]
  simp only [normS_w, normS_iA, gen_chainState, hkey, Prod.map_apply,
    id_eq, Prod.mk.injEq, and_true]
  rfl

/-- `O-Corr-A^j` commutes with `normSt` if the two chains have the same seeds from `j` on. -/
theorem oracleCorrALow_map_normSt (G₁ G₂ : ℕ → W → W × Kae) {k₁ : W} (k₂ : W) (j : ℕ)
    (hseed : ∀ q, j ≤ q → chainState G₁ k₁ q = chainState G₂ k₂ q)
    {st : CState W Kae AD M Cae} (hinv : SeedInv G₁ k₁ st) :
    Prod.map id (normSt G₂ k₂) <$> (oracleCorrALow _ _ AD M (ℕ × Cae) j ()).run st =
      (oracleCorrALow _ _ AD M (ℕ × Cae) j ()).run (normSt G₂ k₂ st) := by
  simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, normSt_end_,
    normSt_corrA, normSt_iA]
  by_cases h₁ : st.end_ = true
  · simp only [h₁, ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  by_cases h₂ : st.iA < j
  · simp only [h₁, h₂, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
      StateT.run_pure, pure_bind, map_pure, Prod.map_apply, id_eq]
    rfl
  · have hA : normS G₂ k₂ st.vA = st.vA := by
      rw [normS, ← hseed _ (by rw [hinv.vA_iA]; omega), ← hinv.vA_w]
    simp only [h₁, h₂, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
      StateT.run_pure, pure_bind, map_pure, Prod.map_apply, id_eq, normSt, hA]

/-- The uniform-randomness oracle commutes with every state map. -/
theorem oracleUnif_map (StS StR : Type) (f : GameState StS StR AD M (ℕ × Cae) →
    GameState StS StR AD M (ℕ × Cae)) (n : ℕ) (st : GameState StS StR AD M (ℕ × Cae)) :
    Prod.map id f <$> (oracleUnif StS StR AD M (ℕ × Cae) n).run st =
      (oracleUnif StS StR AD M (ℕ × Cae) n).run (f st) := by
  simp only [oracleUnif, ToVCVio.unifLiftStateT, ToVCVio.liftTarget_unif_run, Functor.map_map,
    Prod.map_apply, id_eq]

variable [DecidableEq AD] [DecidableEq Cae]

/-- `O-Deliver-B^lk` commutes with `normSt`. -/
theorem oracleDeliverBLookup_map_normSt (G₁ G₂ : ℕ → W → W × Kae) {k₁ : W} (k₂ : W)
    {st : CState W Kae AD M Cae} (hinv : SeedInv G₁ k₁ st) (q : AD × (ℕ × Cae)) :
    Prod.map id (normSt G₂ k₂) <$> (oracleDeliverBLookup (M := M) G₁ q).run st =
      (oracleDeliverBLookup G₂ q).run (normSt G₂ k₂ st) := by
  obtain ⟨a, e⟩ := q
  have hf : (normSt G₂ k₂ st).findTrans a e = st.findTrans a e := rfl
  simp only [oracleDeliverBLookup, StateT.run_bind, StateT.run_get, pure_bind, normSt_end_, hf]
  split_ifs
  · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  rcases st.findTrans a e with _ | ⟨i, a', m, e'⟩
  · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  · have h := rcvKey_normR G₁ G₂ k₂ hinv.vB i
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
      Prod.map_apply, id_eq, normSt_vB, ← h, normSt_chall]
    rcases rcvKey G₁ st.vB i with _ | ⟨vB', K⟩ <;> rfl

omit [DecidableEq AD] [DecidableEq Cae] in
/-- `record` keeps `SeedInv`. -/
theorem SeedInv.record {G : ℕ → W → W × Kae} {k : W} {st : CState W Kae AD M Cae}
    (h : SeedInv G k st) (c : Bool) (a : AD) (m : M) (e : ℕ × Cae) :
    SeedInv G k (st.record c a m e) := by
  unfold GameState.record
  split_ifs
  · exact h
  all_goals exact ⟨h.vA_w, h.vA_iA, h.vB⟩

omit [DecidableEq AD] [DecidableEq Cae] in
/-- A step of A keeps `SeedInv`. -/
theorem SeedInv.send (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) {G : ℕ → W → W × Kae}
    {k : W} {st : CState W Kae AD M Cae} (h : SeedInv G k st) (a : AD) (m : M) :
    SeedInv G k { st with vA := (FromAEADPRG.send ae G st.vA a m).1, iA := st.iA + 1 } := by
  refine ⟨?_, ?_, h.vB⟩
  · simp only [send_eq, h.vA_w, gen_chainState]
  · simp only [send_eq, h.vA_iA]

omit [DecidableEq AD] [DecidableEq Cae] in
/-- The uniform-randomness oracle keeps `SeedInv`. -/
theorem seedInv_oracleUnif {G : ℕ → W → W × Kae} {k : W} (n : ℕ) (st : CState W Kae AD M Cae)
    (h : SeedInv G k st) :
    ∀ z ∈ support ((oracleUnif (SendState W) (RecvState W Kae) AD M (ℕ × Cae) n).run st),
      SeedInv G k z.2 := by
  intro z hz
  rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hz
  obtain ⟨x, rfl⟩ := hz
  exact h

omit [DecidableEq AD] [DecidableEq Cae] in
/-- `O-Corr-A^j` keeps `SeedInv`. -/
theorem seedInv_oracleCorrALow {G : ℕ → W → W × Kae} {k : W} (j : ℕ)
    (st : CState W Kae AD M Cae) (h : SeedInv G k st) :
    ∀ z ∈ support ((oracleCorrALow (SendState W) (RecvState W Kae) AD M (ℕ × Cae) j ()).run st),
      SeedInv G k z.2 := by
  intro z hz
  simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h
  all_goals
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨h.vA_w, h.vA_iA, h.vB⟩

/-- `O-Deliver-B^lk` keeps `SeedInv`. -/
theorem seedInv_oracleDeliverBLookup {G : ℕ → W → W × Kae} {k : W} (q : AD × (ℕ × Cae))
    (st : CState W Kae AD M Cae) (h : SeedInv G k st) :
    ∀ z ∈ support ((oracleDeliverBLookup (M := M) G q).run st), SeedInv G k z.2 := by
  obtain ⟨a, e⟩ := q
  intro z hz
  simp only [oracleDeliverBLookup, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h
  rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
  · simp only [hf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h
  · simp only [hf, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨h.vA_w, h.vA_iA, ?_⟩
    rcases hr : rcvKey G st.vB i with _ | ⟨vB', K⟩
    · simp only [Option.map_none, Option.getD_none]
      exact h.vB
    · simp only [Option.map_some, Option.getD_some]
      exact (rcvKey_some G h.vB hr).2.2.1

end FromAEADPRG

end FSAEADScheme
