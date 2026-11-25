/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Authenticity.Game
public import ToVCVio.OracleComp.SimSemantics.StateT.ExtendState

/-!
# FS-AEAD from AEAD and PRG — moving `G_auth^j` to another chain

A and B keep seeds and keys of the chain in their states, but the game uses a seed only to
derive the next step of the chain, and `O-Corr-A` reveals A's seed. Let two chains `G₁` from
`k₁` and `G₂` from `k₂` have the same keys `K_q` for `q ≥ 1`, and the same seeds `w_q` for
`q ≥ j`. In `G_auth^j`, `O-Corr-A` reveals no seed below `j`, so the two games differ only in the
seeds and keys that their states hold.

`normSt G₂ k₂` replaces every seed and every key of a state by the value of the chain `G₂`
from `k₂` at its position. `authRun_map_normSt` shows that `normSt G₂ k₂` carries the runs of
`G_auth^j` for `G₁` to the runs for `G₂`. The PRG reductions use it to replace the seeds below
`j` by values that they know.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type}

/-! ## The oracles of `G_auth^j` on another chain -/

/-- `O-Transmit-A` commutes with `normSt`. -/
theorem oracleTransmitA_map_normSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) {k₁ : W} (k₂ : W)
    (hkey : ∀ q, 1 ≤ q → chainKey G₁ k₁ q = chainKey G₂ k₂ q)
    {st : CState W Kae AD M Cae} (hinv : SeedInv G₁ k₁ st) (q : AD × M) :
    Prod.map id (normSt G₂ k₂) <$> (oracleTransmitA (fromAEADChain ae G₁) q).run st =
      (oracleTransmitA (fromAEADChain ae G₂) q).run (normSt G₂ k₂ st) := by
  obtain ⟨a, m⟩ := q
  have h := send_normS ae G₁ G₂ k₂ (hkey _ (Nat.succ_pos _)) hinv.vA_w a m
  simp only [oracleTransmitA, StateT.run_bind, StateT.run_get, pure_bind, normSt_end_]
  split_ifs
  · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  · simp only [fromAEADChain, normSt_vA, ← h, StateT.run_bind, StateT.run_set, StateT.run_pure,
      pure_bind, map_pure, Prod.map_apply, id_eq, normSt_record]
    rfl

/-- `O-Chall-A` commutes with `normSt`. -/
theorem oracleChallA_map_normSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) {k₁ : W} (k₂ : W)
    (hkey : ∀ q, 1 ≤ q → chainKey G₁ k₁ q = chainKey G₂ k₂ q) (len : M → ℕ) (b : Bool)
    {st : CState W Kae AD M Cae} (hinv : SeedInv G₁ k₁ st) (q : AD × M × M) :
    Prod.map id (normSt G₂ k₂) <$> (oracleChallA (fromAEADChain ae G₁) len b q).run st =
      (oracleChallA (fromAEADChain ae G₂) len b q).run (normSt G₂ k₂ st) := by
  obtain ⟨a, m₀, m₁⟩ := q
  simp only [oracleChallA, StateT.run_bind, StateT.run_get, pure_bind, normSt_end_,
    normSt_corrA]
  generalize (if b = true then m₁ else m₀) = m
  split_ifs
  · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  · have h := send_normS ae G₁ G₂ k₂ (hkey _ (Nat.succ_pos _)) hinv.vA_w a m
    simp only [fromAEADChain, normSt_vA, ← h, StateT.run_bind, StateT.run_set, StateT.run_pure,
      pure_bind, map_pure, Prod.map_apply, id_eq, normSt_record]
    rfl

/-- `O-Corr-B^⊥` commutes with `normSt`. -/
theorem oracleCorrBSilent_map_normSt (G : ℕ → W → W × Kae) (k : W)
    (st : CState W Kae AD M Cae) :
    Prod.map id (normSt G k) <$> (oracleCorrBSilent _ _ AD M (ℕ × Cae) ()).run st =
      (oracleCorrBSilent _ _ AD M (ℕ × Cae) ()).run (normSt G k st) := by
  simp only [oracleCorrBSilent, StateT.run_bind, StateT.run_get, pure_bind, normSt_end_,
    normSt_chall]
  split_ifs
  · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
      Prod.map_apply, id_eq]
    rfl

variable [DecidableEq AD] [DecidableEq Cae]

/-- Let the chains `G₁` from `k₁` and `G₂` from `k₂` have the same keys. Then `O-Inject-B^stop`
commutes with `normSt`. -/
theorem oracleInjectBStop_map_normSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) {k₁ : W} (k₂ : W)
    (hkey : ∀ q, 1 ≤ q → chainKey G₁ k₁ q = chainKey G₂ k₂ q)
    {st : CState W Kae AD M Cae} (hinv : SeedInv G₁ k₁ st) (q : AD × (ℕ × Cae)) :
    Prod.map id (normSt G₂ k₂) <$> (oracleInjectBStop (fromAEADChain ae G₁) q).run st =
      (oracleInjectBStop (fromAEADChain ae G₂) q).run (normSt G₂ k₂ st) := by
  obtain ⟨a, e⟩ := q
  have hf : (normSt G₂ k₂ st).findTrans a e = st.findTrans a e := rfl
  have h := rcv_normR ae G₁ G₂ k₂ hinv.vB a e (hkey _)
  simp only [oracleInjectBStop, StateT.run_bind, StateT.run_get, pure_bind, normSt_end_, hf,
    fromAEADChain, normSt_vB, ← h]
  split_ifs
  · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  rcases rcv ae G₁ st.vB a e with _ | ⟨vB', i', m'⟩
  · simp only [Option.map_none, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  · simp only [Option.map_some, Prod.map_apply, id_eq, StateT.run_bind, StateT.run_set,
      StateT.run_pure, pure_bind, map_pure]
    rfl

/-- Every step of `G_auth^j` for the chain `G` keeps `SeedInv G k`. -/
theorem seedInv_step (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (k : W) (len : M → ℕ) (b : Bool) (j : ℕ)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (st : CState W Kae AD M Cae) (h : SeedInv G k st) :
    ∀ z ∈ support ((authImplWith (fromAEADChain ae G) len b j (oracleDeliverBLookup G) t).run st),
      SeedInv G k z.2 := by
  intro z hz
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, e⟩) | ⟨a, e⟩)
  · exact seedInv_oracleUnif n st h z hz
  · change z ∈ support ((oracleTransmitA (fromAEADChain ae G) (a, m)).run st) at hz
    simp only [oracleTransmitA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact (h.send ae a m).record _ _ _ _
  · change z ∈ support ((oracleChallA (fromAEADChain ae G) len b (a, m₀, m₁)).run st) at hz
    simp only [oracleChallA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    all_goals
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact (h.send ae a _).record _ _ _ _
  · exact seedInv_oracleCorrALow j st h z hz
  · change z ∈ support ((oracleCorrBSilent _ _ _ _ _ ()).run st) at hz
    simp only [oracleCorrBSilent, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨h.vA_w, h.vA_iA, h.vB⟩
  · exact seedInv_oracleDeliverBLookup (a, e) st h z hz
  · change z ∈ support ((oracleInjectBStop (fromAEADChain ae G) (a, e)).run st) at hz
    simp only [oracleInjectBStop, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    obtain ⟨i, e⟩ := e
    rcases hr : rcv ae G st.vB a (i, e) with _ | ⟨vB', i', m'⟩
    · simp only [fromAEADChain, hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    · simp only [fromAEADChain, hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨h.vA_w, h.vA_iA, (rcv_some ae G h.vB hr).2.2.2.1⟩

/-! ## Moving a run to another chain -/

/-- Let the chains `G₁` from `k₁` and `G₂` from `k₂` have the same keys, and the same seeds from
position `j` on. Then from a state on the chain `G₁`, `normSt G₂ k₂` carries a step of `G_auth^j`
for `G₁` to the step for `G₂`. -/
theorem authImplWith_map_normSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) {k₁ : W} (k₂ : W) (len : M → ℕ) (b : Bool) (j : ℕ)
    (hkey : ∀ q, 1 ≤ q → chainKey G₁ k₁ q = chainKey G₂ k₂ q)
    (hseed : ∀ q, j ≤ q → chainState G₁ k₁ q = chainState G₂ k₂ q)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    {st : CState W Kae AD M Cae} (h : SeedInv G₁ k₁ st) :
    Prod.map id (normSt G₂ k₂) <$>
        (authImplWith (fromAEADChain ae G₁) len b j (oracleDeliverBLookup G₁) t).run st =
      (authImplWith (fromAEADChain ae G₂) len b j (oracleDeliverBLookup G₂) t).run
        (normSt G₂ k₂ st) := by
  rcases t with ((((((n | q) | q) | u) | u) | q) | q)
  · exact oracleUnif_map _ _ _ n st
  · exact oracleTransmitA_map_normSt ae G₁ G₂ k₂ hkey h q
  · exact oracleChallA_map_normSt ae G₁ G₂ k₂ hkey len b h q
  · exact oracleCorrALow_map_normSt G₁ G₂ k₂ j hseed h
  · exact oracleCorrBSilent_map_normSt G₂ k₂ st
  · exact oracleDeliverBLookup_map_normSt G₁ G₂ k₂ h q
  · exact oracleInjectBStop_map_normSt ae G₁ G₂ k₂ hkey h q

/-- **Moving a run to another chain.** Let the chains `G₁` from `k₁` and `G₂` from `k₂` have the
same keys `K_q` for `q ≥ 1`, and the same seeds `w_q` for `q ≥ j`. Then the runs of `G_auth^j`
for `G₁` from `k₁`, with `normSt G₂ k₂` on the final state, are the runs for `G₂` from `k₂`. -/
theorem authRun_map_normSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) (k₁ k₂ : W) (len : M → ℕ) (b : Bool) (j : ℕ)
    (hkey : ∀ q, 1 ≤ q → chainKey G₁ k₁ q = chainKey G₂ k₂ q)
    (hseed : ∀ q, j ≤ q → chainState G₁ k₁ q = chainState G₂ k₂ q)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    Prod.map id (Prod.map (normSt G₂ k₂) id) <$> authRun ae G₁ len b j adversary k₁ =
      authRun ae G₂ len b j adversary k₂ := by
  have hinit : Prod.map (normSt G₂ k₂) id
      ((GameState.init (fromAEADChain ae G₁) k₁ : CState W Kae AD M Cae), AuthHist.init) =
      (GameState.init (fromAEADChain ae G₂) k₂, AuthHist.init) := rfl
  rw [authRun, authRun, ← hinit]
  refine map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (fun s => SeedInv G₁ k₁ s.1)
    (Prod.map (normSt G₂ k₂) id) ?_ ?_ adversary _ ⟨rfl, rfl, ⟨rfl, fun _ _ h => (nomatch h),
      fun _ _ => rfl⟩⟩
  · intro t s hs y hy
    obtain ⟨z, hz, rfl⟩ := QueryImpl.mem_support_extendState_run _ authAux t s.1 s.2 hy
    exact seedInv_step ae G₁ k₁ len b j t s.1 hs z hz
  · intro t s hs
    obtain ⟨st, h⟩ := s
    refine QueryImpl.extendState_run_map_eq _ _ authAux authAux (normSt G₂ k₂) t st h
      (authImplWith_map_normSt ae G₁ G₂ k₂ len b j hkey hseed t hs) fun u s' => ?_
    rcases t with ((((((n | q) | q) | u) | u) | q) | q) <;> rfl

end FromAEADPRG

end FSAEADScheme
