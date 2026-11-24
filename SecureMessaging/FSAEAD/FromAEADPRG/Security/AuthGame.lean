/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Lookup
public import SecureMessaging.FSAEAD.Security.History

/-!
# FS-AEAD from AEAD and PRG — the authenticity game

The game `G_auth^j` of `SecureMessaging.FSAEAD.Security.History` for the construction
`fromAEADChain ae G`, with `O-Deliver-B^lk` for `O-Deliver-B` (`authImplC`). Its runs from the
initial state for a key `k` are `authRun`.

- `prEvent_noDeliverWin_win_eq_authExp`: `Pr[win]` in `fs-aead-nd` for `fromAEADPRG ae prg` is the
  probability of a recorded first win in `G_auth^0` for the chain `G_i = prg.gen`.

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Figure 5, Figure 6, Theorem 5.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal OracleComp.ProgramLogic.Relational

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type}

/-- The state of the FS-AEAD game for the construction. -/
abbrev CState (W Kae AD M Cae : Type) :=
  GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae)

variable [DecidableEq AD] [DecidableEq Cae]

/-- `G_auth^j` for `fromAEADChain ae G`, with `O-Deliver-B^lk` and the history. -/
def authImplC (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (b : Bool) (j : ℕ) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (StateT (CState W Kae AD M Cae × AuthHist) ProbComp) :=
  authImpl (fromAEADChain ae G) len b j (oracleDeliverBLookup G)

/-- The run of `G_auth^j` for `fromAEADChain ae G` from the initial state for the key `k`. -/
def authRun (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (b : Bool) (j : ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W) :
    ProbComp (Bool × (CState W Kae AD M Cae × AuthHist)) :=
  (simulateQ (authImplC ae G len b j) adversary).run (.init (fromAEADChain ae G) k, .init)

/-- The experiment of `G_auth^j` for `fromAEADChain ae G`: sample the key `k` and the bit `b`,
then run the adversary. -/
def authExp [SampleableType W] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (j : ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    ProbComp (Bool × (CState W Kae AD M Cae × AuthHist)) := do
  let k ← $ᵗ W
  let b ← $ᵗ Bool
  authRun ae G len b j adversary k

/-- Every step of `G_auth^j` for the construction keeps `HistInv j`. -/
theorem authImplC_histInv (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (b : Bool) (j : ℕ) (t) (s : CState W Kae AD M Cae × AuthHist)
    (hI : HistInv j s) : ∀ z ∈ support ((authImplC ae G len b j t).run s), HistInv j z.2 :=
  authImpl_histInv _ len b j (oracleDeliverBLookup_flags G) t s hI

/-- Every final state of `G_auth^j` satisfies `HistInv j`. -/
theorem histInv_authRun (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (b : Bool) (j : ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W) :
    ∀ z ∈ support (authRun ae G len b j adversary k), HistInv j z.2 :=
  fun z hz => simulateQ_run_preserves_inv_of_query _ (HistInv j)
    (authImplC_histInv ae G len b j) adversary _ (histInv_init j rfl) z hz

/-- Let `ae` be correct. Then `fs-aead-nd` for `fromAEADChain ae G` sets `win` with the probability
that `G_auth^0` records a first win. -/
theorem prEvent_noDeliverWin_win_eq_authExp [SampleableType W]
    {ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae} (hae : ae.Correct) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    Pr{let r ← (gameRun (fromAEADChain ae G)
        (fsaeadNoDeliverWinImpl (fromAEADChain ae G) len) adversary)}[r.2.2.win = true] =
      Pr{let z ← authExp ae G len 0 adversary}[z.2.2.firstWin.isSome = true] := by
  classical
  rw [prEvent_gameRun_mon_win_eq_lookup hae len adversary, gameRun, authExp]
  refine prEvent_bind_congr _ _ _ _ _ fun k => prEvent_bind_congr _ _ _ _ _ fun b => ?_
  rw [prEvent_map, fsaeadMonLookupImpl,
    prEvent_win_eq_injectBStop _ len b
      (fun q st z hz => (oracleDeliverBLookup_flags G q st z hz).1),
    prEvent_win_eq_authImplWith _ len b (oracleDeliverBLookup_flags G) adversary _
      (fun h => absurd h Bool.false_ne_true),
    ← extendState_run_proj_eq (authImplWith (fromAEADChain ae G) len b 0 (oracleDeliverBLookup G))
      authAux adversary _ AuthHist.init, prEvent_map]
  refine prEvent_congr_of_support _ _ _ fun z hz => ?_
  have := histInv_authRun ae G len b 0 adversary k z hz
  simp only [Prod.map_snd, this.firstWin]

/-! ## No first win above a corruption of A -/

omit [DecidableEq AD] [DecidableEq Cae] in
/-- B has used index `i`: `D[i] = ⊥` and `i ≤ i_B`. `rcvKey` rejects it (`rcvKey_eq_none_iff`). -/
def Consumed (vB : RecvState W Kae) (i : ℕ) : Prop := vB.D i = none ∧ i ≤ vB.iB

omit [DecidableEq AD] [DecidableEq Cae] in
/-- Let B's state be on the chain, and let `rcvKey` move it from `st` to `st'` for index `i`.
Then B has used `i` in `st'`, and every index that B has used in `st`. -/
theorem consumed_of_rcvKey_some {G : ℕ → W → W × Kae} {k : W} {st st' : RecvState W Kae}
    (hst : OnChain G k st) {i : ℕ} {K : Kae} (h : rcvKey G st i = some (st', K)) :
    Consumed st' i ∧ ∀ j, Consumed st j → Consumed st' j := by
  obtain ⟨-, -, -, hiB, hDi, hDj⟩ := rcvKey_some G hst h
  refine ⟨⟨hDi, by omega⟩, fun j hj => ⟨?_, by have := hj.2; omega⟩⟩
  have := hj.2
  by_cases hji : j = i
  · exact hji ▸ hDi
  · rw [hDj j hji, ite_eq_right (by omega)]
    exact hj.1

omit [DecidableEq AD] [DecidableEq Cae] in
/-- The invariant of `G_auth^j` for the authenticity bound.
- B is on the chain from `k`.
- After a successful `O-Corr-A`, `minCorrA` is the smallest counter `t` of A at such a call, and
  every index `i > t` outside `comp` is used by B. So B accepts no injection at such an index.
- The first win is at an index `p ≥ 1`, and `p ≤ t` for the counter `t` of every successful
  `O-Corr-A`. -/
structure AuthInv (G : ℕ → W → W × Kae) (k : W) (s : CState W Kae AD M Cae × AuthHist) :
    Prop where
  vB : OnChain G k s.1.vB
  corrA : s.1.corrA = true → s.2.minCorrA.isSome
  minCorrA : ∀ t, s.2.minCorrA = some t → s.1.corrA = true ∧ t ≤ s.1.iA
  comp : ∀ t, s.2.minCorrA = some t → ∀ i, t < i → s.1.comp i = false → Consumed s.1.vB i
  firstWin : ∀ p, s.2.firstWin = some p → 1 ≤ p ∧ ∀ t, s.2.minCorrA = some t → p ≤ t

omit [DecidableEq AD] [DecidableEq Cae] in
/-- A step that changes neither B's state, nor `corrA`, nor `comp`, nor the history, and does not
lower `i_A`, keeps `AuthInv`. -/
theorem AuthInv.of_eq {G : ℕ → W → W × Kae} {k : W} {st st' : CState W Kae AD M Cae}
    {h : AuthHist} (hI : AuthInv G k (st, h)) (hvB : st'.vB = st.vB) (hc : st'.corrA = st.corrA)
    (hcomp : st'.comp = st.comp) (hiA : st.iA ≤ st'.iA) : AuthInv G k (st', h) :=
  ⟨hvB ▸ hI.vB, hc ▸ hI.corrA, fun t ht => hc ▸ ⟨(hI.minCorrA t ht).1, by
    have := (hI.minCorrA t ht).2; simp only at this ⊢; omega⟩,
    fun t ht i hi hci => hvB ▸ hI.comp t ht i hi (hcomp ▸ hci), hI.firstWin⟩

/-- Every step of `G_auth^j` for the chain `G` keeps `AuthInv G k`. -/
theorem authInv_step (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (k : W) (len : M → ℕ) (b : Bool) (j : ℕ)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (s : CState W Kae AD M Cae × AuthHist) (hH : HistInv j s) (hI : AuthInv G k s) :
    ∀ z ∈ support ((authImplC ae G len b j t).run s), AuthInv G k z.2 := by
  obtain ⟨st, h⟩ := s
  intro z hz
  obtain ⟨y, hy, rfl⟩ := QueryImpl.mem_support_extendState_run _ authAux t st h hz
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, e⟩) | ⟨a, e⟩)
  · change y ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hy
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hy
    obtain ⟨x, rfl⟩ := hy
    exact hI
  · change y ∈ support ((oracleTransmitA (fromAEADChain ae G) (a, m)).run st) at hy
    simp only [oracleTransmitA, StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hI
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy
      refine hI.of_eq ?_ ?_ ?_ ?_ <;> unfold GameState.record <;> split_ifs <;>
        first | rfl | (simp only; omega)
  · change y ∈ support ((oracleChallA (fromAEADChain ae G) len b (a, m₀, m₁)).run st) at hy
    simp only [oracleChallA, StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hI
    all_goals
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy
      refine hI.of_eq ?_ ?_ ?_ ?_ <;> unfold GameState.record <;> split_ifs <;>
        first | rfl | (simp only; omega)
  · change y ∈ support ((oracleCorrALow _ _ _ _ _ j ()).run st) at hy
    cases hend : st.end_
    · have hfw : h.firstWin = none := by
        have h₁ := hH.firstWin
        rw [hH.win_false hend] at h₁
        exact Option.not_isSome_iff_eq_none.mp (by simpa only [Bool.not_eq_true] using h₁)
      -- the new history and the new `comp`
      have key : AuthInv G k
          ({ st with
              corrA := true
              comp := if st.corrA then st.comp else fun i => decide (st.iA < i) },
            { h with minCorrA := some (h.minCorrA.elim st.iA (min · st.iA)) }) := by
        refine ⟨hI.vB, fun _ => rfl, fun t ht => ⟨rfl, ?_⟩, fun t ht i hi hci => ?_,
          fun p hp => absurd hp (by simp only [hfw, reduceCtorEq, not_false_eq_true])⟩
        · simp only [Option.some.injEq] at ht
          change t ≤ st.iA
          cases hm : h.minCorrA <;> simp only [hm, Option.elim_none, Option.elim_some] at ht <;>
            omega
        · simp only [Option.some.injEq] at ht
          change Consumed st.vB i
          change (if st.corrA then st.comp else fun i => decide (st.iA < i)) i = false at hci
          cases hc : st.corrA
          · rw [hc] at hci
            simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not, not_lt] at hci
            cases hm : h.minCorrA <;> simp only [hm, Option.elim_none, Option.elim_some] at ht
            · omega
            · obtain ⟨hc', -⟩ := hI.minCorrA _ hm
              rw [hc] at hc'
              exact absurd hc' Bool.false_ne_true
          · rw [hc] at hci
            simp only [↓reduceIte] at hci
            obtain ⟨t₀, hm⟩ := Option.isSome_iff_exists.mp (hI.corrA hc)
            change h.minCorrA = some t₀ at hm
            simp only [hm, Option.elim_some] at ht
            have h₀ : t₀ ≤ st.iA := (hI.minCorrA t₀ hm).2
            exact hI.comp t₀ hm i (by omega) hci
      by_cases hlt : st.iA < j <;>
        (simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, hlt,
           Bool.false_eq_true, ↓reduceIte, StateT.run_set, StateT.run_pure, support_pure,
           Set.mem_singleton_iff] at hy
         subst hy
         simp only [authAux, hend, Bool.false_eq_true, ↓reduceIte]
         exact key.of_eq rfl rfl rfl le_rfl)
    · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend,
        ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [authAux, hend, ↓reduceIte] using hI
  · change y ∈ support ((oracleCorrBSilent _ _ _ _ _ ()).run st) at hy
    simp only [oracleCorrBSilent, StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hI.vB, hI.corrA, hI.minCorrA, hI.comp, hI.firstWin⟩
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hI.vB, hI.corrA, hI.minCorrA, hI.comp, hI.firstWin⟩
  · change y ∈ support ((oracleDeliverBLookup G (a, e)).run st) at hy
    simp only [oracleDeliverBLookup, StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hI
    rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
    · simp only [hf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hI
    simp only [hf, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    -- B's new state has used `i` and every index that it used before
    obtain ⟨vB', hvB, hon, hci, hold⟩ : ∃ vB', ((rcvKey G st.vB i).map Prod.fst).getD st.vB = vB' ∧
        OnChain G k vB' ∧ Consumed vB' i ∧ ∀ q, Consumed st.vB q → Consumed vB' q := by
      rcases hr : rcvKey G st.vB i with _ | ⟨vB', K⟩
      · exact ⟨st.vB, rfl, hI.vB, (rcvKey_eq_none_iff G st.vB i).1 hr, fun _ h => h⟩
      · exact ⟨vB', rfl, (rcvKey_some G hI.vB hr).2.2.1, consumed_of_rcvKey_some hI.vB hr⟩
    rw [hvB]
    refine ⟨hon, hI.corrA, hI.minCorrA, fun t ht q hq hcq => ?_, hI.firstWin⟩
    simp only [GameState.delete, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hcq
    by_cases hqi : q = i
    · exact hqi ▸ hci
    · exact hold q (hI.comp t ht q hq (hcq.resolve_left hqi))
  · change y ∈ support ((oracleInjectBStop (fromAEADChain ae G) (a, e)).run st) at hy
    simp only [oracleInjectBStop, StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [authAux, Bool.not_and_self, Bool.false_eq_true, ↓reduceIte] using hI
    obtain ⟨i, e⟩ := e
    rcases hr : rcv ae G st.vB a (i, e) with _ | ⟨vB', i', m'⟩
    · simp only [fromAEADChain, hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [authAux, Bool.not_and_self, Bool.false_eq_true, ↓reduceIte] using hI
    simp only [fromAEADChain, hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨K, hk, hii, -⟩ := rcvKey_of_rcv_eq_some ae G hr
    subst hii
    have hon := (rcvKey_some G hI.vB hk).2.2.1
    have hi1 := (rcvKey_some G hI.vB hk).2.1
    obtain ⟨hci, hold⟩ := consumed_of_rcvKey_some hI.vB hk
    -- the new `comp` and the new first win
    have hcomp : ∀ t, h.minCorrA = some t → ∀ q, t < q →
        (fun j => j != i' && st.comp j) q = false → Consumed vB' q := by
      intro t ht q hq hcq
      simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hcq
      by_cases hqi : q = i'
      · exact hqi ▸ hci
      · exact hold q (hI.comp t ht q hq (hcq.resolve_left hqi))
    have hwin : ∀ t, h.minCorrA = some t → st.comp i' = false → i' ≤ t := by
      intro t ht hc
      by_contra hlt
      have := hI.comp t ht i' (by omega) hc
      rw [(rcvKey_eq_none_iff G st.vB i').2 this] at hk
      exact absurd hk (by simp only [reduceCtorEq, not_false_eq_true])
    by_cases hflip : (!st.win && (st.win || !st.comp i')) = true
    · simp only [authAux, GameState.delete, hflip, ↓reduceIte, Option.map_some]
      refine ⟨hon, hI.corrA, hI.minCorrA, hcomp, fun p hp => ?_⟩
      simp only [Option.some.injEq] at hp
      subst hp
      refine ⟨hi1, fun t ht => hwin t ht ?_⟩
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true] at hflip
      rcases hflip with ⟨hw, hw' | hc⟩
      · simp only [hw, Bool.false_eq_true] at hw'
      · exact hc
    · simp only [authAux, GameState.delete, hflip, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hon, hI.corrA, hI.minCorrA, hcomp, hI.firstWin⟩

/-- Every final state of `G_auth^j` for the chain `G` from `k` satisfies `AuthInv G k`. -/
theorem authInv_authRun (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (b : Bool) (j : ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W) :
    ∀ z ∈ support (authRun ae G len b j adversary k), AuthInv G k z.2 := by
  intro z hz
  have h₀ : AuthInv G k ((GameState.init (fromAEADChain ae G) k : CState W Kae AD M Cae),
      AuthHist.init) :=
    ⟨⟨rfl, fun _ _ h => (nomatch h), fun _ _ => rfl⟩, fun h => (nomatch h),
      fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  exact (simulateQ_run_preserves_inv_of_query _ (fun s => HistInv j s ∧ AuthInv G k s)
    (fun t s hs y hy => ⟨authImplC_histInv ae G len b j t s hs.1 y hy,
      authInv_step ae G k len b j t s hs.1 hs.2 y hy⟩) adversary _
    ⟨histInv_init j rfl, h₀⟩ z hz).2

/-! ## From `G_auth^0` to `G_auth^j` -/

omit [DecidableEq AD] [DecidableEq Cae] in
/-- The bad event of the step to `G_auth^j`: a successful `O-Corr-A` at a counter below `j`, or a
successful `O-Corr-B`. -/
def LowBad (j : ℕ) (h : AuthHist) : Prop := (∃ t, h.minCorrA = some t ∧ t < j) ∨ h.corrB = true

omit [DecidableEq AD] [DecidableEq Cae] in
/-- The history update keeps `LowBad j`. -/
theorem lowBad_authAux {j : ℕ}
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (st : CState W Kae AD M Cae) (u) (st' : CState W Kae AD M Cae) {h : AuthHist}
    (hb : LowBad j h) : LowBad j (authAux t st u st' h) := by
  rcases t with ((((((n | q) | q) | u) | u) | q) | q)
  any_goals exact hb
  · simp only [authAux]
    split_ifs
    · exact hb
    · rcases hb with ⟨t, ht, htj⟩ | hb
      · exact .inl ⟨min t st.iA, by simp only [ht, Option.elim_some], by omega⟩
      · exact .inr hb
  · simp only [authAux]
    rcases hb with hb | hb
    · exact .inl hb
    · exact .inr (by simp only [hb, Bool.true_or])
  · simp only [authAux]
    split_ifs
    · exact hb
    · exact hb

/-- From a state without `LowBad j`, `O-Corr-A` and `O-Corr-A^j` with the history give every
event the same probability away from `LowBad j`. -/
theorem prEvent_corrA_and_not_lowBad_eq (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (b : Bool) (j : ℕ)
    (s : CState W Kae AD M Cae × AuthHist)
    (q : Option (SendState W) × (CState W Kae AD M Cae × AuthHist) → Prop) :
    Pr{let z ← (authImplC ae G len b 0 fsaeadSpec.OCorrA).run s}[q z ∧ ¬LowBad j z.2.2] =
      Pr{let z ← (authImplC ae G len b j fsaeadSpec.OCorrA).run s}[q z ∧ ¬LowBad j z.2.2] := by
  obtain ⟨st, h⟩ := s
  simp only [authImplC, authImpl, authImplWith, QueryImpl.extendState_apply,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  by_cases hend : st.end_ = true
  · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, ↓reduceIte,
      StateT.run_pure]
  have hbad (x : Option (SendState W) × (CState W Kae AD M Cae × AuthHist))
      (hx : LowBad j x.2.2) :
      Pr{let z ← (pure x : ProbComp _)}[q z ∧ ¬LowBad j z.2.2] = 0 :=
    prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hq => by
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hq.2 hx
  by_cases hlt : st.iA < j
  · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, hlt,
      Bool.false_eq_true, ↓reduceIte, Nat.not_lt_zero, StateT.run_set, StateT.run_pure]
    erw [hbad _ ?_, hbad _ ?_] <;>
      refine .inl ⟨h.minCorrA.elim st.iA (min · st.iA),
        by simp only [authAux, hend, Bool.false_eq_true, ↓reduceIte], ?_⟩ <;>
      cases h.minCorrA <;> simp only [Option.elim_none, Option.elim_some] <;> omega
  · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, hlt,
      Bool.false_eq_true, ↓reduceIte, Nat.not_lt_zero]

/-- **From `G_auth^0` to `G_auth^j`.** Let `X` be an event of the history that implies a first
win at an index `p ≥ j`. Then `G_auth^0` and `G_auth^j` give `X` the same probability.

Before the first win, a successful `O-Corr-A` at a counter `t < j` leaves every index `p > t`
compromised or used by B (`AuthInv`), so no first win at `p ≥ j` follows; a successful `O-Corr-B`
ends the game. The two games differ only after such a call. -/
theorem prEvent_authRun_eq_low (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (b : Bool) (j : ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W)
    (X : AuthHist → Prop) (hX : ∀ h, X h → ∃ p, h.firstWin = some p ∧ j ≤ p) :
    Pr{let z ← authRun ae G len b 0 adversary k}[X z.2.2] =
      Pr{let z ← authRun ae G len b j adversary k}[X z.2.2] := by
  have hnot (j' : ℕ) (hlow : ∀ z ∈ support (authRun ae G len b j' adversary k), X z.2.2 →
      ¬LowBad j z.2.2) :
      Pr{let z ← authRun ae G len b j' adversary k}[X z.2.2] =
        Pr{let z ← authRun ae G len b j' adversary k}[X z.2.2 ∧ ¬LowBad j z.2.2] :=
    prEvent_congr_of_support _ _ _ fun z hz => ⟨fun h => ⟨h, hlow z hz h⟩, And.left⟩
  rw [hnot 0 ?_, hnot j ?_]
  · refine prEvent_simulateQ_run_and_not_bad_eq (authImplC ae G len b 0)
      (authImplC ae G len b j) (fun s : CState W Kae AD M Cae × AuthHist => LowBad j s.2) ?_ ?_ ?_
      adversary _ fun z => X z.2.2
    · intro t s _ q
      rcases t with ((((((n | q') | q') | u) | u) | q') | q')
      any_goals rfl
      exact prEvent_corrA_and_not_lowBad_eq ae G len b j s q
    all_goals
      intro t s hb z hz
      obtain ⟨y, -, rfl⟩ := QueryImpl.mem_support_extendState_run _ authAux t s.1 s.2 hz
      exact lowBad_authAux t s.1 y.1 y.2 hb
  · intro z hz hXz hb
    obtain ⟨p, hp, hjp⟩ := hX _ hXz
    have hI := histInv_authRun ae G len b j adversary k z hz
    have hw : z.2.1.win = true := by rw [← hI.firstWin, hp]; rfl
    rcases hb with ⟨t, ht, htj⟩ | hb
    · rw [(hI.low t ht htj).2] at hw
      exact Bool.false_ne_true hw
    · rw [(hI.corrB hb).2] at hw
      exact Bool.false_ne_true hw
  · intro z hz hXz hb
    obtain ⟨p, hp, hjp⟩ := hX _ hXz
    have hI := histInv_authRun ae G len b 0 adversary k z hz
    have hA := authInv_authRun ae G len b 0 adversary k z hz
    rcases hb with ⟨t, ht, htj⟩ | hb
    · have := (hA.firstWin p hp).2 t ht
      omega
    · have hw : z.2.1.win = true := by rw [← hI.firstWin, hp]; rfl
      rw [(hI.corrB hb).2] at hw
      exact Bool.false_ne_true hw

end FromAEADPRG

end FSAEADScheme
