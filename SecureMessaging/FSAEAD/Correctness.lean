/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.Defs
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# FS-AEAD — Correctness from a game invariant

A `DeliverInv` for a scheme `fs` is an invariant of the FS-AEAD security game under which
`O-Deliver-B` never changes `win` from false to true. It gives two results:
- `DeliverInv.correct`: `fs` is correct (`FSAEADScheme.Correct`).
- `DeliverInv.securityExp_eq_noDeliverWin`: the security experiment equals the experiment
  of the game `fs-aead-nd` ("no delivery check"), the game of Figure 5 with
  `O-Deliver-B^nd` (`oracleDeliverBNoWin`) for `O-Deliver-B`. The proof of Theorem 5 of
  [ACD19] uses this step from `H1` to `H2`.

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Figure 5, proof of Theorem 5.
-/

@[expose] public section

open OracleSpec OracleComp

namespace FSAEADScheme

variable {K StS StR AD M C : Type}

section NoDeliverWin

variable [DecidableEq AD] [DecidableEq C]

/-- `O-Deliver-B^nd`, the oracle of `fs-aead-nd`: `O-Deliver-B` without its two assignments
`win ← true`. Everything else is as in `oracleDeliverB`. -/
def oracleDeliverBNoWin (fs : FSAEADScheme K StS StR AD M C) :
    QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C) :=
  fun (a, e) => do
    let st ← get
    if st.end_ then return none
    let some (i, _, _, _) := st.findTrans a e | return none
    match fs.rcv st.vB a e with
    | none => return none
    | some (vB, i', m') =>
      set ({ st with vB }.delete i)
      return some (i', if i ∈ st.chall then none else some m')

/-- The oracles of `fs-aead-nd`: `fsaeadSecurityImpl`, with `oracleDeliverBNoWin` for
`O-Deliver-B`. -/
def fsaeadNoDeliverWinImpl (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec StS StR AD M C) (GameM StS StR AD M C) :=
  oracleUnif StS StR AD M C
    + oracleTransmitA fs
    + oracleChallA fs len b
    + oracleCorrA StS StR AD M C
    + oracleCorrB StS StR AD M C
    + oracleDeliverBNoWin fs
    + oracleInjectB fs

/-- The experiment of `fs-aead-nd`: `securityExp` with `fsaeadNoDeliverWinImpl` for
`fsaeadSecurityImpl`. -/
def securityExpNoDeliverWin [SampleableType K] (fs : FSAEADScheme K StS StR AD M C)
    (len : M → ℕ) (adversary : FSAEADAdversary StS StR AD M C) : ProbComp Bool := do
  let k ← $ᵗ K
  let b ← $ᵗ Bool
  let (b', st) ← (simulateQ (fsaeadNoDeliverWinImpl fs len b) adversary).run (.init fs k)
  return st.win || b == b'

variable [DecidableEq M]

/-- Let `st` be a state with `win = false`, and let every outcome of `O-Deliver-B(q)` from
`st` have `win = false`. Then `O-Deliver-B(q)` and `oracleDeliverBNoWin` agree on `st`. -/
private theorem oracleDeliverB_run_eq_noWin_of_win_false (fs : FSAEADScheme K StS StR AD M C)
    (q : AD × C) (st : GameState StS StR AD M C) (hwin : st.win = false)
    (h : ∀ z ∈ support ((oracleDeliverB fs q).run st), z.2.win = false) :
    (oracleDeliverB fs q).run st = (oracleDeliverBNoWin fs q).run st := by
  obtain ⟨a, e⟩ := q
  simp only [oracleDeliverB, oracleDeliverBNoWin, StateT.run_bind, StateT.run_get,
    pure_bind] at h ⊢
  split_ifs at h ⊢ with hend
  · rfl
  rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
  · simp only [StateT.run_pure]
  rcases hr : fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
  · simp_all only [Bool.not_eq_true, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure,
        MonadAttach.support_pure, Set.mem_singleton_iff, Bool.true_eq_false, imp_false, forall_eq]
  · simp_all only [Bool.not_eq_true, GameState.delete, Bool.not_and, Bool.false_or, ne_eq,
        decide_not, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure,
        MonadAttach.support_pure, Set.mem_singleton_iff, Bool.or_eq_false_iff,
        Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, forall_eq, decide_true,
        Bool.and_self, Bool.not_true, Bool.or_self]

/-- Let `st` be a state with `win = true`. Then `O-Deliver-B` and `oracleDeliverBNoWin`
agree on `st`. -/
private theorem oracleDeliverB_run_eq_noWin_of_win_true (fs : FSAEADScheme K StS StR AD M C)
    (q : AD × C) (st : GameState StS StR AD M C) (hwin : st.win = true) :
    (oracleDeliverB fs q).run st = (oracleDeliverBNoWin fs q).run st := by
  obtain ⟨a, e⟩ := q
  simp only [oracleDeliverB, oracleDeliverBNoWin, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hend
  · rfl
  rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
  · simp only [StateT.run_pure]
  rcases hr : fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
  · obtain ⟨⟩ := st
    simp_all only [Bool.not_eq_true, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure,
        StateT.run_pure]
  · simp only [hwin, Bool.not_and, Bool.true_or, bind_pure_comp, StateT.run_map, StateT.run_set,
        map_pure]

end NoDeliverWin

section DeliverInv

variable [DecidableEq AD] [DecidableEq M] [DecidableEq C]

/-- A family `Inv k` of invariants of the FS-AEAD security game for key `k`, under which
`O-Deliver-B` never changes `win` from false to true. -/
structure DeliverInv (fs : FSAEADScheme K StS StR AD M C)
    (Inv : K → GameState StS StR AD M C → Prop) : Prop where
  /-- The initial state for `k` satisfies `Inv k`. -/
  init : ∀ k, Inv k (.init fs k)
  /-- Every oracle of the security game keeps `Inv k`, for every length function and
  challenge bit. -/
  step : ∀ (len : M → ℕ) (b : Bool) (k : K) (t : (fsaeadSpec StS StR AD M C).Domain)
    (st : GameState StS StR AD M C) {z}, Inv k st →
    z ∈ support ((fsaeadSecurityImpl fs len b t).run st) → Inv k z.2
  /-- From a state with `Inv k` and `win = false`, every outcome of `O-Deliver-B` has
  `win = false`. -/
  deliverB : ∀ (k : K) (st : GameState StS StR AD M C) (q : AD × C), Inv k st →
    st.win = false → ∀ z ∈ support ((oracleDeliverB fs q).run st), z.2.win = false

variable {fs : FSAEADScheme K StS StR AD M C} {Inv : K → GameState StS StR AD M C → Prop}

/-- Let `Inv` be a `DeliverInv` for `fs`. Then every oracle of the correctness game keeps
`Inv k ∧ win = false`. -/
theorem DeliverInv.correctness_step (h : DeliverInv fs Inv) (k : K) :
    QueryImpl.PreservesInv (fsaeadCorrectnessImpl fs) fun st => Inv k st ∧ st.win = false := by
  intro t st ⟨hinv, hw⟩ z hz
  -- the oracles shared with the security game, which keep `Inv k` by `h.step`
  have hsec (t' : (fsaeadSpec StS StR AD M C).Domain)
      (hy : ∃ y ∈ support ((fsaeadSecurityImpl fs (fun _ => 0) false t').run st), y.2 = z.2)
      (hwin : z.2.win = false) : Inv k z.2 ∧ z.2.win = false := by
    obtain ⟨y, hy, hyz⟩ := hy
    exact ⟨hyz ▸ h.step _ _ k t' st hinv hy, hwin⟩
  rcases t with (((((n | ⟨a, m⟩) | u) | u) | q) | ⟨a, e⟩)
  · refine hsec (fsaeadSpec.OUnif n) ⟨z, hz, rfl⟩ ?_
    change z ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hz
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hz
    obtain ⟨x, rfl⟩ := hz
    exact hw
  · refine hsec (fsaeadSpec.OTransmitA (a, m)) ⟨z, hz, rfl⟩ ?_
    change z ∈ support ((oracleTransmitA fs (a, m)).run st) at hz
    simp only [oracleTransmitA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hw
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      unfold GameState.record
      split_ifs <;> exact hw
  · refine hsec fsaeadSpec.OCorrA ⟨z, hz, rfl⟩ ?_
    change z ∈ support ((oracleCorrA _ _ _ _ _ ()).run st) at hz
    simp only [oracleCorrA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hw
    all_goals
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact hw
  · refine hsec fsaeadSpec.OCorrB ⟨z, hz, rfl⟩ ?_
    change z ∈ support ((oracleCorrB _ _ _ _ _ ()).run st) at hz
    simp only [oracleCorrB, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hw
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact hw
  · exact hsec (fsaeadSpec.ODeliverB q) ⟨z, hz, rfl⟩ (h.deliverB k st q hinv hw z hz)
  · -- `O-Inject-B^corr` either returns `⊥` or acts as `O-Inject-B` at a compromised index
    change z ∈ support ((oracleInjectBCorr fs (a, e)).run st) at hz
    simp only [oracleInjectBCorr, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz with hend
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hinv, hw⟩
    rcases hr : fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
    · simp only [hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hinv, hw⟩
    simp only [hr] at hz
    split_ifs at hz with hc
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hinv, hw⟩
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
    refine ⟨h.step (fun _ => 0) false k (fsaeadSpec.OInjectB (a, e)) st hinv ?_, hw⟩
    change _ ∈ support ((oracleInjectB fs (a, e)).run st)
    simp only [oracleInjectB, StateT.run_bind, StateT.run_get, pure_bind, hend, hr, hc,
      Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte, StateT.run_set,
      StateT.run_pure, support_pure, Set.mem_singleton_iff]

/-- Let `Inv` be a `DeliverInv` for `fs`. Then `fs` is correct. -/
theorem DeliverInv.correct [SampleableType K] (h : DeliverInv fs Inv) : fs.Correct := by
  intro adversary
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun x hx => ?_
  simp only [correctnessExp, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨k, -, z, hz, rfl⟩ := hx
  have := simulateQ_run_preservesInv _ _ (h.correctness_step k) adversary _
    ⟨h.init k, rfl⟩ z hz
  simp only [this.2, Bool.false_eq_true, not_false_eq_true]

/-- Let `Inv` be a `DeliverInv` for `fs`. Then for every length function `len` and every
adversary, `securityExp` equals the experiment of `fs-aead-nd`. -/
theorem DeliverInv.securityExp_eq_noDeliverWin [SampleableType K] (h : DeliverInv fs Inv)
    (len : M → ℕ) (adversary : FSAEADAdversary StS StR AD M C) :
    securityExp fs len adversary = securityExpNoDeliverWin fs len adversary := by
  unfold securityExp securityExpNoDeliverWin
  congr 1; funext k; congr 1; funext b
  have hsim := map_run_simulateQ_eq_of_query_map_eq_inv' (fsaeadSecurityImpl fs len b)
    (fsaeadNoDeliverWinImpl fs len b) (Inv k) id
    (fun t s hs _ hy => h.step len b k t s hs hy) ?_ adversary _ (h.init k)
  · simp only [Prod.map_id, id_map, id] at hsim
    rw [hsim]
  · intro t st hst
    simp only [Prod.map_id, id_map, id]
    rcases t with ((((((n | am) | amm) | u) | u) | q) | q)
    all_goals try rfl
    cases hw : st.win
    · exact oracleDeliverB_run_eq_noWin_of_win_false fs q st hw (h.deliverB k st q hst hw)
    · exact oracleDeliverB_run_eq_noWin_of_win_true fs q st hw

end DeliverInv

end FSAEADScheme
