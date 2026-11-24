/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.Security.Reject
public import ToVCVio.OracleComp.SimSemantics.StateT.ExtendState
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# FS-AEAD security — the authenticity game with history

The authenticity step of the proof of Theorem 5 of [ACD19] bounds `Pr[win]` in `fs-aead-nd`.
Its reductions measure the position of the first win and stop at the first win. The final state
of `fs-aead-nd` does not record that position, so this file adds a passive history and makes
the game stop.

The game `G_auth^j` (`authImplWith`) changes three oracles of `fs-aead-nd`:
- `O-Inject-B^stop` (`oracleInjectBStop`) also sets `end` when it sets `win`, so the game stops
  at the first win.
- `O-Corr-B^⊥` (`oracleCorrBSilent`) sets `end` but returns `⊥` instead of the two states.
- `O-Corr-A^j` (`oracleCorrALow`) acts as `O-Corr-A`, but if `i_A < j` it also sets `end` and
  returns `⊥`. For `j = 0` it is `O-Corr-A`.

After `O-Corr-B` no oracle sets `win`, and the game stops at the first win, so for `j = 0` these
changes do not change `Pr[win]` (`prEvent_win_eq_authImplWith`).

The history (`AuthHist`, added with `QueryImpl.extendState`) records the position of the first
win, the smallest counter `i_A` at a successful `O-Corr-A`, and a successful `O-Corr-B`. It does
not change the game (`OracleComp.extendState_run_proj_eq`).

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Figure 5, Theorem 5.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal OracleComp.ProgramLogic.Relational

namespace FSAEADScheme

variable {K StS StR AD M C : Type}

/-! ### The oracles -/

/-- **O-Inject-B^stop(a, e)**. `O-Inject-B`, but a win also sets `end`.
```text
O-Inject-B^stop(a, e):
  req ¬(∃ i, m: (i, a, m, e) ∈ trans)
  r ← FS-Rcv(v_B, a, e)
  req r ≠ ⊥
  (v_B, i', m') ← r
  if i' ∉ comp: win ← true; end ← true
  delete(i')
  return (i', m')
``` -/
def oracleInjectBStop [DecidableEq AD] [DecidableEq C] (fs : FSAEADScheme K StS StR AD M C) :
    QueryImpl (AD × C →ₒ Option (ℕ × M)) (GameM StS StR AD M C) :=
  fun (a, e) => do
    let st ← get
    if st.end_ || (st.findTrans a e).isSome then return none
    let some (vB, i', m') := fs.rcv st.vB a e | return none
    set ({ st with vB, win := st.win || !st.comp i', end_ := !st.comp i' }.delete i')
    return some (i', m')

/-- **O-Corr-A^j**. `O-Corr-A`, but if `i_A < j` the oracle also sets `end` and returns `⊥`.
```text
O-Corr-A^j:
  [if ¬corrA: comp ← {i | i > i_A}]
  corrA ← true
  if i_A < j: end ← true; return ⊥
  return v_A
``` -/
def oracleCorrALow (StS StR AD M C : Type) (j : ℕ) :
    QueryImpl (Unit →ₒ Option StS) (GameM StS StR AD M C) :=
  fun () => do
    let st ← get
    if st.end_ then return none
    let comp := if st.corrA then st.comp else fun i => decide (st.iA < i)
    if st.iA < j then
      set { st with corrA := true, comp, end_ := true }
      return none
    set { st with corrA := true, comp }
    return some st.vA

/-- **O-Corr-B^⊥**. `O-Corr-B`, but it returns `⊥` instead of the two states.
```text
O-Corr-B^⊥:
  req chall = ∅
  end ← true
  return ⊥
``` -/
def oracleCorrBSilent (StS StR AD M C : Type) :
    QueryImpl (Unit →ₒ Option (StS × StR)) (GameM StS StR AD M C) :=
  fun () => do
    let st ← get
    if st.end_ || st.chall ≠ ∅ then return none
    set { st with end_ := true }
    return none

/-- `O-Corr-A^0` is `O-Corr-A`. -/
theorem oracleCorrALow_zero : oracleCorrALow StS StR AD M C 0 = oracleCorrA StS StR AD M C := by
  funext u
  simp only [oracleCorrALow, oracleCorrA, Nat.not_lt_zero, ↓reduceIte]

/-- The oracles of `G_auth^j`: `fs-aead-nd` with `deliver` for `O-Deliver-B`, and with
`O-Corr-A^j`, `O-Corr-B^⊥` and `O-Inject-B^stop`. -/
def authImplWith [DecidableEq AD] [DecidableEq C] (fs : FSAEADScheme K StS StR AD M C)
    (len : M → ℕ) (b : Bool) (j : ℕ)
    (deliver : QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C)) :
    QueryImpl (fsaeadSpec StS StR AD M C) (GameM StS StR AD M C) :=
  oracleUnif StS StR AD M C
    + oracleTransmitA fs
    + oracleChallA fs len b
    + oracleCorrALow StS StR AD M C j
    + oracleCorrBSilent StS StR AD M C
    + deliver
    + oracleInjectBStop fs

/-! ### The history -/

/-- The history of a run of `G_auth^j`. -/
structure AuthHist where
  /-- The index of the injection that set `win`. -/
  firstWin : Option ℕ
  /-- The smallest counter `i_A` at a call of `O-Corr-A` before `end`. -/
  minCorrA : Option ℕ
  /-- Whether a call of `O-Corr-B` set `end`. -/
  corrB : Bool

/-- The empty history. -/
def AuthHist.init : AuthHist := ⟨none, none, false⟩

/-- The history update of a query `t` that moves the game from `st` to `st'` with answer `u`. -/
def authAux : (t : (fsaeadSpec StS StR AD M C).Domain) → GameState StS StR AD M C →
    (fsaeadSpec StS StR AD M C).Range t → GameState StS StR AD M C → AuthHist → AuthHist
  | .inl (.inl (.inl (.inr ()))), st, _, _, h =>
    if st.end_ then h else { h with minCorrA := some (h.minCorrA.elim st.iA (min · st.iA)) }
  | .inl (.inl (.inr ())), st, _, st', h =>
    { h with corrB := h.corrB || (!st.end_ && st'.end_) }
  | .inr _, st, u, st', h =>
    if !st.win && st'.win then { h with firstWin := u.map Prod.fst } else h
  | _, _, _, _, h => h

/-- `G_auth^j` with its history. -/
def authImpl [DecidableEq AD] [DecidableEq C] (fs : FSAEADScheme K StS StR AD M C)
    (len : M → ℕ) (b : Bool) (j : ℕ)
    (deliver : QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C)) :
    QueryImpl (fsaeadSpec StS StR AD M C) (StateT (GameState StS StR AD M C × AuthHist) ProbComp) :=
  (authImplWith fs len b j deliver).extendState authAux

end FSAEADScheme

namespace FSAEADScheme

variable {K StS StR AD M C : Type}


/-! ### Steps that stop at `end` -/

/-- A step from `st` to `st'` keeps `win`, sets it only together with `end`, and changes
neither flag after `end`. -/
structure StepOK (st st' : GameState StS StR AD M C) : Prop where
  end_ : st.end_ = true → st'.end_ = true ∧ st'.win = st.win
  win_mono : st.win = true → st'.win = true
  win_end : st'.win = true → st.win = true ∨ st'.end_ = true

theorem StepOK.of_eq {st st' : GameState StS StR AD M C} (h : st' = st) : StepOK st st' :=
  h ▸ ⟨fun h => ⟨h, rfl⟩, id, .inl⟩

theorem StepOK.of_flags {st st' : GameState StS StR AD M C} (hw : st'.win = st.win)
    (he : st.end_ = true → st'.end_ = true) : StepOK st st' :=
  ⟨fun h => ⟨he h, hw⟩, fun h => hw ▸ h, fun h => .inl (hw ▸ h)⟩

/-- Every step of `O-Transmit-A` is `StepOK`. -/
theorem oracleTransmitA_stepOK (fs : FSAEADScheme K StS StR AD M C) (q : AD × M)
    (st : GameState StS StR AD M C) :
    ∀ z ∈ support ((oracleTransmitA fs q).run st), StepOK st z.2 := by
  obtain ⟨a, m⟩ := q
  intro z hz
  simp only [oracleTransmitA, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact .of_eq rfl
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    refine .of_flags (GameState.record_win _ _ _ _ _) fun he => absurd he h

/-- Every step of `O-Chall-A` is `StepOK`. -/
theorem oracleChallA_stepOK (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (b : Bool)
    (q : AD × M × M) (st : GameState StS StR AD M C) :
    ∀ z ∈ support ((oracleChallA fs len b q).run st), StepOK st z.2 := by
  obtain ⟨a, m₀, m₁⟩ := q
  intro z hz
  simp only [oracleChallA, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact .of_eq rfl
  all_goals
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    refine .of_flags (GameState.record_win _ _ _ _ _) fun he => ?_
    simp only [he, Bool.true_or, ne_eq, decide_not, not_true_eq_false] at h

/-- Every step of `O-Corr-A^j` is `StepOK`. -/
theorem oracleCorrALow_stepOK (j : ℕ) (st : GameState StS StR AD M C) :
    ∀ z ∈ support ((oracleCorrALow StS StR AD M C j ()).run st), StepOK st z.2 := by
  intro z hz
  simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact .of_eq rfl
  all_goals
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact .of_flags rfl fun he => absurd he h

/-- Every step of `O-Corr-B` is `StepOK`. -/
theorem oracleCorrB_stepOK (st : GameState StS StR AD M C) :
    ∀ z ∈ support ((oracleCorrB StS StR AD M C ()).run st), StepOK st z.2 := by
  intro z hz
  simp only [oracleCorrB, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact .of_eq rfl
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact .of_flags rfl fun _ => rfl

/-- Every step of `O-Corr-B^⊥` is `StepOK`. -/
theorem oracleCorrBSilent_stepOK (st : GameState StS StR AD M C) :
    ∀ z ∈ support ((oracleCorrBSilent StS StR AD M C ()).run st), StepOK st z.2 := by
  intro z hz
  simp only [oracleCorrBSilent, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact .of_eq rfl
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact .of_flags rfl fun _ => rfl

section Stop

variable [DecidableEq AD] [DecidableEq C]

/-- Every step of `O-Inject-B^stop` is `StepOK`. -/
theorem oracleInjectBStop_stepOK (fs : FSAEADScheme K StS StR AD M C) (q : AD × C)
    (st : GameState StS StR AD M C) :
    ∀ z ∈ support ((oracleInjectBStop fs q).run st), StepOK st z.2 := by
  obtain ⟨a, e⟩ := q
  intro z hz
  simp only [oracleInjectBStop, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact .of_eq rfl
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
  rcases hr : fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
  · simp only [hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact .of_eq rfl
  · simp only [hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨fun he => absurd he (by simp only [h.1, Bool.false_eq_true, not_false_eq_true]),
      fun hw => by simp only [GameState.delete, hw, Bool.true_or], fun hw => ?_⟩
    simp only [GameState.delete, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw ⊢
    rcases hw with hw | hw
    · exact .inl hw
    · exact .inr (by simp only [hw])

/-- Let `deliver` keep `win` and `end`. Then every step of `G_auth^j` is `StepOK`. -/
theorem authImplWith_stepOK (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (b : Bool)
    (j : ℕ) {deliver : QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C)}
    (hd : ∀ q st, ∀ z ∈ support ((deliver q).run st), z.2.win = st.win ∧ z.2.end_ = st.end_)
    (t : (fsaeadSpec StS StR AD M C).Domain) (st : GameState StS StR AD M C) :
    ∀ z ∈ support ((authImplWith fs len b j deliver t).run st), StepOK st z.2 := by
  intro z hz
  rcases t with ((((((n | q) | q) | u) | u) | q) | q)
  · change z ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hz
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hz
    obtain ⟨x, rfl⟩ := hz
    exact .of_eq rfl
  · exact oracleTransmitA_stepOK fs q st z hz
  · exact oracleChallA_stepOK fs len b q st z hz
  · exact oracleCorrALow_stepOK j st z hz
  · exact oracleCorrBSilent_stepOK st z hz
  · obtain ⟨hw, he⟩ := hd q st z hz
    exact .of_flags hw fun h => he.trans h
  · exact oracleInjectBStop_stepOK fs q st z hz

/-- Let `deliver` keep `win` and `end`. Then every step of `fs-aead-nd` with `deliver` and
`O-Inject-B^stop` is `StepOK`. -/
theorem fsaeadImplWith_stop_stepOK (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ)
    (b : Bool) {deliver : QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C)}
    (hd : ∀ q st, ∀ z ∈ support ((deliver q).run st), z.2.win = st.win ∧ z.2.end_ = st.end_)
    (t : (fsaeadSpec StS StR AD M C).Domain) (st : GameState StS StR AD M C) :
    ∀ z ∈ support ((fsaeadImplWith fs len b deliver (oracleInjectBStop fs) t).run st),
      StepOK st z.2 := by
  intro z hz
  rcases t with ((((((n | q) | q) | u) | u) | q) | q)
  · change z ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hz
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hz
    obtain ⟨x, rfl⟩ := hz
    exact .of_eq rfl
  · exact oracleTransmitA_stepOK fs q st z hz
  · exact oracleChallA_stepOK fs len b q st z hz
  · change z ∈ support ((oracleCorrA StS StR AD M C u).run st) at hz
    rw [← oracleCorrALow_zero] at hz
    exact oracleCorrALow_stepOK 0 st z hz
  · exact oracleCorrB_stepOK st z hz
  · obtain ⟨hw, he⟩ := hd q st z hz
    exact .of_flags hw fun h => he.trans h
  · exact oracleInjectBStop_stepOK fs q st z hz

/-- Let `deliver` keep `win` and `end`. Then from a state with `win → end`, the game with
`O-Inject-B^stop` and `G_auth^0` set `win` with the same probability: `O-Corr-B` sets `end`, so no
later oracle sets `win`. -/
theorem prEvent_win_eq_authImplWith (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (b : Bool)
    {deliver : QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C)}
    (hd : ∀ q st, ∀ z ∈ support ((deliver q).run st), z.2.win = st.win ∧ z.2.end_ = st.end_)
    (adversary : FSAEADAdversary StS StR AD M C) (s₀ : GameState StS StR AD M C)
    (hs₀ : s₀.win = true → s₀.end_ = true) :
    Pr{let z ← ((simulateQ (fsaeadImplWith fs len b deliver (oracleInjectBStop fs))
        adversary).run s₀)}[z.2.win = true] =
      Pr{let z ← (simulateQ (authImplWith fs len b 0 deliver) adversary).run s₀}[
        z.2.win = true] := by
  let Inv : GameState StS StR AD M C → Prop := fun st => st.win = true → st.end_ = true
  let bad : GameState StS StR AD M C → Prop := fun st => st.end_ = true ∧ ¬st.win = true
  have hI₁ : ∀ t st, Inv st → ∀ z ∈ support
      ((fsaeadImplWith fs len b deliver (oracleInjectBStop fs) t).run st), Inv z.2 :=
    fun t st hs z hz hw => by
      rcases (fsaeadImplWith_stop_stepOK fs len b hd t st z hz).win_end hw with h | h
      · exact ((fsaeadImplWith_stop_stepOK fs len b hd t st z hz).end_ (hs h)).1
      · exact h
  have hI₂ : ∀ t st, Inv st → ∀ z ∈ support ((authImplWith fs len b 0 deliver t).run st),
      Inv z.2 :=
    fun t st hs z hz hw => by
      rcases (authImplWith_stepOK fs len b 0 hd t st z hz).win_end hw with h | h
      · exact ((authImplWith_stepOK fs len b 0 hd t st z hz).end_ (hs h)).1
      · exact h
  have hgood := prEvent_simulateQ_run_and_not_bad_eq_of_inv _ _ Inv bad hI₁ hI₂ ?_
    (fun t st _ hb z hz => by
      obtain ⟨h₁, h₂⟩ := (fsaeadImplWith_stop_stepOK fs len b hd t st z hz).end_ hb.1
      exact ⟨h₁, h₂ ▸ hb.2⟩)
    (fun t st _ hb z hz => by
      obtain ⟨h₁, h₂⟩ := (authImplWith_stepOK fs len b 0 hd t st z hz).end_ hb.1
      exact ⟨h₁, h₂ ▸ hb.2⟩) adversary s₀ hs₀ fun z => z.2.win = true
  · have hc (mx : ProbComp (Bool × GameState StS StR AD M C)) :
        Pr{let z ← mx}[z.2.win = true ∧ ¬bad z.2] = Pr{let z ← mx}[z.2.win = true] :=
      prEvent_congr mx _ _ fun z => ⟨And.left, fun h => ⟨h, fun hb => hb.2 h⟩⟩
    rwa [hc, hc] at hgood
  · intro t st hs hb q
    rcases t with ((((((n | q') | q') | u) | u) | q') | q')
    any_goals rfl
    · change Pr{let z ← (oracleCorrB _ _ _ _ _ ()).run st}[q z ∧ ¬bad z.2] =
        Pr{let z ← (oracleCorrBSilent _ _ _ _ _ ()).run st}[q z ∧ ¬bad z.2]
      simp only [oracleCorrB, oracleCorrBSilent, StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs with h
      · rfl
      · have hend : st.end_ = false := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h
          simpa only [Bool.not_eq_true] using h.1
        have hwin : st.win = false := by
          cases hw : st.win
          · rfl
          · exact absurd (hs hw) (by simp only [hend, Bool.false_eq_true, not_false_eq_true])
        have h0 (x : Option (StS × StR) × GameState StS StR AD M C) (hx : bad x.2) :
            Pr{let z ← (pure x : ProbComp _)}[q z ∧ ¬bad z.2] = 0 := by
          classical
          simp only [prEvent_pure, hx, not_true_eq_false, and_false, ↓reduceIte]
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        rw [h0 _ ⟨rfl, by simp only [hwin, Bool.false_eq_true, not_false_eq_true]⟩,
          h0 _ ⟨rfl, by simp only [hwin, Bool.false_eq_true, not_false_eq_true]⟩]

/-! ### Invariants of the history -/

/-- The invariant of the history in `G_auth^j`.
- The first win is recorded exactly when `win` holds.
- `win` and a successful `O-Corr-B` set `end`; a successful `O-Corr-B` comes before any win.
- An `O-Corr-A` at a counter below `j` sets `end` and comes before any win. -/
structure HistInv (j : ℕ) (s : GameState StS StR AD M C × AuthHist) : Prop where
  firstWin : s.2.firstWin.isSome = s.1.win
  win_end : s.1.win = true → s.1.end_ = true
  corrB : s.2.corrB = true → s.1.end_ = true ∧ s.1.win = false
  low : ∀ t, s.2.minCorrA = some t → t < j → s.1.end_ = true ∧ s.1.win = false

omit [DecidableEq AD] [DecidableEq C] in
/-- The initial history satisfies the invariant in a state without `win`. -/
theorem histInv_init (j : ℕ) {st : GameState StS StR AD M C} (hw : st.win = false) :
    HistInv j (st, AuthHist.init) :=
  ⟨by simp only [AuthHist.init, Option.isSome_none, hw],
    fun h => absurd (hw ▸ h) Bool.false_ne_true,
    fun h => absurd h Bool.false_ne_true, fun _ h => absurd h (by simp only [AuthHist.init,
      reduceCtorEq, not_false_eq_true])⟩

omit [DecidableEq AD] [DecidableEq C] in
/-- A step that changes neither `win` nor `end` nor the history keeps the invariant. -/
theorem HistInv.of_flags {j : ℕ} {st st' : GameState StS StR AD M C} {h : AuthHist}
    (hI : HistInv j (st, h)) (hw : st'.win = st.win) (he : st'.end_ = st.end_) :
    HistInv j (st', h) :=
  ⟨hw ▸ hI.firstWin, fun h => he ▸ hI.win_end (hw ▸ h),
    fun h => he ▸ hw ▸ hI.corrB h, fun t h₁ h₂ => he ▸ hw ▸ hI.low t h₁ h₂⟩

omit [DecidableEq AD] [DecidableEq C] in
/-- Without `end` there is no `win`. -/
theorem HistInv.win_false {j : ℕ} {s : GameState StS StR AD M C × AuthHist} (hI : HistInv j s)
    (he : s.1.end_ = false) : s.1.win = false := by
  cases hw : s.1.win
  · rfl
  · exact absurd (hI.win_end hw) (by rw [he]; exact Bool.false_ne_true)

/-- Let `deliver` keep `win` and `end`. Then every step of `G_auth^j` with history keeps
`HistInv j`. -/
theorem authImpl_histInv (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (b : Bool)
    (j : ℕ) {deliver : QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C)}
    (hd : ∀ q st, ∀ z ∈ support ((deliver q).run st), z.2.win = st.win ∧ z.2.end_ = st.end_)
    (t : (fsaeadSpec StS StR AD M C).Domain) (s : GameState StS StR AD M C × AuthHist)
    (hI : HistInv j s) : ∀ z ∈ support ((authImpl fs len b j deliver t).run s), HistInv j z.2 := by
  obtain ⟨st, h⟩ := s
  intro z hz
  obtain ⟨y, hy, rfl⟩ := QueryImpl.mem_support_extendState_run _ authAux t st h hz
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | q) | ⟨a, e⟩)
  · change y ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hy
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hy
    obtain ⟨x, rfl⟩ := hy
    exact hI
  · change y ∈ support ((oracleTransmitA fs (a, m)).run st) at hy
    simp only [oracleTransmitA, StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hI
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy
      exact hI.of_flags (GameState.record_win _ _ _ _ _) (GameState.record_end_ _ _ _ _ _)
  · change y ∈ support ((oracleChallA fs len b (a, m₀, m₁)).run st) at hy
    simp only [oracleChallA, StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hI
    all_goals
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy
      exact hI.of_flags (GameState.record_win _ _ _ _ _) (GameState.record_end_ _ _ _ _ _)
  · change y ∈ support ((oracleCorrALow _ _ _ _ _ j ()).run st) at hy
    cases hend : st.end_
    · have hwin : st.win = false := hI.win_false hend
      by_cases hlt : st.iA < j
      · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, hlt,
          Bool.false_eq_true, ↓reduceIte, StateT.run_set, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hy
        subst hy
        simp only [authAux, hend, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hI.firstWin, fun h => absurd (hwin ▸ h) Bool.false_ne_true,
          fun _ => ⟨rfl, hwin⟩, fun _ _ _ => ⟨rfl, hwin⟩⟩
      · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, hlt,
          Bool.false_eq_true, ↓reduceIte, StateT.run_set, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hy
        subst hy
        simp only [authAux, hend, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hI.firstWin, fun h => absurd (hwin ▸ h) Bool.false_ne_true,
          fun h' => absurd (hI.corrB h').1 (by simp only [hend, Bool.false_eq_true,
            not_false_eq_true]), fun t ht hj => ?_⟩
        exfalso
        cases hm : h.minCorrA with
        | none => simp only [hm, Option.elim_none, Option.some.injEq] at ht; omega
        | some t₀ =>
          simp only [hm, Option.elim_some, Option.some.injEq] at ht
          rcases Nat.lt_or_ge t₀ j with h₀ | h₀
          · have := (hI.low t₀ hm h₀).1
            rw [hend] at this
            exact Bool.false_ne_true this
          · omega
    · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend,
        ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [authAux, hend, ↓reduceIte] using hI
  · change y ∈ support ((oracleCorrBSilent _ _ _ _ _ ()).run st) at hy
    simp only [oracleCorrBSilent, StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy with hg
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [authAux, Bool.not_and_self, Bool.and_not_self, Bool.or_false] using hI
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hg
      have hwin : st.win = false := hI.win_false hg.1
      simp only [authAux, hg.1, Bool.not_false, Bool.and_self, Bool.or_true]
      exact ⟨hI.firstWin, fun h => absurd (hwin ▸ h) Bool.false_ne_true,
        fun _ => ⟨rfl, hwin⟩, fun t _ _ => ⟨rfl, hwin⟩⟩
  · obtain ⟨hw, he⟩ := hd q st y hy
    exact hI.of_flags hw he
  · change y ∈ support ((oracleInjectBStop fs (a, e)).run st) at hy
    simp only [oracleInjectBStop, StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy with hg
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [authAux, Bool.not_and_self, Bool.and_not_self, Bool.false_eq_true,
        ↓reduceIte] using hI
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hg
    have hwin : st.win = false := hI.win_false hg.1
    rcases hr : fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
    · simp only [hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [authAux, Bool.not_and_self, Bool.and_not_self, Bool.false_eq_true,
        ↓reduceIte] using hI
    · simp only [hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hy
      subst hy
      cases hc : st.comp i'
      · simp only [authAux, GameState.delete, hwin, Bool.not_false, Bool.or_true,
          Bool.and_self, ↓reduceIte, Option.map_some]
        exact ⟨rfl, fun _ => rfl, fun h' => absurd (hI.corrB h').1 (by
          simp only [hg.1, Bool.false_eq_true, not_false_eq_true]), fun t ht hj => absurd
          (hI.low t ht hj).1 (by simp only [hg.1, Bool.false_eq_true, not_false_eq_true])⟩
      · simp only [authAux, GameState.delete, hwin, Bool.not_true, Bool.or_false,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact hI.of_flags (by simp only [hwin]) (by simp only [hg.1])

/-! ### Injection indices -/

omit [DecidableEq AD] [DecidableEq C] in
/-- Only an injection changes the recorded first win. -/
theorem firstWin_authAux (t : (fsaeadSpec StS StR AD M C).Domain) (ht : ∀ q, t ≠ .inr q)
    (st : GameState StS StR AD M C) (u) (st' : GameState StS StR AD M C) (h : AuthHist) :
    (authAux t st u st' h).firstWin = h.firstWin := by
  rcases t with ((((((n | q) | q) | u) | u) | q) | q)
  all_goals simp only [authAux]
  all_goals first
    | (split_ifs <;> rfl)
    | exact absurd rfl (ht q)

omit [DecidableEq AD] [DecidableEq C] in
/-- An injection keeps the recorded first win or sets it to the index of its answer. -/
theorem firstWin_authAux_inject (q : AD × C) (st : GameState StS StR AD M C) (u : Option (ℕ × M))
    (st' : GameState StS StR AD M C) (h : AuthHist) :
    (authAux (.inr q) st u st' h).firstWin = h.firstWin ∨
      (authAux (.inr q) st u st' h).firstWin = u.map Prod.fst := by
  simp only [authAux]
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

/-- Let `idx e` be the index of every output of `FS-Rcv` on `e`. Then `O-Inject-B^stop` answers an
injection of `e` with the index `idx e`. -/
theorem oracleInjectBStop_index {fs : FSAEADScheme K StS StR AD M C} {idx : C → ℕ}
    (hidx : RcvIndex fs idx) (a : AD) (e : C) (st : GameState StS StR AD M C) :
    ∀ y ∈ support ((oracleInjectBStop fs (a, e)).run st), ∀ r ∈ y.1, r.1 = idx e := by
  intro y hy r hr
  simp only [oracleInjectBStop, StateT.run_bind, StateT.run_get, pure_bind] at hy
  split_ifs at hy
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    cases hr
  rcases hrcv : fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
  · simp only [hrcv, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    cases hr
  · simp only [hrcv, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hy
    subst hy
    cases hr
    exact hidx _ _ _ _ _ _ hrcv

/-- Let `idx e` be the index of every output of `FS-Rcv` on `e`, and let every injection of the
adversary have an index at most `N`. Then every first win that `G_auth^j` records is at an index
at most `N`. -/
theorem firstWin_le_of_injectIndexBound {fs : FSAEADScheme K StS StR AD M C} {idx : C → ℕ}
    (hidx : RcvIndex fs idx) (len : M → ℕ) (b : Bool) (j : ℕ)
    (deliver : QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C))
    {adversary : FSAEADAdversary StS StR AD M C} {N : ℕ}
    (hN : InjectIndexBound idx adversary N) (st : GameState StS StR AD M C) :
    ∀ z ∈ support ((simulateQ (authImpl fs len b j deliver) adversary).run (st, AuthHist.init)),
      ∀ p, z.2.2.firstWin = some p → p ≤ N := by
  set f : GameState StS StR AD M C × AuthHist → ℕ := fun s => if N < s.2.firstWin.getD 0 then 1
    else 0
  have hstep : ∀ t, ¬fsaeadSpec.isInjectAbove idx N t = true → ∀ s,
      ∀ z ∈ support ((authImpl fs len b j deliver t).run s), f z.2 ≤ f s := by
    intro t ht s z hz
    obtain ⟨y, hy, rfl⟩ := QueryImpl.mem_support_extendState_run _ authAux t s.1 s.2 hz
    rcases t with (t | ⟨a, e⟩)
    · simp only [f, firstWin_authAux (.inl t) (fun _ => Sum.inl_ne_inr), le_refl]
    rcases firstWin_authAux_inject (a, e) s.1 y.1 y.2 s.2 with h | h
    · simp only [f, h, le_refl]
    have hle : (y.1.map Prod.fst).getD 0 ≤ N := by
      simp only [fsaeadSpec.isInjectAbove, decide_eq_true_eq, not_lt] at ht
      rcases hy₁ : y.1 with _ | r
      · exact Nat.zero_le _
      · simpa only [Option.map_some, Option.getD_some,
          oracleInjectBStop_index hidx a e s.1 y hy r hy₁] using ht
    simp only [f, h, not_lt.mpr hle, ↓reduceIte, Nat.zero_le]
  intro z hz p hp
  have := IsQueryBoundP.cost_le_of_mem_support_run_simulateQ f
    (fun _ _ s z _ => by simp only [f]; split_ifs <;> omega) hstep hN (st, .init) z hz
  simp only [f, AuthHist.init, Option.getD_none, Nat.not_lt_zero, ↓reduceIte, hp,
    Option.getD_some, add_zero] at this
  split_ifs at this with h
  · omega
  · exact not_lt.mp h

end Stop

section Link

variable [DecidableEq AD] [DecidableEq C]

/-- From a state without `win`, `O-Inject-B` and `O-Inject-B^stop` give every event the same
probability away from `win`. -/
theorem prEvent_oracleInjectB_and_not_win_eq_stop (fs : FSAEADScheme K StS StR AD M C)
    (q : AD × C) (st : GameState StS StR AD M C) (hw : ¬st.win = true)
    (p : Option (ℕ × M) × GameState StS StR AD M C → Prop) :
    Pr{let z ← (oracleInjectB fs q).run st}[p z ∧ ¬z.2.win = true] =
      Pr{let z ← (oracleInjectBStop fs q).run st}[p z ∧ ¬z.2.win = true] := by
  obtain ⟨a, e⟩ := q
  simp only [oracleInjectB, oracleInjectBStop, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hg
  · rfl
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hg
  rcases fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
  · rfl
  cases hc : st.comp i'
  · have h0 (x : Option (ℕ × M) × GameState StS StR AD M C) (hx : x.2.win = true) :
        Pr{let z ← (pure x : ProbComp _)}[p z ∧ ¬z.2.win = true] = 0 := by
      classical
      simp only [prEvent_pure, hx, not_true_eq_false, and_false, ↓reduceIte]
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    rw [h0 _ (by simp only [GameState.delete, hc, Bool.not_false, Bool.or_true]),
      h0 _ (by simp only [GameState.delete, hc, Bool.not_false, Bool.or_true])]
  · obtain ⟨vA₀, vB₀, iA₀, corrA₀, end₀, win₀, trans₀, chall₀, comp₀⟩ := st
    obtain ⟨rfl, -⟩ := hg
    simp only at hc
    simp only [hc, Bool.not_true, Bool.or_false]

/-- Let `deliver` keep `win`. Then from every state, `fs-aead-nd` with `deliver` and the game
with `O-Inject-B^stop` set `win` with the same probability. -/
theorem prEvent_win_eq_injectBStop (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (b : Bool)
    {deliver : QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C)}
    (hd : ∀ q st, ∀ z ∈ support ((deliver q).run st), z.2.win = st.win)
    (adversary : FSAEADAdversary StS StR AD M C) (s₀ : GameState StS StR AD M C) :
    Pr{let z ← ((simulateQ (fsaeadImplWith fs len b deliver (oracleInjectB fs)) adversary).run
        s₀)}[z.2.win = true] =
      Pr{let z ← ((simulateQ (fsaeadImplWith fs len b deliver (oracleInjectBStop fs))
        adversary).run s₀)}[z.2.win = true] := by
  refine prEvent_simulateQ_run_bad_eq _ _ (fun st : GameState StS StR AD M C => st.win = true)
    ?_ (fsaeadImplWith_preservesWin fs len b true (fun q st hw z hz => (hd q st z hz).trans hw)
      (oracleInjectB_preservesWin fs))
    (fsaeadImplWith_preservesWin fs len b true (fun q st hw z hz => (hd q st z hz).trans hw)
      (fun q st hw z hz => (oracleInjectBStop_stepOK fs q st z hz).win_mono hw)) adversary s₀
  intro t st hw q
  rcases t with ((t | q') | q')
  · rfl
  · rfl
  · exact prEvent_oracleInjectB_and_not_win_eq_stop fs q' st hw q

end Link

end FSAEADScheme
