/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.Correctness
public import ToVCVio.ProgramLogic.Relational.IdenticalUntilBad

/-!
# FS-AEAD security — rejecting injections at uncompromised indices

Step 1 of the proof of Theorem 5 of [ACD19]: the advantage in `fs-aead-nd` splits into an
authenticity term and a confidentiality term.

In `fs-aead-nd` only `O-Inject-B` sets `win`: B accepts an injection at an index outside
`comp`. Let `idx c` be the index of every output of `FS-Rcv` on the ciphertext `c`
(`RcvIndex`). The game `G_rej` (`fsaeadRejImpl` with `mon = false`) replaces `O-Inject-B` by
`O-Inject-B^rej`, which returns `⊥` for an injection at an index outside `comp` before it
calls `FS-Rcv`. So `G_rej` never decrypts an injection under a key that the adversary does
not know, and it never sets `win`.

The monitored game `G_rej^mon` (`mon = true`) also sets `win` where `fs-aead-nd` sets it.
With `win` as the bad flag, `fs-aead-nd` and `G_rej^mon` are identical until bad. `G_rej` is
`G_rej^mon` without the monitor. Then (`advantage_noDeliverWin_le`)
```text
|Pr_{fs-aead-nd}[win ∨ b = b'] - 1/2| ≤ Pr_{fs-aead-nd}[win] + |Pr_{G_rej}[b = b'] - 1/2|
```

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

namespace GameState

/-- `record` does not change `win`. -/
@[simp]
theorem record_win (st : GameState StS StR AD M C) (isChall : Bool) (a : AD) (m : M) (e : C) :
    (st.record isChall a m e).win = st.win := by
  unfold record
  split_ifs <;> rfl

/-- `record` does not change `i_A`. -/
@[simp]
theorem record_iA (st : GameState StS StR AD M C) (isChall : Bool) (a : AD) (m : M) (e : C) :
    (st.record isChall a m e).iA = st.iA := by
  unfold record
  split_ifs <;> rfl

/-- `record` does not change B's state. -/
@[simp]
theorem record_vB (st : GameState StS StR AD M C) (isChall : Bool) (a : AD) (m : M) (e : C) :
    (st.record isChall a m e).vB = st.vB := by
  unfold record
  split_ifs <;> rfl

/-- `record` does not change `corrA`. -/
@[simp]
theorem record_corrA (st : GameState StS StR AD M C) (isChall : Bool) (a : AD) (m : M) (e : C) :
    (st.record isChall a m e).corrA = st.corrA := by
  unfold record
  split_ifs <;> rfl

/-- `record` does not change `comp`. -/
@[simp]
theorem record_comp (st : GameState StS StR AD M C) (isChall : Bool) (a : AD) (m : M) (e : C) :
    (st.record isChall a m e).comp = st.comp := by
  unfold record
  split_ifs <;> rfl

/-- `record` does not change `end`. -/
@[simp]
theorem record_end_ (st : GameState StS StR AD M C) (isChall : Bool) (a : AD) (m : M) (e : C) :
    (st.record isChall a m e).end_ = st.end_ := by
  unfold record
  split_ifs <;> rfl

/-- `record` does not change A's state. -/
@[simp]
theorem record_vA (st : GameState StS StR AD M C) (isChall : Bool) (a : AD) (m : M) (e : C) :
    (st.record isChall a m e).vA = st.vA := by
  unfold record
  split_ifs <;> rfl

/-- A record in `trans` after `record` is an old record or the new record at `i_A`. -/
theorem mem_record_trans {st : GameState StS StR AD M C} {isChall : Bool} {a : AD} {m : M}
    {e : C} {r : ℕ × AD × M × C} (hr : r ∈ (st.record isChall a m e).trans) :
    r ∈ st.trans ∨ r = (st.iA, a, m, e) := by
  unfold record at hr
  by_cases hc : (st.corrA && !st.comp st.iA) = true
  · rw [ite_eq_left hc] at hr
    exact .inl hr
  · rw [ite_eq_right hc] at hr
    simpa only [List.mem_append, List.mem_singleton] using hr

/-- `record` keeps every challenge in transit. -/
theorem mem_record_chall {st : GameState StS StR AD M C} {isChall : Bool} {a : AD} {m : M}
    {e : C} {i : ℕ} (hi : i ∈ st.chall) : i ∈ (st.record isChall a m e).chall := by
  unfold record
  by_cases hc : (st.corrA && !st.comp st.iA) = true
  · rw [ite_eq_left hc]
    exact hi
  · rw [ite_eq_right hc]
    cases isChall <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_insert, hi, or_true]

/-- Before a corruption of A, `record` of a challenge puts `i_A` in `chall`. -/
theorem iA_mem_record_chall {st : GameState StS StR AD M C} (hc : st.corrA = false) (a : AD)
    (m : M) (e : C) : st.iA ∈ (st.record true a m e).chall := by
  unfold record
  rw [ite_eq_right (by simp only [hc, Bool.false_and, Bool.false_eq_true, not_false_eq_true])]
  exact Finset.mem_insert_self _ _

/-- The challenges in transit after `record` are the old ones and possibly `i_A`. -/
theorem mem_chall_of_mem_record {st : GameState StS StR AD M C} {isChall : Bool} {a : AD}
    {m : M} {e : C} {i : ℕ} (hi : i ∈ (st.record isChall a m e).chall) :
    i ∈ st.chall ∨ i = st.iA := by
  unfold record at hi
  by_cases hc : (st.corrA && !st.comp st.iA) = true
  · rw [ite_eq_left hc] at hi
    exact .inl hi
  · rw [ite_eq_right hc] at hi
    cases isChall
    · exact .inl hi
    · simpa only [↓reduceIte, Finset.mem_insert, or_comm] using hi

/-- The state with `win = false`. -/
@[simps]
def clearWin (st : GameState StS StR AD M C) : GameState StS StR AD M C := { st with win := false }

/-- `record` does not read `win`. -/
theorem clearWin_record (st : GameState StS StR AD M C) (isChall : Bool) (a : AD) (m : M)
    (e : C) : (st.record isChall a m e).clearWin = st.clearWin.record isChall a m e := by
  unfold record clearWin
  split_ifs <;> rfl

end GameState

/-! ### Runs of the games -/

/-- A run of the security game with the oracles `impl b`: sample `k` and `b`, run the
adversary from the initial state for `k`, and return `b`, the guess `b'` and the final
state. -/
def gameRun [SampleableType K] (fs : FSAEADScheme K StS StR AD M C)
    (impl : Bool → QueryImpl (fsaeadSpec StS StR AD M C) (GameM StS StR AD M C))
    (adversary : FSAEADAdversary StS StR AD M C) :
    ProbComp (Bool × Bool × GameState StS StR AD M C) := do
  let k ← $ᵗ K
  let b ← $ᵗ Bool
  (b, ·) <$> (simulateQ (impl b) adversary).run (.init fs k)

/-- Let the two games give, for every `k` and `b`, the same probability to the events `p b` and
`q b` of the adversary's run. Then their runs give the same probability to `p` and `q`. -/
theorem prEvent_gameRun_congr [SampleableType K] (fs : FSAEADScheme K StS StR AD M C)
    (impl₁ impl₂ : Bool → QueryImpl (fsaeadSpec StS StR AD M C) (GameM StS StR AD M C))
    (adversary : FSAEADAdversary StS StR AD M C)
    (p q : Bool → Bool × GameState StS StR AD M C → Prop)
    (h : ∀ k b, Pr{let z ← (simulateQ (impl₁ b) adversary).run (.init fs k)}[p b z] =
      Pr{let z ← (simulateQ (impl₂ b) adversary).run (.init fs k)}[q b z]) :
    Pr{let r ← gameRun fs impl₁ adversary}[p r.1 r.2] =
      Pr{let r ← gameRun fs impl₂ adversary}[q r.1 r.2] := by
  unfold gameRun
  refine prEvent_bind_congr _ _ _ _ _ fun k => prEvent_bind_congr _ _ _ _ _ fun b => ?_
  rw [prEvent_map, prEvent_map]
  exact h k b

/-- Let `deliver` and `inject` keep `win = w`. Then the oracles of the game keep `win = w`. -/
theorem fsaeadImplWith_preservesWin (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ)
    (b w : Bool) {deliver : QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C)}
    {inject : QueryImpl (AD × C →ₒ Option (ℕ × M)) (GameM StS StR AD M C)}
    (hd : QueryImpl.PreservesInv deliver fun st => st.win = w)
    (hi : QueryImpl.PreservesInv inject fun st => st.win = w) :
    QueryImpl.PreservesInv (fsaeadImplWith fs len b deliver inject) fun st => st.win = w := by
  intro t st hw z hz
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | q) | q)
  · change z ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hz
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hz
    obtain ⟨x, rfl⟩ := hz
    exact hw
  · change z ∈ support ((oracleTransmitA fs (a, m)).run st) at hz
    simp only [oracleTransmitA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz <;>
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_set, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz <;>
      subst hz <;>
      simp only [GameState.record_win, hw]
  · change z ∈ support ((oracleChallA fs len b (a, m₀, m₁)).run st) at hz
    simp only [oracleChallA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz <;>
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_set, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz <;>
      subst hz <;>
      simp only [GameState.record_win, hw]
  · change z ∈ support ((oracleCorrA _ _ _ _ _ ()).run st) at hz
    simp only [oracleCorrA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz <;>
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_set, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz <;>
      subst hz <;>
      exact hw
  · change z ∈ support ((oracleCorrB _ _ _ _ _ ()).run st) at hz
    simp only [oracleCorrB, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz <;>
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_set, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz <;>
      subst hz <;>
      exact hw
  · exact hd q st hw z hz
  · exact hi q st hw z hz

section Reject

variable [DecidableEq AD] [DecidableEq C]

/-- `idx c` is the index of every output of `FS-Rcv` on the ciphertext `c`. -/
def RcvIndex (fs : FSAEADScheme K StS StR AD M C) (idx : C → ℕ) : Prop :=
  ∀ vB a c vB' i m, fs.rcv vB a c = some (vB', i, m) → i = idx c

/-- **O-Inject-B^rej(a, e)**. `O-Inject-B`, but an injection at an index outside `comp` is
rejected before `FS-Rcv` runs. With `mon`, the oracle sets `win` if `FS-Rcv` accepts such an
injection, as `O-Inject-B` does.
```text
O-Inject-B^rej(a, e):
  req ¬(∃ i, m: (i, a, m, e) ∈ trans)
  if idx(e) ∉ comp:
    if mon and FS-Rcv(v_B, a, e) ≠ ⊥: win ← true
    return ⊥
  r ← FS-Rcv(v_B, a, e)
  req r ≠ ⊥
  (v_B, i', m') ← r
  delete(i')
  return (i', m')
``` -/
def oracleInjectBRej (fs : FSAEADScheme K StS StR AD M C) (idx : C → ℕ) (mon : Bool) :
    QueryImpl (AD × C →ₒ Option (ℕ × M)) (GameM StS StR AD M C) :=
  fun (a, e) => do
    let st ← get
    if st.end_ || (st.findTrans a e).isSome then return none
    if !st.comp (idx e) then
      if mon && (fs.rcv st.vB a e).isSome then set { st with win := true }
      return none
    let some (vB, i', m') := fs.rcv st.vB a e | return none
    set ({ st with vB }.delete i')
    return some (i', m')

/-- The oracles of `G_rej` (`mon = false`) and of `G_rej^mon` (`mon = true`): `fs-aead-nd` with
`O-Inject-B^rej` for `O-Inject-B`. -/
def fsaeadRejImpl (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (idx : C → ℕ)
    (mon b : Bool) : QueryImpl (fsaeadSpec StS StR AD M C) (GameM StS StR AD M C) :=
  fsaeadImplWith fs len b (oracleDeliverBNoWin fs) (oracleInjectBRej fs idx mon)

/-- The experiment of `G_rej`: it returns `b = b'`. -/
def securityExpRej [SampleableType K] (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ)
    (idx : C → ℕ) (adversary : FSAEADAdversary StS StR AD M C) : ProbComp Bool :=
  (fun r => r.1 == r.2.1) <$> gameRun fs (fsaeadRejImpl fs len idx false) adversary

/-- The authenticity experiment: it runs `fs-aead-nd` and returns `win`. -/
def winExp [SampleableType K] (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ)
    (adversary : FSAEADAdversary StS StR AD M C) : ProbComp Bool :=
  (fun r => r.2.2.win) <$> gameRun fs (fsaeadNoDeliverWinImpl fs len) adversary

/-! ### Runs of `fs-aead-nd` -/

/-- The experiment of `fs-aead-nd` returns `win ∨ b = b'` of its run. -/
theorem securityExpNoDeliverWin_eq_map_gameRun [SampleableType K]
    (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ)
    (adversary : FSAEADAdversary StS StR AD M C) :
    securityExpNoDeliverWin fs len adversary =
      (fun r => r.2.2.win || r.1 == r.2.1) <$>
        gameRun fs (fsaeadNoDeliverWinImpl fs len) adversary := by
  simp only [securityExpNoDeliverWin, gameRun, map_bind, Functor.map_map, bind_pure_comp]

/-! ### The oracles keep `win` -/

/-- `O-Deliver-B^nd` keeps `win`. -/
theorem oracleDeliverBNoWin_win (fs : FSAEADScheme K StS StR AD M C) (q : AD × C)
    (st : GameState StS StR AD M C) :
    ∀ z ∈ support ((oracleDeliverBNoWin fs q).run st), z.2.win = st.win := by
  intro z hz
  obtain ⟨a, e⟩ := q
  simp only [oracleDeliverBNoWin, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
  · simp only [hf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  rcases hr : fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
  · simp only [hf, hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  · simp only [hf, hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl

/-- `O-Inject-B` keeps `win = true`. -/
theorem oracleInjectB_preservesWin (fs : FSAEADScheme K StS StR AD M C) :
    QueryImpl.PreservesInv (oracleInjectB fs) fun st => st.win = true := by
  rintro ⟨a, e⟩ st hw z hz
  simp only [oracleInjectB, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  rcases hr : fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
  · simp only [hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  · simp only [hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp only [GameState.delete, hw, Bool.true_or]

/-- `O-Inject-B^rej` keeps `win = true`. -/
theorem oracleInjectBRej_preservesWin (fs : FSAEADScheme K StS StR AD M C) (idx : C → ℕ)
    (mon : Bool) :
    QueryImpl.PreservesInv (oracleInjectBRej fs idx mon) fun st => st.win = true := by
  rintro ⟨a, e⟩ st hw z hz
  simp only [oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    rfl
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  rcases hr : fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
  · simp only [hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  · simp only [hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw

/-- `O-Inject-B^rej` without the monitor keeps `win`. -/
theorem oracleInjectBRej_false_win (fs : FSAEADScheme K StS StR AD M C) (idx : C → ℕ)
    (q : AD × C) (st : GameState StS StR AD M C) :
    ∀ z ∈ support ((oracleInjectBRej fs idx false q).run st), z.2.win = st.win := by
  obtain ⟨a, e⟩ := q
  intro z hz
  simp only [oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte] at hz
  split_ifs at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  rcases hr : fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
  · simp only [hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  · simp only [hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl

/-! ### `fs-aead-nd` and `G_rej^mon` are identical until `win` -/

/-- `O-Inject-B` and the monitored `O-Inject-B^rej` give every event the same probability away
from `win`. -/
theorem prEvent_oracleInjectB_and_not_win_eq {fs : FSAEADScheme K StS StR AD M C}
    {idx : C → ℕ} (hidx : RcvIndex fs idx) (q : AD × C) (st : GameState StS StR AD M C)
    (p : Option (ℕ × M) × GameState StS StR AD M C → Prop) :
    Pr{let z ← (oracleInjectB fs q).run st}[p z ∧ ¬z.2.win = true] =
      Pr{let z ← (oracleInjectBRej fs idx true q).run st}[p z ∧ ¬z.2.win = true] := by
  obtain ⟨a, e⟩ := q
  rcases hr : fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
  · simp only [oracleInjectB, oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind, hr,
      Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> rfl
  obtain rfl := hidx _ _ _ _ _ _ hr
  cases hc : st.comp (idx e)
  · simp only [oracleInjectB, oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind, hr,
      hc, Bool.not_false, Bool.or_true, Option.isSome_some, Bool.and_self, ↓reduceIte]
    split_ifs
    · rfl
    · have h0 (x : Option (ℕ × M) × GameState StS StR AD M C) (hx : x.2.win = true) :
          Pr{let z ← (pure x : ProbComp _)}[p z ∧ ¬z.2.win = true] = 0 :=
        by
          classical
          simp only [prEvent_pure, hx, not_true_eq_false, and_false, ↓reduceIte]
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      rw [h0 _ rfl, h0 _ rfl]
  · simp only [oracleInjectB, oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind, hr,
      hc, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]

/-- Let `RcvIndex fs idx` hold. Then for every key `k` and bit `b`, `fs-aead-nd` and
`G_rej^mon` give every event of the adversary's run the same probability away from `win`. -/
theorem prEvent_noDeliverWin_and_not_win_eq {fs : FSAEADScheme K StS StR AD M C}
    {idx : C → ℕ} (hidx : RcvIndex fs idx) (len : M → ℕ) (b : Bool) (k : K)
    (adversary : FSAEADAdversary StS StR AD M C) (p : Bool × GameState StS StR AD M C → Prop) :
    Pr{let z ← ((simulateQ (fsaeadNoDeliverWinImpl fs len b) adversary).run
        (.init fs k))}[p z ∧ ¬z.2.win = true] =
      Pr{let z ← ((simulateQ (fsaeadRejImpl fs len idx true b) adversary).run
        (.init fs k))}[p z ∧ ¬z.2.win = true] := by
  refine prEvent_simulateQ_run_and_not_bad_eq _ _
    (fun st : GameState StS StR AD M C => st.win = true) ?_
    (fun t => fsaeadImplWith_preservesWin fs len b true
      (fun q st hw z hz => (oracleDeliverBNoWin_win fs q st z hz).trans hw)
      (oracleInjectB_preservesWin fs) t)
    (fun t => fsaeadImplWith_preservesWin fs len b true
      (fun q st hw z hz => (oracleDeliverBNoWin_win fs q st z hz).trans hw)
      (oracleInjectBRej_preservesWin fs idx true) t) adversary _ p
  intro t st _ q
  rcases t with ((((((n | am) | amm) | u) | u) | q') | q')
  all_goals try rfl
  exact prEvent_oracleInjectB_and_not_win_eq hidx q' st q

/-- Let `RcvIndex fs idx` hold. Then for every key `k` and bit `b`, `fs-aead-nd` and
`G_rej^mon` set `win` with the same probability. -/
theorem prEvent_noDeliverWin_win_eq {fs : FSAEADScheme K StS StR AD M C}
    {idx : C → ℕ} (hidx : RcvIndex fs idx) (len : M → ℕ) (b : Bool) (k : K)
    (adversary : FSAEADAdversary StS StR AD M C) :
    Pr{let z ← ((simulateQ (fsaeadNoDeliverWinImpl fs len b) adversary).run
        (.init fs k))}[z.2.win = true] =
      Pr{let z ← ((simulateQ (fsaeadRejImpl fs len idx true b) adversary).run
        (.init fs k))}[z.2.win = true] := by
  have h := prEvent_noDeliverWin_and_not_win_eq hidx len b k adversary fun _ => True
  simp only [true_and, prEvent_not_eq_one_sub] at h
  rw [← ENNReal.sub_sub_cancel ENNReal.one_ne_top (prEvent_le_one _), h,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (prEvent_le_one _)]

/-! ### Removing the monitor -/

open GameState (clearWin clearWin_record clearWin_end_ clearWin_corrA clearWin_chall
  clearWin_comp clearWin_vB clearWin_vA clearWin_iA)

/-- `G_rej` on `clearWin st` is `G_rej^mon` on `st` with `clearWin` on the final state: no
oracle of `G_rej^mon` reads `win`. -/
theorem fsaeadRejImpl_run_clearWin (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ)
    (idx : C → ℕ) (b : Bool) (t : (fsaeadSpec StS StR AD M C).Domain)
    (st : GameState StS StR AD M C) :
    Prod.map id clearWin <$> (fsaeadRejImpl fs len idx true b t).run st =
      (fsaeadRejImpl fs len idx false b t).run (clearWin st) := by
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, e⟩) | ⟨a, e⟩)
  · change Prod.map id clearWin <$> (oracleUnif _ _ _ _ _ n).run st =
      (oracleUnif _ _ _ _ _ n).run (clearWin st)
    simp only [oracleUnif, ToVCVio.unifLiftStateT, ToVCVio.liftTarget_unif_run, Functor.map_map,
      Prod.map_apply, id_eq]
  · change Prod.map id clearWin <$> (oracleTransmitA fs (a, m)).run st =
      (oracleTransmitA fs (a, m)).run (clearWin st)
    simp only [oracleTransmitA, StateT.run_bind, StateT.run_get, pure_bind, clearWin_end_,
      clearWin_corrA, clearWin_chall, clearWin_vA, clearWin_iA]
    split_ifs <;> simp only [StateT.run_pure, StateT.run_bind, StateT.run_set, pure_bind,
      map_pure, Prod.map_apply, id_eq, clearWin_record]
    all_goals rfl
  · change Prod.map id clearWin <$> (oracleChallA fs len b (a, m₀, m₁)).run st =
      (oracleChallA fs len b (a, m₀, m₁)).run (clearWin st)
    simp only [oracleChallA, StateT.run_bind, StateT.run_get, pure_bind, clearWin_end_,
      clearWin_corrA, clearWin_chall, clearWin_vA, clearWin_iA]
    split_ifs <;> simp only [StateT.run_pure, StateT.run_bind, StateT.run_set, pure_bind,
      map_pure, Prod.map_apply, id_eq, clearWin_record]
    all_goals rfl
  · change Prod.map id clearWin <$> (oracleCorrA _ _ _ _ _ ()).run st =
      (oracleCorrA _ _ _ _ _ ()).run (clearWin st)
    simp only [oracleCorrA, StateT.run_bind, StateT.run_get, pure_bind, clearWin_end_,
      clearWin_corrA, clearWin_chall, clearWin_vA, clearWin_iA]
    split_ifs <;> simp only [StateT.run_pure, StateT.run_bind, StateT.run_set, pure_bind,
      map_pure, Prod.map_apply, id_eq]
    all_goals rfl
  · change Prod.map id clearWin <$> (oracleCorrB _ _ _ _ _ ()).run st =
      (oracleCorrB _ _ _ _ _ ()).run (clearWin st)
    simp only [oracleCorrB, StateT.run_bind, StateT.run_get, pure_bind, clearWin_end_,
      clearWin_corrA, clearWin_chall, clearWin_vA, clearWin_iA]
    split_ifs <;> simp only [StateT.run_pure, StateT.run_bind, StateT.run_set, pure_bind,
      map_pure, Prod.map_apply, id_eq]
    all_goals rfl
  · change Prod.map id clearWin <$> (oracleDeliverBNoWin fs (a, e)).run st =
      (oracleDeliverBNoWin fs (a, e)).run (clearWin st)
    simp only [oracleDeliverBNoWin, StateT.run_bind, StateT.run_get, pure_bind, clearWin_end_,
      clearWin_vB]
    have hf : (clearWin st).findTrans a e = st.findTrans a e := rfl
    split_ifs
    · rfl
    rw [hf]
    rcases st.findTrans a e with _ | ⟨i, a', m, e'⟩
    · rfl
    rcases fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
    · rfl
    · rfl
  · change Prod.map id clearWin <$> (oracleInjectBRej fs idx true (a, e)).run st =
      (oracleInjectBRej fs idx false (a, e)).run (clearWin st)
    simp only [oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, clearWin_end_, clearWin_comp, clearWin_vB]
    have hf : (clearWin st).findTrans a e = st.findTrans a e := rfl
    rw [hf]
    split_ifs
    · rfl
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
        Prod.map_apply, id_eq]
      rfl
    · rfl
    rcases fs.rcv st.vB a e with _ | ⟨vB, i', m'⟩
    · rfl
    · rfl

/-- `G_rej^mon` and `G_rej` return the same guess with the same probability. -/
theorem prEvent_fsaeadRejImpl_mon_eq (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ)
    (idx : C → ℕ) (b : Bool) (k : K) (adversary : FSAEADAdversary StS StR AD M C)
    (p : Bool → Prop) :
    Pr{let z ← (simulateQ (fsaeadRejImpl fs len idx true b) adversary).run (.init fs k)}[p z.1] =
      Pr{let z ← ((simulateQ (fsaeadRejImpl fs len idx false b) adversary).run
        (.init fs k))}[p z.1] := by
  have h := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ clearWin
    (fsaeadRejImpl_run_clearWin fs len idx b) adversary (.init fs k)
  have hinit : clearWin (GameState.init fs k) = .init fs k := rfl
  rw [hinit] at h
  rw [← h, prEvent_map]
  rfl

/-! ### The split -/

/-- **Step 1.** Let `idx c` be the index of every output of `FS-Rcv` on `c`. Then
```text
|Pr_{fs-aead-nd}[win ∨ b = b'] - 1/2| ≤ Pr_{fs-aead-nd}[win] + |Pr_{G_rej}[b = b'] - 1/2|
``` -/
theorem advantage_noDeliverWin_le [SampleableType K] {fs : FSAEADScheme K StS StR AD M C}
    {idx : C → ℕ} (hidx : RcvIndex fs idx) (len : M → ℕ)
    (adversary : FSAEADAdversary StS StR AD M C) :
    |(Pr{let x ← securityExpNoDeliverWin fs len adversary}[x = true]).toReal - 1 / 2| ≤
      (Pr{let x ← winExp fs len adversary}[x = true]).toReal +
        |(Pr{let x ← securityExpRej fs len idx adversary}[x = true]).toReal - 1 / 2| := by
  set P := gameRun fs (fsaeadNoDeliverWinImpl fs len) adversary
  set R := gameRun fs (fsaeadRejImpl fs len idx true) adversary
  -- `a = w + x` in `fs-aead-nd`
  have ha : Pr{let x ← securityExpNoDeliverWin fs len adversary}[x = true] =
      Pr{let r ← P}[r.2.2.win = true] +
        Pr{let r ← R}[(r.1 == r.2.1) = true ∧ ¬r.2.2.win = true] := by
    rw [securityExpNoDeliverWin_eq_map_gameRun, prEvent_map,
      prEvent_eq_prEvent_and_add_prEvent_and_not P _ fun r => r.2.2.win = true]
    congr 1
    · exact prEvent_congr P _ _ fun r => by
        simp only [Bool.or_eq_true, and_iff_right_iff_imp]
        tauto
    · rw [prEvent_congr P _ (fun r => (r.1 == r.2.1) = true ∧ ¬r.2.2.win = true)
        fun r => by simp only [Bool.or_eq_true]; tauto]
      exact prEvent_gameRun_congr fs _ _ adversary
        (fun b z => (b == z.1) = true ∧ ¬z.2.win = true)
        (fun b z => (b == z.1) = true ∧ ¬z.2.win = true) fun k b =>
          prEvent_noDeliverWin_and_not_win_eq hidx len b k adversary fun z => (b == z.1) = true
  -- `r = y + x` in `G_rej^mon`, with `y ≤ w`
  have hr : Pr{let x ← securityExpRej fs len idx adversary}[x = true] =
      Pr{let r ← R}[(r.1 == r.2.1) = true ∧ r.2.2.win = true] +
        Pr{let r ← R}[(r.1 == r.2.1) = true ∧ ¬r.2.2.win = true] := by
    rw [securityExpRej, prEvent_map, ← prEvent_eq_prEvent_and_add_prEvent_and_not]
    exact (prEvent_gameRun_congr fs _ _ adversary (fun b z => (b == z.1) = true)
      (fun b z => (b == z.1) = true) fun k b =>
        prEvent_fsaeadRejImpl_mon_eq fs len idx b k adversary fun b' => (b == b') = true).symm
  have hy : Pr{let r ← R}[(r.1 == r.2.1) = true ∧ r.2.2.win = true] ≤
      Pr{let x ← winExp fs len adversary}[x = true] := by
    rw [winExp, prEvent_map]
    calc _ ≤ Pr{let r ← R}[r.2.2.win = true] := prEvent_mono R _ _ fun r h => h.2
      _ = _ := (prEvent_gameRun_congr fs _ _ adversary (fun _ z => z.2.win = true)
          (fun _ z => z.2.win = true) fun k b =>
            prEvent_noDeliverWin_win_eq hidx len b k adversary).symm
  have hw' : Pr{let r ← P}[r.2.2.win = true] = Pr{let x ← winExp fs len adversary}[x = true] := by
    rw [winExp, prEvent_map]
  rw [hw'] at ha
  set w := Pr{let x ← winExp fs len adversary}[x = true]
  set x := Pr{let r ← R}[(r.1 == r.2.1) = true ∧ ¬r.2.2.win = true]
  set y := Pr{let r ← R}[(r.1 == r.2.1) = true ∧ r.2.2.win = true]
  have hwt : w ≠ ⊤ := prEvent_ne_top _
  have hxt : x ≠ ⊤ := prEvent_ne_top _
  have hyt : y ≠ ⊤ := prEvent_ne_top _
  rw [ha, hr, ENNReal.toReal_add hwt hxt, ENNReal.toReal_add hyt hxt]
  have hyw : y.toReal ≤ w.toReal := ENNReal.toReal_mono hwt hy
  have hy0 : 0 ≤ y.toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor
  · nlinarith [neg_abs_le (y.toReal + x.toReal - 1 / 2), ENNReal.toReal_nonneg (a := w)]
  · nlinarith [le_abs_self (y.toReal + x.toReal - 1 / 2)]

end Reject

end FSAEADScheme
