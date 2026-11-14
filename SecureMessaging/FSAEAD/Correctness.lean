/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.FSAEAD.Defs
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# FS-AEAD — Correctness

[ACD19, §4.2.1] builds correctness into the security game of Figure 5: `O-Deliver-B` sets
`win` if B rejects an honest ciphertext or outputs a wrong index or message. The proof of
Theorem 5 removes this `win` in the step from `H1` to `H2`.

`fs.Correct len` is the perfect correctness of `fs`: `O-Deliver-B` never changes `win`
from false to true, in every game state that the oracles reach. A forgery that B
accepts at an index that is not compromised already sets `win` in `O-Inject-B`, so a later
delivery failure does not change the result of the experiment.

The game `fs-aead-nd` ("no delivery check") is the game of Figure 5 with
`O-Deliver-B^nd` (`oracleDeliverBNoWin`) for `O-Deliver-B`. It is a hybrid game for
proofs, not a security notion. `securityExp_eq_noDeliverWin` states that for a correct
scheme, its experiment `securityExpNoDeliverWin` equals `securityExp`.

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — §4.2.1, Figure 5, proof of Theorem 5.
-/

open OracleSpec OracleComp

namespace FSAEADScheme

variable {K StS StR AD M C : Type}

section Correctness

variable [DecidableEq AD] [DecidableEq M] [DecidableEq C]

/-- The game states that the oracles reach from `init fs k`, with challenge bit `b` and length
function `len`. -/
-- ANCHOR: Reachable
inductive Reachable (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (b : Bool) (k : K) :
    GameState StS StR AD M C → Prop
  /-- The initial state is reachable. -/
  | init : Reachable fs len b k (.init fs k)
  /-- Every outcome of an oracle from a reachable state is reachable. -/
  | step {st : GameState StS StR AD M C} (t : (fsaeadSpec StS StR AD M C).Domain) {z}
      (hst : Reachable fs len b k st)
      (hz : z ∈ support ((fsaeadSecurityImpl fs len b t).run st)) :
      Reachable fs len b k z.2
-- ANCHOR_END: Reachable

/-- Perfect correctness of an FS-AEAD scheme [ACD19, §4.2.1]: `O-Deliver-B` never changes
`win` from false to true. In every reachable state with `win = false`, every outcome of
`O-Deliver-B` has `win = false`. -/
-- ANCHOR: Correct
def Correct (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) : Prop :=
  ∀ (b : Bool) (k : K) (st : GameState StS StR AD M C), Reachable fs len b k st →
    st.win = false → ∀ (q : AD × C), ∀ z ∈ support ((oracleDeliverB fs q).run st),
      z.2.win = false
-- ANCHOR_END: Correct

omit [DecidableEq M] in
/-- `O-Deliver-B^nd`, the oracle of `fs-aead-nd`: `O-Deliver-B` without its two assignments
`win ← true`. Everything else is as in `oracleDeliverB`. -/
-- ANCHOR: oracleDeliverBNoWin
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
-- ANCHOR_END: oracleDeliverBNoWin

/-- The oracles of `fs-aead-nd`: `fsaeadSecurityImpl`, with `oracleDeliverBNoWin` for
`O-Deliver-B`. -/
-- ANCHOR: fsaeadNoDeliverWinImpl
def fsaeadNoDeliverWinImpl (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec StS StR AD M C) (GameM StS StR AD M C) :=
  oracleUnif StS StR AD M C
    + oracleTransmitA fs
    + oracleChallA fs len b
    + oracleCorrA StS StR AD M C
    + oracleCorrB StS StR AD M C
    + oracleDeliverBNoWin fs
    + oracleInjectB fs
-- ANCHOR_END: fsaeadNoDeliverWinImpl

/-- The experiment of `fs-aead-nd`: `securityExp` with `fsaeadNoDeliverWinImpl` for
`fsaeadSecurityImpl`. -/
-- ANCHOR: securityExpNoDeliverWin
def securityExpNoDeliverWin [SampleableType K] (fs : FSAEADScheme K StS StR AD M C)
    (len : M → ℕ) (adversary : FSAEADAdversary StS StR AD M C) : ProbComp Bool := do
  let k ← $ᵗ K
  let b ← $ᵗ Bool
  let (b', st) ← (simulateQ (fsaeadNoDeliverWinImpl fs len b) adversary).run (.init fs k)
  return st.win || b == b'
-- ANCHOR_END: securityExpNoDeliverWin

/-- Let `st` be a state with `win = false`, and let every outcome of `O-Deliver-B(q)` from
`st` have `win = false`. Then `O-Deliver-B(q)` and `oracleDeliverBNoWin` agree on `st`. -/
theorem oracleDeliverB_run_eq_noWin_of_win_false (fs : FSAEADScheme K StS StR AD M C)
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
theorem oracleDeliverB_run_eq_noWin_of_win_true (fs : FSAEADScheme K StS StR AD M C)
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

/-- Let `fs` be correct for `len`. Then for every adversary, `securityExp` equals the
experiment of `fs-aead-nd`. -/
-- ANCHOR: securityExp_eq_noDeliverWin
theorem securityExp_eq_noDeliverWin [SampleableType K] (fs : FSAEADScheme K StS StR AD M C)
    (len : M → ℕ) (h : fs.Correct len) (adversary : FSAEADAdversary StS StR AD M C) :
    securityExp fs len adversary = securityExpNoDeliverWin fs len adversary
-- ANCHOR_END: securityExp_eq_noDeliverWin
  := by
  unfold securityExp securityExpNoDeliverWin
  congr 1; funext k; congr 1; funext b
  have hsim := map_run_simulateQ_eq_of_query_map_eq_inv' (fsaeadSecurityImpl fs len b)
    (fsaeadNoDeliverWinImpl fs len b) (Reachable fs len b k) id
    (fun t _ hs _ hy => .step t hs hy) ?_ adversary _ .init
  · simp only [Prod.map_id, id_map, id] at hsim
    rw [hsim]
  · intro t st hst
    simp only [Prod.map_id, id_map, id]
    rcases t with ((((((n | am) | amm) | u) | u) | q) | q)
    all_goals try rfl
    cases hw : st.win
    · exact oracleDeliverB_run_eq_noWin_of_win_false fs q st hw (h b k st hst hw q)
    · exact oracleDeliverB_run_eq_noWin_of_win_true fs q st hw

end Correctness

end FSAEADScheme
