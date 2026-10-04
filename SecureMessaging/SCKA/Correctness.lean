/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs
import ToVCVio.OracleComp.ExpectedPayoff
import ToVCVio.OracleComp.SimSemantics.StateT.ExpectedPayoffBound
import ToVCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# The SCKA correctness game: oracle steps and the potential method

Let `scka : SCKAScheme ProbComp IK StA StB I Rho Rand` be an SCKA scheme with initial keys
in `IK`, party states in `StA` and `StB`, epoch keys in `I`, and messages in `Rho`.
Its correctness game lets an adversary schedule sends and deliveries of recorded messages.
`correctnessExp scka adv` returns the final correctness flag; `false` denotes an error.

The update, execution and support lemmas describe individual oracle steps.
`sckaCorrectnessImpl_preservesInv` combines preservation by the four protocol oracles.

For an invariant family `Inv ik`, a potential `V : GameState StA StB I Rho → ℝ≥0∞`, and
`ε : ℝ≥0∞`, `correctness_error_le_of_potential` gives

```
1 - Pr[correctnessExp scka adv = true] ≤ q · ε
```

for every adversary with at most `q` send queries across both parties. Its hypotheses require
invariant initialization with zero potential, invariant preservation, potential at least `1`
when the flag is false, and expected increases of at most `ε` on sends and `0` on other queries.
-/

open OracleSpec OracleComp ENNReal

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type}

/-! ### Game-state updates of the oracles -/

/-- Whether every epoch from `1` to `n` has a key. -/
def knownPrefix (key : ℕ → Option I) (n : ℕ) : Bool :=
  (List.range (n + 1)).all fun t => t = 0 || (key t).isSome

/-- A's send successor: record the message and optional key, set `tcurA` to the send report `tsnd`,
and update the correctness flag. -/
def sendAUpdate [DecidableEq I] (s : GameState StA StB I Rho) (keyOpt : Option (ℕ × I))
    (ρ : Rho) (tsnd : ℕ) (stA' : StA) : GameState StA StB I Rho :=
  let msgA' := Function.update s.msgA (s.nA + 1) (some (ρ, tsnd))
  match keyOpt with
  | none =>
      { s with
        stA := stA', tcurA := tsnd, msgA := msgA', nA := s.nA + 1,
        correct := s.correct && decide (s.tcurA ≤ tsnd) && knownPrefix s.keyA tsnd }
  | some (tI, key) =>
      let keyA' := Function.update s.keyA tI (some key)
      { s with
        stA := stA', tcurA := tsnd, keyA := keyA', msgA := msgA', nA := s.nA + 1,
        correct := s.correct && decide (s.tcurA ≤ tsnd) && (s.keyA tI).isNone &&
          ((s.keyB tI).isNone || s.keyB tI == some key) && knownPrefix keyA' tsnd }

/-- The version of `sendAUpdate` for B. -/
def sendBUpdate [DecidableEq I] (s : GameState StA StB I Rho) (keyOpt : Option (ℕ × I))
    (ρ : Rho) (tsnd : ℕ) (stB' : StB) : GameState StA StB I Rho :=
  let msgB' := Function.update s.msgB (s.nB + 1) (some (ρ, tsnd))
  match keyOpt with
  | none =>
      { s with
        stB := stB', tcurB := tsnd, msgB := msgB', nB := s.nB + 1,
        correct := s.correct && decide (s.tcurB ≤ tsnd) && knownPrefix s.keyB tsnd }
  | some (tI, key) =>
      let keyB' := Function.update s.keyB tI (some key)
      { s with
        stB := stB', tcurB := tsnd, keyB := keyB', msgB := msgB', nB := s.nB + 1,
        correct := s.correct && decide (s.tcurB ≤ tsnd) && (s.keyB tI).isNone &&
          ((s.keyA tI).isNone || s.keyA tI == some key) && knownPrefix keyB' tsnd }

/-- A's receive successor: record the optional key, set `tcurA` to `max tcurA trcv`, and update the
correctness flag using the stored send report `tsnd`. -/
def recvAUpdate [DecidableEq I] (s : GameState StA StB I Rho) (tsnd : ℕ)
    (keyOpt : Option (ℕ × I)) (trcv : ℕ) (stA' : StA) : GameState StA StB I Rho :=
  let tcurA' := max s.tcurA trcv
  match keyOpt with
  | none =>
      { s with
        stA := stA', tcurA := tcurA',
        correct := s.correct && (trcv == tsnd) && knownPrefix s.keyA tcurA' }
  | some (tI, key) =>
      let keyA' := Function.update s.keyA tI (some key)
      { s with
        stA := stA', tcurA := tcurA', keyA := keyA',
        correct := s.correct && (trcv == tsnd) && (s.keyA tI).isNone &&
          ((s.keyB tI).isNone || s.keyB tI == some key) && knownPrefix keyA' tcurA' }

/-- The version of `recvAUpdate` for B. -/
def recvBUpdate [DecidableEq I] (s : GameState StA StB I Rho) (tsnd : ℕ)
    (keyOpt : Option (ℕ × I)) (trcv : ℕ) (stB' : StB) : GameState StA StB I Rho :=
  let tcurB' := max s.tcurB trcv
  match keyOpt with
  | none =>
      { s with
        stB := stB', tcurB := tcurB',
        correct := s.correct && (trcv == tsnd) && knownPrefix s.keyB tcurB' }
  | some (tI, key) =>
      let keyB' := Function.update s.keyB tI (some key)
      { s with
        stB := stB', tcurB := tcurB', keyB := keyB',
        correct := s.correct && (trcv == tsnd) && (s.keyB tI).isNone &&
          ((s.keyA tI).isNone || s.keyA tI == some key) && knownPrefix keyB' tcurB' }

variable (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)

/-! ### Outcomes of the oracles -/

section Oracles

variable [DecidableEq I]

/-- A `SendA` query runs `sendA` on A's state and maps its result: a refusal leaves the game state
unchanged and returns `none`; a result `(keyOpt, ρ, tsnd, stA')` returns
`(tsnd, keyOpt.map Prod.fst, ρ)` and writes `sendAUpdate`. -/
theorem oracleSendA_run_eq :
    (oracleSendA scka ()).run s =
      (fun out => match out with
        | none => (none, s)
        | some (keyOpt, ρ, tsnd, stA') =>
            (some (tsnd, keyOpt.map Prod.fst, ρ), sendAUpdate s keyOpt ρ tsnd stA')) <$>
        scka.sendA s.stA := by
  simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
    monadLift_self, bind_assoc, map_eq_bind_pure_comp]
  refine bind_congr fun out => ?_
  rcases out with _ | ⟨_ | ⟨tI, key⟩, ρ, tsnd, stA'⟩ <;>
    simp [sendAUpdate, knownPrefix, StateT.run_set, StateT.run_pure]

/-- The version of `oracleSendA_run_eq` for B. -/
theorem oracleSendB_run_eq :
    (oracleSendB scka ()).run s =
      (fun out => match out with
        | none => (none, s)
        | some (keyOpt, ρ, tsnd, stB') =>
            (some (tsnd, keyOpt.map Prod.fst, ρ), sendBUpdate s keyOpt ρ tsnd stB')) <$>
        scka.sendB s.stB := by
  simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
    monadLift_self, bind_assoc, map_eq_bind_pure_comp]
  refine bind_congr fun out => ?_
  rcases out with _ | ⟨_ | ⟨tI, key⟩, ρ, tsnd, stB'⟩ <;>
    simp [sendBUpdate, knownPrefix, StateT.run_set, StateT.run_pure]

/-- A send-query outcome is obtained from a supported `sendA` result: refusal gives `(none, s)`, and
acceptance gives the response paired with `sendAUpdate`. -/
theorem mem_support_oracleSendA_run_iff
    (z : Option (ℕ × Option ℕ × Rho) × GameState StA StB I Rho) :
    z ∈ support ((oracleSendA scka ()).run s) ↔
      ∃ out ∈ support (scka.sendA s.stA),
        z = match out with
          | none => (none, s)
          | some (keyOpt, ρ, tsnd, stA') =>
              (some (tsnd, keyOpt.map Prod.fst, ρ), sendAUpdate s keyOpt ρ tsnd stA') := by
  rw [oracleSendA_run_eq, support_map, Set.mem_image]
  exact exists_congr fun out => and_congr_right fun _ => eq_comm

/-- The version of `mem_support_oracleSendA_run_iff` for B. -/
theorem mem_support_oracleSendB_run_iff
    (z : Option (ℕ × Option ℕ × Rho) × GameState StA StB I Rho) :
    z ∈ support ((oracleSendB scka ()).run s) ↔
      ∃ out ∈ support (scka.sendB s.stB),
        z = match out with
          | none => (none, s)
          | some (keyOpt, ρ, tsnd, stB') =>
              (some (tsnd, keyOpt.map Prod.fst, ρ), sendBUpdate s keyOpt ρ tsnd stB') := by
  rw [oracleSendB_run_eq, support_map, Set.mem_image]
  exact exists_congr fun out => and_congr_right fun _ => eq_comm

/-- A `RecvA n` query with no recorded message `n` from B returns `none` and leaves the state
unchanged. -/
theorem oracleRecvA_run_eq_of_none {n : ℕ} (h : s.msgB n = none) :
    (oracleRecvA scka n).run s = pure (none, s) := by
  simp [oracleRecvA, StateT.run_bind, StateT.run_get, h]

/-- A `RecvA n` query whose delivery `recvA` refuses returns `none` and clears the correctness
flag. -/
theorem oracleRecvA_run_eq_of_refuse {n tsnd : ℕ} {ρ : Rho} (h : s.msgB n = some (ρ, tsnd))
    (hr : scka.recvA s.stA ρ = none) :
    (oracleRecvA scka n).run s = pure (none, { s with correct := false }) := by
  simp [oracleRecvA, StateT.run_bind, StateT.run_get, StateT.run_set, h, hr]

/-- A `RecvA n` query whose delivery `recvA` accepts with `(keyOpt, trcv, stA')` returns
`(trcv, keyOpt.map Prod.fst)` and writes `recvAUpdate`. -/
theorem oracleRecvA_run_eq_of_accept {n tsnd trcv : ℕ} {ρ : Rho} {keyOpt : Option (ℕ × I)}
    {stA' : StA} (h : s.msgB n = some (ρ, tsnd))
    (hr : scka.recvA s.stA ρ = some (keyOpt, trcv, stA')) :
    (oracleRecvA scka n).run s =
      pure (some (trcv, keyOpt.map Prod.fst), recvAUpdate s tsnd keyOpt trcv stA') := by
  rcases keyOpt with _ | ⟨tI, key⟩ <;>
    simp [oracleRecvA, recvAUpdate, knownPrefix, StateT.run_bind, StateT.run_get, StateT.run_set,
      h, hr]

/-- The version of `oracleRecvA_run_eq_of_none` for B. -/
theorem oracleRecvB_run_eq_of_none {n : ℕ} (h : s.msgA n = none) :
    (oracleRecvB scka n).run s = pure (none, s) := by
  simp [oracleRecvB, StateT.run_bind, StateT.run_get, h]

/-- The version of `oracleRecvA_run_eq_of_refuse` for B. -/
theorem oracleRecvB_run_eq_of_refuse {n tsnd : ℕ} {ρ : Rho} (h : s.msgA n = some (ρ, tsnd))
    (hr : scka.recvB s.stB ρ = none) :
    (oracleRecvB scka n).run s = pure (none, { s with correct := false }) := by
  simp [oracleRecvB, StateT.run_bind, StateT.run_get, StateT.run_set, h, hr]

/-- The version of `oracleRecvA_run_eq_of_accept` for B. -/
theorem oracleRecvB_run_eq_of_accept {n tsnd trcv : ℕ} {ρ : Rho} {keyOpt : Option (ℕ × I)}
    {stB' : StB} (h : s.msgA n = some (ρ, tsnd))
    (hr : scka.recvB s.stB ρ = some (keyOpt, trcv, stB')) :
    (oracleRecvB scka n).run s =
      pure (some (trcv, keyOpt.map Prod.fst), recvBUpdate s tsnd keyOpt trcv stB') := by
  rcases keyOpt with _ | ⟨tI, key⟩ <;>
    simp [oracleRecvB, recvBUpdate, knownPrefix, StateT.run_bind, StateT.run_get, StateT.run_set,
      h, hr]

end Oracles

/-! ### Invariants -/

/-- The uniform-randomness oracle preserves every predicate on the game state. -/
theorem oracleUnif_preservesInv (Inv : GameState StA StB I Rho → Prop) :
    QueryImpl.PreservesInv (oracleUnif StA StB I Rho) Inv :=
  fun t => StateT.preservesInv_monadLift ((QueryImpl.ofLift unifSpec ProbComp) t) Inv

/-- If the send and receive oracles preserve `Inv`, then so does every query of the correctness
game. -/
theorem sckaCorrectnessImpl_preservesInv [DecidableEq I]
    {Inv : GameState StA StB I Rho → Prop}
    (hSendA : QueryImpl.PreservesInv (oracleSendA scka) Inv)
    (hSendB : QueryImpl.PreservesInv (oracleSendB scka) Inv)
    (hRecvA : QueryImpl.PreservesInv (oracleRecvA scka) Inv)
    (hRecvB : QueryImpl.PreservesInv (oracleRecvB scka) Inv) :
    QueryImpl.PreservesInv (sckaCorrectnessImpl scka) Inv :=
  ((((oracleUnif_preservesInv Inv).add hSendA).add hSendB).add hRecvA).add hRecvB

/-- The known-prefix check holds exactly when every positive epoch through `n` has a key. -/
theorem knownPrefix_eq_true_iff {key : ℕ → Option I} {n : ℕ} :
    knownPrefix key n = true ↔ ∀ t, 0 < t → t ≤ n → key t ≠ none := by
  rw [knownPrefix, List.all_eq_true]
  constructor
  · intro h t hpos hle
    have ht := h t (List.mem_range.mpr (Nat.lt_succ_iff.mpr hle))
    simpa [hpos.ne', Option.isSome_iff_ne_none] using ht
  · intro h t ht
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · simp
    · simpa [Option.isSome_iff_ne_none, hpos.ne'] using
        h t hpos (Nat.lt_succ_iff.mp (List.mem_range.mp ht))

/-- `knownPrefix key n` holds when every epoch from `1` to `n` has a key. -/
theorem knownPrefix_eq_true {key : ℕ → Option I} {n : ℕ}
    (hkey : ∀ t, 0 < t → t ≤ n → key t ≠ none) :
    knownPrefix key n = true :=
  knownPrefix_eq_true_iff.2 hkey

/-- Assigning `some k` at any index preserves `knownPrefix key n`. -/
theorem knownPrefix_update_some {key : ℕ → Option I} {n : ℕ}
    (h : knownPrefix key n = true) (tI : ℕ) (k : I) :
    knownPrefix (Function.update key tI (some k)) n = true := by
  apply knownPrefix_eq_true
  intro t hpos hle
  by_cases ht : t = tI
  · subst t
    simp
  · rw [Function.update_of_ne ht]
    exact knownPrefix_eq_true_iff.1 h t hpos hle

/-- If `key` has keys for exactly the epochs from `1` through `c`, then recording a key for epoch
`c + 1` gives keys for exactly the epochs from `1` through `c + 1`. -/
theorem update_succ_ne_none_iff {key : ℕ → Option I} {c : ℕ}
    (hkey : ∀ t, key t ≠ none ↔ 0 < t ∧ t ≤ c) (k : I) (t : ℕ) :
    Function.update key (c + 1) (some k) t ≠ none ↔ 0 < t ∧ t ≤ c + 1 := by
  by_cases ht : t = c + 1
  · subst t
    simp
  · rw [Function.update_of_ne ht, hkey t]
    omega

/-! ### The potential method -/

/-- Let `scka` be an SCKA scheme, `Inv ik` a predicate on game states for each initial key `ik`,
`V` a potential with values in `ℝ≥0∞`, and `ε : ℝ≥0∞`. Assume:

* `V s ≥ 1` for every state with a false correctness flag;
* for every supported initial key and pair of supported initial party states, the initial game
  state satisfies `Inv ik` and has potential `0`;
* every query preserves `Inv ik` on supported outcomes;
* for every `ik`, query and state satisfying `Inv ik`, the expected successor potential is at
  most `V s + ε` for a send query and at most `V s` otherwise.

Then every adversary `adv` with at most `q` send queries in total across both parties satisfies
`1 - Pr[correctnessExp scka adv = true] ≤ q · ε`. -/
theorem correctness_error_le_of_potential [DecidableEq I]
    (Inv : IK → GameState StA StB I Rho → Prop) (V : GameState StA StB I Rho → ℝ≥0∞)
    (ε : ℝ≥0∞)
    (hV : ∀ s : GameState StA StB I Rho, s.correct = false → 1 ≤ V s)
    (hinit : ∀ ik ∈ support scka.initKeyGen, ∀ stA ∈ support (scka.initA ik),
      ∀ stB ∈ support (scka.initB ik),
        Inv ik (initGameState stA stB) ∧ V (initGameState stA stB) = 0)
    (hpres : ∀ ik, QueryImpl.PreservesInv (sckaCorrectnessImpl scka) (Inv ik))
    (hstep : ∀ ik (t : (sckaCorrectnessSpec Rho).Domain) s, Inv ik s →
      expectedPayoff ((sckaCorrectnessImpl scka t).run s) (fun z => V z.2) ≤
        V s + if isSendQuery (Rho := Rho) t then ε else 0)
    (adv : SCKACorrectnessAdversary Rho) (q : ℕ) (hq : SendQueryBound adv q) :
    1 - Pr[= true | correctnessExp scka adv] ≤ q * ε := by
  -- The expected potential of a complete run from any initial state is at most `q · ε`.
  have hrun : ∀ ik ∈ support scka.initKeyGen, ∀ stA ∈ support (scka.initA ik),
      ∀ stB ∈ support (scka.initB ik),
        expectedPayoff ((simulateQ (sckaCorrectnessImpl scka) adv).run (initGameState stA stB))
          (fun z => if z.2.correct then 0 else 1) ≤ q * ε := by
    intro ik hik stA hA stB hB
    obtain ⟨hinv, h0⟩ := hinit ik hik stA hA stB hB
    have h := expectedPayoff_simulateQ_run_le (sckaCorrectnessImpl scka) (Inv ik) V
      (fun t => isSendQuery (Rho := Rho) t = true) ε (hpres ik) (hstep ik) adv q hq _ hinv
    rw [h0, zero_add] at h
    refine le_trans (expectedPayoff_mono _ _ _ fun z => ?_) h
    split_ifs with hz
    · exact zero_le
    · exact hV _ (Bool.eq_false_iff.mpr hz)
  -- The failure probability is at most the expected indicator of a false flag.
  have hexp : correctnessExp scka adv =
      scka.initKeyGen >>= fun ik => scka.initA ik >>= fun stA => scka.initB ik >>= fun stB =>
        (fun z => z.2.correct) <$>
          (simulateQ (sckaCorrectnessImpl scka) adv).run (initGameState stA stB) := by
    simp [correctnessExp, map_eq_bind_pure_comp]
  have hle : Pr[= false | correctnessExp scka adv] ≤
      expectedPayoff (correctnessExp scka adv) (fun b => if b then 0 else 1) := by
    rw [← probEvent_eq_eq_probOutput]
    exact probEvent_le_expectedPayoff _ _ _ fun b hb => by simp [hb]
  have hfalse : Pr[= false | correctnessExp scka adv] =
      1 - Pr[= true | correctnessExp scka adv] := by
    rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero]
  rw [← hfalse]
  refine hle.trans ?_
  rw [hexp, expectedPayoff_bind]
  refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero fun ik hik => ?_
  rw [expectedPayoff_bind]
  refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero fun stA hA => ?_
  rw [expectedPayoff_bind]
  refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero fun stB hB => ?_
  rw [expectedPayoff_map]
  exact hrun ik hik stA hA stB hB

end SCKAScheme
