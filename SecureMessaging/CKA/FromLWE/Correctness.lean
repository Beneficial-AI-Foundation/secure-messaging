/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Correctness.Distribution

/-!
# Correctness and failure probabilities for LWE CKA

This module proves the tape-prefix invariant and derives the final correctness-game failure bound.
`Correctness.Exchange` contains the exchange laws and the discussion of the paper's correctness
requirement. `Correctness.Tape` proves the sampled-tape laws. `Correctness.HonestRounds` defines
the honest-round experiment and tape interpreter. `Correctness.Progress` proves interpreter
progress, and `Correctness.Distribution` proves distribution equivalence.
-/

open OracleComp ENNReal

namespace lweCKA

open CorrectnessInternal

namespace TapePrefix

private def coin (p : Params) (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    SendACoins p × SendBCoins p :=
  (tape[n]?).getD (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)

private def prefixOK (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) : Bool :=
  decide (∀ j : Fin n, tapeRoundMismatch p ik tape j.val = false)

private def complete (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    CKAScheme.GameState (State p) (Key p) (Message p) :=
  if n = 0 then CKAScheme.initGameState (initA ik) (initB ik)
  else
    let previous := coin p tape (n - 1)
    { stA := if n % 2 = 0 then
        .aSend ik.baseMatrix (ik.baseMatrix * previous.2.secret + previous.2.error)
      else .aRecv ik.baseMatrix previous.1.secret
      stB := if n % 2 = 0 then .bRecv ik.baseMatrix previous.2.secret
        else .bSend ik.baseMatrix (previous.1.secret * ik.baseMatrix + previous.1.error)
      rhoA := none, rhoB := none, keyA := none, keyB := none
      correct := prefixOK p ik tape n
      lastAction := if n % 2 = 0 then some .recvA else some .recvB
      tA := n, tB := n }

private def pending (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    CKAScheme.GameState (State p) (Key p) (Message p) :=
  let current := coin p tape n
  let previous := coin p tape (n - 1)
  if n % 2 = 0 then
    let secret := if n = 0 then ik.secret else previous.2.secret
    let error := if n = 0 then ik.error else previous.2.error
    let value := current.1.secret * (ik.baseMatrix * secret + error) + current.1.extra
    { stA := .aRecv ik.baseMatrix current.1.secret
      stB := .bRecv ik.baseMatrix secret
      rhoA := some (.fromA (current.1.secret * ik.baseMatrix + current.1.error) (makeHint p value))
      rhoB := none, keyA := some (extract p value), keyB := none
      correct := prefixOK p ik tape n, lastAction := some .sendA
      tA := n + 1, tB := n }
  else
    let value := (previous.1.secret * ik.baseMatrix + previous.1.error) *
      current.2.secret + current.2.extra
    { stA := .aRecv ik.baseMatrix previous.1.secret
      stB := .bRecv ik.baseMatrix current.2.secret
      rhoA := none
      rhoB := some (.fromB (ik.baseMatrix * current.2.secret + current.2.error) (makeHint p value))
      keyA := none, keyB := some (extract p value)
      correct := prefixOK p ik tape n, lastAction := some .sendB
      tA := n, tB := n + 1 }

private theorem complete_phase (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    honestPhase p (complete p ik tape n) := by
  by_cases hn : n = 0
  · simp [complete, hn, honestPhase_init]
  · by_cases he : n % 2 = 0
    · simp [complete, hn, he, honestPhase]
    · have ho : n % 2 = 1 := by omega
      simp [complete, hn, ho, honestPhase]

private theorem pending_phase (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    honestPhase p (pending p ik tape n) := by
  by_cases he : n % 2 = 0
  · simp [pending, he, honestPhase]
  · have ho : n % 2 = 1 := by omega
    simp [pending, ho, honestPhase]

private theorem complete_count (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    (complete p ik tape n).tA = n ∧ (complete p ik tape n).tB = n := by
  by_cases hn : n = 0 <;> simp [complete, hn, CKAScheme.initGameState]

private theorem pending_count (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    min (pending p ik tape n).tA (pending p ik tape n).tB = n ∧
    max (pending p ik tape n).tA (pending p ik tape n).tB = n + 1 := by
  by_cases he : n % 2 = 0 <;> simp [pending, he]

private theorem complete_correct (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    (complete p ik tape n).correct = prefixOK p ik tape n := by
  cases n <;> simp [complete, prefixOK, CKAScheme.initGameState]

private theorem pending_correct (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    (pending p ik tape n).correct = prefixOK p ik tape n := by
  by_cases he : n % 2 = 0 <;> simp [pending, he]

private theorem prefixOK_succ (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    prefixOK p ik tape (n + 1) =
      (prefixOK p ik tape n && !tapeRoundMismatch p ik tape n) := by
  simp [prefixOK, Fin.forall_fin_succ', Bool.decide_eq_false]

private theorem coin_get (p : Params) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) : tape[n]? = some (coin p tape n) := by
  simp [coin, List.getElem?_eq_getElem hn]

private def senderValue (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) : SharedMatrix p :=
  let current := coin p tape n
  let previous := coin p tape (n - 1)
  if n % 2 = 0 then
    let secret := if n = 0 then ik.secret else previous.2.secret
    let error := if n = 0 then ik.error else previous.2.error
    current.1.secret * (ik.baseMatrix * secret + error) + current.1.extra
  else
    (previous.1.secret * ik.baseMatrix + previous.1.error) * current.2.secret + current.2.extra

private def receiverValue (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) : SharedMatrix p :=
  let current := coin p tape n
  let previous := coin p tape (n - 1)
  if n % 2 = 0 then
    let secret := if n = 0 then ik.secret else previous.2.secret
    (current.1.secret * ik.baseMatrix + current.1.error) * secret
  else
    previous.1.secret * (ik.baseMatrix * current.2.secret + current.2.error)

private theorem mismatch_values (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) (hn : n < tape.length) :
    tapeRoundMismatch p ik tape n = decide
      (reconcile p (receiverValue p ik tape n) (makeHint p (senderValue p ik tape n)) ≠
        extract p (senderValue p ik tape n)) := by
  cases n with
  | zero => simp [tapeRoundMismatch, coin_get p tape 0 hn, senderValue, receiverValue]
  | succ n =>
    have hprev := coin_get p tape n (by omega)
    have hcur := coin_get p tape (n + 1) hn
    by_cases he : (n + 1) % 2 = 0 <;>
      simp [tapeRoundMismatch, hprev, hcur, senderValue, receiverValue, he]

private theorem recvA_run (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.ORecvA).run s =
      (CKAScheme.oracleRecvA cka ()).run s := rfl

private theorem recvB_run (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.ORecvB).run s =
      (CKAScheme.oracleRecvB cka ()).run s := rfl

private theorem keyAgreement (p : Params) (a b : Key p) :
    (a == b) = !decide (b ≠ a) := by
  by_cases h : a = b
  · subst b
    simp
  · have h' : b ≠ a := Ne.symm h
    simp [h, h']

private theorem pending_recvA (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape rest : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) (ho : n % 2 = 1) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvA).run
      (pending p ik tape n, rest) = pure ((), complete p ik tape (n + 1), rest) := by
  have he : ¬ n % 2 = 0 := by omega
  have hs : (n + 1) % 2 = 0 := by omega
  have hm := mismatch_values p ik tape n hn
  simp only [senderValue, receiverValue, if_neg he] at hm
  cases rest with
  | nil =>
    simp [tapeCorrectnessImpl, recvA_run p, pending, he, complete, hs,
      CKAScheme.oracleRecvA, CKAScheme.validStep, scheme, recvA,
      prefixOK_succ, hm]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvA]
    simp only [pure_bind, map_pure]
    simp only [keyAgreement, ← decide_not, not_not]
  | cons c rest =>
    simp [tapeCorrectnessImpl, recvA_run p, pending, he, complete, hs,
      CKAScheme.oracleRecvA, CKAScheme.validStep, scheme, recvA,
      prefixOK_succ, hm]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvA]
    simp only [pure_bind, map_pure]
    simp only [keyAgreement, ← decide_not, not_not, Nat.lt_irrefl, and_false,
      or_self, ite_false]

private theorem pending_recvB (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape rest : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) (he : n % 2 = 0) :
    (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvB).run
      (pending p ik tape n, rest) = pure ((), complete p ik tape (n + 1), rest) := by
  have hs : ¬ (n + 1) % 2 = 0 := by omega
  have hm := mismatch_values p ik tape n hn
  simp only [senderValue, receiverValue, if_pos he] at hm
  cases rest with
  | nil =>
    simp [tapeCorrectnessImpl, recvB_run p, pending, he, complete, hs,
      CKAScheme.oracleRecvB, CKAScheme.validStep, scheme, recvB,
      prefixOK_succ, hm]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvB]
    simp only [pure_bind, map_pure]
    simp only [keyAgreement, ← decide_not, not_not]
  | cons c rest =>
    simp [tapeCorrectnessImpl, recvB_run p, pending, he, complete, hs,
      CKAScheme.oracleRecvB, CKAScheme.validStep, scheme, recvB,
      prefixOK_succ, hm]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvB]
    simp only [pure_bind, map_pure]
    simp only [keyAgreement, ← decide_not, not_not, Nat.lt_irrefl, false_and,
      or_self, ite_false]

private theorem sendA_run (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendA).run s =
      (CKAScheme.oracleSendA cka ()).run s := rfl

private theorem sendB_run (p : Params)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka CKAScheme.ckaCorrectnessSpec.OSendB).run s =
      (CKAScheme.oracleSendB cka ()).run s := rfl

private theorem drop_coin (p : Params) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) :
    tape.drop n = coin p tape n :: tape.drop (n + 1) := by
  rw [List.drop_eq_getElem_cons hn]
  simp [coin, List.getElem?_eq_getElem hn]

private theorem complete_sendA (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) (he : n % 2 = 0) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendA).run
      (complete p ik tape n, tape.drop n) =
      pure (pending p ik tape n, tape.drop (n + 1)) := by
  rw [drop_coin p tape n hn]
  by_cases hz : n = 0
  · subst n
    simp [tapeCorrectnessImpl, sendA_run p, complete, pending, initA, initB,
      CKAScheme.initGameState, CKAScheme.oracleSendA, CKAScheme.validStep, prefixOK]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]
    simp only [pure_bind, map_pure, Nat.lt_irrefl]
    simp
  · simp [tapeCorrectnessImpl, sendA_run p, complete, pending, he, hz,
      CKAScheme.oracleSendA, CKAScheme.validStep]
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA]
    simp only [pure_bind, map_pure]
    simp

private theorem complete_sendB (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length) (he : n % 2 = 1) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendB).run
      (complete p ik tape n, tape.drop n) =
      pure (pending p ik tape n, tape.drop (n + 1)) := by
  have hz : n ≠ 0 := by omega
  have he' : ¬ n % 2 = 0 := by omega
  rw [drop_coin p tape n hn]
  simp [tapeCorrectnessImpl, sendB_run p, complete, pending, he', hz,
    CKAScheme.oracleSendB, CKAScheme.validStep]
  dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendB]
  simp only [pure_bind, map_pure]
  simp

private theorem invalid_sendA (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendA = false) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendA).run
      (s, tape) = pure (s, tape) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, sendA_run p, CKAScheme.oracleSendA, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendA] <;>
    simp

private theorem invalid_sendB (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .sendB = false) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.OSendB).run
      (s, tape) = pure (s, tape) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, sendB_run p, CKAScheme.oracleSendB, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OSendB] <;>
    simp

private theorem invalid_recvA (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .recvA = false) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvA).run
      (s, tape) = pure (s, tape) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, recvA_run p, CKAScheme.oracleRecvA, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvA] <;>
    simp

private theorem invalid_recvB (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p))
    (hg : CKAScheme.validStep s.lastAction .recvB = false) :
    Prod.snd <$> (tapeCorrectnessImpl p hp χ CKAScheme.ckaCorrectnessSpec.ORecvB).run
      (s, tape) = pure (s, tape) := by
  cases tape <;>
    simp [tapeCorrectnessImpl, recvB_run p, CKAScheme.oracleRecvB, hg] <;>
    dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.ORecvB] <;>
    simp

private theorem unif_run (p : Params) (n : ℕ)
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (cka : CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p)) :
    (CKAScheme.ckaCorrectnessImpl cka (CKAScheme.ckaCorrectnessSpec.OUnif n)).run s =
      (CKAScheme.oracleUnif (State p) (Key p) (Message p) n).run s := rfl

private theorem unif_state (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (s : CKAScheme.GameState (State p) (Key p) (Message p))
    (tape : List (SendACoins p × SendBCoins p)) (n : ℕ) :
    ∀ z ∈ support ((tapeCorrectnessImpl p hp χ
      (CKAScheme.ckaCorrectnessSpec.OUnif n)).run (s, tape)), z.2 = (s, tape) := by
  intro z hz
  cases tape <;>
    simp only [tapeCorrectnessImpl, bind_pure_comp, lt_sup_iff, sup_lt_iff,
      StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift, monadLift_self,
      StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
      support_map, Set.mem_image, Prod.exists] at hz
  all_goals
    rcases hz with ⟨a, b, hab, rfl⟩
    have hb : b = s := by
      rw [unif_run p] at hab
      dsimp [CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaCorrectnessSpec.OUnif] at a hab
      simp only [CKAScheme.oracleUnif, PFunctor.Handler.liftTarget_apply,
        PFunctor.selfMonomial_B, QueryImpl.ofLift_apply, StateT.run_monadLift,
        monadLift_self, bind_pure_comp, support_map, support_liftM,
        OracleQuery.input_query, OracleQuery.cont_query, Set.range_id, Set.image_univ] at hab
      rcases hab with ⟨_, h⟩
      exact (congrArg Prod.snd h).symm
    subst b
    simp

private theorem state_eq_of_map {A S : Type} (mx : ProbComp (A × S)) (s : S)
    (heq : Prod.snd <$> mx = pure s) (z : A × S) (hz : z ∈ support mx) : z.2 = s := by
  have hmem : z.2 ∈ support (Prod.snd <$> mx) := by
    rw [support_map]
    exact ⟨z, hz, rfl⟩
  rw [heq] at hmem
  exact eq_of_mem_support_pure hmem

private inductive Good (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) :
    (CKAScheme.GameState (State p) (Key p) (Message p) ×
      List (SendACoins p × SendBCoins p)) → Prop
  | complete (n : ℕ) (hn : n ≤ tape.length) :
      Good p ik tape (complete p ik tape n, tape.drop n)
  | pending (n : ℕ) (hn : n < tape.length) :
      Good p ik tape (pending p ik tape n, tape.drop (n + 1))
  | exhausted (s rest) (hmin : min s.tA s.tB = tape.length)
      (hc : s.correct = prefixOK p ik tape tape.length) : Good p ik tape (s, rest)
  | overflow (s rest) (hn : tape.length < min s.tA s.tB) : Good p ik tape (s, rest)

private theorem good_correct (p : Params) (ik : InitKey p)
    (tape : List (SendACoins p × SendBCoins p)) (s rest)
    (hg : Good p ik tape (s, rest)) (hn : min s.tA s.tB ≤ tape.length) :
    s.correct = prefixOK p ik tape (min s.tA s.tB) := by
  cases hg with
  | complete n h =>
      rw [(complete_count p ik tape n).1, (complete_count p ik tape n).2, min_self]
      exact complete_correct p ik tape n
  | pending n h =>
      rw [(pending_count p ik tape n).1]
      exact pending_correct p ik tape n
  | exhausted s rest hm hc => simpa [hm] using hc
  | overflow s rest h => omega

private theorem boundary_step (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    (q : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Domain)
    (s rest) (hs : honestPhase p s)
    (hm : min s.tA s.tB = tape.length)
    (hc : s.correct = prefixOK p ik tape tape.length)
    (z) (hz : z ∈ support ((tapeCorrectnessImpl p hp χ q).run (s, rest))) :
    Good p ik tape z.2 := by
  have h := tapeCorrectnessImpl_progress p hp χ q s rest hs z hz
  have hmono : min s.tA s.tB ≤ min z.2.1.tA z.2.1.tB := min_le_min h.2.1 h.2.2.1
  by_cases he : min z.2.1.tA z.2.1.tB = tape.length
  · exact Good.exhausted z.2.1 z.2.2 he ((h.2.2.2.2.2.2 (he.trans hm.symm)).trans hc)
  · apply Good.overflow z.2.1 z.2.2
    exact lt_of_le_of_ne (hm ▸ hmono) (Ne.symm he)

private theorem complete_step (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length)
    (q : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Domain)
    (z) (hz : z ∈ support ((tapeCorrectnessImpl p hp χ q).run
      (complete p ik tape n, tape.drop n))) : Good p ik tape z.2 := by
  have hself := Good.complete (p := p) (ik := ik) (tape := tape) n (by omega)
  match q with
  | CKAScheme.ckaCorrectnessSpec.OUnif k =>
      rw [unif_state p hp χ _ _ k z hz]
      exact hself
  | CKAScheme.ckaCorrectnessSpec.OSendA =>
      by_cases he : n % 2 = 0
      · rw [state_eq_of_map _ _ (complete_sendA p hp χ ik tape n hn he) z hz]
        exact Good.pending n hn
      · have hg : CKAScheme.validStep (complete p ik tape n).lastAction .sendA = false := by
          have hne : n ≠ 0 := by omega
          simp [complete, hne, he, CKAScheme.validStep]
        rw [state_eq_of_map _ _ (invalid_sendA p hp χ _ _ hg) z hz]
        exact hself
  | CKAScheme.ckaCorrectnessSpec.OSendB =>
      by_cases he : n % 2 = 1
      · rw [state_eq_of_map _ _ (complete_sendB p hp χ ik tape n hn he) z hz]
        exact Good.pending n hn
      · have hg : CKAScheme.validStep (complete p ik tape n).lastAction .sendB = false := by
          have he' : n % 2 = 0 := by omega
          by_cases hzero : n = 0 <;> simp [complete, hzero, he',
            CKAScheme.initGameState, CKAScheme.validStep]
        rw [state_eq_of_map _ _ (invalid_sendB p hp χ _ _ hg) z hz]
        exact hself
  | CKAScheme.ckaCorrectnessSpec.ORecvA =>
      have hg : CKAScheme.validStep (complete p ik tape n).lastAction .recvA = false := by
        by_cases hz : n = 0 <;> by_cases he : n % 2 = 0 <;>
          simp [complete, hz, he, CKAScheme.initGameState, CKAScheme.validStep]
      rw [state_eq_of_map _ _ (invalid_recvA p hp χ _ _ hg) z hz]
      exact hself
  | CKAScheme.ckaCorrectnessSpec.ORecvB =>
      have hg : CKAScheme.validStep (complete p ik tape n).lastAction .recvB = false := by
        by_cases hz : n = 0 <;> by_cases he : n % 2 = 0 <;>
          simp [complete, hz, he, CKAScheme.initGameState, CKAScheme.validStep]
      rw [state_eq_of_map _ _ (invalid_recvB p hp χ _ _ hg) z hz]
      exact hself

private theorem pending_step (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    (n : ℕ) (hn : n < tape.length)
    (q : (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)).Domain)
    (z) (hz : z ∈ support ((tapeCorrectnessImpl p hp χ q).run
      (pending p ik tape n, tape.drop (n + 1)))) : Good p ik tape z.2 := by
  have hself := Good.pending (p := p) (ik := ik) (tape := tape) n hn
  match q with
  | CKAScheme.ckaCorrectnessSpec.OUnif k =>
      rw [unif_state p hp χ _ _ k z hz]
      exact hself
  | CKAScheme.ckaCorrectnessSpec.ORecvA =>
      by_cases he : n % 2 = 1
      · have heq := pending_recvA p hp χ ik tape (tape.drop (n + 1)) n hn he
        have hz' := hz
        rw [heq] at hz'
        have hz'' := eq_of_mem_support_pure hz'
        rw [hz'']
        exact Good.complete (n + 1) (by omega)
      · have hg : CKAScheme.validStep (pending p ik tape n).lastAction .recvA = false := by
          have he' : n % 2 = 0 := by omega
          simp [pending, he', CKAScheme.validStep]
        rw [state_eq_of_map _ _ (invalid_recvA p hp χ _ _ hg) z hz]
        exact hself
  | CKAScheme.ckaCorrectnessSpec.ORecvB =>
      by_cases he : n % 2 = 0
      · have heq := pending_recvB p hp χ ik tape (tape.drop (n + 1)) n hn he
        have hz' := hz
        rw [heq] at hz'
        have hz'' := eq_of_mem_support_pure hz'
        rw [hz'']
        exact Good.complete (n + 1) (by omega)
      · have hg : CKAScheme.validStep (pending p ik tape n).lastAction .recvB = false := by
          have he' : n % 2 = 1 := by omega
          simp [pending, he', CKAScheme.validStep]
        rw [state_eq_of_map _ _ (invalid_recvB p hp χ _ _ hg) z hz]
        exact hself
  | CKAScheme.ckaCorrectnessSpec.OSendA =>
      have hg : CKAScheme.validStep (pending p ik tape n).lastAction .sendA = false := by
        by_cases he : n % 2 = 0 <;> simp [pending, he, CKAScheme.validStep]
      rw [state_eq_of_map _ _ (invalid_sendA p hp χ _ _ hg) z hz]
      exact hself
  | CKAScheme.ckaCorrectnessSpec.OSendB =>
      have hg : CKAScheme.validStep (pending p ik tape n).lastAction .sendB = false := by
        by_cases he : n % 2 = 0 <;> simp [pending, he, CKAScheme.validStep]
      rw [state_eq_of_map _ _ (invalid_sendB p hp χ _ _ hg) z hz]
      exact hself

private theorem good_preserved (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p)) :
    QueryImpl.PreservesInv (tapeCorrectnessImpl p hp χ)
      (fun z => honestPhase p z.1 ∧ Good p ik tape z) := by
  intro q initial hin z hz
  rcases initial with ⟨s, rest⟩
  rcases hin with ⟨hs, hg⟩
  have hprogress := tapeCorrectnessImpl_progress p hp χ q s rest hs z hz
  refine ⟨hprogress.1, ?_⟩
  cases hg with
  | complete n hn =>
      by_cases hlt : n < tape.length
      · exact complete_step p hp χ ik tape n hlt q z hz
      · have heq : n = tape.length := by omega
        apply boundary_step p hp χ ik tape q _ _ hs _ _ z hz
        · rw [(complete_count p ik tape n).1, (complete_count p ik tape n).2,
            min_self, heq]
        · rw [complete_correct, heq]
  | pending n hn => exact pending_step p hp χ ik tape n hn q z hz
  | exhausted s rest hm hc =>
      exact boundary_step p hp χ ik tape q s rest hs hm hc z hz
  | overflow s rest hn =>
      exact Good.overflow z.2.1 z.2.2
        (lt_of_lt_of_le hn (min_le_min hprogress.2.1 hprogress.2.2.1))

private theorem prefix_correct (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    {α : Type}
    (oa : OracleComp (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)) α) :
    ∀ z ∈ support ((simulateQ (tapeCorrectnessImpl p hp χ) oa).run
      (CKAScheme.initGameState (initA ik) (initB ik), tape)),
      min z.2.1.tA z.2.1.tB ≤ tape.length →
      z.2.1.correct = decide (∀ j : Fin (min z.2.1.tA z.2.1.tB),
        tapeRoundMismatch p ik tape j.val = false) := by
  intro z hz hn
  have hinit : honestPhase p (CKAScheme.initGameState (initA ik) (initB ik)) ∧
      Good p ik tape (CKAScheme.initGameState (initA ik) (initB ik), tape) := by
    refine ⟨honestPhase_init p ik, ?_⟩
    simpa [complete] using
      Good.complete (p := p) (ik := ik) (tape := tape) 0 (by omega)
  have hfinal := simulateQ_run_preservesInv (tapeCorrectnessImpl p hp χ)
    (fun z => honestPhase p z.1 ∧ Good p ik tape z)
    (good_preserved p hp χ ik tape) oa _ hinit z hz
  exact good_correct p ik tape z.2.1 z.2.2 hfinal.2 hn

end TapePrefix

/-- Assume that the number of completed exchanges is at most the tape length.
The final correctness flag is true exactly when all completed exchanges agree. -/
theorem tapeCorrectnessRun_correct
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (ik : InitKey p) (tape : List (SendACoins p × SendBCoins p))
    {α : Type}
    (oa : OracleComp (CKAScheme.ckaCorrectnessSpec (Message p) (Key p)) α) :
    ∀ z ∈ support
      ((simulateQ (tapeCorrectnessImpl p hp χ) oa).run
        (CKAScheme.initGameState (initA ik) (initB ik), tape)),
      min z.2.1.tA z.2.1.tB ≤ tape.length →
      z.2.1.correct =
        decide (∀ j : Fin (min z.2.1.tA z.2.1.tB),
          tapeRoundMismatch p ik tape j.val = false) := by
  exact TapePrefix.prefix_correct p hp χ ik tape oa

/-- Run the correctness experiment and return the adversary result together with the final game
state. -/
def correctnessStateExp
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p)) :
    ProbComp (Bool × CKAScheme.GameState (State p) (Key p) (Message p)) := do
  let cka := scheme p hp χ
  let ik ← cka.initKeyGen
  let stateA ← cka.initA ik
  let stateB ← cka.initB ik
  (simulateQ (CKAScheme.ckaCorrectnessImpl cka) adv).run
    (CKAScheme.initGameState stateA stateB)

/-- Every possible final state of the correctness experiment satisfies `honestPhase`. -/
theorem correctnessStateExp_honestPhase
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p)) :
    ∀ z ∈ support (correctnessStateExp p hp χ adv), honestPhase p z.2 := by
  intro z hz
  simp only [correctnessStateExp, scheme, pure_bind, support_bind, Set.mem_iUnion] at hz
  obtain ⟨ik, hik, hz⟩ := hz
  exact simulateQ_run_preservesInv _ (honestPhase p)
    (correctnessImpl_preserves_honestPhase p hp χ) adv _
    (honestPhase_init p ik) z hz

/-- The public correctness experiment returns the correctness flag from the final game state. -/
theorem correctnessExp_eq_map_state
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p)) :
    CKAScheme.correctnessExp (scheme p hp χ) adv =
      (fun z => z.2.correct) <$> correctnessStateExp p hp χ adv := by
  simp [CKAScheme.correctnessExp, correctnessStateExp, map_eq_bind_pure_comp]

/-- Require at most `T` completed exchanges in every possible outcome of the correctness experiment.
The count is `min tA tB`, so a send without its matching receive does not count. -/
def HasExchangeBound
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p))
    (T : ℕ) : Prop :=
  ∀ z ∈ support (correctnessStateExp p hp χ adv), min z.2.tA z.2.tB ≤ T

/-- If every run completes at most `T` exchanges, its failure probability is at most `min 1 (T *
firstExchangeFailureProb)`. -/
theorem correctness_failure_le
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p))
    (T : ℕ) (hT : HasExchangeBound p hp χ adv T) :
    Pr{let x ← CKAScheme.correctnessExp (scheme p hp χ) adv}[x = false] ≤
      min 1 ((T : ℝ≥0∞) * firstExchangeFailureProb p χ) := by
  have hReplay := fun (ik : InitKey p) (N : ℕ) =>
    evalDist_tapeCorrectnessRun p hp χ adv
      (CKAScheme.initGameState (initA ik) (initB ik))
      (honestPhase_init p ik) N
  have hPrefix := fun ik tape =>
    tapeCorrectnessRun_correct p hp χ ik tape adv
  classical
  let runTape := fun t : InitKey p × List (SendACoins p × SendBCoins p) =>
    (simulateQ (tapeCorrectnessImpl p hp χ) adv).run
      (CKAScheme.initGameState (initA t.1) (initB t.1), t.2)
  let replay : ProbComp (Bool × CKAScheme.GameState (State p) (Key p) (Message p)) := do
    let t ← sampleHonestTape p χ (T + 1)
    let z ← runTape t
    return (z.1, z.2.1)
  have hdist : finiteLaw (replay) = finiteLaw (correctnessStateExp p hp χ adv) := by
    simp only [replay, sampleHonestTape, correctnessStateExp, scheme, bind_assoc,
      pure_bind]
    exact evalDist_bind_congr' (initKeyGen p χ) fun ik => hReplay ik (T + 1)
  have hcount : ∀ t ∈ support (sampleHonestTape p χ (T + 1)),
      ∀ z ∈ support (runTape t), min z.2.1.tA z.2.1.tB ≤ T := by
    intro t ht z hz
    apply hT (z.1, z.2.1)
    apply (mem_support_iff_of_evalDist_eq hdist _).1
    simp only [replay, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨t, ht, z, hz, rfl⟩
  have hevent : Pr{let z ← replay}[z.2.correct = false] ≤
      (T : ℝ≥0∞) * firstExchangeFailureProb p χ := by
    calc
      Pr{let z ← replay}[z.2.correct = false] =
          Pr{let z ← sampleHonestTape p χ (T + 1) >>= runTape}[z.2.1.correct = false] := by
        simp [replay, OracleComp.prEvent_bind_eq_tsum, Function.comp_def]
      _ ≤ Pr{let t ← sampleHonestTape p χ (T + 1)}[∃ j : Fin T, tapeRoundMismatch p t.1 t.2 j.val = true] := by
        apply prEvent_bind_le_prEvent_of_support
        intro t ht hgood
        apply (OracleComp.prEvent_eq_zero_iff _ _).mpr
        intro z hz hfalse
        have hc := hcount t ht z hz
        have hl := sampleHonestTape_length p χ (T + 1) t ht
        have hpref := hPrefix t.1 t.2 z hz (by omega)
        have hall : ∀ j : Fin (min z.2.1.tA z.2.1.tB),
            tapeRoundMismatch p t.1 t.2 j.val = false := by
          intro j
          have hnot : tapeRoundMismatch p t.1 t.2 j.val ≠ true := by
            intro h
            exact hgood ⟨⟨j.val, by omega⟩, h⟩
          exact Bool.eq_false_iff.mpr hnot
        simp [hall, hfalse] at hpref
      _ ≤ (T : ℝ≥0∞) * firstExchangeFailureProb p χ :=
        probEvent_tapePrefixFailure_le p χ T
  apply le_min (prEvent_le_one _)
  rw [correctnessExp_eq_map_state, prEvent_map]
  have heq : Pr{let z ← replay}[z.2.correct = false] =
      Pr{let z ← correctnessStateExp p hp χ adv}[z.2.correct = false] := by
    rw [probEvent_def, probEvent_def, hdist]
  exact heq ▸ hevent

/-- If every run completes at most `T` exchanges and the first exchange has zero failure
probability, correctness holds with probability one. -/
theorem correctness_of_zero
    (p : Params) (hp : p.WellFormed) (χ : ProbComp (Scalar p))
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) (Key p))
    (T : ℕ) (hT : HasExchangeBound p hp χ adv T)
    (hzero : firstExchangeFailureProb p χ = 0) :
    Pr{let x ← CKAScheme.correctnessExp (scheme p hp χ) adv}[x = true] = 1 := by
  have hz : Pr{let x ← CKAScheme.correctnessExp (scheme p hp χ) adv}[x = false] = 0 :=
    le_antisymm
      (by simpa [hzero] using correctness_failure_le p hp χ adv T hT)
      bot_le
  apply (OracleComp.prEvent_eq_one_iff _ (· = true)).2
  intro y hy
  cases y
  · exact False.elim ((OracleComp.prEvent_eq_zero_iff _ (· = false)).1 hz false hy rfl)
  · rfl

end lweCKA
