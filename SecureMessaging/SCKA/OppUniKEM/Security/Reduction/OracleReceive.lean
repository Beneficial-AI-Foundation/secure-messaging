/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Game
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Receive

/-!
# Delivery oracles under marked game states

**Statement.** For every selected epoch, material value, game state, and
message index, marking commutes with the honest intermediate receive
oracle of either party, including its response and full successor state.

**Proof.** Both games look up the same message table and run related local
receives. A records the key already in B's table, so key-consistency checks
agree after marking. B derives no key. The proof covers unavailable indices
and arbitrary reuse of indices; the local receive relation covers the
resulting delayed, reordered, and repeated messages.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

omit [DecidableEq K] in
/-- For every material value, selected epoch, game state, and message,
A's pinned receive equals the auxiliary receive using B's recorded key
as its constant decapsulation result. -/
theorem honest_recvA_eq_ideal
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (msg : Message Sym) :
    (honestScheme ecEk ecCt0 ecCt1 m e s).recvA s.stA msg =
      recvA (keyDecapsKEM base (s.keyB s.stA.t))
        (keyDecapsOnOff base onoff (s.keyB s.stA.t))
        (keyDecapsDet base (s.keyB s.stA.t)) ecCt0 ecCt1 s.stA msg := by
  rcases msg with ⟨ch, ack, epoch, bit⟩
  cases bit
  all_goals try (rename_i bit; fin_cases bit)
  all_goals cases ch
  all_goals cases hd : s.stA.dkA <;> cases hc : s.stA.ct0 <;> cases hk : s.keyB s.stA.t
  all_goals
    simp only [honestScheme, scheme, recvA, hd, hc,
      Pinned.deterministic, hk]
    repeat' (split <;> simp_all only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Bool.and_eq_true, beq_iff_eq, Option.some.injEq, Prod.mk.injEq, true_and])

set_option backward.dsimp.instances true in
/-- For every honest state and message index, B's symbolic receive oracle
equals its honest pinned receive oracle followed by marking. Both message
availability and correctness bookkeeping are preserved. -/
theorem oracleRecvB_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (SCKAScheme.oracleRecvB
      (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) n).run (markState e s) =
    Prod.map id (markState e) <$>
      (SCKAScheme.oracleRecvB (honestScheme ecEk ecCt0 ecCt1 m e s) n).run s := by
  simp only [SCKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgA n with
  | none => simp [markState, markA, markB, hm, StateT.run_pure, Prod.map]
  | some entry =>
    rcases entry with ⟨msg, tsnd⟩
    simp only [markState, hm]
    dsimp only [symbolicScheme, scheme]
    rw [recvB_mark]
    have heq : (honestScheme ecEk ecCt0 ecCt1 m e s).recvB s.stB msg =
        recvB base onoff ecEk s.stB msg := rfl
    rw [heq]
    cases hr : recvB base onoff ecEk s.stB msg with
    | none => simp [StateT.run_set, markState, markA, markB, Prod.map]
    | some out =>
      rcases out with ⟨key, t, next⟩
      have hk := recvB_key_none base onoff ecEk s.stB msg key t next hr
      subst key
      simp [StateT.run_set, markState, markA, markB, Prod.map]

set_option backward.dsimp.instances true in
/-- For every honest state and message index, A's symbolic receive oracle
equals its honest pinned receive oracle followed by marking. A's auxiliary
decapsulation uses B's recorded key, keeping each consistency check equal. -/
theorem oracleRecvA_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e n : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (SCKAScheme.oracleRecvA
      (symbolicScheme base onoff ecEk ecCt0 ecCt1 leak m e s) n).run (markState e s) =
    Prod.map id (markState e) <$>
      (SCKAScheme.oracleRecvA (honestScheme ecEk ecCt0 ecCt1 m e s) n).run s := by
  simp only [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgB n with
  | none => simp [markState, markA, markB, hm, StateT.run_pure, Prod.map]
  | some entry =>
    rcases entry with ⟨msg, tsnd⟩
    simp only [markState, hm]
    dsimp only [symbolicScheme, scheme]
    rw [recvA_mark]
    have heq := honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak m e s msg
    rw [heq]
    cases hr : recvA (keyDecapsKEM base (s.keyB s.stA.t))
        (keyDecapsOnOff base onoff (s.keyB s.stA.t))
        (keyDecapsDet base (s.keyB s.stA.t)) ecCt0 ecCt1 s.stA msg with
    | none => simp [StateT.run_set, markState, markA, markB, Prod.map]
    | some out =>
      rcases out with ⟨key, t, next⟩
      cases key with
      | none => simp [StateT.run_set, markState, markA, markB, Prod.map]
      | some key =>
        rcases key with ⟨epoch, k⟩
        obtain ⟨rfl, hk⟩ := recvA_key_source base onoff ecCt0 ecCt1
          (s.keyB s.stA.t) s.stA msg epoch k t next hr
        simp [StateT.run_set, markState, markA, markB,
          Prod.map, hk, ← mark_update]

end oppUniKemCKA.Security.Embedding
