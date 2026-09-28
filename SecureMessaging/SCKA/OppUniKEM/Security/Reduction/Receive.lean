/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation
import SecureMessaging.SCKA.OppUniKEM.Security.Ideal

/-!
# Receive operations under marked states

**Statement.** For every selected epoch, local state, and input message,
marking commutes with B's receive and A's auxiliary receive. B preserves
public decoding and acknowledgement behavior. A uses the marked form of
the honest auxiliary decapsulation result and marks each returned epoch key.

**Proof.** Inspect the receive branches. Public fields determine decoding
and acknowledgement updates. A successful epoch advance erases the private
field, so marking after the advance agrees with erasing the marked field.
The statements apply to every message, including delayed and repeated inputs.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq Sym]

/-- For every B-state and message, a successful B-receive returns an absent
derived key. B records keys only through online encapsulation in its send. -/
theorem recvB_key_none
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (s : StB onoff Sym) (msg : Message Sym)
    (key : Option (ℕ × K)) (t : ℕ) (next : StB onoff Sym)
    (h : recvB base onoff ecEk s msg = some (key, t, next)) : key = none := by
  unfold recvB at h
  repeat' split at h
  all_goals simp_all

/-- For every A-state and message, if constant-decapsulation receive
returns `(t, k)`, then `t` is A's initial epoch and the supplied constant
decapsulation result is `some k`. -/
theorem recvA_key_source
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (key : Option K)
    (s : StA onoff Sym) (msg : Message Sym)
    (t : ℕ) (k : K) (trcv : ℕ) (next : StA onoff Sym)
    (h : recvA (keyDecapsKEM base key) (keyDecapsOnOff base onoff key)
      (keyDecapsDet base key) ecCt0 ecCt1 s msg = some (some (t, k), trcv, next)) :
    t = s.t ∧ key = some k := by
  rcases msg with ⟨ch, ack, epoch, bit⟩
  by_cases ht : s.t = epoch
  all_goals
    simp only [recvA, ht, ↓reduceIte] at h
    repeat' split at h
    all_goals simp_all

set_option backward.dsimp.instances true in
/-- For every local B-state and input message, symbolic receive equals
honest receive followed by marking B's successor. Both return an absent key
and the delivered message's sending epoch. -/
theorem recvB_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (e : ℕ)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K))
    (s : StB onoff Sym) (msg : Message Sym) :
    recvB (kem base onoff selectedA selectedB pkStar ctStar key)
      (onOff base onoff selectedA selectedB pkStar ctStar key) ecEk (markB e s) msg =
      (recvB base onoff ecEk s msg).map (fun (_, t, u) => (none, t, markB e u)) := by
  rcases msg with ⟨ch, ack, t, b⟩
  by_cases hadv : s.t < t
  all_goals
    simp only [recvB, markB, hadv, ↓reduceIte]
    repeat' (split <;> simp_all only [Option.map_none, Option.map_some])

set_option maxHeartbeats 800000 in
-- Splitting the receive branches also expands the state-marking equations.
set_option backward.dsimp.instances true in
/-- For every local A-state, input message, and auxiliary key `key`, symbolic
receive with decapsulation result `key.map (mark e s.t)` equals honest
auxiliary receive followed by marking its returned epoch key and successor. -/
theorem recvA_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (e : ℕ)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option K)
    (s : StA onoff Sym) (msg : Message Sym) :
    recvA (kem base onoff selectedA selectedB pkStar ctStar (key.map (mark e s.t)))
      (onOff base onoff selectedA selectedB pkStar ctStar (key.map (mark e s.t)))
      (deterministic base onoff selectedA selectedB pkStar ctStar (key.map (mark e s.t)))
      ecCt0 ecCt1 (markA e s) msg =
      (recvA (keyDecapsKEM base key) (keyDecapsOnOff base onoff key)
        (keyDecapsDet base key) ecCt0 ecCt1 s msg).map
        (fun (out, t, u) =>
          (out.map (fun (epoch, k) => (epoch, mark e epoch k)), t, markA e u)) := by
  rcases msg with ⟨ch, ack, t, b⟩
  cases b
  all_goals try (rename_i bit; fin_cases bit)
  all_goals cases ch
  all_goals cases hd : s.dkA <;> cases hc : s.ct0 <;> cases hk : key
  all_goals
    simp only [recvA, markA, hd, hc]
    repeat' (split <;> simp_all only [Option.map_none, Option.map_some])
  all_goals
    simp_all only [Fin.mk_one, Fin.isValue, Bool.and_eq_true, beq_iff_eq,
      Option.some.injEq, Prod.mk.injEq, true_and]
    repeat' (split <;> simp_all only [Option.map_none, Option.map_some,
      and_true, true_and, Bool.not_eq_true, Nat.add_eq_left, one_ne_zero,
      and_false, ↓reduceIte, and_self])

end oppUniKemCKA.Security.Embedding
