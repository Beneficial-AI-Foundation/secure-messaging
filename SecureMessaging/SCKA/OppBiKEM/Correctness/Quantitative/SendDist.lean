/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.SendProvenance

/-!
# Distribution of Opp-BiKEM `send` in its randomised cases

`send` samples only in two situations: key generation when the advance gate holds, and
encapsulation when the own key is acknowledged, no ciphertext is retained and the peer's key
is known. In both, the rest of the send is deterministic. `send_eq_advance` and
`send_eq_encaps` state `send` as the sampler followed by a `pure` of an explicit outcome
(`advanceSend`, `encapsSend`); the quantitative proof computes expected values from them.
`send_emittedKey_peerAck` records the acknowledgement guards an emitted key implies.
-/

open OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- The flags `sendWith` advertises. -/
def advertisedAck (role : Role) (st : State PK SK C Sym) : Ack :=
  { ekRec := decide (st.req.reqEpoch - role.offset ∈ st.ack.ekRec)
    ctRec := decide (st.req.reqEpoch ∈ st.ack.ctRec) }

/-- Outcome of a send that advances the epoch with key pair `kp` and emits the first chunk of
the new public key. -/
def advanceSend (role : Role) (ecEk : ErasureCodePayload PK Sym) (st : State PK SK C Sym)
    (kp : PK × SK) : Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym :=
  let tRes := st.res.resEpoch + 2
  let keyEpoch := tRes + role.offset
  let st' : State PK SK C Sym :=
    { res := ⟨tRes, st.res.ekPeer, st.res.ct, 1⟩
      req := ⟨st.req.reqEpoch, (keyEpoch, kp.2) :: st.req.dk.filter (fun p => p.1 != keyEpoch),
        some kp.1, st.req.receivedChunks⟩
      ack := st.ack }
  let ρ : Message Sym :=
    { ch := some (ecEk.encode kp.1 1), tRes := tRes, tReq := st.req.reqEpoch
      sendingEpoch := st.ack.sendingHorizon, ack := advertisedAck role st, bit := some 0 }
  (none, ρ, ρ.sendingEpoch, st')

/-- Outcome of a send that encapsulates `ck` at the current responder epoch and emits the
first ciphertext chunk. -/
def encapsSend (role : Role) (ecCt : ErasureCodePayload C Sym) (st : State PK SK C Sym)
    (ck : C × K) : Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym :=
  let st' : State PK SK C Sym :=
    { res := ⟨st.res.resEpoch, st.res.ekPeer, some ck.1, 1⟩, req := st.req, ack := st.ack }
  let ρ : Message Sym :=
    { ch := some (ecCt.encode ck.1 1), tRes := st.res.resEpoch, tReq := st.req.reqEpoch
      sendingEpoch := st.ack.sendingHorizon, ack := advertisedAck role st, bit := some 1 }
  (some (st.res.resEpoch.toNat, ck.2), ρ, ρ.sendingEpoch, st')

/-- When the advance gate holds and the new key epoch is not yet acknowledged, `send` is key
generation followed by the deterministic `advanceSend`. -/
theorem send_eq_advance (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (hek : st.req.ek = none)
    (hgate : st.res.resEpoch ∈ st.ack.ctRec ∧ st.res.resEpoch + role.offset ∈ st.ack.ctRec)
    (hfresh : st.res.resEpoch + 2 + role.offset ∉ st.ack.ekRec) :
    send role kem ecEk ecCt st =
      kem.keygen >>= fun kp => pure (some (advanceSend role ecEk st kp)) := by
  unfold send sendWith
  simp only [hek, Option.isNone_none, hgate, and_self, decide_true, Bool.and_self, if_true,
    hfresh, not_false_eq_true, bind_assoc, pure_bind, Option.map_some]
  rfl

/-- When the gate fails because the current ciphertext is unacknowledged, the own key is
acknowledged, no ciphertext is retained and the peer's key is known, `send` is encapsulation
followed by the deterministic `encapsSend`. -/
theorem send_eq_encaps (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (hnot : st.res.resEpoch ∉ st.ack.ctRec)
    (hacked : st.res.resEpoch + role.offset ∈ st.ack.ekRec)
    (hct : st.res.ct = none) (hpeerAck : st.res.resEpoch ∈ st.ack.ekRec)
    {pk : PK} (hpk : st.res.ekPeer st.res.resEpoch = some pk) :
    send role kem ecEk ecCt st =
      kem.encaps pk >>= fun ck => pure (some (encapsSend role ecCt st ck)) := by
  unfold send sendWith
  simp only [hnot, false_and, decide_false, Bool.and_false, Bool.false_eq_true, if_false,
    hacked, not_true_eq_false, not_false_eq_true, hct, Option.isNone_none, hpeerAck,
    decide_true, Bool.and_self, if_true, hpk, bind_assoc, pure_bind, Option.map_some]
  rfl

/-- A send that emits a key encapsulated at the post-send responder epoch, which the state
had already recorded as received by the peer. -/
theorem send_emittedKey_peerAck (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (tI : ℕ) (k : K) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym)
    (hout : some (some (tI, k), ρ, tsnd, st') ∈ support (send role kem ecEk ecCt st)) :
    st'.res.resEpoch ∈ st.ack.ekRec ∧ st'.res.resEpoch + role.offset ∈ st.ack.ekRec := by
  rw [send, mem_support_bind_iff] at hout
  obtain ⟨out, hmem, hout⟩ := hout
  cases out with
  | none => simp at hout
  | some out =>
    rcases out with ⟨key, msg, epoch, state, rand⟩
    simp only [support_pure, Set.mem_singleton_iff, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hout
    unfold sendWith at hmem
    dsimp only at hmem
    repeat' first
      | split at hmem
      | (rw [mem_support_bind_iff] at hmem; obtain ⟨x, _, hmem⟩ := hmem)
    all_goals simp only [support_pure, Set.mem_singleton_iff,
      Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hmem
    all_goals obtain ⟨hkey, rfl, rfl, rfl, rfl⟩ := hmem
    all_goals first
      | exact hkey.elim
      | simp_all

end oppBiKemCKA
