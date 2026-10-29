/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Construction

/-!
# Opp-BiKEM-CKA — Decision-tree form of `recv`

`recv` follows the paper with `let mut` and early `return`, which elaborates to a deeply
nested term. `recvSpec` is the same function, re-written as a plain decision tree over named
intermediate values (`recvAck`, `recvReq`, `recvFinish`), and `recv_eq_recvSpec` proves the
two agree. Every later fact about a receive is read off `recvSpec` with one case split per
named condition instead of a brute-force split of the elaborated `do` block.
-/

open KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Acknowledgements after ingesting the message's flags: a set public-key flag adds
`ρ.tReq + role.offset` to `ekRec`, a set ciphertext flag adds `ρ.tReq` to `ctRec`. -/
def recvAck (role : Role) (ack : Acknowledgements) (ρ : Message Sym) : Acknowledgements :=
  { ekRec := if ρ.ack.ekRec = true then insert (ρ.tReq + role.offset) ack.ekRec else ack.ekRec
    ctRec := if ρ.ack.ctRec = true then insert ρ.tReq ack.ctRec else ack.ctRec }

/-- The requester epoch after a non-stale message: advanced by two if the message is ahead. -/
def recvReq (st : State PK SK C Sym) (ρ : Message Sym) : ℤ :=
  if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2 else st.req.reqEpoch

/-- Assemble the post-receive state: the given requester epoch, peer keys, secret keys,
buffer of chunks, and acknowledgements. The acknowledged outgoing material is cleared. -/
def recvFinish (role : Role) (st : State PK SK C Sym) (q : ℤ) (ekPeer : ℤ → Option PK)
    (dk : List (ℤ × SK)) (chunks : Finset (ℕ × Sym)) (ack : Acknowledgements) :
    State PK SK C Sym :=
  { res := ⟨st.res.resEpoch, ekPeer,
      if st.res.resEpoch ∈ ack.ctRec then none else st.res.ct, st.res.ich⟩
    req := ⟨q, dk, if st.res.resEpoch + role.offset ∈ ack.ekRec then none else st.req.ek, chunks⟩
    ack := ack }

/-- `recvSpec` with decapsulation replaced by an arbitrary recovery function of the epoch, the
stored secret key and the decoded ciphertext. The real receive uses `fun _ sk c => hDet.decapsDet
sk c`; an ideal receive may ignore `sk` and `c` and read a key table instead. -/
def recvWith (role : Role) [DecidableEq Sym] (recover : ℤ → SK → C → Option K)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × State PK SK C Sym) :=
  let ack := recvAck role st.ack ρ
  if ρ.tRes < st.req.reqEpoch then
    some (none, ρ.sendingEpoch, { st with ack := ack })
  else
    let q := recvReq st ρ
    let pe := q - role.offset
    if (st.res.ekPeer pe).isNone = true ∧ ρ.bit = some 0 then
      match (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 with
      | none =>
          some (none, ρ.sendingEpoch,
            recvFinish role st q st.res.ekPeer st.req.dk
              (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).1 ack)
      | some pk =>
          some (none, ρ.sendingEpoch,
            recvFinish role st q (Function.update st.res.ekPeer pe (some pk)) st.req.dk ∅
              { ack with ekRec := insert pe ack.ekRec })
    else if q ∉ ack.ctRec ∧ ρ.bit = some 1 then
      match (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).2 with
      | none =>
          some (none, ρ.sendingEpoch,
            recvFinish role st q st.res.ekPeer st.req.dk
              (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).1 ack)
      | some c => do
          let sk ← st.req.dk.lookup q
          let k ← recover q sk c
          some (some (q.toNat, k), ρ.sendingEpoch,
            recvFinish role st q st.res.ekPeer (st.req.dk.filter (fun p => p.1 != q)) ∅
              { ack with ctRec := insert q ack.ctRec })
    else
      some (none, ρ.sendingEpoch,
        recvFinish role st q st.res.ekPeer st.req.dk st.req.receivedChunks ack)

/-- `recv` as a decision tree. -/
def recvSpec (role : Role) (kem : KEMScheme ProbComp K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × State PK SK C Sym) :=
  let ack := recvAck role st.ack ρ
  if ρ.tRes < st.req.reqEpoch then
    some (none, ρ.sendingEpoch, { st with ack := ack })
  else
    let q := recvReq st ρ
    let pe := q - role.offset
    if (st.res.ekPeer pe).isNone = true ∧ ρ.bit = some 0 then
      match (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 with
      | none =>
          some (none, ρ.sendingEpoch,
            recvFinish role st q st.res.ekPeer st.req.dk
              (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).1 ack)
      | some pk =>
          some (none, ρ.sendingEpoch,
            recvFinish role st q (Function.update st.res.ekPeer pe (some pk)) st.req.dk ∅
              { ack with ekRec := insert pe ack.ekRec })
    else if q ∉ ack.ctRec ∧ ρ.bit = some 1 then
      match (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).2 with
      | none =>
          some (none, ρ.sendingEpoch,
            recvFinish role st q st.res.ekPeer st.req.dk
              (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).1 ack)
      | some c => do
          let sk ← st.req.dk.lookup q
          let k ← hDet.decapsDet sk c
          some (some (q.toNat, k), ρ.sendingEpoch,
            recvFinish role st q st.res.ekPeer (st.req.dk.filter (fun p => p.1 != q)) ∅
              { ack with ctRec := insert q ack.ctRec })
    else
      some (none, ρ.sendingEpoch,
        recvFinish role st q st.res.ekPeer st.req.dk st.req.receivedChunks ack)

-- The equivalence is a uniform case split over every branch of the elaborated `do` block.
set_option maxHeartbeats 1000000 in -- about two hundred leaves closed by `rfl`
set_option linter.unusedSimpArgs false in
/-- `recv` agrees with its decision-tree description. -/
lemma recv_eq_recvSpec (role : Role) (kem : KEMScheme ProbComp K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    recv role kem hDet ecEk ecCt st ρ = recvSpec role kem hDet ecEk ecCt st ρ := by
  unfold recvSpec recvFinish recvReq recvAck
  rw [recv]
  dsimp only
  by_cases hct : ρ.ack.ctRec = true <;> by_cases hek : ρ.ack.ekRec = true <;>
    simp only [hct, hek, Bool.false_eq_true, ite_true, ite_false]
  all_goals by_cases hstale : ρ.tRes < st.req.reqEpoch <;>
    simp only [hstale, ite_true, ite_false]
  all_goals try rfl
  all_goals by_cases hadv : st.req.reqEpoch < ρ.tRes <;>
    simp only [hadv, ite_true, ite_false]
  all_goals
    cases hpk : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 <;>
    cases hctd : (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).2 <;>
    (try simp only [hpk, hctd, Option.pure_def])
  all_goals split_ifs <;> rfl

/-- `recvSpec` is `recvWith` for the KEM's deterministic decapsulation. -/
lemma recvSpec_eq_recvWith (role : Role) (kem : KEMScheme ProbComp K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    recvSpec role kem hDet ecEk ecCt st ρ =
      recvWith role (fun _ sk c => hDet.decapsDet sk c) ecEk ecCt st ρ :=
  rfl

/-- `recv` is `recvWith` for the KEM's deterministic decapsulation. -/
lemma recv_eq_recvWith (role : Role) (kem : KEMScheme ProbComp K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    recv role kem hDet ecEk ecCt st ρ =
      recvWith role (fun _ sk c => hDet.decapsDet sk c) ecEk ecCt st ρ :=
  (recv_eq_recvSpec role kem hDet ecEk ecCt st ρ).trans
    (recvSpec_eq_recvWith role kem hDet ecEk ecCt st ρ)

/-- Two recovery functions that agree on the epoch, secret key and ciphertext actually reached by
the ciphertext branch give the same receive. -/
lemma recvWith_eq_of_agree (role : Role) [DecidableEq Sym]
    (recover₁ recover₂ : ℤ → SK → C → Option K)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (hagree : ∀ sk c, ¬ ρ.tRes < st.req.reqEpoch → ρ.bit = some 1 →
      recvReq st ρ ∉ (recvAck role st.ack ρ).ctRec →
      st.req.dk.lookup (recvReq st ρ) = some sk →
      (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).2 = some c →
      recover₁ (recvReq st ρ) sk c = recover₂ (recvReq st ρ) sk c) :
    recvWith role recover₁ ecEk ecCt st ρ = recvWith role recover₂ ecEk ecCt st ρ := by
  dsimp only [recvWith]
  split_ifs with hst _ hg2 <;> try rfl
  cases hdec : (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).2 with
  | none => rfl
  | some c =>
    cases hlk : st.req.dk.lookup (recvReq st ρ) with
    | none => rfl
    | some sk =>
      simp only [Option.bind_eq_bind, Option.bind, hagree sk c hst hg2.2 hg2.1 hlk hdec]

/-- A successful `recvWith` keeps the responder epoch. -/
lemma recvWith_resEpoch (role : Role) [DecidableEq Sym] (recover : ℤ → SK → C → Option K)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recvWith role recover ecEk ecCt st ρ = some (key?, trcv, st')) :
    st'.res.resEpoch = st.res.resEpoch := by
  dsimp only [recvWith] at hout
  split_ifs at hout <;> (try split at hout) <;>
    (try (simp only [Option.some.injEq, Prod.mk.injEq] at hout; obtain ⟨-, -, rfl⟩ := hout; rfl))
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hout
  obtain ⟨sk, -, k, -, hout⟩ := hout
  simp only [Option.some.injEq, Prod.mk.injEq] at hout
  obtain ⟨-, -, rfl⟩ := hout
  rfl

end oppBiKemCKA
