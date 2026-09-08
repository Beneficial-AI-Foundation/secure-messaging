/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs
import SecureMessaging.ErasureCode.Defs
import ToVCVio.CryptoFoundations.KeyEncapMech

/-!
# Opp-BiKEM-CKA

Algorithms from Figures 17–18 of https://eprint.iacr.org/2025/2267.pdf.
A encapsulates in odd epochs and B in even epochs. Each party sends its next
public key before its ciphertext, overlapping the two directions of exchange.

Internal counters use integers because initialization uses the dummy epoch `-1`.
The SCKA interface uses natural epochs; dummy epochs never produce honest keys.
Acknowledgements are finite sets of integer indices, making the maximum sending
epoch computable. Secret keys are a finite association list, so erasure really
removes the corresponding entry and the vulnerable epoch set is computable.

We make the following corrections wrt the paper (more info in the docs)

1. Local-variable typos in Send-B and Rec-A (using B's responder
counter in Send-B and B's received ciphertext in Rec-A),
2. We use the existing KEM interface's
`(public key, secret key)` and `decaps secretKey ciphertext` order.
3. [The biggest change] We correct the public-key acknowledgement indices:
Send-A advertises `reqEpoch - 1` and
Send-B advertises `reqEpoch + 1` (line 21 in each figure).
Rec-A records the bit at the sender's `reqEpoch + 1`, and Rec-B at the sender's
`reqEpoch - 1` (line 8 in each figure). These are the entries set by peer-key
decoding; the printed indices prevent acknowledgement of the first public keys.
-/

open KEMScheme

universe u

namespace oppBiKemCKA

/-- A's offset is `+1`; B's is `-1`. This is the only role-dependent
arithmetic in the common send/receive algorithms. -/
-- ANCHOR: role
inductive Role where
  | A
  | B
  deriving DecidableEq

def Role.offset : Role → ℤ
  | .A => 1
  | .B => -1
-- ANCHOR_END: role

/-- The paper's per-message acknowledgement bits. -/
structure Ack where
  ekRec : Bool
  ctRec : Bool

/-- `ACK[t]` is represented by membership in two finite sets. -/
-- ANCHOR: acknowledgements
structure Acknowledgements where
  ekRec : Finset ℤ
  ctRec : Finset ℤ

/-- Largest nonnegative index with two adjacent acknowledged ciphertexts
(both t and t-1 in act.ctRec).
The empty maximum is zero; honest states initially acknowledge `-1` and `0`. -/
def Acknowledgements.sendingEpoch (ack : Acknowledgements) : ℕ :=
  (ack.ctRec.filter fun t => t - 1 ∈ ack.ctRec).sup Int.toNat
-- ANCHOR_END: acknowledgements

/-- Message `(ch, t_res, t_req, t_snd, ack, b)`; selector `0` means public
key and `1` means ciphertext. The explicit sending epoch survives delayed delivery. -/
-- ANCHOR: message
abbrev Bit := Fin 2

structure Message (Sym : Type) where
  ch : Option (ℕ × Sym)
  resEpoch : ℤ
  reqEpoch : ℤ
  sendingEpoch : ℕ
  ack : Ack
  bit : Option Bit
-- ANCHOR_END: message

/-- Responder and requestor variables, flattened as in Opp-UniKEM's states.
`ekPeer` is the paper's sparse public-key array, with `none` at unused indices.
`dk` stores only present secret keys; updates replace any entry at that epoch. -/
-- ANCHOR: state
structure State (PK SK C Sym : Type) where
  resEpoch : ℤ
  ekPeer : ℤ → Option PK
  ct : Option C
  ich : ℕ
  reqEpoch : ℤ
  dk : List (ℤ × SK)
  ek : Option PK
  -- received_chunks corresponds L_ch in the paper
  received_chunks : Finset (ℕ × Sym)
  ack : Acknowledgements

abbrev StA := State
abbrev StB := State
-- ANCHOR_END: state

/-- Both randomized calls may run in a send on arbitrary input states.
Each absent component means that this send did not run that primitive.
Used for leak versions of the send operation-/
-- ANCHOR: sendRand
structure SendRand (KeygenRand EncapsRand : Type) where
  keygen : Option KeygenRand
  encaps : Option EncapsRand
-- ANCHOR_END: sendRand

section Construction

variable {m : Type → Type u} [Monad m] {K PK SK C Sym : Type}

-- ANCHOR: initKeyGen
def initKeyGen : m Unit := pure ()
-- ANCHOR_END: initKeyGen

/-- Dummy ciphertexts `-1` and `0` are acknowledged to enable the first send. -/
-- ANCHOR: init
def init (role : Role) (_ik : Unit) : m (State PK SK C Sym) :=
  pure { resEpoch := if role = .A then -1 else 0
         reqEpoch := if role = .A then 0 else -1
         ekPeer := fun _ => none
         ct := none, ich := 0, dk := [], ek := none, received_chunks := ∅
         ack := { ekRec := ∅, ctRec := {-1, 0} } }
-- ANCHOR_END: init

-- ANCHOR: initA
def initA : Unit → m (StA PK SK C Sym) := init .A
-- ANCHOR_END: initA

-- ANCHOR: initB
def initB : Unit → m (StB PK SK C Sym) := init .B
-- ANCHOR_END: initB

/-- Only stored decapsulation keys expose epoch keys. Dummy indices are excluded. -/
-- ANCHOR: vuln
def vuln (st : State PK SK C Sym) : Finset ℕ :=
  ((st.dk.map Prod.fst).toFinset.filter fun t => 0 < t).image Int.toNat

def vulnA (st : StA PK SK C Sym) : Finset ℕ := vuln st

def vulnB (st : StB PK SK C Sym) : Finset ℕ := vuln st
-- ANCHOR_END: vuln

/-- Attach the two acknowledgement bits with their requestor-epoch meaning. -/
def message (role : Role) (st : State PK SK C Sym)
    (ch : Option (ℕ × Sym)) (bit : Option Bit) : Message Sym :=
  { ch, bit, resEpoch := st.resEpoch, reqEpoch := st.reqEpoch
    sendingEpoch := st.ack.sendingEpoch
    ack := { ekRec := decide (st.reqEpoch - role.offset ∈ st.ack.ekRec)
             ctRec := decide (st.reqEpoch ∈ st.ack.ctRec) } }

/-- Common send algorithm. Supplying the randomized primitives explicitly lets
ordinary and leaking sends share the same state transitions. -/
-- ANCHOR: sendWith
def sendWith {RKey REnc : Type} (role : Role)
    (keygen : m ((PK × SK) × RKey)) (encaps : PK → m ((C × K) × REnc))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
      SendRand RKey REnc)) := do
  let (st, rKey?) ←
    if st.ek.isNone && decide (st.resEpoch ∈ st.ack.ctRec ∧
        st.resEpoch + role.offset ∈ st.ack.ctRec) then do
      let ((ek, dk), rKey) ← keygen
      let t := st.resEpoch + 2
      let keyEpoch := t + role.offset
      pure ({ st with resEpoch := t, ich := 0, ek := some ek
                      dk := (keyEpoch, dk) :: st.dk.filter (fun p => p.1 != keyEpoch) },
            some rKey)
    else pure (st, none)
  let (key?, ch?, bit?, st, rEnc?) ←
    if st.resEpoch + role.offset ∉ st.ack.ekRec then do
      let ich := st.ich + 1
      let ch? := st.ek.map (fun ek => ecEk.encode ek ich)
      pure (none, ch?, some (0 : Bit), { st with ich }, none)
    else if st.resEpoch ∉ st.ack.ctRec then do
      let (key?, st, rEnc?) ←
        if st.ct.isNone && decide (st.resEpoch ∈ st.ack.ekRec) then
          match st.ekPeer st.resEpoch with
          | none => pure (none, st, none)
          | some ekPeer => do
              let ((ct, key), rEnc) ← encaps ekPeer
              pure (some (st.resEpoch.toNat, key), { st with ct := some ct, ich := 0 },
                some rEnc)
        else pure (none, st, none)
      let ich := st.ich + 1
      let ch? := st.ct.map (fun ct => ecCt.encode ct ich)
      pure (key?, ch?, some (1 : Bit), { st with ich }, rEnc?)
    else pure (none, none, none, st, none)
  let ρ := message role st ch? bit?
  pure (some (key?, ρ, ρ.sendingEpoch, st, { keygen := rKey?, encaps := rEnc? }))
-- ANCHOR_END: sendWith

/-- Ordinary send: dummy `Unit` coins are discarded. -/
-- ANCHOR: send
def send (role : Role) (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym)) := do
  let out ← sendWith role
    (do let keys ← kem.keygen; pure (keys, ()))
    (fun pk => do let out ← kem.encaps pk; pure (out, ())) ecEk ecCt st
  pure (out.map fun (key?, ρ, t, st, _) => (key?, ρ, t, st))
-- ANCHOR_END: send

-- ANCHOR: sendA
def sendA (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) := send .A kem ecEk ecCt stA
-- ANCHOR_END: sendA

-- ANCHOR: sendB
def sendB (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) := send .B kem ecEk ecCt stB
-- ANCHOR_END: sendB

-- ANCHOR: sendArleak
def sendArleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stA : StA PK SK C Sym) :=
  sendWith .A leak.keygenRleak leak.encapsRleak ecEk ecCt stA
-- ANCHOR_END: sendArleak

-- ANCHOR: sendBrleak
def sendBrleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stB : StB PK SK C Sym) :=
  sendWith .B leak.keygenRleak leak.encapsRleak ecEk ecCt stB
-- ANCHOR_END: sendBrleak

/-- Common receive algorithm. A stale payload is ignored, but its explicitly
indexed acknowledgements are retained. Decapsulation failure does not acknowledge
receipt of an epoch key or erase the secret key needed to recover it.
TODO: When it comes to proving, how do we make sure that there is no decapsulation failure?
-/
-- ANCHOR: recv
def recv (role : Role) (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × State PK SK C Sym) :=
  let ack := st.ack
  let ack := if ρ.ack.ctRec then { ack with ctRec := insert ρ.reqEpoch ack.ctRec } else ack
  let ack := if ρ.ack.ekRec then
      { ack with ekRec := insert (ρ.reqEpoch + role.offset) ack.ekRec } else ack
  let st := { st with ack }
  if ρ.resEpoch < st.reqEpoch then
  -- outdated message
    some (none, ρ.sendingEpoch, st)
  else
    let st := if st.reqEpoch < ρ.resEpoch
              -- first message of the new epoch
              then { st with reqEpoch := st.reqEpoch + 2 }
              else st
    -- Captures the relation of "1 removed" epochs
    --   - if A is requesting the key for epoch t, it receives B's public key for t-1
    --   - if B is requesting the key for epoch t, it receives A's public key for t+1
    let peerKeyEpoch := st.reqEpoch - role.offset
    let (key?, st) :=
      match ρ.bit, ρ.ch with
      | some 0, some ch =>
          if (st.ekPeer peerKeyEpoch).isNone then
            let received_chunks := insert ch st.received_chunks
            match ecEk.decode received_chunks with
            | none => (none, { st with received_chunks })
            | some ekPeer =>
                (none, { st with received_chunks := ∅
                                 ekPeer := Function.update st.ekPeer peerKeyEpoch (some ekPeer)
                                 ack := { st.ack with ekRec := insert peerKeyEpoch st.ack.ekRec } })
          else (none, st)
      | some 1, some ch =>
          if st.reqEpoch ∉ st.ack.ctRec then
            match st.dk.lookup st.reqEpoch with
            | none => (none, st)
            | some dk =>
                let received_chunks := insert ch st.received_chunks
                match ecCt.decode received_chunks with
                | none => (none, { st with received_chunks })
                | some ct =>
                    match hDet.decapsDet dk ct with
                    | none => (none, st)
                    | some key =>
                        (some (st.reqEpoch.toNat, key),
                          { st with received_chunks := ∅
                                    dk := st.dk.filter (fun p => p.1 != st.reqEpoch)
                                    ack := { st.ack with
                                      ctRec := insert st.reqEpoch st.ack.ctRec } })
          else (none, st)
      | _, _ => (none, st)
    -- deleting the stored material that has been fully delivered
    let st := if st.resEpoch ∈ st.ack.ctRec then { st with ct := none } else st
    let st := if st.resEpoch + role.offset ∈ st.ack.ekRec then { st with ek := none } else st
    some (key?, ρ.sendingEpoch, st)
-- ANCHOR_END: recv

-- ANCHOR: recvA
def recvA (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) (ρ : Message Sym) := recv .A kem hDet ecEk ecCt stA ρ
-- ANCHOR_END: recvA

-- ANCHOR: recvB
def recvB (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) (ρ : Message Sym) := recv .B kem hDet ecEk ecCt stB ρ
-- ANCHOR_END: recvB

-- ANCHOR: scheme
def scheme (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    SCKAScheme m Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) where
  initKeyGen := initKeyGen
  initA := initA
  initB := initB
  sendA := sendA kem ecEk ecCt
  sendArleak := sendArleak kem ecEk ecCt leak
  recvA := recvA kem hDet ecEk ecCt
  sendB := sendB kem ecEk ecCt
  sendBrleak := sendBrleak kem ecEk ecCt leak
  recvB := recvB kem hDet ecEk ecCt
-- ANCHOR_END: scheme

end Construction
end oppBiKemCKA
