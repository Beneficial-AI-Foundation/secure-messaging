/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Sampling
import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# Executable masked KEM reduction

The simulator retains observable fields while omitting the selected decapsulation key and
encapsulation state. This module defines its operations and adversary only; correspondence,
installation arguments and analytical bad-event estimates belong to downstream modules.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

/-- The seven party-state positions that would retain the selected decapsulation key or
encapsulation state, each without that secret. The epoch is selected and authentication is unit. -/
inductive Masked (P : Parameters ProbComp) where
  /-- `keysSampled` without the decapsulation key. -/
  | keysSampled (vec : P.inc.PKvector) (enc : EncoderState (P.inc.PKheader × P.Mac) P.Sym)
  /-- `headerSent` without the decapsulation key. -/
  | headerSent (dec : DecoderState P.inc.C₁ P.Sym) (enc : EncoderState P.inc.PKvector P.Sym)
  /-- `ct1Received` without the decapsulation key. -/
  | ct1Received (ct1 : P.inc.C₁) (enc : EncoderState P.inc.PKvector P.Sym)
  /-- `ekSentCt1Received` without the decapsulation key. -/
  | ekSentCt1Received (ct1 : P.inc.C₁) (dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym)
  /-- `ct1Sampled` without the encapsulation state. -/
  | ct1Sampled (hdr : P.inc.PKheader) (ct1 : P.inc.C₁) (enc : EncoderState P.inc.C₁ P.Sym)
      (dec : DecoderState P.inc.PKvector P.Sym)
  /-- `ekReceivedCt1Sampled` without the encapsulation state. -/
  | ekReceivedCt1Sampled (ct1 : P.inc.C₁) (hdr : P.inc.PKheader) (vec : P.inc.PKvector)
      (enc : EncoderState P.inc.C₁ P.Sym)
  /-- `ct1Acknowledged` without the encapsulation state. -/
  | ct1Acknowledged (hdr : P.inc.PKheader) (ct1 : P.inc.C₁)
      (dec : DecoderState P.inc.PKvector P.Sym)

/-- A party state of the simulator: an ordinary state, or a masked state of the selected epoch. -/
abbrev SimParty (P : Parameters ProbComp) := State P Unit ⊕ Masked P

/-- The game state of the simulator: the party states, key and message tables, send counters and
the exposed and challenged epochs. It keeps no correctness bookkeeping. -/
structure SimGame (P : Parameters ProbComp) where
  /-- A's state. -/
  stA : SimParty P
  /-- B's state. -/
  stB : SimParty P
  /-- A's key table. -/
  keyA : ℕ → Option P.EpochKey
  /-- B's key table. -/
  keyB : ℕ → Option P.EpochKey
  /-- A's sent messages with their sending epochs. -/
  msgA : ℕ → Option (Message P.Sym × ℕ)
  /-- B's sent messages with their sending epochs. -/
  msgB : ℕ → Option (Message P.Sym × ℕ)
  /-- The number of messages A has sent. -/
  nA : ℕ
  /-- The number of messages B has sent. -/
  nB : ℕ
  /-- The exposed epochs. -/
  exposed : Finset ℕ
  /-- The challenged epochs. -/
  challenged : Finset ℕ

/-- The state of the simulator: its game and the records of the samples it drew itself. -/
structure SimState (P : Parameters ProbComp) where
  /-- The game state. -/
  game : SimGame P
  /-- The key pairs and first-stage encapsulations the simulator sampled itself. -/
  transcript : ℕ → EpochTranscript P

/-- The public challenge supplied to the KEM reduction: the public key, the two ciphertext parts
and the test key. -/
structure Challenge (P : Parameters ProbComp) where
  /-- The challenge public key. -/
  pk : P.PK
  /-- The first part of the challenge ciphertext. -/
  ct1 : P.inc.C₁
  /-- The second part of the challenge ciphertext. -/
  ct2 : P.inc.C₂
  /-- The test key, real or uniform. -/
  key : P.K

/-- The state of `party` in the simulator. -/
def SimGame.stateAt (g : SimGame P) (party : Bool) : SimParty P :=
  if party then g.stA else g.stB

/-- A key table after recording an optional output key. -/
def keyUpdate (keys : ℕ → Option P.EpochKey) : Option (ℕ × P.EpochKey) → ℕ → Option P.EpochKey
  | none => keys
  | some (t, k) => Function.update keys t (some k)

/-- The simulator's game after a send of `party`. -/
def SimGame.sendUpdate (g : SimGame P) (party : Bool) (key : Option (ℕ × P.EpochKey))
    (msg : Message P.Sym) (tsnd : ℕ) (st : SimParty P) : SimGame P :=
  if party then
    { g with
      stA := st, keyA := keyUpdate g.keyA key
      msgA := Function.update g.msgA (g.nA + 1) (some (msg, tsnd)), nA := g.nA + 1 }
  else
    { g with
      stB := st, keyB := keyUpdate g.keyB key
      msgB := Function.update g.msgB (g.nB + 1) (some (msg, tsnd)), nB := g.nB + 1 }

/-- The simulator's game after a receive of `party`. -/
def SimGame.recvUpdate (g : SimGame P) (party : Bool) (key : Option (ℕ × P.EpochKey))
    (st : SimParty P) : SimGame P :=
  if party then { g with stA := st, keyA := keyUpdate g.keyA key }
  else { g with stB := st, keyB := keyUpdate g.keyB key }

/-- The masked view of a party state for the selected epoch `e`. -/
def maskState (e : ℕ) : State P Unit → SimParty P
  | .keysSampled t a sk vec enc =>
      if t = e then .inr (.keysSampled vec enc) else .inl (.keysSampled t a sk vec enc)
  | .headerSent t a sk dec enc =>
      if t = e then .inr (.headerSent dec enc) else .inl (.headerSent t a sk dec enc)
  | .ct1Received t a sk ct1 enc =>
      if t = e then .inr (.ct1Received ct1 enc) else .inl (.ct1Received t a sk ct1 enc)
  | .ekSentCt1Received t a sk ct1 dec =>
      if t = e then .inr (.ekSentCt1Received ct1 dec)
      else .inl (.ekSentCt1Received t a sk ct1 dec)
  | .ct1Sampled t a hdr es ct1 enc dec =>
      if t = e then .inr (.ct1Sampled hdr ct1 enc dec)
      else .inl (.ct1Sampled t a hdr es ct1 enc dec)
  | .ekReceivedCt1Sampled t a es ct1 hdr vec enc =>
      if t = e then .inr (.ekReceivedCt1Sampled ct1 hdr vec enc)
      else .inl (.ekReceivedCt1Sampled t a es ct1 hdr vec enc)
  | .ct1Acknowledged t a hdr es ct1 dec =>
      if t = e then .inr (.ct1Acknowledged hdr ct1 dec)
      else .inl (.ct1Acknowledged t a hdr es ct1 dec)
  | st => .inl st

/-- A masked state's exposure footprint: its own epoch, the selected epoch. -/
def simVuln (e : ℕ) : SimParty P → Finset ℕ
  | .inl st => vuln st
  | .inr _ => {e}

/-- The corruption reply of a simulator state: the state itself if it is not masked. -/
def unmask : SimParty P → Option (State P Unit)
  | .inl st => some st
  | .inr _ => none

/-- The send of a masked state of epoch `e`: its next chunk and successor state. -/
def maskedSend (e : ℕ) : Masked P → Message P.Sym × Masked P
  | .keysSampled vec enc =>
      ({ epoch := e, type := .hdr, data := some enc.nextChunk.1 },
        .keysSampled vec enc.nextChunk.2)
  | .headerSent dec enc =>
      ({ epoch := e, type := .ek, data := some enc.nextChunk.1 },
        .headerSent dec enc.nextChunk.2)
  | .ct1Received ct1 enc =>
      ({ epoch := e, type := .ekCt1Ack, data := some enc.nextChunk.1 },
        .ct1Received ct1 enc.nextChunk.2)
  | .ekSentCt1Received ct1 dec =>
      ({ epoch := e, type := .none, data := none }, .ekSentCt1Received ct1 dec)
  | .ct1Sampled hdr ct1 enc dec =>
      ({ epoch := e, type := .ct1, data := some enc.nextChunk.1 },
        .ct1Sampled hdr ct1 enc.nextChunk.2 dec)
  | .ekReceivedCt1Sampled ct1 hdr vec enc =>
      ({ epoch := e, type := .ct1, data := some enc.nextChunk.1 },
        .ekReceivedCt1Sampled ct1 hdr vec enc.nextChunk.2)
  | .ct1Acknowledged hdr ct1 dec =>
      ({ epoch := e, type := .none, data := none }, .ct1Acknowledged hdr ct1 dec)

/-- The receive of a masked state of epoch `e`: the receive of the corresponding state, with the
challenge's second ciphertext part `ct2` in place of the second encapsulation stage, and the
derived test key `v` as the key where the generator completes epoch `e`. -/
def maskedRecv (P : Parameters ProbComp) [DecidableEq P.Sym] (hMac : P.Mac = Unit) (e : ℕ)
    (ct2 : P.inc.C₂) (v : P.EpochKey) (m : Masked P) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × SimParty P) :=
  let ignore : Option (Option (ℕ × P.EpochKey) × ℕ × SimParty P) :=
    some (none, msg.epoch - 1, .inr m)
  let ct2Sampled (ct1 : P.inc.C₁) : SimParty P :=
    .inl (.ct2Sampled e () (EncoderState.init P.ecpCt2
      (ct2, (auth P hMac).macCiphertext () e (ct1, ct2))))
  if !msg.wellFormed then ignore
  else match m with
    | .keysSampled vec _ =>
        match msg.type, msg.data with
        | .ct1, some chunk =>
            if msg.epoch = e then some (none, msg.epoch - 1, .inr (.headerSent
              ((DecoderState.empty P.ecpCt1).addChunk chunk) (EncoderState.init P.ecpEk vec)))
            else ignore
        | _, _ => ignore
    | .headerSent dec enc =>
        match msg.type, msg.data with
        | .ct1, some chunk =>
            if msg.epoch = e then
              match (dec.addChunk chunk).decodedPayload with
              | some ct1 => some (none, msg.epoch - 1, .inr (.ct1Received ct1 enc))
              | none => some (none, msg.epoch - 1, .inr (.headerSent (dec.addChunk chunk) enc))
            else ignore
        | _, _ => ignore
    | .ct1Received ct1 _ =>
        match msg.type, msg.data with
        | .ct2, some chunk =>
            if msg.epoch = e then some (none, msg.epoch - 1, .inr (.ekSentCt1Received ct1
              ((DecoderState.empty P.ecpCt2).addChunk chunk)))
            else ignore
        | _, _ => ignore
    | .ekSentCt1Received ct1 dec =>
        match msg.type, msg.data with
        | .ct2, some chunk =>
            if msg.epoch = e then
              match (dec.addChunk chunk).decodedPayload with
              | some _ => some (some (e, v), msg.epoch - 1,
                  .inl (.noHeaderReceived (e + 1) () (DecoderState.empty P.ecpHdr)))
              | none => some (none, msg.epoch - 1,
                  .inr (.ekSentCt1Received ct1 (dec.addChunk chunk)))
            else ignore
        | _, _ => ignore
    | .ct1Sampled hdr ct1 enc dec =>
        match msg.type, msg.data with
        | .ek, some chunk =>
            if msg.epoch = e then
              match (dec.addChunk chunk).decodedPayload with
              | some vec =>
                  if P.inc.validPK hdr vec then
                    some (none, msg.epoch - 1, .inr (.ekReceivedCt1Sampled ct1 hdr vec enc))
                  else none
              | none => some (none, msg.epoch - 1,
                  .inr (.ct1Sampled hdr ct1 enc (dec.addChunk chunk)))
            else ignore
        | .ekCt1Ack, some chunk =>
            if msg.epoch = e then
              match (dec.addChunk chunk).decodedPayload with
              | some vec =>
                  if P.inc.validPK hdr vec then some (none, msg.epoch - 1, ct2Sampled ct1)
                  else none
              | none => some (none, msg.epoch - 1,
                  .inr (.ct1Acknowledged hdr ct1 (dec.addChunk chunk)))
            else ignore
        | _, _ => ignore
    | .ekReceivedCt1Sampled ct1 _ _ _ =>
        match msg.type, msg.data with
        | .ekCt1Ack, some _ =>
            if msg.epoch = e then some (none, msg.epoch - 1, ct2Sampled ct1) else ignore
        | _, _ => ignore
    | .ct1Acknowledged hdr ct1 dec =>
        match msg.type, msg.data with
        | .ekCt1Ack, some chunk =>
            if msg.epoch = e then
              match (dec.addChunk chunk).decodedPayload with
              | some vec =>
                  if P.inc.validPK hdr vec then some (none, msg.epoch - 1, ct2Sampled ct1)
                  else none
              | none => some (none, msg.epoch - 1,
                  .inr (.ct1Acknowledged hdr ct1 (dec.addChunk chunk)))
            else ignore
        | _, _ => ignore

/-- The joint send sample of an ordinary party state with its records, without a bad flag. -/
def ghostSample (P : Parameters ProbComp) (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc) (T : ℕ → EpochTranscript P) (st : State P Unit) :
    ProbComp ((SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      (ℕ → EpochTranscript P)) :=
  match st with
  | .keysUnsampled t a => (fun x : (P.PK × P.SK) × irl.KeygenRand =>
      ((keygenStep P hMac t a x.1.1 x.1.2, SendRand.keygen x.2),
        Function.update T t { (T t) with keypair := some x.1 })) <$> irl.keygenRleak
  | .headerReceived t a hdr dec => (fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
      ((encaps1Step P hMac t a hdr dec x.1.1 x.1.2.1 x.1.2.2, SendRand.encaps1 x.2),
        Function.update T t { (T t) with encaps1 := some x.1 })) <$> irl.encaps1Rleak hdr
  | st => (fun out => (out, T)) <$> MLKEMBraid.sendRleak P irl (auth P hMac) st

/-- The send of an ordinary state of the selected epoch `e` that samples, with the challenge
installed: key generation installs the challenge public key, and first-stage encapsulation the
first challenge ciphertext part with the derived test key `v`. -/
def targetSend (P : Parameters ProbComp) (hMac : P.Mac = Unit) (e : ℕ) (ch : Challenge P)
    (v : P.EpochKey) : State P Unit → Option (Message P.Sym × Masked P × Option (ℕ × P.EpochKey))
  | .keysUnsampled t a =>
      if t = e then
        some ({ epoch := t, type := .hdr, data := some (hdrChunk P hMac t a ch.pk).1 },
          .keysSampled (P.inc.toVector ch.pk) (hdrChunk P hMac t a ch.pk).2, none)
      else none
  | .headerReceived t _ hdr dec =>
      if t = e then
        some ({ epoch := t, type := .ct1, data := some (ct1Chunk P ch.ct1).1 },
          .ct1Sampled hdr ch.ct1 (ct1Chunk P ch.ct1).2 dec, some (t, v))
      else none
  | _ => none

/-- A send of `party` in the simulator. A masked state sends its next chunk. An ordinary state of
the selected epoch that samples uses the installed challenge (`targetSend`); its leaking send is
refused as in the trace game, or else accepted only to expose `e`, without coins. Every other
send is the trace send with its records, without a bad flag. -/
def simSend (P : Parameters ProbComp) (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc) (e : ℕ) (ch : Challenge P) (party leaking : Bool) :
    StateT (SimState P) ProbComp
      (Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand)) :=
  fun s => match s.game.stateAt party with
    | .inr m =>
        pure (some (e - 1, none, (maskedSend e m).1, SendRand.none),
          { s with
            game := s.game.sendUpdate party none (maskedSend e m).1 (e - 1)
              (.inr (maskedSend e m).2) })
    | .inl st =>
        match targetSend P hMac e ch (P.kdfOK ch.key e) st with
        | some (msg, m, key) =>
            if leaking && decide ({e} ∩ s.game.challenged ≠ ∅) then pure (none, s)
            else pure (if leaking then none
                else some (e - 1, key.map Prod.fst, msg, SendRand.none),
              { s with
                game := { s.game.sendUpdate party key msg (e - 1) (.inr m) with
                  exposed := if leaking then s.game.exposed ∪ {e} else s.game.exposed } })
        | none =>
            (fun w : (SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand) ×
                (ℕ → EpochTranscript P) =>
              if leaking && decide ((exposure P irl).send st w.1.1.state w.1.2 ∩
                  s.game.challenged ≠ ∅) then (none, s)
              else (some (w.1.1.sendingEpoch, w.1.1.outputKey.map Prod.fst, w.1.1.msg, w.1.2),
                { game := { s.game.sendUpdate party w.1.1.outputKey w.1.1.msg w.1.1.sendingEpoch
                      (.inl w.1.1.state) with
                    exposed := if leaking then
                      s.game.exposed ∪ (exposure P irl).send st w.1.1.state w.1.2
                    else s.game.exposed },
                  transcript := w.2 })) <$> ghostSample P hMac irl s.transcript st

/-- The receive of a simulator party state: the repaired receive of an ordinary state with the
simulator's records, and `maskedRecv` for a masked state. -/
def simRecv (P : Parameters ProbComp) [DecidableEq P.Sym] (hMac : P.Mac = Unit) (e : ℕ)
    (ch : Challenge P) (v : P.EpochKey) (T : ℕ → EpochTranscript P) (st : SimParty P)
    (msg : Message P.Sym) : Option (Option (ℕ × P.EpochKey) × ℕ × SimParty P) :=
  match st with
  | .inl st => (repairedRecv P hMac true T st msg).map fun r => (r.1, r.2.1, .inl r.2.2)
  | .inr m => maskedRecv P hMac e ch.ct2 v m msg

/-- The receive oracle of `party` in the simulator. -/
def simReceive (P : Parameters ProbComp) [DecidableEq P.Sym] (hMac : P.Mac = Unit) (e : ℕ)
    (ch : Challenge P) (party : Bool) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ)) (StateT (SimState P) ProbComp) :=
  fun n s =>
    match (if party then s.game.msgB else s.game.msgA) n with
    | none => pure (none, s)
    | some (msg, _) =>
        match simRecv P hMac e ch (P.kdfOK ch.key e) s.transcript (s.game.stateAt party) msg with
        | none => pure (none, s)
        | some (key, trcv, st') =>
            pure (some (trcv, key.map Prod.fst),
              { s with game := s.game.recvUpdate party key st' })

/-- The available key of epoch `t` in the simulator: A's key, else B's. -/
def simLookup (g : SimGame P) (t : ℕ) : Option P.EpochKey :=
  match g.keyA t with
  | some k => some k
  | none => g.keyB t

/-- The challenge oracle of the simulator: every challenge follows `mode`. -/
def simChallenge (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
    (mode : ℕ → Mode) : QueryImpl (ℕ →ₒ Option P.EpochKey) (StateT (SimState P) ProbComp) :=
  fun t s =>
    if t ∈ s.game.exposed ∨ t ∈ s.game.challenged then pure (none, s)
    else match simLookup s.game t with
      | none => pure (none, s)
      | some k => (fun out => (some out, { s with game :=
          { s.game with challenged := insert t s.game.challenged } })) <$>
          challengeValue P (mode t) t k

/-- The corruption oracle of `party` in the simulator; a masked state is never disclosed. -/
def simCorrupt (P : Parameters ProbComp) (e : ℕ) (party : Bool) :
    QueryImpl (Unit →ₒ Option (State P Unit)) (StateT (SimState P) ProbComp) :=
  fun _ s =>
    if simVuln e (s.game.stateAt party) ∩ s.game.challenged ≠ ∅ then pure (none, s)
    else pure (unmask (s.game.stateAt party), { s with game :=
      { s.game with exposed := s.game.exposed ∪ simVuln e (s.game.stateAt party) } })

/-- The uniform-randomness oracle of the simulator. -/
def simUnif (P : Parameters ProbComp) : QueryImpl unifSpec (StateT (SimState P) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SimState P) ProbComp)

/-- The ordinary send oracle of `party` in the simulator. -/
def simPlain (P : Parameters ProbComp) (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc) (e : ℕ) (ch : Challenge P) (party : Bool) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Message P.Sym)) (StateT (SimState P) ProbComp) :=
  fun _ => (fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
    simSend P hMac irl e ch party false

/-- The leaking send oracle of `party` in the simulator. -/
def simLeak (P : Parameters ProbComp) (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc) (e : ℕ) (ch : Challenge P) (party : Bool) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Message P.Sym ×
      SendRand irl.KeygenRand irl.Encaps1Rand)) (StateT (SimState P) ProbComp) :=
  fun _ => simSend P hMac irl e ch party true

/-- The masked simulation of the security interface for the selected epoch `e` with the
challenge `ch`. Earlier epochs are challenged with uniform keys and the others with their keys;
the key of `e` is the derived test key. -/
def simImpl (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) (e : ℕ) (ch : Challenge P) :
    QueryImpl (Spec P irl) (StateT (SimState P) ProbComp) :=
  simUnif P + simPlain P hMac irl e ch true + simPlain P hMac irl e ch false +
    simReceive P hMac e ch true + simReceive P hMac e ch false +
    simLeak P hMac irl e ch true + simLeak P hMac irl e ch false +
    simChallenge P (fun t => if t < e then .uniform else .real) +
    simCorrupt P e true + simCorrupt P e false

/-- The initial state of the simulator: the literal initial states, no keys, messages or
records. -/
def simInit (P : Parameters ProbComp) (hMac : P.Mac = Unit) : SimState P :=
  { game :=
      { stA := .inl (MLKEMBraid.initA P (auth P hMac) ())
        stB := .inl (MLKEMBraid.initB P (auth P hMac) ())
        keyA := fun _ => none, keyB := fun _ => none
        msgA := fun _ => none, msgB := fun _ => none
        nA := 0, nB := 0, exposed := ∅, challenged := ∅ }
    transcript := fun _ => { keypair := none, encaps1 := none } }

/-- Stop the simulator when the selected epoch `e` is exposed. -/
def simStop (e : ℕ) (s : SimState P) : Bool :=
  decide (e ∈ s.game.exposed)

/-- **`kemReduction`**: the IND-CPA adversary for epoch `e`. For `e = 0` it returns `false`.
Otherwise its first phase keeps the challenge public key, and its second phase runs `A` once
against the masked simulation `simImpl` of the stopped repaired game, with the challenge public
key, ciphertext parts and test key installed at epoch `e`; it returns `A`'s bit, or `false` when
`e` becomes exposed. The simulator never compares epoch keys, so no decidable equality of epoch
keys is required. -/
def kemReduction (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (e : ℕ) : P.kem.IND_CPA_Adversary :=
  match e with
  | 0 =>
      { State := Unit, preChallenge := fun _ => pure ()
        postChallenge := fun _ _ _ => pure false }
  | e + 1 =>
      { State := P.PK
        preChallenge := fun pk => pure pk
        postChallenge := fun pk c k => stoppedRun
          (simImpl P hMac irl (e + 1) ⟨pk, (P.inc.splitC c).1, (P.inc.splitC c).2, k⟩)
          (simStop (e + 1)) A (simInit P hMac) }

end MLKEMBraid.NoAuth
