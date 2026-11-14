/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Scheduled
public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Exposure
public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Games
public import SecureMessaging.SCKA.MLKEMBraid.Security.Games
public import SecureMessaging.SCKA.MLKEMBraid.Correctness.Invariant
public import SecureMessaging.SCKA.Security
public import ToVCVio.EvalDist.BoolDist

/-!
# Trace games of authenticated ML-KEM Braid

The security game of `scheme P S irl` is run again with extra bookkeeping. This module defines
that game, `traceImpl`, for a general authenticator state type `AS`.

The game keeps, for each epoch, a record of what it has decided for that epoch: the key pair, the
first-stage encapsulation, the epoch key output by the encapsulator, and the authenticator value
installed by the update of the epoch (`EpochRecord`). It reads three kinds of settings.

- A table `Installed` of values fixed before the run. An entry is read at exactly one query, the
  first query that needs it, and the value read is then written to the record.
- `Modes`, which say how an entry that is absent from the table is chosen: the real way, or
  uniformly at random.
- `UpdateRules`, which say how the game derives an epoch key and an authenticator value.

With an empty table and real modes, the game with `view := S.toRatcheted` is the security game of
`scheme P S irl`. With `repair`, the receiver that completes the second ciphertext of a recorded
encapsulation outputs the recorded key and installed authenticator value instead of decapsulating.
-/

@[expose] public section

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace MLKEMBraid.Auth

open Braid

/-- What the game has decided for one epoch: the key pair, the first-stage encapsulation, the
epoch key output at the first-stage encapsulation, and the authenticator value installed by the
update of the epoch. Epoch `0` holds the initial authenticator value. -/
structure EpochRecord (P : Parameters ProbComp) (AS : Type) where
  /-- The key pair of the epoch, if sampled. -/
  keypair : Option (P.PK × P.SK)
  /-- The encapsulation state, first ciphertext and KEM key of the epoch, if sampled. -/
  encaps1 : Option (P.inc.St × P.inc.C₁ × P.K)
  /-- The epoch key output by the encapsulator, if any. -/
  key : Option P.EpochKey
  /-- The authenticator value installed by the update of the epoch, if any. -/
  pair : Option AS

/-- Forget the epoch key and the authenticator value of a record. -/
def EpochRecord.toTranscript {P : Parameters ProbComp} {AS : Type} (r : EpochRecord P AS) :
    EpochTranscript P :=
  { keypair := r.keypair, encaps1 := r.encaps1 }

/-- Values fixed before a run. An absent entry is chosen by the game, by its mode. -/
structure Installed (P : Parameters ProbComp) (irl : P.kem.IncrementalRandLeak P.inc)
    (AS : Type) where
  /-- The key pair of an epoch, with the coins that generated it. -/
  kp : ℕ → Option ((P.PK × P.SK) × irl.KeygenRand)
  /-- The first-stage encapsulation of an epoch, with its coins. -/
  ec : ℕ → Option ((P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand)
  /-- The epoch key output at the first-stage encapsulation of an epoch. -/
  key : ℕ → Option P.EpochKey
  /-- The authenticator value installed by the update of an epoch; epoch `0` is the initial
  value. -/
  pair : ℕ → Option AS
  /-- The answer to an eligible challenge of an epoch. -/
  chal : ℕ → Option P.EpochKey

/-- The table with no entry. -/
def Installed.empty {P : Parameters ProbComp} {irl : P.kem.IncrementalRandLeak P.inc} {AS : Type} :
    Installed P irl AS where
  kp _ := none
  ec _ := none
  key _ := none
  pair _ := none
  chal _ := none

/-- How an epoch key that is absent from the table is chosen: from the shared secret, from a fresh
uniform shared secret, or uniformly. -/
inductive KeyMode where
  /-- The key derived from the sampled shared secret. -/
  | real
  /-- The key derived from a fresh uniform shared secret. -/
  | derivedUniform
  /-- A uniform key. -/
  | uniform

/-- How an authenticator value that is absent from the table is chosen: by the schedule, or
uniformly. -/
inductive PairMode where
  /-- The value given by the schedule. -/
  | real
  /-- A uniform root and an independent uniform MAC key. -/
  | uniform

/-- The modes of the entries of a run, epoch by epoch. -/
structure Modes where
  /-- How the epoch key of an epoch is chosen. -/
  key : ℕ → KeyMode
  /-- How the authenticator value of an epoch is chosen. -/
  pair : ℕ → PairMode
  /-- How an eligible challenge of an epoch is answered. -/
  chal : ℕ → Braid.NoAuth.Mode

/-- Every entry is chosen the real way. -/
def Modes.real : Modes where
  key _ := .real
  pair _ := .real
  chal _ := .real

/-- The modes of the real game, except that a challenge of an epoch `t ≤ j` is answered
uniformly. -/
def Modes.hybrid (j : ℕ) : Modes :=
  { Modes.real with chal := fun t => if t ≤ j then .uniform else .real }

/-- How the game derives an epoch key from the sampled shared secret, an authenticator value from
the previous one and the epoch key, and the initial authenticator value. -/
structure UpdateRules (P : Parameters ProbComp) (AS : Type) where
  /-- The epoch key of an epoch from its shared secret. -/
  key : ℕ → P.K → ProbComp P.EpochKey
  /-- The authenticator value of an epoch from the previous value and the epoch key. -/
  pair : ℕ → AS → P.EpochKey → ProbComp AS
  /-- The initial authenticator value. -/
  initPair : ProbComp AS

variable {P : Parameters ProbComp} {Root MacKey : Type} {AS : Type}

/-- The rules of the installed game: an installed entry is returned as it is, and any other entry
is chosen by its mode. -/
def installedRules [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root]
    [SampleableType MacKey] {irl : P.kem.IncrementalRandLeak P.inc}
    (S : ScheduledAuthenticator P Root MacKey) (tbl : Installed P irl (Root × MacKey))
    (modes : Modes) : UpdateRules P (Root × MacKey) where
  key t k := match tbl.key t with
    | some x => pure x
    | none => match modes.key t with
      | .real => pure (P.kdfOK k t)
      | .derivedUniform => (fun u => P.kdfOK u t) <$> ($ᵗ P.K)
      | .uniform => $ᵗ P.EpochKey
  pair t prev x := match tbl.pair t with
    | some p => pure p
    | none => match modes.pair t with
      | .real => pure (S.F t prev.1 x)
      | .uniform => do
          let r ← $ᵗ Root
          let m ← $ᵗ MacKey
          pure (r, m)
  initPair := match tbl.pair 0 with
    | some p => pure p
    | none => match modes.pair 0 with
      | .real => (fun ik => S.F 1 S.initRoot ik) <$> ($ᵗ P.EpochKey)
      | .uniform => do
          let r ← $ᵗ Root
          let m ← $ᵗ MacKey
          pure (r, m)

/-- `S.toRatcheted` with the epoch keys and authenticator values of the records `T` in place of
the computed ones. The initial key is read only if the initial value is not recorded. -/
def recorded [DecidableEq P.Mac] (S : ScheduledAuthenticator P Root MacKey)
    (T : ℕ → EpochRecord P (Root × MacKey)) :
    RatchetedAuthenticator P.EpochKey P.EpochKey (Root × MacKey)
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac :=
  { S.toRatcheted with
    init := fun ik e => (T 0).pair.getD (S.F e S.initRoot ik)
    update := fun s e k => (T e).pair.getD (S.F e s.1 ((T e).key.getD k)) }

/-- The exposure policy E⁺ for the authenticator state type `AS`: every corruption exposes the
stored epoch and its successor, and a leak of key-generation or first-stage encapsulation coins
exposes both. At `AS := Root × MacKey` this is `successorExposure P irl Root MacKey`. -/
def exposureAt (P : Parameters ProbComp) (irl : P.kem.IncrementalRandLeak P.inc) (AS : Type) :
    SCKAScheme.VulnerableEpochs (State P AS) (SendRand irl.KeygenRand irl.Encaps1Rand) where
  corrupt st := {st.epoch, st.epoch + 1}
  rleak st coins := match coins with
    | .none => ∅
    | .keygen _ | .encaps1 _ => {st.epoch, st.epoch + 1}

/-- The state of a trace game: the game state, the records, and a bad flag that stays set once it
is set. -/
structure TraceState (P : Parameters ProbComp) (AS : Type) where
  /-- The state of the security game. -/
  game : GameState P AS
  /-- The record of each epoch. The adversary never sees them. -/
  transcript : ℕ → EpochRecord P AS
  /-- Set at a first-stage encapsulation when decapsulation would not give the derived key. -/
  bad : Bool

/-- Run a game-state oracle on the `game` field, and keep the records and the bad flag. -/
def liftGame {α : Type} (c : StateT (GameState P AS) ProbComp α) :
    StateT (TraceState P AS) ProbComp α :=
  fun s => (fun z => (z.1, { s with game := z.2 })) <$> c.run s.game

/-- The leaking send of `party` with its records. At a key-generation or first-stage
encapsulation send it uses the installed sample if there is one and samples otherwise, records
the sample, and derives the epoch key and the authenticator value with `rules`. -/
def sampledSend [DecidableEq P.EpochKey] (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    (s : TraceState P AS) (party : Bool) :
    ProbComp ((SendResult P AS × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      (ℕ → EpochRecord P AS) × Bool) :=
  match s.game.stateAt party with
  | .keysUnsampled t a => do
      let x ← match tbl.kp t with
        | some x => pure x
        | none => irl.keygenRleak
      let hdr := P.inc.toHeader x.1.1
      let (chunk, enc) := (EncoderState.init P.ecpHdr (hdr, view.macHeader a t hdr)).nextChunk
      pure (({ msg := { epoch := t, type := .hdr, data := some chunk }
               sendingEpoch := t - 1, outputKey := none
               state := .keysSampled t a x.1.2 (P.inc.toVector x.1.1) enc },
             .keygen x.2),
        Function.update s.transcript t { (s.transcript t) with keypair := some x.1 }, s.bad)
  | .headerReceived t a hdr dec => do
      let x ← match tbl.ec t with
        | some x => pure x
        | none => irl.encaps1Rleak hdr
      let key ← rules.key t x.1.2.2
      let pair ← rules.pair t a key
      let (chunk, enc) := (EncoderState.init P.ecpCt1 x.1.2.1).nextChunk
      pure (({ msg := { epoch := t, type := .ct1, data := some chunk }
               sendingEpoch := t - 1, outputKey := some (t, key)
               state := .ct1Sampled t pair hdr x.1.1 x.1.2.1 enc dec },
             .encaps1 x.2),
        Function.update s.transcript t
          { (s.transcript t) with encaps1 := some x.1, key := some key, pair := some pair },
        match (s.transcript t).keypair with
        | none => s.bad
        | some (pk, sk) => s.bad || decide (decapsEpochKey (P := P) t pk sk x.1.1 x.1.2.1 ≠
            some (P.kdfOK x.1.2.2 t)))
  | st => (fun out => (out, s.transcript, s.bad)) <$> Braid.sendRleak P irl view st

/-- A send of `party` that reveals its coins if `leaking`. If the game refuses a leaking send, it
keeps neither the new game state nor the new records. Otherwise it updates the game state with
`Braid.sendUpdate`. -/
def traceSend [DecidableEq P.EpochKey] (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    (party leaking : Bool) :
    StateT (TraceState P AS) ProbComp
      (Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand)) :=
  fun s => (fun w : (SendResult P AS × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      (ℕ → EpochRecord P AS) × Bool =>
    let result := w.1.1
    let coins := w.1.2
    let leaked := (exposureAt P irl AS).rleak (s.game.stateAt party) coins
    if leaking && decide (leaked ∩ s.game.challenged ≠ ∅) then (none, s)
    else (some (result.sendingEpoch, result.outputKey.map Prod.fst, result.msg, coins),
      { game := { Braid.sendUpdate s.game party result with
          exposed := if leaking then s.game.exposed ∪ leaked else s.game.exposed },
        transcript := w.2.1, bad := w.2.2 })) <$> sampledSend view irl tbl rules s party

/-- The receive algorithm of the trace game. With `repair`, a well-formed `ct₂` message completing
the decoder of `ekSentCt1Received t` outputs the recorded epoch key of `t` and installs the
recorded authenticator value of `t`, without decapsulating and without verifying the tag. Every
other input runs `recvSCKA`. -/
def repairedRecv (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (repair : Bool) (T : ℕ → EpochRecord P AS) (st : State P AS) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × State P AS) :=
  if repair then
    match st, msg.type, msg.data with
    | .ekSentCt1Received t a _ _ dec, .ct2, some chunk =>
        if msg.wellFormed && decide (msg.epoch = t) then
          match P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk), (T t).key with
          | some _, some x =>
              some (some (t, x), msg.epoch - 1,
                .noHeaderReceived (t + 1) ((T t).pair.getD a) P.decHdr.empty)
          | _, _ => Braid.recvSCKA P view st msg
        else Braid.recvSCKA P view st msg
    | _, _, _ => Braid.recvSCKA P view st msg
  else Braid.recvSCKA P view st msg

/-- ML-KEM Braid with the authenticator `view` and the receive algorithm `repairedRecv` for the
records `T`. -/
def recvScheme [SampleableType P.EpochKey] (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (repair : Bool) (T : ℕ → EpochRecord P AS) :
    SCKAScheme ProbComp P.EpochKey (State P AS) (State P AS) P.EpochKey (Message P.Sym)
      (SendRand irl.KeygenRand irl.Encaps1Rand) :=
  { Braid.scheme P view irl ($ᵗ P.EpochKey) with
    recvA := repairedRecv view repair T
    recvB := repairedRecv view repair T }

/-- The receive oracle of `party`: the receive oracle of `recvScheme`. -/
def traceReceive [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (repair party : Bool) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ)) (StateT (TraceState P AS) ProbComp) :=
  fun n s => (liftGame (if party then
      SCKAScheme.oracleRecvA (recvScheme view irl repair s.transcript) n
    else SCKAScheme.oracleRecvB (recvScheme view irl repair s.transcript) n)) s

/-- The recorded key of epoch `e` read by the challenge oracle: A's key, else B's. -/
def lookupKey (g : GameState P AS) (e : ℕ) : Option P.EpochKey :=
  match g.keyA e with
  | some k => some k
  | none => g.keyB e

/-- The challenge oracle. An eligible challenge of `e` is answered by the installed answer for
`e` if there is one, and otherwise by `Braid.NoAuth.challengeValue` for the mode of `e`. -/
def traceChallenge [SampleableType P.K] [SampleableType P.EpochKey]
    {irl : P.kem.IncrementalRandLeak P.inc} (tbl : Installed P irl AS) (modes : Modes) :
    QueryImpl (ℕ →ₒ Option P.EpochKey) (StateT (TraceState P AS) ProbComp) :=
  fun e s =>
    if e ∈ s.game.exposed ∨ e ∈ s.game.challenged then pure (none, s)
    else match lookupKey s.game e with
      | none => pure (none, s)
      | some k => (fun out => (some out, { s with game :=
          { s.game with challenged := insert e s.game.challenged } })) <$>
          (match tbl.chal e with
            | some w => pure w
            | none => Braid.NoAuth.challengeValue P (modes.chal e) e k)

/-- The uniform-randomness oracle of the trace game. -/
def traceUnif (P : Parameters ProbComp) (AS : Type) :
    QueryImpl unifSpec (StateT (TraceState P AS) ProbComp) :=
  fun t => liftGame (SCKAScheme.oracleUnif (State P AS) (State P AS) P.EpochKey (Message P.Sym) t)

/-- The ordinary send oracle of `party`, which hides the sampled coins. -/
def tracePlain [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    (party : Bool) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Message P.Sym)) (StateT (TraceState P AS) ProbComp) :=
  fun _ => (fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
    traceSend view irl tbl rules party false

/-- The leaking send oracle of `party`. -/
def traceLeak [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    (party : Bool) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Message P.Sym ×
      SendRand irl.KeygenRand irl.Encaps1Rand)) (StateT (TraceState P AS) ProbComp) :=
  fun _ => traceSend view irl tbl rules party true

/-- The corruption oracle of A. It refuses if the exposed epochs meet the challenged ones, and
otherwise exposes them and answers with the observation `obs` of A's state. The records are never
revealed. -/
def traceCorruptA (irl : P.kem.IncrementalRandLeak P.inc)
    (obs : State P AS → Option (State P (Root × MacKey))) :
    QueryImpl (Unit →ₒ Option (State P (Root × MacKey))) (StateT (TraceState P AS) ProbComp) :=
  fun _ s =>
    let V := (exposureAt P irl AS).corrupt s.game.stA
    if V ∩ s.game.challenged ≠ ∅ then pure (none, s)
    else pure (obs s.game.stA, { s with game := { s.game with exposed := s.game.exposed ∪ V } })

/-- The version of `traceCorruptA` for B. -/
def traceCorruptB (irl : P.kem.IncrementalRandLeak P.inc)
    (obs : State P AS → Option (State P (Root × MacKey))) :
    QueryImpl (Unit →ₒ Option (State P (Root × MacKey))) (StateT (TraceState P AS) ProbComp) :=
  fun _ s =>
    let V := (exposureAt P irl AS).corrupt s.game.stB
    if V ∩ s.game.challenged ≠ ∅ then pure (none, s)
    else pure (obs s.game.stB, { s with game := { s.game with exposed := s.game.exposed ∪ V } })

/-- With the observation `some`, the corruption oracles of the trace game are the corruption
oracles of the SCKA security game for E⁺, lifted to the trace state. -/
theorem traceCorrupt_eq_oracleCorrupt (irl : P.kem.IncrementalRandLeak P.inc) :
    (traceCorruptA (AS := Root × MacKey) (MacKey := MacKey) irl some =
      fun t => liftGame (SCKAScheme.oracleCorruptA (successorExposure P irl Root MacKey).corrupt
        (State P (Root × MacKey)) P.EpochKey (Message P.Sym) t)) ∧
    (traceCorruptB (AS := Root × MacKey) (MacKey := MacKey) irl some =
      fun t => liftGame (SCKAScheme.oracleCorruptB (successorExposure P irl Root MacKey).corrupt
        (State P (Root × MacKey)) P.EpochKey (Message P.Sym) t)) := by
  constructor <;> funext u s <;> cases u <;>
    simp [traceCorruptA, traceCorruptB, liftGame, exposureAt, successorExposure,
      SCKAScheme.oracleCorruptA_run, SCKAScheme.oracleCorruptB_run] <;> split_ifs <;> rfl

/-- The security interface of the trace game. -/
def traceImpl [SampleableType P.K] [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (obs : State P AS → Option (State P (Root × MacKey)))
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    (modes : Modes) (repair : Bool) :
    QueryImpl (Spec P Root MacKey irl) (StateT (TraceState P AS) ProbComp) :=
  traceUnif P AS + tracePlain view irl tbl rules true + tracePlain view irl tbl rules false +
    traceReceive view irl repair true + traceReceive view irl repair false +
    traceLeak view irl tbl rules true + traceLeak view irl tbl rules false +
    traceChallenge tbl modes + traceCorruptA irl obs + traceCorruptB irl obs

/-- The initial state of a trace game with the initial authenticator value `a0`: both parties at
epoch `1`, the record of epoch `0` holding `a0`, no other record, and the bad flag false. -/
def initTrace (P : Parameters ProbComp) (a0 : AS) : TraceState P AS :=
  { game := SCKAScheme.initGameState (State.keysUnsampled 1 a0)
      (State.noHeaderReceived 1 a0 P.decHdr.empty)
    transcript := fun t =>
      { keypair := none, encaps1 := none, key := none, pair := if t = 0 then some a0 else none }
    bad := false }

/-- Run the adversary in the trace game. The initial authenticator value is drawn by
`rules.initPair`. -/
def run [SampleableType P.K] [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (obs : State P AS → Option (State P (Root × MacKey)))
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (tbl : Installed P irl AS) (rules : UpdateRules P AS) (modes : Modes) (repair : Bool)
    (A : Adversary P S irl) : ProbComp (Bool × TraceState P AS) := do
  let a0 ← rules.initPair
  (simulateQ (traceImpl view obs irl tbl rules modes repair) A).run (initTrace P a0)

/-- The SCKA security game of `scheme P S irl` with the challenge bit fixed to `b`, under E⁺ for
both parties. -/
def fixed [DecidableEq P.Mac] [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P S irl) (b : Bool) : ProbComp Bool :=
  SCKAScheme.securityExpFixedBit (scheme P S irl) A b
    (successorExposure P irl Root MacKey) (successorExposure P irl Root MacKey)

/-- The repaired hybrid: the real game with the repaired receive, in which an eligible challenge
of an epoch `t ≤ j` is answered uniformly. -/
def hybrid [DecidableEq P.Mac] [SampleableType P.K] [SampleableType P.EpochKey]
    [SampleableType Root] [SampleableType MacKey] [DecidableEq P.EpochKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P S irl) (j : ℕ) : ProbComp Bool :=
  Prod.fst <$> run S.toRatcheted some S irl Installed.empty
    (installedRules S (Installed.empty (irl := irl)) (Modes.hybrid j)) (Modes.hybrid j) true A

end MLKEMBraid.Auth
