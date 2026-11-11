/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.NoAuth
public import SecureMessaging.SCKA.MLKEMBraid.Correctness.Invariant
public import ToVCVio.EvalDist.BoolDist
public import SecureMessaging.SCKA.MLKEMBraid.Security.KDFGame

/-!
# No-authentication Braid security games

The trace game `traceImpl` runs the same security interface on a `TraceState`: the actual game
state, records of the sampled key pairs and first-stage encapsulations, and a bad flag.
-/

@[expose] public section

open OracleSpec OracleComp

namespace Braid.NoAuth

/-- The full SCKA security interface of the no-authentication instance. -/
abbrev Spec (P : Parameters ProbComp)
    (irl : P.kem.IncrementalRandLeak P.inc) :=
  SCKAScheme.sckaSecuritySpec (State P Unit) (State P Unit)
    P.EpochKey (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand)

/-- An adaptive Boolean-output adversary for the full security interface. -/
abbrev Adversary (P : Parameters ProbComp)
    (irl : P.kem.IncrementalRandLeak P.inc) :=
  OracleComp (Spec P irl) Bool

/-- On every path of oracle answers, `A` makes at most `qS` send queries in total, counting all
four send queries. -/
-- ANCHOR: sendQueryBound
def SendQueryBound {P : Parameters ProbComp}
    {irl : P.kem.IncrementalRandLeak P.inc}
    (A : Adversary P irl) (qS : ℕ) : Prop :=
  A.IsQueryBoundP (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) qS
-- ANCHOR_END: sendQueryBound

/-- How the challenge oracle answers a successful challenge of an epoch. -/
inductive Mode where
  /-- Return the recorded epoch key. -/
  | real
  /-- Sample a uniform epoch key. -/
  | uniform
  /-- Derive an epoch key from a fresh uniform raw KEM key. -/
  | derivedUniform

/-- The state of the security game with records of the sampled values and a bad flag that stays
set once it is set. -/
structure TraceState (P : Parameters ProbComp) where
  /-- The state of the security game that the oracles use. -/
  game : Braid.GameState P Unit
  /-- The sampled key pairs and first-stage encapsulations. The adversary never sees them. -/
  transcript : ℕ → Braid.EpochTranscript P
  /-- Set at a first-stage encapsulation when decapsulation would not give the derived key. -/
  bad : Bool

open ErasureCodePayload.Streaming

/-- Run a game-state oracle on the `game` field, and keep the records and the bad flag. -/
def liftGame {P : Parameters ProbComp} {α : Type}
    (c : StateT (Braid.GameState P Unit) ProbComp α) :
    StateT (TraceState P) ProbComp α :=
  fun s => (fun z => (z.1, { s with game := z.2 })) <$> c.run s.game

/-- The key-generation send of epoch `t` with the key pair `(pk, sk)`: the result of the
key-generation branch of `sendRleak`. -/
def keygenStep (P : Parameters ProbComp) (hMac : P.Mac = Unit) (t : ℕ) (a : Unit) (pk : P.PK)
    (sk : P.SK) : SendResult P Unit :=
  let hdr := P.inc.toHeader pk
  let (chunk, enc) :=
    (EncoderState.init P.ecpHdr (hdr, (auth P hMac).macHeader a t hdr)).nextChunk
  { msg := { epoch := t, type := .hdr, data := some chunk }
    sendingEpoch := t - 1, outputKey := none
    state := .keysSampled t a sk (P.inc.toVector pk) enc }

/-- The first-stage encapsulation send of epoch `t` with the sample `(es, ct1, k)`: the result of
the first-stage encapsulation branch of `sendRleak`. -/
def encaps1Step (P : Parameters ProbComp) (hMac : P.Mac = Unit) (t : ℕ) (a : Unit)
    (hdr : P.inc.PKheader) (dec : P.decEk.D) (es : P.inc.St)
    (ct1 : P.inc.C₁) (k : P.K) : SendResult P Unit :=
  let (chunk, enc) := (EncoderState.init P.ecpCt1 ct1).nextChunk
  { msg := { epoch := t, type := .ct1, data := some chunk }
    sendingEpoch := t - 1, outputKey := some (t, P.kdfOK k t)
    state := .ct1Sampled t ((auth P hMac).update a t (P.kdfOK k t)) hdr es ct1 enc dec }

/-- The bad flag after a first-stage encapsulation sample `c` of epoch `t`. -/
def encaps1Bad {P : Parameters ProbComp} [DecidableEq P.EpochKey] (s : TraceState P) (t : ℕ)
    (c : P.inc.St × P.inc.C₁ × P.K) : Bool :=
  match (s.transcript t).keypair with
  | none => s.bad
  | some (pk, sk) => s.bad || decide (decapsEpochKey (P := P) t pk sk c.1 c.2.1 ≠
      some (P.kdfOK c.2.2 t))

/-- The leaking send of `party` with its records. It also records a sampled key pair or
first-stage encapsulation, and updates the bad flag by testing decapsulation. -/
def sampledSend (P : Parameters ProbComp) [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (s : TraceState P) (party : Bool) :
    ProbComp ((SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      (ℕ → EpochTranscript P) × Bool) :=
  match s.game.stateAt party with
  | .keysUnsampled e a => (fun x : (P.PK × P.SK) × irl.KeygenRand =>
      ((keygenStep P hMac e a x.1.1 x.1.2, .keygen x.2),
        Function.update s.transcript e { (s.transcript e) with keypair := some x.1 }, s.bad)) <$>
      irl.keygenRleak
  | .headerReceived e a hdr dec => (fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
      ((encaps1Step P hMac e a hdr dec x.1.1 x.1.2.1 x.1.2.2, .encaps1 x.2),
        Function.update s.transcript e { (s.transcript e) with encaps1 := some x.1 },
        encaps1Bad s e x.1)) <$> irl.encaps1Rleak hdr
  | st => (fun out => (out, s.transcript, s.bad)) <$>
      Braid.sendRleak P irl (auth P hMac) st

/-- Forgetting the records of `sampledSend` gives the leaking send. -/
theorem sampledSend_erase (P : Parameters ProbComp) [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (s : TraceState P) (party : Bool) :
    Prod.fst <$> sampledSend P hMac irl s party =
      Braid.sendRleak P irl (auth P hMac) (s.game.stateAt party) := by
  cases hst : s.game.stateAt party <;>
    simp [sampledSend, hst, Braid.sendRleak, keygenStep, encaps1Step]

/-- A send of `party` that reveals its coins if `leaking`. If the game refuses a leaking send, it
keeps neither the new game state nor the new records. Otherwise it updates the game state with
`Braid.sendUpdate`. -/
def traceSend (P : Parameters ProbComp) [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (party leaking : Bool) :
    StateT (TraceState P) ProbComp
      (Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand)) :=
  fun s => (fun w : (SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      (ℕ → EpochTranscript P) × Bool =>
    let result := w.1.1
    let coins := w.1.2
    let leaked := (nativeExposure P irl).rleak (s.game.stateAt party) coins
    if leaking && decide (leaked ∩ s.game.challenged ≠ ∅) then (none, s)
    else (some (result.sendingEpoch, result.outputKey.map Prod.fst, result.msg, coins),
      { game := { Braid.sendUpdate s.game party result with
          exposed := if leaking then s.game.exposed ∪ leaked else s.game.exposed },
        transcript := w.2.1, bad := w.2.2 })) <$> sampledSend P hMac irl s party

/-- The receive algorithm of the trace game. With `repair`, a well-formed `ct₂` message completing
the decoder of `ekSentCt1Received e` outputs the recorded derived key of epoch `e` instead of
decapsulating. Every other input runs `recvSCKA`. -/
def repairedRecv (P : Parameters ProbComp)
    (hMac : P.Mac = Unit) (repair : Bool) (T : ℕ → EpochTranscript P)
    (st : State P Unit) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × State P Unit) :=
  if repair then
    match st, msg.type, msg.data with
    | .ekSentCt1Received e _ _ _ dec, .ct2, some chunk =>
        if msg.wellFormed && decide (msg.epoch = e) then
          match P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk), (T e).encaps1 with
          | some _, some (_, _, k) =>
              some (some (e, P.kdfOK k e), msg.epoch - 1,
                .noHeaderReceived (e + 1) () P.decHdr.empty)
          | _, _ => Braid.recvSCKA P (auth P hMac) st msg
        else Braid.recvSCKA P (auth P hMac) st msg
    | _, _, _ => Braid.recvSCKA P (auth P hMac) st msg
  else Braid.recvSCKA P (auth P hMac) st msg

/-- The no-authentication scheme with the receive algorithm `repairedRecv` for transcript `T`. -/
def recvScheme (P : Parameters ProbComp)
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (repair : Bool) (T : ℕ → EpochTranscript P) :
    SCKAScheme ProbComp Unit (State P Unit) (State P Unit) P.EpochKey (Message P.Sym)
      (SendRand irl.KeygenRand irl.Encaps1Rand) :=
  { scheme P hMac irl with
    recvA := repairedRecv P hMac repair T
    recvB := repairedRecv P hMac repair T }

/-- The receive oracle of `party`: the scheme's receive oracle with `repairedRecv`. -/
def traceReceive (P : Parameters ProbComp)
    [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (repair party : Bool) : QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (TraceState P) ProbComp) :=
  fun n s => (liftGame (if party then
      SCKAScheme.oracleRecvA (recvScheme P hMac irl repair s.transcript) n
    else SCKAScheme.oracleRecvB (recvScheme P hMac irl repair s.transcript) n)) s

/-- The recorded key of epoch `e` read by the challenge oracle: A's key, else B's. -/
def lookupKey {P : Parameters ProbComp} (g : Braid.GameState P Unit) (e : ℕ) :
    Option P.EpochKey :=
  match g.keyA e with
  | some k => some k
  | none => g.keyB e

/-- The challenge answer for the recorded key `k` of epoch `e` under the replacement rule `m`. -/
def challengeValue (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
    (m : Mode) (e : ℕ) (k : P.EpochKey) : ProbComp P.EpochKey :=
  match m with
  | .real => pure k
  | .uniform => $ᵗ P.EpochKey
  | .derivedUniform => (fun u => P.kdfOK u e) <$> ($ᵗ P.K)

/-- The challenge oracle with the replacement rule `mode e` for epoch `e`. -/
def traceChallenge (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    (mode : ℕ → Mode) : QueryImpl (ℕ →ₒ Option P.EpochKey) (StateT (TraceState P) ProbComp) :=
  fun e s =>
    if e ∈ s.game.exposed ∨ e ∈ s.game.challenged then pure (none, s)
    else match lookupKey s.game e with
      | none => pure (none, s)
      | some k => (fun out => (some out, { s with game :=
          { s.game with challenged := insert e s.game.challenged } })) <$>
          challengeValue P (mode e) e k

/-- The uniform-randomness oracle of the trace game. -/
def traceUnif (P : Parameters ProbComp) : QueryImpl unifSpec (StateT (TraceState P) ProbComp) :=
  fun t => liftGame ((SCKAScheme.oracleUnif (State P Unit) (State P Unit)
    P.EpochKey (Message P.Sym)) t)

/-- The ordinary send oracle of `party` in the trace game, which hides the sampled coins. -/
def tracePlain (P : Parameters ProbComp) [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) (party : Bool) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Message P.Sym))
      (StateT (TraceState P) ProbComp) :=
  fun _ => (fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
    traceSend P hMac irl party false

/-- The leaking send oracle of `party` in the trace game. -/
def traceLeak (P : Parameters ProbComp) [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) (party : Bool) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Message P.Sym ×
      SendRand irl.KeygenRand irl.Encaps1Rand)) (StateT (TraceState P) ProbComp) :=
  fun _ => traceSend P hMac irl party true

/-- The corruption oracle of A in the trace game. It never reveals the records. -/
def traceCorruptA (P : Parameters ProbComp) :
    QueryImpl (Unit →ₒ Option (State P Unit)) (StateT (TraceState P) ProbComp) :=
  fun t => liftGame ((SCKAScheme.oracleCorruptA vuln (State P Unit) P.EpochKey (Message P.Sym)) t)

/-- The corruption oracle of B in the trace game. It never reveals the records. -/
def traceCorruptB (P : Parameters ProbComp) :
    QueryImpl (Unit →ₒ Option (State P Unit)) (StateT (TraceState P) ProbComp) :=
  fun t => liftGame ((SCKAScheme.oracleCorruptB vuln (State P Unit) P.EpochKey (Message P.Sym)) t)

/-- The SCKA security interface with recorded samples and optional repaired receives. -/
def traceImpl (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (repair : Bool) (mode : ℕ → Mode) :
    QueryImpl (Spec P irl) (StateT (TraceState P) ProbComp) :=
  traceUnif P + tracePlain P hMac irl true + tracePlain P hMac irl false +
    traceReceive P hMac irl repair true + traceReceive P hMac irl repair false +
    traceLeak P hMac irl true + traceLeak P hMac irl false + traceChallenge P mode +
    traceCorruptA P + traceCorruptB P

/-- The literal initial state of the trace games. -/
def initTrace (P : Parameters ProbComp) (hMac : P.Mac = Unit) : TraceState P :=
  { game := SCKAScheme.initGameState (Braid.initA P (auth P hMac) ())
      (Braid.initB P (auth P hMac) ())
    transcript := fun _ => { keypair := none, encaps1 := none }
    bad := false }

/-- Run the adversary in the trace game from the initial game state, with empty records and the
bad flag false. -/
def run (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (repair : Bool) (mode : ℕ → Mode) (A : Adversary P irl) :
    ProbComp (Bool × TraceState P) :=
  (simulateQ (traceImpl P hMac irl repair mode) A).run
    (initTrace P hMac)

/-- The security game with the exposure functions `nativeExposure` and the challenge bit fixed to
`b`, run from the initial states. -/
def fixed (P : Parameters ProbComp)
    [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (b : Bool) : ProbComp Bool :=
  (simulateQ (SCKAScheme.sckaSecurityImpl b
    (nativeExposure P irl) (nativeExposure P irl) (scheme P hMac irl)) A).run'
      (SCKAScheme.initGameState (Braid.initA P (auth P hMac) ())
        (Braid.initB P (auth P hMac) ()))

/-- `fixed A b` is the SCKA security experiment with the bit fixed to `b` and the functions
`nativeExposure`. -/
theorem fixed_eq_native
    (P : Parameters ProbComp)
    [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (b : Bool) :
    fixed P hMac irl A b =
      SCKAScheme.securityExpFixedBit (scheme P hMac irl) A b
        (nativeExposure P irl) (nativeExposure P irl) := by
  have h1 : (scheme P hMac irl).initKeyGen = pure () := rfl
  have h2 : ∀ ik, (scheme P hMac irl).initA ik = pure (Braid.initA P (auth P hMac) ik) :=
    fun _ => rfl
  have h3 : ∀ ik, (scheme P hMac irl).initB ik = pure (Braid.initB P (auth P hMac) ik) :=
    fun _ => rfl
  simp only [SCKAScheme.securityExpFixedBit, h1, h2, h3, pure_bind]
  simp only [fixed, StateT.run'_eq, map_eq_bind_pure_comp]
  rfl

/-- The repaired hybrid with uniform keys at the epochs `1, …, j` and real keys after them. -/
def hybrid (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (j : ℕ) : ProbComp Bool :=
  Prod.fst <$> run P hMac irl true
    (fun t => if t ≤ j then .uniform else .real) A

/-- The repaired hybrid with uniform keys at the epochs before `e`, the key `kdfOK u e` for a
uniform shared secret `u` at `e`, and real keys after `e`. -/
def rawHybrid (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (e : ℕ) : ProbComp Bool :=
  Prod.fst <$> run P hMac irl true
    (fun t => if t < e then .uniform
      else if t = e then .derivedUniform else .real) A

end Braid.NoAuth
