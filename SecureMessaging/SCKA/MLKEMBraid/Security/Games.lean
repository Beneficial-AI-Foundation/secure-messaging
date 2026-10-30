/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.NoAuth
import SecureMessaging.SCKA.MLKEMBraid.Correctness.Invariant
import ToVCVio.EvalDist.BoolDist

/-!
# No-authentication Braid security games

The explicit-policy and baseline delta games agree on the complete joint
response/state computation, for either bit and any initial game state. The
comparison uses the supported joint send output, including its returned coins;
it assumes neither correctness nor admissibility of the trace.

The trace game `traceImpl` runs the same security interface on a `TraceState`: the actual game
state, ghost records of the key-generation and first-stage encapsulation samples, and a virtual
bad flag. Its query components (`traceUnif`, `tracePlain`, `traceReceive`, `traceLeak`,
`traceChallenge`, `traceCorruptA`, `traceCorruptB`) and the helpers `sampledSend`, `traceSend`,
`repairedRecv` and `recvScheme` form the internal interface used by the invariant, bad-event and
reduction modules.
-/

open OracleSpec OracleComp

namespace MLKEMBraid.NoAuth

/-- The full SCKA security interface of the no-authentication instance. -/
abbrev Spec (P : Parameters ProbComp)
    (irl : P.kem.IncrementalRandLeak P.inc) :=
  SCKAScheme.sckaSecuritySpec (State P Unit) (State P Unit)
    P.EpochKey (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand)

/-- An adaptive Boolean-output adversary for the full security interface. -/
abbrev Adversary (P : Parameters ProbComp)
    (irl : P.kem.IncrementalRandLeak P.inc) :=
  OracleComp (Spec P irl) Bool

/-- Select all four send indices, including ordinary and leaking sends of both parties. -/
def isSendQuery {P : Parameters ProbComp}
    {irl : P.kem.IncrementalRandLeak P.inc} : (Spec P irl).Domain → Bool
  | .inl (.inl (.inl (.inl (.inl t)))) =>
      SCKAScheme.isSendQuery (Rho := Message P.Sym) t
  | .inl (.inl (.inl (.inl (.inr _)))) => true
  | .inl (.inl (.inl (.inr _))) => true
  | _ => false

/-- A pathwise bound on all four security-interface send query indices combined. -/
def SendQueryBound {P : Parameters ProbComp}
    {irl : P.kem.IncrementalRandLeak P.inc}
    (A : Adversary P irl) (qS : ℕ) : Prop :=
  A.IsQueryBoundP (fun t => isSendQuery (P := P) (irl := irl) t = true) qS

/-- The replacement rule at a successful epoch challenge. -/
inductive Mode where
  /-- Return the recorded epoch key. -/
  | real
  /-- Sample a uniform epoch key. -/
  | uniform
  /-- Derive an epoch key from a fresh uniform raw KEM key. -/
  | derivedUniform

/-- Security game state with ghost sampling records and an absorbing virtual bad flag. -/
structure TraceState (P : Parameters ProbComp) where
  /-- The actual oracle-visible security-game state. -/
  game : MLKEMBraid.GameState P Unit
  /-- Actual key-generation and first-stage encapsulation samples, never disclosed as ghost data. -/
  transcript : ℕ → MLKEMBraid.EpochTranscript P
  /-- A derived-key decapsulation discrepancy recorded at first-stage encapsulation. -/
  bad : Bool

private theorem oracleSendArleak_eq_delta
    (P : Parameters ProbComp) [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) :
    SCKAScheme.ExposurePolicy.oracleSendArleak (exposure P irl).send (scheme P hMac irl) =
      SCKAScheme.ExposurePolicy.oracleSendArleak
        (deltaExposure P irl).send (scheme P hMac irl) := by
  funext u s
  cases u
  change (SCKAScheme.ExposurePolicy.oracleSendArleak (exposure P irl).send
    (scheme P hMac irl) ()).run s =
      (SCKAScheme.ExposurePolicy.oracleSendArleak
        (deltaExposure P irl).send (scheme P hMac irl) ()).run s
  simp only [SCKAScheme.ExposurePolicy.oracleSendArleak, deltaExposure,
    SCKAScheme.ExposurePolicy.ofDelta,
    StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift, monadLift_self,
    scheme, MLKEMBraid.scheme, bind_assoc]
  refine bind_congr_of_forall_mem_support _ fun out hout => ?_
  rcases out with ⟨r, rand⟩
  rw [sendExposure_eq_delta P hMac irl s.stA (r, rand) hout]
  rfl

private theorem oracleSendBrleak_eq_delta
    (P : Parameters ProbComp) [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) :
    SCKAScheme.ExposurePolicy.oracleSendBrleak (exposure P irl).send (scheme P hMac irl) =
      SCKAScheme.ExposurePolicy.oracleSendBrleak
        (deltaExposure P irl).send (scheme P hMac irl) := by
  funext u s
  cases u
  change (SCKAScheme.ExposurePolicy.oracleSendBrleak (exposure P irl).send
    (scheme P hMac irl) ()).run s =
      (SCKAScheme.ExposurePolicy.oracleSendBrleak
        (deltaExposure P irl).send (scheme P hMac irl) ()).run s
  simp only [SCKAScheme.ExposurePolicy.oracleSendBrleak, deltaExposure,
    SCKAScheme.ExposurePolicy.ofDelta,
    StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift, monadLift_self,
    scheme, MLKEMBraid.scheme, bind_assoc]
  refine bind_congr_of_forall_mem_support _ fun out hout => ?_
  rcases out with ⟨r, rand⟩
  rw [sendExposure_eq_delta P hMac irl s.stB (r, rand) hout]
  rfl

private theorem securityImpl_eq_delta
    (P : Parameters ProbComp)
    [SampleableType P.EpochKey] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) (b : Bool) :
    SCKAScheme.ExposurePolicy.sckaSecurityImpl b (exposure P irl) (exposure P irl)
        (scheme P hMac irl) =
      SCKAScheme.ExposurePolicy.sckaSecurityImpl b
        (deltaExposure P irl) (deltaExposure P irl) (scheme P hMac irl) := by
  simp only [SCKAScheme.ExposurePolicy.sckaSecurityImpl]
  rw [oracleSendArleak_eq_delta P hMac irl, oracleSendBrleak_eq_delta P hMac irl]
  rfl

/-- Sampled-bit experiment and guessing advantage fidelity to the frozen baseline game. -/
theorem securityGame_equiv_delta
    (P : Parameters ProbComp)
    [SampleableType P.EpochKey] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) :
    SCKAScheme.ExposurePolicy.securityExp (scheme P hMac irl) A
        (exposure P irl) (exposure P irl) =ᵈ
            SCKAScheme.ExposurePolicy.securityExp (scheme P hMac irl) A
        (deltaExposure P irl) (deltaExposure P irl) ∧
    SCKAScheme.ExposurePolicy.sckaGuessAdvantage (scheme P hMac irl) A
        (exposure P irl) (exposure P irl) =
      SCKAScheme.ExposurePolicy.sckaGuessAdvantage (scheme P hMac irl) A
        (deltaExposure P irl) (deltaExposure P irl) := by
  have hexp : SCKAScheme.ExposurePolicy.securityExp (scheme P hMac irl) A
      (exposure P irl) (exposure P irl) =
      SCKAScheme.ExposurePolicy.securityExp (scheme P hMac irl) A
        (deltaExposure P irl) (deltaExposure P irl) := by
    simp only [SCKAScheme.ExposurePolicy.securityExp, securityImpl_eq_delta P hMac irl]
  constructor
  · rw [hexp]
  · simp only [SCKAScheme.ExposurePolicy.sckaGuessAdvantage, hexp]

open ErasureCodePayload.Streaming

/-- Run a game-state oracle on the `game` field, keeping the ghost records and bad flag. -/
def liftGame {P : Parameters ProbComp} {α : Type}
    (c : StateT (MLKEMBraid.GameState P Unit) ProbComp α) :
    StateT (TraceState P) ProbComp α :=
  fun s => (fun z => (z.1, { s with game := z.2 })) <$> c.run s.game

/-- The actual joint send sample of `party`, with the ghost record of a key-generation or
first-stage encapsulation sample and the bad flag after its virtual decapsulation test. -/
def sampledSend (P : Parameters ProbComp) [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (s : TraceState P) (party : Bool) :
    ProbComp ((SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      (ℕ → EpochTranscript P) × Bool) :=
  match s.game.stateAt party with
  | .keysUnsampled e a => do
      let ((pk, sk), rand) ← irl.keygenRleak
      let hdr := P.inc.toHeader pk
      let vec := P.inc.toVector pk
      let tag := (auth P hMac).macHeader a e hdr
      let (chunk, enc) := (EncoderState.init P.ecpHdr (hdr, tag)).nextChunk
      let r : SendResult P Unit :=
        { msg := { epoch := e, type := .hdr, data := some chunk }
          sendingEpoch := e - 1, outputKey := none
          state := .keysSampled e a sk vec enc }
      let T := Function.update s.transcript e { (s.transcript e) with keypair := some (pk, sk) }
      pure ((r, .keygen rand), T, s.bad)
  | .headerReceived e a hdr dec => do
      let ((es, ct1, k), rand) ← irl.encaps1Rleak hdr
      let ik := P.kdfOK k e
      let (chunk, enc) := (EncoderState.init P.ecpCt1 ct1).nextChunk
      let r : SendResult P Unit :=
        { msg := { epoch := e, type := .ct1, data := some chunk }
          sendingEpoch := e - 1, outputKey := some (e, ik)
          state := .ct1Sampled e ((auth P hMac).update a e ik) hdr es ct1 enc dec }
      let T := Function.update s.transcript e { (s.transcript e) with encaps1 := some (es, ct1, k) }
      let bad := match (s.transcript e).keypair with
        | none => s.bad
        | some (pk, sk) =>
            s.bad || decide (decapsEpochKey (P := P) e pk sk es ct1 ≠ some (P.kdfOK k e))
      pure ((r, .encaps1 rand), T, bad)
  | st => (fun out => (out, s.transcript, s.bad)) <$>
      MLKEMBraid.sendRleak P irl (auth P hMac) st

/-- Discarding the ghost records of `sampledSend` gives the actual leaking send. -/
theorem sampledSend_erase (P : Parameters ProbComp) [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (s : TraceState P) (party : Bool) :
    Prod.fst <$> sampledSend P hMac irl s party =
      MLKEMBraid.sendRleak P irl (auth P hMac) (s.game.stateAt party) := by
  cases hst : s.game.stateAt party <;>
    simp [sampledSend, hst, MLKEMBraid.sendRleak]

/-- A send of `party`, leaking its coins if `leaking`. A refused leaking proposal commits neither
the game state nor its ghost records; otherwise the game update is `MLKEMBraid.sendUpdate`. -/
def traceSend (P : Parameters ProbComp) [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (party leaking : Bool) :
    StateT (TraceState P) ProbComp
      (Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand)) :=
  fun s => (fun w : (SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      (ℕ → EpochTranscript P) × Bool =>
    if leaking && decide ((exposure P irl).send (s.game.stateAt party) w.1.1.state w.1.2 ∩
        s.game.challenged ≠ ∅) then (none, s)
    else (some (w.1.1.sendingEpoch, w.1.1.outputKey.map Prod.fst, w.1.1.msg, w.1.2),
      { game := { MLKEMBraid.sendUpdate s.game party w.1.1 with
          exposed := if leaking then
            s.game.exposed ∪ (exposure P irl).send (s.game.stateAt party) w.1.1.state w.1.2
          else s.game.exposed },
        transcript := w.2.1, bad := w.2.2 })) <$> sampledSend P hMac irl s party

/-- The receive algorithm of the trace game. With `repair`, a well-formed `ct₂` message completing
the decoder of `ekSentCt1Received e` outputs the transcript's derived key of epoch `e` in place of
decapsulation; every other input runs `recvSCKA`. -/
def repairedRecv (P : Parameters ProbComp) [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (repair : Bool) (T : ℕ → EpochTranscript P)
    (st : State P Unit) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × State P Unit) :=
  if repair then
    match st, msg.type, msg.data with
    | .ekSentCt1Received e _ _ _ dec, .ct2, some chunk =>
        if msg.wellFormed && decide (msg.epoch = e) then
          match (dec.addChunk chunk).decodedPayload, (T e).encaps1 with
          | some _, some (_, _, k) =>
              some (some (e, P.kdfOK k e), msg.epoch - 1,
                .noHeaderReceived (e + 1) () (DecoderState.empty P.ecpHdr))
          | _, _ => MLKEMBraid.recvSCKA P (auth P hMac) st msg
        else MLKEMBraid.recvSCKA P (auth P hMac) st msg
    | _, _, _ => MLKEMBraid.recvSCKA P (auth P hMac) st msg
  else MLKEMBraid.recvSCKA P (auth P hMac) st msg

/-- The no-authentication scheme with the receive algorithm `repairedRecv` for transcript `T`. -/
def recvScheme (P : Parameters ProbComp) [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (repair : Bool) (T : ℕ → EpochTranscript P) :
    SCKAScheme ProbComp Unit (State P Unit) (State P Unit) P.EpochKey (Message P.Sym)
      (SendRand irl.KeygenRand irl.Encaps1Rand) :=
  { scheme P hMac irl with
    recvA := repairedRecv P hMac repair T
    recvB := repairedRecv P hMac repair T }

/-- The receive oracle of `party`: the scheme's receive oracle with `repairedRecv`. -/
def traceReceive (P : Parameters ProbComp)
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (repair party : Bool) : QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (TraceState P) ProbComp) :=
  fun n s => (liftGame (if party then
      SCKAScheme.oracleRecvA (recvScheme P hMac irl repair s.transcript) n
    else SCKAScheme.oracleRecvB (recvScheme P hMac irl repair s.transcript) n)) s

/-- The recorded key of epoch `e` read by the challenge oracle: A's key, else B's. -/
def lookupKey {P : Parameters ProbComp} (g : MLKEMBraid.GameState P Unit) (e : ℕ) :
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

/-- The corruption oracle of A in the trace game; it never discloses ghost records. -/
def traceCorruptA (P : Parameters ProbComp) :
    QueryImpl (Unit →ₒ Option (State P Unit)) (StateT (TraceState P) ProbComp) :=
  fun t => liftGame ((SCKAScheme.oracleCorruptA vuln (State P Unit) P.EpochKey (Message P.Sym)) t)

/-- The corruption oracle of B in the trace game; it never discloses ghost records. -/
def traceCorruptB (P : Parameters ProbComp) :
    QueryImpl (Unit →ₒ Option (State P Unit)) (StateT (TraceState P) ProbComp) :=
  fun t => liftGame ((SCKAScheme.oracleCorruptB vuln (State P Unit) P.EpochKey (Message P.Sym)) t)

/-- The security interface with same-site ghost records and optional proof-game receive repair. -/
def traceImpl (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (repair : Bool) (mode : ℕ → Mode) :
    QueryImpl (Spec P irl) (StateT (TraceState P) ProbComp) :=
  traceUnif P + tracePlain P hMac irl true + tracePlain P hMac irl false +
    traceReceive P hMac irl repair true + traceReceive P hMac irl repair false +
    traceLeak P hMac irl true + traceLeak P hMac irl false + traceChallenge P mode +
    traceCorruptA P + traceCorruptB P

/-- Simulate the adversary from the literal initial game and empty ghost transcript. -/
def run (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (repair : Bool) (mode : ℕ → Mode) (A : Adversary P irl) :
    ProbComp (Bool × TraceState P) :=
  (simulateQ (traceImpl P hMac irl repair mode) A).run
    { game := SCKAScheme.initGameState (MLKEMBraid.initA P (auth P hMac) ())
        (MLKEMBraid.initB P (auth P hMac) ())
      transcript := fun _ => { keypair := none, encaps1 := none }
      bad := false }

/-- The actual explicit-policy fixed-bit game, without ghost repair. -/
def fixed (P : Parameters ProbComp)
    [SampleableType P.EpochKey] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (b : Bool) : ProbComp Bool :=
  (simulateQ (SCKAScheme.ExposurePolicy.sckaSecurityImpl b
    (exposure P irl) (exposure P irl) (scheme P hMac irl)) A).run'
      (SCKAScheme.initGameState (MLKEMBraid.initA P (auth P hMac) ())
        (MLKEMBraid.initB P (auth P hMac) ()))

/-- Repaired numerical-epoch hybrid: uniform output keys through epoch j. -/
def hybrid (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (j : ℕ) : ProbComp Bool :=
  Prod.fst <$> run P hMac irl true
    (fun t => if t ≤ j then .uniform else .real) A

/-- Repaired adjacent hybrid with a uniformly sampled raw key at the selected epoch. -/
def rawHybrid (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (e : ℕ) : ProbComp Bool :=
  Prod.fst <$> run P hMac irl true
    (fun t => if t < e then .uniform
      else if t = e then .derivedUniform else .real) A

/-- The uniform-input key-derivation experiment, independent of protocol correctness. -/
def kdfExp (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    (e : ℕ) (D : P.EpochKey → ProbComp Bool) (derived : Bool) : ProbComp Bool :=
  if derived then do
    let u ← $ᵗ P.K
    D (P.kdfOK u e)
  else do
    let x ← $ᵗ P.EpochKey
    D x

/-- A key-derivation distinguisher that first chooses the epoch label. -/
structure KDFContextAdversary (P : Parameters ProbComp) where
  /-- The information kept between choosing the label and guessing. -/
  State : Type
  /-- Choose the epoch label and the kept information. -/
  context : ProbComp (ℕ × State)
  /-- Guess from the kept information and the epoch key received. -/
  guess : State → P.EpochKey → ProbComp Bool

/-- Key-derivation game. The label `e` is chosen first; then `kdfExp` runs the fixed-epoch game at
`e`: with `derived = true` the distinguisher receives `kdfOK u e` for uniform `u`, with `false` a
uniform epoch key. -/
def kdfContextExp (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
    (C : KDFContextAdversary P) (derived : Bool) : ProbComp Bool := do
  let (e, st) ← C.context
  kdfExp P e (C.guess st) derived

/-- Distinguishing advantage of a key-derivation adversary. -/
noncomputable def kdfAdvantage (P : Parameters ProbComp) [SampleableType P.K]
    [SampleableType P.EpochKey] (C : KDFContextAdversary P) : ℝ :=
  (𝒟[kdfContextExp P C true].boolDist 𝒟[kdfContextExp P C false]).toReal

end MLKEMBraid.NoAuth
