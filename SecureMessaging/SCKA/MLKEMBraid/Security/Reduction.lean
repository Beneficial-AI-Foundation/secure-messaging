/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.BadEvent
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

/-!
# Explicit KEM and KDF reductions

Adjacent repaired hybrids differ only at the challenge of one numerical epoch `e`. This file
defines the two explicit reductions of the hybrid argument and proves the KDF and KEM steps. The
installed trace games `traceImplAt`, their flag discipline, the stop at the exposure of `e` and the
installation of the challenge value are in `BadEvent`.

* **Stopping.** `signedGap_stop`: two repaired trace games whose challenge modes agree off `e`
  have the same signed output gap after both are stopped (output `false`) when `e` becomes
  exposed. A run in which `e` is challenged never stops, the two games differ only at an eligible
  challenge of `e`, which commits both, and after an exposure of `e` every continuation agrees.
* **Installed challenge values.** `stoppedRun_chalSample`: sampling the challenge value of `e`
  once before the run and answering with it is the same as sampling it at the challenge.
* **KDF reduction.** `kdfReduction e x` runs the stopped repaired game once, sampling all KEM
  material itself, and answers the eligible challenge of `e` with `x`; `kdf_gap_eq` identifies
  its uniform-input KDF advantage with the gap between the adjacent hybrids.
* **KEM reduction.** `kemReduction e` runs a single-pass masked simulation of the stopped repaired
  game (`simImpl`): states of epoch `e` that would hold the selected decapsulation key or
  encapsulation state are `Masked` and never materialized; the challenge public key is installed
  at the key generation of `e`, the challenge ciphertext parts at its first-stage encapsulation
  and at the encapsulator's second stage, and the derived test key is the key of `e`. The
  simulator view `simOf` of a trace state masks those states, relabels the key of `e` and erases
  the records of `e`; `StepSim` states that one simulator query agrees with one trace query up to
  answers dropped by the stop.
* **Once-used KEM samples.** The installed trace game also accepts a key pair and a first-stage
  sample of `e`. `stoppedRun_installKeygen` and `stoppedRun_installEncaps1`: sampling them once
  before the stopped run is the same as sampling them at their sends (`optionRun_install`).
  `simStep_eq`: with both installed, the masked simulator and the installed trace game accept with
  the same probability (`simImpl_step`, query by query). `kem_gap_eq` identifies the IND-CPA
  advantage of `kemReduction` with the gap between the adjacent hybrids.
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

/-! ### The KDF reduction -/

/-- **`kdfReduction`**: the uniform-input KDF distinguisher for epoch `e`. For `e = 0` it returns
`false`. Otherwise it runs the repaired game of `A` once, stopped with `false` when `e` becomes
exposed, sampling all KEM material itself; an eligible challenge of `e` is answered with the test
value `x`, earlier epochs with uniform keys and later epochs with their real keys. -/
def kdfReduction (P : Parameters ProbComp) [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (e : ℕ) : P.EpochKey → ProbComp Bool :=
  fun x => match e with
    | 0 => pure false
    | e + 1 => stoppedRun (traceImplAt P hMac irl (e + 1) none none (some x)
        (fun t => if t < e + 1 then .uniform else .real)) (targetStop (e + 1)) A
        (initTrace P hMac)

/-- **`kdf_gap_eq`**: for a positive epoch `e`, the gap between the hybrid with the derived
uniform key at `e` and the hybrid with a uniform key at `e` is the uniform-input KDF advantage of
`kdfReduction` at `e`. No code-correctness assumption is used. -/
theorem kdf_gap_eq (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (e : ℕ) (he : 0 < e) :
    (rawHybrid P hMac irl A e).boolDistAdvantage (hybrid P hMac irl A e) =
      (kdfExp P e (kdfReduction P hMac irl A e) true).boolDistAdvantage
        (kdfExp P e (kdfReduction P hMac irl A e) false) := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  have hJH : ∀ t, t ≠ n + 1 →
      (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform else Mode.real) =
        (if t ≤ n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg ht, if_neg (by omega)]
  have hJD : ∀ t, t ≠ n + 1 →
      (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform else Mode.real) =
        (if t < n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg ht, if_neg h]
  have hHD : ∀ t, t ≠ n + 1 →
      (if t ≤ n + 1 then Mode.uniform else Mode.real) =
        (if t < n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hgap := signedGap_stop hMac irl
    (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real)
    (fun t => if t ≤ n + 1 then .uniform else .real) (n + 1) hJH A
  have hJ : Pr[= true | stoppedRun (traceImpl P hMac irl true
        (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real))
        (targetStop (n + 1)) A (initTrace P hMac)] =
      Pr[= true | kdfExp P (n + 1) (kdfReduction P hMac irl A (n + 1)) true] := by
    rw [← traceImplAt_none hMac irl (n + 1), ← stoppedRun_chalSample hMac irl (n + 1) none none _
      ((fun u => P.kdfOK u (n + 1)) <$> ($ᵗ P.K)) (fun k => by simp [challengeValue])]
    simp only [kdfExp, kdfReduction, ↓reduceIte, bind_map_left,
      traceImplAt_congr hMac irl (n + 1) none none _ _ _ hJD]
  have hH : Pr[= true | stoppedRun (traceImpl P hMac irl true
        (fun t => if t ≤ n + 1 then .uniform else .real))
        (targetStop (n + 1)) A (initTrace P hMac)] =
      Pr[= true | kdfExp P (n + 1) (kdfReduction P hMac irl A (n + 1)) false] := by
    rw [← traceImplAt_none hMac irl (n + 1), ← stoppedRun_chalSample hMac irl (n + 1) none none _
      ($ᵗ P.EpochKey) (fun k => by simp [challengeValue])]
    simp only [kdfExp, kdfReduction, Bool.false_eq_true, ↓reduceIte,
      traceImplAt_congr hMac irl (n + 1) none none _ _ _ hHD]
  unfold ProbComp.boolDistAdvantage rawHybrid hybrid
  rw [hgap, hJ, hH]

/-! ### The masked simulator of the KEM reduction -/

/-- A party state of the selected epoch with its secret removed: the four states in which the
generator retains the decapsulation key, and the three states in which the encapsulator retains
the encapsulation state, each without that secret. The epoch is the selected epoch and the
authentication state is the unit. -/
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

/-! ### The simulator view of a trace state -/

/-- An output key with the key of the selected epoch `e` replaced by `v`. -/
def relabelKey (e : ℕ) (v : P.EpochKey) : Option (ℕ × P.EpochKey) → Option (ℕ × P.EpochKey)
  | none => none
  | some (t, k) => some (t, if t = e then v else k)

/-- A key table with the key of the selected epoch `e` replaced by `v`. -/
def relabel (e : ℕ) (v : P.EpochKey) (keys : ℕ → Option P.EpochKey) : ℕ → Option P.EpochKey :=
  fun t => if t = e then (keys t).map fun _ => v else keys t

/-- Ghost records with the records of the selected epoch `e` erased. -/
def eraseAt (e : ℕ) (T : ℕ → EpochTranscript P) : ℕ → EpochTranscript P :=
  fun t => if t = e then { keypair := none, encaps1 := none } else T t

/-- The simulator game of a trace game: masked states and relabelled keys at `e`. -/
def simGameOf (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit) : SimGame P :=
  { stA := maskState e g.stA, stB := maskState e g.stB
    keyA := relabel e v g.keyA, keyB := relabel e v g.keyB
    msgA := g.msgA, msgB := g.msgB, nA := g.nA, nB := g.nB
    exposed := g.exposed, challenged := g.challenged }

/-- The simulator state of a trace state. -/
def simOf (e : ℕ) (v : P.EpochKey) (s : TraceState P) : SimState P :=
  { game := simGameOf e v s.game, transcript := eraseAt e s.transcript }

section SimView

/-- The simulator's party state is the masked trace party state. -/
theorem simGameOf_stateAt (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit)
    (party : Bool) : (simGameOf e v g).stateAt party = maskState e (g.stateAt party) := by
  cases party <;> rfl

/-- The game of the simulator view. -/
theorem simOf_game (e : ℕ) (v : P.EpochKey) (s : TraceState P) :
    (simOf e v s).game = simGameOf e v s.game := rfl

/-- The records of the simulator view. -/
theorem simOf_transcript (e : ℕ) (v : P.EpochKey) (s : TraceState P) :
    (simOf e v s).transcript = eraseAt e s.transcript := rfl

/-- The exposed epochs of the simulator view. -/
theorem simGameOf_exposed (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit) :
    (simGameOf e v g).exposed = g.exposed := rfl

/-- The challenged epochs of the simulator view. -/
theorem simGameOf_challenged (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit) :
    (simGameOf e v g).challenged = g.challenged := rfl

/-- The messages of A in the simulator view. -/
theorem simGameOf_msgA (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit) :
    (simGameOf e v g).msgA = g.msgA := rfl

/-- The messages of B in the simulator view. -/
theorem simGameOf_msgB (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit) :
    (simGameOf e v g).msgB = g.msgB := rfl

/-- Relabelling commutes with recording a key. -/
theorem relabel_update (e : ℕ) (v : P.EpochKey) (keys : ℕ → Option P.EpochKey) (t : ℕ)
    (k : P.EpochKey) :
    relabel e v (Function.update keys t (some k)) =
      Function.update (relabel e v keys) t (some (if t = e then v else k)) := by
  funext u
  by_cases hu : u = t
  · subst hu
    by_cases he : u = e <;> simp [relabel, he]
  · simp [relabel, hu]

/-- Relabelling commutes with recording an optional key. -/
theorem relabel_keyUpdate (e : ℕ) (v : P.EpochKey) (keys : ℕ → Option P.EpochKey)
    (key : Option (ℕ × P.EpochKey)) :
    relabel e v (keyUpdate keys key) = keyUpdate (relabel e v keys) (relabelKey e v key) := by
  rcases key with _ | ⟨t, k⟩
  · rfl
  · exact relabel_update e v keys t k

/-- Relabelling keeps the epoch of an output key. -/
theorem relabelKey_map_fst (e : ℕ) (v : P.EpochKey) (key : Option (ℕ × P.EpochKey)) :
    (relabelKey e v key).map Prod.fst = key.map Prod.fst := by
  rcases key with _ | ⟨t, k⟩ <;> rfl

/-- Erasing `e` commutes with recording a key pair of another epoch. -/
theorem eraseAt_update_keypair (e t : ℕ) (ht : t ≠ e) (T : ℕ → EpochTranscript P)
    (x : P.PK × P.SK) :
    Function.update (eraseAt e T) t { (eraseAt e T t) with keypair := some x } =
      eraseAt e (Function.update T t { (T t) with keypair := some x }) := by
  funext u
  by_cases hu : u = t
  · subst hu
    simp [eraseAt, ht]
  · simp [eraseAt, hu]

/-- Erasing `e` commutes with recording a first-stage encapsulation of another epoch. -/
theorem eraseAt_update_encaps1 (e t : ℕ) (ht : t ≠ e) (T : ℕ → EpochTranscript P)
    (x : P.inc.St × P.inc.C₁ × P.K) :
    Function.update (eraseAt e T) t { (eraseAt e T t) with encaps1 := some x } =
      eraseAt e (Function.update T t { (T t) with encaps1 := some x }) := by
  funext u
  by_cases hu : u = t
  · subst hu
    simp [eraseAt, ht]
  · simp [eraseAt, hu]

/-- Erasing `e` forgets every record of `e`. -/
theorem eraseAt_update_self (e : ℕ) (T : ℕ → EpochTranscript P) (r : EpochTranscript P) :
    eraseAt e (Function.update T e r) = eraseAt e T := by
  funext u
  by_cases hu : u = e
  · simp [eraseAt, hu]
  · simp [eraseAt, hu]

/-- `maskState` keeps an ordinary state. -/
theorem maskState_eq_inl {e : ℕ} {st st' : State P Unit} (h : maskState e st = .inl st') :
    st' = st := by
  cases st <;> simp only [maskState] at h <;> (try split_ifs at h) <;> simp_all

/-- The exposure footprint of a masked view is that of the state. -/
theorem simVuln_maskState (e : ℕ) (st : State P Unit) : simVuln e (maskState e st) = vuln st := by
  cases st <;> simp only [maskState] <;> (try split_ifs) <;> simp_all [simVuln, vuln, State.epoch]

/-- A masked state sends its next chunk deterministically. -/
theorem send_masked (hMac : P.Mac = Unit) {e : ℕ} {st : State P Unit} {m : Masked P}
    (hm : maskState e st = .inr m) :
    ∃ R : SendResult P Unit, MLKEMBraid.send P (auth P hMac) st = pure R ∧
      R.msg = (maskedSend e m).1 ∧ R.sendingEpoch = e - 1 ∧ R.outputKey = none ∧
      maskState e R.state = .inr (maskedSend e m).2 := by
  cases st with
  | keysUnsampled t a => simp [maskState] at hm
  | noHeaderReceived t a dec => simp [maskState] at hm
  | headerReceived t a hdr dec => simp [maskState] at hm
  | ct2Sampled t a enc => simp [maskState] at hm
  | keysSampled t a sk vec enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | headerSent t a sk dec enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | ct1Received t a sk ct1 enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | ekSentCt1Received t a sk ct1 dec =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | ct1Sampled t a hdr es ct1 enc dec =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | ekReceivedCt1Sampled t a es ct1 hdr vec enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm
  | ct1Acknowledged t a hdr es ct1 dec =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        exact ⟨_, rfl, rfl, rfl, rfl, by simp only [maskState, ↓reduceIte]; rfl⟩
      · simp [maskState, ht] at hm

/-- Lifted uniform randomness keeps any state. -/
theorem liftTarget_unif_run {σ : Type} (t : ℕ) (s : σ) :
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp)) t).run s =
      (fun a => (a, s)) <$> (QueryImpl.ofLift unifSpec ProbComp) t := by
  simp [StateT.run_monadLift, map_eq_bind_pure_comp]

variable [DecidableEq P.EpochKey]

/-- The simulator game of a trace send update. -/
theorem simGameOf_sendUpdate (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit)
    (party : Bool) (r : SendResult P Unit) (X : Finset ℕ) :
    simGameOf e v { sendUpdate g party r with exposed := X } =
      { (simGameOf e v g).sendUpdate party (relabelKey e v r.outputKey) r.msg r.sendingEpoch
          (maskState e r.state) with exposed := X } := by
  cases party <;> rcases hk : r.outputKey with _ | ⟨t, k⟩ <;>
    simp [simGameOf, sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hk,
      SimGame.sendUpdate, keyUpdate, relabelKey, relabel_update]

/-- The simulator game of a trace receive update. -/
theorem simGameOf_recvUpdate (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit)
    (party : Bool) (tsnd trcv : ℕ) (key : Option (ℕ × P.EpochKey)) (st : State P Unit) :
    simGameOf e v (recvUpdate g party tsnd ⟨trcv, key, st⟩ trcv) =
      (simGameOf e v g).recvUpdate party (relabelKey e v key) (maskState e st) := by
  cases party <;> rcases key with _ | ⟨t, k⟩ <;>
    simp [simGameOf, recvUpdate, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate,
      SimGame.recvUpdate, keyUpdate, relabelKey, relabel_update]

end SimView

/-! ### Agreement of one simulator query with one trace query -/

/-- One simulator query from the simulator view of a trace state agrees with one trace query, up
to answers dropped because `e` became exposed. -/
def StepSim (e : ℕ) (v : P.EpochKey) {α : Type} (oS : ProbComp (α × SimState P))
    (oT : ProbComp (α × TraceState P)) : Prop :=
  𝒟[(fun w => (if simStop e w.2 then none else some w.1, w.2)) <$> oS] =
    𝒟[(fun w => (if targetStop e w.2 then none else some w.1, simOf e v w.2)) <$> oT]

section Step

variable {e : ℕ} {v : P.EpochKey}

/-- Exact agreement gives `StepSim`. -/
theorem StepSim.of_eq {α : Type} {oS : ProbComp (α × SimState P)}
    {oT : ProbComp (α × TraceState P)} (h : 𝒟[oS] = 𝒟[Prod.map id (simOf e v) <$> oT]) :
    StepSim e v oS oT := by
  unfold StepSim
  rw [evalDist_map, h, ← evalDist_map, Functor.map_map]
  rfl

/-- A deterministic step that exposes `e` on both sides gives `StepSim`. -/
theorem StepSim.pure_stop {α : Type} (a b : α) (s' : TraceState P)
    (hstop : targetStop e s' = true) :
    StepSim e v (pure (a, simOf e v s')) (pure (b, s')) := by
  have hS : simStop e (simOf e v s') = true := hstop
  unfold StepSim
  simp [hS, hstop]

/-- `StepSim` combines over a sum of oracle implementations. -/
theorem stepSim_add {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (Inv : TraceState P → Prop)
    {i₁ : QueryImpl spec₁ (StateT (SimState P) ProbComp)}
    {i₂ : QueryImpl spec₂ (StateT (SimState P) ProbComp)}
    {j₁ : QueryImpl spec₁ (StateT (TraceState P) ProbComp)}
    {j₂ : QueryImpl spec₂ (StateT (TraceState P) ProbComp)}
    (h₁ : ∀ t s, Inv s → StepSim e v ((i₁ t).run (simOf e v s)) ((j₁ t).run s))
    (h₂ : ∀ t s, Inv s → StepSim e v ((i₂ t).run (simOf e v s)) ((j₂ t).run s)) :
    ∀ t s, Inv s → StepSim e v (((i₁ + i₂) t).run (simOf e v s)) (((j₁ + j₂) t).run s)
  | .inl t, s, hs => h₁ t s hs
  | .inr t, s, hs => h₂ t s hs

/-- `StepSim` is the per-query hypothesis of the stopped state-map comparison. -/
theorem stopOnState_simOf {ι : Type} {spec : OracleSpec ι}
    (S : QueryImpl spec (StateT (SimState P) ProbComp))
    (G : QueryImpl spec (StateT (TraceState P) ProbComp)) (q : spec.Domain) (s : TraceState P)
    (h : StepSim e v ((S q).run (simOf e v s)) ((G q).run s)) :
    𝒟[((stopOnState S (simStop e) q).run).run (simOf e v s)] =
      𝒟[Prod.map id (simOf e v) <$> ((stopOnState G (targetStop e) q).run).run s] := by
  rw [stopOnState_run, stopOnState_run, Functor.map_map]
  exact h

/-- Exact agreement survives a map of the answers. -/
theorem exact_mapAnswer {α β : Type} {oS : ProbComp (α × SimState P)}
    {oT : ProbComp (α × TraceState P)} (f : α → β)
    (h : 𝒟[oS] = 𝒟[Prod.map id (simOf e v) <$> oT]) :
    𝒟[(fun w => (f w.1, w.2)) <$> oS] =
      𝒟[Prod.map id (simOf e v) <$> ((fun w => (f w.1, w.2)) <$> oT)] := by
  rw [evalDist_map_eq_of_evalDist_eq h, Functor.map_map, Functor.map_map]
  rfl

end Step

/-- Maps agreeing on the support give the same distribution. -/
theorem evalDist_map_congr_support {α β : Type} (X : ProbComp α) (f g : α → β)
    (h : ∀ x ∈ support X, f x = g x) : 𝒟[f <$> X] = 𝒟[g <$> X] := by
  congr 1
  simp only [map_eq_bind_pure_comp]
  exact bind_congr_of_forall_mem_support X fun x hx => by simp only [Function.comp_apply, h x hx]

section Queries

variable {e : ℕ} {v : P.EpochKey}

/-- The uniform-randomness query of the trace game. -/
theorem traceUnif_run (t : ℕ) (s : TraceState P) :
    (traceUnif P t).run s = (fun a => (a, s)) <$> (QueryImpl.ofLift unifSpec ProbComp) t := by
  rw [show traceUnif P t = liftGame (SCKAScheme.oracleUnif (State P Unit) (State P Unit)
      P.EpochKey (Message P.Sym) t) from rfl, liftGame_run, SCKAScheme.oracleUnif,
    liftTarget_unif_run, Functor.map_map]

/-- The uniform-randomness query agrees. -/
theorem unif_step (t : ℕ) (s : TraceState P) :
    StepSim e v ((simUnif P t).run (simOf e v s)) ((traceUnif P t).run s) :=
  StepSim.of_eq (by
    rw [show (simUnif P t).run (simOf e v s) = _ from liftTarget_unif_run t (simOf e v s),
      traceUnif_run, Functor.map_map]
    rfl)

/-- A corruption of A on the game state. -/
theorem oracleCorruptA_run (V : State P Unit → Finset ℕ) (g : MLKEMBraid.GameState P Unit) :
    (SCKAScheme.oracleCorruptA V (State P Unit) P.EpochKey (Message P.Sym) ()).run g =
      if V g.stA ∩ g.challenged ≠ ∅ then pure (none, g)
      else pure (some g.stA, { g with exposed := g.exposed ∪ V g.stA }) := by
  simp only [SCKAScheme.oracleCorruptA, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs <;> simp [StateT.run_set, StateT.run_pure]

/-- A corruption of B on the game state. -/
theorem oracleCorruptB_run (V : State P Unit → Finset ℕ) (g : MLKEMBraid.GameState P Unit) :
    (SCKAScheme.oracleCorruptB V (State P Unit) P.EpochKey (Message P.Sym) ()).run g =
      if V g.stB ∩ g.challenged ≠ ∅ then pure (none, g)
      else pure (some g.stB, { g with exposed := g.exposed ∪ V g.stB }) := by
  simp only [SCKAScheme.oracleCorruptB, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs <;> simp [StateT.run_set, StateT.run_pure]

/-- A corruption of A agrees; a masked state exposes `e`, which stops both runs. -/
theorem corruptA_step (s : TraceState P) :
    StepSim e v ((simCorrupt P e true ()).run (simOf e v s)) ((traceCorruptA P ()).run s) := by
  have hT : (traceCorruptA P ()).run s = (fun z => (z.1, { s with game := z.2 })) <$>
      (SCKAScheme.oracleCorruptA vuln (State P Unit) P.EpochKey (Message P.Sym) ()).run
        s.game := rfl
  have hS : (simCorrupt P e true ()).run (simOf e v s) =
      if simVuln e (maskState e s.game.stA) ∩ s.game.challenged ≠ ∅ then
        pure (none, simOf e v s)
      else pure (unmask (maskState e s.game.stA), { simOf e v s with game :=
        { (simOf e v s).game with
          exposed := s.game.exposed ∪ simVuln e (maskState e s.game.stA) } }) := rfl
  rw [hT, oracleCorruptA_run, hS, simVuln_maskState]
  by_cases hc : vuln s.game.stA ∩ s.game.challenged = ∅
  · rw [if_neg (not_not.mpr hc), if_neg (not_not.mpr hc), map_pure]
    rcases hm : maskState e s.game.stA with st' | m
    · have h := maskState_eq_inl hm
      subst h
      exact StepSim.of_eq (by rw [map_pure]; rfl)
    · have he : vuln s.game.stA = {e} := by
        rw [← simVuln_maskState e s.game.stA, hm]
        rfl
      exact StepSim.pure_stop (s' := { s with game :=
        { s.game with exposed := s.game.exposed ∪ vuln s.game.stA } }) _ _
        (by simp [targetStop, he])
  · rw [if_pos hc, if_pos hc, map_pure]
    exact StepSim.of_eq (by rw [map_pure]; rfl)

/-- A corruption of B agrees; a masked state exposes `e`, which stops both runs. -/
theorem corruptB_step (s : TraceState P) :
    StepSim e v ((simCorrupt P e false ()).run (simOf e v s)) ((traceCorruptB P ()).run s) := by
  have hT : (traceCorruptB P ()).run s = (fun z => (z.1, { s with game := z.2 })) <$>
      (SCKAScheme.oracleCorruptB vuln (State P Unit) P.EpochKey (Message P.Sym) ()).run
        s.game := rfl
  have hS : (simCorrupt P e false ()).run (simOf e v s) =
      if simVuln e (maskState e s.game.stB) ∩ s.game.challenged ≠ ∅ then
        pure (none, simOf e v s)
      else pure (unmask (maskState e s.game.stB), { simOf e v s with game :=
        { (simOf e v s).game with
          exposed := s.game.exposed ∪ simVuln e (maskState e s.game.stB) } }) := rfl
  rw [hT, oracleCorruptB_run, hS, simVuln_maskState]
  by_cases hc : vuln s.game.stB ∩ s.game.challenged = ∅
  · rw [if_neg (not_not.mpr hc), if_neg (not_not.mpr hc), map_pure]
    rcases hm : maskState e s.game.stB with st' | m
    · have h := maskState_eq_inl hm
      subst h
      exact StepSim.of_eq (by rw [map_pure]; rfl)
    · have he : vuln s.game.stB = {e} := by
        rw [← simVuln_maskState e s.game.stB, hm]
        rfl
      exact StepSim.pure_stop (s' := { s with game :=
        { s.game with exposed := s.game.exposed ∪ vuln s.game.stB } }) _ _
        (by simp [targetStop, he])
  · rw [if_pos hc, if_pos hc, map_pure]
    exact StepSim.of_eq (by rw [map_pure]; rfl)

/-- The available key in the simulator view. -/
theorem simLookup_simGameOf (e : ℕ) (v : P.EpochKey) (g : MLKEMBraid.GameState P Unit) (t : ℕ) :
    simLookup (simGameOf e v g) t =
      if t = e then (lookupKey g t).map (fun _ => v) else lookupKey g t := by
  by_cases ht : t = e
  · subst ht
    cases hA : g.keyA t <;> cases hB : g.keyB t <;>
      simp [simLookup, lookupKey, simGameOf, relabel, hA, hB]
  · simp only [simLookup, lookupKey, simGameOf, relabel, if_neg ht]
    rfl

/-- The challenge query agrees, given the installed value or the key of `e`. -/
theorem challenge_step [SampleableType P.K] [SampleableType P.EpochKey]
    (xo : Option P.EpochKey) (t : ℕ) (s : TraceState P)
    (hxo : ∀ x, xo = some x → x = v)
    (hkey : xo = none → ∀ kk, lookupKey s.game e = some kk → kk = v) :
    StepSim e v
      ((simChallenge P (fun t => if t < e then .uniform else .real) t).run (simOf e v s))
      ((traceChallengeAt P (fun t => if t < e then .uniform else .real) e xo t).run s) := by
  apply StepSim.of_eq
  change 𝒟[simChallenge P _ t (simOf e v s)] =
    𝒟[Prod.map id (simOf e v) <$> traceChallengeAt P _ e xo t s]
  simp only [simChallenge, traceChallengeAt, simOf_game, simGameOf_exposed,
    simGameOf_challenged, simLookup_simGameOf]
  by_cases hex : t ∈ s.game.exposed ∨ t ∈ s.game.challenged
  · rw [if_pos hex, if_pos hex, map_pure]
    rfl
  · rw [if_neg hex, if_neg hex]
    by_cases ht : t = e
    · subst ht
      rw [if_pos rfl]
      cases hk : lookupKey s.game t with
      | none =>
          simp only [Option.map_none, map_pure]
          rfl
      | some kk =>
          simp only [Option.map_some, lt_irrefl, if_false]
          cases xo with
          | none =>
              obtain rfl := hkey rfl kk hk
              simp only [challengeValue, map_pure]
              rfl
          | some x =>
              obtain rfl := hxo x rfl
              simp only [↓reduceIte, challengeValue, map_pure]
              rfl
    · rw [if_neg ht]
      cases hk : lookupKey s.game t with
      | none =>
          simp only [map_pure]
          rfl
      | some kk =>
          cases xo with
          | none =>
              simp only [Functor.map_map]
              rfl
          | some x =>
              simp only [if_neg ht, Functor.map_map]
              rfl

end Queries

section Sends

variable (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- A send edge from an ordinary state that does not sample at `e` keeps the state ordinary and
the key unrelabelled. -/
theorem ghost_succ {e : ℕ} {v v' : P.EpochKey} {ch : Challenge P} {st : State P Unit}
    {r : SendResult P Unit} (hedge : SendEdge (auth P hMac) st r)
    (hm : maskState e st = .inl st) (hT : targetSend P hMac e ch v' st = none) :
    maskState e r.state = .inl r.state ∧ relabelKey e v r.outputKey = r.outputKey := by
  cases hedge <;> simp_all [maskState, relabelKey, targetSend]

variable [DecidableEq P.EpochKey]

/-- No sample is installed outside the sampling states of `e`. -/
theorem installedSample_eq_none (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (s : TraceState P) (party : Bool)
    (h1 : ∀ a, s.game.stateAt party ≠ .keysUnsampled e a)
    (h2 : ∀ a hdr dec, s.game.stateAt party ≠ .headerReceived e a hdr dec) :
    installedSample P hMac e kp ec s party = none := by
  unfold installedSample
  cases hst : s.game.stateAt party with
  | keysUnsampled t a =>
      have ht : t ≠ e := fun h => h1 a (by rw [hst, h])
      rcases kp with _ | ⟨pk, sk⟩
      · rfl
      · simp only [if_neg ht]
  | headerReceived t a hdr dec =>
      have ht : t ≠ e := fun h => h2 a hdr dec (by rw [hst, h])
      rcases ec with _ | ⟨es, ct1, k⟩
      · rfl
      · simp only [if_neg ht]
  | _ => rfl

/-- The trace send of a masked state. -/
theorem traceSend_masked (party leaking : Bool) (s : TraceState P) {e : ℕ} {m : Masked P}
    (hm : maskState e (s.game.stateAt party) = .inr m) {R : SendResult P Unit}
    (hR : MLKEMBraid.send P (auth P hMac) (s.game.stateAt party) = pure R) :
    traceSend P hMac irl party leaking s =
      pure (some (R.sendingEpoch, R.outputKey.map Prod.fst, R.msg, SendRand.none),
        { game := { sendUpdate s.game party R with exposed := s.game.exposed },
          transcript := s.transcript, bad := s.bad }) := by
  have h1 : ∀ t a, s.game.stateAt party ≠ .keysUnsampled t a := fun t a h => by
    rw [h] at hm
    simp [maskState] at hm
  have h2 : ∀ t a hdr dec, s.game.stateAt party ≠ .headerReceived t a hdr dec :=
    fun t a hdr dec h => by
      rw [h] at hm
      simp [maskState] at hm
  simp only [traceSend, sampledSend_of_noSample hMac irl s party h1 h2, hR, map_pure]
  simp [exposure, sendExposure]

/-- The send of a masked state agrees. -/
theorem sendStep_masked (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party leaking : Bool) (s : TraceState P)
    {m : Masked P} (hm : maskState e (s.game.stateAt party) = .inr m) :
    𝒟[(simSend P hMac irl e ch party leaking).run (simOf e v s)] =
      𝒟[Prod.map id (simOf e v) <$> (traceSendAt P hMac irl e kp ec party leaking).run s] := by
  obtain ⟨R, hR, hmsg, hep, hkey, hst⟩ := send_masked hMac hm
  have hI : installedSample P hMac e kp ec s party = none :=
    installedSample_eq_none hMac e kp ec s party
      (fun a h => by rw [h] at hm; simp [maskState] at hm)
      (fun a hdr dec h => by rw [h] at hm; simp [maskState] at hm)
  have hT : (traceSendAt P hMac irl e kp ec party leaking).run s =
      traceSend P hMac irl party leaking s := by
    change traceSendAt P hMac irl e kp ec party leaking s = _
    simp only [traceSendAt, hI]
  have hS : (simOf e v s).game.stateAt party = .inr m := by
    rw [simOf_game, simGameOf_stateAt, hm]
  rw [hT, traceSend_masked hMac irl party leaking s hm hR, map_pure]
  change 𝒟[simSend P hMac irl e ch party leaking (simOf e v s)] = _
  simp only [simSend, hS]
  congr 2
  simp only [Prod.map, id, simOf, simGameOf_sendUpdate, hmsg, hep, hkey, hst, relabelKey,
    Option.map_none]
  cases party <;> rfl

/-- The ghost sample of an ordinary state is the trace sample with `e` erased. -/
theorem ghostSample_eq (e : ℕ) (s : TraceState P) (party : Bool)
    (h1 : ∀ a, s.game.stateAt party ≠ .keysUnsampled e a)
    (h2 : ∀ a hdr dec, s.game.stateAt party ≠ .headerReceived e a hdr dec) :
    ghostSample P hMac irl (eraseAt e s.transcript) (s.game.stateAt party) =
      (fun w => (w.1, eraseAt e w.2.1)) <$> sampledSend P hMac irl s party := by
  cases hst : s.game.stateAt party with
  | keysUnsampled t a =>
      have ht : t ≠ e := fun h => h1 a (by rw [hst, h])
      rw [sampledSend_eq_keygen hMac irl s party hst, Functor.map_map]
      simp only [ghostSample]
      refine congrArg (· <$> irl.keygenRleak) (funext fun x => ?_)
      simp only [eraseAt_update_keypair e t ht]
  | headerReceived t a hdr dec =>
      have ht : t ≠ e := fun h => h2 a hdr dec (by rw [hst, h])
      rw [sampledSend_eq_encaps1 hMac irl s party hst, Functor.map_map]
      simp only [ghostSample]
      refine congrArg (· <$> irl.encaps1Rleak hdr) (funext fun x => ?_)
      simp only [eraseAt_update_encaps1 e t ht]
  | _ =>
      simp only [ghostSample, sampledSend, hst, MLKEMBraid.sendRleak, Functor.map_map]

end Sends

/-! ### Receives -/

section Receives

variable (hMac : P.Mac = Unit)

/-- The second ciphertext part of a recorded `ct2Sampled` state is the transcript's. -/
theorem ct2_of_local {T : ℕ → EpochTranscript P} {e : ℕ} {a : Unit} {ct2 : P.inc.C₂}
    {tag : P.Mac} {pk : P.PK} {sk : P.SK} {es : P.inc.St} {c1 : P.inc.C₁} {k : P.K}
    (hkp : (T e).keypair = some (pk, sk)) (hec : (T e).encaps1 = some (es, c1, k))
    (h : LocalPayloadInv (auth P hMac) () T
      (.ct2Sampled e a (EncoderState.init P.ecpCt2 (ct2, tag)))) :
    ct2 = P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk) := by
  obtain ⟨-, pk', sk', es', c1', k', hkp', hec', -, hpay⟩ := h
  obtain ⟨rfl, rfl⟩ : pk = pk' ∧ sk = sk' := by simpa using hkp.symm.trans hkp'
  obtain ⟨rfl, rfl, rfl⟩ : es = es' ∧ c1 = c1' ∧ k = k' := by simpa using hec.symm.trans hec'
  exact congrArg Prod.fst hpay

variable [DecidableEq P.Sym]

/-- A receive edge from an ordinary state keeps it ordinary and its key unrelabelled. -/
theorem recvEdge_unmasked {e : ℕ} {v : P.EpochKey} {st : State P Unit} {msg : Message P.Sym}
    {r : RecvResult P Unit} (hedge : ReceiveEdge (auth P hMac) st msg r)
    (hm : maskState e st = .inl st) :
    maskState e r.state = .inl r.state ∧ relabelKey e v r.outputKey = r.outputKey := by
  cases hedge <;> simp_all [maskState, relabelKey]

/-- The repaired receive of an ordinary state ignores the erased records of `e`. -/
theorem repairedRecv_eraseAt {e : ℕ} {T : ℕ → EpochTranscript P} {st : State P Unit}
    (msg : Message P.Sym) (hm : maskState e st = .inl st) :
    repairedRecv P hMac true (eraseAt e T) st msg = repairedRecv P hMac true T st msg := by
  cases st with
  | ekSentCt1Received t a sk ct1 dec =>
      have ht : t ≠ e := by
        rintro rfl
        simp [maskState] at hm
      rcases msg with ⟨me, mt, md⟩
      cases mt <;> cases md <;> simp [repairedRecv, eraseAt, ht]
  | _ =>
      rw [repairedRecv_eq_of_not_ekSent true _ msg (fun _ _ _ _ _ h => by cases h),
        repairedRecv_eq_of_not_ekSent true _ msg (fun _ _ _ _ _ h => by cases h)]

/-- The repaired receive of an ordinary state keeps it ordinary and its key unrelabelled. -/
theorem repairedRecv_unmasked {e : ℕ} {v : P.EpochKey} {T : ℕ → EpochTranscript P}
    {st : State P Unit} {msg : Message P.Sym} {key? : Option (ℕ × P.EpochKey)} {trcv : ℕ}
    {st' : State P Unit} (hm : maskState e st = .inl st)
    (hr : repairedRecv P hMac true T st msg = some (key?, trcv, st')) :
    maskState e st' = .inl st' ∧ relabelKey e v key? = key? := by
  have hscka : ∀ x, MLKEMBraid.recvSCKA P (auth P hMac) st msg = some x →
      maskState e x.2.2 = .inl x.2.2 ∧ relabelKey e v x.1 = x.1 := by
    intro x hx
    unfold MLKEMBraid.recvSCKA at hx
    split at hx
    · cases hx
    · rename_i r hrecv
      cases hx
      exact recvEdge_unmasked hMac (ReceiveEdge.of_eq_ok (auth P hMac) hrecv) hm
  cases st with
  | ekSentCt1Received t a sk ct1 dec =>
      have ht : t ≠ e := by
        rintro rfl
        simp [maskState] at hm
      simp only [repairedRecv, ↓reduceIte] at hr
      split at hr
      · split at hr
        · split at hr
          · cases hr
            clear hscka
            simp_all [maskState, relabelKey]
          · exact hscka _ hr
        · exact hscka _ hr
      · exact hscka _ hr
  | _ =>
      rw [repairedRecv_eq_of_not_ekSent true _ msg (fun _ _ _ _ _ h => by cases h)] at hr
      exact hscka _ hr

/-- The masked receive of `keysSampled`. -/
private theorem maskedRecv_keysSampled {e : ℕ} {v : P.EpochKey} {c2 : P.inc.C₂} {a : Unit}
    {sk : P.SK} {vec : P.inc.PKvector} {enc : EncoderState (P.inc.PKheader × P.Mac) P.Sym}
    {msg : Message P.Sym} {key? : Option (ℕ × P.EpochKey)} {trcv : ℕ} {st' : State P Unit}
    (hr : MLKEMBraid.recvSCKA P (auth P hMac) (.keysSampled e a sk vec enc) msg =
      some (key?, trcv, st')) :
    maskedRecv P hMac e c2 v (.keysSampled vec enc) msg =
      some (relabelKey e v key?, trcv, maskState e st') := by
  rcases msg with ⟨me, mt, md⟩
  by_cases he : me = e
  · subst he
    cases mt <;> cases md <;>
      simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.false_eq_true,
        Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
        Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
        ↓reduceIte] at hr <;>
      obtain ⟨rfl, rfl, rfl⟩ := hr <;>
      simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
  · cases mt <;> cases md <;>
      simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, he, Bool.false_eq_true,
        Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
        Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
        ↓reduceIte] at hr <;>
      obtain ⟨rfl, rfl, rfl⟩ := hr <;>
      simp [maskedRecv, Message.wellFormed, maskState, relabelKey, he]

/-- The masked receive of `headerSent`. -/
private theorem maskedRecv_headerSent {e : ℕ} {v : P.EpochKey} {c2 : P.inc.C₂} {a : Unit}
    {sk : P.SK} {dec : DecoderState P.inc.C₁ P.Sym} {enc : EncoderState P.inc.PKvector P.Sym}
    {msg : Message P.Sym} {key? : Option (ℕ × P.EpochKey)} {trcv : ℕ} {st' : State P Unit}
    (hr : MLKEMBraid.recvSCKA P (auth P hMac) (.headerSent e a sk dec enc) msg =
      some (key?, trcv, st')) :
    maskedRecv P hMac e c2 v (.headerSent dec enc) msg =
      some (relabelKey e v key?, trcv, maskState e st') := by
  rcases msg with ⟨me, mt, md⟩
  by_cases he : me = e
  · subst he
    cases mt
    case ct1 =>
      cases md with
      | none =>
          simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.not_false,
            Option.isSome_none, Option.some.injEq, Prod.mk.injEq, ↓reduceIte] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
      | some chunk =>
          cases hd : (dec.addChunk chunk).decodedPayload <;>
            simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, hd, Bool.false_eq_true,
              Bool.not_true, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
              ↓reduceIte] at hr <;>
            obtain ⟨rfl, rfl, rfl⟩ := hr <;>
            simp [maskedRecv, Message.wellFormed, maskState, relabelKey, hd]
    all_goals
      cases md <;>
        simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.false_eq_true,
          Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
          Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
          ↓reduceIte] at hr <;>
        obtain ⟨rfl, rfl, rfl⟩ := hr <;>
        simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
  · cases mt <;> cases md <;>
      simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, he, Bool.false_eq_true,
        Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
        Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
        ↓reduceIte] at hr <;>
      obtain ⟨rfl, rfl, rfl⟩ := hr <;>
      simp [maskedRecv, Message.wellFormed, maskState, relabelKey, he]

/-- The masked receive of `ct1Received`. -/
private theorem maskedRecv_ct1Received {e : ℕ} {v : P.EpochKey} {c2 : P.inc.C₂} {a : Unit}
    {sk : P.SK} {ct1 : P.inc.C₁} {enc : EncoderState P.inc.PKvector P.Sym}
    {msg : Message P.Sym} {key? : Option (ℕ × P.EpochKey)} {trcv : ℕ} {st' : State P Unit}
    (hr : MLKEMBraid.recvSCKA P (auth P hMac) (.ct1Received e a sk ct1 enc) msg =
      some (key?, trcv, st')) :
    maskedRecv P hMac e c2 v (.ct1Received ct1 enc) msg =
      some (relabelKey e v key?, trcv, maskState e st') := by
  rcases msg with ⟨me, mt, md⟩
  by_cases he : me = e
  · subst he
    cases mt <;> cases md <;>
      simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.false_eq_true,
        Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
        Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
        ↓reduceIte] at hr <;>
      obtain ⟨rfl, rfl, rfl⟩ := hr <;>
      simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
  · cases mt <;> cases md <;>
      simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, he, Bool.false_eq_true,
        Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
        Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
        ↓reduceIte] at hr <;>
      obtain ⟨rfl, rfl, rfl⟩ := hr <;>
      simp [maskedRecv, Message.wellFormed, maskState, relabelKey, he]

/-- The masked receive of `ekSentCt1Received`: the repaired completion outputs the test key. -/
private theorem maskedRecv_ekSent {e : ℕ} {v : P.EpochKey} {c2 : P.inc.C₂}
    {T : ℕ → EpochTranscript P} {a : Unit} {sk : P.SK} {ct1 : P.inc.C₁}
    {dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym} {x : P.inc.St × P.inc.C₁ × P.K}
    (hE : (T e).encaps1 = some x)
    {msg : Message P.Sym} {key? : Option (ℕ × P.EpochKey)} {trcv : ℕ} {st' : State P Unit}
    (hr : repairedRecv P hMac true T (.ekSentCt1Received e a sk ct1 dec) msg =
      some (key?, trcv, st')) :
    maskedRecv P hMac e c2 v (.ekSentCt1Received ct1 dec) msg =
      some (relabelKey e v key?, trcv, maskState e st') := by
  obtain ⟨es0, c10, k0⟩ := x
  rcases msg with ⟨me, mt, md⟩
  by_cases he : me = e
  · subst he
    cases mt
    case ct2 =>
      cases md with
      | none =>
          simp only [repairedRecv, MLKEMBraid.recvSCKA, receive, Message.wellFormed,
            Bool.not_false, Option.isSome_none, Option.some.injEq, Prod.mk.injEq,
            ↓reduceIte] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
      | some chunk =>
          cases hd : (dec.addChunk chunk).decodedPayload <;>
            simp only [repairedRecv, MLKEMBraid.recvSCKA, receive, Message.wellFormed, hd, hE,
              Bool.and_self, Bool.false_eq_true, Bool.not_true, decide_true,
              Option.isSome_some, Option.some.injEq, Prod.mk.injEq, ↓reduceIte] at hr <;>
            obtain ⟨rfl, rfl, rfl⟩ := hr <;>
            simp [maskedRecv, Message.wellFormed, maskState, relabelKey, hd]
    all_goals
      cases md <;>
        simp only [repairedRecv, MLKEMBraid.recvSCKA, receive, Message.wellFormed,
          Bool.false_eq_true, Bool.not_false, Bool.not_true, Option.isNone_none,
          Option.isNone_some, Option.isSome_none, Option.isSome_some, Option.some.injEq,
          Prod.mk.injEq, ↓reduceIte] at hr <;>
        obtain ⟨rfl, rfl, rfl⟩ := hr <;>
        simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
  · cases mt <;> cases md <;>
      simp only [repairedRecv, MLKEMBraid.recvSCKA, receive, Message.wellFormed, he,
        Bool.and_false, Bool.false_eq_true, Bool.not_false, Bool.not_true, decide_false,
        Option.isNone_none, Option.isNone_some, Option.isSome_none, Option.isSome_some,
        Option.some.injEq, Prod.mk.injEq, ↓reduceIte] at hr <;>
      obtain ⟨rfl, rfl, rfl⟩ := hr <;>
      simp [maskedRecv, Message.wellFormed, maskState, relabelKey, he]

/-- The masked receive of `ct1Sampled`: a completed vector gives the challenge `ct₂`. -/
private theorem maskedRecv_ct1Sampled {e : ℕ} {v : P.EpochKey} {c2 : P.inc.C₂}
    {T : ℕ → EpochTranscript P} {hdr : P.inc.PKheader} {es : P.inc.St} {c1 : P.inc.C₁}
    {enc : EncoderState P.inc.C₁ P.Sym} {dec : DecoderState P.inc.PKvector P.Sym}
    (hloc : LocalPayloadInv (auth P hMac) () T (.ct1Sampled e () hdr es c1 enc dec))
    (hc2 : ∀ pk sk es c1 k, (T e).keypair = some (pk, sk) → (T e).encaps1 = some (es, c1, k) →
      c2 = P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk))
    {msg : Message P.Sym} {key? : Option (ℕ × P.EpochKey)} {trcv : ℕ} {st' : State P Unit}
    (hr : MLKEMBraid.recvSCKA P (auth P hMac) (.ct1Sampled e () hdr es c1 enc dec) msg =
      some (key?, trcv, st'))
    (hloc' : LocalPayloadInv (auth P hMac) () T st') :
    maskedRecv P hMac e c2 v (.ct1Sampled hdr c1 enc dec) msg =
      some (relabelKey e v key?, trcv, maskState e st') := by
  obtain ⟨-, pk, sk, k, hkp, hec, -⟩ := hloc
  rcases msg with ⟨me, mt, md⟩
  by_cases he : me = e
  · subst he
    cases mt
    case ek =>
      cases md with
      | none =>
          simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.not_false,
            Option.isSome_none, Option.some.injEq, Prod.mk.injEq, ↓reduceIte] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
      | some chunk =>
          cases hd : (dec.addChunk chunk).decodedPayload with
          | none =>
              simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, hd,
                Bool.false_eq_true, Bool.not_true, Option.isSome_some, Option.some.injEq,
                Prod.mk.injEq, ↓reduceIte] at hr
              obtain ⟨rfl, rfl, rfl⟩ := hr
              simp [maskedRecv, Message.wellFormed, maskState, relabelKey, hd]
          | some vec =>
              by_cases hv : P.inc.validPK hdr vec = true
              · simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, hd, hv,
                  Bool.false_eq_true, Bool.not_true, Option.isSome_some, Option.some.injEq,
                  Prod.mk.injEq, ↓reduceIte] at hr
                obtain ⟨rfl, rfl, rfl⟩ := hr
                simp [maskedRecv, Message.wellFormed, maskState, relabelKey, hd, hv]
              · simp [MLKEMBraid.recvSCKA, receive, Message.wellFormed, hd, hv] at hr
    case ekCt1Ack =>
      cases md with
      | none =>
          simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.not_false,
            Option.isSome_none, Option.some.injEq, Prod.mk.injEq, ↓reduceIte] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
      | some chunk =>
          cases hd : (dec.addChunk chunk).decodedPayload with
          | none =>
              simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, hd,
                Bool.false_eq_true, Bool.not_true, Option.isSome_some, Option.some.injEq,
                Prod.mk.injEq, ↓reduceIte] at hr
              obtain ⟨rfl, rfl, rfl⟩ := hr
              simp [maskedRecv, Message.wellFormed, maskState, relabelKey, hd]
          | some vec =>
              by_cases hv : P.inc.validPK hdr vec = true
              · simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, hd, hv,
                  Bool.false_eq_true, Bool.not_true, Option.isSome_some, Option.some.injEq,
                  Prod.mk.injEq, ↓reduceIte] at hr
                obtain ⟨rfl, rfl, rfl⟩ := hr
                have h2 : P.hEnc2.encaps2Det es hdr vec = c2 := by
                  rw [hc2 pk sk es c1 k hkp hec]
                  exact ct2_of_local hMac hkp hec hloc'
                simp [maskedRecv, Message.wellFormed, maskState, relabelKey, hd, hv, h2]
              · simp [MLKEMBraid.recvSCKA, receive, Message.wellFormed, hd, hv] at hr
    all_goals
      cases md <;>
        simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.false_eq_true,
          Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
          Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
          ↓reduceIte] at hr <;>
        obtain ⟨rfl, rfl, rfl⟩ := hr <;>
        simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
  · cases mt <;> cases md <;>
      simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, he, Bool.false_eq_true,
        Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
        Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
        ↓reduceIte] at hr <;>
      obtain ⟨rfl, rfl, rfl⟩ := hr <;>
      simp [maskedRecv, Message.wellFormed, maskState, relabelKey, he]

/-- The masked receive of `ekReceivedCt1Sampled`: the acknowledgement gives the challenge `ct₂`. -/
private theorem maskedRecv_ekReceived {e : ℕ} {v : P.EpochKey} {c2 : P.inc.C₂}
    {T : ℕ → EpochTranscript P} {es : P.inc.St} {c1 : P.inc.C₁} {hdr : P.inc.PKheader}
    {vec : P.inc.PKvector} {enc : EncoderState P.inc.C₁ P.Sym}
    (hloc : LocalPayloadInv (auth P hMac) () T (.ekReceivedCt1Sampled e () es c1 hdr vec enc))
    (hc2 : ∀ pk sk es c1 k, (T e).keypair = some (pk, sk) → (T e).encaps1 = some (es, c1, k) →
      c2 = P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk))
    {msg : Message P.Sym} {key? : Option (ℕ × P.EpochKey)} {trcv : ℕ} {st' : State P Unit}
    (hr : MLKEMBraid.recvSCKA P (auth P hMac) (.ekReceivedCt1Sampled e () es c1 hdr vec enc)
      msg = some (key?, trcv, st'))
    (hloc' : LocalPayloadInv (auth P hMac) () T st') :
    maskedRecv P hMac e c2 v (.ekReceivedCt1Sampled c1 hdr vec enc) msg =
      some (relabelKey e v key?, trcv, maskState e st') := by
  obtain ⟨-, pk, sk, k, hkp, hec, -⟩ := hloc
  rcases msg with ⟨me, mt, md⟩
  by_cases he : me = e
  · subst he
    cases mt
    case ekCt1Ack =>
      cases md with
      | none =>
          simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.not_false,
            Option.isSome_none, Option.some.injEq, Prod.mk.injEq, ↓reduceIte] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
      | some chunk =>
          simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.false_eq_true,
            Bool.not_true, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
            ↓reduceIte] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          have h2 : P.hEnc2.encaps2Det es hdr vec = c2 := by
            rw [hc2 pk sk es c1 k hkp hec]
            exact ct2_of_local hMac hkp hec hloc'
          simp [maskedRecv, Message.wellFormed, maskState, relabelKey, h2]
    all_goals
      cases md <;>
        simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.false_eq_true,
          Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
          Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
          ↓reduceIte] at hr <;>
        obtain ⟨rfl, rfl, rfl⟩ := hr <;>
        simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
  · cases mt <;> cases md <;>
      simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, he, Bool.false_eq_true,
        Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
        Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
        ↓reduceIte] at hr <;>
      obtain ⟨rfl, rfl, rfl⟩ := hr <;>
      simp [maskedRecv, Message.wellFormed, maskState, relabelKey, he]

/-- The masked receive of `ct1Acknowledged`: a completed vector gives the challenge `ct₂`. -/
private theorem maskedRecv_ct1Acknowledged {e : ℕ} {v : P.EpochKey} {c2 : P.inc.C₂}
    {T : ℕ → EpochTranscript P} {hdr : P.inc.PKheader} {es : P.inc.St} {c1 : P.inc.C₁}
    {dec : DecoderState P.inc.PKvector P.Sym}
    (hloc : LocalPayloadInv (auth P hMac) () T (.ct1Acknowledged e () hdr es c1 dec))
    (hc2 : ∀ pk sk es c1 k, (T e).keypair = some (pk, sk) → (T e).encaps1 = some (es, c1, k) →
      c2 = P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk))
    {msg : Message P.Sym} {key? : Option (ℕ × P.EpochKey)} {trcv : ℕ} {st' : State P Unit}
    (hr : MLKEMBraid.recvSCKA P (auth P hMac) (.ct1Acknowledged e () hdr es c1 dec) msg =
      some (key?, trcv, st'))
    (hloc' : LocalPayloadInv (auth P hMac) () T st') :
    maskedRecv P hMac e c2 v (.ct1Acknowledged hdr c1 dec) msg =
      some (relabelKey e v key?, trcv, maskState e st') := by
  obtain ⟨-, pk, sk, k, hkp, hec, -⟩ := hloc
  rcases msg with ⟨me, mt, md⟩
  by_cases he : me = e
  · subst he
    cases mt
    case ekCt1Ack =>
      cases md with
      | none =>
          simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.not_false,
            Option.isSome_none, Option.some.injEq, Prod.mk.injEq, ↓reduceIte] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
      | some chunk =>
          cases hd : (dec.addChunk chunk).decodedPayload with
          | none =>
              simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, hd,
                Bool.false_eq_true, Bool.not_true, Option.isSome_some, Option.some.injEq,
                Prod.mk.injEq, ↓reduceIte] at hr
              obtain ⟨rfl, rfl, rfl⟩ := hr
              simp [maskedRecv, Message.wellFormed, maskState, relabelKey, hd]
          | some vec =>
              by_cases hv : P.inc.validPK hdr vec = true
              · simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, hd, hv,
                  Bool.false_eq_true, Bool.not_true, Option.isSome_some, Option.some.injEq,
                  Prod.mk.injEq, ↓reduceIte] at hr
                obtain ⟨rfl, rfl, rfl⟩ := hr
                have h2 : P.hEnc2.encaps2Det es hdr vec = c2 := by
                  rw [hc2 pk sk es c1 k hkp hec]
                  exact ct2_of_local hMac hkp hec hloc'
                simp [maskedRecv, Message.wellFormed, maskState, relabelKey, hd, hv, h2]
              · simp [MLKEMBraid.recvSCKA, receive, Message.wellFormed, hd, hv] at hr
    all_goals
      cases md <;>
        simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, Bool.false_eq_true,
          Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
          Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
          ↓reduceIte] at hr <;>
        obtain ⟨rfl, rfl, rfl⟩ := hr <;>
        simp [maskedRecv, Message.wellFormed, maskState, relabelKey]
  · cases mt <;> cases md <;>
      simp only [MLKEMBraid.recvSCKA, receive, Message.wellFormed, he, Bool.false_eq_true,
        Bool.not_false, Bool.not_true, Option.isNone_none, Option.isNone_some,
        Option.isSome_none, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
        ↓reduceIte] at hr <;>
      obtain ⟨rfl, rfl, rfl⟩ := hr <;>
      simp [maskedRecv, Message.wellFormed, maskState, relabelKey, he]

/-- The masked receive mirrors the repaired receive of the corresponding state, with the challenge
`ct₂` and the derived test key. -/
theorem maskedRecv_eq {e : ℕ} {v : P.EpochKey} {c2 : P.inc.C₂} {T : ℕ → EpochTranscript P}
    {st : State P Unit} {m : Masked P} (hm : maskState e st = .inr m)
    (hloc : LocalPayloadInv (auth P hMac) () T st)
    (hc2 : ∀ pk sk es c1 k, (T e).keypair = some (pk, sk) → (T e).encaps1 = some (es, c1, k) →
      c2 = P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk))
    {msg : Message P.Sym} {key? : Option (ℕ × P.EpochKey)} {trcv : ℕ} {st' : State P Unit}
    (hr : repairedRecv P hMac true T st msg = some (key?, trcv, st'))
    (hloc' : LocalPayloadInv (auth P hMac) () T st') :
    maskedRecv P hMac e c2 v m msg = some (relabelKey e v key?, trcv, maskState e st') := by
  cases st with
  | keysUnsampled t a => simp [maskState] at hm
  | noHeaderReceived t a dec => simp [maskState] at hm
  | headerReceived t a hdr dec => simp [maskState] at hm
  | ct2Sampled t a enc => simp [maskState] at hm
  | keysSampled t a sk vec enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        rw [repairedRecv_eq_of_not_ekSent true T msg (fun _ _ _ _ _ h => by cases h)] at hr
        exact maskedRecv_keysSampled hMac hr
      · simp [maskState, ht] at hm
  | headerSent t a sk dec enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        rw [repairedRecv_eq_of_not_ekSent true T msg (fun _ _ _ _ _ h => by cases h)] at hr
        exact maskedRecv_headerSent hMac hr
      · simp [maskState, ht] at hm
  | ct1Received t a sk ct1 enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        rw [repairedRecv_eq_of_not_ekSent true T msg (fun _ _ _ _ _ h => by cases h)] at hr
        exact maskedRecv_ct1Received hMac hr
      · simp [maskState, ht] at hm
  | ekSentCt1Received t a sk ct1 dec =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        obtain ⟨-, pk, es0, k0, -, hE, -⟩ := hloc
        exact maskedRecv_ekSent hMac hE hr
      · simp [maskState, ht] at hm
  | ct1Sampled t a hdr es ct1 enc dec =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        cases a
        rw [repairedRecv_eq_of_not_ekSent true T msg (fun _ _ _ _ _ h => by cases h)] at hr
        exact maskedRecv_ct1Sampled hMac hloc hc2 hr hloc'
      · simp [maskState, ht] at hm
  | ekReceivedCt1Sampled t a es ct1 hdr vec enc =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        cases a
        rw [repairedRecv_eq_of_not_ekSent true T msg (fun _ _ _ _ _ h => by cases h)] at hr
        exact maskedRecv_ekReceived hMac hloc hc2 hr hloc'
      · simp [maskState, ht] at hm
  | ct1Acknowledged t a hdr es ct1 dec =>
      by_cases ht : t = e
      · subst ht
        simp only [maskState, ↓reduceIte] at hm
        cases hm
        cases a
        rw [repairedRecv_eq_of_not_ekSent true T msg (fun _ _ _ _ _ h => by cases h)] at hr
        exact maskedRecv_ct1Acknowledged hMac hloc hc2 hr hloc'
      · simp [maskState, ht] at hm

/-- The simulator's receive of the masked view mirrors the repaired receive. -/
theorem simRecv_eq {e : ℕ} {v : P.EpochKey} (ch : Challenge P) (hv : P.kdfOK ch.key e = v)
    {T : ℕ → EpochTranscript P} {st : State P Unit} {msg : Message P.Sym}
    {key? : Option (ℕ × P.EpochKey)} {trcv : ℕ} {st' : State P Unit}
    (hloc : LocalPayloadInv (auth P hMac) () T st)
    (hc2 : ∀ pk sk es c1 k, (T e).keypair = some (pk, sk) → (T e).encaps1 = some (es, c1, k) →
      ch.ct2 = P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk))
    (hr : repairedRecv P hMac true T st msg = some (key?, trcv, st'))
    (hloc' : LocalPayloadInv (auth P hMac) () T st') :
    simRecv P hMac e ch (P.kdfOK ch.key e) (eraseAt e T) (maskState e st) msg =
      some (relabelKey e v key?, trcv, maskState e st') := by
  rcases hm : maskState e st with st0 | m
  · obtain rfl := maskState_eq_inl hm
    obtain ⟨h1, h2⟩ := repairedRecv_unmasked hMac (v := v) hm hr
    simp only [simRecv, repairedRecv_eraseAt hMac msg hm, hr, Option.map_some, h1, h2]
  · simp only [simRecv, hv]
    exact maskedRecv_eq hMac hm hloc hc2 hr hloc'

end Receives

/-! ### The once-used key pair and first-stage sample -/

section Installs

variable [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- The ordinary key-generation send of `e`, lazily. -/
theorem plain_keygen_on (e : ℕ) (party : Bool) (s : TraceState P) {a0 : Unit}
    (hst : s.game.stateAt party = .keysUnsampled e a0) :
    𝒟[(tracePlainAt P hMac irl e none none party ()).run s] =
      𝒟[P.kem.keygen >>= fun x => (tracePlainAt P hMac irl e (some x) none party ()).run s] := by
  have hL : (tracePlainAt P hMac irl e none none party ()).run s =
      (fun y : (P.PK × P.SK) × irl.KeygenRand =>
        (some (e - 1, none, (keygenStep P hMac e a0 y.1.1 y.1.2).msg),
          keygenState hMac s party false e a0 y.1)) <$> irl.keygenRleak := by
    simp only [tracePlainAt, StateT.run_map, traceSendAt_none,
      traceSend_keygen_run hMac irl false hst, Functor.map_map]
    congr 1
  have hI : ∀ x, (tracePlainAt P hMac irl e (some x) none party ()).run s =
      pure (some (e - 1, none, (keygenStep P hMac e a0 x.1 x.2).msg),
        keygenState hMac s party false e a0 x) := by
    intro x
    simp only [tracePlainAt, StateT.run_map, traceSendAt_keygen_run hMac irl false hst x none]
    simp
  rw [hL, keygen_eq_map irl, bind_map_left]
  simp only [hI, map_eq_bind_pure_comp]
  rfl

/-- The leaking key-generation send of `e`, lazily, when it is not refused. -/
theorem leak_keygen_on (e : ℕ) (party : Bool) (s : TraceState P) {a0 : Unit}
    (hst : s.game.stateAt party = .keysUnsampled e a0)
    (hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true) :
    𝒟[(fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
        (traceLeakAt P hMac irl e none none party ()).run s] =
      𝒟[P.kem.keygen >>= fun x => (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
        (traceLeakAt P hMac irl e (some x) none party ()).run s] := by
  have hL : (traceLeakAt P hMac irl e none none party ()).run s =
      (fun y : (P.PK × P.SK) × irl.KeygenRand =>
        (some (e - 1, none, (keygenStep P hMac e a0 y.1.1 y.1.2).msg, SendRand.keygen y.2),
          keygenState hMac s party true e a0 y.1)) <$> irl.keygenRleak := by
    change (traceSendAt P hMac irl e none none party true).run s = _
    rw [traceSendAt_none, traceSend_keygen_run hMac irl true hst]
    congr 1
    funext y
    rw [if_neg hc]
  have hstop : ∀ x, targetStop e (keygenState hMac s party true e a0 x) = true := fun x => by
    simp [targetStop, keygenState]
  have hR : ∀ x, (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceLeakAt P hMac irl e (some x) none party ()).run s =
      pure (none, keygenState hMac s party true e a0 x) := by
    intro x
    change (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceSendAt P hMac irl e (some x) none party true).run s = _
    rw [traceSendAt_keygen_run hMac irl true hst x none, if_neg hc, map_pure]
    simp only [hstop, ↓reduceIte]
  have hLHS : (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceLeakAt P hMac irl e none none party ()).run s =
      (fun y : (P.PK × P.SK) × irl.KeygenRand =>
        (none, keygenState hMac s party true e a0 y.1)) <$> irl.keygenRleak := by
    rw [hL, Functor.map_map]
    simp only [hstop, ↓reduceIte]
  rw [hLHS, keygen_eq_map irl, bind_map_left]
  simp only [hR, map_eq_bind_pure_comp]
  rfl

/-- A refused leaking key-generation send of `e` does not depend on the installed key pair. -/
theorem leak_keygen_refused (e : ℕ) (party : Bool) (s : TraceState P) {a0 : Unit}
    (hst : s.game.stateAt party = .keysUnsampled e a0)
    (hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true) (x : P.PK × P.SK) :
    𝒟[(traceLeakAt P hMac irl e (some x) none party ()).run s] =
      𝒟[(traceLeakAt P hMac irl e none none party ()).run s] := by
  have h1 : (traceLeakAt P hMac irl e (some x) none party ()).run s = pure (none, s) := by
    change (traceSendAt P hMac irl e (some x) none party true).run s = _
    rw [traceSendAt_keygen_run hMac irl true hst x none, if_pos hc]
  have h2 : (traceLeakAt P hMac irl e none none party ()).run s =
      (fun _ => (none, s)) <$> irl.keygenRleak := by
    change (traceSendAt P hMac irl e none none party true).run s = _
    rw [traceSendAt_none, traceSend_keygen_run hMac irl true hst]
    congr 1
    funext y
    rw [if_pos hc]
  rw [h1, h2, map_eq_bind_pure_comp]
  exact (evalDist_bind_ignore _ _).symm

/-- The ordinary first-stage encapsulation send of `e`, lazily. -/
theorem plain_encaps1_on (e : ℕ) (kp : Option (P.PK × P.SK)) (party : Bool) (s : TraceState P)
    {a0 : Unit} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a0 hdr dec) :
    𝒟[(tracePlainAt P hMac irl e kp none party ()).run s] =
      𝒟[P.inc.encaps1 hdr >>= fun c => (tracePlainAt P hMac irl e kp (some c) party ()).run s] := by
  have hL : (tracePlainAt P hMac irl e kp none party ()).run s =
      (fun y : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
        (some (e - 1, some e, (encaps1Step P hMac e a0 hdr dec y.1.1 y.1.2.1 y.1.2.2).msg),
          encaps1State hMac s party false e a0 hdr dec y.1)) <$> irl.encaps1Rleak hdr := by
    simp only [tracePlainAt, StateT.run_map, traceSendAt_hdr_lazy hMac irl e kp party false s hst,
      traceSend_encaps1_run hMac irl false hst, Functor.map_map]
    congr 1
  have hI : ∀ c, (tracePlainAt P hMac irl e kp (some c) party ()).run s =
      pure (some (e - 1, some e, (encaps1Step P hMac e a0 hdr dec c.1 c.2.1 c.2.2).msg),
        encaps1State hMac s party false e a0 hdr dec c) := by
    intro c
    simp only [tracePlainAt, StateT.run_map, traceSendAt_encaps1_run hMac irl false hst kp c]
    simp
  rw [hL, encaps1_eq_map irl, bind_map_left]
  simp only [hI, map_eq_bind_pure_comp]
  rfl

/-- The leaking first-stage encapsulation send of `e`, lazily, when it is not refused. -/
theorem leak_encaps1_on (e : ℕ) (kp : Option (P.PK × P.SK)) (party : Bool) (s : TraceState P)
    {a0 : Unit} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a0 hdr dec)
    (hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true) :
    𝒟[(fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
        (traceLeakAt P hMac irl e kp none party ()).run s] =
      𝒟[P.inc.encaps1 hdr >>= fun c => (fun w => (if targetStop e w.2 then none else some w.1,
        w.2)) <$> (traceLeakAt P hMac irl e kp (some c) party ()).run s] := by
  have hL : (traceLeakAt P hMac irl e kp none party ()).run s =
      (fun y : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
        (some (e - 1, some e, (encaps1Step P hMac e a0 hdr dec y.1.1 y.1.2.1 y.1.2.2).msg,
          SendRand.encaps1 y.2), encaps1State hMac s party true e a0 hdr dec y.1)) <$>
        irl.encaps1Rleak hdr := by
    change (traceSendAt P hMac irl e kp none party true).run s = _
    rw [traceSendAt_hdr_lazy hMac irl e kp party true s hst,
      traceSend_encaps1_run hMac irl true hst]
    congr 1
    funext y
    rw [if_neg hc]
  have hstop : ∀ c, targetStop e (encaps1State hMac s party true e a0 hdr dec c) = true :=
    fun c => by simp [targetStop, encaps1State]
  have hR : ∀ c, (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceLeakAt P hMac irl e kp (some c) party ()).run s =
      pure (none, encaps1State hMac s party true e a0 hdr dec c) := by
    intro c
    change (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceSendAt P hMac irl e kp (some c) party true).run s = _
    rw [traceSendAt_encaps1_run hMac irl true hst kp c, if_neg hc, map_pure]
    simp only [hstop, ↓reduceIte]
  have hLHS : (fun w => (if targetStop e w.2 then none else some w.1, w.2)) <$>
      (traceLeakAt P hMac irl e kp none party ()).run s =
      (fun y : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
        (none, encaps1State hMac s party true e a0 hdr dec y.1)) <$> irl.encaps1Rleak hdr := by
    rw [hL, Functor.map_map]
    simp only [hstop, ↓reduceIte]
  rw [hLHS, encaps1_eq_map irl, bind_map_left]
  simp only [hR, map_eq_bind_pure_comp]
  rfl

/-- A refused leaking first-stage encapsulation send of `e` does not depend on the installed
sample. -/
theorem leak_encaps1_refused (e : ℕ) (kp : Option (P.PK × P.SK)) (party : Bool)
    (s : TraceState P) {a0 : Unit} {hdr : P.inc.PKheader}
    {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a0 hdr dec)
    (hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true)
    (c : P.inc.St × P.inc.C₁ × P.K) :
    𝒟[(traceLeakAt P hMac irl e kp (some c) party ()).run s] =
      𝒟[(traceLeakAt P hMac irl e kp none party ()).run s] := by
  have h1 : (traceLeakAt P hMac irl e kp (some c) party ()).run s = pure (none, s) := by
    change (traceSendAt P hMac irl e kp (some c) party true).run s = _
    rw [traceSendAt_encaps1_run hMac irl true hst kp c, if_pos hc]
  have h2 : (traceLeakAt P hMac irl e kp none party ()).run s =
      (fun _ => (none, s)) <$> irl.encaps1Rleak hdr := by
    change (traceSendAt P hMac irl e kp none party true).run s = _
    rw [traceSendAt_hdr_lazy hMac irl e kp party true s hst,
      traceSend_encaps1_run hMac irl true hst]
    congr 1
    funext y
    rw [if_pos hc]
  rw [h1, h2, map_eq_bind_pure_comp]
  exact (evalDist_bind_ignore _ _).symm

end Installs

/-! ### The invariant of the installed games -/

/-- The invariant of an installed trace game: the repaired trace invariant, and the records of
`e` are unrecorded or the installed samples. -/
def InstInv (hMac : P.Mac = Unit) (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (s : TraceState P) : Prop :=
  TraceInv hMac true s ∧
    (∀ x, kp = some x → (s.transcript e).keypair = none ∨ (s.transcript e).keypair = some x) ∧
    (∀ c, ec = some c → (s.transcript e).encaps1 = none ∨ (s.transcript e).encaps1 = some c)

section InstInvLemmas

variable (hMac : P.Mac = Unit)

/-- Under `InstInv`, a first-stage encapsulation of `e` reads the installed header. -/
theorem InstInv.header {e : ℕ} {x : P.PK × P.SK} {ec : Option (P.inc.St × P.inc.C₁ × P.K)}
    {s : TraceState P} (hs : InstInv hMac e (some x) ec s) {party : Bool} {a : Unit}
    {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a hdr dec) : hdr = P.inc.toHeader x.1 := by
  have hl := (hs.1.1 (Or.inl rfl)).1.local party
  rw [hst] at hl
  obtain ⟨-, -, pk, sk, hkp', hhdr, -⟩ := hl
  rcases hs.2.1 x rfl with h0 | h0
  · rw [h0] at hkp'
    cases hkp'
  · rw [h0] at hkp'
    obtain rfl : x = (pk, sk) := Option.some.inj hkp'
    exact hhdr

/-- Under the repaired invariant, a recorded key pair of `e` excludes its key generation. -/
theorem isKeygenAt_false {s : TraceState P} (hs : TraceInv hMac true s) {e : ℕ}
    (hu : (s.transcript e).keypair ≠ none) (p : Bool) :
    isKeygenAt e (s.game.stateAt p) = false := by
  have hl := (hs.1 (Or.inl rfl)).1.local p
  cases hst : s.game.stateAt p with
  | keysUnsampled t a =>
      rw [hst] at hl
      obtain ⟨-, hk, -⟩ := hl
      simp only [isKeygenAt, decide_eq_false_iff_not]
      rintro rfl
      exact hu hk
  | _ => rfl

/-- Under the repaired invariant, a recorded first-stage sample of `e` excludes its first-stage
encapsulation. -/
theorem isEncaps1At_false {s : TraceState P} (hs : TraceInv hMac true s) {e : ℕ}
    (hu : (s.transcript e).encaps1 ≠ none) (p : Bool) :
    isEncaps1At e (s.game.stateAt p) = false := by
  have hl := (hs.1 (Or.inl rfl)).1.local p
  cases hst : s.game.stateAt p with
  | headerReceived t a hdr dec =>
      rw [hst] at hl
      obtain ⟨-, hk, -⟩ := hl
      simp only [isEncaps1At, decide_eq_false_iff_not]
      rintro rfl
      exact hu hk
  | _ => rfl

/-- An installed challenge keeps the trace invariant of the repaired game. -/
theorem traceChallengeAt_traceInv [SampleableType P.K] [SampleableType P.EpochKey]
    (mode : ℕ → Mode) (e : ℕ) (x : Option P.EpochKey) :
    QueryImpl.PreservesInv (traceChallengeAt P mode e x) (TraceInv hMac true) := by
  intro t s hs z hz
  rcases mem_support_traceChallengeAt hz with hz | ⟨hex, hz⟩
  · rw [hz]
    exact hs
  · rw [hz]
    refine ⟨fun _ => ⟨(hs.1 (Or.inl rfl)).1.setFlags _ _, fun h => absurd h (by decide)⟩, ?_⟩
    change s.game.exposed ∩ insert t s.game.challenged = ∅
    rw [Finset.inter_insert_of_notMem hex]
    exact hs.2

end InstInvLemmas

section Dispatch

variable [SampleableType P.K] [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
  [DecidableEq P.Sym] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- Every query records at most one sample, the installed one at `e`. -/
theorem traceImplAt_transcriptStep (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ q s z, z ∈ support ((traceImplAt P hMac irl e kp ec xo m q).run s) →
      TranscriptStep e kp ec s z.2 :=
  relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _
    (relStep_add _ (relStep_add _ (relStep_add _ (relStep_add _
      (fun t s z hz => by
        obtain ⟨w, -, rfl⟩ := mem_support_liftGame
          (c := SCKAScheme.oracleUnif (State P Unit) (State P Unit) P.EpochKey (Message P.Sym)
            t) hz
        exact Or.inl rfl)
      (fun t s z hz => by
        obtain ⟨w, hw, rfl⟩ := mem_support_tracePlainAt hMac irl hz
        exact traceSendAt_transcriptStep hMac irl e kp ec true false s hw))
      (fun t s z hz => by
        obtain ⟨w, hw, rfl⟩ := mem_support_tracePlainAt hMac irl hz
        exact traceSendAt_transcriptStep hMac irl e kp ec false false s hw))
      (fun n s z hz => by
        rw [traceReceive_run] at hz
        obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
        exact Or.inl rfl))
      (fun n s z hz => by
        rw [traceReceive_run] at hz
        obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
        exact Or.inl rfl))
      (fun t s z hz => traceSendAt_transcriptStep hMac irl e kp ec true true s hz))
      (fun t s z hz => traceSendAt_transcriptStep hMac irl e kp ec false true s hz))
      (fun t s z hz => by
        rcases mem_support_traceChallengeAt hz with h | ⟨-, h⟩ <;> exact Or.inl (by rw [h])))
      (fun t s z hz => by
        obtain ⟨w, -, rfl⟩ := mem_support_liftGame
          (c := SCKAScheme.oracleCorruptA vuln (State P Unit) P.EpochKey (Message P.Sym) t) hz
        exact Or.inl rfl))
      (fun t s z hz => by
        obtain ⟨w, -, rfl⟩ := mem_support_liftGame
          (c := SCKAScheme.oracleCorruptB vuln (State P Unit) P.EpochKey (Message P.Sym) t) hz
        exact Or.inl rfl)

/-- Every query of an installed game keeps the trace invariant of the repaired game. -/
theorem traceImplAt_traceInv (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct) (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct) (e : ℕ) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (xo : Option P.EpochKey) (m : ℕ → Mode)
    (hkp : ∀ x, kp = some x → x ∈ support P.kem.keygen) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), TraceInv hMac true s →
      (∀ c party a hdr dec, ec = some c → s.game.stateAt party = .headerReceived e a hdr dec →
        c ∈ support (P.inc.encaps1 hdr)) →
      ∀ z ∈ support ((traceImplAt P hMac irl e kp ec xo m q).run s), TraceInv hMac true z.2
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl t)))))))), s, hs, _, z, hz =>
      traceUnif_preservesInv hMac true t s hs z hz
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, hs, H, z, hz => by
      obtain ⟨w, hw, rfl⟩ := mem_support_tracePlainAt hMac irl hz
      exact traceSendAt_traceInv hMac irl e kp ec true false s hs hkp
        (fun c a hdr dec h1 h2 => H c true a hdr dec h1 h2) hw
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, hs, H, z, hz => by
      obtain ⟨w, hw, rfl⟩ := mem_support_tracePlainAt hMac irl hz
      exact traceSendAt_traceInv hMac irl e kp ec false false s hs hkp
        (fun c a hdr dec h1 h2 => H c false a hdr dec h1 h2) hw
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr n)))))), s, hs, _, z, hz =>
      traceReceive_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct true true
        n s hs z hz
  | .inl (.inl (.inl (.inl (.inl (.inr n))))), s, hs, _, z, hz =>
      traceReceive_preservesInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct true false
        n s hs z hz
  | .inl (.inl (.inl (.inl (.inr t)))), s, hs, H, z, hz =>
      traceSendAt_traceInv hMac irl e kp ec true true s hs hkp
        (fun c a hdr dec h1 h2 => H c true a hdr dec h1 h2) hz
  | .inl (.inl (.inl (.inr t))), s, hs, H, z, hz =>
      traceSendAt_traceInv hMac irl e kp ec false true s hs hkp
        (fun c a hdr dec h1 h2 => H c false a hdr dec h1 h2) hz
  | .inl (.inl (.inr t)), s, hs, _, z, hz => traceChallengeAt_traceInv hMac m e xo t s hs z hz
  | .inl (.inr t), s, hs, _, z, hz => traceCorruptA_preservesInv hMac true t s hs z hz
  | .inr t, s, hs, _, z, hz => traceCorruptB_preservesInv hMac true t s hs z hz

/-- Every query of an installed game keeps `InstInv`. -/
theorem traceImplAt_instInv (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct) (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct) (e : ℕ) (x : P.PK × P.SK)
    (ec ec' : Option (P.inc.St × P.inc.C₁ × P.K)) (xo : Option P.EpochKey) (m : ℕ → Mode)
    (hkp : x ∈ support P.kem.keygen)
    (hec : ∀ c, ec = some c → c ∈ support (P.inc.encaps1 (P.inc.toHeader x.1)))
    (hec' : ec' = none ∨ ec' = ec) :
    ∀ q s, InstInv hMac e (some x) ec' s →
      ∀ z ∈ support ((traceImplAt P hMac irl e (some x) ec xo m q).run s),
        InstInv hMac e (some x) ec' z.2 := by
  intro q s hs z hz
  have hstep := traceImplAt_transcriptStep hMac irl e (some x) ec xo m q s z hz
  refine ⟨traceImplAt_traceInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e
    (some x) ec xo m (fun y h => by cases h; exact hkp) q s hs.1 ?_ z hz,
    hstep.keypairAt hs.2.1, ?_⟩
  · intro c party a hdr dec hc hst
    have hrel : InstInv hMac e (some x) ec' s := hs
    rw [hrel.header hMac hst]
    exact hec c hc
  · rcases hec' with rfl | rfl
    · intro c h
      cases h
    · exact hstep.encapsAt hs.2.2

/-- A hit key generation records the installed key pair. -/
theorem keygen_hit_records (e : ℕ) (x : P.PK × P.SK) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), sendHit (isKeygenAt e) e q s = true →
      ∀ w ∈ support ((traceImplAt P hMac irl e (some x) none xo m q).run s),
        (w.2.transcript e).keypair ≠ none
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, h, w, hw => by
      have h' : isKeygenAt e (s.game.stateAt true) = true := h
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true h'
      obtain ⟨u, hu, rfl⟩ := mem_support_tracePlainAt hMac irl hw
      exact traceSendAt_keygen_records hMac irl hst x (by simp) hu
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, h, w, hw => by
      have h' : isKeygenAt e (s.game.stateAt false) = true := h
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true h'
      obtain ⟨u, hu, rfl⟩ := mem_support_tracePlainAt hMac irl hw
      exact traceSendAt_keygen_records hMac irl hst x (by simp) hu
  | .inl (.inl (.inl (.inl (.inr t)))), s, h, w, hw => by
      have h' : (isKeygenAt e (s.game.stateAt true) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      exact traceSendAt_keygen_records hMac irl hst x hc hw
  | .inl (.inl (.inl (.inr t))), s, h, w, hw => by
      have h' : (isKeygenAt e (s.game.stateAt false) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      exact traceSendAt_keygen_records hMac irl hst x hc hw
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))), _, h, _, _ => by
      simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inr _))))), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inl (.inr _)), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inr _), _, h, _, _ => by simp [sendHit] at h
  | .inr _, _, h, _, _ => by simp [sendHit] at h

/-- A hit first-stage encapsulation records the installed sample. -/
theorem encaps1_hit_records (e : ℕ) (kp : Option (P.PK × P.SK))
    (c : P.inc.St × P.inc.C₁ × P.K) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), sendHit (isEncaps1At e) e q s = true →
      ∀ w ∈ support ((traceImplAt P hMac irl e kp (some c) xo m q).run s),
        (w.2.transcript e).encaps1 ≠ none
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, h, w, hw => by
      have h' : isEncaps1At e (s.game.stateAt true) = true := h
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true h'
      obtain ⟨u, hu, rfl⟩ := mem_support_tracePlainAt hMac irl hw
      exact traceSendAt_encaps1_records hMac irl hst kp c (by simp) hu
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, h, w, hw => by
      have h' : isEncaps1At e (s.game.stateAt false) = true := h
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true h'
      obtain ⟨u, hu, rfl⟩ := mem_support_tracePlainAt hMac irl hw
      exact traceSendAt_encaps1_records hMac irl hst kp c (by simp) hu
  | .inl (.inl (.inl (.inl (.inr t)))), s, h, w, hw => by
      have h' : (isEncaps1At e (s.game.stateAt true) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      exact traceSendAt_encaps1_records hMac irl hst kp c hc hw
  | .inl (.inl (.inl (.inr t))), s, h, w, hw => by
      have h' : (isEncaps1At e (s.game.stateAt false) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      exact traceSendAt_encaps1_records hMac irl hst kp c hc hw
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))), _, h, _, _ => by
      simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inr _))))), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inl (.inr _)), _, h, _, _ => by simp [sendHit] at h
  | .inl (.inr _), _, h, _, _ => by simp [sendHit] at h
  | .inr _, _, h, _, _ => by simp [sendHit] at h

/-- The queries other than sends ignore the installed samples. -/
theorem traceImplAt_offSend (e : ℕ) (kp kp' : Option (P.PK × P.SK))
    (ec ec' : Option (P.inc.St × P.inc.C₁ × P.K)) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), NonSend q →
      𝒟[((stopOnState (traceImplAt P hMac irl e kp ec xo m) (targetStop e) q).run).run s] =
        𝒟[((stopOnState (traceImplAt P hMac irl e kp' ec' xo m) (targetStop e) q).run).run s]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl t)))))))), s, _ =>
      stopped_congr _ _ s (by
        change 𝒟[(traceUnif P t).run s] = 𝒟[(traceUnif P t).run s]
        rfl)
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr n)))))), s, _ =>
      stopped_congr _ _ s (by
        change 𝒟[(traceReceive P hMac irl true true n).run s] =
          𝒟[(traceReceive P hMac irl true true n).run s]
        rfl)
  | .inl (.inl (.inl (.inl (.inl (.inr n))))), s, _ =>
      stopped_congr _ _ s (by
        change 𝒟[(traceReceive P hMac irl true false n).run s] =
          𝒟[(traceReceive P hMac irl true false n).run s]
        rfl)
  | .inl (.inl (.inr t)), s, _ =>
      stopped_congr _ _ s (by
        change 𝒟[(traceChallengeAt P m e xo t).run s] = 𝒟[(traceChallengeAt P m e xo t).run s]
        rfl)
  | .inl (.inr t), s, _ =>
      stopped_congr _ _ s (by
        change 𝒟[(traceCorruptA P t).run s] = 𝒟[(traceCorruptA P t).run s]
        rfl)
  | .inr t, s, _ =>
      stopped_congr _ _ s (by
        change 𝒟[(traceCorruptB P t).run s] = 𝒟[(traceCorruptB P t).run s]
        rfl)
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))))), _, h => False.elim h
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _))))))), _, h => False.elim h
  | .inl (.inl (.inl (.inl (.inr _)))), _, h => False.elim h
  | .inl (.inl (.inl (.inr _))), _, h => False.elim h

/-- Off a hit, installing a key pair changes no query. -/
theorem keygen_off (e : ℕ) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), sendHit (isKeygenAt e) e q s = false →
      ∀ x, 𝒟[((stopOnState (traceImplAt P hMac irl e (some x) none xo m) (targetStop e) q).run).run
          s] =
        𝒟[((stopOnState (traceImplAt P hMac irl e none none xo m) (targetStop e) q).run).run s]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, h, x => by
      cases t
      refine stopped_congr _ _ s ?_
      change 𝒟[(tracePlainAt P hMac irl e (some x) none true ()).run s] =
        𝒟[(tracePlainAt P hMac irl e none none true ()).run s]
      simp only [tracePlainAt, StateT.run_map, traceSendAt_kp_off hMac irl e x true false s h]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, h, x => by
      cases t
      refine stopped_congr _ _ s ?_
      change 𝒟[(tracePlainAt P hMac irl e (some x) none false ()).run s] =
        𝒟[(tracePlainAt P hMac irl e none none false ()).run s]
      simp only [tracePlainAt, StateT.run_map, traceSendAt_kp_off hMac irl e x false false s h]
  | .inl (.inl (.inl (.inl (.inr t)))), s, h, x => by
      cases t
      refine stopped_congr _ _ s ?_
      by_cases hk : isKeygenAt e (s.game.stateAt true) = true
      · obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
        have hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by
          simpa [sendHit, hk] using h
        exact leak_keygen_refused hMac irl e true s hst hc x
      · change 𝒟[(traceSendAt P hMac irl e (some x) none true true).run s] =
          𝒟[(traceSendAt P hMac irl e none none true true).run s]
        rw [traceSendAt_kp_off hMac irl e x true true s (by simpa using hk)]
  | .inl (.inl (.inl (.inr t))), s, h, x => by
      cases t
      refine stopped_congr _ _ s ?_
      by_cases hk : isKeygenAt e (s.game.stateAt false) = true
      · obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
        have hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by
          simpa [sendHit, hk] using h
        exact leak_keygen_refused hMac irl e false s hst hc x
      · change 𝒟[(traceSendAt P hMac irl e (some x) none false true).run s] =
          𝒟[(traceSendAt P hMac irl e none none false true).run s]
        rw [traceSendAt_kp_off hMac irl e x false true s (by simpa using hk)]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl t)))))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr n)))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inl (.inl (.inl (.inr n))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inr t)), s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inr t), s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inr t, s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial

/-- At a hit, the lazy key generation is the installed one with a sampled key pair. -/
theorem keygen_on (e : ℕ) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), sendHit (isKeygenAt e) e q s = true →
      𝒟[((stopOnState (traceImplAt P hMac irl e none none xo m) (targetStop e) q).run).run s] =
        𝒟[P.kem.keygen >>= fun x =>
          ((stopOnState (traceImplAt P hMac irl e (some x) none xo m) (targetStop e) q).run).run
            s]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, h => by
      have h' : isKeygenAt e (s.game.stateAt true) = true := h
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true h'
      cases t
      exact stopped_bind _ _ _ s (plain_keygen_on hMac irl e true s hst)
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, h => by
      have h' : isKeygenAt e (s.game.stateAt false) = true := h
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true h'
      cases t
      exact stopped_bind _ _ _ s (plain_keygen_on hMac irl e false s hst)
  | .inl (.inl (.inl (.inl (.inr t)))), s, h => by
      have h' : (isKeygenAt e (s.game.stateAt true) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      cases t
      simp only [stopOnState_run]
      exact leak_keygen_on hMac irl e true s hst hc
  | .inl (.inl (.inl (.inr t))), s, h => by
      have h' : (isKeygenAt e (s.game.stateAt false) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hst⟩ := isKeygenAt_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      cases t
      simp only [stopOnState_run]
      exact leak_keygen_on hMac irl e false s hst hc
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))), _, h => by
      simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))), _, h => by simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inr _))))), _, h => by simp [sendHit] at h
  | .inl (.inl (.inr _)), _, h => by simp [sendHit] at h
  | .inl (.inr _), _, h => by simp [sendHit] at h
  | .inr _, _, h => by simp [sendHit] at h

/-- Off a hit, installing a first-stage sample changes no query. -/
theorem encaps1_off (e : ℕ) (kp : Option (P.PK × P.SK)) (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), sendHit (isEncaps1At e) e q s = false →
      ∀ c, 𝒟[((stopOnState (traceImplAt P hMac irl e kp (some c) xo m) (targetStop e) q).run).run
          s] =
        𝒟[((stopOnState (traceImplAt P hMac irl e kp none xo m) (targetStop e) q).run).run s]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, h, c => by
      cases t
      refine stopped_congr _ _ s ?_
      change 𝒟[(tracePlainAt P hMac irl e kp (some c) true ()).run s] =
        𝒟[(tracePlainAt P hMac irl e kp none true ()).run s]
      simp only [tracePlainAt, StateT.run_map, traceSendAt_ec_off hMac irl e kp c true false s h]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, h, c => by
      cases t
      refine stopped_congr _ _ s ?_
      change 𝒟[(tracePlainAt P hMac irl e kp (some c) false ()).run s] =
        𝒟[(tracePlainAt P hMac irl e kp none false ()).run s]
      simp only [tracePlainAt, StateT.run_map, traceSendAt_ec_off hMac irl e kp c false false s h]
  | .inl (.inl (.inl (.inl (.inr t)))), s, h, c => by
      cases t
      refine stopped_congr _ _ s ?_
      by_cases hk : isEncaps1At e (s.game.stateAt true) = true
      · obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
        have hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by
          simpa [sendHit, hk] using h
        exact leak_encaps1_refused hMac irl e kp true s hst hc c
      · change 𝒟[(traceSendAt P hMac irl e kp (some c) true true).run s] =
          𝒟[(traceSendAt P hMac irl e kp none true true).run s]
        rw [traceSendAt_ec_off hMac irl e kp c true true s (by simpa using hk)]
  | .inl (.inl (.inl (.inr t))), s, h, c => by
      cases t
      refine stopped_congr _ _ s ?_
      by_cases hk : isEncaps1At e (s.game.stateAt false) = true
      · obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
        have hc : (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by
          simpa [sendHit, hk] using h
        exact leak_encaps1_refused hMac irl e kp false s hst hc c
      · change 𝒟[(traceSendAt P hMac irl e kp (some c) false true).run s] =
          𝒟[(traceSendAt P hMac irl e kp none false true).run s]
        rw [traceSendAt_ec_off hMac irl e kp c false true s (by simpa using hk)]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl t)))))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr n)))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inl (.inl (.inl (.inr n))))), s, _, _ =>
      traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inl (.inr t)), s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inl (.inr t), s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial
  | .inr t, s, _, _ => traceImplAt_offSend hMac irl e _ _ _ _ xo m _ s trivial

/-- At a hit, the lazy first-stage encapsulation is the installed one with a sampled triple. -/
theorem encaps1_on (e : ℕ) (x : P.PK × P.SK) (ec' : Option (P.inc.St × P.inc.C₁ × P.K))
    (xo : Option P.EpochKey) (m : ℕ → Mode) :
    ∀ (q : (Spec P irl).Domain) (s : TraceState P), InstInv hMac e (some x) ec' s →
      sendHit (isEncaps1At e) e q s = true →
      𝒟[((stopOnState (traceImplAt P hMac irl e (some x) none xo m) (targetStop e) q).run).run
          s] =
        𝒟[P.inc.encaps1 (P.inc.toHeader x.1) >>= fun c =>
          ((stopOnState (traceImplAt P hMac irl e (some x) (some c) xo m) (targetStop e)
            q).run).run s]
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t)))))))), s, hs, h => by
      have h' : isEncaps1At e (s.game.stateAt true) = true := h
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true h'
      rw [← hs.header hMac hst]
      cases t
      exact stopped_bind _ _ _ s (plain_encaps1_on hMac irl e (some x) true s hst)
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr t))))))), s, hs, h => by
      have h' : isEncaps1At e (s.game.stateAt false) = true := h
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true h'
      rw [← hs.header hMac hst]
      cases t
      exact stopped_bind _ _ _ s (plain_encaps1_on hMac irl e (some x) false s hst)
  | .inl (.inl (.inl (.inl (.inr t)))), s, hs, h => by
      have h' : (isEncaps1At e (s.game.stateAt true) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      rw [← hs.header hMac hst]
      cases t
      simp only [stopOnState_run]
      exact leak_encaps1_on hMac irl e (some x) true s hst hc
  | .inl (.inl (.inl (.inr t))), s, hs, h => by
      have h' : (isEncaps1At e (s.game.stateAt false) &&
          !decide ({e} ∩ s.game.challenged ≠ ∅)) = true := h
      rw [Bool.and_eq_true] at h'
      obtain ⟨hk, hn⟩ := h'
      obtain ⟨a0, hdr, dec, hst⟩ := isEncaps1At_eq_true hk
      have hc : ¬ (true && decide ({e} ∩ s.game.challenged ≠ ∅)) = true := by simpa using hn
      rw [← hs.header hMac hst]
      cases t
      simp only [stopOnState_run]
      exact leak_encaps1_on hMac irl e (some x) false s hst hc
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))), _, _, h => by
      simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))), _, _, h => by simp [sendHit] at h
  | .inl (.inl (.inl (.inl (.inl (.inr _))))), _, _, h => by simp [sendHit] at h
  | .inl (.inl (.inr _)), _, _, h => by simp [sendHit] at h
  | .inl (.inr _), _, _, h => by simp [sendHit] at h
  | .inr _, _, _, h => by simp [sendHit] at h

/-- **Installing the key pair of `e`.** Sampling the key pair of `e` once before the stopped run
and installing it is the same as sampling it at the key generation of `e`. -/
theorem stoppedRun_installKeygen (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct) (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct) (e : ℕ) (xo : Option P.EpochKey) (m : ℕ → Mode)
    (A : Adversary P irl) (s : TraceState P) (hs : TraceInv hMac true s) :
    Pr[= true | P.kem.keygen >>= fun x =>
        stoppedRun (traceImplAt P hMac irl e (some x) none xo m) (targetStop e) A s] =
      Pr[= true | stoppedRun (traceImplAt P hMac irl e none none xo m) (targetStop e) A s] :=
  optionRun_install P.kem.keygen
    (fun x => stopOnState (traceImplAt P hMac irl e (some x) none xo m) (targetStop e))
    (stopOnState (traceImplAt P hMac irl e none none xo m) (targetStop e))
    (TraceInv hMac true) (fun s => (s.transcript e).keypair ≠ none) (sendHit (isKeygenAt e) e)
    (fun x hx q s hs z hz _ => by
      obtain ⟨w, hw, rfl⟩ := mem_support_stopOnState hz
      exact traceImplAt_traceInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e
        (some x) none xo m (fun y h => by cases h; exact hx) q s hs
        (fun _ _ _ _ _ h => by cases h) w hw)
    (fun x _ q s _ hu z hz _ => by
      obtain ⟨w, hw, rfl⟩ := mem_support_stopOnState hz
      exact (traceImplAt_transcriptStep hMac irl e (some x) none xo m q s w hw).keypair_ne hu)
    (fun q s hs hu => sendHit_false (fun p => isKeygenAt_false hMac hs hu p) q)
    (fun x _ q s _ hh z hz _ => by
      obtain ⟨w, hw, rfl⟩ := mem_support_stopOnState hz
      exact keygen_hit_records hMac irl e x xo m q s hh w hw)
    (fun q s _ hh x _ => keygen_off hMac irl e xo m q s hh x)
    (fun q s _ hh => keygen_on hMac irl e xo m q s hh)
    A s hs

/-- **Installing the first-stage sample of `e`.** With the key pair of `e` installed, sampling the
first-stage encapsulation of `e` once before the stopped run and installing it is the same as
sampling it at the first-stage encapsulation of `e`. -/
theorem stoppedRun_installEncaps1 (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct) (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct) (e : ℕ) (x : P.PK × P.SK)
    (hx : x ∈ support P.kem.keygen) (xo : Option P.EpochKey) (m : ℕ → Mode)
    (A : Adversary P irl) (s : TraceState P) (hs : InstInv hMac e (some x) none s) :
    Pr[= true | P.inc.encaps1 (P.inc.toHeader x.1) >>= fun c =>
        stoppedRun (traceImplAt P hMac irl e (some x) (some c) xo m) (targetStop e) A s] =
      Pr[= true | stoppedRun (traceImplAt P hMac irl e (some x) none xo m) (targetStop e) A s] :=
  optionRun_install (P.inc.encaps1 (P.inc.toHeader x.1))
    (fun c => stopOnState (traceImplAt P hMac irl e (some x) (some c) xo m) (targetStop e))
    (stopOnState (traceImplAt P hMac irl e (some x) none xo m) (targetStop e))
    (InstInv hMac e (some x) none) (fun s => (s.transcript e).encaps1 ≠ none)
    (sendHit (isEncaps1At e) e)
    (fun c hc q s hs z hz _ => by
      obtain ⟨w, hw, rfl⟩ := mem_support_stopOnState hz
      exact traceImplAt_instInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e x
        (some c) none xo m hx (fun c' h => by cases h; exact hc) (Or.inl rfl) q s hs w hw)
    (fun c _ q s _ hu z hz _ => by
      obtain ⟨w, hw, rfl⟩ := mem_support_stopOnState hz
      exact (traceImplAt_transcriptStep hMac irl e (some x) (some c) xo m q s w hw).encaps1_ne hu)
    (fun q s hs hu => sendHit_false (fun p => isEncaps1At_false hMac hs.1 hu p) q)
    (fun c _ q s _ hh z hz _ => by
      obtain ⟨w, hw, rfl⟩ := mem_support_stopOnState hz
      exact encaps1_hit_records hMac irl e (some x) c xo m q s hh w hw)
    (fun q s _ hh c _ => encaps1_off hMac irl e (some x) xo m q s hh c)
    (fun q s hs hh => encaps1_on hMac irl e x none xo m q s hs hh)
    A s hs

/-- **Installing both samples of `e`.** Sampling the key pair and the first-stage sample of `e`
once before the stopped run from the initial state is the same as sampling them at their sends. -/
theorem stoppedRun_installBoth (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct) (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct) (e : ℕ) (xo : Option P.EpochKey) (m : ℕ → Mode)
    (A : Adversary P irl) :
    Pr[= true | P.kem.keygen >>= fun x => P.inc.encaps1 (P.inc.toHeader x.1) >>= fun c =>
        stoppedRun (traceImplAt P hMac irl e (some x) (some c) xo m) (targetStop e) A
          (initTrace P hMac)] =
      Pr[= true | stoppedRun (traceImplAt P hMac irl e none none xo m) (targetStop e) A
        (initTrace P hMac)] :=
  (probOutput_bind_congr fun x hx =>
    stoppedRun_installEncaps1 hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e x hx xo
      m A (initTrace P hMac)
      ⟨traceInv_init hMac true, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩).trans
    (stoppedRun_installKeygen hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e xo m A
      (initTrace P hMac) (traceInv_init hMac true))

end Dispatch

/-! ### Sends of the simulator -/

section SendSteps

variable (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) [DecidableEq P.EpochKey]

/-- The key-generation send of `e` agrees. -/
theorem sendStep_keygen (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (sk : P.SK)
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party leaking : Bool) (s : TraceState P)
    {a : Unit} (hst : s.game.stateAt party = .keysUnsampled e a) :
    𝒟[(simSend P hMac irl e ch party leaking).run (simOf e v s)] =
      𝒟[Prod.map id (simOf e v) <$>
        (traceSendAt P hMac irl e (some (ch.pk, sk)) ec party leaking).run s] := by
  rw [traceSendAt_keygen_run hMac irl leaking hst (ch.pk, sk) ec]
  have hS : (simOf e v s).game.stateAt party = .inl (.keysUnsampled e a) := by
    rw [simOf_game, simGameOf_stateAt, hst]
    rfl
  change 𝒟[simSend P hMac irl e ch party leaking (simOf e v s)] = _
  simp only [simSend, hS, targetSend, ↓reduceIte]
  by_cases hc : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
  · have hc' : (leaking && decide ({e} ∩ (simOf e v s).game.challenged ≠ ∅)) = true := hc
    rw [if_pos hc', if_pos hc, map_pure]
    rfl
  · have hc' : ¬ (leaking && decide ({e} ∩ (simOf e v s).game.challenged ≠ ∅)) = true := hc
    rw [if_neg hc', if_neg hc, map_pure]
    congr 2
    simp only [Prod.map, id, simOf, simGameOf_sendUpdate, keygenState, keygenStep_eq,
      eraseAt_update_self, relabelKey, Option.map_none, maskState, ↓reduceIte, simGameOf_exposed]

/-- The first-stage encapsulation send of `e` agrees. -/
theorem sendStep_encaps1 (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v)
    (kp : Option (P.PK × P.SK)) (es : P.inc.St) (k : P.K) (party leaking : Bool)
    (s : TraceState P) {a : Unit} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a hdr dec) :
    𝒟[(simSend P hMac irl e ch party leaking).run (simOf e v s)] =
      𝒟[Prod.map id (simOf e v) <$>
        (traceSendAt P hMac irl e kp (some (es, ch.ct1, k)) party leaking).run s] := by
  rw [traceSendAt_encaps1_run hMac irl leaking hst kp (es, ch.ct1, k)]
  have hS : (simOf e v s).game.stateAt party = .inl (.headerReceived e a hdr dec) := by
    rw [simOf_game, simGameOf_stateAt, hst]
    rfl
  change 𝒟[simSend P hMac irl e ch party leaking (simOf e v s)] = _
  simp only [simSend, hS, targetSend, ↓reduceIte, hv]
  by_cases hc : (leaking && decide ({e} ∩ s.game.challenged ≠ ∅)) = true
  · have hc' : (leaking && decide ({e} ∩ (simOf e v s).game.challenged ≠ ∅)) = true := hc
    rw [if_pos hc', if_pos hc, map_pure]
    rfl
  · have hc' : ¬ (leaking && decide ({e} ∩ (simOf e v s).game.challenged ≠ ∅)) = true := hc
    rw [if_neg hc', if_neg hc, map_pure]
    congr 2
    simp only [Prod.map, id, simOf, simGameOf_sendUpdate, encaps1State, encaps1Step_eq,
      eraseAt_update_self, relabelKey, Option.map_some, maskState, ↓reduceIte, simGameOf_exposed]

/-- A send of an ordinary state that samples nothing installed agrees. -/
theorem sendStep_ghost (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (kp : Option (P.PK × P.SK))
    (ec : Option (P.inc.St × P.inc.C₁ × P.K)) (party leaking : Bool) (s : TraceState P)
    (hm : maskState e (s.game.stateAt party) = .inl (s.game.stateAt party))
    (hT : targetSend P hMac e ch (P.kdfOK ch.key e) (s.game.stateAt party) = none) :
    𝒟[(simSend P hMac irl e ch party leaking).run (simOf e v s)] =
      𝒟[Prod.map id (simOf e v) <$> (traceSendAt P hMac irl e kp ec party leaking).run s] := by
  have h1 : ∀ a, s.game.stateAt party ≠ .keysUnsampled e a := fun a h => by
    rw [h] at hT
    simp [targetSend] at hT
  have h2 : ∀ a hdr dec, s.game.stateAt party ≠ .headerReceived e a hdr dec :=
    fun a hdr dec h => by
      rw [h] at hT
      simp [targetSend] at hT
  have hI := installedSample_eq_none hMac e kp ec s party h1 h2
  have hTr : (traceSendAt P hMac irl e kp ec party leaking).run s =
      traceSend P hMac irl party leaking s := by
    change traceSendAt P hMac irl e kp ec party leaking s = _
    simp only [traceSendAt, hI]
  have hS : (simGameOf e v s.game).stateAt party = .inl (s.game.stateAt party) := by
    rw [simGameOf_stateAt, hm]
  rw [hTr]
  change 𝒟[simSend P hMac irl e ch party leaking (simOf e v s)] = _
  simp only [simSend, simOf_game, hS, hT, simOf_transcript,
    ghostSample_eq hMac irl e s party h1 h2, traceSend, Functor.map_map]
  apply evalDist_map_congr_support
  intro w hw
  have hedge : SendEdge (auth P hMac) (s.game.stateAt party) w.1.1 := by
    refine (mem_support_send_iff (auth P hMac)).mp ?_
    have h1' : w.1 ∈ support
        (MLKEMBraid.sendRleak P irl (auth P hMac) (s.game.stateAt party)) := by
      rw [← sampledSend_erase P hMac irl s party, support_map]
      exact ⟨w, hw, rfl⟩
    rw [send_eq_map_sendRleak P irl, support_map]
    exact ⟨w.1, h1', rfl⟩
  obtain ⟨hmw, hkw⟩ := ghost_succ hMac (v := v) hedge hm hT
  simp only [apply_ite (Prod.map id (simOf e v))]
  refine if_congr Iff.rfl rfl ?_
  simp only [Prod.map, id, simOf, simGameOf_sendUpdate, hmw, hkw, simGameOf_exposed]

/-- Every send agrees, with the challenge key pair and first-stage sample installed. -/
theorem sendStep (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v)
    (sk : P.SK) (es : P.inc.St) (k : P.K) (party leaking : Bool) (s : TraceState P) :
    𝒟[(simSend P hMac irl e ch party leaking).run (simOf e v s)] =
      𝒟[Prod.map id (simOf e v) <$>
        (traceSendAt P hMac irl e (some (ch.pk, sk)) (some (es, ch.ct1, k)) party leaking).run
          s] := by
  rcases hm : maskState e (s.game.stateAt party) with st' | m
  · obtain rfl := maskState_eq_inl hm
    cases hT : targetSend P hMac e ch (P.kdfOK ch.key e) (s.game.stateAt party) with
    | none => exact sendStep_ghost hMac irl e v ch _ _ party leaking s hm hT
    | some x =>
        cases hst : s.game.stateAt party with
        | keysUnsampled t a =>
            by_cases ht : t = e
            · subst ht
              exact sendStep_keygen hMac irl t v ch sk _ party leaking s hst
            · rw [hst] at hT
              simp [targetSend, ht] at hT
        | headerReceived t a hdr dec =>
            by_cases ht : t = e
            · subst ht
              exact sendStep_encaps1 hMac irl t v ch hv _ es k party leaking s hst
            · rw [hst] at hT
              simp [targetSend, ht] at hT
        | _ =>
            rw [hst] at hT
            simp [targetSend] at hT
  · exact sendStep_masked hMac irl e v ch _ _ party leaking s hm

/-- The ordinary send query agrees. -/
theorem plainStep (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v)
    (sk : P.SK) (es : P.inc.St) (k : P.K) (party : Bool) (t : Unit) (s : TraceState P) :
    StepSim e v ((simPlain P hMac irl e ch party t).run (simOf e v s))
      ((tracePlainAt P hMac irl e (some (ch.pk, sk)) (some (es, ch.ct1, k)) party t).run s) :=
  StepSim.of_eq (by
    simp only [simPlain, tracePlainAt, StateT.run_map]
    exact exact_mapAnswer _ (sendStep hMac irl e v ch hv sk es k party false s))

/-- The leaking send query agrees. -/
theorem leakStep (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v)
    (sk : P.SK) (es : P.inc.St) (k : P.K) (party : Bool) (t : Unit) (s : TraceState P) :
    StepSim e v ((simLeak P hMac irl e ch party t).run (simOf e v s))
      ((traceLeakAt P hMac irl e (some (ch.pk, sk)) (some (es, ch.ct1, k)) party t).run s) :=
  StepSim.of_eq (sendStep hMac irl e v ch hv sk es k party true s)

end SendSteps

section ReceiveStep

variable [DecidableEq P.EpochKey] [DecidableEq P.Sym] (hMac : P.Mac = Unit)
  (irl : P.kem.IncrementalRandLeak P.inc)

/-- An accepted trace receive. -/
theorem traceReceive_accept (party : Bool) (n : ℕ) (s : TraceState P) {msg : Message P.Sym}
    {tsnd : ℕ} {key? : Option (ℕ × P.EpochKey)} {trcv : ℕ} {st' : State P Unit}
    (hm : s.game.messagesAt (!party) n = some (msg, tsnd))
    (hr : repairedRecv P hMac true s.transcript (s.game.stateAt party) msg =
      some (key?, trcv, st')) :
    (traceReceive P hMac irl true party n).run s =
      pure (some (trcv, key?.map Prod.fst),
        { s with game := recvUpdate s.game party tsnd ⟨trcv, key?, st'⟩ trcv }) := by
  rw [traceReceive_run, liftGame_run]
  cases party
  · have hm' : s.game.msgA n = some (msg, tsnd) := hm
    rw [if_neg Bool.false_ne_true, SCKAScheme.oracleRecvB_run_eq_of_accept
      (recvScheme P hMac irl true s.transcript) s.game hm' hr, map_pure]
    rfl
  · have hm' : s.game.msgB n = some (msg, tsnd) := hm
    rw [if_pos rfl, SCKAScheme.oracleRecvA_run_eq_of_accept
      (recvScheme P hMac irl true s.transcript) s.game hm' hr, map_pure]
    rfl

/-- A trace receive of a missing message. -/
theorem traceReceive_missing (party : Bool) (n : ℕ) (s : TraceState P)
    (hm : s.game.messagesAt (!party) n = none) :
    (traceReceive P hMac irl true party n).run s = pure (none, s) := by
  rw [traceReceive_run, liftGame_run]
  cases party
  · have hm' : s.game.msgA n = none := hm
    rw [if_neg Bool.false_ne_true, SCKAScheme.oracleRecvB_run_eq_of_none _ _ hm', map_pure]
  · have hm' : s.game.msgB n = none := hm
    rw [if_pos rfl, SCKAScheme.oracleRecvA_run_eq_of_none _ _ hm', map_pure]

/-- A receive query agrees under the repaired invariant. -/
theorem recvStep (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v) (party : Bool)
    (n : ℕ) (s : TraceState P) (h : RepairInv hMac s.transcript s.game)
    (hc2 : ∀ pk sk es c1 k, (s.transcript e).keypair = some (pk, sk) →
      (s.transcript e).encaps1 = some (es, c1, k) →
      ch.ct2 = P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk)) :
    StepSim e v ((simReceive P hMac e ch party n).run (simOf e v s))
      ((traceReceive P hMac irl true party n).run s) := by
  apply StepSim.of_eq
  have hmsg : (if party then (simOf e v s).game.msgB else (simOf e v s).game.msgA) n =
      s.game.messagesAt (!party) n := by
    cases party <;> rfl
  change 𝒟[simReceive P hMac e ch party n (simOf e v s)] = _
  simp only [simReceive, hmsg]
  cases hm : s.game.messagesAt (!party) n with
  | none =>
      rw [traceReceive_missing hMac irl party n s hm, map_pure]
      rfl
  | some entry =>
      obtain ⟨msg, tsnd⟩ := entry
      obtain ⟨key?, st', -, htrue, hinv⟩ := recv_outcome hHdrCorrect hEkCorrect hCt1Correct
        hCt2Correct irl h party hm true (fun h => absurd h (by decide))
      have hloc' : LocalPayloadInv (auth P hMac) () s.transcript st' := by
        simpa using hinv.local party
      have hS := simRecv_eq hMac ch hv (h.local party) hc2 htrue hloc'
      rw [traceReceive_accept hMac irl party n s hm htrue, map_pure]
      simp only [simOf_transcript, simOf_game, simGameOf_stateAt, hS]
      congr 2
      simp only [Prod.map, id, relabelKey_map_fst, simOf, simGameOf_recvUpdate]

end ReceiveStep

/-! ### The simulation step -/

/-- The invariant of the repaired trace game with the key pair `(pk, sk)` and the first-stage
sample `(es, c1, k)` installed at `e`. -/
def SimInv (hMac : P.Mac = Unit) (e : ℕ) (pk : P.PK) (sk : P.SK) (es : P.inc.St) (c1 : P.inc.C₁)
    (k : P.K) (s : TraceState P) : Prop :=
  InstInv hMac e (some (pk, sk)) (some (es, c1, k)) s

section SimInvLemmas

variable {hMac : P.Mac = Unit} {e : ℕ} {pk : P.PK} {sk : P.SK} {es : P.inc.St} {c1 : P.inc.C₁}
  {k : P.K} {s : TraceState P}

/-- The repaired invariant of `SimInv`. -/
theorem SimInv.repair (h : SimInv hMac e pk sk es c1 k s) : RepairInv hMac s.transcript s.game :=
  (h.1.1 (Or.inl rfl)).1

/-- Under `SimInv`, the second ciphertext part of the recorded samples of `e` is `c2`. -/
theorem SimInv.ct2 (h : SimInv hMac e pk sk es c1 k s) {c2 : P.inc.C₂}
    (hc2 : c2 = P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk)) :
    ∀ pk' sk' es' c1' k', (s.transcript e).keypair = some (pk', sk') →
      (s.transcript e).encaps1 = some (es', c1', k') →
      c2 = P.hEnc2.encaps2Det es' (P.inc.toHeader pk') (P.inc.toVector pk') := by
  intro pk' sk' es' c1' k' hkp hec
  rcases h.2.1 (pk, sk) rfl with h1 | h1
  · rw [h1] at hkp
    cases hkp
  rcases h.2.2 (es, c1, k) rfl with h2 | h2
  · rw [h2] at hec
    cases hec
  rw [h1] at hkp
  rw [h2] at hec
  obtain ⟨rfl, rfl⟩ : pk = pk' ∧ sk = sk' := by simpa using hkp
  obtain ⟨rfl, rfl, rfl⟩ : es = es' ∧ c1 = c1' ∧ k = k' := by simpa using hec
  exact hc2

/-- Under `SimInv`, a recorded key of `e` is the derived key of the installed sample. -/
theorem SimInv.key (h : SimInv hMac e pk sk es c1 k s) :
    ∀ kk, lookupKey s.game e = some kk → kk = P.kdfOK k e := by
  intro kk hk
  have hR := h.repair
  have hk2 : ∀ party : Bool, (if party then s.game.keyA else s.game.keyB) e = some kk →
      kk = P.kdfOK k e := by
    intro party hp
    rw [hR.keys party e] at hp
    by_cases hc : 0 < e ∧ e ≤ (if party then s.game.stA else s.game.stB).completedEpoch
    · rw [if_pos hc] at hp
      rcases h.2.2 (es, c1, k) rfl with h2 | h2
      · rw [h2] at hp
        cases hp
      · rw [h2] at hp
        simpa using hp.symm
    · rw [if_neg hc] at hp
      cases hp
  have hk' : s.game.keyA e = some kk ∨ s.game.keyB e = some kk := by
    unfold lookupKey at hk
    cases hA : s.game.keyA e <;> simp_all
  rcases hk' with hp | hp
  · exact hk2 true (by simpa using hp)
  · exact hk2 false (by simpa using hp)

end SimInvLemmas

/-- The simulator view of the literal initial trace state is the simulator's initial state. -/
theorem simOf_initTrace (hMac : P.Mac = Unit) (e : ℕ) (v : P.EpochKey) :
    simOf e v (initTrace P hMac) = simInit P hMac := by
  have h1 : (relabel e v fun _ => (none : Option P.EpochKey)) = fun _ => none :=
    funext fun t => by simp [relabel]
  have h2 : (eraseAt e fun _ => ({ keypair := none, encaps1 := none } : EpochTranscript P)) =
      fun _ => { keypair := none, encaps1 := none } :=
    funext fun t => by simp [eraseAt]
  simp [simOf, simGameOf, initTrace, simInit, SCKAScheme.initGameState, maskState,
    MLKEMBraid.initA, MLKEMBraid.initB, h1, h2]

section SimStep

variable [SampleableType P.K] [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
  [DecidableEq P.Sym] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- Every query of the simulator agrees with the installed trace game under `SimInv`. -/
theorem simImpl_step (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v) (sk : P.SK)
    (es : P.inc.St) (k : P.K)
    (hc2 : ch.ct2 = P.hEnc2.encaps2Det es (P.inc.toHeader ch.pk) (P.inc.toVector ch.pk))
    (xo : Option P.EpochKey) (hxo : ∀ x, xo = some x → x = v)
    (hxk : xo = none → v = P.kdfOK k e) :
    ∀ q s, SimInv hMac e ch.pk sk es ch.ct1 k s →
      StepSim e v ((simImpl P hMac irl e ch q).run (simOf e v s))
        ((traceImplAt P hMac irl e (some (ch.pk, sk)) (some (es, ch.ct1, k)) xo
          (fun t => if t < e then .uniform else .real) q).run s) :=
  stepSim_add _ (stepSim_add _ (stepSim_add _ (stepSim_add _ (stepSim_add _
    (stepSim_add _ (stepSim_add _ (stepSim_add _ (stepSim_add _
      (fun t s _ => unif_step t s)
      (fun t s _ => plainStep hMac irl e v ch hv sk es k true t s))
      (fun t s _ => plainStep hMac irl e v ch hv sk es k false t s))
      (fun n s hs => recvStep hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e v ch hv
        true n s hs.repair (hs.ct2 hc2)))
      (fun n s hs => recvStep hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e v ch hv
        false n s hs.repair (hs.ct2 hc2)))
      (fun t s _ => leakStep hMac irl e v ch hv sk es k true t s))
      (fun t s _ => leakStep hMac irl e v ch hv sk es k false t s))
      (fun t s hs => challenge_step xo t s hxo
        (fun hn kk hk => (hs.key kk hk).trans (hxk hn).symm)))
      (fun t s _ => by cases t; exact corruptA_step s))
      (fun t s _ => by cases t; exact corruptB_step s)

/-- **Simulation.** With the challenge key pair and first-stage sample installed at `e`, the
masked simulator and the installed trace game accept with the same probability. -/
theorem simStep_eq (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (e : ℕ) (v : P.EpochKey) (ch : Challenge P) (hv : P.kdfOK ch.key e = v) (sk : P.SK)
    (es : P.inc.St) (k : P.K)
    (hc2 : ch.ct2 = P.hEnc2.encaps2Det es (P.inc.toHeader ch.pk) (P.inc.toVector ch.pk))
    (xo : Option P.EpochKey) (hxo : ∀ x, xo = some x → x = v)
    (hxk : xo = none → v = P.kdfOK k e)
    (hkp : (ch.pk, sk) ∈ support P.kem.keygen)
    (hec : (es, ch.ct1, k) ∈ support (P.inc.encaps1 (P.inc.toHeader ch.pk)))
    (A : Adversary P irl) :
    Pr[= true | stoppedRun (simImpl P hMac irl e ch) (simStop e) A (simInit P hMac)] =
      Pr[= true | stoppedRun (traceImplAt P hMac irl e (some (ch.pk, sk))
        (some (es, ch.ct1, k)) xo (fun t => if t < e then .uniform else .real)) (targetStop e) A
        (initTrace P hMac)] := by
  rw [← simOf_initTrace hMac e v]
  exact probOutput_optionRun_eq_of_state_map
    (stopOnState (traceImplAt P hMac irl e (some (ch.pk, sk)) (some (es, ch.ct1, k)) xo
      (fun t => if t < e then .uniform else .real)) (targetStop e))
    (stopOnState (simImpl P hMac irl e ch) (simStop e)) (simOf e v)
    (SimInv hMac e ch.pk sk es ch.ct1 k)
    (fun q s hs z hz _ => by
      obtain ⟨w, hw, rfl⟩ := mem_support_stopOnState hz
      exact traceImplAt_instInv hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e
        (ch.pk, sk) (some (es, ch.ct1, k)) (some (es, ch.ct1, k)) xo _ hkp
        (fun c h => by cases h; exact hec) (Or.inr rfl) q s hs w hw)
    (fun q s hs => stopOnState_simOf _ _ q s
      (simImpl_step hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct e v ch hv sk es k
        hc2 xo hxo hxk q s hs))
    A (initTrace P hMac)
    ⟨traceInv_init hMac true, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩

end SimStep

/-! ### The IND-CPA experiments of the KEM reduction -/

section KEMGap

variable [SampleableType P.K] [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
  [DecidableEq P.Sym] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

omit [DecidableEq P.EpochKey] in
/-- The fixed-bit IND-CPA experiment of `kemReduction`, with the challenge ciphertext split into
the first-stage sample and its deterministic second part. -/
theorem indCPAExpProb_kemReduction (A : Adversary P irl) (n : ℕ) (b : Bool) :
    Pr[= true | KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) b] =
      Pr[= true | P.kem.keygen >>= fun x => P.inc.encaps1 (P.inc.toHeader x.1) >>= fun c =>
        ($ᵗ P.K) >>= fun u => stoppedRun (simImpl P hMac irl (n + 1)
          ⟨x.1, c.2.1, P.hEnc2.encaps2Det c.1 (P.inc.toHeader x.1) (P.inc.toVector x.1),
            if b then c.2.2 else u⟩) (simStop (n + 1)) A (simInit P hMac)] := by
  have h : KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) b =
      P.kem.keygen >>= fun x => P.kem.encaps x.1 >>= fun ck => ($ᵗ P.K) >>= fun u =>
        stoppedRun (simImpl P hMac irl (n + 1) ⟨x.1, (P.inc.splitC ck.1).1,
          (P.inc.splitC ck.1).2, if b then ck.2 else u⟩) (simStop (n + 1)) A (simInit P hMac) := by
    simp only [KEMScheme.indCPAExpProb, KEMScheme.indCPAPrefix, bind_assoc]
    refine bind_congr fun x => ?_
    obtain ⟨pk, sk⟩ := x
    simp only [kemReduction, pure_bind]
  rw [h]
  refine probOutput_bind_congr fun x _ => ?_
  rw [encaps_eq_map x.1, bind_map_left]
  simp only [Equiv.apply_symm_apply]

/-- **The real-key experiment** of `kemReduction` is the stopped repaired game with real keys
from `e` on. -/
theorem kem_real_side (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct) (n : ℕ)
    (A : Adversary P irl) :
    Pr[= true | KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) true] =
      Pr[= true | stoppedRun (traceImplAt P hMac irl (n + 1) none none none
        (fun t => if t < n + 1 then .uniform else .real)) (targetStop (n + 1)) A
        (initTrace P hMac)] := by
  rw [indCPAExpProb_kemReduction hMac irl A n true,
    ← stoppedRun_installBoth hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct (n + 1) none
      _ A]
  refine probOutput_bind_congr fun x hx => probOutput_bind_congr fun c hc => ?_
  obtain ⟨pk, sk⟩ := x
  obtain ⟨es, c1, k⟩ := c
  simp only [↓reduceIte]
  rw [probOutput_bind_const']
  exact simStep_eq hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct (n + 1)
    (P.kdfOK k (n + 1)) ⟨pk, c1, _, k⟩ rfl sk es k rfl none (fun _ h => by cases h)
    (fun _ => rfl) hx hc A

/-- **The random-key experiment** of `kemReduction` is the stopped repaired game with a derived
uniform key installed at `e`. -/
theorem kem_rand_side (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct) (n : ℕ)
    (A : Adversary P irl) :
    Pr[= true | KEMScheme.indCPAExpProb P.kem (kemReduction P hMac irl A (n + 1)) false] =
      Pr[= true | ($ᵗ P.K) >>= fun u => stoppedRun (traceImplAt P hMac irl (n + 1) none none
        (some (P.kdfOK u (n + 1))) (fun t => if t < n + 1 then .uniform else .real))
        (targetStop (n + 1)) A (initTrace P hMac)] := by
  rw [indCPAExpProb_kemReduction hMac irl A n false]
  have h1 : ∀ x ∈ support P.kem.keygen, ∀ c ∈ support (P.inc.encaps1 (P.inc.toHeader x.1)),
      ∀ u : P.K,
      Pr[= true | stoppedRun (simImpl P hMac irl (n + 1)
          ⟨x.1, c.2.1, P.hEnc2.encaps2Det c.1 (P.inc.toHeader x.1) (P.inc.toVector x.1),
            if false then c.2.2 else u⟩) (simStop (n + 1)) A (simInit P hMac)] =
        Pr[= true | stoppedRun (traceImplAt P hMac irl (n + 1) (some x) (some c)
          (some (P.kdfOK u (n + 1))) (fun t => if t < n + 1 then .uniform else .real))
          (targetStop (n + 1)) A (initTrace P hMac)] := by
    intro x hx c hc u
    obtain ⟨pk, sk⟩ := x
    obtain ⟨es, c1, k⟩ := c
    exact simStep_eq hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct (n + 1)
      (P.kdfOK u (n + 1)) ⟨pk, c1, _, u⟩ rfl sk es k rfl (some (P.kdfOK u (n + 1)))
      (fun _ h => (Option.some.inj h).symm) (fun h => by cases h) hx hc A
  calc _ = Pr[= true | P.kem.keygen >>= fun x => P.inc.encaps1 (P.inc.toHeader x.1) >>= fun c =>
          ($ᵗ P.K) >>= fun u => stoppedRun (traceImplAt P hMac irl (n + 1) (some x) (some c)
            (some (P.kdfOK u (n + 1))) (fun t => if t < n + 1 then .uniform else .real))
            (targetStop (n + 1)) A (initTrace P hMac)] :=
        probOutput_bind_congr fun x hx => probOutput_bind_congr fun c hc =>
          probOutput_bind_congr fun u _ => h1 x hx c hc u
    _ = _ := (probOutput_swap3 _ _ _ _ _).trans
        (probOutput_bind_congr fun _ _ => stoppedRun_installBoth hMac irl hHdrCorrect hEkCorrect
          hCt1Correct hCt2Correct (n + 1) _ _ A)

end KEMGap

/-- **`kem_gap_eq`**: for a positive epoch `e`, the gap between the hybrid with uniform keys
before `e` and the hybrid with a derived uniform key at `e` is the IND-CPA advantage of
`kemReduction` at `e`. -/
theorem kem_gap_eq (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (e : ℕ) (he : 0 < e) :
    (hybrid P hMac irl A (e - 1)).boolDistAdvantage (rawHybrid P hMac irl A e) =
      P.kem.IND_CPA_Advantage ProbCompRuntime.probComp (kemReduction P hMac irl A e) := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  have hHD : (fun t => if t ≤ n + 1 - 1 then Mode.uniform else Mode.real) =
      fun t => if t < n + 1 then Mode.uniform else Mode.real := by
    funext t
    by_cases h : t < n + 1
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hHJ : ∀ t, t ≠ n + 1 →
      (if t ≤ n + 1 - 1 then Mode.uniform else Mode.real) =
        (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform
          else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h, if_neg ht]
  have hJD : ∀ t, t ≠ n + 1 →
      (if t < n + 1 then Mode.uniform else if t = n + 1 then Mode.derivedUniform
        else Mode.real) = (if t < n + 1 then Mode.uniform else Mode.real) := by
    intro t ht
    by_cases h : t < n + 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg ht, if_neg h]
  have hgap := signedGap_stop hMac irl
    (fun t => if t ≤ n + 1 - 1 then .uniform else .real)
    (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real)
    (n + 1) hHJ A
  have hH : Pr[= true | stoppedRun (traceImpl P hMac irl true
        (fun t => if t ≤ n + 1 - 1 then .uniform else .real)) (targetStop (n + 1)) A
        (initTrace P hMac)] =
      Pr[= true | P.kem.IND_CPA_Exp ProbCompRuntime.probComp (kemReduction P hMac irl A (n + 1))
        true] := by
    rw [← KEMScheme.indCPAExpProb_probOutput_true_eq,
      kem_real_side hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct n A,
      ← traceImplAt_none hMac irl (n + 1), hHD]
  have hJ : Pr[= true | stoppedRun (traceImpl P hMac irl true
        (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real))
        (targetStop (n + 1)) A (initTrace P hMac)] =
      Pr[= true | P.kem.IND_CPA_Exp ProbCompRuntime.probComp (kemReduction P hMac irl A (n + 1))
        false] := by
    rw [← KEMScheme.indCPAExpProb_probOutput_true_eq,
      kem_rand_side hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct n A,
      ← traceImplAt_none hMac irl (n + 1),
      ← stoppedRun_chalSample hMac irl (n + 1) none none
        (fun t => if t < n + 1 then .uniform else if t = n + 1 then .derivedUniform else .real)
        ((fun u => P.kdfOK u (n + 1)) <$> ($ᵗ P.K)) (fun k => by simp [challengeValue]),
      bind_map_left]
    simp only [traceImplAt_congr hMac irl (n + 1) none none _ _ _ hJD]
  unfold ProbComp.boolDistAdvantage hybrid rawHybrid
  rw [hgap, hH, hJ, KEMScheme.IND_CPA_Advantage_eq_fixed_branch_dist]

end MLKEMBraid.NoAuth
