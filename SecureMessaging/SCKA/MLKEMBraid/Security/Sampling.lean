/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Games
import SecureMessaging.SCKA.MLKEMBraid.Correctness.SendPayload
import SecureMessaging.SCKA.Correctness
import SecureMessaging.SCKA.Security

/-!
# Joint sampling and elementary trace transitions

The normalization equations retain send results, leaked coins, transcript updates and bad
flags together. Invariant, installed-game and simulator proofs share these equations without
importing analytical risk bounds.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

/-- `liftGame` runs a game oracle on the `game` field. -/
theorem liftGame_run {α : Type} (c : StateT (MLKEMBraid.GameState P Unit) ProbComp α)
    (s : TraceState P) :
    (liftGame c).run s = (fun z => (z.1, { s with game := z.2 })) <$> c.run s.game := rfl

/-- Projecting a lifted game oracle to its game state gives the game oracle. -/
theorem map_game_liftGame {α : Type} (c : StateT (MLKEMBraid.GameState P Unit) ProbComp α)
    (s : TraceState P) :
    Prod.map id TraceState.game <$> (liftGame c).run s = c.run s.game := by
  rw [liftGame_run, Functor.map_map]
  exact id_map (c.run s.game)

/-- Outcomes of a lifted game oracle keep the ghost records and bad flag. -/
theorem mem_support_liftGame {α : Type} {c : StateT (MLKEMBraid.GameState P Unit) ProbComp α}
    {s : TraceState P} {z : α × TraceState P} (hz : z ∈ support ((liftGame c).run s)) :
    ∃ w ∈ support (c.run s.game), z = (w.1, { s with game := w.2 }) := by
  rw [liftGame_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

/-- A corruption of A reveals A's state, or is refused without a state change. -/
theorem mem_support_oracleCorruptA {V : State P Unit → Finset ℕ}
    {g : MLKEMBraid.GameState P Unit} {w : Option (State P Unit) × MLKEMBraid.GameState P Unit}
    (hw : w ∈ support ((SCKAScheme.oracleCorruptA V (State P Unit) P.EpochKey
      (Message P.Sym) ()).run g)) :
    w.2 = g ∨ (V g.stA ∩ g.challenged = ∅ ∧ w.2 = { g with exposed := g.exposed ∪ V g.stA }) := by
  rw [SCKAScheme.oracleCorruptA_run] at hw
  split_ifs at hw with hc
  · left
    rw [mem_support_pure_iff] at hw
    rw [hw]
  · right
    rw [mem_support_pure_iff] at hw
    exact ⟨not_not.mp hc, by rw [hw]⟩

/-- The version of `mem_support_oracleCorruptA` for B. -/
theorem mem_support_oracleCorruptB {V : State P Unit → Finset ℕ}
    {g : MLKEMBraid.GameState P Unit} {w : Option (State P Unit) × MLKEMBraid.GameState P Unit}
    (hw : w ∈ support ((SCKAScheme.oracleCorruptB V (State P Unit) P.EpochKey
      (Message P.Sym) ()).run g)) :
    w.2 = g ∨ (V g.stB ∩ g.challenged = ∅ ∧ w.2 = { g with exposed := g.exposed ∪ V g.stB }) := by
  rw [SCKAScheme.oracleCorruptB_run] at hw
  split_ifs at hw with hc
  · left
    rw [mem_support_pure_iff] at hw
    rw [hw]
  · right
    rw [mem_support_pure_iff] at hw
    exact ⟨not_not.mp hc, by rw [hw]⟩

/-- A challenge leaves the state unchanged, or adds an unexposed epoch to the challenged set. -/
theorem mem_support_traceChallenge [SampleableType P.K] [SampleableType P.EpochKey]
    {mode : ℕ → Mode} {e : ℕ} {s : TraceState P} {z : Option P.EpochKey × TraceState P}
    (hz : z ∈ support ((traceChallenge P mode e).run s)) :
    z.2 = s ∨ (e ∉ s.game.exposed ∧
      z.2 = { s with game := { s.game with challenged := insert e s.game.challenged } }) := by
  change z ∈ support (traceChallenge P mode e s) at hz
  simp only [traceChallenge] at hz
  split_ifs at hz with hex
  · left
    rw [mem_support_pure_iff] at hz
    rw [hz]
  · cases hk : lookupKey s.game e with
    | none =>
        simp only [hk, mem_support_pure_iff] at hz
        left
        rw [hz]
    | some k =>
        simp only [hk, support_map] at hz
        obtain ⟨out, -, rfl⟩ := hz
        exact Or.inr ⟨fun h => hex (Or.inl h), rfl⟩

/-- The send predicate in the nesting of `traceImpl`'s components. -/
def sendElim (P : Parameters ProbComp) (irl : P.kem.IncrementalRandLeak P.inc) :
    (Spec P irl).Domain → Bool :=
  Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim
    (fun _ => false) (fun _ => true)) (fun _ => true)) (fun _ => false)) (fun _ => false))
    (fun _ => true)) (fun _ => true)) (fun _ => false)) (fun _ => false)) (fun _ => false)

/-- `isSendQuery` selects the four send components of `traceImpl`. -/
theorem isSendQuery_eq_sendElim (irl : P.kem.IncrementalRandLeak P.inc) :
    ∀ t : (Spec P irl).Domain, isSendQuery t = sendElim P irl t
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))) => rfl
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))))) => rfl
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _))))))) => rfl
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))) => rfl
  | .inl (.inl (.inl (.inl (.inl (.inr _))))) => rfl
  | .inl (.inl (.inl (.inl (.inr _)))) => rfl
  | .inl (.inl (.inl (.inr _))) => rfl
  | .inl (.inl (.inr _)) => rfl
  | .inl (.inr _) => rfl
  | .inr _ => rfl

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
    (hdr : P.inc.PKheader) (dec : DecoderState P.inc.PKvector P.Sym) (es : P.inc.St)
    (ct1 : P.inc.C₁) (k : P.K) : SendResult P Unit :=
  let (chunk, enc) := (EncoderState.init P.ecpCt1 ct1).nextChunk
  { msg := { epoch := t, type := .ct1, data := some chunk }
    sendingEpoch := t - 1, outputKey := some (t, P.kdfOK k t)
    state := .ct1Sampled t ((auth P hMac).update a t (P.kdfOK k t)) hdr es ct1 enc dec }

/-- The bad flag after a first-stage encapsulation sample `c` of epoch `t`. -/
def encaps1Bad [DecidableEq P.EpochKey] (s : TraceState P) (t : ℕ)
    (c : P.inc.St × P.inc.C₁ × P.K) : Bool :=
  match (s.transcript t).keypair with
  | none => s.bad
  | some (pk, sk) => s.bad || decide (decapsEpochKey (P := P) t pk sk c.1 c.2.1 ≠
      some (P.kdfOK c.2.2 t))

/-- The sample of a key-generation send. -/
theorem sampledSend_eq_keygen [DecidableEq P.EpochKey] (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc) (s : TraceState P) (party : Bool) {t : ℕ}
    {a : Unit} (hst : s.game.stateAt party = .keysUnsampled t a) :
    sampledSend P hMac irl s party = (fun x : (P.PK × P.SK) × irl.KeygenRand =>
      ((keygenStep P hMac t a x.1.1 x.1.2, SendRand.keygen x.2),
        Function.update s.transcript t { (s.transcript t) with keypair := some x.1 }, s.bad)) <$>
      irl.keygenRleak := by
  simp only [sampledSend, hst, map_eq_bind_pure_comp]
  exact bind_congr fun x => by obtain ⟨⟨pk, sk⟩, rand⟩ := x; rfl

/-- The sample of a first-stage encapsulation send. -/
theorem sampledSend_eq_encaps1 [DecidableEq P.EpochKey] (hMac : P.Mac = Unit)
    (irl : P.kem.IncrementalRandLeak P.inc) (s : TraceState P) (party : Bool) {t : ℕ}
    {a : Unit} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived t a hdr dec) :
    sampledSend P hMac irl s party = (fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
      ((encaps1Step P hMac t a hdr dec x.1.1 x.1.2.1 x.1.2.2, SendRand.encaps1 x.2),
        Function.update s.transcript t { (s.transcript t) with encaps1 := some x.1 },
        encaps1Bad s t x.1)) <$> irl.encaps1Rleak hdr := by
  simp only [sampledSend, hst, map_eq_bind_pure_comp]
  exact bind_congr fun x => by obtain ⟨⟨es, ct1, k⟩, rand⟩ := x; rfl

section Projections

variable (irl : P.kem.IncrementalRandLeak P.inc)

/-- Key generation is the first component of the leaking key generation. -/
theorem keygen_eq_map : P.kem.keygen = Prod.fst <$> irl.keygenRleak := by
  rw [← irl.keygen_fst, map_eq_bind_pure_comp]
  rfl

/-- First-stage encapsulation is the first component of its leaking version. -/
theorem encaps1_eq_map (hdr : P.inc.PKheader) :
    P.inc.encaps1 hdr = Prod.fst <$> irl.encaps1Rleak hdr := by
  rw [← irl.encaps1_fst hdr, map_eq_bind_pure_comp]
  rfl

/-- Encapsulation is the first stage followed by the deterministic second stage. -/
theorem encaps_eq_map (pk : P.PK) :
    P.kem.encaps pk = (fun c : P.inc.St × P.inc.C₁ × P.K =>
      (P.inc.splitC.symm (c.2.1, P.hEnc2.encaps2Det c.1 (P.inc.toHeader pk)
        (P.inc.toVector pk)), c.2.2)) <$> P.inc.encaps1 (P.inc.toHeader pk) := by
  rw [P.inc.encaps_eq_stagedEncaps pk, KEMScheme.IncrementalStructure.stagedEncaps,
    map_eq_bind_pure_comp]
  refine bind_congr fun c => ?_
  obtain ⟨es, c1, k⟩ := c
  simp [P.hEnc2.encaps2_eq]

end Projections

/-- The first header chunk and encoder of epoch `t` for the public key `pk`. -/
def hdrChunk (P : Parameters ProbComp) (hMac : P.Mac = Unit) (t : ℕ) (a : Unit) (pk : P.PK) :
    (ℕ × P.Sym) × EncoderState (P.inc.PKheader × P.Mac) P.Sym :=
  (EncoderState.init P.ecpHdr
    (P.inc.toHeader pk, (auth P hMac).macHeader a t (P.inc.toHeader pk))).nextChunk

/-- The first `ct₁` chunk and encoder for `ct1`. -/
def ct1Chunk (P : Parameters ProbComp) (ct1 : P.inc.C₁) :
    (ℕ × P.Sym) × EncoderState P.inc.C₁ P.Sym :=
  (EncoderState.init P.ecpCt1 ct1).nextChunk

/-- The key-generation send in terms of `hdrChunk`. -/
theorem keygenStep_eq (hMac : P.Mac = Unit) (t : ℕ) (a : Unit) (pk : P.PK) (sk : P.SK) :
    keygenStep P hMac t a pk sk =
      { msg := { epoch := t, type := .hdr, data := some (hdrChunk P hMac t a pk).1 }
        sendingEpoch := t - 1, outputKey := none
        state := .keysSampled t a sk (P.inc.toVector pk) (hdrChunk P hMac t a pk).2 } := rfl

/-- The first-stage encapsulation send in terms of `ct1Chunk`. -/
theorem encaps1Step_eq (hMac : P.Mac = Unit) (t : ℕ) (a : Unit) (hdr : P.inc.PKheader)
    (dec : DecoderState P.inc.PKvector P.Sym) (es : P.inc.St) (ct1 : P.inc.C₁) (k : P.K) :
    encaps1Step P hMac t a hdr dec es ct1 k =
      { msg := { epoch := t, type := .ct1, data := some (ct1Chunk P ct1).1 }
        sendingEpoch := t - 1, outputKey := some (t, P.kdfOK k t)
        state := .ct1Sampled t ((auth P hMac).update a t (P.kdfOK k t)) hdr es ct1
          (ct1Chunk P ct1).2 dec } := rfl

section NoSample

variable (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- A send from a state that does not sample is `send` without coins. -/
theorem sendRleak_of_noSample {st : State P Unit} (h1 : ∀ t a, st ≠ .keysUnsampled t a)
    (h2 : ∀ t a hdr dec, st ≠ .headerReceived t a hdr dec) :
    MLKEMBraid.sendRleak P irl (auth P hMac) st =
      (fun r => (r, SendRand.none)) <$> MLKEMBraid.send P (auth P hMac) st := by
  cases st with
  | keysUnsampled t a => exact absurd rfl (h1 t a)
  | headerReceived t a hdr dec => exact absurd rfl (h2 t a hdr dec)
  | _ => rfl

variable [DecidableEq P.EpochKey]

/-- The sample of a send that samples nothing. -/
theorem sampledSend_of_noSample (s : TraceState P) (party : Bool)
    (h1 : ∀ t a, s.game.stateAt party ≠ .keysUnsampled t a)
    (h2 : ∀ t a hdr dec, s.game.stateAt party ≠ .headerReceived t a hdr dec) :
    sampledSend P hMac irl s party = (fun r => ((r, SendRand.none), s.transcript, s.bad)) <$>
      MLKEMBraid.send P (auth P hMac) (s.game.stateAt party) := by
  have hS : sampledSend P hMac irl s party = (fun out => (out, s.transcript, s.bad)) <$>
      MLKEMBraid.sendRleak P irl (auth P hMac) (s.game.stateAt party) := by
    cases hst : s.game.stateAt party with
    | keysUnsampled t a => exact absurd hst (h1 t a)
    | headerReceived t a hdr dec => exact absurd hst (h2 t a hdr dec)
    | _ => simp only [sampledSend, hst]
  rw [hS, sendRleak_of_noSample hMac irl h1 h2, Functor.map_map]

end NoSample

variable [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- Outcomes of a trace send: a refused proposal, or the committed sampled proposal. -/
theorem mem_support_traceSend {party leaking : Bool} {s : TraceState P}
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) :
    z.2 = s ∨ ∃ w ∈ support (sampledSend P hMac irl s party),
      (leaking = true →
        (exposure P irl).send (s.game.stateAt party) w.1.1.state w.1.2 ∩ s.game.challenged = ∅) ∧
      z.2 = { game := { sendUpdate s.game party w.1.1 with
                exposed := if leaking then
                  s.game.exposed ∪ (exposure P irl).send (s.game.stateAt party) w.1.1.state w.1.2
                else s.game.exposed },
              transcript := w.2.1, bad := w.2.2 } := by
  change z ∈ support (traceSend P hMac irl party leaking s) at hz
  simp only [traceSend] at hz
  rw [support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  dsimp only
  by_cases hc : (leaking && decide ((exposure P irl).send (s.game.stateAt party) w.1.1.state
      w.1.2 ∩ s.game.challenged ≠ ∅)) = true
  · left
    rw [ite_eq_left hc]
  · right
    refine ⟨w, hw, fun hl => ?_, by rw [ite_eq_right hc]⟩
    subst hl
    simpa using hc

/-- A send never clears the bad flag. -/
private theorem sampledSend_bad {s : TraceState P} {party : Bool}
    {w : (SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      (ℕ → EpochTranscript P) × Bool}
    (hw : w ∈ support (sampledSend P hMac irl s party)) (hb : s.bad = true) : w.2.2 = true := by
  cases hst : s.game.stateAt party with
  | keysUnsampled e a =>
      rw [sampledSend_eq_keygen hMac irl s party hst, support_map] at hw
      obtain ⟨x, -, rfl⟩ := hw
      exact hb
  | headerReceived e a hdr dec =>
      rw [sampledSend_eq_encaps1 hMac irl s party hst, support_map] at hw
      obtain ⟨x, -, rfl⟩ := hw
      dsimp only [encaps1Bad]
      split <;> simp [hb]
  | _ =>
      rw [sampledSend_of_noSample hMac irl s party (by simp [hst]) (by simp [hst]),
        support_map] at hw
      obtain ⟨x, -, rfl⟩ := hw
      exact hb

/-- A trace send never clears the bad flag. -/
theorem traceSend_bad {party leaking : Bool} {s : TraceState P} (hb : s.bad = true)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) : z.2.bad = true := by
  rcases mem_support_traceSend hMac irl hz with hz | ⟨w, hw, -, hz⟩
  · rw [hz]; exact hb
  · rw [hz]; exact sampledSend_bad hMac irl hw hb

/-- The send update keeps the exposed and challenged epochs. -/
theorem sendUpdate_flags (g : MLKEMBraid.GameState P Unit) (party : Bool)
    (r : SendResult P Unit) :
    (sendUpdate g party r).exposed = g.exposed ∧
      (sendUpdate g party r).challenged = g.challenged := by
  cases party <;> rcases hk : r.outputKey with _ | ⟨e, k⟩ <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hk]

/-- A trace send keeps the exposed and challenged epochs disjoint. -/
theorem traceSend_disjoint {party leaking : Bool} {s : TraceState P}
    (hs : s.game.exposed ∩ s.game.challenged = ∅)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) :
    z.2.game.exposed ∩ z.2.game.challenged = ∅ := by
  rcases mem_support_traceSend hMac irl hz with hz | ⟨w, -, hE, hz⟩
  · rw [hz]; exact hs
  rw [hz]
  obtain ⟨-, hch⟩ := sendUpdate_flags s.game party w.1.1
  dsimp only
  rw [hch]
  cases leaking
  · simpa using hs
  · simp only [ite_true]
    rw [Finset.union_inter_distrib_right, Finset.union_eq_empty]
    exact ⟨hs, hE rfl⟩

end MLKEMBraid.NoAuth
