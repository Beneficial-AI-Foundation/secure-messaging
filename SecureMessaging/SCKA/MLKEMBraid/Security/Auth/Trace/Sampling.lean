/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Trace.Basic
public import SecureMessaging.SCKA.MLKEMBraid.Security.Sampling

/-!
# Elementary transitions of the trace games

This module rewrites the sends of the trace game of `Trace.Basic` for each kind of sample, and
proves the facts about its oracles that later modules use: what a send, a challenge and a
corruption can change, and how the initial authenticator value enters `run`.

Each equation for a send keeps the send result, the leaked coins, the records and the bad flag
together. A table entry that is present gives an equation without a sample.
-/

@[expose] public section

open OracleSpec OracleComp
open SCKAScheme.sckaSecuritySpec SCKAScheme.sckaCorrectnessSpec
open ErasureCodePayload.Streaming

namespace MLKEMBraid.Auth

open Braid

/-- The key-generation send of epoch `t` with the key pair `(pk, sk)`. -/
def keygenStep {P : Parameters ProbComp} {AS : Type}
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (t : ℕ) (a : AS) (pk : P.PK) (sk : P.SK) : SendResult P AS :=
  let hdr := P.inc.toHeader pk
  let (chunk, enc) := (EncoderState.init P.ecpHdr (hdr, view.macHeader a t hdr)).nextChunk
  { msg := { epoch := t, type := .hdr, data := some chunk }
    sendingEpoch := t - 1, outputKey := none
    state := .keysSampled t a sk (P.inc.toVector pk) enc }

/-- The first-stage encapsulation send of epoch `t`, with the sample `(es, ct1)`, the epoch key
`x` and the authenticator value `p` that the game has determined for the epoch. -/
def encaps1Step {P : Parameters ProbComp} {AS : Type} (t : ℕ) (_a : AS)
    (hdr : P.inc.PKheader) (dec : P.decEk.D) (es : P.inc.St) (ct1 : P.inc.C₁)
    (x : P.EpochKey) (p : AS) : SendResult P AS :=
  let (chunk, enc) := (EncoderState.init P.ecpCt1 ct1).nextChunk
  { msg := { epoch := t, type := .ct1, data := some chunk }
    sendingEpoch := t - 1, outputKey := some (t, x)
    state := .ct1Sampled t p hdr es ct1 enc dec }

/-- The bad flag after a first-stage encapsulation sample `c` of epoch `t`: it is set if
decapsulation of the sample with the recorded key pair does not give the key derived from the
sampled shared secret. -/
def encaps1Bad {P : Parameters ProbComp} {AS : Type} [DecidableEq P.EpochKey]
    (s : TraceState P AS) (t : ℕ) (c : P.inc.St × P.inc.C₁ × P.K) : Bool :=
  match (s.transcript t).keypair with
  | none => s.bad
  | some (pk, sk) => s.bad || decide (decapsEpochKey (P := P) t pk sk c.1 c.2.1 ≠
      some (P.kdfOK c.2.2 t))

/-- The first header chunk and encoder of epoch `t` for the public key `pk`. -/
def hdrChunk {P : Parameters ProbComp} {AS : Type}
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (t : ℕ) (a : AS) (pk : P.PK) :
    (ℕ × P.Sym) × EncoderState (P.inc.PKheader × P.Mac) P.Sym :=
  (EncoderState.init P.ecpHdr
    (P.inc.toHeader pk, view.macHeader a t (P.inc.toHeader pk))).nextChunk

/-- The key-generation send in terms of `hdrChunk`. -/
theorem keygenStep_eq {P : Parameters ProbComp} {AS : Type}
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (t : ℕ) (a : AS) (pk : P.PK) (sk : P.SK) :
    keygenStep view t a pk sk =
      { msg := { epoch := t, type := .hdr, data := some (hdrChunk view t a pk).1 }
        sendingEpoch := t - 1, outputKey := none
        state := .keysSampled t a sk (P.inc.toVector pk) (hdrChunk view t a pk).2 } := rfl

/-- The first-stage encapsulation send in terms of `Braid.NoAuth.ct1Chunk`. -/
theorem encaps1Step_eq {P : Parameters ProbComp} {AS : Type} (t : ℕ) (a : AS)
    (hdr : P.inc.PKheader) (dec : P.decEk.D) (es : P.inc.St) (ct1 : P.inc.C₁)
    (x : P.EpochKey) (p : AS) :
    encaps1Step t a hdr dec es ct1 x p =
      { msg := { epoch := t, type := .ct1, data := some (Braid.NoAuth.ct1Chunk P ct1).1 }
        sendingEpoch := t - 1, outputKey := some (t, x)
        state := .ct1Sampled t p hdr es ct1 (Braid.NoAuth.ct1Chunk P ct1).2 dec } := rfl

/-- The send predicate in the nesting of `traceImpl`'s components. -/
def sendElim (P : Parameters ProbComp) (Root MacKey : Type)
    (irl : P.kem.IncrementalRandLeak P.inc) : (Spec P Root MacKey irl).Domain → Bool :=
  Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim
    (fun _ => false) (fun _ => true)) (fun _ => true)) (fun _ => false)) (fun _ => false))
    (fun _ => true)) (fun _ => true)) (fun _ => false)) (fun _ => false)) (fun _ => false)

/-- `sckaSecuritySpec.isSendQuery` selects the four send components of `traceImpl`. -/
theorem isSendQuery_eq_sendElim (P : Parameters ProbComp) (Root MacKey : Type)
    (irl : P.kem.IncrementalRandLeak P.inc) :
    ∀ t : (Spec P Root MacKey irl).Domain,
      SCKAScheme.sckaSecuritySpec.isSendQuery t = sendElim P Root MacKey irl t
  | OCorrectness (OUnif _) => rfl
  | OCorrectness OSendA => rfl
  | OCorrectness OSendB => rfl
  | OCorrectness (ORecvA _) => rfl
  | OCorrectness (ORecvB _) => rfl
  | OSendArleak => rfl
  | OSendBrleak => rfl
  | OChall _ => rfl
  | OCorruptA => rfl
  | OCorruptB => rfl

/-- The initial authenticator value `p` enters `run` as the starting state: if `rules.initPair`
is `pure p`, `run` is the simulation from `initTrace P p`. -/
theorem run_initPair_install {P : Parameters ProbComp} {Root MacKey : Type} {AS : Type}
    [SampleableType P.K] [SampleableType P.EpochKey] [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (obs : State P AS → Option (State P (Root × MacKey)))
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (tbl : Installed P irl AS) (rules : UpdateRules P AS) (modes : Modes) (repair : Bool)
    (A : Adversary P S irl) (p : AS) :
    run view obs S irl tbl { rules with initPair := pure p } modes repair A =
      (simulateQ (traceImpl view obs irl tbl rules modes repair) A).run (initTrace P p) := by
  simp only [run, pure_bind]
  rfl

variable {P : Parameters ProbComp} {AS : Type}

/-- The sample of a key-generation send when the table has no key pair for the epoch. -/
theorem sampledSend_eq_keygen [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    (s : TraceState P AS) (party : Bool) {t : ℕ} {a : AS}
    (hst : s.game.stateAt party = .keysUnsampled t a) (hkp : tbl.kp t = none) :
    sampledSend view irl tbl rules s party = (fun x : (P.PK × P.SK) × irl.KeygenRand =>
      ((keygenStep view t a x.1.1 x.1.2, SendRand.keygen x.2),
        Function.update s.transcript t { (s.transcript t) with keypair := some x.1 }, s.bad)) <$>
      irl.keygenRleak := by
  simp only [sampledSend, hst, hkp, map_eq_bind_pure_comp]
  exact bind_congr fun x => by obtain ⟨⟨pk, sk⟩, rand⟩ := x; rfl

/-- The sample of a key-generation send when the table has the key pair `x` for the epoch. -/
theorem sampledSend_eq_keygen_installed [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    (s : TraceState P AS) (party : Bool) {t : ℕ} {a : AS} {x : (P.PK × P.SK) × irl.KeygenRand}
    (hst : s.game.stateAt party = .keysUnsampled t a) (hkp : tbl.kp t = some x) :
    sampledSend view irl tbl rules s party =
      pure ((keygenStep view t a x.1.1 x.1.2, SendRand.keygen x.2),
        Function.update s.transcript t { (s.transcript t) with keypair := some x.1 }, s.bad) := by
  simp only [sampledSend, hst, hkp, pure_bind]
  obtain ⟨⟨pk, sk⟩, rand⟩ := x
  rfl

/-- The sample of a first-stage encapsulation send when the table has no encapsulation for the
epoch. -/
theorem sampledSend_eq_encaps1 [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    (s : TraceState P AS) (party : Bool) {t : ℕ} {a : AS} {hdr : P.inc.PKheader}
    {dec : P.decEk.D} (hst : s.game.stateAt party = .headerReceived t a hdr dec)
    (hec : tbl.ec t = none) :
    sampledSend view irl tbl rules s party = (do
      let x ← irl.encaps1Rleak hdr
      let key ← rules.key t x.1.2.2
      let pair ← rules.pair t a key
      pure ((encaps1Step t a hdr dec x.1.1 x.1.2.1 key pair, SendRand.encaps1 x.2),
        Function.update s.transcript t
          { (s.transcript t) with encaps1 := some x.1, key := some key, pair := some pair },
        encaps1Bad s t x.1)) := by
  simp only [sampledSend, hst, hec]
  exact bind_congr fun x => by obtain ⟨⟨es, ct1, k⟩, rand⟩ := x; rfl

/-- The sample of a first-stage encapsulation send when the table has the encapsulation `x` for
the epoch. -/
theorem sampledSend_eq_encaps1_installed [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    (s : TraceState P AS) (party : Bool) {t : ℕ} {a : AS} {hdr : P.inc.PKheader}
    {dec : P.decEk.D} {x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand}
    (hst : s.game.stateAt party = .headerReceived t a hdr dec) (hec : tbl.ec t = some x) :
    sampledSend view irl tbl rules s party = (do
      let key ← rules.key t x.1.2.2
      let pair ← rules.pair t a key
      pure ((encaps1Step t a hdr dec x.1.1 x.1.2.1 key pair, SendRand.encaps1 x.2),
        Function.update s.transcript t
          { (s.transcript t) with encaps1 := some x.1, key := some key, pair := some pair },
        encaps1Bad s t x.1)) := by
  simp only [sampledSend, hst, hec, pure_bind]
  obtain ⟨⟨es, ct1, k⟩, rand⟩ := x
  rfl

/-- A send from a state that does not sample is `send` without coins. -/
theorem sendRleak_of_noSample
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) {st : State P AS}
    (h1 : ∀ t a, st ≠ .keysUnsampled t a) (h2 : ∀ t a hdr dec, st ≠ .headerReceived t a hdr dec) :
    Braid.sendRleak P irl view st =
      (fun r => (r, SendRand.none)) <$> Braid.send P view st := by
  cases st with
  | keysUnsampled t a => exact absurd rfl (h1 t a)
  | headerReceived t a hdr dec => exact absurd rfl (h2 t a hdr dec)
  | _ => rfl

/-- The sample of a send that samples nothing. -/
theorem sampledSend_of_noSample [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    (s : TraceState P AS) (party : Bool)
    (h1 : ∀ t a, s.game.stateAt party ≠ .keysUnsampled t a)
    (h2 : ∀ t a hdr dec, s.game.stateAt party ≠ .headerReceived t a hdr dec) :
    sampledSend view irl tbl rules s party =
      (fun r => ((r, SendRand.none), s.transcript, s.bad)) <$>
        Braid.send P view (s.game.stateAt party) := by
  have hS : sampledSend view irl tbl rules s party = (fun out => (out, s.transcript, s.bad)) <$>
      Braid.sendRleak P irl view (s.game.stateAt party) := by
    cases hst : s.game.stateAt party with
    | keysUnsampled t a => exact absurd hst (h1 t a)
    | headerReceived t a hdr dec => exact absurd hst (h2 t a hdr dec)
    | _ => simp only [sampledSend, hst]
  rw [hS, sendRleak_of_noSample view irl h1 h2, Functor.map_map]

/-- `liftGame` runs a game oracle on the `game` field. -/
theorem liftGame_run {α : Type} (c : StateT (GameState P AS) ProbComp α) (s : TraceState P AS) :
    (liftGame c).run s = (fun z => (z.1, { s with game := z.2 })) <$> c.run s.game := rfl

/-- Projecting a lifted game oracle to its game state gives the game oracle. -/
theorem map_game_liftGame {α : Type} (c : StateT (GameState P AS) ProbComp α)
    (s : TraceState P AS) :
    Prod.map id TraceState.game <$> (liftGame c).run s = c.run s.game := by
  rw [liftGame_run, Functor.map_map]
  exact id_map (c.run s.game)

/-- The outcomes of a lifted game oracle keep the records and the bad flag. -/
theorem mem_support_liftGame {α : Type} {c : StateT (GameState P AS) ProbComp α}
    {s : TraceState P AS} {z : α × TraceState P AS} (hz : z ∈ support ((liftGame c).run s)) :
    ∃ w ∈ support (c.run s.game), z = (w.1, { s with game := w.2 }) := by
  rw [liftGame_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

/-- A corruption of A reveals A's state, or is refused without a state change. -/
theorem mem_support_oracleCorruptA {V : State P AS → Finset ℕ} {g : GameState P AS}
    {w : Option (State P AS) × GameState P AS}
    (hw : w ∈ support ((SCKAScheme.oracleCorruptA V (State P AS) P.EpochKey
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
theorem mem_support_oracleCorruptB {V : State P AS → Finset ℕ} {g : GameState P AS}
    {w : Option (State P AS) × GameState P AS}
    (hw : w ∈ support ((SCKAScheme.oracleCorruptB V (State P AS) P.EpochKey
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
    {irl : P.kem.IncrementalRandLeak P.inc} {tbl : Installed P irl AS} {modes : Modes} {e : ℕ}
    {s : TraceState P AS} {z : Option P.EpochKey × TraceState P AS}
    (hz : z ∈ support ((traceChallenge tbl modes e).run s)) :
    z.2 = s ∨ (e ∉ s.game.exposed ∧
      z.2 = { s with game := { s.game with challenged := insert e s.game.challenged } }) := by
  change z ∈ support (traceChallenge tbl modes e s) at hz
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

/-- Outcomes of a trace send: a refused proposal, or the committed sampled proposal. -/
theorem mem_support_traceSend [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    {party leaking : Bool} {s : TraceState P AS}
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P AS}
    (hz : z ∈ support ((traceSend view irl tbl rules party leaking).run s)) :
    z.2 = s ∨ ∃ w ∈ support (sampledSend view irl tbl rules s party),
      (leaking = true →
        (exposureAt P irl AS).rleak (s.game.stateAt party) w.1.2 ∩ s.game.challenged = ∅) ∧
      z.2 = { game := { sendUpdate s.game party w.1.1 with
                exposed := if leaking then
                  s.game.exposed ∪ (exposureAt P irl AS).rleak (s.game.stateAt party) w.1.2
                else s.game.exposed },
              transcript := w.2.1, bad := w.2.2 } := by
  change z ∈ support (traceSend view irl tbl rules party leaking s) at hz
  simp only [traceSend] at hz
  rw [support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  dsimp only
  by_cases hc : (leaking && decide ((exposureAt P irl AS).rleak (s.game.stateAt party)
      w.1.2 ∩ s.game.challenged ≠ ∅)) = true
  · left
    rw [ite_eq_left hc]
  · right
    refine ⟨w, hw, fun hl => ?_, by rw [ite_eq_right hc]⟩
    subst hl
    simpa using hc

/-- A trace send never clears the bad flag. -/
theorem traceSend_bad [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    {party leaking : Bool} {s : TraceState P AS} (hb : s.bad = true)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P AS}
    (hz : z ∈ support ((traceSend view irl tbl rules party leaking).run s)) :
    z.2.bad = true := by
  rcases mem_support_traceSend view irl tbl rules hz with hz | ⟨w, hw, -, hz⟩
  · rw [hz]; exact hb
  rw [hz]
  change w.2.2 = true
  cases hst : s.game.stateAt party with
  | keysUnsampled e a =>
      cases hkp : tbl.kp e with
      | none =>
          rw [sampledSend_eq_keygen view irl tbl rules s party hst hkp, support_map] at hw
          obtain ⟨x, -, rfl⟩ := hw
          exact hb
      | some x =>
          rw [sampledSend_eq_keygen_installed view irl tbl rules s party hst hkp,
            support_pure, Set.mem_singleton_iff] at hw
          rw [hw]
          exact hb
  | headerReceived e a hdr dec =>
      cases hec : tbl.ec e with
      | none =>
          rw [sampledSend_eq_encaps1 view irl tbl rules s party hst hec] at hw
          simp only [mem_support_bind_iff, mem_support_pure_iff] at hw
          obtain ⟨x, -, key, -, pair, -, rfl⟩ := hw
          dsimp only [encaps1Bad]
          split <;> simp [hb]
      | some x =>
          rw [sampledSend_eq_encaps1_installed view irl tbl rules s party hst hec] at hw
          simp only [mem_support_bind_iff, mem_support_pure_iff] at hw
          obtain ⟨key, -, pair, -, rfl⟩ := hw
          dsimp only [encaps1Bad]
          split <;> simp [hb]
  | _ =>
      rw [sampledSend_of_noSample view irl tbl rules s party (by simp [hst]) (by simp [hst]),
        support_map] at hw
      obtain ⟨x, -, rfl⟩ := hw
      exact hb

/-- The send update keeps the exposed and challenged epochs. -/
theorem sendUpdate_flags [DecidableEq P.EpochKey] (g : GameState P AS) (party : Bool)
    (r : SendResult P AS) :
    (sendUpdate g party r).exposed = g.exposed ∧
      (sendUpdate g party r).challenged = g.challenged := by
  cases party <;> rcases hk : r.outputKey with _ | ⟨e, k⟩ <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hk]

/-- A trace send keeps the exposed and challenged epochs disjoint. -/
theorem traceSend_disjoint [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    {party leaking : Bool} {s : TraceState P AS}
    (hs : s.game.exposed ∩ s.game.challenged = ∅)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P AS}
    (hz : z ∈ support ((traceSend view irl tbl rules party leaking).run s)) :
    z.2.game.exposed ∩ z.2.game.challenged = ∅ := by
  rcases mem_support_traceSend view irl tbl rules hz with hz | ⟨w, -, hE, hz⟩
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

end MLKEMBraid.Auth
