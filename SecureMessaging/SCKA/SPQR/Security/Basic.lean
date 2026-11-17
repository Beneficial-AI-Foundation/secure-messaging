/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Correctness.Relation
public import SecureMessaging.SCKA.Security.Hybrids

/-!
# SPQR security interface and transitions over variable operations

Let `P : SPQR.Parameters ProbComp`, `auth` a ratcheted authenticator, `sampleInitKey` a sampler of
initial keys, and `scheme P auth sampleInitKey` the SPQR scheme (`SPQR.Construction`).

**Definitions.**

- `SecurityAdversary P AuthState`: the Boolean adversaries against the SCKA security interface
  `securitySpec P AuthState` of SPQR.
- `vuln P AuthState`: the exposure policy of both parties. Every SPQR state `st` carries an
  authenticator state, which the update of epoch `st.authEpoch` consumes together with the key of
  that epoch (`PartyState.authEpoch`). Corrupting a state `st` of epoch `t` exposes `st.authEpoch`,
  and also `t` and `t + 1` if `st` holds a decapsulation key or an encapsulation state
  (`PartyState.holdsSecret`). A leaking send that runs key generation or first-stage
  encapsulation at `t` exposes `t` and `t + 1`: the key of `t` turns an authenticator state
  entering `t` into the one entering `t + 1`.
- `authAt auth e upd`: `auth` with its update at epoch `e` replaced by `upd`.
- `Ops P`: the operations that the proof games vary, namely the leaking key-generation and
  first-stage encapsulation samplers, indexed by the epoch of the sending party, the second stage,
  and the generator's key derivation at the completion of `ct₂`; `Ops.real P` are those of `P`,
  with `P.kdfOK` after decapsulation, and `idealOps ops s` looks up the key recorded by the peer in
  `s`.
- `sendRleakWith auth ops` and `sendWith auth ops`: the leaking and ordinary sends with the
  samplers of `ops`; `recvWith auth ops`: `Chunked.recv` with the second stage and the key
  derivation of `ops`.
- `schemeWith auth ops sampleInitKey`: the SCKA instance of these transitions.

**Main results.**

- The sends over `Ops.real P` are those of `scheme P auth sampleInitKey` (`sendWith_real`,
  `sendRleakWith_real`).
- Every possible leaking send from `st` returns coins `rand` with
  `(vuln P AuthState).rleak st rand = leakEpochs st`, where `leakEpochs st` is
  `{st.epoch, st.epoch + 1}` if a send from `st` samples and `∅` otherwise
  (`sendRleakWith_exposure`, `scheme_sendArleak_exposure`).
- With the second stage of `P`, `recvWith` agrees with `recv` on every delivery other than a `ct₂`
  chunk of the current epoch in `ekSentCt1Received` (`recvWith_eq_recv_of_real`), and on that
  chunk too when the key derivation of `ops` is decapsulation followed by `P.kdfOK`
  (`recvWith_eq_recv_of_completeKey`).
-/

@[expose] public section

open OracleSpec OracleComp

namespace SPQR

open Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}

/-! ### Interface and exposure policy -/

/-- SPQR's SCKA security interface. -/
abbrev securitySpec (P : SPQR.Parameters ProbComp) (AuthState : Type) :=
  SCKAScheme.sckaSecuritySpec (PartyState P AuthState) (PartyState P AuthState) P.EpochKey
    (Message P.Sym) (Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand)

/-- A Boolean adversary against `securitySpec P AuthState`. -/
abbrev SecurityAdversary (P : SPQR.Parameters ProbComp) (AuthState : Type) :=
  SCKAScheme.SCKAAdversary (PartyState P AuthState) (PartyState P AuthState) P.EpochKey
    (Message P.Sym) (Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand)

/-- Whether a state holds a decapsulation key or an encapsulation state: the four generator states
after key generation and the three encapsulator states between the first and the second stage of
encapsulation. -/
-- ANCHOR: SPQR_holdsSecret
def Chunked.PartyState.holdsSecret : PartyState P AuthState → Bool
  | .keysSampled .. | .headerSent .. | .ct1Received .. | .ekSentCt1Received .. => true
  | .ct1Sampled .. | .ekReceivedCt1Sampled .. | .ct1Acknowledged .. => true
  | _ => false
-- ANCHOR_END: SPQR_holdsSecret

/-- Whether the authenticator state of a party already includes the key of its current epoch: the
four encapsulator states after first-stage encapsulation. -/
-- ANCHOR: SPQR_authUpdated
def Chunked.PartyState.authUpdated : PartyState P AuthState → Bool
  | .ct1Sampled .. | .ekReceivedCt1Sampled .. | .ct1Acknowledged .. | .ct2Sampled .. => true
  | _ => false
-- ANCHOR_END: SPQR_authUpdated

/-- The epoch whose authenticator update consumes the authenticator state of `st`: the epoch after
`st.epoch` if the state already includes the key of `st.epoch`, and `st.epoch` otherwise. -/
-- ANCHOR: SPQR_authEpoch
def Chunked.PartyState.authEpoch (st : PartyState P AuthState) : ℕ :=
  if st.authUpdated then st.epoch + 1 else st.epoch
-- ANCHOR_END: SPQR_authEpoch

/-- Whether a send from the state samples: `keysUnsampled` and `headerReceived`. -/
def Chunked.PartyState.samples : PartyState P AuthState → Bool
  | .keysUnsampled .. | .headerReceived .. => true
  | _ => false

/-- The epochs exposed by a leaking send from `st`: `{st.epoch, st.epoch + 1}` if the send samples,
else `∅`. -/
def leakEpochs (st : PartyState P AuthState) : Finset ℕ :=
  if st.samples then {st.epoch, st.epoch + 1} else ∅

/-- The exposure policy of SPQR, shared by both parties. Corrupting a state `st` of epoch `t`
exposes `st.authEpoch`, the epoch whose authenticator update consumes the revealed authenticator
state, and also `t` and `t + 1` if `st` holds a secret of `t`. A leaking send that returns
key-generation or encapsulation coins of `t` exposes `t` and `t + 1`. The second epoch is exposed
because the key of `t` turns an authenticator state entering `t` into the one entering `t + 1`. -/
-- ANCHOR: SPQR_vuln
def vuln (P : SPQR.Parameters ProbComp) (AuthState : Type) :
    SCKAScheme.VulnerableEpochs (PartyState P AuthState)
      (Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand) where
  corrupt st := insert st.authEpoch (if st.holdsSecret then {st.epoch, st.epoch + 1} else ∅)
  rleak st rand := match rand with
    | .none => ∅
    | .keygen _ => {st.epoch, st.epoch + 1}
    | .encaps1 _ => {st.epoch, st.epoch + 1}
-- ANCHOR_END: SPQR_vuln

/-- An epoch `t` is exposed by corrupting `st` exactly when it is `st.authEpoch`, or `st` holds a
secret and `t` is `st.epoch` or `st.epoch + 1`. -/
theorem mem_vuln_corrupt {st : PartyState P AuthState} {t : ℕ} :
    t ∈ (vuln P AuthState).corrupt st ↔
      t = st.authEpoch ∨ (st.holdsSecret = true ∧ (t = st.epoch ∨ t = st.epoch + 1)) := by
  by_cases h : st.holdsSecret <;> simp [vuln, h]

/-- Corrupting a state that holds a secret of its epoch exposes that epoch and the next one. -/
theorem mem_vuln_corrupt_of_holdsSecret {st : PartyState P AuthState}
    (h : st.holdsSecret = true) :
    st.epoch ∈ (vuln P AuthState).corrupt st ∧ st.epoch + 1 ∈ (vuln P AuthState).corrupt st :=
  ⟨mem_vuln_corrupt.mpr (Or.inr ⟨h, Or.inl rfl⟩), mem_vuln_corrupt.mpr (Or.inr ⟨h, Or.inr rfl⟩)⟩

/-- The key table of `party`. -/
def GameState.keysAt (s : GameState P AuthState) (party : Bool) : ℕ → Option P.EpochKey :=
  if party then s.keyA else s.keyB

/-- The generator of epoch `t` is `A` if `t` is odd and `B` otherwise. -/
def generatorOf (t : ℕ) : Bool := decide (t % 2 = 1)

/-! ### Game-state updates and their translation into Braid -/

/-- Translate the result of a receive. -/
def Chunked.RecvResult.toBraid (r : RecvResult P AuthState) :
    Braid.RecvResult P.toBraid AuthState :=
  ⟨r.receivingEpoch, r.outputKey, r.state.toBraid⟩

/-- The translation keeps the correctness flag. -/
@[simp] theorem toBraid_correct (s : GameState P AuthState) : s.toBraid.correct = s.correct := rfl

/-- The translation keeps the key tables. -/
@[simp] theorem toBraid_keysAt (s : GameState P AuthState) (party : Bool) :
    s.toBraid.keysAt party = if party then s.keyA else s.keyB := by
  cases party <;> rfl

/-- A message recorded by `party` is recorded, translated, in the translated game state. -/
theorem GameState.toBraid_messagesAt_eq_some {s : GameState P AuthState} {party : Bool} {n : ℕ}
    {msg : Message P.Sym} {tsnd : ℕ} (h : s.messagesAt party n = some (msg, tsnd)) :
    s.toBraid.messagesAt party n = some (msg.toBraid, tsnd) := by
  simp [h]

/-- The translation of the initial SPQR game state is the initial Braid game state. -/
theorem toBraid_initGameState
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (ik : InitKey) :
    GameState.toBraid (SCKAScheme.initGameState (initA P auth ik) (initB P auth ik)) =
      SCKAScheme.initGameState (Braid.initA P.toBraid auth ik)
        (Braid.initB P.toBraid auth ik) := rfl

section Updates

variable [DecidableEq P.EpochKey]

/-- The game state written by the send query of `party` for the send result `r`. -/
def sendUpdate (s : GameState P AuthState) (party : Bool) (r : SendResult P AuthState) :
    GameState P AuthState :=
  if party then SCKAScheme.sendAUpdate s r.outputKey r.msg r.sendingEpoch r.state
  else SCKAScheme.sendBUpdate s r.outputKey r.msg r.sendingEpoch r.state

/-- The game state written by the receive query of `party` for the receive result `r`, the stored
report `tsnd` and the receive report `trcv`. -/
def recvUpdate (s : GameState P AuthState) (party : Bool) (tsnd : ℕ) (r : RecvResult P AuthState)
    (trcv : ℕ) : GameState P AuthState :=
  if party then SCKAScheme.recvAUpdate s tsnd r.outputKey trcv r.state
  else SCKAScheme.recvBUpdate s tsnd r.outputKey trcv r.state

/-- A send changes the state of the sender only. -/
@[simp] theorem stateAt_sendUpdate (s : GameState P AuthState) (party who : Bool)
    (r : SendResult P AuthState) :
    (sendUpdate s party r).stateAt who = if who = party then r.state else s.stateAt who := by
  cases party <;> cases who <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hkey, GameState.stateAt]

/-- A send records the sent message, with its report, as the next message of the sender. -/
@[simp] theorem messagesAt_sendUpdate (s : GameState P AuthState) (party who : Bool)
    (r : SendResult P AuthState) :
    (sendUpdate s party r).messagesAt who =
      if who = party then
        Function.update (s.messagesAt party) ((if party then s.nA else s.nB) + 1)
          (some (r.msg, r.sendingEpoch))
      else s.messagesAt who := by
  cases party <;> cases who <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hkey, GameState.messagesAt]

/-- A receive changes the state of the receiver only. -/
@[simp] theorem stateAt_recvUpdate (s : GameState P AuthState) (party who : Bool) (tsnd : ℕ)
    (r : RecvResult P AuthState) (trcv : ℕ) :
    (recvUpdate s party tsnd r trcv).stateAt who =
      if who = party then r.state else s.stateAt who := by
  cases party <;> cases who <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp [recvUpdate, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, hkey, GameState.stateAt]

/-- A receive keeps both message tables. -/
@[simp] theorem messagesAt_recvUpdate (s : GameState P AuthState) (party who : Bool) (tsnd : ℕ)
    (r : RecvResult P AuthState) (trcv : ℕ) :
    (recvUpdate s party tsnd r trcv).messagesAt who = s.messagesAt who := by
  cases party <;> cases who <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp [recvUpdate, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, hkey, GameState.messagesAt]

/-- The translation of a send update is the Braid send update for the translated result. -/
theorem toBraid_sendUpdate (s : GameState P AuthState) (party : Bool)
    (r : SendResult P AuthState) :
    (sendUpdate s party r).toBraid = Braid.sendUpdate s.toBraid party r.toBraid := by
  obtain ⟨ρ, tsnd, keyOpt, st'⟩ := r
  have htable (msgs : ℕ → Option (Message P.Sym × ℕ)) (k : ℕ) :
      (fun n => (Function.update msgs k (some (ρ, tsnd)) n).map
        fun (msg, t) => (msg.toBraid, t)) =
      Function.update (fun n => (msgs n).map fun (msg, t) => (msg.toBraid, t)) k
        (some (ρ.toBraid, tsnd)) :=
    Function.comp_update (Option.map (Prod.map Chunked.Message.toBraid id)) msgs k (some (ρ, tsnd))
  cases party <;> rcases keyOpt with _ | ⟨tI, key⟩ <;>
    simp only [sendUpdate, Braid.sendUpdate, SendResult.toBraid, Bool.false_eq_true, ↓reduceIte,
      SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, GameState.toBraid, htable] <;> rfl

/-- The translation of a receive update is the Braid receive update for the translated result. -/
theorem toBraid_recvUpdate (s : GameState P AuthState) (party : Bool) (tsnd : ℕ)
    (r : RecvResult P AuthState) (trcv : ℕ) :
    (recvUpdate s party tsnd r trcv).toBraid =
      Braid.recvUpdate s.toBraid party tsnd r.toBraid trcv := by
  cases party <;> rcases hk : r.outputKey with _ | ⟨tI, key⟩ <;>
    simp [recvUpdate, Braid.recvUpdate, Chunked.RecvResult.toBraid, SCKAScheme.recvAUpdate,
      SCKAScheme.recvBUpdate, GameState.toBraid, hk]

end Updates

variable (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (sampleInitKey : ProbComp InitKey)

/-! ### The authenticator with one update replaced -/

/-- The authenticator `auth` with its update at epoch `e` replaced by `upd`; the other operations
are unchanged. -/
@[simps -fullyApplied init macHeader verifyHeader macCiphertext verifyCiphertext]
def authAt (e : ℕ) (upd : AuthState → AuthState) :
    RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac :=
  { auth with update := fun a t ik => if t = e then upd a else auth.update a t ik }

/-- At epoch `e`, `authAt auth e upd` updates with `upd`. -/
@[simp] theorem authAt_update_self (e : ℕ) (upd : AuthState → AuthState)
    (a : AuthState) (ik : P.EpochKey) : (authAt auth e upd).update a e ik = upd a := by
  simp [authAt]

/-- At an epoch `t ≠ e`, `authAt auth e upd` updates as `auth`. -/
@[simp] theorem authAt_update_of_ne (e : ℕ) (upd : AuthState → AuthState)
    (a : AuthState) {t : ℕ} (ht : t ≠ e) (ik : P.EpochKey) :
    (authAt auth e upd).update a t ik = auth.update a t ik := by
  simp [authAt, ht]

/-- Replacing the update at `e` twice keeps the second replacement. -/
@[simp] theorem authAt_authAt (e : ℕ) (upd upd' : AuthState → AuthState) :
    authAt (authAt auth e upd) e upd' = authAt auth e upd' := by
  unfold authAt
  congr 1
  funext a t ik
  by_cases h : t = e <;> simp [h]

end SPQR

open ErasureCodePayload.Streaming

namespace SPQR.Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}

/-- The operations of an SPQR instance varied by the proof games: the leaking samplers, indexed
by the epoch of the sending party, the second-stage encapsulation, and the generator's key
derivation at the completion of `ct₂`. -/
structure Ops (P : SPQR.Parameters ProbComp) where
  /-- Key generation with its coins, at the given epoch. -/
  keygenRleak : ℕ → ProbComp ((P.PK × P.SK) × P.det.KeygenRand)
  /-- First-stage encapsulation with its coins, at the given epoch. -/
  encaps1Rleak : ℕ → P.det.PKheader →
    ProbComp ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)
  /-- Second-stage encapsulation at the given epoch, from the encapsulation state, header and
  vector. -/
  encaps2 : ℕ → P.det.St → P.det.PKheader → P.det.PKvector → P.det.C₂
  /-- The epoch key of the generator at epoch `t` with decapsulation key `sk` on the ciphertext
  `(ct1, ct2)`, or `none` to refuse. -/
  completeKey : ℕ → P.SK → P.det.C₁ → P.det.C₂ → Option P.EpochKey

/-- The operations of `scheme P auth sampleInitKey`: the leaking key generation and first stage of
`P` (`P.generateRleak`, `P.encaps1Rleak`), its second stage, and decapsulation (`P.decaps`) followed
by `P.kdfOK`. -/
def Ops.real (P : SPQR.Parameters ProbComp) :
    Ops P where
  keygenRleak _ := P.generateRleak
  encaps1Rleak _ := P.encaps1Rleak
  encaps2 _ := P.det.encaps2Det
  completeKey t sk c1 c2 := (P.decaps sk c1 c2).map (P.kdfOK · t)

/-- The second stage of `Ops.real P` is that of `P`. -/
@[simp] theorem Ops.real_encaps2 (t : ℕ) : (Ops.real P).encaps2 t = P.det.encaps2Det := rfl

/-- `ops` with the key derivation replaced by the lookup of the key recorded by the peer in `s`. -/
def idealOps (ops : Ops P) (s : GameState P AuthState) :
    Ops P :=
  { ops with completeKey := fun t _ _ _ => s.keysAt (!generatorOf t) t }

variable (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)

/-- `SPQR.sendRleak` with the samplers of `ops`. -/
def sendRleakWith (ops : Ops P) (st : PartyState P AuthState) :
    ProbComp (SendResult P AuthState × Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand) :=
  match st with
  | .keysUnsampled core => do
      let ((pk, sk), r) ← ops.keygenRleak core.ep
      let hdr := P.det.toHeader pk
      let tag := auth.macHeader core.authSt core.ep hdr
      let core' : EkSender.HeaderSent P AuthState :=
        ⟨core.ep, core.authSt, pk, sk⟩
      let (chunk, enc) := (EncoderState.init P.ecpHdr (hdr, tag)).nextChunk
      pure (⟨⟨core.ep, .hdr chunk⟩, core.ep - 1, none, .keysSampled core' enc⟩, .keygen r)
  | .headerReceived core dec => do
      let ((encapsSt, c1, k), r) ← ops.encaps1Rleak core.ep core.hdr
      let ik := P.kdfOK k core.ep
      let core' : CtSender.Ct1Sent P AuthState :=
        ⟨core.ep, auth.update core.authSt core.ep ik, core.hdr, encapsSt, c1⟩
      let (chunk, enc) := (EncoderState.init P.ecpCt1 c1).nextChunk
      pure (⟨⟨core.ep, .ct1 chunk⟩, core.ep - 1, some (core.ep, ik),
        .ct1Sampled core' enc dec⟩, .encaps1 r)
  | st => (fun r => (r, .none)) <$> SPQR.send P auth st

/-- `SPQR.send` with the samplers of `ops`. -/
def sendWith (ops : Ops P) (st : PartyState P AuthState) :
    ProbComp (SendResult P AuthState) :=
  Prod.fst <$> sendRleakWith auth ops st

/-- The leaking send of `Ops.real P` is `SPQR.sendRleak`. -/
theorem sendRleakWith_real (st : PartyState P AuthState) :
    sendRleakWith auth (Ops.real P) st = sendRleak P auth st := by
  cases st <;>
    simp only [sendRleakWith, Ops.real, SPQR.sendRleak, EkSender.sendHeaderRleak,
      CtSender.sendCt1Rleak, Parameters.generateRleak, Parameters.encaps1Rleak,
      map_eq_pure_bind, bind_assoc, pure_bind]

/-- The send of `Ops.real P` is `SPQR.send`. -/
theorem sendWith_real (st : PartyState P AuthState) :
    sendWith auth (Ops.real P) st = SPQR.send P auth st := by
  rw [sendWith, sendRleakWith_real, ← send_eq_map_sendRleak]

/-- The exposure of a leaking send of `ops` from `st` is `leakEpochs st`. -/
theorem sendRleakWith_exposure (ops : Ops P)
    (st : PartyState P AuthState)
    (out : SendResult P AuthState × Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand)
    (hout : out ∈ support (sendRleakWith auth ops st)) :
    (vuln P AuthState).rleak st out.2 = leakEpochs st := by
  cases st
  case keysUnsampled core =>
    simp only [sendRleakWith, mem_support_bind_iff, mem_support_pure_iff] at hout
    obtain ⟨⟨⟨pk, sk⟩, r⟩, -, rfl⟩ := hout
    rfl
  case headerReceived core dec =>
    simp only [sendRleakWith, mem_support_bind_iff, mem_support_pure_iff] at hout
    obtain ⟨⟨⟨es, c1, k⟩, r⟩, -, rfl⟩ := hout
    rfl
  all_goals
    simp only [sendRleakWith, support_map, Set.mem_image] at hout
    obtain ⟨r, -, rfl⟩ := hout
    rfl

/-- The sends do not use the key derivation. -/
theorem sendRleakWith_idealOps (ops : Ops P) (s : GameState P AuthState)
    (st : PartyState P AuthState) :
    sendRleakWith auth (idealOps ops s) st = sendRleakWith auth ops st := by
  cases st <;> rfl

/-- The ordinary sends do not use the key derivation. -/
theorem sendWith_idealOps (ops : Ops P) (s : GameState P AuthState)
    (st : PartyState P AuthState) :
    sendWith auth (idealOps ops s) st = sendWith auth ops st := by
  rw [sendWith, sendRleakWith_idealOps, ← sendWith]

/-- `EkSender.recvCt2` with the key derivation `completeKey`: refuse if it returns `none`, else
ratchet the authenticator with the key, verify the tag, and return the next state and the key. -/
def recvCt2With (completeKey : ℕ → P.SK → P.det.C₁ → P.det.C₂ → Option P.EpochKey)
    (st : EkSender.EkSentCt1Received P AuthState) (c2 : P.det.C₂) (tag : P.Mac) :
    Option (CtSender.NoHeaderReceived AuthState × (ℕ × P.EpochKey)) :=
  match completeKey st.ep st.sk st.c1 c2 with
  | none => none
  | some ik =>
    let authSt' := auth.update st.authSt st.ep ik
    if auth.verifyCiphertext authSt' st.ep (st.c1, c2) tag then
      some (⟨st.ep + 1, authSt'⟩, (st.ep, ik))
    else none

/-- `recvCt2With` with decapsulation followed by `P.kdfOK` is `EkSender.recvCt2`. -/
private theorem recvCt2With_decaps (st : EkSender.EkSentCt1Received P AuthState) (c2 : P.det.C₂)
    (tag : P.Mac) (completeKey : ℕ → P.SK → P.det.C₁ → P.det.C₂ → Option P.EpochKey)
    (h : completeKey st.ep st.sk st.c1 c2 =
      (P.det.decapsDet st.sk (P.det.splitC.symm (st.c1, c2))).map (fun k => P.kdfOK k st.ep)) :
    recvCt2With auth completeKey st c2 tag =
      EkSender.recvCt2 P auth st c2 tag := by
  simp only [recvCt2With, EkSender.recvCt2, Parameters.decaps, h]
  cases P.det.decapsDet st.sk (P.det.splitC.symm (st.c1, c2)) <;> rfl

/-- `Chunked.completeCt2` with the second-stage encapsulation `encaps2` of the epoch: the second
ciphertext component, its tag under the current authenticator state, and the `ct₂` encoder. -/
def completeCt2With (encaps2 : ℕ → P.det.St → P.det.PKheader → P.det.PKvector → P.det.C₂)
    (core : CtSender.Ct1SentEkReceived P AuthState) : PartyState P AuthState :=
  let c2 := encaps2 core.ep core.encapsSt core.hdr core.ek
  let tag := auth.macCiphertext core.authSt core.ep (core.c1, c2)
  .ct2Sampled ⟨core.ep, core.authSt⟩ (EncoderState.init P.ecpCt2 (c2, tag))

/-- `completeCt2With` with the second stage of `P` is `Chunked.completeCt2`. -/
private theorem completeCt2With_det :
    completeCt2With auth (fun _ => P.det.encaps2Det) = completeCt2 P auth := rfl

/-- `Chunked.recv` with the second stage and the key derivation of `ops`: at the current epoch, a
delivery completing the encapsulation-key vector after `ct₁` is acknowledged, or acknowledging
`ct₁` after the vector, completes stage two with `completeCt2With ops.encaps2`; a `ct₂` chunk in
`ekSentCt1Received` extends the `ct₂` decoder and, on completion, derives the key with
`recvCt2With ops.completeKey`. Every other delivery is received by `recv`. -/
def recvWith (ops : Ops P)
    (st : PartyState P AuthState) (msg : Message P.Sym) :
    Except Error (RecvResult P AuthState) :=
  match st, msg with
  | .ekSentCt1Received core dec, ⟨e, .ct2 chunk⟩ =>
      if e = core.ep then
        let dec' := P.decCt2.addChunk dec chunk
        match P.decCt2.decodedPayload dec' with
        | some (c2, tag) =>
            match recvCt2With auth ops.completeKey core c2 tag with
            | some (next, key) =>
                .ok ⟨e - 1, some key, .noHeaderReceived next (P.decHdr.empty)⟩
            | none => .error .macVerifyFailed
        | none => .ok ⟨e - 1, none, .ekSentCt1Received core dec'⟩
      else recv P auth st msg
  | .ct1Sampled core _ dec, ⟨e, .ekCt1Ack chunk⟩ =>
      if e = core.ep then
        let dec' := P.decEk.addChunk dec chunk
        match P.decEk.decodedPayload dec' with
        | some vec =>
            match CtSender.recvEk P core vec with
            | some core' => .ok ⟨e - 1, none, completeCt2With auth ops.encaps2 core'⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨e - 1, none, .ct1Acknowledged core dec'⟩
      else recv P auth st msg
  | .ekReceivedCt1Sampled core _, ⟨e, .ct1Ack⟩ =>
      if e = core.ep then .ok ⟨e - 1, none, completeCt2With auth ops.encaps2 core⟩
      else recv P auth st msg
  | .ekReceivedCt1Sampled core _, ⟨e, .ekCt1Ack _⟩ =>
      if e = core.ep then .ok ⟨e - 1, none, completeCt2With auth ops.encaps2 core⟩
      else recv P auth st msg
  | .ct1Acknowledged core dec, ⟨e, .ek chunk⟩ =>
      if e = core.ep then
        let dec' := P.decEk.addChunk dec chunk
        match P.decEk.decodedPayload dec' with
        | some vec =>
            match CtSender.recvEk P core vec with
            | some core' => .ok ⟨e - 1, none, completeCt2With auth ops.encaps2 core'⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨e - 1, none, .ct1Acknowledged core dec'⟩
      else recv P auth st msg
  | .ct1Acknowledged core dec, ⟨e, .ekCt1Ack chunk⟩ =>
      if e = core.ep then
        let dec' := P.decEk.addChunk dec chunk
        match P.decEk.decodedPayload dec' with
        | some vec =>
            match CtSender.recvEk P core vec with
            | some core' => .ok ⟨e - 1, none, completeCt2With auth ops.encaps2 core'⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨e - 1, none, .ct1Acknowledged core dec'⟩
      else recv P auth st msg
  | _, _ => recv P auth st msg


/-- If the second stage of `ops` is that of `P`, `recvWith auth ops` and `recv P auth` agree on
every delivery other than a `ct₂` chunk of the current epoch in `ekSentCt1Received`. -/
theorem recvWith_eq_recv_of_real (ops : Ops P)
    (st : PartyState P AuthState) (msg : Message P.Sym)
    (h2 : ∀ t, ops.encaps2 t = P.det.encaps2Det)
    (h : ∀ core dec chunk, st = .ekSentCt1Received core dec → msg ≠ ⟨core.ep, .ct2 chunk⟩) :
    recvWith auth ops st msg = recv P auth st msg := by
  have hc : completeCt2With auth ops.encaps2 = completeCt2 P auth := by
    rw [show ops.encaps2 = fun _ => P.det.encaps2Det from funext h2, completeCt2With_det]
  obtain ⟨e, payload⟩ := msg
  cases st <;> cases payload <;> try rfl
  case ekSentCt1Received.ct2 core dec chunk =>
    simp only [recvWith]
    rw [ite_eq_right]
    exact fun he => h core dec chunk rfl (by rw [he])
  case ekReceivedCt1Sampled.ct1Ack core enc | ekReceivedCt1Sampled.ekCt1Ack core enc _ =>
    simp only [recvWith, hc]
    split_ifs with he
    · subst he
      simp only [recv, PartyState.epoch, lt_self_iff_false, ↓reduceIte]
    · rfl
  case ct1Sampled.ekCt1Ack core _ dec chunk | ct1Acknowledged.ek core dec chunk |
      ct1Acknowledged.ekCt1Ack core dec chunk =>
    simp only [recvWith, hc]
    split_ifs with he
    · subst he
      simp only [recv, PartyState.epoch, lt_self_iff_false, ↓reduceIte]
      generalize P.decEk.decodedPayload (P.decEk.addChunk dec chunk) = decoded
      cases decoded with
      | none => rfl
      | some vec =>
        dsimp only
        cases CtSender.recvEk P core vec <;> rfl
    · rfl

/-- `recvWith auth ops` on a `ct₂` chunk of the current epoch in `ekSentCt1Received`: extend the
`ct₂` decoder; on completion derive the key with `recvCt2With`. -/
theorem recvWith_ekSentCt1Received_ct2 (ops : Ops P)
    (core : EkSender.EkSentCt1Received P AuthState)
    (dec : P.decCt2.D) (chunk : ℕ × P.Sym) :
    recvWith auth ops (.ekSentCt1Received core dec) ⟨core.ep, .ct2 chunk⟩ =
      match P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) with
      | some (c2, tag) =>
          match recvCt2With auth ops.completeKey core c2 tag with
          | some (next, key) =>
              .ok ⟨core.ep - 1, some key, .noHeaderReceived next (P.decHdr.empty)⟩
          | none => .error .macVerifyFailed
      | none => .ok ⟨core.ep - 1, none, .ekSentCt1Received core (P.decCt2.addChunk dec chunk)⟩ := by
  simp [recvWith]

/-- `recv` on a `ct₂` chunk of the current epoch in `ekSentCt1Received`: extend the `ct₂`
decoder; on completion decapsulate with `EkSender.recvCt2`. -/
private theorem recv_ekSentCt1Received_ct2 (core : EkSender.EkSentCt1Received P AuthState)
    (dec : P.decCt2.D) (chunk : ℕ × P.Sym) :
    recv P auth (.ekSentCt1Received core dec) ⟨core.ep, .ct2 chunk⟩ =
      match P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) with
      | some (c2, tag) =>
          match EkSender.recvCt2 P auth core c2 tag with
          | some (next, key) =>
              .ok ⟨core.ep - 1, some key, .noHeaderReceived next (P.decHdr.empty)⟩
          | none => .error .macVerifyFailed
      | none => .ok ⟨core.ep - 1, none, .ekSentCt1Received core (P.decCt2.addChunk dec chunk)⟩ := by
  simp only [recv, PartyState.epoch, lt_self_iff_false, ↓reduceIte]
  generalize P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) = decoded
  cases decoded with
  | none => rfl
  | some ct =>
    obtain ⟨c2, tag⟩ := ct
    dsimp only
    cases EkSender.recvCt2 P auth core c2 tag <;> rfl

/-- If the second stage of `ops` is that of `P` and `completeKey` agrees with decapsulation
followed by `P.kdfOK` on the ciphertext reached by the delivery,
`recvWith auth ops st msg = recv P auth st msg`. -/
theorem recvWith_eq_recv_of_completeKey (ops : Ops P)
    (st : PartyState P AuthState) (msg : Message P.Sym)
    (h2 : ∀ t, ops.encaps2 t = P.det.encaps2Det)
    (h : ∀ core dec chunk c2 tag, st = .ekSentCt1Received core dec → msg = ⟨core.ep, .ct2 chunk⟩ →
      P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) = some (c2, tag) →
      ops.completeKey core.ep core.sk core.c1 c2 =
        (P.det.decapsDet core.sk (P.det.splitC.symm (core.c1, c2))).map
          (fun k => P.kdfOK k core.ep)) :
    recvWith auth ops st msg = recv P auth st msg := by
  by_cases hcell : ∃ core dec chunk, st = .ekSentCt1Received core dec ∧
      msg = ⟨core.ep, .ct2 chunk⟩
  · obtain ⟨core, dec, chunk, rfl, rfl⟩ := hcell
    rw [recvWith_ekSentCt1Received_ct2, recv_ekSentCt1Received_ct2]
    generalize hdec : P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) = decoded
    cases decoded with
    | none => rfl
    | some ct =>
      obtain ⟨c2, tag⟩ := ct
      dsimp only
      rw [recvCt2With_decaps auth core c2 tag _ (h core dec chunk c2 tag rfl rfl hdec)]
  · exact recvWith_eq_recv_of_real auth ops st msg h2
      (fun core dec chunk hst hmsg => hcell ⟨core, dec, chunk, hst, hmsg⟩)

/-- Adapt `recvWith` to SCKA; an error refuses delivery and a success forwards its report. -/
def recvSCKAWith (ops : Ops P) (st : PartyState P AuthState)
    (msg : Message P.Sym) : Option (Option (ℕ × P.EpochKey) × ℕ × PartyState P AuthState) :=
  match recvWith auth ops st msg with
  | .error _ => none
  | .ok r => some (r.outputKey, r.receivingEpoch, r.state)

/-- If `recvWith auth ops` and `recv` agree on `st` and `msg`, so do the SCKA receives. -/
theorem recvSCKAWith_eq_recvSCKA (ops : Ops P)
    (st : PartyState P AuthState) (msg : Message P.Sym)
    (h : recvWith auth ops st msg = recv P auth st msg) :
    recvSCKAWith auth ops st msg = recvSCKA P auth st msg := by
  unfold recvSCKAWith recvSCKA
  rw [h]
  cases recv P auth st msg <;> rfl

/-- The SCKA scheme with the transitions of `ops`; both parties use the same algorithms. -/
def schemeWith (ops : Ops P) (sampleInitKey : ProbComp InitKey) :
    SCKAScheme ProbComp InitKey (PartyState P AuthState) (PartyState P AuthState)
      P.EpochKey (Message P.Sym) (Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand) :=
  let sendSCKA (st : PartyState P AuthState) := do
    let r ← sendWith auth ops st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))
  let sendRleakSCKA (st : PartyState P AuthState) := do
    let (r, rand) ← sendRleakWith auth ops st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state, rand))
  { initKeyGen := sampleInitKey
    initA := fun ik => pure (initA P auth ik)
    initB := fun ik => pure (initB P auth ik)
    sendA := sendSCKA
    sendArleak := sendRleakSCKA
    recvA := recvSCKAWith auth ops
    sendB := sendSCKA
    sendBrleak := sendRleakSCKA
    recvB := recvSCKAWith auth ops }

variable (ops : Ops P) (sampleInitKey : ProbComp InitKey)

/-- Discarding the coins of a leaking send of `schemeWith auth ops sampleInitKey` gives its
ordinary send. -/
theorem schemeWith_sendArleak_forget (st : PartyState P AuthState) :
    (do
      let out ← (schemeWith auth ops sampleInitKey).sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
      (schemeWith auth ops sampleInitKey).sendA st := by
  simp only [schemeWith, sendWith, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  rfl

/-- A leaking send of `schemeWith` never refuses. -/
theorem schemeWith_sendArleak_neverFails (st : PartyState P AuthState) :
    none ∉ support ((schemeWith auth ops sampleInitKey).sendArleak st) := by
  simp [schemeWith]

end SPQR.Chunked

namespace SPQR

open Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (sampleInitKey : ProbComp InitKey)

/-! ### Sends of the scheme -/

section Sends

/-- Discarding the coins of a leaking send of `scheme P auth sampleInitKey` gives its ordinary
send. -/
theorem scheme_sendArleak_forget (st : PartyState P AuthState) :
    (do
      let out ← (scheme P auth sampleInitKey).sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
      (scheme P auth sampleInitKey).sendA st := by
  simp only [scheme, send_eq_map_sendRleak P auth st, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_def]
  rfl

/-- Every possible leaking send of `scheme P auth sampleInitKey` from `st` returns coins `rand` with
`(vuln P AuthState).rleak st rand = leakEpochs st`. -/
theorem scheme_sendArleak_exposure (st : PartyState P AuthState)
    (key : Option (ℕ × P.EpochKey)) (msg : Message P.Sym) (epoch : ℕ) (st' : PartyState P AuthState)
    (rand : Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand)
    (hout : some (key, msg, epoch, st', rand) ∈
      support ((scheme P auth sampleInitKey).sendArleak st)) :
    (vuln P AuthState).rleak st rand = leakEpochs st := by
  simp only [scheme, mem_support_bind_iff] at hout
  obtain ⟨⟨r, rand'⟩, hr, hout⟩ := hout
  simp only [mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at hout
  obtain ⟨-, -, -, -, rfl⟩ := hout
  rw [← Chunked.sendRleakWith_real] at hr
  exact Chunked.sendRleakWith_exposure auth (Chunked.Ops.real P) st (r, _) hr

end Sends

end SPQR
