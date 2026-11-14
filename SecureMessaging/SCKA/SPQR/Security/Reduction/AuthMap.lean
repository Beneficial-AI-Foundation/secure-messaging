/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Security.Ideal
public import SecureMessaging.SCKA.MLKEMBraid.Security.KeyHiding

/-!
# Authenticator maps

Every SPQR state carries an authenticator state, which the update of epoch `st.authEpoch`
consumes (`Security.Basic`). An *authenticator map* `π : ℕ → AuthState → AuthState` assigns to an
authenticator state `a` consumed by the update of epoch `t` the state `π t a`; `authMapSt π`
applies it to the authenticator state of a party state, and `authMapState π` to both party states
of a game state.

**Definition.** `AuthMap A₁ A₂ π` states that `π` maps the authenticator `A₁` to `A₂`: on mapped
states, the tags and verifications of `A₂` are those of `A₁`, and the update of epoch `t` maps to
the update of `A₂` on the mapped state.

**Results.** Assume `AuthMap A₁ A₂ π`.

- *Naturality of the transitions.* The SPQR transitions over `A₂` from a mapped state are those
  over `A₁` followed by the map, for every choice of operations: `sendRleakWith_authMap`,
  `recv_authMap`, `recvWith_authMap`.
- *Transport of the stopped games.* If `π t` is the identity for `t ≠ e`, the security oracles over
  `A₂` from `authMapState π s` and over `A₁` from `s`, with a challenge oracle commuting with the
  map, both stopped at the first exposure of `e`, accept equally often
  (`prEvent_stoppedRun_authMap`). A corruption answer differs only for a state whose
  authenticator state the update of `e` consumes, and that corruption exposes `e`.

**The authenticator of the hidden state.** Let `h` be operations on hidden states
(`Braid.HiddenAuth`, `MLKEMBraid.Security.KeyHiding`) and `0 < e`. The authenticator
`withHidden auth h e` keeps a representative `a` in place of the authenticator state entering `e`:
its update of `e - 1` keeps `a`, its header operations at `e` and its ciphertext operations at
`e - 1` are those of `h` on `a`, and its update of `e` is `h.next`. The map `hiddenMap e hide`,
which applies `hide` to the authenticator states consumed by the update of `e`, maps
`withHidden auth (Braid.hiddenAuth auth hide e u) e` to `authAt auth (e - 1) hide`, both with the
update of `e` keyed by `u` (`authMap_withHidden`).
-/

@[expose] public section

open OracleSpec OracleComp ErasureCodePayload.Streaming

namespace SPQR

open Chunked
open Braid (HiddenAuth hiddenAuth hiddenState)

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}

/-! ### Mapping authenticator states -/

/-- The party state with its authenticator state `a` replaced by `f a`. -/
def Chunked.PartyState.mapAuth (f : AuthState → AuthState) :
    PartyState P AuthState → PartyState P AuthState
  | .keysUnsampled core => .keysUnsampled { core with authSt := f core.authSt }
  | .keysSampled core enc => .keysSampled { core with authSt := f core.authSt } enc
  | .headerSent core enc dec => .headerSent { core with authSt := f core.authSt } enc dec
  | .ct1Received core enc => .ct1Received { core with authSt := f core.authSt } enc
  | .ekSentCt1Received core dec => .ekSentCt1Received { core with authSt := f core.authSt } dec
  | .noHeaderReceived core dec => .noHeaderReceived { core with authSt := f core.authSt } dec
  | .headerReceived core dec => .headerReceived { core with authSt := f core.authSt } dec
  | .ct1Sampled core enc dec => .ct1Sampled { core with authSt := f core.authSt } enc dec
  | .ekReceivedCt1Sampled core enc =>
      .ekReceivedCt1Sampled { core with authSt := f core.authSt } enc
  | .ct1Acknowledged core dec => .ct1Acknowledged { core with authSt := f core.authSt } dec
  | .ct2Sampled core enc => .ct2Sampled { core with authSt := f core.authSt } enc

/-- The party state with its authenticator state `a` replaced by `π st.authEpoch a`. -/
def authMapSt (π : ℕ → AuthState → AuthState) (st : PartyState P AuthState) :
    PartyState P AuthState :=
  st.mapAuth (π st.authEpoch)

/-- A send result with its state mapped by `authMapSt π`. -/
def authMapSendRes (π : ℕ → AuthState → AuthState) (r : SendResult P AuthState) :
    SendResult P AuthState :=
  ⟨r.msg, r.sendingEpoch, r.outputKey, authMapSt π r.state⟩

/-- A receive result with its state mapped by `authMapSt π`. -/
def authMapRecvRes (π : ℕ → AuthState → AuthState) (r : RecvResult P AuthState) :
    RecvResult P AuthState :=
  ⟨r.receivingEpoch, r.outputKey, authMapSt π r.state⟩

/-- The game state with both party states mapped by `authMapSt π`. -/
@[simps -fullyApplied]
def authMapState (π : ℕ → AuthState → AuthState) (s : GameState P AuthState) :
    GameState P AuthState :=
  { s with stA := authMapSt π s.stA, stB := authMapSt π s.stB }

variable (π : ℕ → AuthState → AuthState)

/-- Mapping the authenticator state keeps the epoch. -/
@[simp] theorem PartyState.mapAuth_epoch (f : AuthState → AuthState) (st : PartyState P AuthState) :
    (st.mapAuth f).epoch = st.epoch := by
  cases st <;> rfl

/-- Mapping the authenticator state keeps whether the state holds a secret. -/
@[simp] theorem PartyState.mapAuth_holdsSecret (f : AuthState → AuthState)
    (st : PartyState P AuthState) : (st.mapAuth f).holdsSecret = st.holdsSecret := by
  cases st <;> rfl

/-- Mapping the authenticator state keeps whether it includes the key of the current epoch. -/
@[simp] theorem PartyState.mapAuth_authUpdated (f : AuthState → AuthState)
    (st : PartyState P AuthState) : (st.mapAuth f).authUpdated = st.authUpdated := by
  cases st <;> rfl

/-- Mapping the authenticator state keeps the epoch whose update consumes it. -/
@[simp] theorem PartyState.mapAuth_authEpoch (f : AuthState → AuthState)
    (st : PartyState P AuthState) : (st.mapAuth f).authEpoch = st.authEpoch := by
  simp [PartyState.authEpoch]

/-- Mapping the authenticator state by the identity changes nothing. -/
@[simp] theorem PartyState.mapAuth_id (st : PartyState P AuthState) : st.mapAuth id = st := by
  cases st <;> rfl

/-- `authMapSt π` keeps the epoch. -/
@[simp] theorem authMapSt_epoch (st : PartyState P AuthState) :
    (authMapSt π st).epoch = st.epoch := PartyState.mapAuth_epoch _ st

/-- `authMapSt π` keeps the epoch whose update consumes the authenticator state. -/
@[simp] theorem authMapSt_authEpoch (st : PartyState P AuthState) :
    (authMapSt π st).authEpoch = st.authEpoch := PartyState.mapAuth_authEpoch _ st

/-- `authMapSt π` keeps whether the state holds a secret. -/
@[simp] theorem authMapSt_holdsSecret (st : PartyState P AuthState) :
    (authMapSt π st).holdsSecret = st.holdsSecret := PartyState.mapAuth_holdsSecret _ st

/-- A state whose authenticator state is consumed by the update of an epoch where `π` is the
identity is unchanged by `authMapSt π`. -/
theorem authMapSt_eq_self {st : PartyState P AuthState} (h : π st.authEpoch = id) :
    authMapSt π st = st := by
  rw [authMapSt, h, PartyState.mapAuth_id]

/-- Corrupting a state exposes the same epochs before and after `authMapSt π`. -/
@[simp] theorem vuln_corrupt_authMapSt (st : PartyState P AuthState) :
    (vuln P AuthState).corrupt (authMapSt π st) = (vuln P AuthState).corrupt st := by
  simp [vuln]

/-- A leaking send exposes the same epochs before and after `authMapSt π`. -/
@[simp] theorem vuln_rleak_authMapSt (st : PartyState P AuthState)
    (rand : Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand) :
    (vuln P AuthState).rleak (authMapSt π st) rand = (vuln P AuthState).rleak st rand := by
  cases rand <;> simp [vuln]

/-! ### Authenticator maps -/

/-- The authenticator map `π` maps the authenticator `A₁` to `A₂`: for every authenticator state
`a`, epoch `t`, header `h`, ciphertext `c`, tag and key `ik`, the header tags and verifications of
`A₂` at `t` on `π t a`, and its ciphertext tags and verifications at `t` on `π (t + 1) a`, are
those of `A₁` on `a`, and `π (t + 1)` maps `A₁.update a t ik` to `A₂.update (π t a) t ik`. -/
structure AuthMap (A₁ A₂ : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (π : ℕ → AuthState → AuthState) : Prop where
  /-- Header tags at `t` agree on states consumed by the update of `t`. -/
  macHeader : ∀ a t h, A₂.macHeader (π t a) t h = A₁.macHeader a t h
  /-- Header verifications at `t` agree on states consumed by the update of `t`. -/
  verifyHeader : ∀ a t h tag, A₂.verifyHeader (π t a) t h tag = A₁.verifyHeader a t h tag
  /-- The update of `t` commutes with the map. -/
  update : ∀ a t ik, π (t + 1) (A₁.update a t ik) = A₂.update (π t a) t ik
  /-- Ciphertext tags at `t` agree on states consumed by the update of `t + 1`. -/
  macCiphertext : ∀ a t c, A₂.macCiphertext (π (t + 1) a) t c = A₁.macCiphertext a t c
  /-- Ciphertext verifications at `t` agree on states consumed by the update of `t + 1`. -/
  verifyCiphertext : ∀ a t c tag,
    A₂.verifyCiphertext (π (t + 1) a) t c tag = A₁.verifyCiphertext a t c tag

/-! ### Naturality of the transitions -/

section Transitions

variable {A₁ A₂ : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac} {π}

/-- The leaking send over `A₂` from a mapped state is the leaking send over `A₁` followed by the
map, with the coins unchanged. -/
theorem sendRleakWith_authMap (hmap : AuthMap A₁ A₂ π) (ops : Ops P)
    (st : PartyState P AuthState) :
    sendRleakWith A₂ ops (authMapSt π st) =
      Prod.map (authMapSendRes π) id <$> sendRleakWith A₁ ops st := by
  cases st
  case keysUnsampled core =>
    simp only [sendRleakWith, authMapSt, PartyState.mapAuth, PartyState.authEpoch,
      PartyState.authUpdated, PartyState.epoch, Bool.false_eq_true, ↓reduceIte,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, hmap.macHeader]
    refine bind_congr fun x => ?_
    simp [authMapSendRes, authMapSt, PartyState.mapAuth, PartyState.authEpoch,
      PartyState.authUpdated, PartyState.epoch]
  case headerReceived core dec =>
    simp only [sendRleakWith, authMapSt, PartyState.mapAuth, PartyState.authEpoch,
      PartyState.authUpdated, PartyState.epoch, Bool.false_eq_true, ↓reduceIte,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, ← hmap.update]
    refine bind_congr fun x => ?_
    simp [authMapSendRes, authMapSt, PartyState.mapAuth, PartyState.authEpoch,
      PartyState.authUpdated, PartyState.epoch]
  all_goals
    simp only [sendRleakWith, SPQR.send, Chunked.send, authMapSt,
      PartyState.mapAuth, PartyState.authEpoch, PartyState.authUpdated, PartyState.epoch,
      map_pure, Prod.map, authMapSendRes, id]
    try rfl

/-- The ordinary send over `A₂` from a mapped state is the send over `A₁` followed by the map. -/
theorem sendWith_authMap (hmap : AuthMap A₁ A₂ π) (ops : Ops P)
    (st : PartyState P AuthState) :
    sendWith A₂ ops (authMapSt π st) = authMapSendRes π <$> sendWith A₁ ops st := by
  simp [sendWith, sendRleakWith_authMap hmap, Functor.map_map]

/-- The header verification over `A₂` from a state whose authenticator state is mapped by `π`
at its epoch is the verification over `A₁` followed by the map. -/
theorem recvHeader_authMap (hmap : AuthMap A₁ A₂ π) (core : CtSender.NoHeaderReceived AuthState)
    (hdr : P.det.PKheader) (tag : P.Mac) :
    CtSender.recvHeader P A₂ { core with authSt := π core.ep core.authSt } hdr tag =
      (CtSender.recvHeader P A₁ core hdr tag).map
        (fun c => { c with authSt := π c.ep c.authSt }) := by
  simp only [CtSender.recvHeader, hmap.verifyHeader]
  split_ifs <;> rfl

/-- The decapsulating receive of `ct₂` over `A₂` from a mapped generator state is the receive over
`A₁` followed by the map at the next epoch. -/
theorem recvCt2_authMap (hmap : AuthMap A₁ A₂ π) (core : EkSender.EkSentCt1Received P AuthState)
    (c2 : P.det.C₂) (tag : P.Mac) :
    EkSender.recvCt2 P A₂ { core with authSt := π core.ep core.authSt } c2 tag =
      (EkSender.recvCt2 P A₁ core c2 tag).map
        (fun r => ({ r.1 with authSt := π r.1.ep r.1.authSt }, r.2)) := by
  simp only [EkSender.recvCt2]
  cases P.decaps core.sk core.c1 c2 with
  | none => rfl
  | some k =>
    simp only [← hmap.update, hmap.verifyCiphertext]
    split_ifs <;> rfl

/-- `recvCt2With` over `A₂` from a mapped generator state is `recvCt2With` over `A₁` followed by
the map at the next epoch. -/
theorem recvCt2With_authMap (hmap : AuthMap A₁ A₂ π)
    (completeKey : ℕ → P.SK → P.det.C₁ → P.det.C₂ → Option P.EpochKey)
    (core : EkSender.EkSentCt1Received P AuthState) (c2 : P.det.C₂) (tag : P.Mac) :
    recvCt2With A₂ completeKey { core with authSt := π core.ep core.authSt } c2 tag =
      (recvCt2With A₁ completeKey core c2 tag).map
        (fun r => ({ r.1 with authSt := π r.1.ep r.1.authSt }, r.2)) := by
  simp only [recvCt2With]
  cases completeKey core.ep core.sk core.c1 c2 with
  | none => rfl
  | some ik =>
    simp only [← hmap.update, hmap.verifyCiphertext]
    split_ifs <;> rfl

/-- The second stage over `A₂` from a mapped encapsulator state is the second stage over `A₁`
followed by the map. -/
theorem completeCt2_authMap (hmap : AuthMap A₁ A₂ π)
    (core : CtSender.Ct1SentEkReceived P AuthState) :
    completeCt2 P A₂ { core with authSt := π (core.ep + 1) core.authSt } =
      authMapSt π (completeCt2 P A₁ core) := by
  simp [completeCt2, authMapSt, PartyState.mapAuth, PartyState.authEpoch,
    PartyState.authUpdated, PartyState.epoch, hmap.macCiphertext]

/-- `completeCt2With` over `A₂` from a mapped encapsulator state is `completeCt2With` over `A₁`
followed by the map. -/
theorem completeCt2With_authMap (hmap : AuthMap A₁ A₂ π)
    (encaps2 : ℕ → P.det.St → P.det.PKheader → P.det.PKvector → P.det.C₂)
    (core : CtSender.Ct1SentEkReceived P AuthState) :
    completeCt2With A₂ encaps2 { core with authSt := π (core.ep + 1) core.authSt } =
      authMapSt π (completeCt2With A₁ encaps2 core) := by
  simp [completeCt2With, authMapSt, PartyState.mapAuth, PartyState.authEpoch,
    PartyState.authUpdated, PartyState.epoch, hmap.macCiphertext]


set_option hygiene false in
/-- Close a receive cell by simplification with the context. -/
local macro "amap_close" : tactic => `(tactic|
  simp [Except.map, authMapRecvRes, authMapSt, PartyState.mapAuth, PartyState.authEpoch,
    PartyState.authUpdated, PartyState.epoch, EkSender.sendEk, EkSender.recvCt1,
    CtSender.recvNextEpoch, *])

set_option hygiene false in
/-- Unfold `recv` and the map on a party state given by its constructor. -/
local macro "amap_unfold" : tactic => `(tactic|
  simp only [recv, authMapSt, PartyState.mapAuth, PartyState.authEpoch, PartyState.authUpdated,
    PartyState.epoch, Bool.false_eq_true, ↓reduceIte, Message.epoch, Message.payload])

set_option hygiene false in
/-- Unfold `recvWith` and the map on a party state given by its constructor. -/
local macro "amap_with" : tactic => `(tactic|
  simp only [recvWith, authMapSt, PartyState.mapAuth, PartyState.authEpoch, PartyState.authUpdated,
    PartyState.epoch, Bool.false_eq_true, ↓reduceIte])

/-- The receive in `keysUnsampled` commutes with the authenticator map. -/
private theorem recv_authMap_keysUnsampled (core : EkSender.KeysUnsampled AuthState)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π (.keysUnsampled core)) msg =
      Except.map (authMapRecvRes π) (recv P A₁ (.keysUnsampled core) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  all_goals (amap_unfold; split_ifs <;> amap_close)

/-- The receive in `keysSampled` commutes with the authenticator map. -/
private theorem recv_authMap_keysSampled (core : EkSender.HeaderSent P AuthState)
    (enc : EncoderState (P.det.PKheader × P.Mac) P.Sym)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π (.keysSampled core enc)) msg =
      Except.map (authMapRecvRes π) (recv P A₁ (.keysSampled core enc) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  all_goals (amap_unfold; split_ifs <;> amap_close)

/-- The receive in `headerSent` commutes with the authenticator map. -/
private theorem recv_authMap_headerSent (core : EkSender.EkSent P AuthState)
    (enc : EncoderState P.det.PKvector P.Sym) (dec : P.decCt1.D)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π (.headerSent core enc dec)) msg =
      Except.map (authMapRecvRes π) (recv P A₁ (.headerSent core enc dec) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  case ct1 chunk =>
    amap_unfold
    split_ifs
    · amap_close
    · amap_close
    · cases P.decCt1.decodedPayload (P.decCt1.addChunk dec chunk) <;> amap_close
  all_goals (amap_unfold; split_ifs <;> amap_close)

/-- The receive in `ct1Received` commutes with the authenticator map. -/
private theorem recv_authMap_ct1Received (core : EkSender.EkSentCt1Received P AuthState)
    (enc : EncoderState P.det.PKvector P.Sym)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π (.ct1Received core enc)) msg =
      Except.map (authMapRecvRes π) (recv P A₁ (.ct1Received core enc) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  all_goals (amap_unfold; split_ifs <;> amap_close)

/-- The receive in `ekSentCt1Received` commutes with the authenticator map. -/
private theorem recv_authMap_ekSentCt1Received (hmap : AuthMap A₁ A₂ π)
    (core : EkSender.EkSentCt1Received P AuthState)
    (dec : P.decCt2.D)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π (.ekSentCt1Received core dec)) msg =
      Except.map (authMapRecvRes π) (recv P A₁ (.ekSentCt1Received core dec) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  case ct2 chunk =>
    amap_unfold
    split_ifs
    · amap_close
    · amap_close
    · cases P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) with
      | none => amap_close
      | some ct =>
        obtain ⟨c2, tag⟩ := ct
        simp only [recvCt2_authMap hmap]
        cases EkSender.recvCt2 P A₁ core c2 tag <;> amap_close
  all_goals (amap_unfold; split_ifs <;> amap_close)

/-- The receive in `noHeaderReceived` commutes with the authenticator map. -/
private theorem recv_authMap_noHeaderReceived (hmap : AuthMap A₁ A₂ π)
    (core : CtSender.NoHeaderReceived AuthState)
    (dec : P.decHdr.D)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π (.noHeaderReceived core dec)) msg =
      Except.map (authMapRecvRes π) (recv P A₁ (.noHeaderReceived core dec) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  case hdr chunk =>
    amap_unfold
    split_ifs
    · amap_close
    · amap_close
    · cases P.decHdr.decodedPayload (P.decHdr.addChunk dec chunk) with
      | none => amap_close
      | some ht =>
        obtain ⟨hdr, tag⟩ := ht
        simp only [recvHeader_authMap hmap]
        cases CtSender.recvHeader P A₁ core hdr tag <;> amap_close
  all_goals (amap_unfold; split_ifs <;> amap_close)

/-- The receive in `headerReceived` commutes with the authenticator map. -/
private theorem recv_authMap_headerReceived (core : CtSender.HeaderReceived P AuthState)
    (dec : P.decEk.D)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π (.headerReceived core dec)) msg =
      Except.map (authMapRecvRes π) (recv P A₁ (.headerReceived core dec) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  all_goals (amap_unfold; split_ifs <;> amap_close)

/-- The receive in `ct1Sampled` commutes with the authenticator map. -/
private theorem recv_authMap_ct1Sampled (hmap : AuthMap A₁ A₂ π)
    (core : CtSender.Ct1Sent P AuthState)
    (enc : EncoderState P.det.C₁ P.Sym) (dec : P.decEk.D)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π (.ct1Sampled core enc dec)) msg =
      Except.map (authMapRecvRes π) (recv P A₁ (.ct1Sampled core enc dec) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  case ek chunk =>
    amap_unfold
    split_ifs
    · amap_close
    · amap_close
    · cases P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => amap_close
      | some vec =>
        simp only [CtSender.recvEk, Parameters.ekMatchesHeader]
        split_ifs <;> amap_close
  case ekCt1Ack chunk =>
    amap_unfold
    split_ifs
    · amap_close
    · amap_close
    · cases P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => amap_close
      | some vec =>
        simp only [CtSender.recvEk, Parameters.ekMatchesHeader]
        split_ifs <;>
          simp [Except.map, authMapRecvRes, completeCt2, authMapSt, PartyState.mapAuth,
            PartyState.authEpoch, PartyState.authUpdated, PartyState.epoch, hmap.macCiphertext, *]
  all_goals (amap_unfold; split_ifs <;> amap_close)

/-- The receive in `ekReceivedCt1Sampled` commutes with the authenticator map. -/
private theorem recv_authMap_ekReceivedCt1Sampled (hmap : AuthMap A₁ A₂ π)
    (core : CtSender.Ct1SentEkReceived P AuthState)
    (enc : EncoderState P.det.C₁ P.Sym)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π (.ekReceivedCt1Sampled core enc)) msg =
      Except.map (authMapRecvRes π) (recv P A₁ (.ekReceivedCt1Sampled core enc) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  case ct1Ack =>
    amap_unfold
    split_ifs
    · amap_close
    · amap_close
    · simp [Except.map, authMapRecvRes, completeCt2_authMap hmap, *]
  case ekCt1Ack chunk =>
    amap_unfold
    split_ifs
    · amap_close
    · amap_close
    · simp [Except.map, authMapRecvRes, completeCt2_authMap hmap, *]
  all_goals (amap_unfold; split_ifs <;> amap_close)

/-- The receive in `ct1Acknowledged` commutes with the authenticator map. -/
private theorem recv_authMap_ct1Acknowledged (hmap : AuthMap A₁ A₂ π)
    (core : CtSender.Ct1Sent P AuthState)
    (dec : P.decEk.D)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π (.ct1Acknowledged core dec)) msg =
      Except.map (authMapRecvRes π) (recv P A₁ (.ct1Acknowledged core dec) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  case ek chunk =>
    amap_unfold
    split_ifs
    · amap_close
    · amap_close
    · cases P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => amap_close
      | some vec =>
        simp only [CtSender.recvEk, Parameters.ekMatchesHeader]
        split_ifs <;>
          simp [Except.map, authMapRecvRes, completeCt2, authMapSt, PartyState.mapAuth,
            PartyState.authEpoch, PartyState.authUpdated, PartyState.epoch, hmap.macCiphertext, *]
  case ekCt1Ack chunk =>
    amap_unfold
    split_ifs
    · amap_close
    · amap_close
    · cases P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => amap_close
      | some vec =>
        simp only [CtSender.recvEk, Parameters.ekMatchesHeader]
        split_ifs <;>
          simp [Except.map, authMapRecvRes, completeCt2, authMapSt, PartyState.mapAuth,
            PartyState.authEpoch, PartyState.authUpdated, PartyState.epoch, hmap.macCiphertext, *]
  all_goals (amap_unfold; split_ifs <;> amap_close)

/-- The receive in `ct2Sampled` commutes with the authenticator map. -/
private theorem recv_authMap_ct2Sampled (core : CtSender.Ct2Sent AuthState)
    (enc : EncoderState (P.det.C₂ × P.Mac) P.Sym)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π (.ct2Sampled core enc)) msg =
      Except.map (authMapRecvRes π) (recv P A₁ (.ct2Sampled core enc) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  all_goals
    amap_unfold
    simp only [CtSender.recvNextEpoch]
    split_ifs <;> amap_close

/-- The receive over `A₂` from a mapped state is the receive over `A₁` followed by the map. -/
theorem recv_authMap (hmap : AuthMap A₁ A₂ π) (st : PartyState P AuthState)
    (msg : Message P.Sym) :
    recv P A₂ (authMapSt π st) msg = Except.map (authMapRecvRes π) (recv P A₁ st msg) := by
  cases st
  · exact recv_authMap_keysUnsampled _ msg
  · exact recv_authMap_keysSampled _ _ msg
  · exact recv_authMap_headerSent _ _ _ msg
  · exact recv_authMap_ct1Received _ _ msg
  · exact recv_authMap_ekSentCt1Received hmap _ _ msg
  · exact recv_authMap_noHeaderReceived hmap _ _ msg
  · exact recv_authMap_headerReceived _ _ msg
  · exact recv_authMap_ct1Sampled hmap _ _ _ msg
  · exact recv_authMap_ekReceivedCt1Sampled hmap _ _ msg
  · exact recv_authMap_ct1Acknowledged hmap _ _ msg
  · exact recv_authMap_ct2Sampled _ _ msg

/-- `recvWith` in `ekSentCt1Received` commutes with the authenticator map. -/
private theorem recvWith_authMap_ekSentCt1Received (hmap : AuthMap A₁ A₂ π)
    (ops : Ops P) (core : EkSender.EkSentCt1Received P AuthState)
    (dec : P.decCt2.D) (msg : Message P.Sym) :
    recvWith A₂ ops (authMapSt π (.ekSentCt1Received core dec)) msg =
      Except.map (authMapRecvRes π) (recvWith A₁ ops (.ekSentCt1Received core dec) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  case ct2 chunk =>
    amap_with
    split_ifs with hme
    · subst hme
      cases P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) with
      | none => amap_close
      | some ct =>
        obtain ⟨c2, tag⟩ := ct
        simp only [recvCt2With_authMap hmap]
        cases recvCt2With A₁ ops.completeKey core c2 tag <;> amap_close
    · exact recv_authMap_ekSentCt1Received hmap core dec _
  all_goals exact recv_authMap_ekSentCt1Received hmap core dec _

/-- `recvWith` in `ct1Sampled` commutes with the authenticator map. -/
private theorem recvWith_authMap_ct1Sampled (hmap : AuthMap A₁ A₂ π)
    (ops : Ops P) (core : CtSender.Ct1Sent P AuthState)
    (enc : EncoderState P.det.C₁ P.Sym) (dec : P.decEk.D)
    (msg : Message P.Sym) :
    recvWith A₂ ops (authMapSt π (.ct1Sampled core enc dec)) msg =
      Except.map (authMapRecvRes π) (recvWith A₁ ops (.ct1Sampled core enc dec) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  case ekCt1Ack chunk =>
    amap_with
    split_ifs with hme
    · subst hme
      cases P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => amap_close
      | some vec =>
        simp only [CtSender.recvEk, Parameters.ekMatchesHeader]
        split_ifs <;>
          simp [Except.map, authMapRecvRes, completeCt2With, authMapSt, PartyState.mapAuth,
            PartyState.authEpoch, PartyState.authUpdated, PartyState.epoch, hmap.macCiphertext, *]
    · exact recv_authMap_ct1Sampled hmap core enc dec _
  all_goals exact recv_authMap_ct1Sampled hmap core enc dec _

/-- `recvWith` in `ekReceivedCt1Sampled` commutes with the authenticator map. -/
private theorem recvWith_authMap_ekReceivedCt1Sampled (hmap : AuthMap A₁ A₂ π)
    (ops : Ops P) (core : CtSender.Ct1SentEkReceived P AuthState)
    (enc : EncoderState P.det.C₁ P.Sym) (msg : Message P.Sym) :
    recvWith A₂ ops (authMapSt π (.ekReceivedCt1Sampled core enc)) msg =
      Except.map (authMapRecvRes π) (recvWith A₁ ops (.ekReceivedCt1Sampled core enc) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  case ct1Ack =>
    amap_with
    split_ifs with hme
    · simp [Except.map, authMapRecvRes, completeCt2With_authMap hmap]
    · exact recv_authMap_ekReceivedCt1Sampled hmap core enc _
  case ekCt1Ack chunk =>
    amap_with
    split_ifs with hme
    · simp [Except.map, authMapRecvRes, completeCt2With_authMap hmap]
    · exact recv_authMap_ekReceivedCt1Sampled hmap core enc _
  all_goals exact recv_authMap_ekReceivedCt1Sampled hmap core enc _

/-- `recvWith` in `ct1Acknowledged` commutes with the authenticator map. -/
private theorem recvWith_authMap_ct1Acknowledged (hmap : AuthMap A₁ A₂ π)
    (ops : Ops P) (core : CtSender.Ct1Sent P AuthState)
    (dec : P.decEk.D) (msg : Message P.Sym) :
    recvWith A₂ ops (authMapSt π (.ct1Acknowledged core dec)) msg =
      Except.map (authMapRecvRes π) (recvWith A₁ ops (.ct1Acknowledged core dec) msg) := by
  obtain ⟨me, payload⟩ := msg
  cases payload
  case ek chunk =>
    amap_with
    split_ifs with hme
    · subst hme
      cases P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => amap_close
      | some vec =>
        simp only [CtSender.recvEk, Parameters.ekMatchesHeader]
        split_ifs <;>
          simp [Except.map, authMapRecvRes, completeCt2With, authMapSt, PartyState.mapAuth,
            PartyState.authEpoch, PartyState.authUpdated, PartyState.epoch, hmap.macCiphertext, *]
    · exact recv_authMap_ct1Acknowledged hmap core dec _
  case ekCt1Ack chunk =>
    amap_with
    split_ifs with hme
    · subst hme
      cases P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => amap_close
      | some vec =>
        simp only [CtSender.recvEk, Parameters.ekMatchesHeader]
        split_ifs <;>
          simp [Except.map, authMapRecvRes, completeCt2With, authMapSt, PartyState.mapAuth,
            PartyState.authEpoch, PartyState.authUpdated, PartyState.epoch, hmap.macCiphertext, *]
    · exact recv_authMap_ct1Acknowledged hmap core dec _
  all_goals exact recv_authMap_ct1Acknowledged hmap core dec _

/-- The receive `recvWith` over `A₂` from a mapped state is the receive over `A₁` followed by the
map, for every choice of operations. -/
theorem recvWith_authMap (hmap : AuthMap A₁ A₂ π) (ops : Ops P)
    (st : PartyState P AuthState) (msg : Message P.Sym) :
    recvWith A₂ ops (authMapSt π st) msg =
      Except.map (authMapRecvRes π) (recvWith A₁ ops st msg) := by
  cases st
  case ekSentCt1Received core dec => exact recvWith_authMap_ekSentCt1Received hmap ops core dec msg
  case ct1Sampled core enc dec => exact recvWith_authMap_ct1Sampled hmap ops core enc dec msg
  case ekReceivedCt1Sampled core enc =>
    exact recvWith_authMap_ekReceivedCt1Sampled hmap ops core enc msg
  case ct1Acknowledged core dec => exact recvWith_authMap_ct1Acknowledged hmap ops core dec msg
  all_goals exact recv_authMap hmap _ msg

end Transitions


section Transport

variable {A₁ A₂ : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac} {π}

/-! ### Transport of the stopped games -/

section Updates

variable [DecidableEq P.EpochKey]

/-- A's send update commutes with the authenticator map. -/
theorem sendAUpdate_authMapState (s : GameState P AuthState) (keyOpt : Option (ℕ × P.EpochKey))
    (ρ : Message P.Sym) (tsnd : ℕ) (stA' : PartyState P AuthState) :
    SCKAScheme.sendAUpdate (authMapState π s) keyOpt ρ tsnd (authMapSt π stA') =
      authMapState π (SCKAScheme.sendAUpdate s keyOpt ρ tsnd stA') := by
  rcases keyOpt with _ | ⟨tI, key⟩ <;> rfl

/-- B's send update commutes with the authenticator map. -/
theorem sendBUpdate_authMapState (s : GameState P AuthState) (keyOpt : Option (ℕ × P.EpochKey))
    (ρ : Message P.Sym) (tsnd : ℕ) (stB' : PartyState P AuthState) :
    SCKAScheme.sendBUpdate (authMapState π s) keyOpt ρ tsnd (authMapSt π stB') =
      authMapState π (SCKAScheme.sendBUpdate s keyOpt ρ tsnd stB') := by
  rcases keyOpt with _ | ⟨tI, key⟩ <;> rfl

/-- A's receive update commutes with the authenticator map. -/
theorem recvAUpdate_authMapState (s : GameState P AuthState) (tsnd : ℕ)
    (keyOpt : Option (ℕ × P.EpochKey)) (trcv : ℕ) (stA' : PartyState P AuthState) :
    SCKAScheme.recvAUpdate (authMapState π s) tsnd keyOpt trcv (authMapSt π stA') =
      authMapState π (SCKAScheme.recvAUpdate s tsnd keyOpt trcv stA') := by
  rcases keyOpt with _ | ⟨tI, key⟩ <;> rfl

/-- B's receive update commutes with the authenticator map. -/
theorem recvBUpdate_authMapState (s : GameState P AuthState) (tsnd : ℕ)
    (keyOpt : Option (ℕ × P.EpochKey)) (trcv : ℕ) (stB' : PartyState P AuthState) :
    SCKAScheme.recvBUpdate (authMapState π s) tsnd keyOpt trcv (authMapSt π stB') =
      authMapState π (SCKAScheme.recvBUpdate s tsnd keyOpt trcv stB') := by
  rcases keyOpt with _ | ⟨tI, key⟩ <;> rfl

end Updates

section Oracles

variable [DecidableEq P.EpochKey]
  (ops : Ops P) (sampleInitKey : ProbComp InitKey)

/-- A's send query over `A₂` from a mapped game state is the query over `A₁` followed by the
map. -/
theorem oracleSendA_authMap (hmap : AuthMap A₁ A₂ π) (s : GameState P AuthState) :
    (SCKAScheme.oracleSendA (schemeWith A₂ (idealOps ops (authMapState π s)) sampleInitKey)
        ()).run (authMapState π s) =
      Prod.map id (authMapState π) <$>
        (SCKAScheme.oracleSendA (schemeWith A₁ (idealOps ops s) sampleInitKey) ()).run s := by
  rw [SCKAScheme.oracleSendA_run_eq, SCKAScheme.oracleSendA_run_eq]
  simp only [schemeWith, sendWith_idealOps, authMapState_stA, sendWith_authMap hmap,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun r => ?_
  simp [authMapSendRes, sendAUpdate_authMapState]

/-- B version of `oracleSendA_authMap`. -/
theorem oracleSendB_authMap (hmap : AuthMap A₁ A₂ π) (s : GameState P AuthState) :
    (SCKAScheme.oracleSendB (schemeWith A₂ (idealOps ops (authMapState π s)) sampleInitKey)
        ()).run (authMapState π s) =
      Prod.map id (authMapState π) <$>
        (SCKAScheme.oracleSendB (schemeWith A₁ (idealOps ops s) sampleInitKey) ()).run s := by
  rw [SCKAScheme.oracleSendB_run_eq, SCKAScheme.oracleSendB_run_eq]
  simp only [schemeWith, sendWith_idealOps, authMapState_stB, sendWith_authMap hmap,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun r => ?_
  simp [authMapSendRes, sendBUpdate_authMapState]

/-- A's receive query over `A₂` from a mapped game state is the query over `A₁` followed by the
map. -/
theorem oracleRecvA_authMap (hmap : AuthMap A₁ A₂ π) (s : GameState P AuthState) (n : ℕ) :
    (SCKAScheme.oracleRecvA (schemeWith A₂ (idealOps ops (authMapState π s)) sampleInitKey)
        n).run (authMapState π s) =
      Prod.map id (authMapState π) <$>
        (SCKAScheme.oracleRecvA (schemeWith A₁ (idealOps ops s) sampleInitKey) n).run s := by
  have hops : idealOps ops (authMapState π s) = idealOps ops s := rfl
  cases hm : s.msgB n with
  | none =>
    rw [SCKAScheme.oracleRecvA_run_eq_of_none _ _ hm,
      SCKAScheme.oracleRecvA_run_eq_of_none _ _ (by simpa using hm)]
    simp
  | some entry =>
    obtain ⟨ρ, tsnd⟩ := entry
    have hm' : (authMapState π s).msgB n = some (ρ, tsnd) := by simpa using hm
    have hrel := recvWith_authMap hmap (idealOps ops s) s.stA ρ
    rcases hr : recvWith A₁ (idealOps ops s) s.stA ρ with err | r
    · rw [SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ hm' (by
        simp [schemeWith, recvSCKAWith, hops, hrel, hr, Except.map]),
        SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ hm (by simp [schemeWith, recvSCKAWith, hr])]
      simp [authMapState]
    · rw [SCKAScheme.oracleRecvA_run_eq_of_accept _ _ hm' (keyOpt := r.outputKey)
        (trcv := r.receivingEpoch) (stA' := authMapSt π r.state)
        (by simp [schemeWith, recvSCKAWith, hops, hrel, hr, authMapRecvRes, Except.map]),
        SCKAScheme.oracleRecvA_run_eq_of_accept _ _ hm (keyOpt := r.outputKey)
        (trcv := r.receivingEpoch) (stA' := r.state) (by simp [schemeWith, recvSCKAWith, hr]),
        map_pure, recvAUpdate_authMapState]
      rfl

/-- B version of `oracleRecvA_authMap`. -/
theorem oracleRecvB_authMap (hmap : AuthMap A₁ A₂ π) (s : GameState P AuthState) (n : ℕ) :
    (SCKAScheme.oracleRecvB (schemeWith A₂ (idealOps ops (authMapState π s)) sampleInitKey)
        n).run (authMapState π s) =
      Prod.map id (authMapState π) <$>
        (SCKAScheme.oracleRecvB (schemeWith A₁ (idealOps ops s) sampleInitKey) n).run s := by
  have hops : idealOps ops (authMapState π s) = idealOps ops s := rfl
  cases hm : s.msgA n with
  | none =>
    rw [SCKAScheme.oracleRecvB_run_eq_of_none _ _ hm,
      SCKAScheme.oracleRecvB_run_eq_of_none _ _ (by simpa using hm)]
    simp
  | some entry =>
    obtain ⟨ρ, tsnd⟩ := entry
    have hm' : (authMapState π s).msgA n = some (ρ, tsnd) := by simpa using hm
    have hrel := recvWith_authMap hmap (idealOps ops s) s.stB ρ
    rcases hr : recvWith A₁ (idealOps ops s) s.stB ρ with err | r
    · rw [SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ hm' (by
        simp [schemeWith, recvSCKAWith, hops, hrel, hr, Except.map]),
        SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ hm (by simp [schemeWith, recvSCKAWith, hr])]
      simp [authMapState]
    · rw [SCKAScheme.oracleRecvB_run_eq_of_accept _ _ hm' (keyOpt := r.outputKey)
        (trcv := r.receivingEpoch) (stB' := authMapSt π r.state)
        (by simp [schemeWith, recvSCKAWith, hops, hrel, hr, authMapRecvRes, Except.map]),
        SCKAScheme.oracleRecvB_run_eq_of_accept _ _ hm (keyOpt := r.outputKey)
        (trcv := r.receivingEpoch) (stB' := r.state) (by simp [schemeWith, recvSCKAWith, hr]),
        map_pure, recvBUpdate_authMapState]
      rfl

/-- A's leaking send over `A₂` from a mapped game state is the query over `A₁` followed by the
map, with the same coins and exposed epochs. -/
theorem oracleSendArleak_authMap (hmap : AuthMap A₁ A₂ π) (s : GameState P AuthState) :
    (SCKAScheme.oracleSendArleak (vuln P AuthState).rleak
        (schemeWith A₂ (idealOps ops (authMapState π s)) sampleInitKey) ()).run
        (authMapState π s) =
      Prod.map id (authMapState π) <$>
        (SCKAScheme.oracleSendArleak (vuln P AuthState).rleak
          (schemeWith A₁ (idealOps ops s) sampleInitKey) ()).run s := by
  rw [SCKAScheme.oracleSendArleak_run_eq, SCKAScheme.oracleSendArleak_run_eq]
  simp only [schemeWith, sendRleakWith_idealOps, authMapState_stA, sendRleakWith_authMap hmap,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun r => ?_
  obtain ⟨r, coins⟩ := r
  simp only [Prod.map, authMapSendRes, id, vuln_rleak_authMapSt, authMapState_challenged]
  split_ifs
  · rfl
  · simp only [sendAUpdate_authMapState]
    rfl

/-- B version of `oracleSendArleak_authMap`. -/
theorem oracleSendBrleak_authMap (hmap : AuthMap A₁ A₂ π) (s : GameState P AuthState) :
    (SCKAScheme.oracleSendBrleak (vuln P AuthState).rleak
        (schemeWith A₂ (idealOps ops (authMapState π s)) sampleInitKey) ()).run
        (authMapState π s) =
      Prod.map id (authMapState π) <$>
        (SCKAScheme.oracleSendBrleak (vuln P AuthState).rleak
          (schemeWith A₁ (idealOps ops s) sampleInitKey) ()).run s := by
  rw [SCKAScheme.oracleSendBrleak_run_eq, SCKAScheme.oracleSendBrleak_run_eq]
  simp only [schemeWith, sendRleakWith_idealOps, authMapState_stB, sendRleakWith_authMap hmap,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun r => ?_
  obtain ⟨r, coins⟩ := r
  simp only [Prod.map, authMapSendRes, id, vuln_rleak_authMapSt, authMapState_challenged]
  split_ifs
  · rfl
  · simp only [sendBUpdate_authMapState]
    rfl

omit [DecidableEq P.EpochKey] in
/-- The pinned challenge oracle commutes with the authenticator map: it reads and writes only
the key tables and the exposed and challenged sets. -/
theorem pinnedChallenge_run_authMapState [SampleableType P.EpochKey] (e : ℕ) (kStar : P.EpochKey)
    (t : ℕ) (s : GameState P AuthState) :
    (SCKAScheme.pinnedChallenge e kStar t).run (authMapState π s) =
      Prod.map id (authMapState π) <$> (SCKAScheme.pinnedChallenge e kStar t).run s := by
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [SCKAScheme.pinnedChallenge, SCKAScheme.pinnedChallengeWith, hg]
  · cases hA : s.keyA t <;> cases hB : s.keyB t <;> by_cases hr : 0 < t ∧ t < e <;>
      simp [SCKAScheme.pinnedChallenge, SCKAScheme.pinnedChallengeWith, hg, hA, hB, hr,
        StateT.run_bind, StateT.run_set, StateT.run_pure, StateT.run_monadLift, monadLift_self,
        authMapState]

omit [DecidableEq P.EpochKey] in
/-- The masked answer and state of A's corruption agree from a mapped game state and from the
game state, when `π t` is the identity for `t ≠ e`: the answer differs only for a state whose
authenticator state the update of `e` consumes, and that corruption exposes `e`. -/
theorem oracleCorruptA_authMap (e : ℕ) (hπ : ∀ t, t ≠ e → π t = id) (s : GameState P AuthState) :
    (fun y : Option (PartyState P AuthState) × GameState P AuthState =>
        (if decide (e ∈ y.2.exposed) then none else some y.1, y.2)) <$>
      (SCKAScheme.oracleCorruptA (vuln P AuthState).corrupt (PartyState P AuthState)
        P.EpochKey (Message P.Sym) ()).run (authMapState π s) =
    (fun y : Option (PartyState P AuthState) × GameState P AuthState =>
        (if decide (e ∈ y.2.exposed) then none else some y.1, authMapState π y.2)) <$>
      (SCKAScheme.oracleCorruptA (vuln P AuthState).corrupt (PartyState P AuthState)
        P.EpochKey (Message P.Sym) ()).run s := by
  rw [SCKAScheme.oracleCorruptA_run, SCKAScheme.oracleCorruptA_run, authMapState_stA,
    authMapState_challenged, vuln_corrupt_authMapSt]
  split_ifs with hg
  · simp only [map_pure, authMapState_exposed]
  · simp only [map_pure, authMapState_exposed]
    by_cases he : e ∈ s.exposed ∪ (vuln P AuthState).corrupt s.stA
    · simp [he]
      rfl
    · have hne : s.stA.authEpoch ≠ e := fun h => he (Finset.mem_union_right _
        (mem_vuln_corrupt.mpr (Or.inl h.symm)))
      simp [he, authMapState, authMapSt_eq_self π (hπ _ hne)]

omit [DecidableEq P.EpochKey] in
/-- B version of `oracleCorruptA_authMap`. -/
theorem oracleCorruptB_authMap (e : ℕ) (hπ : ∀ t, t ≠ e → π t = id) (s : GameState P AuthState) :
    (fun y : Option (PartyState P AuthState) × GameState P AuthState =>
        (if decide (e ∈ y.2.exposed) then none else some y.1, y.2)) <$>
      (SCKAScheme.oracleCorruptB (vuln P AuthState).corrupt (PartyState P AuthState)
        P.EpochKey (Message P.Sym) ()).run (authMapState π s) =
    (fun y : Option (PartyState P AuthState) × GameState P AuthState =>
        (if decide (e ∈ y.2.exposed) then none else some y.1, authMapState π y.2)) <$>
      (SCKAScheme.oracleCorruptB (vuln P AuthState).corrupt (PartyState P AuthState)
        P.EpochKey (Message P.Sym) ()).run s := by
  rw [SCKAScheme.oracleCorruptB_run, SCKAScheme.oracleCorruptB_run, authMapState_stB,
    authMapState_challenged, vuln_corrupt_authMapSt]
  split_ifs with hg
  · simp only [map_pure, authMapState_exposed]
  · simp only [map_pure, authMapState_exposed]
    by_cases he : e ∈ s.exposed ∪ (vuln P AuthState).corrupt s.stB
    · simp [he]
      rfl
    · have hne : s.stB.authEpoch ≠ e := fun h => he (Finset.mem_union_right _
        (mem_vuln_corrupt.mpr (Or.inl h.symm)))
      simp [he, authMapState, authMapSt_eq_self π (hπ _ hne)]


/-- Every stopped query over `A₂` from a mapped game state has the distribution of the stopped
query over `A₁` followed by the map, when `π t` is the identity for `t ≠ e`, the challenge oracle
commutes with the map, and both stop at the first exposure of `e`. -/
theorem oracle_authMap (hmap : AuthMap A₁ A₂ π) (e : ℕ) (hπ : ∀ t, t ≠ e → π t = id)
    (chall : QueryImpl (ℕ →ₒ Option P.EpochKey) (StateT (GameState P AuthState) ProbComp))
    (hchall : ∀ t s, (chall t).run (authMapState π s) =
      Prod.map id (authMapState π) <$> (chall t).run s)
    (t : (securitySpec P AuthState).Domain) (s : GameState P AuthState) :
    ((stopOnState (SCKAScheme.securityImplAt
        (fun u => schemeWith A₂ (idealOps ops u) sampleInitKey) chall
        (vuln P AuthState) (vuln P AuthState)) (fun u => decide (e ∈ u.exposed)) t).run).run
      (authMapState π s) =ᵈ
    Prod.map id (authMapState π) <$>
      ((stopOnState (SCKAScheme.securityImplAt
        (fun u => schemeWith A₁ (idealOps ops u) sampleInitKey) chall
        (vuln P AuthState) (vuln P AuthState)) (fun u => decide (e ∈ u.exposed)) t).run).run s := by
  have hstop : ∀ u : GameState P AuthState,
      decide (e ∈ (authMapState π u).exposed) = decide (e ∈ u.exposed) := fun u => rfl
  rcases t with (((((t | u) | u) | t) | u) | u)
  · apply evalDistEq_stopOnState_of_map _ _ _ _ _ hstop
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf]
    rcases t with ((((n | u) | u) | n) | n)
    · simp only [SCKAScheme.sckaCorrectnessImpl]
      exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleUnif_run_map _ n s)
    · cases u
      simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact ToVCVio.evalDistEq_of_eq (oracleSendA_authMap ops sampleInitKey hmap s)
    · cases u
      simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact ToVCVio.evalDistEq_of_eq (oracleSendB_authMap ops sampleInitKey hmap s)
    · simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact ToVCVio.evalDistEq_of_eq (oracleRecvA_authMap ops sampleInitKey hmap s n)
    · simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact ToVCVio.evalDistEq_of_eq (oracleRecvB_authMap ops sampleInitKey hmap s n)
  · cases u
    apply evalDistEq_stopOnState_of_map _ _ _ _ _ hstop
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    exact ToVCVio.evalDistEq_of_eq (oracleSendArleak_authMap ops sampleInitKey hmap s)
  · cases u
    apply evalDistEq_stopOnState_of_map _ _ _ _ _ hstop
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    exact ToVCVio.evalDistEq_of_eq (oracleSendBrleak_authMap ops sampleInitKey hmap s)
  · apply evalDistEq_stopOnState_of_map _ _ _ _ _ hstop
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf]
    exact ToVCVio.evalDistEq_of_eq (hchall t s)
  · cases u
    rw [stopOnState_run_eq_map, stopOnState_run_eq_map, Functor.map_map]
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf]
    exact ToVCVio.evalDistEq_of_eq (oracleCorruptA_authMap e hπ s)
  · cases u
    rw [stopOnState_run_eq_map, stopOnState_run_eq_map, Functor.map_map]
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf, QueryImpl.add_apply_inr]
    exact ToVCVio.evalDistEq_of_eq (oracleCorruptB_authMap e hπ s)

/-- Transport of the stopped games: if `π` maps `A₁` to `A₂`, `π t` is the identity for `t ≠ e`,
and the challenge oracle commutes with the map, then for every adversary the security oracles
over `A₂` from `authMapState π s₀` and over `A₁` from `s₀`, with the operations `ops`, stopped at
the first exposure of `e`, accept equally often. -/
theorem prEvent_stoppedRun_authMap (hmap : AuthMap A₁ A₂ π) (e : ℕ)
    (hπ : ∀ t, t ≠ e → π t = id)
    (chall : QueryImpl (ℕ →ₒ Option P.EpochKey) (StateT (GameState P AuthState) ProbComp))
    (hchall : ∀ t s, (chall t).run (authMapState π s) =
      Prod.map id (authMapState π) <$> (chall t).run s)
    (adv : SecurityAdversary P AuthState) (s₀ : GameState P AuthState) :
    Pr{let x ← (stoppedRun (SCKAScheme.securityImplAt
        (fun u => schemeWith A₂ (idealOps ops u) sampleInitKey) chall
        (vuln P AuthState) (vuln P AuthState)) (fun u => decide (e ∈ u.exposed)) adv
        (authMapState π s₀))}[x = true] =
    Pr{let x ← (stoppedRun (SCKAScheme.securityImplAt
        (fun u => schemeWith A₁ (idealOps ops u) sampleInitKey) chall
        (vuln P AuthState) (vuln P AuthState)) (fun u => decide (e ∈ u.exposed)) adv
        s₀)}[x = true] := by
  unfold stoppedRun
  exact prEvent_optionRun_eq_of_state_map _ _ (authMapState π) (fun _ => True)
    (fun _ _ _ _ _ _ => trivial)
    (fun t s _ => oracle_authMap ops sampleInitKey hmap e hπ chall hchall t s) adv s₀ trivial

end Oracles

end Transport

/-! ### The authenticator of the hidden state -/

section Hidden

variable (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)

/-- The authenticator that keeps a representative in place of the hidden authenticator state
entering `e`: its update at `e - 1` keeps its argument, its header operations at `e` and its
ciphertext operations at `e - 1` are those of `h` on the representative, and its update at `e` is
`h.next`; every other operation is that of `auth`. -/
def withHidden (h : HiddenAuth AuthState P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (e : ℕ) :
    RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac where
  init := auth.init
  update a t ik := if t = e then h.next a else if t + 1 = e then a else auth.update a t ik
  macHeader a t hdr := if t = e then h.macHeader a hdr else auth.macHeader a t hdr
  verifyHeader a t hdr tag :=
    if t = e then h.verifyHeader a hdr tag else auth.verifyHeader a t hdr tag
  macCiphertext a t c := if t + 1 = e then h.macCiphertext a c else auth.macCiphertext a t c
  verifyCiphertext a t c tag :=
    if t + 1 = e then h.verifyCiphertext a c tag else auth.verifyCiphertext a t c tag
  verifyHeader_correct a t hdr := by
    by_cases ht : t = e <;> simp [ht, h.verifyHeader_correct, auth.verifyHeader_correct]
  verifyCiphertext_correct a t c := by
    by_cases ht : t + 1 = e <;>
      simp [ht, h.verifyCiphertext_correct, auth.verifyCiphertext_correct]

/-- The authenticator map replacing an authenticator state consumed by the update of `e` by
`hide` of it. -/
def hiddenMap (e : ℕ) (hide : AuthState → AuthState) : ℕ → AuthState → AuthState :=
  fun t => if t = e then hide else id

/-- `hiddenMap e hide t` is the identity for `t ≠ e`. -/
theorem hiddenMap_of_ne {e t : ℕ} (hide : AuthState → AuthState) (ht : t ≠ e) :
    hiddenMap e hide t = id := by
  simp [hiddenMap, ht]

/-- For `0 < e`, `hiddenMap e hide` maps the simulated instance's authenticator over
`withHidden auth (Braid.hiddenAuth auth hide e u) e` to the one over `authAt auth (e - 1) hide`,
both with the update of `e` keyed by `u`. -/
theorem authMap_withHidden {e : ℕ} (he : 0 < e) (hide : AuthState → AuthState)
    (u k : P.EpochKey) :
    AuthMap
      (authAt (withHidden auth (hiddenAuth auth hide e u) e) e
        (fun a => (withHidden auth (hiddenAuth auth hide e u) e).update a e k))
      (authAt (authAt auth (e - 1) hide) e (fun a => (authAt auth (e - 1) hide).update a e u))
      (hiddenMap e hide) := by
  have hne : e ≠ e - 1 := by omega
  refine ⟨fun a t hdr => ?_, fun a t hdr tag => ?_, fun a t ik => ?_, fun a t c => ?_,
    fun a t c tag => ?_⟩
  · by_cases ht : t = e <;> simp [authAt, withHidden, hiddenAuth, hiddenMap, ht]
  · by_cases ht : t = e <;> simp [authAt, withHidden, hiddenAuth, hiddenMap, ht]
  · by_cases ht : t = e
    · subst ht
      simp [authAt, withHidden, hiddenAuth, hiddenMap, hne]
    · by_cases ht' : t + 1 = e
      · subst ht'
        simp [authAt, withHidden, hiddenAuth, hiddenMap]
      · have ht'' : t ≠ e - 1 := by omega
        simp [authAt, withHidden, hiddenAuth, hiddenMap, ht, ht', ht'']
  · by_cases ht : t + 1 = e
    · subst ht
      simp [authAt, withHidden, hiddenAuth, hiddenMap]
    · simp [authAt, withHidden, hiddenAuth, hiddenMap, ht]
  · by_cases ht : t + 1 = e
    · subst ht
      simp [authAt, withHidden, hiddenAuth, hiddenMap]
    · simp [authAt, withHidden, hiddenAuth, hiddenMap, ht]

end Hidden

/-- The initial game states of two authenticators correspond under `π` when `π 1` maps the
initial authenticator state of the first to that of the second. -/
theorem authMapState_initState {π}
    (A₁ A₂ : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (ik₁ ik₂ : InitKey)
    (h : π 1 (A₁.init ik₁ 1) = A₂.init ik₂ 1) :
    authMapState π (initState A₁ ik₁) = initState A₂ ik₂ := by
  simp [initState, authMapState, SCKAScheme.initGameState, authMapSt, PartyState.mapAuth,
    PartyState.authEpoch, PartyState.authUpdated, PartyState.epoch, initA, initB, h]

end SPQR
