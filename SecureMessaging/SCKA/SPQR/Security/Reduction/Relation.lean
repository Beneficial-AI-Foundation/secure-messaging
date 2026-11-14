/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Security.Reduction.Pinned

/-!
# The simulated instance and hiding the challenge-epoch secrets

Let `e` be the epoch at which the reductions embed their challenge and `kemMat` its KEM material
(`Reduction.Pinned`). The simulator knows only the public values of `e`, a public key `pk` and
ciphertext components `ct1`, `ct2`, and the authenticator update `upd` of `e`. In place of the
secret key, the encapsulation state, and the KEM key of `e`, it uses *dummies* `d : Dummies P`,
drawn by `sampleDummies` from a fresh key pair and first stage. This module relates its states to
those of the honest instance `honestSchemeOf kemMat` (`Reduction.Pinned`), which pins both sampling
phases of `e` to `kemMat`.

- *Simulated instance.* At epoch `e`, the operations `simOps pk ct1 ct2 d e` return `pk` with
  the dummy secret key, then the dummy state, `ct1`, and the dummy KEM key, each with fresh coins,
  and `ct2` as second ciphertext component; the other epochs run the real operations. The
  simulated instance `simSchemeOf pk ct1 ct2 upd` is the ideal instance over these operations with
  the authenticator update of `e` replaced by `upd`.
- *Hiding.* `hideSt e d` replaces the secret key or encapsulation state of epoch `e` in a party
  state by its dummy, and `hideKeys e τ` every key recorded at `e` by the dummy epoch key
  `τ := P.kdfOK d.k e`. `hideState e d τ` hides both party states and both key tables of a game
  state; `hideSendRes` and `hideRecvRes` hide the state of a send or receive result and replace an
  output key at `e` by `τ`.
- *Commutation.* Take the public values of `kemMat` and the update
  `upd a := auth.update a e (kemMat.epochKey e)`. An operation of the simulated instance on a
  hidden state equals the operation of the honest instance followed by hiding: in distribution for
  the ordinary send (`sendWith_sim_hide`), as a computation for the leaking send of a state that
  does not sample at `e`, with the coins unchanged (`sendRleakWith_sim_hide_of_not_samples`), and,
  under the pinned invariant of `kemMat` and with a sound vector decoder, for the receive of a
  message recorded by the peer (`recvWith_sim_hide`).
-/

@[expose] public section

open OracleSpec OracleComp ErasureCodePayload.Streaming

namespace SPQR

open Chunked

/-- The dummy secrets of the simulated epoch: a decapsulation key, an encapsulation state and a
KEM key. -/
structure Dummies (P : SPQR.Parameters ProbComp) where
  /-- The dummy decapsulation key. -/
  sk : P.SK
  /-- The dummy encapsulation state. -/
  es : P.det.St
  /-- The dummy KEM key. -/
  k : P.K

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (sampleInitKey : ProbComp InitKey)
  (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
  (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)

/-- Sample the dummies: the secret key of a fresh key pair, and the state and KEM key of a fresh
first stage at its header. -/
def sampleDummies : ProbComp (Dummies P) := do
  let (pk, sk) ← P.det.toKEM.keygen
  let (es, _, k) ← P.det.toIncremental.encaps1 (P.det.toHeader pk)
  pure ⟨sk, es, k⟩

/-! ### The simulated operations -/

/-- The operations of the simulator: at epoch `e`, key generation returns `pk` with the dummy
secret key and fresh coins, the first stage returns the dummy state, `ct1` and the dummy KEM key
with fresh coins, and the second stage returns `ct2`; the other epochs run the real
operations. -/
def simOps (pk : P.PK) (ct1 : P.det.C₁) (ct2 : P.det.C₂) (d : Dummies P) (e : ℕ) :
    Ops P where
  keygenRleak t :=
    if t = e then (fun z => ((pk, d.sk), z.2)) <$> P.det.toRandLeak.keygenRleak else
      P.det.toRandLeak.keygenRleak
  encaps1Rleak t hdr :=
    if t = e then (fun z => ((d.es, ct1, d.k), z.2)) <$> P.det.toRandLeak.encaps1Rleak hdr
    else P.det.toRandLeak.encaps1Rleak hdr
  encaps2 t es hdr vec := if t = e then ct2 else P.det.encaps2Det es hdr vec
  completeKey t sk c1 c2 :=
    (P.det.decapsDet sk (P.det.splitC.symm (c1, c2))).map (fun k => P.kdfOK k t)

/-! ### Hiding -/

/-- The party state with the secret key, respectively the encapsulation state, of epoch `e`
replaced by the dummy. -/
def hideSt (e : ℕ) (d : Dummies P) : PartyState P AuthState → PartyState P AuthState
  | .keysSampled core enc =>
      .keysSampled (if core.ep = e then { core with sk := d.sk } else core) enc
  | .headerSent core enc dec =>
      .headerSent (if core.ep = e then { core with sk := d.sk } else core) enc dec
  | .ct1Received core enc =>
      .ct1Received (if core.ep = e then { core with sk := d.sk } else core) enc
  | .ekSentCt1Received core dec =>
      .ekSentCt1Received (if core.ep = e then { core with sk := d.sk } else core) dec
  | .ct1Sampled core enc dec =>
      .ct1Sampled (if core.ep = e then { core with encapsSt := d.es } else core) enc dec
  | .ekReceivedCt1Sampled core enc =>
      .ekReceivedCt1Sampled (if core.ep = e then { core with encapsSt := d.es } else core) enc
  | .ct1Acknowledged core dec =>
      .ct1Acknowledged (if core.ep = e then { core with encapsSt := d.es } else core) dec
  | st => st

/-- The key table with every key recorded at `e` replaced by `τ`. -/
def hideKeys (e : ℕ) (τ : P.EpochKey) (keys : ℕ → Option P.EpochKey) : ℕ → Option P.EpochKey :=
  fun t => if t = e then (keys t).map (fun _ => τ) else keys t

/-- The game state with both party states and both key tables hidden. -/
@[simps -fullyApplied]
def hideState (e : ℕ) (d : Dummies P) (τ : P.EpochKey) (s : GameState P AuthState) :
    GameState P AuthState :=
  { s with
    stA := hideSt e d s.stA
    stB := hideSt e d s.stB
    keyA := hideKeys e τ s.keyA
    keyB := hideKeys e τ s.keyB }

/-- An output key `(t, k)` with `k` replaced by `τ` if `t = e`. -/
def hideKey (e : ℕ) (τ : P.EpochKey) (p : ℕ × P.EpochKey) : ℕ × P.EpochKey :=
  (p.1, if p.1 = e then τ else p.2)

/-- A send result with its state hidden and its output key at `e` replaced by `τ`. -/
def hideSendRes (e : ℕ) (d : Dummies P) (τ : P.EpochKey) (r : SendResult P AuthState) :
    SendResult P AuthState :=
  ⟨r.msg, r.sendingEpoch, r.outputKey.map (hideKey e τ), hideSt e d r.state⟩

/-- A receive result with its state hidden and its output key at `e` replaced by `τ`. -/
def hideRecvRes (e : ℕ) (d : Dummies P) (τ : P.EpochKey) (r : RecvResult P AuthState) :
    RecvResult P AuthState :=
  ⟨r.receivingEpoch, r.outputKey.map (hideKey e τ), hideSt e d r.state⟩

variable (e : ℕ) (d : Dummies P) (τ : P.EpochKey)

/-- Hiding keeps the epoch. -/
theorem hideSt_epoch (st : PartyState P AuthState) : (hideSt e d st).epoch = st.epoch := by
  cases st <;> simp only [hideSt, PartyState.epoch] <;> split_ifs <;> rfl

/-- Hiding keeps whether the state holds a secret. -/
@[simp] theorem hideSt_holdsSecret (st : PartyState P AuthState) :
    (hideSt e d st).holdsSecret = st.holdsSecret := by
  cases st <;> rfl

/-- Hiding keeps whether the authenticator state includes the key of the current epoch. -/
@[simp] theorem hideSt_authUpdated (st : PartyState P AuthState) :
    (hideSt e d st).authUpdated = st.authUpdated := by
  cases st <;> rfl

/-- Hiding keeps the epoch whose authenticator update consumes the authenticator state. -/
@[simp] theorem hideSt_authEpoch (st : PartyState P AuthState) :
    (hideSt e d st).authEpoch = st.authEpoch := by
  simp [PartyState.authEpoch, hideSt_epoch]

/-- A state of another epoch is unchanged by hiding. -/
theorem hideSt_eq_of_ne {st : PartyState P AuthState} (h : st.epoch ≠ e) : hideSt e d st = st := by
  cases st <;> simp only [hideSt, PartyState.epoch] at h ⊢ <;> simp [h]

/-- The hidden state of a state without a secret is itself. -/
theorem hideSt_eq_self_of_not_holdsSecret {st : PartyState P AuthState}
    (h : st.holdsSecret = false) : hideSt e d st = st := by
  cases st <;> simp only [PartyState.holdsSecret] at h <;> first | rfl | cases h

/-- Hiding keeps whether a key is recorded. -/
@[simp] theorem hideKeys_isSome (keys : ℕ → Option P.EpochKey) (t : ℕ) :
    (hideKeys e τ keys t).isSome = (keys t).isSome := by
  unfold hideKeys
  split_ifs <;> simp

/-- Hiding keeps whether a key is absent. -/
@[simp] theorem hideKeys_isNone (keys : ℕ → Option P.EpochKey) (t : ℕ) :
    (hideKeys e τ keys t).isNone = (keys t).isNone := by
  unfold hideKeys
  split_ifs <;> simp

/-- The hidden table at another epoch. -/
theorem hideKeys_of_ne (keys : ℕ → Option P.EpochKey) {t : ℕ} (h : t ≠ e) :
    hideKeys e τ keys t = keys t := by
  simp [hideKeys, h]

/-- The hidden table at `e`. -/
@[simp] theorem hideKeys_self (keys : ℕ → Option P.EpochKey) :
    hideKeys e τ keys e = (keys e).map (fun _ => τ) := by
  simp [hideKeys]

/-- Hiding commutes with recording a key. -/
theorem hideKeys_update (keys : ℕ → Option P.EpochKey) (t : ℕ) (k : P.EpochKey) :
    hideKeys e τ (Function.update keys t (some k)) =
      Function.update (hideKeys e τ keys) t (some (if t = e then τ else k)) := by
  funext u
  by_cases hu : u = t
  · subst hu
    simp only [hideKeys, Function.update_self, Option.map_some]
    split_ifs <;> rfl
  · simp [hideKeys, Function.update_of_ne hu]

/-- The prefix check reads only whether keys are recorded. -/
@[simp] theorem knownPrefix_hideKeys (keys : ℕ → Option P.EpochKey) (n : ℕ) :
    SCKAScheme.knownPrefix (hideKeys e τ keys) n = SCKAScheme.knownPrefix keys n := by
  simp [SCKAScheme.knownPrefix]

/-- The empty table is unchanged by hiding. -/
private theorem hideKeys_none : hideKeys e τ (fun _ => none) = fun _ => none := by
  funext t
  simp [hideKeys]

/-- The initial game state is unchanged by hiding. -/
theorem hideState_initState (ik : InitKey) :
    hideState e d τ (initState auth ik) = initState auth ik := by
  simp [hideState, initState, SCKAScheme.initGameState, initA, initB, hideSt, hideKeys_none]

/-- Hiding the key table of a party. -/
theorem hideState_keysAt (s : GameState P AuthState) (party : Bool) :
    (hideState e d τ s).keysAt party = hideKeys e τ (s.keysAt party) := by
  cases party <;> rfl

/-! ### The sends -/

section Sends

variable (kemMat : KEMMaterial P)

/-- From a hidden state, the ordinary send of the simulated instance has the distribution of the
send of the honest instance followed by `hideSendRes`. -/
theorem sendWith_sim_hide (st : PartyState P AuthState) :
    sendWith (authAt auth e (fun a => auth.update a e (kemMat.epochKey e)))
        (simOps kemMat.pk kemMat.ct1 kemMat.ct2 d e) (hideSt e d st) =ᵈ
      hideSendRes e d (P.kdfOK d.k e) <$>
        sendWith auth (pinOps (some kemMat.kg) (some kemMat.enc) e) st := by
  obtain ⟨⟨⟨pk, sk⟩, rkg⟩, ⟨⟨es, c1, k⟩, renc⟩⟩ := kemMat
  cases st
  case keysUnsampled core =>
    by_cases h : core.ep = e
    · subst h
      simp only [sendWith, sendRleakWith, hideSt, simOps, pinOps, Option.elim, ↓reduceIte,
        KEMMaterial.pk, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      refine (OracleComp.EvalDistEq.bind_const_of_support P.det.toRandLeak.keygenRleak (fun _ _ =>
        rfl)).trans
        (ToVCVio.evalDistEq_of_eq ?_)
      simp [hideSendRes, hideSt]
    · simp only [sendWith, sendRleakWith, hideSt, simOps, pinOps, h, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      simp only [KEMScheme.IncrementalKEMDet.toRandLeak,
        KEMScheme.IncrementalKEMDet.toIncremental, bind_assoc, pure_bind]
      refine ToVCVio.evalDistEq_of_eq (bind_congr fun z => ?_)
      simp [hideSendRes, hideSt, h]
  case headerReceived core dec =>
    by_cases h : core.ep = e
    · subst h
      simp only [sendWith, sendRleakWith, hideSt, simOps, pinOps, Option.elim, ↓reduceIte,
        KEMMaterial.ct1, KEMMaterial.epochKey, KEMMaterial.key, map_eq_bind_pure_comp, bind_assoc,
        pure_bind, Function.comp_def, authAt_update_self]
      refine (OracleComp.EvalDistEq.bind_const_of_support (P.det.toRandLeak.encaps1Rleak core.hdr)
        (fun _ _ => rfl)).trans (ToVCVio.evalDistEq_of_eq ?_)
      simp [hideSendRes, hideSt, hideKey]
    · simp only [sendWith, sendRleakWith, hideSt, simOps, pinOps, h, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
        authAt_update_of_ne auth e _ _ h]
      simp only [KEMScheme.IncrementalKEMDet.toRandLeak,
        KEMScheme.IncrementalKEMDet.toIncremental, bind_assoc, pure_bind]
      refine ToVCVio.evalDistEq_of_eq (bind_congr fun z => ?_)
      simp [hideSendRes, hideSt, hideKey, h]
  all_goals
    refine ToVCVio.evalDistEq_of_eq ?_
    simp only [sendWith, sendRleakWith, SPQR.send, Chunked.send, hideSt, hideSendRes, map_pure]
    first
    | (split_ifs <;> simp [*])
    | simp

/-- For a state whose send does not sample at `e`, the leaking send of the simulated instance from
the hidden state is the leaking send of the honest instance followed by `hideSendRes`, with the
coins unchanged. -/
theorem sendRleakWith_sim_hide_of_not_samples (st : PartyState P AuthState)
    (h : ¬ (st.samples = true ∧ st.epoch = e)) :
    sendRleakWith (authAt auth e (fun a => auth.update a e (kemMat.epochKey e)))
        (simOps kemMat.pk kemMat.ct1 kemMat.ct2 d e) (hideSt e d st) =
      Prod.map (hideSendRes e d (P.kdfOK d.k e)) id <$>
        sendRleakWith auth (pinOps (some kemMat.kg) (some kemMat.enc) e) st := by
  obtain ⟨⟨⟨pk, sk⟩, rkg⟩, ⟨⟨es, c1, k⟩, renc⟩⟩ := kemMat
  cases st
  case keysUnsampled core =>
    have hne : core.ep ≠ e := fun hee => h ⟨rfl, hee⟩
    simp only [sendRleakWith, hideSt, simOps, pinOps, hne, ↓reduceIte, map_eq_bind_pure_comp,
      Function.comp_def]
    simp only [KEMScheme.IncrementalKEMDet.toRandLeak,
      KEMScheme.IncrementalKEMDet.toIncremental, bind_assoc, pure_bind]
    refine bind_congr fun z => ?_
    simp [hideSendRes, hideSt, hne]
  case headerReceived core dec =>
    have hne : core.ep ≠ e := fun hee => h ⟨rfl, hee⟩
    simp only [sendRleakWith, hideSt, simOps, pinOps, hne, ↓reduceIte, map_eq_bind_pure_comp,
      Function.comp_def, authAt_update_of_ne auth e _ _ hne]
    simp only [KEMScheme.IncrementalKEMDet.toRandLeak,
      KEMScheme.IncrementalKEMDet.toIncremental, bind_assoc, pure_bind]
    refine bind_congr fun z => ?_
    simp [hideSendRes, hideSt, hideKey, hne]
  all_goals
    simp only [sendRleakWith, SPQR.send, Chunked.send, hideSt, hideSendRes, map_pure, Prod.map]
    first
    | (split_ifs <;> simp [*])
    | simp

end Sends

/-! ### The simulated instance -/

/-- The simulated instance: the ideal instance over `simOps pk ct1 ct2 d e`, with the
authenticator update of epoch `e` replaced by `upd`. -/
abbrev simSchemeOf (pk : P.PK) (ct1 : P.det.C₁) (ct2 : P.det.C₂)
    (upd : AuthState → AuthState) (s : GameState P AuthState) :=
  schemeWith (authAt auth e upd) (idealOps (simOps pk ct1 ct2 d e) s) sampleInitKey

/-! ### Facts at the simulated epoch -/

variable (kemMat : KEMMaterial P)

section Facts

variable {ik : InitKey} {T : ℕ → Braid.EpochTranscript P.toBraid} {s : GameState P AuthState}
  {D : ℕ → P.toBraid.PK → P.toBraid.SK → P.toBraid.inc.St → P.toBraid.inc.C₁ → P.toBraid.K → Prop}
  (hT : Braid.TranscriptInv auth D ik T s.toBraid)
  (hpin : PinnedTranscript (some kemMat.kg.1) (some kemMat.enc.1) e T)

include hT hpin

include hEkSound in
/-- A vector decoder holding chunks of the vector of the transcript key pair at `e`, extended by a
vector chunk recorded by the peer for `e`, decodes only to the vector of `kemMat.pk`. -/
private theorem ek_decoded_eq (party : Bool)
    {n tsnd : ℕ} {payload : Payload P.Sym} {chunk : ℕ × P.Sym}
    (hentry : s.messagesAt (!party) n = some (⟨e, payload⟩, tsnd))
    (hpay : payload = .ek chunk ∨ payload = .ekCt1Ack chunk)
    {pk : P.PK} {sk : P.SK} (hkp : (T e).keypair = some (pk, sk))
    {dec : P.decEk.D} (hrcv : P.decEk.Received P.ecpEk (P.det.toVector pk) dec)
    {vec : P.det.PKvector} (hv : P.decEk.decodedPayload (P.decEk.addChunk dec chunk) = some vec) :
    vec = P.det.toVector kemMat.pk := by
  have hPayload := hT.messages (!party) n _ tsnd (GameState.toBraid_messagesAt_eq_some hentry)
  obtain ⟨pk', sk', i, hkp', hch⟩ : ∃ pk' sk' i, (T e).keypair = some (pk', sk') ∧
      chunk = P.ecpEk.encode (P.det.toVector pk') i := by
    rcases hpay with rfl | rfl <;>
      simp only [Message.toBraid, Braid.MessagePayloadInv,
        Option.some.injEq] at hPayload <;> exact hPayload
  obtain ⟨rfl, -⟩ : pk = pk' ∧ sk = sk' := by simpa using hkp.symm.trans hkp'
  have hC := hEkSound.received_addChunk hrcv i
  erw [← hch] at hC
  obtain ⟨-, hnone | hsome⟩ := hC
  · rw [hnone] at hv
    cases hv
  · rw [hsome] at hv
    obtain ⟨-, -, hvec⟩ := hpin.1 kemMat.pk kemMat.sk rfl pk sk hkp
    rw [← hvec]
    exact (Option.some.inj hv).symm

/-- A party in `ct1Sampled` at `e` holds the header of `kemMat.pk` and the state `kemMat.es`, and
its vector decoder holds chunks of the vector of the transcript key pair. -/
private theorem PinnedInv.ct1Sampled_facts (party : Bool) {core : CtSender.Ct1Sent P AuthState}
    {enc : EncoderState P.det.C₁ P.Sym} {dec : P.decEk.D}
    (hst : s.stateAt party = .ct1Sampled core enc dec) (he : core.ep = e) :
    core.hdr = P.det.toHeader kemMat.pk ∧ core.encapsSt = kemMat.es ∧
      ∃ pk sk, (T e).keypair = some (pk, sk) ∧
        P.decEk.Received P.ecpEk (P.det.toVector pk) dec := by
  have hL := hT.local (P := P.toBraid) auth party
  rw [GameState.toBraid_stateAt, hst] at hL
  simp only [PartyState.toBraid, Braid.LocalPayloadInv] at hL
  obtain ⟨-, pk, sk, key, hkp, hc, hhdr, -, hrcv⟩ := hL
  rw [he] at hkp hc
  obtain ⟨-, hh, -⟩ := hpin.1 kemMat.pk kemMat.sk rfl pk sk hkp
  obtain ⟨hes, -, -⟩ := hpin.2 kemMat.es kemMat.ct1 kemMat.key rfl _ _ _ hc
  exact ⟨hhdr.trans hh, hes, pk, sk, hkp, hrcv⟩

/-- A party in `ekReceivedCt1Sampled` at `e` holds the header and vector of `kemMat.pk` and the
state `kemMat.es`. -/
private theorem PinnedInv.ekReceived_facts (party : Bool)
    {core : CtSender.Ct1SentEkReceived P AuthState} {enc : EncoderState P.det.C₁ P.Sym}
    (hst : s.stateAt party = .ekReceivedCt1Sampled core enc) (he : core.ep = e) :
    core.hdr = P.det.toHeader kemMat.pk ∧ core.ek = P.det.toVector kemMat.pk
      ∧ core.encapsSt = kemMat.es := by
  have hL := hT.local (P := P.toBraid) auth party
  rw [GameState.toBraid_stateAt, hst] at hL
  simp only [PartyState.toBraid, Braid.LocalPayloadInv] at hL
  obtain ⟨-, pk, sk, key, hkp, hc, hhdr, hvec, -⟩ := hL
  rw [he] at hkp hc
  obtain ⟨-, hh, hv⟩ := hpin.1 kemMat.pk kemMat.sk rfl pk sk hkp
  obtain ⟨hes, -, -⟩ := hpin.2 kemMat.es kemMat.ct1 kemMat.key rfl _ _ _ hc
  exact ⟨hhdr.trans hh, hvec.trans hv, hes⟩

/-- A party in `ct1Acknowledged` at `e` holds the header of `kemMat.pk` and the state `kemMat.es`,
and its vector decoder holds chunks of the vector of the transcript key pair. -/
private theorem PinnedInv.ct1Acknowledged_facts (party : Bool)
    {core : CtSender.Ct1Sent P AuthState}
    {dec : P.decEk.D}
    (hst : s.stateAt party = .ct1Acknowledged core dec) (he : core.ep = e) :
    core.hdr = P.det.toHeader kemMat.pk ∧ core.encapsSt = kemMat.es ∧
      ∃ pk sk, (T e).keypair = some (pk, sk) ∧
        P.decEk.Received P.ecpEk (P.det.toVector pk) dec := by
  have hL := hT.local (P := P.toBraid) auth party
  rw [GameState.toBraid_stateAt, hst] at hL
  simp only [PartyState.toBraid, Braid.LocalPayloadInv] at hL
  obtain ⟨-, pk, sk, key, hkp, hc, hhdr, hrcv⟩ := hL
  rw [he] at hkp hc
  obtain ⟨-, hh, -⟩ := hpin.1 kemMat.pk kemMat.sk rfl pk sk hkp
  obtain ⟨hes, -, -⟩ := hpin.2 kemMat.es kemMat.ct1 kemMat.key rfl _ _ _ hc
  exact ⟨hhdr.trans hh, hes, pk, sk, hkp, hrcv⟩

end Facts

/-! ### The receive relation -/

section Receive


set_option hygiene false in
/-- The cells of `recvWith_sim_hide` and `recvWith_sim_hide_of_ne` that do not read the pinned KEM
material: unfold both receives definitionally, resolve the epoch test of the hiding and the table
reads, split on the epochs and decoders, and compare. -/
local macro "hide_generic" : tactic => `(tactic|
  (dsimp only [recvWith, recv, hideSt, EkSender.sendEk, EkSender.recvCt1,
     CtSender.recvNextEpoch, CtSender.recvHeader, CtSender.recvEk, Parameters.ekMatchesHeader,
     Parameters.encaps2, Parameters.decaps, idealOps, simOps, pinOps, completeCt2With, recvCt2With]
   try simp only [hee, ↓reduceIte, hideState_keysAt, hideKeys_of_ne, authAt_update_of_ne,
     authAt_verifyHeader, authAt_macCiphertext, authAt_verifyCiphertext, ne_eq,
     not_false_eq_true]
   repeat' split
   all_goals try simp only [PartyState.epoch] at *
   all_goals first
     | omega
     | (simp_all [hideRecvRes, hideSt, hideKey, Except.map]; done)
     | (simp_all [hideRecvRes, hideSt, hideKey, Except.map]
        repeat' (obtain ⟨-, rfl⟩ := ‹_ ∧ _ = _›)
        subst_vars
        simp_all [hideRecvRes, hideSt, hideKey, Except.map]
        done)
   done))

set_option hygiene false in
/-- The fallback of an overridden cell of `recvWith_sim_hide`: a message of another epoch is
ignored or refused by both receives. -/
local macro "hide_fallback" : tactic => `(tactic|
  (rcases Nat.lt_or_gt_of_ne hme with hlt | hgt
   · simp [recv, PartyState.epoch, hlt, hideRecvRes, hideSt, Except.map]
   · simp [recv, PartyState.epoch, hgt, not_lt.mpr hgt.le, hideRecvRes, hideSt, Except.map]))

set_option hygiene false in
/-- `hide_fallback` for a state at another epoch than `e`. -/
local macro "hide_fallback_ne" : tactic => `(tactic|
  (rcases Nat.lt_or_gt_of_ne hme with hlt | hgt
   · simp [recv, PartyState.epoch, hlt, hideRecvRes, hideSt, hee, Except.map]
   · simp [recv, PartyState.epoch, hgt, not_lt.mpr hgt.le, hideRecvRes, hideSt, hee, Except.map]))

set_option maxHeartbeats 400000 in
-- The enumeration of the 11 states × 7 payloads exceeds the default budget.
/-- From a state at another epoch than `e`, the simulated and the honest instances receive alike,
and hiding changes nothing. -/
private theorem recvWith_sim_hide_of_ne (s : GameState P AuthState) (st : PartyState P AuthState)
    (hee : st.epoch ≠ e) (msg : Message P.Sym) :
    recvWith (authAt auth e (fun a => auth.update a e (kemMat.epochKey e)))
        (idealOps (simOps kemMat.pk kemMat.ct1 kemMat.ct2 d e)
          (hideState e d (P.kdfOK d.k e) s))
        (hideSt e d st) msg =
      Except.map (hideRecvRes e d (P.kdfOK d.k e))
        (recvWith auth (idealOps (pinOps (some kemMat.kg) (some kemMat.enc) e) s) st msg) := by
  obtain ⟨me, payload⟩ := msg
  cases st <;> cases payload <;> simp only [PartyState.epoch] at hee
  case ekSentCt1Received.ct2 core dec chunk =>
    rw [hideSt_eq_of_ne e d (st := .ekSentCt1Received core dec) hee]
    by_cases hme : me = core.ep
    · subst hme
      simp only [recvWith, ↓reduceIte, idealOps, recvCt2With, hideState_keysAt,
        hideKeys_of_ne _ _ _ hee, authAt_update_of_ne _ _ _ _ hee, authAt_verifyCiphertext]
      cases hdec : P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) with
      | none => simp [hideRecvRes, hideSt, hee, Except.map]
      | some ct =>
        obtain ⟨c2, tag⟩ := ct
        dsimp only
        cases hk : s.keysAt (!generatorOf core.ep) core.ep with
        | none => simp [Except.map]
        | some ik =>
          dsimp only
          split_ifs <;> simp [hideRecvRes, hideSt, hideKey, hee, Except.map]
    · simp only [recvWith, hme, ↓reduceIte]
      hide_fallback_ne
  case ekReceivedCt1Sampled.ct1Ack core enc | ekReceivedCt1Sampled.ekCt1Ack core enc _ =>
    rw [hideSt_eq_of_ne e d (st := .ekReceivedCt1Sampled core enc) hee]
    by_cases hme : me = core.ep
    · subst hme
      simp [recvWith, idealOps, simOps, pinOps, completeCt2With, hideRecvRes, hideSt, hee,
        Except.map]
    · simp only [recvWith, hme, ↓reduceIte]
      hide_fallback_ne
  case ct1Sampled.ek core enc dec chunk =>
    rw [hideSt_eq_of_ne e d (st := .ct1Sampled core enc dec) hee]
    by_cases hme : me = core.ep
    · subst hme
      simp only [recvWith, recv, PartyState.epoch, lt_self_iff_false, ↓reduceIte]
      cases hdec : P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => simp [hideRecvRes, hideSt, hee, Except.map]
      | some vec =>
        simp only [CtSender.recvEk, Parameters.ekMatchesHeader]
        split_ifs with hvalid
        · simp [hideRecvRes, hideSt, hee, Except.map, hvalid]
        · simp [Except.map, hvalid]
    · simp only [recvWith]
      hide_fallback_ne
  case ct1Sampled.ekCt1Ack core enc dec chunk =>
    rw [hideSt_eq_of_ne e d (st := .ct1Sampled core enc dec) hee]
    by_cases hme : me = core.ep
    · subst hme
      simp only [recvWith, ↓reduceIte]
      cases hdec : P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => simp [hideRecvRes, hideSt, hee, Except.map]
      | some vec =>
        simp only [CtSender.recvEk, Parameters.ekMatchesHeader]
        split_ifs with hvalid
        · simp [idealOps, simOps, pinOps, completeCt2With, hideRecvRes, hideSt, hee, Except.map,
            hvalid]
        · simp [Except.map, hvalid]
    · simp only [recvWith, hme, ↓reduceIte]
      hide_fallback_ne
  case ct1Acknowledged.ek core dec chunk | ct1Acknowledged.ekCt1Ack core dec chunk =>
    rw [hideSt_eq_of_ne e d (st := .ct1Acknowledged core dec) hee]
    by_cases hme : me = core.ep
    · subst hme
      simp only [recvWith, ↓reduceIte]
      cases hdec : P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => simp [hideRecvRes, hideSt, hee, Except.map]
      | some vec =>
        simp only [CtSender.recvEk, Parameters.ekMatchesHeader]
        split_ifs with hvalid
        · simp [idealOps, simOps, pinOps, completeCt2With, hideRecvRes, hideSt, hee, Except.map,
            hvalid]
        · simp [Except.map, hvalid]
    · simp only [recvWith, hme, ↓reduceIte]
      hide_fallback_ne
  all_goals hide_generic

set_option maxHeartbeats 400000 in
-- The enumeration of the 11 states × 7 payloads exceeds the default budget.
include hEkSound in
/-- Under the pinned invariant, the receive of a message recorded by the peer of `party` by the
simulated instance from the hidden state is `hideRecvRes` of the receive of the honest instance. -/
theorem recvWith_sim_hide {s : GameState P AuthState}
    (hs : PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e s) (party : Bool) {n : ℕ}
    {msg : Message P.Sym} {tsnd : ℕ} (hentry : s.messagesAt (!party) n = some (msg, tsnd)) :
    recvWith (authAt auth e (fun a => auth.update a e (kemMat.epochKey e)))
        (idealOps (simOps kemMat.pk kemMat.ct1 kemMat.ct2 d e)
          (hideState e d (P.kdfOK d.k e) s))
        (hideSt e d (s.stateAt party)) msg =
      Except.map (hideRecvRes e d (P.kdfOK d.k e))
        (recvWith auth (idealOps (pinOps (some kemMat.kg) (some kemMat.enc) e) s)
          (s.stateAt party) msg) := by
  obtain ⟨⟨ik, T, hT, hpin⟩, hack⟩ := hs
  obtain ⟨st, hst⟩ : ∃ st, s.stateAt party = st := ⟨_, rfl⟩
  rw [hst]
  rcases eq_or_ne st.epoch e with hee | hee
  swap
  · exact recvWith_sim_hide_of_ne auth e d kemMat s st hee msg
  obtain ⟨me, payload⟩ := msg
  -- The state is at the simulated epoch.
  cases st <;> cases payload <;> simp only [PartyState.epoch] at hee
  case ekSentCt1Received.ct2 core dec chunk =>
    subst hee
    rw [show hideSt core.ep d (.ekSentCt1Received core dec) =
        .ekSentCt1Received { core with sk := d.sk } dec by simp [hideSt]]
    by_cases hme : me = core.ep
    · subst hme
      simp only [recvWith, ↓reduceIte, idealOps, recvCt2With,
        hideState_keysAt, hideKeys_self, authAt_update_self, authAt_verifyCiphertext]
      cases hdec : P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) with
      | none => simp [hideRecvRes, hideSt, Except.map]
      | some ct =>
        obtain ⟨c2, tag⟩ := ct
        dsimp only
        cases hk : s.keysAt (!generatorOf core.ep) core.ep with
        | none => simp [Except.map]
        | some ik =>
          have hik : ik = kemMat.epochKey core.ep :=
            PinnedInv.keys_eq auth ⟨⟨_, T, hT, hpin⟩, hack⟩ _ hk
          subst hik
          simp only [KEMMaterial.epochKey]
          split_ifs with hv <;> simp [hv, hideRecvRes, hideSt, hideKey, Except.map]
    · simp only [recvWith, hme, ↓reduceIte]
      hide_fallback
  case ekReceivedCt1Sampled.ct1Ack core enc | ekReceivedCt1Sampled.ekCt1Ack core enc _ =>
    subst hee
    obtain ⟨hhdr, hvec, hes⟩ :=
      PinnedInv.ekReceived_facts auth core.ep kemMat hT hpin party hst rfl
    rw [show hideSt core.ep d (.ekReceivedCt1Sampled core enc) =
        .ekReceivedCt1Sampled { core with encapsSt := d.es } enc by simp [hideSt]]
    by_cases hme : me = core.ep
    · subst hme
      simp [recvWith, idealOps, simOps, pinOps, completeCt2With, hideRecvRes, hideSt, hhdr,
        hvec, hes, KEMMaterial.ct2, Except.map]
    · simp only [recvWith, hme, ↓reduceIte]
      hide_fallback
  case ct1Sampled.ekCt1Ack core enc dec chunk =>
    subst hee
    obtain ⟨hhdr, hes, pk, sk, hkp, hrcv⟩ :=
      PinnedInv.ct1Sampled_facts auth core.ep kemMat hT hpin party hst rfl
    rw [show hideSt core.ep d (.ct1Sampled core enc dec) =
        .ct1Sampled { core with encapsSt := d.es } enc dec by simp [hideSt]]
    by_cases hme : me = core.ep
    · subst hme
      simp only [recvWith, ↓reduceIte]
      cases hdec : P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => simp [hideRecvRes, hideSt, Except.map]
      | some vec =>
        have hv := ek_decoded_eq auth hEkSound core.ep kemMat hT hpin party hentry
          (Or.inr rfl)
          hkp hrcv hdec
        subst hv
        have hvalid : P.det.validPK (P.det.toHeader kemMat.pk) (P.det.toVector kemMat.pk) = true :=
          (P.det.splitPK kemMat.pk).2
        simp [CtSender.recvEk, Parameters.ekMatchesHeader, idealOps, simOps, pinOps,
          completeCt2With, hideRecvRes, hideSt, hhdr, hes, hvalid, KEMMaterial.ct2, Except.map]
    · simp only [recvWith, hme, ↓reduceIte]
      hide_fallback
  case ct1Acknowledged.ek core dec chunk | ct1Acknowledged.ekCt1Ack core dec chunk =>
    subst hee
    obtain ⟨hhdr, hes, pk, sk, hkp, hrcv⟩ :=
      PinnedInv.ct1Acknowledged_facts auth core.ep kemMat hT hpin party hst rfl
    rw [show hideSt core.ep d (.ct1Acknowledged core dec) =
        .ct1Acknowledged { core with encapsSt := d.es } dec by simp [hideSt]]
    by_cases hme : me = core.ep
    · subst hme
      simp only [recvWith, ↓reduceIte]
      cases hdec : P.decEk.decodedPayload (P.decEk.addChunk dec chunk) with
      | none => simp [hideRecvRes, hideSt, Except.map]
      | some vec =>
        have hv := ek_decoded_eq auth hEkSound core.ep kemMat hT hpin party hentry
          (by first | exact .inl rfl | exact .inr rfl) hkp hrcv hdec
        subst hv
        have hvalid : P.det.validPK (P.det.toHeader kemMat.pk) (P.det.toVector kemMat.pk) = true :=
          (P.det.splitPK kemMat.pk).2
        simp [CtSender.recvEk, Parameters.ekMatchesHeader, idealOps, simOps, pinOps,
          completeCt2With, hideRecvRes, hideSt, hhdr, hes, hvalid, KEMMaterial.ct2, Except.map]
    · simp only [recvWith, hme, ↓reduceIte]
      hide_fallback
  all_goals (clear hT hpin hst hentry hEkSound; hide_generic)

end Receive

end SPQR
