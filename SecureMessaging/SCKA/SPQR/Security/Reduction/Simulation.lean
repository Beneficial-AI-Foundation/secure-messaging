/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Security.Reduction.Relation
public import SecureMessaging.SCKA.Security.Hybrids

/-!
# The simulation theorem

Let `adv` be an SCKA adversary against SPQR, `e` the simulated epoch (the challenge epoch drawn by
the reductions or the epoch before it), `kemMat` a possible KEM material of `e`
(`Reduction.Pinned`), `d` dummies (`Reduction.Relation`), and `ik` an initial key. For a candidate
key `kStar`, the pinned challenge `pinnedChallenge e kStar` (`SCKA.Security.Hybrids`) answers an
eligible challenge at `t` with a uniform key if `0 < t < e`, `kStar` if `t = e`, and the recorded
key otherwise.

Consider two games that run `adv` from `initState auth ik` against the security oracles with this
challenge oracle, return `false` at the first query that exposes `e`, and otherwise return the
output of `adv`:

- The *honest game* `Q_e(kemMat, kStar)` runs the honest instance `honestSchemeOf kemMat`, which
  pins both sampling phases of `e` to `kemMat`.
- The *simulated game* `Sim_e(kemMat, kStar)` runs the simulated instance `simSchemeOf`
  (`Reduction.Relation`) with the public values `kemMat.pk`, `kemMat.ct1`, `kemMat.ct2`, the
  dummies `d` in place of the secrets of `e`, and the authenticator update of `e` with
  `kemMat.epochKey e`.

Assume sound stream decoders. The simulation theorem is the acceptance equality
(`prEvent_stoppedRun_sim_eq_honest_pinned`):

```text
Pr[Sim_e(kemMat, kStar) = true] = Pr[Q_e(kemMat, kStar) = true].
```

It is an instance of `prEvent_stoppedRun_sim_eq_honest`, which holds for every challenge oracle
that records challenges and commutes with hiding at `e`, in games stopped at the first exposure of
`e` or of `e + 1`. The other instance used by the reductions,
`prEvent_stoppedRun_sim_eq_honest_challOf`, takes the challenge oracle of a challenge mode `μ`
with `μ e = true` and stops at `e + 1`.

**Results.** Let `τ := P.kdfOK d.k e` be the dummy epoch key and `hideState e d τ` the hiding map
(`Reduction.Relation`).

- From a state `s` satisfying the pinned invariant of `kemMat`, the stopped simulated query from
  `hideState e d τ s` has the joint response/state distribution of the stopped honest query from `s`
  with its successor hidden. The answers differ only on stopped paths: a corruption of the party
  holding a secret of `e`, and the coins of a leaking send sampling at `e` (`oracle_sim_hide`).
- The game-state updates of the sends and receives commute with hiding when, for some epoch key
  `k₀`, every key recorded by the peer at `e` and the key output at `e` are `k₀`
  (`sendUpdate_hideState`, `recvUpdate_hideState`).
-/

@[expose] public section

open OracleSpec OracleComp ErasureCodePayload.Streaming

namespace SPQR

open Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (sampleInitKey : ProbComp InitKey)
  (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
  (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
  (e : ℕ) {e' : ℕ} (d : Dummies P) (τ : P.EpochKey)

/-! ### Hiding the game-state updates -/

/-- The prefix check after recording a key reads only whether keys are recorded. -/
private theorem knownPrefix_update_hideKeys (keys : ℕ → Option P.EpochKey) (t : ℕ)
    (k k' : P.EpochKey)
    (n : ℕ) :
    SCKAScheme.knownPrefix (Function.update (hideKeys e τ keys) t (some k')) n =
      SCKAScheme.knownPrefix (Function.update keys t (some k)) n := by
  simp only [SCKAScheme.knownPrefix]
  congr 1
  funext u
  by_cases hu : u = t
  · subst hu
    simp
  · simp [Function.update_of_ne hu]

section Updates

variable [DecidableEq P.EpochKey]

/-- The consistency test of a recorded key is unchanged by hiding when the keys at `e` of the
table and the key recorded at `e` are `k₀`. -/
private theorem hideKeys_beq_hideKey (keys : ℕ → Option P.EpochKey) (t : ℕ) (key k₀ : P.EpochKey)
    (hkeys : ∀ k, keys e = some k → k = k₀) (hkey : t = e → key = k₀) :
    (hideKeys e τ keys t == some (if t = e then τ else key)) = (keys t == some key) := by
  by_cases ht : t = e
  · subst ht
    cases h : keys t with
    | none => simp [hideKeys, h]
    | some k =>
      obtain rfl := hkeys k h
      simp [hideKeys, h, hkey rfl]
  · simp [hideKeys, ht]


/-- The key table of `party` after its send records its output key. -/
private theorem keysAt_sendUpdate_self (s : GameState P AuthState) (party : Bool)
    (r : SendResult P AuthState) {t : ℕ} {key : P.EpochKey} (hk : r.outputKey = some (t, key)) :
    (sendUpdate s party r).keysAt party t = some key := by
  cases party <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, GameState.keysAt, hk]

/-- The key table of `party` after its receive records its output key. -/
private theorem keysAt_recvUpdate_self (s : GameState P AuthState) (party : Bool) (tsnd : ℕ)
    (r : RecvResult P AuthState) (trcv : ℕ) {t : ℕ} {key : P.EpochKey}
    (hk : r.outputKey = some (t, key)) :
    (recvUpdate s party tsnd r trcv).keysAt party t = some key := by
  cases party <;>
    simp [recvUpdate, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, GameState.keysAt, hk]

/-- The send update commutes with hiding, when every key recorded by the peer at `e` and the key
output at `e` are `k₀`. -/
theorem sendUpdate_hideState (s : GameState P AuthState) (party : Bool)
    (r : SendResult P AuthState) (k₀ : P.EpochKey)
    (hkeys : ∀ k, s.keysAt (!party) e = some k → k = k₀)
    (hr : ∀ key, r.outputKey = some (e, key) → key = k₀) :
    sendUpdate (hideState e d τ s) party (hideSendRes e d τ r) =
      hideState e d τ (sendUpdate s party r) := by
  rcases hk : r.outputKey with _ | ⟨tI, key⟩
  · cases party <;>
      simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hideSendRes, hideState, hk]
  · have hkey : tI = e → key = k₀ := fun h => hr key (h ▸ hk)
    have hb := hideKeys_beq_hideKey e τ (s.keysAt (!party)) tI key k₀ hkeys hkey
    cases party
    · simp only [GameState.keysAt, Bool.not_false, ↓reduceIte] at hb
      simp [sendUpdate, SCKAScheme.sendBUpdate, hideSendRes, hideState, hideKey, hk,
        hideKeys_update, hb, knownPrefix_update_hideKeys e τ s.keyB tI key]
    · simp only [GameState.keysAt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hb
      simp [sendUpdate, SCKAScheme.sendAUpdate, hideSendRes, hideState, hideKey, hk,
        hideKeys_update, hb, knownPrefix_update_hideKeys e τ s.keyA tI key]

/-- The receive update commutes with hiding, when every key recorded by the peer at `e` and the
key output at `e` are `k₀`. -/
theorem recvUpdate_hideState (s : GameState P AuthState) (party : Bool) (tsnd : ℕ)
    (r : RecvResult P AuthState) (trcv : ℕ) (k₀ : P.EpochKey)
    (hkeys : ∀ k, s.keysAt (!party) e = some k → k = k₀)
    (hr : ∀ key, r.outputKey = some (e, key) → key = k₀) :
    recvUpdate (hideState e d τ s) party tsnd (hideRecvRes e d τ r) trcv =
      hideState e d τ (recvUpdate s party tsnd r trcv) := by
  rcases hk : r.outputKey with _ | ⟨tI, key⟩
  · cases party <;>
      simp [recvUpdate, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, hideRecvRes, hideState, hk]
  · have hkey : tI = e → key = k₀ := fun h => hr key (h ▸ hk)
    have hb := hideKeys_beq_hideKey e τ (s.keysAt (!party)) tI key k₀ hkeys hkey
    cases party
    · simp only [GameState.keysAt, Bool.not_false, ↓reduceIte] at hb
      simp [recvUpdate, SCKAScheme.recvBUpdate, hideRecvRes, hideState, hideKey, hk,
        hideKeys_update, hb, knownPrefix_update_hideKeys e τ s.keyB tI key]
    · simp only [GameState.keysAt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hb
      simp [recvUpdate, SCKAScheme.recvAUpdate, hideRecvRes, hideState, hideKey, hk,
        hideKeys_update, hb, knownPrefix_update_hideKeys e τ s.keyA tI key]

end Updates

/-! ### The exposure policy under hiding -/

/-- Hiding does not change the epochs exposed by a corruption. -/
private theorem vuln_corrupt_hideSt (st : PartyState P AuthState) :
    (vuln P AuthState).corrupt (hideSt e d st) = (vuln P AuthState).corrupt st := by
  simp [vuln, hideSt_epoch]

/-- Hiding does not change the epochs exposed by a leaking send. -/
private theorem vuln_rleak_hideSt (st : PartyState P AuthState)
    (rand : Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand) :
    (vuln P AuthState).rleak (hideSt e d st) rand = (vuln P AuthState).rleak st rand := by
  cases rand <;> simp [vuln, hideSt_epoch]

/-- For `e' = e` or `e' = e + 1`, a state whose corruption does not expose `e'` is unchanged by
hiding at `e`. -/
private theorem hideSt_eq_self_of_not_mem_corrupt (he' : e' = e ∨ e' = e + 1)
    {st : PartyState P AuthState} (h : e' ∉ (vuln P AuthState).corrupt st) :
    hideSt e d st = st := by
  by_cases hsec : st.holdsSecret
  · refine hideSt_eq_of_ne e d fun hne => h ?_
    have hmem := mem_vuln_corrupt_of_holdsSecret hsec
    rcases he' with rfl | rfl
    · rw [← hne]
      exact hmem.1
    · rw [← hne]
      exact hmem.2
  · exact hideSt_eq_self_of_not_holdsSecret e d (Bool.eq_false_iff.mpr hsec)

/-- A sampling state is `keysUnsampled` or `headerReceived`. -/
private theorem PartyState.samples_cases {st : PartyState P AuthState} (h : st.samples = true) :
    (∃ core, st = .keysUnsampled core) ∨ (∃ core dec, st = .headerReceived core dec) := by
  cases st <;> simp [PartyState.samples] at h ⊢

/-! ### The queries -/

section Queries

variable (kemMat : KEMMaterial P)

/-- The masked response/state pairs of A's corruption agree from the hidden state and from the
state: the response differs only when the corruption exposes `e`. -/
private theorem oracleCorruptA_sim_hide (he' : e' = e ∨ e' = e + 1) (s : GameState P AuthState) :
    (fun y : Option (PartyState P AuthState) × GameState P AuthState =>
        (if decide (e' ∈ y.2.exposed) then none else some y.1, y.2)) <$>
      (SCKAScheme.oracleCorruptA (vuln P AuthState).corrupt (PartyState P AuthState)
        P.EpochKey (Message P.Sym) ()).run (hideState e d τ s) =
    (fun y : Option (PartyState P AuthState) × GameState P AuthState =>
        (if decide (e' ∈ y.2.exposed) then none else some y.1, hideState e d τ y.2)) <$>
      (SCKAScheme.oracleCorruptA (vuln P AuthState).corrupt (PartyState P AuthState)
        P.EpochKey (Message P.Sym) ()).run s := by
  rw [SCKAScheme.oracleCorruptA_run, SCKAScheme.oracleCorruptA_run, hideState_stA,
    hideState_challenged, vuln_corrupt_hideSt]
  split_ifs with hg
  · by_cases he : e' ∈ s.exposed <;> simp [he]
  · simp only [map_pure, hideState_exposed]
    by_cases he : e' ∈ s.exposed ∪ (vuln P AuthState).corrupt s.stA
    · simp [he, hideState]
    · have hst := hideSt_eq_self_of_not_mem_corrupt e d he'
        (fun h => he (Finset.mem_union_right _ h))
      simp [he, hideState, hst]

/-- B version of `oracleCorruptA_sim_hide`. -/
private theorem oracleCorruptB_sim_hide (he' : e' = e ∨ e' = e + 1) (s : GameState P AuthState) :
    (fun y : Option (PartyState P AuthState) × GameState P AuthState =>
        (if decide (e' ∈ y.2.exposed) then none else some y.1, y.2)) <$>
      (SCKAScheme.oracleCorruptB (vuln P AuthState).corrupt (PartyState P AuthState)
        P.EpochKey (Message P.Sym) ()).run (hideState e d τ s) =
    (fun y : Option (PartyState P AuthState) × GameState P AuthState =>
        (if decide (e' ∈ y.2.exposed) then none else some y.1, hideState e d τ y.2)) <$>
      (SCKAScheme.oracleCorruptB (vuln P AuthState).corrupt (PartyState P AuthState)
        P.EpochKey (Message P.Sym) ()).run s := by
  rw [SCKAScheme.oracleCorruptB_run, SCKAScheme.oracleCorruptB_run, hideState_stB,
    hideState_challenged, vuln_corrupt_hideSt]
  split_ifs with hg
  · by_cases he : e' ∈ s.exposed <;> simp [he]
  · simp only [map_pure, hideState_exposed]
    by_cases he : e' ∈ s.exposed ∪ (vuln P AuthState).corrupt s.stB
    · simp [he, hideState]
    · have hst := hideSt_eq_self_of_not_mem_corrupt e d he'
        (fun h => he (Finset.mem_union_right _ h))
      simp [he, hideState, hst]

section Challenge

variable [SampleableType P.EpochKey]

/-- The challenge oracle pinned at `e` commutes with hiding: at `e` it reads only whether a key
is recorded, and the other epochs are not hidden. -/
private theorem pinnedChallenge_run_hideState (kStar : P.EpochKey) (t : ℕ)
    (s : GameState P AuthState) :
    (SCKAScheme.pinnedChallenge e kStar t).run (hideState e d τ s) =
      Prod.map id (hideState e d τ) <$> (SCKAScheme.pinnedChallenge e kStar t).run s := by
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [SCKAScheme.pinnedChallenge, SCKAScheme.pinnedChallengeWith, hg]
  · by_cases ht : t = e
    · subst ht
      cases hA : s.keyA t <;> cases hB : s.keyB t <;>
        simp [SCKAScheme.pinnedChallenge, SCKAScheme.pinnedChallengeWith, hg, hA, hB, hideKeys_self,
          StateT.run_bind, StateT.run_set, StateT.run_pure, hideState]
    · cases hA : s.keyA t <;> cases hB : s.keyB t <;> by_cases hr : 0 < t ∧ t < e <;>
        simp [SCKAScheme.pinnedChallenge, SCKAScheme.pinnedChallengeWith, hg, hA, hB, ht, hr,
          hideKeys_of_ne _ _ _ ht, StateT.run_bind, StateT.run_set, StateT.run_pure,
          StateT.run_monadLift, monadLift_self, hideState]

/-- The challenge oracle of a challenge mode with `mode e = true` commutes with hiding: at `e` it
answers with a uniform key and reads only whether a key is recorded, and the other epochs are not
hidden. -/
theorem challOf_run_hideState (mode : ℕ → Bool) (hmode : mode e = true) (t : ℕ)
    (s : GameState P AuthState) :
    (SCKAScheme.challOf mode t).run (hideState e d τ s) =
      Prod.map id (hideState e d τ) <$> (SCKAScheme.challOf mode t).run s := by
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [SCKAScheme.challOf, SCKAScheme.oracleChall, hg]
  · by_cases ht : t = e
    · subst ht
      cases hA : s.keyA t <;> cases hB : s.keyB t <;>
        simp [SCKAScheme.challOf, SCKAScheme.oracleChall, hg, hA, hB, hmode, hideKeys_self,
          StateT.run_bind, StateT.run_set, StateT.run_pure, StateT.run_monadLift,
          monadLift_self, hideState]
    · cases hA : s.keyA t <;> cases hB : s.keyB t <;> cases hm : mode t <;>
        simp [SCKAScheme.challOf, SCKAScheme.oracleChall, hg, hA, hB, hm,
          hideKeys_of_ne _ _ _ ht, StateT.run_bind, StateT.run_set, StateT.run_pure,
          StateT.run_monadLift, monadLift_self, hideState]

end Challenge

/-- The pinned operations of a possible KEM material are possible at every state under its pinned
invariant. -/
private theorem material_pinOps_possibleAt (hm : kemMat ∈ support (sampleMaterial))
    {s : GameState P AuthState} (hs : PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e s)
    (party : Bool) : OpsPossibleAt (pinOps (some kemMat.kg) (some kemMat.enc) e)
      (s.stateAt party) :=
  pinOps_possibleAt auth (kg? := some kemMat.kg) (enc? := some kemMat.enc)
    (fun kg h => by cases h; exact (sampleMaterial_ordinary_support kemMat hm).1)
    (fun kg enc h1 h2 => by cases h1; cases h2; exact
      (sampleMaterial_ordinary_support kemMat hm).2)
    (fun _ _ => ⟨kemMat.kg, rfl⟩) hs party

/-- The key output at `e` by a possible send of `party` in the honest instance is
`kemMat.epochKey e`. -/
private theorem honest_send_key_eq (hm : kemMat ∈ support (sampleMaterial))
    {s : GameState P AuthState} (hs : PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e s)
    (party : Bool) {r : SendResult P AuthState}
    (hr : r ∈ support (sendWith auth (pinOps (some kemMat.kg) (some kemMat.enc) e)
      (s.stateAt party)))
    {key : P.EpochKey} (hkey : r.outputKey = some (e, key)) : key = kemMat.epochKey e := by
  classical
  exact PinnedInv.keys_eq auth
    (pinnedInv_sendUpdate auth (kg? := some kemMat.kg) (enc? := some kemMat.enc) party
      (material_pinOps_possibleAt auth e kemMat hm hs party) hs hr) party
    (keysAt_sendUpdate_self s party r hkey)

/-! ### The leaking sends -/

/-- The result of the key-generation send from `core` with the key pair `(pk, sk)`. -/
def hdrResult (core : EkSender.KeysUnsampled AuthState) (pk : P.PK) (sk : P.SK) :
    SendResult P AuthState :=
  let hdr := P.det.toHeader pk
  let tag := auth.macHeader core.authSt core.ep hdr
  let core' : EkSender.HeaderSent P AuthState := ⟨core.ep, core.authSt, pk, sk⟩
  let (chunk, enc) := (EncoderState.init P.ecpHdr (hdr, tag)).nextChunk
  ⟨⟨core.ep, .hdr chunk⟩, core.ep - 1, none, .keysSampled core' enc⟩

/-- The result of the first-stage send from `core` with the vector decoder `dec` and the first
stage `(es, c1, k)`. -/
def ct1Result (core : CtSender.HeaderReceived P AuthState)
    (dec : P.decEk.D) (es : P.det.St) (c1 : P.det.C₁) (k : P.K) :
    SendResult P AuthState :=
  let ik := P.kdfOK k core.ep
  let core' : CtSender.Ct1Sent P AuthState :=
    ⟨core.ep, auth.update core.authSt core.ep ik, core.hdr, es, c1⟩
  let (chunk, enc) := (EncoderState.init P.ecpCt1 c1).nextChunk
  ⟨⟨core.ep, .ct1 chunk⟩, core.ep - 1, some (core.ep, ik), .ct1Sampled core' enc dec⟩

/-- The pinned leaking send from `keysUnsampled` at `e` returns the pinned key pair and coins. -/
theorem sendRleakWith_pinOps_keysUnsampled (kg : (P.PK × P.SK) × P.det.KeygenRand)
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand))
    (core : EkSender.KeysUnsampled AuthState) (he : core.ep = e) :
    sendRleakWith auth (pinOps (some kg) enc? e) (.keysUnsampled core) =
      pure (hdrResult auth core kg.1.1 kg.1.2, .keygen kg.2) := by
  subst he
  simp only [sendRleakWith, pinOps_keygenRleak_self, Option.elim, pure_bind]
  rfl

/-- The simulated leaking send from `keysUnsampled` at `e` returns `kemMat.pk` with the dummy secret
key and fresh coins: the hidden honest result with the coins of a fresh key generation. -/
private theorem sendRleakWith_simOps_keysUnsampled (core : EkSender.KeysUnsampled AuthState)
    (he : core.ep = e) :
    sendRleakWith (authAt auth e (fun a => auth.update a e (kemMat.epochKey e)))
        (simOps kemMat.pk kemMat.ct1 kemMat.ct2 d e) (.keysUnsampled core) =
      (fun res => (hideSendRes e d τ (hdrResult auth core kemMat.pk kemMat.sk), .keygen res.2)) <$>
        P.det.toRandLeak.keygenRleak := by
  subst he
  simp only [sendRleakWith, simOps, ↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  refine bind_congr fun res => ?_
  simp [hideSendRes, hdrResult, hideSt]

/-- The pinned leaking send from `headerReceived` at `e` returns the pinned first stage and
coins. -/
theorem sendRleakWith_pinOps_headerReceived (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc : (P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)
    (core : CtSender.HeaderReceived P AuthState) (dec : P.decEk.D)
    (he : core.ep = e) :
    sendRleakWith auth (pinOps kg? (some enc) e) (.headerReceived core dec) =
      pure (ct1Result auth core dec enc.1.1 enc.1.2.1 enc.1.2.2, .encaps1 enc.2) := by
  subst he
  simp only [sendRleakWith, pinOps_encaps1Rleak_self, Option.elim, pure_bind]
  rfl

/-- The simulated leaking send from `headerReceived` at `e` returns `kemMat.ct1` with the dummy
state and KEM key and fresh coins: the hidden honest result with the coins of a fresh first stage.
-/
private theorem sendRleakWith_simOps_headerReceived (core : CtSender.HeaderReceived P AuthState)
    (dec : P.decEk.D) (he : core.ep = e) :
    sendRleakWith (authAt auth e (fun a => auth.update a e (kemMat.epochKey e)))
        (simOps kemMat.pk kemMat.ct1 kemMat.ct2 d e) (.headerReceived core dec) =
      (fun res => (hideSendRes e d (P.kdfOK d.k e)
        (ct1Result auth core dec kemMat.es kemMat.ct1 kemMat.key),
        .encaps1 res.2)) <$> P.det.toRandLeak.encaps1Rleak core.hdr := by
  subst he
  simp only [sendRleakWith, simOps, ↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  refine bind_congr fun res => ?_
  simp [hideSendRes, ct1Result, hideSt, hideKey, KEMMaterial.epochKey]


include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- The key output at `e` by an accepting receive of `party` in the honest instance, of a message
recorded by the peer, is `kemMat.epochKey e`. -/
private theorem honest_recv_key_eq
    {s : GameState P AuthState} (hs : PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e s)
    (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    (hentry : s.messagesAt (!party) n = some (msg, tsnd)) {r : RecvResult P AuthState}
    (hr : recvWith auth (idealOps (pinOps (some kemMat.kg) (some kemMat.enc) e) s)
      (s.stateAt party) msg =
      .ok r) {key : P.EpochKey} (hkey : r.outputKey = some (e, key)) : key = kemMat.epochKey e := by
  classical
  exact PinnedInv.keys_eq auth
    (pinnedInv_recvUpdate auth (kg? := some kemMat.kg)
      (enc? := some kemMat.enc) hHdrSound hEkSound
      hCt1Sound hCt2Sound hs party hentry hr) party
    (keysAt_recvUpdate_self s party tsnd r r.receivingEpoch hkey)

variable [DecidableEq P.EpochKey]

/-- The simulated instance at the hidden state: `simSchemeOf` with the public values of `kemMat` and
the update of `e` with `kemMat.epochKey e`. -/
local notation "simAt" s =>
  simSchemeOf auth sampleInitKey e d kemMat.pk kemMat.ct1 kemMat.ct2
    (fun a => auth.update a e (kemMat.epochKey e))
    (hideState e d (P.kdfOK d.k e) s)

/-- The honest instance at a state. -/
local notation "honAt" s => honestSchemeOf auth sampleInitKey e kemMat s

/-- A's ordinary send of the simulated instance from the hidden state has the distribution of the
send of the honest instance, with the state hidden. -/
private theorem oracleSendA_sim_hide (hm : kemMat ∈ support (sampleMaterial))
    (s : GameState P AuthState) (hs : PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e s) :
    (SCKAScheme.oracleSendA (simAt s) ()).run (hideState e d (P.kdfOK d.k e) s) =ᵈ
      Prod.map id (hideState e d (P.kdfOK d.k e)) <$>
        (SCKAScheme.oracleSendA (honAt s) ()).run s := by
  rw [SCKAScheme.oracleSendA_run_eq, SCKAScheme.oracleSendA_run_eq, hideState_stA]
  simp only [schemeWith, sendWith_idealOps, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  refine ((sendWith_sim_hide auth e d kemMat s.stA).bind_left _).trans ?_
  rw [bind_map_left]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun r hr =>
    ToVCVio.evalDistEq_of_eq (congrArg pure ?_)
  have h := sendUpdate_hideState e d (P.kdfOK d.k e) s true r (kemMat.epochKey e)
    (fun k hk => PinnedInv.keys_eq auth hs _ hk)
    (fun key hkey => honest_send_key_eq auth e kemMat hm hs true hr hkey)
  simp only [sendUpdate, ↓reduceIte, hideSendRes] at h
  simp only [hideSendRes]
  rw [h]
  simp [Option.map_map, Function.comp_def, hideKey, Prod.map]

/-- B version of `oracleSendA_sim_hide`. -/
private theorem oracleSendB_sim_hide (hm : kemMat ∈ support (sampleMaterial))
    (s : GameState P AuthState) (hs : PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e s) :
    (SCKAScheme.oracleSendB (simAt s) ()).run (hideState e d (P.kdfOK d.k e) s) =ᵈ
      Prod.map id (hideState e d (P.kdfOK d.k e)) <$>
        (SCKAScheme.oracleSendB (honAt s) ()).run s := by
  rw [SCKAScheme.oracleSendB_run_eq, SCKAScheme.oracleSendB_run_eq, hideState_stB]
  simp only [schemeWith, sendWith_idealOps, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  refine ((sendWith_sim_hide auth e d kemMat s.stB).bind_left _).trans ?_
  rw [bind_map_left]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun r hr =>
    ToVCVio.evalDistEq_of_eq (congrArg pure ?_)
  have h := sendUpdate_hideState e d (P.kdfOK d.k e) s false r (kemMat.epochKey e)
    (fun k hk => PinnedInv.keys_eq auth hs _ hk)
    (fun key hkey => honest_send_key_eq auth e kemMat hm hs false hr hkey)
  simp only [sendUpdate, Bool.false_eq_true, ↓reduceIte, hideSendRes] at h
  simp only [hideSendRes]
  rw [h]
  simp [Option.map_map, Function.comp_def, hideKey, Prod.map]

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- A's receive of the simulated instance from the hidden state is the receive of the honest
instance, with the state hidden. -/
private theorem oracleRecvA_sim_hide
    (s : GameState P AuthState) (hs : PinnedInv auth (some kemMat.kg.1)
      (some kemMat.enc.1) e s) (n : ℕ) :
    (SCKAScheme.oracleRecvA (simAt s) n).run (hideState e d (P.kdfOK d.k e) s) =
      Prod.map id (hideState e d (P.kdfOK d.k e)) <$>
        (SCKAScheme.oracleRecvA (honAt s) n).run s := by
  cases hm : s.msgB n with
  | none =>
    rw [SCKAScheme.oracleRecvA_run_eq_of_none _ _ hm,
      SCKAScheme.oracleRecvA_run_eq_of_none _ _ (by simpa using hm)]
    simp
  | some entry =>
    obtain ⟨ρ, tsnd⟩ := entry
    have hentry : s.messagesAt (!true) n = some (ρ, tsnd) := hm
    have hm' : (hideState e d (P.kdfOK d.k e) s).msgB n = some (ρ, tsnd) := by simpa using hm
    have hrel := recvWith_sim_hide auth hEkSound e d kemMat hs true hentry
    simp only [GameState.stateAt, ↓reduceIte] at hrel
    rcases hr : recvWith auth (idealOps (pinOps (some kemMat.kg) (some kemMat.enc) e) s) s.stA ρ
      with err | r
    · rw [SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ hm' (by simp [schemeWith, recvSCKAWith,
        hrel, hr, Except.map]), SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ hm (by
        simp [schemeWith, recvSCKAWith, hr])]
      simp [hideState]
    · rw [SCKAScheme.oracleRecvA_run_eq_of_accept _ _ hm' (keyOpt := (hideRecvRes e d
        (P.kdfOK d.k e) r).outputKey) (trcv := r.receivingEpoch) (stA' := hideSt e d r.state)
        (by simp [schemeWith, recvSCKAWith, hrel, hr, hideRecvRes, Except.map]),
        SCKAScheme.oracleRecvA_run_eq_of_accept _ _ hm (keyOpt := r.outputKey)
        (trcv := r.receivingEpoch) (stA' := r.state) (by simp [schemeWith, recvSCKAWith, hr]),
        map_pure]
      have h := recvUpdate_hideState e d (P.kdfOK d.k e) s true tsnd r r.receivingEpoch
        (kemMat.epochKey e) (fun k hk => PinnedInv.keys_eq auth hs _ hk)
        (fun key hkey => honest_recv_key_eq auth hHdrSound hEkSound hCt1Sound
          hCt2Sound e kemMat hs true hentry hr hkey)
      simp only [recvUpdate, ↓reduceIte, hideRecvRes] at h
      simp only [hideRecvRes]
      rw [h]
      simp [Option.map_map, Function.comp_def, hideKey, Prod.map]

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- B version of `oracleRecvA_sim_hide`. -/
private theorem oracleRecvB_sim_hide
    (s : GameState P AuthState) (hs : PinnedInv auth (some kemMat.kg.1)
      (some kemMat.enc.1) e s) (n : ℕ) :
    (SCKAScheme.oracleRecvB (simAt s) n).run (hideState e d (P.kdfOK d.k e) s) =
      Prod.map id (hideState e d (P.kdfOK d.k e)) <$>
        (SCKAScheme.oracleRecvB (honAt s) n).run s := by
  cases hm : s.msgA n with
  | none =>
    rw [SCKAScheme.oracleRecvB_run_eq_of_none _ _ hm,
      SCKAScheme.oracleRecvB_run_eq_of_none _ _ (by simpa using hm)]
    simp
  | some entry =>
    obtain ⟨ρ, tsnd⟩ := entry
    have hentry : s.messagesAt (!false) n = some (ρ, tsnd) := hm
    have hm' : (hideState e d (P.kdfOK d.k e) s).msgA n = some (ρ, tsnd) := by simpa using hm
    have hrel := recvWith_sim_hide auth hEkSound e d kemMat hs false hentry
    simp only [GameState.stateAt, Bool.false_eq_true, ↓reduceIte] at hrel
    rcases hr : recvWith auth (idealOps (pinOps (some kemMat.kg) (some kemMat.enc) e) s) s.stB ρ
      with err | r
    · rw [SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ hm' (by simp [schemeWith, recvSCKAWith,
        hrel, hr, Except.map]), SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ hm (by
        simp [schemeWith, recvSCKAWith, hr])]
      simp [hideState]
    · rw [SCKAScheme.oracleRecvB_run_eq_of_accept _ _ hm' (keyOpt := (hideRecvRes e d
        (P.kdfOK d.k e) r).outputKey) (trcv := r.receivingEpoch) (stB' := hideSt e d r.state)
        (by simp [schemeWith, recvSCKAWith, hrel, hr, hideRecvRes, Except.map]),
        SCKAScheme.oracleRecvB_run_eq_of_accept _ _ hm (keyOpt := r.outputKey)
        (trcv := r.receivingEpoch) (stB' := r.state) (by simp [schemeWith, recvSCKAWith, hr]),
        map_pure]
      have h := recvUpdate_hideState e d (P.kdfOK d.k e) s false tsnd r r.receivingEpoch
        (kemMat.epochKey e) (fun k hk => PinnedInv.keys_eq auth hs _ hk)
        (fun key hkey => honest_recv_key_eq auth hHdrSound hEkSound hCt1Sound
          hCt2Sound e kemMat hs false hentry hr hkey)
      simp only [recvUpdate, Bool.false_eq_true, ↓reduceIte, hideRecvRes] at h
      simp only [hideRecvRes]
      rw [h]
      simp [Option.map_map, Function.comp_def, hideKey, Prod.map]

/-- The masked response/state pairs of A's leaking send agree from the hidden state and from the
state: the response differs only for a send sampling at `e`, which exposes `e`. -/
private theorem oracleSendArleak_sim_hide (hm : kemMat ∈ support (sampleMaterial))
    (he' : e' = e ∨ e' = e + 1)
    (s : GameState P AuthState) (hs : PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e s) :
    (fun y : Option (ℕ × Option ℕ × Message P.Sym ×
          Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand) × GameState P AuthState =>
        (if decide (e' ∈ y.2.exposed) then none else some y.1, y.2)) <$>
      (SCKAScheme.oracleSendArleak (vuln P AuthState).rleak (simAt s) ()).run
        (hideState e d (P.kdfOK d.k e) s) =ᵈ
    (fun y : Option (ℕ × Option ℕ × Message P.Sym ×
          Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand) × GameState P AuthState =>
        (if decide (e' ∈ y.2.exposed) then none else some y.1,
          hideState e d (P.kdfOK d.k e) y.2)) <$>
      (SCKAScheme.oracleSendArleak (vuln P AuthState).rleak (honAt s) ()).run s := by
  rw [SCKAScheme.oracleSendArleak_run_eq, SCKAScheme.oracleSendArleak_run_eq, hideState_stA]
  simp only [schemeWith, sendRleakWith_idealOps, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  have hkeys : ∀ k, s.keysAt (!true) e = some k → k = kemMat.epochKey e :=
    fun k hk => PinnedInv.keys_eq auth hs _ hk
  by_cases hsamp : s.stA.samples = true ∧ s.stA.epoch = e
  · rcases PartyState.samples_cases hsamp.1 with ⟨core, hst⟩ | ⟨core, dec, hst⟩
    · have he : core.ep = e := by simpa [hst, PartyState.epoch] using hsamp.2
      subst he
      have h := sendUpdate_hideState core.ep d (P.kdfOK d.k core.ep) s true
        (hdrResult auth core kemMat.pk kemMat.sk) (kemMat.epochKey core.ep) hkeys
        (fun key hkey => by simp [hdrResult] at hkey)
      simp only [sendUpdate, ↓reduceIte] at h
      rw [hst, hideSt_eq_self_of_not_holdsSecret core.ep d rfl,
        sendRleakWith_simOps_keysUnsampled auth core.ep d (P.kdfOK d.k core.ep) kemMat core rfl,
        sendRleakWith_pinOps_keysUnsampled auth core.ep kemMat.kg (some kemMat.enc) core rfl]
      simp only [KEMMaterial.pk, KEMMaterial.sk] at h ⊢
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      refine OracleComp.EvalDistEq.bind_const_of_support P.det.toRandLeak.keygenRleak fun res _ =>
        ?_
      refine congrArg pure ?_
      simp only [vuln, PartyState.epoch, hideState_challenged]
      by_cases hc : ({core.ep, core.ep + 1} ∩ s.challenged : Finset ℕ) = ∅
      · have hx : e' ∈ s.exposed ∪ {core.ep, core.ep + 1} := by
          rcases he' with rfl | rfl <;> simp
        simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte, hx, decide_true, hideState_exposed]
        rw [h]
        simp [hideState]
      · simp [hc]
    · have he : core.ep = e := by simpa [hst, PartyState.epoch] using hsamp.2
      subst he
      have h := sendUpdate_hideState core.ep d (P.kdfOK d.k core.ep) s true
        (ct1Result auth core dec kemMat.es kemMat.ct1 kemMat.key) (kemMat.epochKey core.ep) hkeys
        (fun key hkey => by
          simp only [ct1Result, Option.some.injEq, Prod.mk.injEq, true_and] at hkey
          exact hkey.symm)
      simp only [sendUpdate, ↓reduceIte] at h
      rw [hst, hideSt_eq_self_of_not_holdsSecret core.ep d rfl,
        sendRleakWith_simOps_headerReceived auth core.ep d kemMat core dec rfl,
        sendRleakWith_pinOps_headerReceived auth core.ep
          (some kemMat.kg) kemMat.enc core dec rfl]
      simp only [KEMMaterial.es, KEMMaterial.ct1, KEMMaterial.key] at h ⊢
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      refine OracleComp.EvalDistEq.bind_const_of_support (P.det.toRandLeak.encaps1Rleak core.hdr)
        fun res _ => ?_
      refine congrArg pure ?_
      simp only [vuln, PartyState.epoch, hideState_challenged]
      by_cases hc : ({core.ep, core.ep + 1} ∩ s.challenged : Finset ℕ) = ∅
      · have hx : e' ∈ s.exposed ∪ {core.ep, core.ep + 1} := by
          rcases he' with rfl | rfl <;> simp
        simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte, hx, decide_true, hideState_exposed]
        rw [h]
        simp [hideState]
      · simp [hc]
  · rw [sendRleakWith_sim_hide_of_not_samples auth e d kemMat s.stA hsamp]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    refine OracleComp.EvalDistEq.bind_congr_of_support _ fun res hres =>
      ToVCVio.evalDistEq_of_eq (congrArg pure ?_)
    obtain ⟨r, rand⟩ := res
    have hr : r ∈ support (sendWith auth
      (pinOps (some kemMat.kg) (some kemMat.enc) e) s.stA) := by
      simp only [sendWith, support_map, Set.mem_image]
      exact ⟨(r, rand), hres, rfl⟩
    have h := sendUpdate_hideState e d (P.kdfOK d.k e) s true r (kemMat.epochKey e) hkeys
      (fun key hkey => honest_send_key_eq auth e kemMat hm hs true hr hkey)
    simp only [sendUpdate, ↓reduceIte, hideSendRes] at h
    simp only [Prod.map, id, vuln_rleak_hideSt, hideSendRes, hideState_challenged]
    by_cases hg : (vuln P AuthState).rleak s.stA rand ∩ s.challenged ≠ ∅
    · rw [ite_eq_left hg, ite_eq_left hg]
      by_cases he : e' ∈ s.exposed <;> simp [he]
    · rw [ite_eq_right hg, ite_eq_right hg]
      simp only [hideState_exposed]
      rw [h]
      simp [Option.map_map, Function.comp_def, hideKey, hideState]

/-- B version of `oracleSendArleak_sim_hide`. -/
private theorem oracleSendBrleak_sim_hide (hm : kemMat ∈ support (sampleMaterial))
    (he' : e' = e ∨ e' = e + 1)
    (s : GameState P AuthState) (hs : PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e s) :
    (fun y : Option (ℕ × Option ℕ × Message P.Sym ×
          Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand) × GameState P AuthState =>
        (if decide (e' ∈ y.2.exposed) then none else some y.1, y.2)) <$>
      (SCKAScheme.oracleSendBrleak (vuln P AuthState).rleak (simAt s) ()).run
        (hideState e d (P.kdfOK d.k e) s) =ᵈ
    (fun y : Option (ℕ × Option ℕ × Message P.Sym ×
          Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand) × GameState P AuthState =>
        (if decide (e' ∈ y.2.exposed) then none else some y.1,
          hideState e d (P.kdfOK d.k e) y.2)) <$>
      (SCKAScheme.oracleSendBrleak (vuln P AuthState).rleak (honAt s) ()).run s := by
  rw [SCKAScheme.oracleSendBrleak_run_eq, SCKAScheme.oracleSendBrleak_run_eq, hideState_stB]
  simp only [schemeWith, sendRleakWith_idealOps, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  have hkeys : ∀ k, s.keysAt (!false) e = some k → k = kemMat.epochKey e :=
    fun k hk => PinnedInv.keys_eq auth hs _ hk
  by_cases hsamp : s.stB.samples = true ∧ s.stB.epoch = e
  · rcases PartyState.samples_cases hsamp.1 with ⟨core, hst⟩ | ⟨core, dec, hst⟩
    · have he : core.ep = e := by simpa [hst, PartyState.epoch] using hsamp.2
      subst he
      have h := sendUpdate_hideState core.ep d (P.kdfOK d.k core.ep) s false
        (hdrResult auth core kemMat.pk kemMat.sk) (kemMat.epochKey core.ep) hkeys
        (fun key hkey => by simp [hdrResult] at hkey)
      simp only [sendUpdate, Bool.false_eq_true, ↓reduceIte] at h
      rw [hst, hideSt_eq_self_of_not_holdsSecret core.ep d rfl,
        sendRleakWith_simOps_keysUnsampled auth core.ep d (P.kdfOK d.k core.ep) kemMat core rfl,
        sendRleakWith_pinOps_keysUnsampled auth core.ep kemMat.kg (some kemMat.enc) core rfl]
      simp only [KEMMaterial.pk, KEMMaterial.sk] at h ⊢
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      refine OracleComp.EvalDistEq.bind_const_of_support P.det.toRandLeak.keygenRleak fun res _ =>
        ?_
      refine congrArg pure ?_
      simp only [vuln, PartyState.epoch, hideState_challenged]
      by_cases hc : ({core.ep, core.ep + 1} ∩ s.challenged : Finset ℕ) = ∅
      · have hx : e' ∈ s.exposed ∪ {core.ep, core.ep + 1} := by
          rcases he' with rfl | rfl <;> simp
        simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte, hx, decide_true, hideState_exposed]
        rw [h]
        simp [hideState]
      · simp [hc]
    · have he : core.ep = e := by simpa [hst, PartyState.epoch] using hsamp.2
      subst he
      have h := sendUpdate_hideState core.ep d (P.kdfOK d.k core.ep) s false
        (ct1Result auth core dec kemMat.es kemMat.ct1 kemMat.key) (kemMat.epochKey core.ep) hkeys
        (fun key hkey => by
          simp only [ct1Result, Option.some.injEq, Prod.mk.injEq, true_and] at hkey
          exact hkey.symm)
      simp only [sendUpdate, Bool.false_eq_true, ↓reduceIte] at h
      rw [hst, hideSt_eq_self_of_not_holdsSecret core.ep d rfl,
        sendRleakWith_simOps_headerReceived auth core.ep d kemMat core dec rfl,
        sendRleakWith_pinOps_headerReceived auth core.ep
          (some kemMat.kg) kemMat.enc core dec rfl]
      simp only [KEMMaterial.es, KEMMaterial.ct1, KEMMaterial.key] at h ⊢
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      refine OracleComp.EvalDistEq.bind_const_of_support (P.det.toRandLeak.encaps1Rleak core.hdr)
        fun res _ => ?_
      refine congrArg pure ?_
      simp only [vuln, PartyState.epoch, hideState_challenged]
      by_cases hc : ({core.ep, core.ep + 1} ∩ s.challenged : Finset ℕ) = ∅
      · have hx : e' ∈ s.exposed ∪ {core.ep, core.ep + 1} := by
          rcases he' with rfl | rfl <;> simp
        simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte, hx, decide_true, hideState_exposed]
        rw [h]
        simp [hideState]
      · simp [hc]
  · rw [sendRleakWith_sim_hide_of_not_samples auth e d kemMat s.stB hsamp]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    refine OracleComp.EvalDistEq.bind_congr_of_support _ fun res hres =>
      ToVCVio.evalDistEq_of_eq (congrArg pure ?_)
    obtain ⟨r, rand⟩ := res
    have hr : r ∈ support (sendWith auth
      (pinOps (some kemMat.kg) (some kemMat.enc) e) s.stB) := by
      simp only [sendWith, support_map, Set.mem_image]
      exact ⟨(r, rand), hres, rfl⟩
    have h := sendUpdate_hideState e d (P.kdfOK d.k e) s false r (kemMat.epochKey e) hkeys
      (fun key hkey => honest_send_key_eq auth e kemMat hm hs false hr hkey)
    simp only [sendUpdate, Bool.false_eq_true, ↓reduceIte, hideSendRes] at h
    simp only [Prod.map, id, vuln_rleak_hideSt, hideSendRes, hideState_challenged]
    by_cases hg : (vuln P AuthState).rleak s.stB rand ∩ s.challenged ≠ ∅
    · rw [ite_eq_left hg, ite_eq_left hg]
      by_cases he : e' ∈ s.exposed <;> simp [he]
    · rw [ite_eq_right hg, ite_eq_right hg]
      simp only [hideState_exposed]
      rw [h]
      simp [Option.map_map, Function.comp_def, hideKey, hideState]

/-! ### The simulation theorem -/

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders and a possible KEM material `kemMat`, every query of the security
oracles over the honest instance with a challenge oracle recording challenges preserves the pinned
invariant of `kemMat`. -/
theorem honestImpl_preservesInv (hm : kemMat ∈ support (sampleMaterial))
    (chall : QueryImpl (ℕ →ₒ Option P.EpochKey) (StateT (GameState P AuthState) ProbComp))
    (hchall : SCKAScheme.RecordsChallenges chall) :
    QueryImpl.PreservesInv (SCKAScheme.securityImplAt
      (honestSchemeOf auth sampleInitKey e kemMat)
      chall (vuln P AuthState) (vuln P AuthState))
      (PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e) :=
  SCKAScheme.securityImplAt_preservesInv _ _ _ _ _
    (fun _ exposed challenged h => h.with_bookkeeping auth exposed challenged)
    (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
    (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st) hchall
    (fun s hs t res hres => pinnedCorrectness_preserves_at auth (kg? := some kemMat.kg)
      (enc? := some kemMat.enc) sampleInitKey hHdrSound hEkSound hCt1Sound hCt2Sound
      (fun kg h => by cases h; exact (sampleMaterial_ordinary_support kemMat hm).1)
      (fun kg enc h1 h2 => by
        cases h1; cases h2; exact (sampleMaterial_ordinary_support kemMat hm).2)
      (fun _ _ => ⟨kemMat.kg, rfl⟩) s hs t res hres)

variable [SampleableType P.EpochKey]

omit [SampleableType P.EpochKey] in
include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Let `chall` be a challenge oracle that commutes with hiding at `e`, and `e' = e` or
`e' = e + 1`. From a state `s` with the pinned invariant of `kemMat`, the simulated query stopped at
the first exposure of `e'`, from `hideState e d τ s`, has the joint response/state distribution of
the stopped query of the honest instance from `s` with its state hidden. Both instances answer
challenges with `chall`. -/
theorem oracle_sim_hide (hm : kemMat ∈ support (sampleMaterial))
    (chall : QueryImpl (ℕ →ₒ Option P.EpochKey) (StateT (GameState P AuthState) ProbComp))
    (hchall : ∀ t s, (chall t).run (hideState e d (P.kdfOK d.k e) s) =
      Prod.map id (hideState e d (P.kdfOK d.k e)) <$> (chall t).run s)
    (he' : e' = e ∨ e' = e + 1)
    (t : (securitySpec P AuthState).Domain) (s : GameState P AuthState)
    (hs : PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e s) :
    ((stopOnState (SCKAScheme.securityImplAt
      (simSchemeOf auth sampleInitKey e d kemMat.pk kemMat.ct1
        kemMat.ct2 (fun a => auth.update a e (kemMat.epochKey e)))
          chall (vuln P AuthState) (vuln P AuthState))
        (fun u => decide (e' ∈ u.exposed)) t).run).run
      (hideState e d (P.kdfOK d.k e) s) =ᵈ
    Prod.map id (hideState e d (P.kdfOK d.k e)) <$>
      ((stopOnState (SCKAScheme.securityImplAt (honestSchemeOf auth sampleInitKey e kemMat)
        chall (vuln P AuthState) (vuln P AuthState))
        (fun u => decide (e' ∈ u.exposed)) t).run).run s := by
  have hstop : ∀ u : GameState P AuthState,
      decide (e' ∈ (hideState e d (P.kdfOK d.k e) u).exposed) = decide (e' ∈ u.exposed) :=
    fun u => rfl
  rcases t with (((((t | u) | u) | t) | u) | u)
  · apply evalDistEq_stopOnState_of_map _ _ _ _ _ hstop
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf]
    rcases t with ((((n | u) | u) | n) | n)
    · simp only [SCKAScheme.sckaCorrectnessImpl]
      exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleUnif_run_map _ n s)
    · cases u
      simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact oracleSendA_sim_hide auth sampleInitKey e d kemMat hm s hs
    · cases u
      simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact oracleSendB_sim_hide auth sampleInitKey e d kemMat hm s hs
    · simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact ToVCVio.evalDistEq_of_eq (oracleRecvA_sim_hide auth sampleInitKey hHdrSound
        hEkSound hCt1Sound hCt2Sound e d kemMat s hs n)
    · simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact ToVCVio.evalDistEq_of_eq (oracleRecvB_sim_hide auth sampleInitKey hHdrSound
        hEkSound hCt1Sound hCt2Sound e d kemMat s hs n)
  · cases u
    rw [stopOnState_run_eq_map, stopOnState_run_eq_map, Functor.map_map]
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    exact oracleSendArleak_sim_hide auth sampleInitKey e d kemMat hm he' s hs
  · cases u
    rw [stopOnState_run_eq_map, stopOnState_run_eq_map, Functor.map_map]
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    exact oracleSendBrleak_sim_hide auth sampleInitKey e d kemMat hm he' s hs
  · apply evalDistEq_stopOnState_of_map _ _ _ _ _ hstop
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf]
    exact ToVCVio.evalDistEq_of_eq (hchall t s)
  · cases u
    rw [stopOnState_run_eq_map, stopOnState_run_eq_map, Functor.map_map]
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf]
    exact ToVCVio.evalDistEq_of_eq (oracleCorruptA_sim_hide e d _ he' s)
  · cases u
    rw [stopOnState_run_eq_map, stopOnState_run_eq_map, Functor.map_map]
    rw [SCKAScheme.securityImplAt_run, SCKAScheme.securityImplAt_run]
    simp only [SCKAScheme.securityImplOf, QueryImpl.add_apply_inr]
    exact ToVCVio.evalDistEq_of_eq (oracleCorruptB_sim_hide e d _ he' s)

omit [SampleableType P.EpochKey] in
include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- The simulation theorem: let `chall` be a challenge oracle that records challenges and commutes
with hiding at `e`, and let `e' = e` or `e' = e + 1`. Assuming sound stream decoders and a possible
KEM material `kemMat`, for every initial key `ik`, the simulated game with the public values of
`kemMat` and the update of `e` with `kemMat.epochKey e` accepts as often as the honest game over
the honest instance of `kemMat`. Both use the challenge oracle `chall`, run from
`initState auth ik`, and return `false` at the first exposure of `e'`. -/
theorem prEvent_stoppedRun_sim_eq_honest (hm : kemMat ∈ support (sampleMaterial))
    (chall : QueryImpl (ℕ →ₒ Option P.EpochKey) (StateT (GameState P AuthState) ProbComp))
    (hrec : SCKAScheme.RecordsChallenges chall)
    (hchall : ∀ t s, (chall t).run (hideState e d (P.kdfOK d.k e) s) =
      Prod.map id (hideState e d (P.kdfOK d.k e)) <$> (chall t).run s)
    (he' : e' = e ∨ e' = e + 1) (adv : SecurityAdversary P AuthState) (ik : InitKey) :
    Pr{let x ← (stoppedRun (SCKAScheme.securityImplAt (simSchemeOf auth sampleInitKey e d
        kemMat.pk kemMat.ct1 kemMat.ct2 (fun a => auth.update a e (kemMat.epochKey e)))
        chall (vuln P AuthState) (vuln P AuthState))
      (fun u => decide (e' ∈ u.exposed)) adv (initState auth ik))}[x = true] =
    Pr{let x ← (stoppedRun (SCKAScheme.securityImplAt
      (honestSchemeOf auth sampleInitKey e kemMat)
        chall (vuln P AuthState) (vuln P AuthState))
      (fun u => decide (e' ∈ u.exposed)) adv (initState auth ik))}[x = true] := by
  have h0 := hideState_initState auth e d (P.kdfOK d.k e) ik
  conv_lhs => rw [← h0]
  unfold stoppedRun
  refine prEvent_optionRun_eq_of_state_map _ _ (hideState e d (P.kdfOK d.k e))
    (PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e) ?_ ?_ adv _
    (pinnedInv_initState auth _ _ e ik)
  · intro t s hs res hres hsome
    obtain ⟨y, hy, -, hzy⟩ := exists_of_mem_support_stopOnState _ _ t s res hres hsome
    rw [hzy]
    exact honestImpl_preservesInv auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound e kemMat hm _ hrec t s hs y hy
  · intro t s hs
    exact oracle_sim_hide auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound e d kemMat hm chall hchall he' t s hs

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- The simulation theorem for the challenge oracle `pinnedChallenge e kStar`, stopped at `e`: the
simulated game and the honest game `Q_e(kemMat, kStar)` accept equally often. -/
theorem prEvent_stoppedRun_sim_eq_honest_pinned (hm : kemMat ∈ support (sampleMaterial))
    (kStar : P.EpochKey) (adv : SecurityAdversary P AuthState) (ik : InitKey) :
    Pr{let x ← (stoppedRun (SCKAScheme.securityImplAt (simSchemeOf auth sampleInitKey e d
        kemMat.pk kemMat.ct1 kemMat.ct2 (fun a => auth.update a e (kemMat.epochKey e)))
        (SCKAScheme.pinnedChallenge e kStar) (vuln P AuthState) (vuln P AuthState))
      (fun u => decide (e ∈ u.exposed)) adv (initState auth ik))}[x = true] =
    Pr{let x ← (stoppedRun (SCKAScheme.securityImplAt
      (honestSchemeOf auth sampleInitKey e kemMat)
        (SCKAScheme.pinnedChallenge e kStar) (vuln P AuthState) (vuln P AuthState))
      (fun u => decide (e ∈ u.exposed)) adv (initState auth ik))}[x = true] :=
  prEvent_stoppedRun_sim_eq_honest auth sampleInitKey hHdrSound hEkSound hCt1Sound
    hCt2Sound e d kemMat hm _ (SCKAScheme.pinnedChallenge_recordsChallenges e kStar)
    (pinnedChallenge_run_hideState e d _ kStar) (Or.inl rfl) adv ik

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- The simulation theorem for the challenge oracle of a challenge mode with `mode e = true`,
stopped at `e + 1`: the simulated game and the honest game over the honest instance of `kemMat`
accept equally often. -/
theorem prEvent_stoppedRun_sim_eq_honest_challOf (hm : kemMat ∈ support (sampleMaterial))
    (mode : ℕ → Bool) (hmode : mode e = true) (adv : SecurityAdversary P AuthState)
    (ik : InitKey) :
    Pr{let x ← (stoppedRun (SCKAScheme.securityImplAt (simSchemeOf auth sampleInitKey e d
        kemMat.pk kemMat.ct1 kemMat.ct2 (fun a => auth.update a e (kemMat.epochKey e)))
        (SCKAScheme.challOf mode) (vuln P AuthState) (vuln P AuthState))
      (fun u => decide (e + 1 ∈ u.exposed)) adv (initState auth ik))}[x = true] =
    Pr{let x ← (stoppedRun (SCKAScheme.securityImplAt
      (honestSchemeOf auth sampleInitKey e kemMat)
        (SCKAScheme.challOf mode) (vuln P AuthState) (vuln P AuthState))
      (fun u => decide (e + 1 ∈ u.exposed)) adv (initState auth ik))}[x = true] :=
  prEvent_stoppedRun_sim_eq_honest auth sampleInitKey hHdrSound hEkSound hCt1Sound
    hCt2Sound e d kemMat hm _ (SCKAScheme.challOf_recordsChallenges mode)
    (challOf_run_hideState e d _ mode hmode) (Or.inr rfl) adv ik

end Queries

end SPQR
