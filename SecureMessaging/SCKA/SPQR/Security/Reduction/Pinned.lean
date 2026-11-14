/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Security.Ideal

/-!
# Pinned KEM material

Let `e` be the epoch at which the reductions embed their challenge. The *KEM material*
`kemMat : KEMMaterial P` of an epoch records the outputs and coins of its two sampling phases,
key generation (`kemMat.kg`) and first-stage encapsulation (`kemMat.enc`). It is drawn by
`sampleMaterial`: `kg ← P.det.toRandLeak.keygenRleak`, then `enc ← P.det.toRandLeak.encaps1Rleak
(toHeader pk)` for the public key `pk` of `kg`. Its components are `kemMat.pk`, `kemMat.sk`,
`kemMat.es`, `kemMat.ct1` and `kemMat.key`; `kemMat.ct2` completes the ciphertext from `kemMat.es`
at `kemMat.pk`, and the epoch key derived at `e` is `kemMat.epochKey e := P.kdfOK kemMat.key e`.

- A sampling phase of `e` is *pinned* when it returns a value fixed in advance. The operations
  `pinOps kg? enc? e` pin the key generation of `e` to `kg` if `kg? = some kg` and its first
  stage to `enc` if `enc? = some enc`; all other calls sample honestly.
- The instance `pinnedSchemeOf kg? enc? e` runs SPQR over these operations, with the generator of
  an epoch outputting the key recorded by the encapsulator instead of decapsulating, as the ideal
  instance does (`Security.Ideal`). The *honest instance* `honestSchemeOf kemMat` pins both
  phases of `e` to `kemMat`.
- For samples `kg? : Option (PK × SK)` and `enc? : Option (St × C₁ × K)`, without their coins,
  the *pinned invariant* `PinnedInv auth kg? enc? e s` states that `s` is sample-consistent
  (`Security.Invariant`) with a transcript whose entries of epoch `e`, when present, agree with
  these samples (`PinnedTranscript`). The pinned instance `pinnedSchemeOf kg? enc? e` keeps
  `PinnedInv auth (kg?.map Prod.fst) (enc?.map Prod.fst) e`.

**Results.**

- Drawing the KEM material and reading off its public values and key is a fresh key generation
  and encapsulation (`sampleMaterial_bind_challenge`):
  `kemMat ← sampleMaterial; f kemMat.pk kemMat.ct1 kemMat.ct2 kemMat.key` is the computation
  `(pk, _) ← P.det.toKEM.keygen; (c, k) ← P.det.toKEM.encaps pk; f pk (splitC c).1 (splitC c).2 k`.
- When the pinned samples are possible outputs of the samplers and the first stage is pinned only
  together with the key generation, the correctness queries of the pinned instance preserve the
  pinned invariant (`pinnedInv_sendUpdate`, `pinnedInv_recvUpdate`,
  `pinnedCorrectness_preserves_at`).
- Under the pinned invariant, every key recorded at `e` is the epoch key derived from `enc`
  (`PinnedInv.keys_eq`), and a party in `headerReceived` at `e` holds the header of `kg`
  (`PinnedInv.hdr_eq`).
-/

@[expose] public section

open OracleSpec OracleComp ErasureCodePayload.Streaming

namespace SPQR

open Chunked

/-- KEM material of one epoch: the outputs and coins of its key generation and of its first-stage
encapsulation. -/
structure KEMMaterial (P : SPQR.Parameters ProbComp) where
  /-- The key pair with the coins of its generation. -/
  kg : (P.PK × P.SK) × P.det.KeygenRand
  /-- The encapsulation state, first ciphertext component and KEM key, with the coins of the
  first stage. -/
  enc : (P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand

namespace KEMMaterial

variable {P : SPQR.Parameters ProbComp}
  (kemMat : KEMMaterial P)

/-- The public key. -/
def pk : P.PK := kemMat.kg.1.1

/-- The secret key. -/
def sk : P.SK := kemMat.kg.1.2

/-- The encapsulation state. -/
def es : P.det.St := kemMat.enc.1.1

/-- The first ciphertext component. -/
def ct1 : P.det.C₁ := kemMat.enc.1.2.1

/-- The KEM key. -/
def key : P.K := kemMat.enc.1.2.2

/-- The second ciphertext component completed from the state at the public key. -/
def ct2 : P.det.C₂ :=
  P.det.encaps2Det kemMat.es (P.det.toHeader kemMat.pk) (P.det.toVector kemMat.pk)

/-- The epoch key derived at epoch `e`. -/
def epochKey (e : ℕ) : P.EpochKey := P.kdfOK kemMat.key e

end KEMMaterial

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (sampleInitKey : ProbComp InitKey)
  (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
  (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)

/-! ### Sampling the KEM material -/

/-- Sample the KEM material of an epoch: `kg ← P.det.toRandLeak.keygenRleak`, then
`enc ← P.det.toRandLeak.encaps1Rleak (toHeader pk)` for the public key `pk` of `kg`. -/
def sampleMaterial : ProbComp (KEMMaterial P) := do
  let kg ← P.det.toRandLeak.keygenRleak
  let enc ← P.det.toRandLeak.encaps1Rleak (P.det.toHeader kg.1.1)
  pure ⟨kg, enc⟩

/-- The components of a possible KEM material are possible outputs of the leaking samplers. -/
theorem sampleMaterial_support (kemMat : KEMMaterial P)
    (hm : kemMat ∈ support (sampleMaterial)) :
    kemMat.kg ∈ support P.det.toRandLeak.keygenRleak ∧
      kemMat.enc ∈ support (P.det.toRandLeak.encaps1Rleak (P.det.toHeader kemMat.pk)) := by
  simp only [sampleMaterial, mem_support_bind_iff, mem_support_pure_iff] at hm
  obtain ⟨kg, hkg, enc, henc, rfl⟩ := hm
  exact ⟨hkg, henc⟩

/-- The key pair and first stage of a possible KEM material are possible outputs of
`P.det.toKEM.keygen` and of `P.det.toIncremental.encaps1 (toHeader kemMat.pk)`. -/
theorem sampleMaterial_ordinary_support (kemMat : KEMMaterial P)
    (hm : kemMat ∈ support (sampleMaterial)) :
    kemMat.kg.1 ∈ support P.det.toKEM.keygen ∧
      kemMat.enc.1 ∈ support (P.det.toIncremental.encaps1 (P.det.toHeader kemMat.pk)) := by
  obtain ⟨hkg, henc⟩ := sampleMaterial_support kemMat hm
  exact ⟨(opsPossible_real (P := P)).1 0 _ hkg,
    (opsPossible_real (P := P)).2.1 0 (P.det.toHeader kemMat.pk) _ henc⟩

/-- `kemMat ← sampleMaterial; f kemMat.pk kemMat.ct1 kemMat.ct2 kemMat.key` is
`(pk, _) ← P.det.toKEM.keygen; (c, k) ← P.det.toKEM.encaps pk; f pk (splitC c).1 (splitC c).2 k`. -/
theorem sampleMaterial_bind_challenge {α : Type}
    (f : P.PK → P.det.C₁ → P.det.C₂ → P.K → ProbComp α) :
    (do
      let kemMat ← sampleMaterial
      f kemMat.pk kemMat.ct1 kemMat.ct2 kemMat.key) =
    (do
      let (pk, _) ← P.det.toKEM.keygen
      let (c, k) ← P.det.toKEM.encaps pk
      f pk (P.det.splitC c).1 (P.det.splitC c).2 k) := by
  rw [← P.det.toRandLeak.keygen_fst]
  simp only [sampleMaterial, bind_assoc, pure_bind]
  refine bind_congr fun kg => ?_
  obtain ⟨⟨pk, sk⟩, r⟩ := kg
  simp only [KEMMaterial.pk]
  rw [P.det.toIncremental.encaps_eq_stagedEncaps, KEMScheme.IncrementalStructure.stagedEncaps,
    ← P.det.toRandLeak.encaps1_fst]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun enc => ?_
  obtain ⟨⟨es, c1, k⟩, r'⟩ := enc
  simp only [pure_bind, KEMMaterial.ct1, KEMMaterial.ct2, KEMMaterial.key,
    KEMMaterial.es, KEMMaterial.pk, KEMScheme.IncrementalKEMDet.toIncremental,
    KEMScheme.IncrementalKEMDet.toHeader,
    KEMScheme.IncrementalKEMDet.toVector, KEMScheme.IncrementalStructure.toHeader,
    KEMScheme.IncrementalStructure.toVector]
  erw [P.det.splitC.apply_symm_apply]
  rfl

/-! ### Pinned operations -/

/-- The real operations, with the key generation of epoch `e` returning `kg` if `kg? = some kg`
and its first-stage encapsulation returning `enc` if `enc? = some enc`. -/
def pinOps (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)) (e : ℕ) : Ops P :=
  { Ops.real P with
    keygenRleak t := if t = e then kg?.elim P.det.toRandLeak.keygenRleak pure else
      P.det.toRandLeak.keygenRleak
    encaps1Rleak t hdr :=
      if t = e then enc?.elim (P.det.toRandLeak.encaps1Rleak hdr) pure else
        P.det.toRandLeak.encaps1Rleak hdr }

variable (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
  (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)) (e : ℕ)

/-- Pinning nothing gives the real operations. -/
theorem pinOps_none_none : pinOps none none e = Ops.real P := by
  dsimp only [pinOps, Ops.real, Option.elim, Parameters.generateRleak, Parameters.encaps1Rleak,
    KEMScheme.IncrementalKEMDet.toRandLeak, KEMScheme.IncrementalKEMDet.toIncremental]
  simp only [ite_self]
  rfl

/-- The key generation of the pinned epoch. -/
@[simp] theorem pinOps_keygenRleak_self :
    (pinOps kg? enc? e).keygenRleak e = kg?.elim P.det.toRandLeak.keygenRleak pure := by
  exact ite_eq_left rfl

/-- The key generation of the other epochs. -/
theorem pinOps_keygenRleak_of_ne {t : ℕ} (h : t ≠ e) :
    (pinOps kg? enc? e).keygenRleak t = P.det.toRandLeak.keygenRleak := by
  exact ite_eq_right h

/-- The first stage of the pinned epoch. -/
@[simp] theorem pinOps_encaps1Rleak_self (hdr : P.det.PKheader) :
    (pinOps kg? enc? e).encaps1Rleak e hdr = enc?.elim (P.det.toRandLeak.encaps1Rleak hdr) pure :=
      by
  exact ite_eq_left rfl

/-- The first stage of the other epochs. -/
theorem pinOps_encaps1Rleak_of_ne {t : ℕ} (h : t ≠ e) (hdr : P.det.PKheader) :
    (pinOps kg? enc? e).encaps1Rleak t hdr = P.det.toRandLeak.encaps1Rleak hdr := by
  exact ite_eq_right h

/-- The ideal instance with the key generation of `e` pinned to `kg?` and its first stage pinned to
`enc?`, at the game state `s`:
`schemeWith auth (idealOps (pinOps kg? enc? e) s) sampleInitKey`. -/
abbrev pinnedSchemeOf (s : GameState P AuthState) :=
  schemeWith auth (idealOps (pinOps kg? enc? e) s) sampleInitKey

/-- The honest instance of the KEM material `kemMat`: the ideal instance with the key generation and
the first stage of `e` pinned to `kemMat`, `pinnedSchemeOf (some kemMat.kg) (some kemMat.enc) e`. -/
abbrev honestSchemeOf (kemMat : KEMMaterial P)
    (s : GameState P AuthState) :=
  pinnedSchemeOf auth sampleInitKey (some kemMat.kg) (some kemMat.enc) e s

/-- The result of a key-generation send of epoch `e` pinned to `kg`. -/
private theorem sendWith_pinOps_keysUnsampled (kg : (P.PK × P.SK) × P.det.KeygenRand)
    (core : EkSender.KeysUnsampled AuthState) (he : core.ep = e) {r : SendResult P AuthState}
    (hr : r ∈ support (sendWith auth (pinOps (some kg) enc? e) (.keysUnsampled core))) :
    r.state = .keysSampled ⟨core.ep, core.authSt, kg.1.1, kg.1.2⟩ (EncoderState.init P.ecpHdr
      (P.det.toHeader kg.1.1,
        auth.macHeader core.authSt core.ep (P.det.toHeader kg.1.1))).nextChunk.2 := by
  subst he
  simp only [sendWith, sendRleakWith, pinOps_keygenRleak_self, Option.elim, pure_bind,
    support_map, Set.mem_image, mem_support_pure_iff] at hr
  obtain ⟨x, rfl, rfl⟩ := hr
  rfl

/-- The result of a first-stage send of epoch `e` pinned to `enc`. -/
private theorem sendWith_pinOps_headerReceived (enc : (P.det.St × P.det.C₁ × P.K) ×
    P.det.Encaps1Rand)
    (core : CtSender.HeaderReceived P AuthState) (dec : P.decEk.D)
    (he : core.ep = e) {r : SendResult P AuthState}
    (hr : r ∈ support (sendWith auth (pinOps kg? (some enc) e) (.headerReceived core dec))) :
    r.state = .ct1Sampled ⟨core.ep, auth.update core.authSt core.ep (P.kdfOK enc.1.2.2 core.ep),
        core.hdr, enc.1.1, enc.1.2.1⟩ (EncoderState.init P.ecpCt1 enc.1.2.1).nextChunk.2 dec ∧
      r.outputKey = some (core.ep, P.kdfOK enc.1.2.2 core.ep) := by
  subst he
  simp only [sendWith, sendRleakWith, pinOps_encaps1Rleak_self, Option.elim, pure_bind,
    support_map, Set.mem_image, mem_support_pure_iff] at hr
  obtain ⟨x, rfl, rfl⟩ := hr
  exact ⟨rfl, rfl⟩

/-! ### The pinned invariant -/

/-- The entries of epoch `e` in `T`, when present, agree with the pinned values: the key pair has
the secret key, header and vector of `kg`, and the first stage has the state and first component
of `enc` and derives its epoch key. -/
def PinnedTranscript (kg? : Option (P.PK × P.SK)) (enc? : Option (P.det.St × P.det.C₁ × P.K))
    (e : ℕ) (T : ℕ → Braid.EpochTranscript P.toBraid) : Prop :=
  (∀ pk₀ sk₀, kg? = some (pk₀, sk₀) → ∀ pk sk, (T e).keypair = some (pk, sk) →
    sk = sk₀ ∧ P.det.toHeader pk = P.det.toHeader pk₀ ∧ P.det.toVector pk = P.det.toVector pk₀) ∧
  (∀ es₀ ct1₀ k₀, enc? = some (es₀, ct1₀, k₀) → ∀ es ct1 k, (T e).encaps1 = some (es, ct1, k) →
    es = es₀ ∧ ct1 = ct1₀ ∧ P.kdfOK k e = P.kdfOK k₀ e)

/-- `s.toBraid` satisfies the transcript invariant without decapsulation clause for some initial
key and a pinned transcript, and `s` satisfies `Ct1AckInv`. -/
def PinnedInv (kg? : Option (P.PK × P.SK)) (enc? : Option (P.det.St × P.det.C₁ × P.K)) (e : ℕ)
    (s : GameState P AuthState) : Prop :=
  (∃ (ik : InitKey) (T : ℕ → Braid.EpochTranscript P.toBraid),
    Braid.TranscriptInv auth (fun _ _ _ _ _ _ => True) ik T s.toBraid ∧
      PinnedTranscript kg? enc? e T) ∧ Ct1AckInv s

variable {kg? enc? e}

/-- The empty transcript is pinned. -/
private theorem pinnedTranscript_empty (kg? : Option (P.PK × P.SK))
    (enc? : Option (P.det.St × P.det.C₁ × P.K)) (e : ℕ) :
    PinnedTranscript kg? enc? e (fun _ => { keypair := none, encaps1 := none }) := by
  simp [PinnedTranscript]

/-- The initial game state satisfies the pinned invariant. -/
theorem pinnedInv_initState (kg? : Option (P.PK × P.SK))
    (enc? : Option (P.det.St × P.det.C₁ × P.K)) (e : ℕ) (ik : InitKey) :
    PinnedInv auth kg? enc? e (initState auth ik) :=
  ⟨⟨ik, _, Braid.transcriptInv_initGameState (P := P.toBraid) auth ik,
    pinnedTranscript_empty kg? enc? e⟩, ct1AckInv_initGameState auth ik⟩

/-- The pinned invariant ignores the exposed and challenged sets. -/
theorem PinnedInv.with_bookkeeping {kg? : Option (P.PK × P.SK)}
    {enc? : Option (P.det.St × P.det.C₁ × P.K)} {e : ℕ} {s : GameState P AuthState}
    (h : PinnedInv auth kg? enc? e s) (exposed challenged : Finset ℕ) :
    PinnedInv auth kg? enc? e { s with exposed := exposed, challenged := challenged } :=
  let ⟨⟨ik, T, hT, hpin⟩, hack⟩ := h
  ⟨⟨ik, T, hT.setFlags exposed challenged, hpin⟩, hack⟩

/-- Under the pinned invariant with `enc? = some (es₀, ct1₀, k₀)`, every key recorded at `e` is
`P.kdfOK k₀ e`. -/
theorem PinnedInv.keys_eq {kg? : Option (P.PK × P.SK)} {es₀ : P.det.St} {ct1₀ : P.det.C₁}
    {k₀ : P.K} {e : ℕ} {s : GameState P AuthState}
    (h : PinnedInv auth kg? (some (es₀, ct1₀, k₀)) e s) (party : Bool) {k : P.EpochKey}
    (hk : s.keysAt party e = some k) : k = P.kdfOK k₀ e := by
  obtain ⟨⟨ik, T, hT, -, hpin⟩, -⟩ := h
  have hkeys := hT.keys party e
  have hk' : (if party then s.toBraid.keyA else s.toBraid.keyB) e = some k := by
    cases party <;> exact hk
  rw [hk'] at hkeys
  by_cases hb : 0 < e ∧
    e ≤ (if party then s.toBraid.stA else s.toBraid.stB).completedEpoch
  · rw [ite_eq_left hb] at hkeys
    obtain ⟨⟨es, ct1, key⟩, hc, hkey⟩ := Option.map_eq_some_iff.mp hkeys.symm
    obtain ⟨-, -, hkdf⟩ := hpin es₀ ct1₀ k₀ rfl es ct1 key hc
    dsimp only at hkey
    rw [← hkey, hkdf]
  · rw [ite_eq_right hb] at hkeys
    cases hkeys

/-- Under the pinned invariant with `kg? = some (pk₀, sk₀)`, a party in `headerReceived` at `e`
holds the header of `pk₀`. -/
theorem PinnedInv.hdr_eq {pk₀ : P.PK} {sk₀ : P.SK} {enc? : Option (P.det.St × P.det.C₁ × P.K)}
    {e : ℕ} {s : GameState P AuthState} (h : PinnedInv auth (some (pk₀, sk₀)) enc? e s)
    (party : Bool) {core : CtSender.HeaderReceived P AuthState}
    {dec : P.decEk.D}
    (hst : s.stateAt party = .headerReceived core dec) (he : core.ep = e) :
    core.hdr = P.det.toHeader pk₀ := by
  obtain ⟨⟨ik, T, hT, hpin, -⟩, -⟩ := h
  have hL := hT.local (P := P.toBraid) auth party
  rw [GameState.toBraid_stateAt, hst] at hL
  simp only [PartyState.toBraid, Braid.LocalPayloadInv] at hL
  obtain ⟨-, -, pk, sk, hkp, hhdr, -⟩ := hL
  rw [he] at hkp
  obtain ⟨-, hh, -⟩ := hpin pk₀ sk₀ rfl pk sk hkp
  exact hhdr.trans hh

/-- The pinned operations are possible at every state under the pinned invariant, when the
pinned samples are possible and the first stage is pinned only together with the key
generation. -/
theorem pinOps_possibleAt
    (hkg : ∀ kg, kg? = some kg → kg.1 ∈ support P.det.toKEM.keygen)
    (henc : ∀ kg enc, kg? = some kg → enc? = some enc →
      enc.1 ∈ support (P.det.toIncremental.encaps1 (P.det.toHeader kg.1.1)))
    (hstage : ∀ enc, enc? = some enc → ∃ kg, kg? = some kg)
    {s : GameState P AuthState} (hs : PinnedInv auth (kg?.map Prod.fst) (enc?.map Prod.fst) e s)
    (party : Bool) : OpsPossibleAt (pinOps kg? enc? e) (s.stateAt party) := by
  cases hst : s.stateAt party
  case keysUnsampled core =>
    intro out hout
    by_cases hee : core.ep = e
    · rw [hee, pinOps_keygenRleak_self] at hout
      cases hkgq : kg? with
      | none =>
        rw [hkgq] at hout
        simp only [Option.elim] at hout
        rw [← P.det.toRandLeak.keygen_fst]
        exact (mem_support_bind_iff _ _ _).mpr ⟨out, hout, by simp⟩
      | some kg =>
        rw [hkgq] at hout
        simp only [Option.elim, mem_support_pure_iff] at hout
        subst hout
        exact hkg _ hkgq
    · rw [pinOps_keygenRleak_of_ne _ _ _ hee] at hout
      rw [← P.det.toRandLeak.keygen_fst]
      exact (mem_support_bind_iff _ _ _).mpr ⟨out, hout, by simp⟩
  case headerReceived core dec =>
    intro out hout
    by_cases hee : core.ep = e
    · rw [hee, pinOps_encaps1Rleak_self] at hout
      cases hencq : enc? with
      | none =>
        rw [hencq] at hout
        simp only [Option.elim] at hout
        exact (opsPossible_real (P := P)).2.1 core.ep core.hdr out hout
      | some enc =>
        rw [hencq] at hout
        simp only [Option.elim, mem_support_pure_iff] at hout
        subst hout
        obtain ⟨⟨⟨pk₀, sk₀⟩, rkg⟩, hkgq⟩ := hstage _ hencq
        rw [hkgq, Option.map_some] at hs
        rw [PinnedInv.hdr_eq auth hs party hst hee]
        exact henc _ _ hkgq hencq
    · rw [pinOps_encaps1Rleak_of_ne _ _ _ hee] at hout
      exact (opsPossible_real (P := P)).2.1 core.ep core.hdr out hout
  all_goals trivial

/-! ### Preservation -/

variable [DecidableEq P.EpochKey]

/-- A send of `party` through `sendWith auth (pinOps kg? enc? e)` that is possible at the
sender's state preserves the pinned invariant. -/
theorem pinnedInv_sendUpdate {s : GameState P AuthState} (party : Bool)
    (hposs : OpsPossibleAt (pinOps kg? enc? e) (s.stateAt party))
    (hs : PinnedInv auth (kg?.map Prod.fst) (enc?.map Prod.fst) e s) {r : SendResult P AuthState}
    (hr : r ∈ support (sendWith auth (pinOps kg? enc? e) (s.stateAt party))) :
    PinnedInv auth (kg?.map Prod.fst) (enc?.map Prod.fst) e (sendUpdate s party r) := by
  classical
  obtain ⟨⟨ik, T, hT, hpin⟩, hack⟩ := hs
  have hedge : Braid.SendEdge auth (s.toBraid.stateAt party) r.toBraid := by
    rw [GameState.toBraid_stateAt]
    exact sendEdge_toBraid auth (sendWith_mem_support_send auth hposs hr)
  have hCP := Braid.controlInv_statePairInv_sendUpdate (P := P.toBraid) auth ⟨hT.control,
    hT.statePair⟩
    party hedge
  have hc := Braid.sendUpdate_correct_of_transcriptInv (P := P.toBraid) auth hT party hedge
  have heq := Braid.sendUpdate_eq_successor_of_correct s.toBraid party r.toBraid
    hT.correct hc
  rw [heq] at hCP
  refine ⟨⟨ik, ?_⟩, ct1AckInv_sendUpdate auth party hposs hack hr⟩
  rw [toBraid_sendUpdate, heq]
  cases hst : s.stateAt party with
  | keysUnsampled core =>
    have hst' : s.toBraid.stateAt party = .keysUnsampled core.ep core.authSt := by
      rw [GameState.toBraid_stateAt, hst]; rfl
    rw [hst'] at hedge
    generalize hrb : r.toBraid = rb at hedge hCP
    obtain ⟨_, _, pk, sk, -⟩ := hedge
    have hT' := Braid.send_keysUnsampled_transcript (P := P.toBraid) auth hT party hst' pk sk hCP
    have hstate := congrArg Braid.SendResult.state hrb
    refine ⟨_, hT', fun pk₀ sk₀ hkg pk' sk' hkp => ?_, fun es₀ ct1₀ k₀ henc es ct1 k hc' => ?_⟩
    · by_cases hee : core.ep = e
      · subst hee
        rw [Function.update_self] at hkp
        simp only [Option.some.injEq, Prod.mk.injEq] at hkp
        obtain ⟨rfl, rfl⟩ := hkp
        obtain ⟨kg, rfl⟩ : ∃ kg, kg? = some kg := by
          cases hkgq : kg? with
          | none => rw [hkgq] at hkg; simp at hkg
          | some kg => exact ⟨kg, rfl⟩
        simp only [Option.map_some, Option.some.injEq] at hkg
        rw [hst] at hr
        have hr' := sendWith_pinOps_keysUnsampled auth enc? core.ep kg core rfl hr
        simp only [hkg] at hr'
        have hstate' := congrArg PartyState.toBraid hr'
        rw [show r.toBraid.state = r.state.toBraid from rfl, hstate'] at hstate
        dsimp only [PartyState.toBraid] at hstate
        obtain ⟨-, -, hsk, hvec, henc⟩ := Braid.State.keysSampled.inj hstate
        refine ⟨hsk.symm, ?_, hvec.symm⟩
        have := congrArg
          (fun st : EncoderState (P.det.PKheader × P.Mac) P.Sym => st.payload.1) henc
        exact this.symm
      · rw [Function.update_of_ne (Ne.symm hee)] at hkp
        exact hpin.1 pk₀ sk₀ hkg pk' sk' hkp
    · have hc'' : (T e).encaps1 = some (es, ct1, k) := by
        by_cases hee : core.ep = e
        · rw [hee, Function.update_self] at hc'
          exact hc'
        · rw [Function.update_of_ne (Ne.symm hee)] at hc'
          exact hc'
      exact hpin.2 es₀ ct1₀ k₀ henc es ct1 k hc''
  | headerReceived core dec =>
    have hst' : s.toBraid.stateAt party =
        .headerReceived core.ep core.authSt core.hdr dec := by
      rw [GameState.toBraid_stateAt, hst]; rfl
    rw [hst'] at hedge
    generalize hrb : r.toBraid = rb at hedge hCP
    cases hedge
    rename_i es ct1 key _
    have hT' := Braid.send_headerReceived_transcript (P := P.toBraid) auth hT party hst' es ct1
      key hCP
    have hstate := congrArg Braid.SendResult.state hrb
    have hout := congrArg Braid.SendResult.outputKey hrb
    refine ⟨_, hT', fun pk₀ sk₀ hkg pk' sk' hkp => ?_, fun es₀ ct1₀ k₀ henc es' ct1' k' hc' => ?_⟩
    · have hkp' : (T e).keypair = some (pk', sk') := by
        by_cases hee : core.ep = e
        · rw [hee, Function.update_self] at hkp
          exact hkp
        · rw [Function.update_of_ne (Ne.symm hee)] at hkp
          exact hkp
      exact hpin.1 pk₀ sk₀ hkg pk' sk' hkp'
    · by_cases hee : core.ep = e
      · subst hee
        rw [Function.update_self] at hc'
        simp only [Option.some.injEq, Prod.mk.injEq] at hc'
        obtain ⟨rfl, rfl, rfl⟩ := hc'
        obtain ⟨enc, rfl⟩ : ∃ enc, enc? = some enc := by
          cases hencq : enc? with
          | none => rw [hencq] at henc; simp at henc
          | some enc => exact ⟨enc, rfl⟩
        simp only [Option.map_some, Option.some.injEq] at henc
        rw [hst] at hr
        obtain ⟨hr', hout'⟩ :=
          sendWith_pinOps_headerReceived auth kg? core.ep enc core dec rfl hr
        simp only [henc] at hr' hout'
        have hstate' := congrArg PartyState.toBraid hr'
        rw [show r.toBraid.state = r.state.toBraid from rfl, hstate'] at hstate
        dsimp only [PartyState.toBraid] at hstate
        obtain ⟨-, -, -, hes, hct1, -, -⟩ := Braid.State.ct1Sampled.inj hstate
        rw [show r.toBraid.outputKey = r.outputKey from rfl, hout'] at hout
        simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hout
        exact ⟨hes.symm, hct1.symm, hout.symm⟩
      · rw [Function.update_of_ne (Ne.symm hee)] at hc'
        exact hpin.2 es₀ ct1₀ k₀ henc es' ct1' k' hc'
  | _ =>
    refine ⟨T, Braid.send_existing_transcript (P := P.toBraid) auth hT party hedge ?_ hCP, hpin⟩
    rw [GameState.toBraid_stateAt, hst]
    trivial


include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- A receive by `party` of the message recorded by the peer at index `n`, through
`recvWith auth (idealOps (pinOps kg? enc? e) s)`, preserves the pinned invariant. -/
theorem pinnedInv_recvUpdate {s : GameState P AuthState}
    (hs : PinnedInv auth (kg?.map Prod.fst) (enc?.map Prod.fst) e s) (party : Bool) {n : ℕ}
    {msg : Message P.Sym} {tsnd : ℕ} (hentry : s.messagesAt (!party) n = some (msg, tsnd))
    {r : RecvResult P AuthState}
    (hr : recvWith auth (idealOps (pinOps kg? enc? e) s) (s.stateAt party) msg = .ok r) :
    PinnedInv auth (kg?.map Prod.fst) (enc?.map Prod.fst) e
      (recvUpdate s party tsnd r r.receivingEpoch) := by
  obtain ⟨⟨ik, T, hT, hpin⟩, hack⟩ := hs
  obtain ⟨hT', hack', -⟩ := transcriptInv_recvUpdate_ideal auth hHdrSound hEkSound hCt1Sound
    hCt2Sound (ops := pinOps kg? enc? e) (fun _ => rfl) hT hack party hentry hr
  exact ⟨⟨ik, T, hT', hpin⟩, hack'⟩

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Every correctness query of `schemeWith auth (idealOps (pinOps kg? enc? e) s) sampleInitKey`
from `s` preserves the pinned invariant, when the pinned samples are possible and the first stage
is pinned only together with the key generation. -/
theorem pinnedCorrectness_preserves_at (hkg : ∀ kg, kg? = some kg → kg.1 ∈ support
    P.det.toKEM.keygen)
    (henc : ∀ kg enc, kg? = some kg → enc? = some enc →
      enc.1 ∈ support (P.det.toIncremental.encaps1 (P.det.toHeader kg.1.1)))
    (hstage : ∀ enc, enc? = some enc → ∃ kg, kg? = some kg)
    (s : GameState P AuthState) (hs : PinnedInv auth (kg?.map Prod.fst) (enc?.map Prod.fst) e s)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message P.Sym)).Domain)
    (res : (SCKAScheme.sckaCorrectnessSpec (Message P.Sym)).Range t × GameState P AuthState)
    (hres : res ∈ support ((SCKAScheme.sckaCorrectnessImpl
      (schemeWith auth (idealOps (pinOps kg? enc? e) s) sampleInitKey) t).run s)) :
    PinnedInv auth (kg?.map Prod.fst) (enc?.map Prod.fst) e res.2 :=
  schemeWith_correctness_preserves auth sampleInitKey (pinOps kg? enc? e)
    (PinnedInv auth (kg?.map Prod.fst) (enc?.map Prod.fst) e) s hs
    (fun party _ hr => pinnedInv_sendUpdate auth party
      (pinOps_possibleAt auth hkg henc hstage hs party) hs hr)
    (fun party _ _ _ hentry => by
      obtain ⟨r, hr, -⟩ := recvWith_ideal_outcome auth hHdrSound hEkSound hCt1Sound hCt2Sound
        (ops := pinOps kg? enc? e) (fun _ => rfl) hs.1.choose_spec.choose_spec.1 hs.2 party
        hentry
      exact ⟨r, hr, pinnedInv_recvUpdate auth hHdrSound hEkSound hCt1Sound hCt2Sound hs party
        hentry hr⟩)
    t res hres

end SPQR
