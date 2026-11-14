/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Security.Reduction.Simulation

/-!
# Deferring the samples of the challenge epoch

**Setting.** Let
- `adv` be an SCKA adversary against SPQR and `ik` an initial key;
- `e` be the epoch at which the reductions embed their challenge, and `e'` be `e` or `e + 1`;
- `μ : ℕ → Bool` be a challenge mode: an eligible challenge at `t` returns a uniform key if `μ t`
  and the recorded key otherwise.

Assume that the four stream decoders of `P` are sound for their erasure codes.

**Experiments.** Both run `adv` from `initState auth ik` with challenges answered under `μ`, use
the key recorded by the encapsulator instead of decapsulating, return `false` at the first query
that exposes `e'`, and otherwise return the output of `adv`.

- **Stopped ideal game** (`idealImpl μ`, `Security.Ideal`): each sampling phase of `e` samples at
  its protocol call.
- **Pinned game** (`pinnedImpl (some kemMat.kg) (some kemMat.enc) μ`): the outputs and coins of the
  key generation and first-stage encapsulation of `e` are drawn in advance as the KEM material
  `kemMat ← sampleMaterial` (`Reduction.Pinned`).

**Main result** (`stoppedRun_material_deferred`): both games accept with the same probability.
Under the hybrid mode `μ := hybridMode i`, the stopped ideal game is the stopped hybrid
`stoppedHybridExp adv i e ik` (`Security.Ideal`). For a version `x ∈ {real, random}`, in which a
challenge at `e` returns the recorded key (`real`) or an independent uniform key (`random`), and
`i := e - 1` in `real` and `i := e` in `random`, the two games stopped at `e` are the stopped hybrid
`S_e^x` and the pinned hybrid `P_e^x`:

```text
Pr[P_e^x = true] = Pr[S_e^x = true].
```
-/

@[expose] public section

open OracleSpec OracleComp ErasureCodePayload.Streaming
open SCKAScheme.sckaSecuritySpec SCKAScheme.sckaCorrectnessSpec

namespace SPQR

open Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (sampleInitKey : ProbComp InitKey)
  (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
  (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
  (e : ℕ) {e' : ℕ}

/-! ### Phases and their use

Before the first exposure of `e'`, each sampling phase of `e` runs in at most one query.
`usesPhase` tests whether a query runs a phase and `phaseSent` whether it has run; they are the
`hit` and `used` tests of `stoppedRun_sample_once_eq`.
-/

/-- The two sampling phases of an epoch. -/
inductive Phase where
  /-- The key generation of the generator. -/
  | keygen
  /-- The first-stage encapsulation of the encapsulator. -/
  | encaps1
  deriving DecidableEq

/-- Whether a send from `st` runs `phase` at `e`: from `keysUnsampled` at `e` for the key
generation, from `headerReceived` at `e` for the first stage. -/
def runsPhase (phase : Phase) : PartyState P AuthState → Bool
  | .keysUnsampled core => decide (phase = .keygen ∧ core.ep = e)
  | .headerReceived core _ => decide (phase = .encaps1 ∧ core.ep = e)
  | _ => false

/-- The payload of the message sent by the phase. -/
def phasePayload (phase : Phase) (chunk : ℕ × P.Sym) : Payload P.Sym :=
  match phase with
  | .keygen => .hdr chunk
  | .encaps1 => .ct1 chunk

/-- Predicate stating that `phase` has run at epoch `e`: a party has recorded a message with the
phase's payload at `e`, at an index at most its send counter. -/
def phaseSent (phase : Phase) (s : GameState P AuthState) : Prop :=
  ∃ party n chunk tsnd, n ≤ s.countAt party ∧
    s.messagesAt party n = some (⟨e, phasePayload phase chunk⟩, tsnd)

/-- Marks queries `t` that run `phase` at epoch `e` from state `s`: the ordinary or leaking send of
a party whose state runs it, excluding leaking sends rejected because `e` or `e + 1` was
challenged. -/
def usesPhase (phase : Phase) (t : (securitySpec P AuthState).Domain)
    (s : GameState P AuthState) : Bool :=
  match t with
  | OCorrectness OSendA => runsPhase e phase s.stA
  | OCorrectness OSendB => runsPhase e phase s.stB
  | OSendArleak => runsPhase e phase s.stA && decide (e ∉ s.challenged ∧ e + 1 ∉ s.challenged)
  | OSendBrleak => runsPhase e phase s.stB && decide (e ∉ s.challenged ∧ e + 1 ∉ s.challenged)
  | _ => false

/-- A state running the key generation at `e` is `keysUnsampled` at `e`. -/
private theorem runsPhase_keygen_iff (st : PartyState P AuthState) :
    runsPhase e .keygen st = true ↔ ∃ core, st = .keysUnsampled core ∧ core.ep = e := by
  cases st <;> simp [runsPhase]

/-- A state running the first stage at `e` is `headerReceived` at `e`. -/
private theorem runsPhase_encaps1_iff (st : PartyState P AuthState) :
    runsPhase e .encaps1 st = true ↔ ∃ core dec, st = .headerReceived core dec ∧ core.ep = e := by
  cases st <;> simp [runsPhase]

/-! ### Independence of the sends from an unused pin -/

/-- A leaking send from a state that does not run the key generation of `e` is the same
computation for every pinned key pair. -/
private theorem sendRleakWith_pinOps_kg_irrel (kg? kg?' : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand))
    (st : PartyState P AuthState) (h : runsPhase e .keygen st = false) :
    sendRleakWith auth (pinOps kg? enc? e) st =
      sendRleakWith auth (pinOps kg?' enc? e) st := by
  cases st
  case keysUnsampled core =>
    have hne : core.ep ≠ e := by simpa [runsPhase] using h
    simp only [sendRleakWith, pinOps_keygenRleak_of_ne _ _ _ hne]
  all_goals rfl

/-- A leaking send from a state that does not run the first stage of `e` is the same computation
for every pinned first stage. -/
private theorem sendRleakWith_pinOps_enc_irrel (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc? enc?' : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand))
    (st : PartyState P AuthState) (h : runsPhase e .encaps1 st = false) :
    sendRleakWith auth (pinOps kg? enc? e) st =
      sendRleakWith auth (pinOps kg? enc?' e) st := by
  cases st
  case headerReceived core dec =>
    have hne : core.ep ≠ e := by simpa [runsPhase] using h
    simp only [sendRleakWith, pinOps_encaps1Rleak_of_ne _ _ _ hne]
  all_goals rfl

/-- The message of a send running `phase` at `e` carries the phase's payload at epoch `e`. -/
private theorem sendWith_phase_msg
    (ops : Ops P)
    (phase : Phase) {st : PartyState P AuthState} (hrun : runsPhase e phase st = true)
    {r : SendResult P AuthState} (hr : r ∈ support (sendWith auth ops st)) :
    ∃ chunk, r.msg = ⟨e, phasePayload phase chunk⟩ := by
  cases phase
  · obtain ⟨core, rfl, rfl⟩ := (runsPhase_keygen_iff e st).mp hrun
    simp only [sendWith, sendRleakWith, support_map, Set.mem_image, mem_support_bind_iff,
      mem_support_pure_iff] at hr
    obtain ⟨x, ⟨⟨⟨pk, sk⟩, rnd⟩, -, rfl⟩, rfl⟩ := hr
    exact ⟨_, rfl⟩
  · obtain ⟨core, dec, rfl, rfl⟩ := (runsPhase_encaps1_iff e st).mp hrun
    simp only [sendWith, sendRleakWith, support_map, Set.mem_image, mem_support_bind_iff,
      mem_support_pure_iff] at hr
    obtain ⟨x, ⟨⟨⟨es, c1, k⟩, rnd⟩, -, rfl⟩, rfl⟩ := hr
    exact ⟨_, rfl⟩

/-- The exposure of a leaking send running `phase` at `e` is `{e, e + 1}`. -/
private theorem leakEpochs_of_runsPhase (phase : Phase) {st : PartyState P AuthState}
    (hrun : runsPhase e phase st = true) : leakEpochs st = {e, e + 1} := by
  cases phase
  · obtain ⟨core, rfl, rfl⟩ := (runsPhase_keygen_iff e st).mp hrun
    rfl
  · obtain ⟨core, dec, rfl, rfl⟩ := (runsPhase_encaps1_iff e st).mp hrun
    rfl

/-- If neither `e` nor `e + 1` is in `C`, then `{e, e + 1} ∩ C = ∅`. -/
private theorem inter_eq_empty_of_notMem {C : Finset ℕ} (hc : e ∉ C ∧ e + 1 ∉ C) :
    ({e, e + 1} ∩ C : Finset ℕ) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with ⟨rfl | rfl, ht⟩
  · exact hc.1 ht
  · exact hc.2 ht

/-- If `e` or `e + 1` is in `C`, then `{e, e + 1} ∩ C ≠ ∅`. -/
private theorem inter_ne_empty_of_mem {C : Finset ℕ} (hc : e ∈ C ∨ e + 1 ∈ C) :
    ({e, e + 1} ∩ C : Finset ℕ) ≠ ∅ := by
  rw [← Finset.nonempty_iff_ne_empty]
  rcases hc with hc | hc
  · exact ⟨e, Finset.mem_inter.mpr ⟨by simp, hc⟩⟩
  · exact ⟨e + 1, Finset.mem_inter.mpr ⟨by simp, hc⟩⟩

/-- The operations pinned to a possible key pair only are possible. -/
private theorem opsPossible_pinOps_kg (kg : (P.PK × P.SK) × P.det.KeygenRand)
    (hkg : kg.1 ∈ support P.det.toKEM.keygen) : OpsPossible P (pinOps (some kg) none e) := by
  refine ⟨fun t out hout => ?_, fun t hdr out hout => ?_, fun _ => rfl⟩
  · by_cases ht : t = e
    · subst ht
      simp only [pinOps_keygenRleak_self, Option.elim, mem_support_pure_iff] at hout
      exact hout ▸ hkg
    · rw [pinOps_keygenRleak_of_ne _ _ _ ht] at hout
      exact (opsPossible_real).1 t out hout
  · by_cases ht : t = e
    · subst ht
      simp only [pinOps_encaps1Rleak_self, Option.elim] at hout
      exact (opsPossible_real).2.1 t hdr out hout
    · rw [pinOps_encaps1Rleak_of_ne _ _ _ ht] at hout
      exact (opsPossible_real).2.1 t hdr out hout

/-! ### Single use of the samples -/

/-- Once `phase` has run at `e`, it stays run: every security query over a state-dependent
instance whose ordinary sends forget the coins of its leaking sends, and whose challenge oracle
records challenges, preserves `phaseSent e phase`. -/
private theorem phaseSent_preserved [DecidableEq P.EpochKey] (phase : Phase)
    (schemeOf : GameState P AuthState → SCKAScheme ProbComp InitKey (PartyState P AuthState)
      (PartyState P AuthState) P.EpochKey (Message P.Sym)
      (Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand))
    (chall : QueryImpl (ℕ →ₒ Option P.EpochKey) (StateT (GameState P AuthState) ProbComp))
    (hmA : ∀ s st, (do
      let out ← (schemeOf s).sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendA st)
    (hmB : ∀ s st, (do
      let out ← (schemeOf s).sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendB st)
    (hchall : SCKAScheme.RecordsChallenges chall) :
    QueryImpl.PreservesInv
      (SCKAScheme.securityImplAt schemeOf chall (vuln P AuthState) (vuln P AuthState))
      (phaseSent e phase) := by
  rintro t s ⟨party, n, chunk, tsnd, hn, hm⟩ res hres
  cases party
  · exact ⟨false, n, chunk, tsnd,
      SCKAScheme.securityImplAt_preserves_recordedB schemeOf chall _ _ hmA hmB hchall n _ t s
        ⟨hn, hm⟩ res hres⟩
  · exact ⟨true, n, chunk, tsnd,
      SCKAScheme.securityImplAt_preserves_recordedA schemeOf chall _ _ hmA hmB hchall n _ t s
        ⟨hn, hm⟩ res hres⟩

/-- In a state satisfying the transcript invariant in which `phase` has run at `e`
(`phaseSent e phase`), no party's state runs it at `e`. -/
private theorem not_runsPhase_of_phaseSent {ik : InitKey} {T : ℕ → Braid.EpochTranscript
    P.toBraid}
    {s : GameState P AuthState}
    {D : ℕ → P.toBraid.PK → P.toBraid.SK → P.toBraid.inc.St → P.toBraid.inc.C₁ → P.toBraid.K → Prop}
    (hT : Braid.TranscriptInv auth D ik T s.toBraid)
    (phase : Phase) (hsent : phaseSent e phase s) (party : Bool) :
    runsPhase e phase (s.stateAt party) = false := by
  obtain ⟨p', n, chunk, tsnd, -, hm⟩ := hsent
  have hmsg := hT.messages p' n _ tsnd (GameState.toBraid_messagesAt_eq_some hm)
  have hloc := hT.local (P := P.toBraid) auth party
  rw [GameState.toBraid_stateAt] at hloc
  cases phase
  · simp only [Message.toBraid, phasePayload, Braid.MessagePayloadInv] at hmsg
    obtain ⟨pk, sk, i, hkp, -⟩ := hmsg
    cases hst : s.stateAt party
    all_goals try rfl
    case keysUnsampled core =>
      rw [hst] at hloc
      simp only [PartyState.toBraid, Braid.LocalPayloadInv] at hloc
      obtain ⟨-, hnone, -⟩ := hloc
      simp only [runsPhase, decide_eq_false_iff_not, not_and, true_implies]
      intro he
      rw [he, hkp] at hnone
      cases hnone
  · simp only [Message.toBraid, phasePayload, Braid.MessagePayloadInv] at hmsg
    obtain ⟨es, ct1, key, i, hc, -⟩ := hmsg
    cases hst : s.stateAt party
    all_goals try rfl
    case headerReceived core dec =>
      rw [hst] at hloc
      simp only [PartyState.toBraid, Braid.LocalPayloadInv] at hloc
      obtain ⟨-, hnone, -⟩ := hloc
      simp only [runsPhase, decide_eq_false_iff_not, not_and, true_implies]
      intro he
      rw [he, hc] at hnone
      cases hnone

/-- Once `phase` has run at `e` (`phaseSent e phase`), no query runs it at `e` from a state
satisfying the transcript invariant. -/
private theorem usesPhase_eq_false_of_phaseSent {ik : InitKey}
    {T : ℕ → Braid.EpochTranscript P.toBraid}
    {s : GameState P AuthState}
    {D : ℕ → P.toBraid.PK → P.toBraid.SK → P.toBraid.inc.St → P.toBraid.inc.C₁ → P.toBraid.K → Prop}
    (hT : Braid.TranscriptInv auth D ik T s.toBraid)
    (phase : Phase) (hsent : phaseSent e phase s) (t : (securitySpec P AuthState).Domain) :
    usesPhase e phase t s = false := by
  have hA := not_runsPhase_of_phaseSent auth e hT phase hsent true
  have hB := not_runsPhase_of_phaseSent auth e hT phase hsent false
  simp only [GameState.stateAt, Bool.false_eq_true, ↓reduceIte] at hA hB
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    all_goals try cases u
    all_goals simp [usesPhase, hA, hB]
  all_goals try cases u
  all_goals simp [usesPhase, hA, hB]

/-! ### Averaging of the samples -/

/-- Drawing the key pair `kg ← P.det.toRandLeak.keygenRleak` before a leaking send pinned to `kg`
or at its key generation gives the same output distribution. -/
private theorem sendRleakWith_sample_keygen
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand))
    (st : PartyState P AuthState) :
    (do
      let kg ← P.det.toRandLeak.keygenRleak
      sendRleakWith auth (pinOps (some kg) enc? e) st) =ᵈ
    sendRleakWith auth (pinOps none enc? e) st := by
  cases st
  case keysUnsampled core =>
    by_cases he : core.ep = e
    · subst he
      refine ToVCVio.evalDistEq_of_eq ?_
      simp only [sendRleakWith, pinOps_keygenRleak_self, Option.elim,
        KEMScheme.IncrementalKEMDet.toRandLeak, KEMScheme.IncrementalKEMDet.toIncremental,
        bind_assoc, pure_bind]
    · simp only [sendRleakWith, pinOps_keygenRleak_of_ne _ _ _ he]
      exact OracleComp.EvalDistEq.bind_const_of_support P.det.toRandLeak.keygenRleak fun _ _ => rfl
  all_goals exact OracleComp.EvalDistEq.bind_const_of_support P.det.toRandLeak.keygenRleak fun _ _
    => rfl

/-- From a state whose header at `e`, if any, is that of `kg.pk`, drawing the first stage
`enc ← P.det.toRandLeak.encaps1Rleak (toHeader kg.pk)` before a leaking send pinned to `kg` and
`enc` or at its first stage gives the same output distribution; the key pair stays pinned to
`kg`. -/
private theorem sendRleakWith_sample_encaps1 (kg : (P.PK × P.SK) × P.det.KeygenRand)
    (st : PartyState P AuthState)
    (hhdr : ∀ core dec, st = .headerReceived core dec → core.ep = e →
      core.hdr = P.det.toHeader kg.1.1) :
    (do
      let enc ← P.det.toRandLeak.encaps1Rleak (P.det.toHeader kg.1.1)
      sendRleakWith auth (pinOps (some kg) (some enc) e) st) =ᵈ
    sendRleakWith auth (pinOps (some kg) none e) st := by
  cases st
  case headerReceived core dec =>
    by_cases he : core.ep = e
    · have hh := hhdr core dec rfl he
      subst he
      refine ToVCVio.evalDistEq_of_eq ?_
      simp only [sendRleakWith, pinOps_encaps1Rleak_self, Option.elim, hh,
        KEMScheme.IncrementalKEMDet.toRandLeak, KEMScheme.IncrementalKEMDet.toIncremental,
        bind_assoc, pure_bind]
    · simp only [sendRleakWith, pinOps_encaps1Rleak_of_ne _ _ _ he]
      exact OracleComp.EvalDistEq.bind_const_of_support _ fun _ _ => rfl
  all_goals exact OracleComp.EvalDistEq.bind_const_of_support _ fun _ _ => rfl

/-! ### The invariant of the first-stage deferral

The first-stage sample is drawn at the header of the pinned public key, so its deferral holds from
the states satisfying `encapsDeferralInv kg`; the key-generation deferral holds from those
satisfying `Inv auth` (`Security.Invariant`).
-/

/-- A pinned invariant with the first stage pinned implies the one with it unpinned. -/
private theorem PinnedInv.weaken {kg? : Option (P.PK × P.SK)} {enc₀ : P.det.St × P.det.C₁ × P.K}
    {s : GameState P AuthState} (h : PinnedInv auth kg? (some enc₀) e s) :
    PinnedInv auth kg? none e s :=
  let ⟨⟨ik, T, hT, hpin⟩, hack⟩ := h
  ⟨⟨ik, T, hT, hpin.1, fun _ _ _ h => by cases h⟩, hack⟩

/-- The invariant of the first-stage deferral for the key pair `kg`: the pinned invariant of `kg`,
and, as long as the first stage of `e` has not been run, the pinned invariant of `kg` with every
possible first stage. -/
def encapsDeferralInv (kg : (P.PK × P.SK) × P.det.KeygenRand) (s : GameState P AuthState) : Prop :=
  PinnedInv auth (some kg.1) none e s ∧
    (¬ phaseSent e .encaps1 s → ∀ enc ∈ support (P.det.toRandLeak.encaps1Rleak (P.det.toHeader
      kg.1.1)),
      PinnedInv auth (some kg.1) (some enc.1) e s)

/-- The invariant of the first-stage deferral holds initially. -/
private theorem encapsDeferralInv_initState (kg : (P.PK × P.SK) × P.det.KeygenRand) (ik : InitKey) :
    encapsDeferralInv auth e kg (initState auth ik) :=
  ⟨pinnedInv_initState auth _ _ e ik, fun _ _ _ => pinnedInv_initState auth _ _ e ik⟩

section Oracles


/-! ### Independence of the instances from an unused pin -/

/-- From a state that does not run the key generation of `e`, the sends of two instances whose
pins differ only in the key pair agree. -/
private theorem schemeWith_pinOps_kg_irrel_sendA
    (kg? kg?' : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)) (s : GameState P AuthState)
    (st : PartyState P AuthState) (h : runsPhase e .keygen st = false) :
    (schemeWith auth (idealOps (pinOps kg? enc? e) s) sampleInitKey).sendA st =
      (schemeWith auth (idealOps (pinOps kg?' enc? e) s) sampleInitKey).sendA st := by
  simp only [schemeWith, sendWith, sendRleakWith_idealOps,
    sendRleakWith_pinOps_kg_irrel auth e kg? kg?' enc? st h]

/-- Leaking version of `schemeWith_pinOps_kg_irrel_sendA`. -/
private theorem schemeWith_pinOps_kg_irrel_sendArleak
    (kg? kg?' : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)) (s : GameState P AuthState)
    (st : PartyState P AuthState) (h : runsPhase e .keygen st = false) :
    (schemeWith auth (idealOps (pinOps kg? enc? e) s) sampleInitKey).sendArleak st =
      (schemeWith auth (idealOps (pinOps kg?' enc? e) s) sampleInitKey).sendArleak st := by
  simp only [schemeWith, sendRleakWith_idealOps,
    sendRleakWith_pinOps_kg_irrel auth e kg? kg?' enc? st h]

/-- First-stage version of `schemeWith_pinOps_kg_irrel_sendA`. -/
private theorem schemeWith_pinOps_enc_irrel_sendA (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc? enc?' : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand))
    (s : GameState P AuthState) (st : PartyState P AuthState)
    (h : runsPhase e .encaps1 st = false) :
    (schemeWith auth (idealOps (pinOps kg? enc? e) s) sampleInitKey).sendA st =
      (schemeWith auth (idealOps (pinOps kg? enc?' e) s) sampleInitKey).sendA st := by
  simp only [schemeWith, sendWith, sendRleakWith_idealOps,
    sendRleakWith_pinOps_enc_irrel auth e kg? enc? enc?' st h]

/-- Leaking version of `schemeWith_pinOps_enc_irrel_sendA`. -/
private theorem schemeWith_pinOps_enc_irrel_sendArleak
    (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc? enc?' : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand))
    (s : GameState P AuthState) (st : PartyState P AuthState)
    (h : runsPhase e .encaps1 st = false) :
    (schemeWith auth (idealOps (pinOps kg? enc? e) s) sampleInitKey).sendArleak st =
      (schemeWith auth (idealOps (pinOps kg? enc?' e) s) sampleInitKey).sendArleak st := by
  simp only [schemeWith, sendRleakWith_idealOps,
    sendRleakWith_pinOps_enc_irrel auth e kg? enc? enc?' st h]

variable [DecidableEq P.EpochKey]

/-- After an ordinary send of `party` running `phase` at `e`, `phase` has run at `e`
(`phaseSent e phase`). -/
private theorem phaseSent_of_send (ops : Ops P) (phase : Phase) (party : Bool)
    (s : GameState P AuthState) (hrun : runsPhase e phase (s.stateAt party) = true)
    (res : Option (ℕ × Option ℕ × Message P.Sym) × GameState P AuthState)
    (hres : res ∈ support
      ((SCKAScheme.oracleSend (schemeWith auth ops sampleInitKey) party ()).run s)) :
    phaseSent e phase res.2 := by
  obtain ⟨out, hout, rfl⟩ :=
    (SCKAScheme.mem_support_oracleSend_run_iff _ s rfl party res).mp hres
  simp only [schemeWith, mem_support_bind_iff, mem_support_pure_iff] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  obtain ⟨chunk, hmsg⟩ := sendWith_phase_msg auth e ops phase hrun hr
  refine ⟨party, s.countAt party + 1, chunk, r.sendingEpoch, ?_, ?_⟩ <;>
    cases party <;> rcases r.outputKey with _ | ⟨_, _⟩ <;>
    simp [SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, GameState.countAt,
      GameState.messagesAt, hmsg]

/-- If A's state runs `phase` at `e` and neither `e` nor `e + 1` is challenged, A's leaking send
exposes `e'` for `e' = e` or `e' = e + 1`. -/
private theorem exposed_of_sendArleak_phase (ops : Ops P)
    (phase : Phase) (he' : e' = e ∨ e' = e + 1)
    (s : GameState P AuthState)
    (hrun : runsPhase e phase s.stA = true) (hc : e ∉ s.challenged ∧ e + 1 ∉ s.challenged)
    (res : Option (ℕ × Option ℕ × Message P.Sym ×
      Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand) × GameState P AuthState)
    (hres : res ∈ support ((SCKAScheme.oracleSendArleak (vuln P AuthState).rleak
      (schemeWith auth ops sampleInitKey) ()).run s)) :
    e' ∈ res.2.exposed := by
  rw [SCKAScheme.oracleSendArleak_run_eq, support_map] at hres
  obtain ⟨out, hout, rfl⟩ := hres
  rcases out with _ | ⟨keyOpt, ρ, tsnd, stA', rand⟩
  · exact absurd hout (schemeWith_sendArleak_neverFails auth ops sampleInitKey s.stA)
  · simp only [schemeWith, mem_support_bind_iff, mem_support_pure_iff, Option.some.injEq,
      Prod.mk.injEq] at hout
    obtain ⟨⟨r, rand'⟩, hr, -, -, -, -, heq⟩ := hout
    have hleak := sendRleakWith_exposure auth ops s.stA (r, rand') hr
    rw [leakEpochs_of_runsPhase e phase hrun] at hleak
    rw [← heq] at hleak
    dsimp only
    rw [hleak, inter_eq_empty_of_notMem e hc]
    rcases he' with rfl | rfl <;> simp

/-- B version of `exposed_of_sendArleak_phase`. -/
private theorem exposed_of_sendBrleak_phase (ops : Ops P)
    (phase : Phase) (he' : e' = e ∨ e' = e + 1)
    (s : GameState P AuthState)
    (hrun : runsPhase e phase s.stB = true) (hc : e ∉ s.challenged ∧ e + 1 ∉ s.challenged)
    (res : Option (ℕ × Option ℕ × Message P.Sym ×
      Braid.SendRand P.det.KeygenRand P.det.Encaps1Rand) × GameState P AuthState)
    (hres : res ∈ support ((SCKAScheme.oracleSendBrleak (vuln P AuthState).rleak
      (schemeWith auth ops sampleInitKey) ()).run s)) :
    e' ∈ res.2.exposed := by
  rw [SCKAScheme.oracleSendBrleak_run_eq, support_map] at hres
  obtain ⟨out, hout, rfl⟩ := hres
  rcases out with _ | ⟨keyOpt, ρ, tsnd, stB', rand⟩
  · exact absurd hout (schemeWith_sendArleak_neverFails auth ops sampleInitKey s.stB)
  · simp only [schemeWith, mem_support_bind_iff, mem_support_pure_iff, Option.some.injEq,
      Prod.mk.injEq] at hout
    obtain ⟨⟨r, rand'⟩, hr, -, -, -, -, heq⟩ := hout
    have hleak := sendRleakWith_exposure auth ops s.stB (r, rand') hr
    rw [leakEpochs_of_runsPhase e phase hrun] at hleak
    rw [← heq] at hleak
    dsimp only
    rw [hleak, inter_eq_empty_of_notMem e hc]
    rcases he' with rfl | rfl <;> simp

/-- If A's state runs the key generation of `e` and `e` or `e + 1` is already challenged, A's
leaking-send query in an instance pinned to `kg` returns `none` and leaves the state unchanged: it
is the computation `pure (none, s)`. -/
private theorem oracleSendArleak_pinned_keygen_rejected (kg : (P.PK × P.SK) × P.det.KeygenRand)
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)) (s : GameState P AuthState)
    (hrun : runsPhase e .keygen s.stA = true) (hc : e ∈ s.challenged ∨ e + 1 ∈ s.challenged) :
    (SCKAScheme.oracleSendArleak (vuln P AuthState).rleak
      (schemeWith auth (idealOps (pinOps (some kg) enc? e) s) sampleInitKey) ()).run s =
      pure (none, s) := by
  rw [SCKAScheme.oracleSendArleak_run_eq]
  obtain ⟨core, hst, he⟩ := (runsPhase_keygen_iff e s.stA).mp hrun
  simp only [schemeWith, sendRleakWith_idealOps, hst,
    sendRleakWith_pinOps_keysUnsampled auth e kg enc? core he, map_eq_bind_pure_comp,
    pure_bind, Function.comp_def]
  simp [vuln, PartyState.epoch, he, inter_ne_empty_of_mem e hc]

/-- B version of `oracleSendArleak_pinned_keygen_rejected`. -/
private theorem oracleSendBrleak_pinned_keygen_rejected (kg : (P.PK × P.SK) × P.det.KeygenRand)
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)) (s : GameState P AuthState)
    (hrun : runsPhase e .keygen s.stB = true) (hc : e ∈ s.challenged ∨ e + 1 ∈ s.challenged) :
    (SCKAScheme.oracleSendBrleak (vuln P AuthState).rleak
      (schemeWith auth (idealOps (pinOps (some kg) enc? e) s) sampleInitKey) ()).run s =
      pure (none, s) := by
  rw [SCKAScheme.oracleSendBrleak_run_eq]
  obtain ⟨core, hst, he⟩ := (runsPhase_keygen_iff e s.stB).mp hrun
  simp only [schemeWith, sendRleakWith_idealOps, hst,
    sendRleakWith_pinOps_keysUnsampled auth e kg enc? core he, map_eq_bind_pure_comp,
    pure_bind, Function.comp_def]
  simp [vuln, PartyState.epoch, he, inter_ne_empty_of_mem e hc]

/-- First-stage version of `oracleSendArleak_pinned_keygen_rejected`, for an instance pinned to
`enc`. -/
private theorem oracleSendArleak_pinned_encaps1_rejected
    (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc : (P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand) (s : GameState P AuthState)
    (hrun : runsPhase e .encaps1 s.stA = true) (hc : e ∈ s.challenged ∨ e + 1 ∈ s.challenged) :
    (SCKAScheme.oracleSendArleak (vuln P AuthState).rleak
      (schemeWith auth (idealOps (pinOps kg? (some enc) e) s) sampleInitKey) ()).run s =
      pure (none, s) := by
  rw [SCKAScheme.oracleSendArleak_run_eq]
  obtain ⟨core, dec, hst, he⟩ := (runsPhase_encaps1_iff e s.stA).mp hrun
  simp only [schemeWith, sendRleakWith_idealOps, hst,
    sendRleakWith_pinOps_headerReceived auth e kg? enc core dec he, map_eq_bind_pure_comp,
    pure_bind, Function.comp_def]
  simp [vuln, PartyState.epoch, he, inter_ne_empty_of_mem e hc]

/-- B version of `oracleSendArleak_pinned_encaps1_rejected`. -/
private theorem oracleSendBrleak_pinned_encaps1_rejected
    (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc : (P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand) (s : GameState P AuthState)
    (hrun : runsPhase e .encaps1 s.stB = true) (hc : e ∈ s.challenged ∨ e + 1 ∈ s.challenged) :
    (SCKAScheme.oracleSendBrleak (vuln P AuthState).rleak
      (schemeWith auth (idealOps (pinOps kg? (some enc) e) s) sampleInitKey) ()).run s =
      pure (none, s) := by
  rw [SCKAScheme.oracleSendBrleak_run_eq]
  obtain ⟨core, dec, hst, he⟩ := (runsPhase_encaps1_iff e s.stB).mp hrun
  simp only [schemeWith, sendRleakWith_idealOps, hst,
    sendRleakWith_pinOps_headerReceived auth e kg? enc core dec he, map_eq_bind_pure_comp,
    pure_bind, Function.comp_def]
  simp [vuln, PartyState.epoch, he, inter_ne_empty_of_mem e hc]

/-! ### The pinned families: independence, single use and averaging -/

variable [SampleableType P.EpochKey]

/-- The oracles of the ideal game with the key generation of `e` pinned to `kg?` and its first
stage pinned to `enc?`, with challenge mode `mode`. -/
abbrev pinnedImpl (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)) (mode : ℕ → Bool) :=
  SCKAScheme.modeImpl (pinnedSchemeOf auth sampleInitKey kg? enc? e) (vuln P AuthState)
    (vuln P AuthState) mode

/-- Without pins, `pinnedImpl` is `idealImpl`. -/
private theorem pinnedImpl_none_none (mode : ℕ → Bool) :
    pinnedImpl auth sampleInitKey e none none mode = idealImpl auth sampleInitKey mode := by
  unfold pinnedImpl idealImpl idealSchemeOf pinnedSchemeOf
  rw [pinOps_none_none]

/-- From a state in which no party runs the first-stage encapsulation of `e`, two families whose
pins differ only in the encapsulation answer every query by the same computation. -/
private theorem pinnedImpl_run_eq_of_not_runs_encaps1
    (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc? enc?' : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)) (mode : ℕ → Bool)
    (t : (securitySpec P AuthState).Domain) (s : GameState P AuthState)
    (hA : runsPhase e .encaps1 s.stA = false) (hB : runsPhase e .encaps1 s.stB = false) :
    (pinnedImpl auth sampleInitKey e kg? enc? mode t).run s =
      (pinnedImpl auth sampleInitKey e kg? enc?' mode t).run s := by
  apply SCKAScheme.securityImplAt_congr (R := fun {_} => Eq) (hrefl := fun _ => rfl)
  · exact fun _ =>
      schemeWith_pinOps_enc_irrel_sendA auth sampleInitKey e kg? enc? enc?' s s.stA hA
  · exact fun _ =>
      schemeWith_pinOps_enc_irrel_sendA auth sampleInitKey e kg? enc? enc?' s s.stB hB
  · exact fun _ _ _ _ _ => rfl
  · exact fun _ _ _ _ _ => rfl
  · exact fun _ => SCKAScheme.oracleSendArleak_run_congr _ _ _ s
      (schemeWith_pinOps_enc_irrel_sendArleak auth sampleInitKey e kg? enc? enc?' s s.stA hA)
  · exact fun _ => SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
      (schemeWith_pinOps_enc_irrel_sendArleak auth sampleInitKey e kg? enc? enc?' s s.stB hB)

/-- A query that does not run the key generation of `e` (`usesPhase e .keygen t s = false`) is the
same computation for every pinned key pair. -/
private theorem pinnedImpl_run_eq_of_not_uses_keygen (kg kg' : (P.PK × P.SK) × P.det.KeygenRand)
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)) (mode : ℕ → Bool)
    (t : (securitySpec P AuthState).Domain) (s : GameState P AuthState)
    (h : usesPhase e .keygen t s = false) :
    (pinnedImpl auth sampleInitKey e (some kg) enc? mode t).run s =
      (pinnedImpl auth sampleInitKey e (some kg') enc? mode t).run s := by
  apply SCKAScheme.securityImplAt_congr (R := fun {_} => Eq) (hrefl := fun _ => rfl)
  · rintro rfl
    simp only [usesPhase] at h
    exact schemeWith_pinOps_kg_irrel_sendA auth sampleInitKey e _ _ enc? s s.stA h
  · rintro rfl
    simp only [usesPhase] at h
    exact schemeWith_pinOps_kg_irrel_sendA auth sampleInitKey e _ _ enc? s s.stB h
  · exact fun _ _ _ _ _ => rfl
  · exact fun _ _ _ _ _ => rfl
  · rintro rfl
    by_cases hrun : runsPhase e .keygen s.stA = true
    · have hc : e ∈ s.challenged ∨ e + 1 ∈ s.challenged := by
        have h' : e ∉ s.challenged → e + 1 ∈ s.challenged := by simpa [usesPhase, hrun] using h
        exact (em (e ∈ s.challenged)).imp_right h'
      exact (oracleSendArleak_pinned_keygen_rejected auth sampleInitKey e kg enc? s hrun
        hc).trans (oracleSendArleak_pinned_keygen_rejected auth sampleInitKey e kg' enc? s
          hrun hc).symm
    · exact SCKAScheme.oracleSendArleak_run_congr _ _ _ s
        (schemeWith_pinOps_kg_irrel_sendArleak auth sampleInitKey e _ _ enc? s s.stA
          (Bool.eq_false_iff.mpr hrun))
  · rintro rfl
    by_cases hrun : runsPhase e .keygen s.stB = true
    · have hc : e ∈ s.challenged ∨ e + 1 ∈ s.challenged := by
        have h' : e ∉ s.challenged → e + 1 ∈ s.challenged := by simpa [usesPhase, hrun] using h
        exact (em (e ∈ s.challenged)).imp_right h'
      exact (oracleSendBrleak_pinned_keygen_rejected auth sampleInitKey e kg enc? s hrun
        hc).trans (oracleSendBrleak_pinned_keygen_rejected auth sampleInitKey e kg' enc? s
          hrun hc).symm
    · exact SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
        (schemeWith_pinOps_kg_irrel_sendArleak auth sampleInitKey e _ _ enc? s s.stB
          (Bool.eq_false_iff.mpr hrun))

/-- First-stage version of `pinnedImpl_run_eq_of_not_uses_keygen`. -/
private theorem pinnedImpl_run_eq_of_not_uses_encaps1
    (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc enc' : (P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand) (mode : ℕ → Bool)
    (t : (securitySpec P AuthState).Domain) (s : GameState P AuthState)
    (h : usesPhase e .encaps1 t s = false) :
    (pinnedImpl auth sampleInitKey e kg? (some enc) mode t).run s =
      (pinnedImpl auth sampleInitKey e kg? (some enc') mode t).run s := by
  apply SCKAScheme.securityImplAt_congr (R := fun {_} => Eq) (hrefl := fun _ => rfl)
  · rintro rfl
    simp only [usesPhase] at h
    exact schemeWith_pinOps_enc_irrel_sendA auth sampleInitKey e kg? _ _ s s.stA h
  · rintro rfl
    simp only [usesPhase] at h
    exact schemeWith_pinOps_enc_irrel_sendA auth sampleInitKey e kg? _ _ s s.stB h
  · exact fun _ _ _ _ _ => rfl
  · exact fun _ _ _ _ _ => rfl
  · rintro rfl
    by_cases hrun : runsPhase e .encaps1 s.stA = true
    · have hc : e ∈ s.challenged ∨ e + 1 ∈ s.challenged := by
        have h' : e ∉ s.challenged → e + 1 ∈ s.challenged := by simpa [usesPhase, hrun] using h
        exact (em (e ∈ s.challenged)).imp_right h'
      exact (oracleSendArleak_pinned_encaps1_rejected auth sampleInitKey e kg? enc s hrun
        hc).trans (oracleSendArleak_pinned_encaps1_rejected auth sampleInitKey e kg? enc' s
          hrun hc).symm
    · exact SCKAScheme.oracleSendArleak_run_congr _ _ _ s
        (schemeWith_pinOps_enc_irrel_sendArleak auth sampleInitKey e kg? _ _ s s.stA
          (Bool.eq_false_iff.mpr hrun))
  · rintro rfl
    by_cases hrun : runsPhase e .encaps1 s.stB = true
    · have hc : e ∈ s.challenged ∨ e + 1 ∈ s.challenged := by
        have h' : e ∉ s.challenged → e + 1 ∈ s.challenged := by simpa [usesPhase, hrun] using h
        exact (em (e ∈ s.challenged)).imp_right h'
      exact (oracleSendBrleak_pinned_encaps1_rejected auth sampleInitKey e kg? enc s hrun
        hc).trans (oracleSendBrleak_pinned_encaps1_rejected auth sampleInitKey e kg? enc' s
          hrun hc).symm
    · exact SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
        (schemeWith_pinOps_enc_irrel_sendArleak auth sampleInitKey e kg? _ _ s s.stB
          (Bool.eq_false_iff.mpr hrun))

/-- A query running `phase` at `e` leaves `phaseSent e phase` true in every possible successor
state where `e'` remains unexposed. -/
private theorem phaseSent_of_usesPhase (phase : Phase)
    (kg? : Option ((P.PK × P.SK) × P.det.KeygenRand))
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand)) (mode : ℕ → Bool)
    (he' : e' = e ∨ e' = e + 1)
    (t : (securitySpec P AuthState).Domain) (s : GameState P AuthState)
    (hh : usesPhase e phase t s = true)
    (res : (securitySpec P AuthState).Range t × GameState P AuthState)
    (hres : res ∈ support ((pinnedImpl auth sampleInitKey e kg? enc? mode t).run s))
    (hstop : decide (e' ∈ res.2.exposed) = false) : phaseSent e phase res.2 := by
  rw [SCKAScheme.securityImplAt_run] at hres
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    all_goals try cases u
    all_goals try simp only [usesPhase, Bool.false_eq_true] at hh
    · exact phaseSent_of_send auth sampleInitKey e _ phase true s hh res hres
    · exact phaseSent_of_send auth sampleInitKey e _ phase false s hh res hres
  · cases u
    simp only [usesPhase, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact absurd (exposed_of_sendArleak_phase auth sampleInitKey e _ phase he' s hh.1 hh.2 res
      hres)
      (by simpa using hstop)
  · cases u
    simp only [usesPhase, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact absurd (exposed_of_sendBrleak_phase auth sampleInitKey e _ phase he' s hh.1 hh.2 res
      hres)
      (by simpa using hstop)
  all_goals try cases u
  all_goals simp [usesPhase] at hh

/-- Drawing the key pair `kg ← P.det.toRandLeak.keygenRleak` before a query pinned to `kg` or at
its key generation gives the same joint answer/state distribution. -/
private theorem pinnedImpl_sample_keygen_eq
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand))
    (mode : ℕ → Bool) (t : (securitySpec P AuthState).Domain) (s : GameState P AuthState) :
    (do
      let kg ← P.det.toRandLeak.keygenRleak
      (pinnedImpl auth sampleInitKey e (some kg) enc? mode t).run s) =ᵈ
    (pinnedImpl auth sampleInitKey e none enc? mode t).run s := by
  refine SCKAScheme.securityImplAt_sample_eq _ _ _ P.det.toRandLeak.keygenRleak
    (fun kg s => schemeWith auth (idealOps (pinOps (some kg) enc? e) s) sampleInitKey)
    (pinnedSchemeOf auth sampleInitKey none enc? e) s
    ?_ ?_ ?_ ?_ (fun _ _ _ => rfl) (fun _ _ _ => rfl) t
  all_goals
    simp only [schemeWith, sendWith, sendRleakWith_idealOps, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_def]
    rw [← bind_assoc]
    exact (sendRleakWith_sample_keygen auth e enc? _).bind_left _

/-- From a state with the pinned invariant of `kg`, drawing the first stage
`enc ← P.det.toRandLeak.encaps1Rleak (toHeader kg.pk)` before a query pinned to `kg` and `enc` or
at its first stage gives the same joint answer/state distribution. -/
private theorem pinnedImpl_sample_encaps1_eq (kg : (P.PK × P.SK) × P.det.KeygenRand)
    {s : GameState P AuthState} (hs : PinnedInv auth (some kg.1) none e s) (mode : ℕ → Bool)
    (t : (securitySpec P AuthState).Domain) :
    (do
      let enc ← P.det.toRandLeak.encaps1Rleak (P.det.toHeader kg.1.1)
      (pinnedImpl auth sampleInitKey e (some kg) (some enc) mode t).run s) =ᵈ
    (pinnedImpl auth sampleInitKey e (some kg) none mode t).run s := by
  have hhdrA : ∀ core dec, s.stA = .headerReceived core dec → core.ep = e →
      core.hdr = P.det.toHeader kg.1.1 := fun core dec hst he =>
    PinnedInv.hdr_eq auth (pk₀ := kg.1.1) (sk₀ := kg.1.2) hs true hst he
  have hhdrB : ∀ core dec, s.stB = .headerReceived core dec → core.ep = e →
      core.hdr = P.det.toHeader kg.1.1 := fun core dec hst he =>
    PinnedInv.hdr_eq auth (pk₀ := kg.1.1) (sk₀ := kg.1.2) hs false hst he
  refine SCKAScheme.securityImplAt_sample_eq _ _ _ (P.det.toRandLeak.encaps1Rleak (P.det.toHeader
    kg.1.1))
    (fun enc s => schemeWith auth (idealOps (pinOps (some kg) (some enc) e) s) sampleInitKey)
    (pinnedSchemeOf auth sampleInitKey (some kg) none e) s
    ?_ ?_ ?_ ?_ (fun _ _ _ => rfl) (fun _ _ _ => rfl) t
  all_goals
    simp only [schemeWith, sendWith, sendRleakWith_idealOps, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_def]
    rw [← bind_assoc]
    first
    | exact (sendRleakWith_sample_encaps1 auth e kg s.stA hhdrA).bind_left _
    | exact (sendRleakWith_sample_encaps1 auth e kg s.stB hhdrB).bind_left _

/-! ### Preservation of the invariants -/

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- For a possible key pair `kg`, and a first stage `enc?` that, when pinned, is a possible
first stage at the header of `kg`, every query of the pinned game with its key generation pinned to
`kg` and its first stage pinned to `enc?` preserves the pinned invariant of `kg` and `enc?`. -/
private theorem pinnedImpl_preserves_pinnedInv (kg : (P.PK × P.SK) × P.det.KeygenRand)
    (hkg : kg.1 ∈ support P.det.toKEM.keygen)
    (enc? : Option ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand))
    (henc : ∀ enc, enc? = some enc → enc.1 ∈ support (P.det.toIncremental.encaps1 (P.det.toHeader
      kg.1.1)))
    (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (pinnedImpl auth sampleInitKey e (some kg) enc? mode)
      (PinnedInv auth (some kg.1) (enc?.map Prod.fst) e) :=
  SCKAScheme.securityImplAt_preservesInv _ _ _ _ _
    (fun _ exposed challenged h => h.with_bookkeeping auth exposed challenged)
    (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
    (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
    (SCKAScheme.challOf_recordsChallenges _)
    (fun s hs t res hres => pinnedCorrectness_preserves_at auth (kg? := some kg) (enc? := enc?)
      sampleInitKey hHdrSound hEkSound hCt1Sound hCt2Sound
      (fun _ h => by cases h; exact hkg) (fun _ enc h1 h2 => by cases h1; exact henc enc h2)
      (fun _ _ => ⟨kg, rfl⟩) s hs t res hres)

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- `Inv auth` is preserved by every query of the family pinned to a possible key pair only. -/
private theorem pinnedImpl_preserves_Inv (kg : (P.PK × P.SK) × P.det.KeygenRand)
    (hkg : kg.1 ∈ support P.det.toKEM.keygen) (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (pinnedImpl auth sampleInitKey e (some kg) none mode) (Inv auth) :=
  SCKAScheme.securityImplAt_preservesInv _ _ _ _ _
    (fun _ exposed challenged h => h.with_bookkeeping auth exposed challenged)
    (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
    (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
    (SCKAScheme.challOf_recordsChallenges _)
    (fun s hs t res hres => idealCorrectness_preserves_at auth sampleInitKey hHdrSound hEkSound
      hCt1Sound hCt2Sound (opsPossible_pinOps_kg e kg hkg) s hs t res hres)

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- The invariant of the first-stage deferral is preserved by every query of the family pinned to
`kg` and a possible first stage, on the successors with `e'` unexposed, for `e' = e` or
`e' = e + 1`. -/
private theorem encapsDeferralInv_preserved (kg : (P.PK × P.SK) × P.det.KeygenRand)
    (hkg : kg ∈ support P.det.toRandLeak.keygenRleak) (enc : (P.det.St × P.det.C₁ × P.K) ×
      P.det.Encaps1Rand)
    (henc : enc ∈ support (P.det.toRandLeak.encaps1Rleak (P.det.toHeader kg.1.1))) (mode : ℕ → Bool)
    (he' : e' = e ∨ e' = e + 1)
    (t : (securitySpec P AuthState).Domain) (s : GameState P AuthState)
    (hs : encapsDeferralInv auth e kg s)
    (res : (securitySpec P AuthState).Range t × GameState P AuthState)
    (hres : res ∈ support ((pinnedImpl auth sampleInitKey e (some kg) (some enc) mode t).run s))
    (hstop : decide (e' ∈ res.2.exposed) = false) : encapsDeferralInv auth e kg res.2 := by
  obtain ⟨hpin, hfresh⟩ := hs
  have hkg' : kg.1 ∈ support P.det.toKEM.keygen := by
    rw [← P.det.toRandLeak.keygen_fst]
    exact (mem_support_bind_iff _ _ _).mpr ⟨_, hkg, by simp⟩
  have henc' : ∀ enc', enc' ∈ support (P.det.toRandLeak.encaps1Rleak (P.det.toHeader kg.1.1)) →
      enc'.1 ∈ support (P.det.toIncremental.encaps1 (P.det.toHeader kg.1.1)) := fun enc' h => by
    exact (opsPossible_real (P := P)).2.1 e (P.det.toHeader kg.1.1) enc' h
  have hT := hpin.1.choose_spec.choose_spec.1
  by_cases hsent : phaseSent e .encaps1 s
  · have hA := not_runsPhase_of_phaseSent auth e hT .encaps1 hsent true
    have hB := not_runsPhase_of_phaseSent auth e hT .encaps1 hsent false
    simp only [GameState.stateAt, Bool.false_eq_true, ↓reduceIte] at hA hB
    rw [pinnedImpl_run_eq_of_not_runs_encaps1 auth sampleInitKey e (some kg) (some enc) none
      mode t s hA hB] at hres
    refine ⟨pinnedImpl_preserves_pinnedInv auth sampleInitKey hHdrSound hEkSound
      hCt1Sound hCt2Sound e kg hkg' none (fun _ h => by cases h) mode t s hpin res hres,
      fun hns => ?_⟩
    exact absurd (phaseSent_preserved e .encaps1 _ _
      (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
      (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
      (SCKAScheme.challOf_recordsChallenges _) t s hsent res hres) hns
  · have hall := hfresh hsent
    refine ⟨PinnedInv.weaken auth e (pinnedImpl_preserves_pinnedInv auth sampleInitKey
      hHdrSound hEkSound hCt1Sound hCt2Sound e kg hkg' (some enc)
      (fun _ h => by cases h; exact henc' enc henc) mode t s (hall enc henc) res hres),
      fun hns enc' henc'' => ?_⟩
    by_cases huse : usesPhase e .encaps1 t s = true
    · exact absurd (phaseSent_of_usesPhase auth sampleInitKey e .encaps1 (some kg) (some enc)
        mode he' t s huse res hres hstop) hns
    · rw [pinnedImpl_run_eq_of_not_uses_encaps1 auth sampleInitKey e (some kg) enc enc' mode
        t s (Bool.eq_false_iff.mpr huse)] at hres
      exact pinnedImpl_preserves_pinnedInv auth sampleInitKey hHdrSound hEkSound
        hCt1Sound hCt2Sound e kg hkg' (some enc')
        (fun _ h => by cases h; exact henc' enc' henc'')
        mode t s (hall enc' henc'') res hres

/-! ### The deferrals

First the first-stage sample of `e`, for each possible pinned key pair, and then the
key-generation sample move from the start of the run to their protocol calls.
-/

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders, drawing the key pair `kg ← P.det.toRandLeak.keygenRleak` before
the run or at the key generation of `e` gives equal acceptance probabilities from
`initState auth ik`, when both runs stop at the first exposure of `e'`, for `e' = e` or
`e' = e + 1`; the first stage is sampled at its call. The runs are against
`pinnedImpl (some kg) none mode` and `pinnedImpl none none mode`. -/
theorem stoppedRun_keygen_deferred (he' : e' = e ∨ e' = e + 1) (mode : ℕ → Bool)
    (adv : SecurityAdversary P AuthState) (ik : InitKey) :
    Pr{let x ← (do
      let kg ← P.det.toRandLeak.keygenRleak
      stoppedRun (pinnedImpl auth sampleInitKey e (some kg) none mode)
        (fun u => decide (e' ∈ u.exposed)) adv (initState auth ik))}[x = true] =
    Pr{let x ← (stoppedRun (pinnedImpl auth sampleInitKey e none none mode)
      (fun u => decide (e' ∈ u.exposed)) adv (initState auth ik))}[x = true] :=
  stoppedRun_sample_once_eq P.det.toRandLeak.keygenRleak
    (fun kg => pinnedImpl auth sampleInitKey e (some kg) none mode)
    (pinnedImpl auth sampleInitKey e none none mode) (fun u => decide (e' ∈ u.exposed))
    (Inv auth) (phaseSent e .keygen) (usesPhase e .keygen)
    (fun kg hkg t s hs res hres _ => pinnedImpl_preserves_Inv auth sampleInitKey hHdrSound
      hEkSound hCt1Sound hCt2Sound e kg (by
        rw [← P.det.toRandLeak.keygen_fst]
        exact (mem_support_bind_iff _ _ _).mpr ⟨_, hkg, by simp⟩) mode t s hs res hres)
    (fun _ _ t s _ hu res hres _ => phaseSent_preserved e .keygen _ _
      (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
      (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
      (SCKAScheme.challOf_recordsChallenges _) t s hu res hres)
    (fun t s _ hh kg _ kg' _ => ToVCVio.evalDistEq_of_eq
      (pinnedImpl_run_eq_of_not_uses_keygen auth sampleInitKey e kg kg' none mode t s hh))
    (fun t _ hs hu => usesPhase_eq_false_of_phaseSent auth e hs.1.choose_spec.choose_spec
      .keygen hu t)
    (fun _ _ t s _ hh res hres hstop => phaseSent_of_usesPhase auth sampleInitKey e .keygen _ _
      mode he' t s hh res hres hstop)
    (fun t s _ => pinnedImpl_sample_keygen_eq auth sampleInitKey e none mode t s)
    adv _ (Inv_initGameState auth ik)

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders, for a possible key pair `kg` pinned at `e`, drawing the first
stage `enc ← P.det.toRandLeak.encaps1Rleak (toHeader kg.pk)` before the run or at the first stage of
`e` gives equal acceptance probabilities from `initState auth ik`, when both runs stop at the first
exposure of `e'`, for `e' = e` or `e' = e + 1`. The runs are against
`pinnedImpl (some kg) (some enc) mode` and `pinnedImpl (some kg) none mode`. -/
theorem stoppedRun_encaps1_deferred (he' : e' = e ∨ e' = e + 1)
    (kg : (P.PK × P.SK) × P.det.KeygenRand)
    (hkg : kg ∈ support P.det.toRandLeak.keygenRleak) (mode : ℕ → Bool)
    (adv : SecurityAdversary P AuthState) (ik : InitKey) :
    Pr{let x ← (do
      let enc ← P.det.toRandLeak.encaps1Rleak (P.det.toHeader kg.1.1)
      stoppedRun (pinnedImpl auth sampleInitKey e (some kg) (some enc) mode)
        (fun u => decide (e' ∈ u.exposed)) adv (initState auth ik))}[x = true] =
    Pr{let x ← (stoppedRun (pinnedImpl auth sampleInitKey e (some kg) none mode)
      (fun u => decide (e' ∈ u.exposed)) adv (initState auth ik))}[x = true] :=
  stoppedRun_sample_once_eq (P.det.toRandLeak.encaps1Rleak (P.det.toHeader kg.1.1))
    (fun enc => pinnedImpl auth sampleInitKey e (some kg) (some enc) mode)
    (pinnedImpl auth sampleInitKey e (some kg) none mode) (fun u => decide (e' ∈ u.exposed))
    (encapsDeferralInv auth e kg) (phaseSent e .encaps1) (usesPhase e .encaps1)
    (fun enc henc t s hs res hres hstop => encapsDeferralInv_preserved auth sampleInitKey
      hHdrSound hEkSound hCt1Sound hCt2Sound e kg hkg enc henc mode he' t s hs res hres
      hstop)
    (fun _ _ t s _ hu res hres _ => phaseSent_preserved e .encaps1 _ _
      (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
      (fun _ st => schemeWith_sendArleak_forget auth _ sampleInitKey st)
      (SCKAScheme.challOf_recordsChallenges _) t s hu res hres)
    (fun t s _ hh enc _ enc' _ => ToVCVio.evalDistEq_of_eq
      (pinnedImpl_run_eq_of_not_uses_encaps1 auth sampleInitKey e (some kg) enc enc' mode t s
        hh))
    (fun t _ hs hu => usesPhase_eq_false_of_phaseSent auth e
      hs.1.1.choose_spec.choose_spec.1 .encaps1 hu t)
    (fun _ _ t s _ hh res hres hstop => phaseSent_of_usesPhase auth sampleInitKey e .encaps1 _ _
      mode he' t s hh res hres hstop)
    (fun t _ hs => pinnedImpl_sample_encaps1_eq auth sampleInitKey e kg hs.1 mode t)
    adv _ (encapsDeferralInv_initState auth e kg ik)

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Assuming sound stream decoders, drawing the KEM material of `e` before the run or at the
protocol calls gives equal acceptance probabilities: for every challenge mode `mode`, the pinned
game with `kemMat ← sampleMaterial` and the ideal game under `mode`, both run from
`initState auth ik` and stopped at the first exposure of `e'`, for `e' = e` or `e' = e + 1`. For
`mode := hybridMode i` and `e' = e`, the ideal game is the stopped hybrid
`stoppedHybridExp adv i e ik`, so `i = e - 1` (`real`) and `i = e` (`random`) give
`Pr[P_e^x = true] = Pr[S_e^x = true]`. -/
theorem stoppedRun_material_deferred (he' : e' = e ∨ e' = e + 1) (mode : ℕ → Bool)
    (adv : SecurityAdversary P AuthState) (ik : InitKey) :
    Pr{let x ← (do
      let kemMat ← sampleMaterial
      stoppedRun (pinnedImpl auth sampleInitKey e (some kemMat.kg) (some kemMat.enc) mode)
        (fun u => decide (e' ∈ u.exposed)) adv (initState auth ik))}[x = true] =
    Pr{let x ← (stoppedRun (idealImpl auth sampleInitKey mode)
      (fun u => decide (e' ∈ u.exposed)) adv (initState auth ik))}[x = true] := by
  rw [← pinnedImpl_none_none auth sampleInitKey e mode,
    ← stoppedRun_keygen_deferred auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound e he' mode adv ik]
  simp only [sampleMaterial, bind_assoc, pure_bind, map_bind]
  refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun kg hkg => ?_
  simpa only [map_bind] using stoppedRun_encaps1_deferred auth sampleInitKey hHdrSound
    hEkSound hCt1Sound hCt2Sound e he' kg hkg mode adv ik

end Oracles

end SPQR
