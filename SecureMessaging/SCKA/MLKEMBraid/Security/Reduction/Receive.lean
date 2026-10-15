/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.ProjectionBasic
import SecureMessaging.SCKA.MLKEMBraid.Security.Invariant.Receive

/-!
# Receive projections of the masked simulator

The masked receive preserves the repaired receive's joint output/state behavior. Local payload
facts identify the retained second ciphertext component; repaired completion uses the derived
test key without assuming that actual decapsulation succeeds.
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

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

end MLKEMBraid.NoAuth
