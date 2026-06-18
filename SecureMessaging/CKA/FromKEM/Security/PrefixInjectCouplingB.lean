/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.PrefixInjectCouplingCore

/-!
# CKA from KEM — Injected-Prefix Coupling, challenged party B

Mirror of `PrefixInjectCouplingA` for a challenged party B: the injecting
send is `OSendA` at bumped counter `gp.challengeEpoch - 1`, the receive of
the injected message is `ORecvB`, and the pause happens at `OChallB` in the
`preBToAHonestState`/`preBToAReductionState` shapes.
-/

open OracleSpec OracleComp ENNReal KEMScheme
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-! ## The pre-injection invariant, challenged party B

`preTraceB` mirrors `preTraceA` with the B-side bounds: the injection now
happens at an A-send, bumping `tA` to `gp.challengeEpoch - 1`, so the
alternation trace keeps `tA` at least two epochs below the challenge epoch at
the receive that could precede the injecting send, and the challenge epoch is
even. -/

private def preTraceB
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Prop :=
  match σ.lastAction with
  | none => σ.tA = 0 ∧ σ.tB = 0
  | some .sendA => σ.tA % 2 = 1 ∧ σ.tA = σ.tB + 1 ∧ σ.tA + 3 ≤ gp.challengeEpoch
  | some .recvB => σ.tB % 2 = 1 ∧ σ.tA = σ.tB ∧ σ.tB + 3 ≤ gp.challengeEpoch
  | some .sendB => σ.tB % 2 = 0 ∧ σ.tB = σ.tA + 1 ∧ σ.tB + 2 ≤ gp.challengeEpoch
  | some .recvA => σ.tA % 2 = 0 ∧ σ.tA = σ.tB ∧ σ.tA + 2 ≤ gp.challengeEpoch
  | some .challA | some .challB => False

private def preInvB
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Prop :=
  securityShapeInv kem σ ∧ 2 ≤ gp.challengeEpoch ∧ preTraceB gp σ

/-- Inside the B-side pre-injection invariant `willChallengeB` is false: where
a challenge would be a valid next step, the counter is still at least two
epochs below the challenge epoch. -/
private lemma willChallengeB_eq_false_of_preInvB
    (kem : KEMScheme ProbComp K PK SK C)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : preInvB kem gp σ) :
    willChallengeB gp σ = false := by
  obtain ⟨-, he2, htrace⟩ := hσ
  by_cases hvalid : CKAScheme.validStep σ.lastAction .challB = true
  · have hne : (σ.tB + 1 == gp.challengeEpoch) = false := by
      rw [beq_eq_false_iff_ne]
      cases hlast : σ.lastAction with
      | none => simp [CKAScheme.validStep, hlast] at hvalid
      | some act =>
          cases act <;> simp [CKAScheme.validStep, hlast] at hvalid
          case recvB =>
            simp only [preTraceB, hlast] at htrace
            omega
    simp [willChallengeB, hne]
  · simp [willChallengeB, Bool.eq_false_of_not_eq_true hvalid]

/-! ## Preservation of the B-side pre-injection invariant

One lemma per state-changing oracle of `securityImpl`, mirroring the A-side
lemmas with the `preTraceB` bounds.  The guarded send is now `sendA`; the
`sendA` randomness-leaking variant needs the PCS gate and the even challenge
epoch for its bound, the `sendB` ones need neither. -/

private lemma preInvB_preserved_sendA_of_not_inject [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.B)
    (heven : gp.challengeEpoch % 2 = 0)
    (σ : SecurityState K PK SK C)
    (hσ : preInvB kem gp σ)
    (hnoinj : sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 } = false)
    (z : Option (Message C PK × K) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)).run σ)) :
    preInvB kem gp z.2 := by
  obtain ⟨hshape, he2, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleSendA (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .sendA
  case false =>
    have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleSendA, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he2, htrace⟩
  case true =>
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
      simp [CKAScheme.validStep] at hGuard
    all_goals (
      have hne : tA + 1 ≠ gp.challengeEpoch - 1 := by
        simpa [sendAInjectsChallengeKey, hparty] using hnoinj
      rcases (by simpa [securityShapeInv] using hshape) with
        ⟨pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [CKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
      have hz' : ∃ c key pk' sk',
          (c, key) ∈ support (kem.encaps pk) ∧
          (pk', sk') ∈ support kem.keygen ∧
          (some ((c, pk'), key),
            ({ stA := State.recvReady sk', stB := State.recvReady sk,
               rhoA := some (c, pk'), rhoB := none,
               keyA := some key, keyB := none,
               correct := corr, lastAction := some .sendA,
               tA := tA + 1, tB := tB } : SecurityState K PK SK C)) = z := by
        simpa [CKAScheme.validStep, scheme, send] using hz
      obtain ⟨c, key, pk', sk', hck, hks', rfl⟩ := hz'
      refine ⟨?_, he2, ?_⟩
      · exact ⟨pk, sk, c, key, pk', sk', hks, hck, hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [preTraceB] at htrace ⊢
        omega)

private lemma preInvB_preserved_recvB [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : preInvB kem gp σ)
    (z : Unit × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σ)) :
    preInvB kem gp z.2 := by
  obtain ⟨hshape, he2, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .recvB
  case false =>
    have hzEq : z = ((), ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleRecvB, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he2, htrace⟩
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hGuard
    cases action <;> simp [CKAScheme.validStep] at hGuard
    · -- previous action was the A-send carrying the pending message
      rcases (by simpa [securityShapeInv] using hshape) with
        ⟨pk, sk, hks, c, key, hck, pk', sk', hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hdec := decapsDet_eq_some_of_mem_support
        (pk := pk) (sk := sk) (c := c) (key := key) kem hDet hkem hks hck
      have hzEq : z = ((), ⟨State.recvReady sk', State.sendReady pk',
          none, none, none, none, corr, some .recvB, tA, tB + 1⟩) := by
        simpa [CKAScheme.oracleRecvB, CKAScheme.validStep, scheme, recv, hdec,
          stateT_run] using hz
      subst hzEq
      refine ⟨?_, he2, ?_⟩
      · exact ⟨pk', sk', hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [preTraceB] at htrace ⊢
        omega
    · -- a challenge never appears as the last action inside the invariant
      exact False.elim (by simp only [securityShapeInv] at hshape)

private lemma preInvB_preserved_recvA [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : preInvB kem gp σ)
    (z : Unit × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σ)) :
    preInvB kem gp z.2 := by
  obtain ⟨hshape, he2, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .recvA
  case false =>
    have hzEq : z = ((), ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleRecvA, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he2, htrace⟩
  case true =>
    rcases last with _ | action
    · simp [CKAScheme.validStep] at hGuard
    cases action <;> simp [CKAScheme.validStep] at hGuard
    · -- previous action was the B-send carrying the pending message
      rcases (by simpa [securityShapeInv] using hshape) with
        ⟨pk, sk, hks, c, key, hck, pk', sk', hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hdec := decapsDet_eq_some_of_mem_support
        (pk := pk) (sk := sk) (c := c) (key := key) kem hDet hkem hks hck
      have hzEq : z = ((), ⟨State.sendReady pk', State.recvReady sk',
          none, none, none, none, corr, some .recvA, tA + 1, tB⟩) := by
        simpa [CKAScheme.oracleRecvA, CKAScheme.validStep, scheme, recv, hdec,
          stateT_run] using hz
      subst hzEq
      refine ⟨?_, he2, ?_⟩
      · exact ⟨pk', sk', hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [preTraceB] at htrace ⊢
        omega
    · -- a challenge never appears as the last action inside the invariant
      exact False.elim (by simp only [securityShapeInv] at hshape)

private lemma preInvB_preserved_sendB [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : preInvB kem gp σ)
    (z : Option (Message C PK × K) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)).run σ)) :
    preInvB kem gp z.2 := by
  obtain ⟨hshape, he2, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleSendB (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .sendB
  case false =>
    have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleSendB, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he2, htrace⟩
  case true =>
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
      simp [CKAScheme.validStep] at hGuard
    rcases (by simpa [securityShapeInv] using hshape) with
      ⟨pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [CKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
    have hz' : ∃ c key pk' sk',
        (c, key) ∈ support (kem.encaps pk) ∧
        (pk', sk') ∈ support kem.keygen ∧
        (some ((c, pk'), key),
          ({ stA := State.recvReady sk, stB := State.recvReady sk',
             rhoA := none, rhoB := some (c, pk'),
             keyA := none, keyB := some key,
             correct := corr, lastAction := some .sendB,
             tA := tA, tB := tB + 1 } : SecurityState K PK SK C)) = z := by
      simpa [CKAScheme.validStep, scheme, send] using hz
    obtain ⟨c, key, pk', sk', hck, hks', rfl⟩ := hz'
    refine ⟨?_, he2, ?_⟩
    · exact ⟨pk, sk, c, key, pk', sk', hks, hck, hks', rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [preTraceB] at htrace ⊢
      omega

private lemma preInvB_preserved_sendA_rleak [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hΔ : 2 ≤ gp.ΔPCS)
    (heven : gp.challengeEpoch % 2 = 0)
    (σ : SecurityState K PK SK C)
    (hσ : preInvB kem gp σ)
    (z : Option (Message C PK × K × leak.Rand) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run σ)) :
    preInvB kem gp z.2 := by
  obtain ⟨hshape, he2, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .sendA
  case false =>
    have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleSendA_rleak, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he2, htrace⟩
  case true =>
    by_cases hPCS : max (tA + 1) tB + gp.ΔPCS ≤ gp.challengeEpoch
    · rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
        simp [CKAScheme.validStep] at hGuard
      all_goals (
        rcases (by simpa [securityShapeInv] using hshape) with
          ⟨pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rw [CKAScheme.oracleSendA_rleak, StateT.run_bind, StateT.run_get] at hz
        have hz' : ∃ c key rEnc pk' sk' rKG,
            ((c, key), rEnc) ∈ support (leak.encaps_rleak pk) ∧
            ((pk', sk'), rKG) ∈ support leak.keygen_rleak ∧
            (some ((c, pk'), key, (rEnc, rKG)),
              ({ stA := State.recvReady sk', stB := State.recvReady sk,
                 rhoA := some (c, pk'), rhoB := none,
                 keyA := some key, keyB := none,
                 correct := corr, lastAction := some .sendA,
                 tA := tA + 1, tB := tB } : SecurityState K PK SK C)) = z := by
          simpa [CKAScheme.validStep, CKAScheme.allowCorrPCS, hPCS, scheme,
            send_rleak] using hz
        obtain ⟨c, key, rEnc, pk', sk', rKG, hck, hks', rfl⟩ := hz'
        refine ⟨?_, he2, ?_⟩
        · exact ⟨pk, sk, c, key, pk', sk', hks,
            mem_support_encaps_of_encaps_rleak kem leak hck,
            mem_support_keygen_of_keygen_rleak kem leak hks',
            rfl, rfl, rfl, rfl, rfl, rfl⟩
        · simp only [preTraceB] at htrace ⊢
          omega)
    · have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
        simpa [CKAScheme.oracleSendA_rleak, hGuard, CKAScheme.allowCorrPCS, hPCS,
          stateT_run] using hz
      subst hzEq
      exact ⟨hshape, he2, htrace⟩

private lemma preInvB_preserved_sendB_rleak [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C)
    (hσ : preInvB kem gp σ)
    (z : Option (Message C PK × K × leak.Rand) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp false
      (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run σ)) :
    preInvB kem gp z.2 := by
  obtain ⟨hshape, he2, htrace⟩ := hσ
  change z ∈ support ((CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σ) at hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  cases hGuard : CKAScheme.validStep last .sendB
  case false =>
    have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
      simpa [CKAScheme.oracleSendB_rleak, hGuard, stateT_run] using hz
    subst hzEq
    exact ⟨hshape, he2, htrace⟩
  case true =>
    by_cases hPCS : max tA (tB + 1) + gp.ΔPCS ≤ gp.challengeEpoch
    · rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
        simp [CKAScheme.validStep] at hGuard
      rcases (by simpa [securityShapeInv] using hshape) with
        ⟨pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [CKAScheme.oracleSendB_rleak, StateT.run_bind, StateT.run_get] at hz
      have hz' : ∃ c key rEnc pk' sk' rKG,
          ((c, key), rEnc) ∈ support (leak.encaps_rleak pk) ∧
          ((pk', sk'), rKG) ∈ support leak.keygen_rleak ∧
          (some ((c, pk'), key, (rEnc, rKG)),
            ({ stA := State.recvReady sk, stB := State.recvReady sk',
               rhoA := none, rhoB := some (c, pk'),
               keyA := none, keyB := some key,
               correct := corr, lastAction := some .sendB,
               tA := tA, tB := tB + 1 } : SecurityState K PK SK C)) = z := by
        simpa [CKAScheme.validStep, CKAScheme.allowCorrPCS, hPCS, scheme,
          send_rleak] using hz
      obtain ⟨c, key, rEnc, pk', sk', rKG, hck, hks', rfl⟩ := hz'
      refine ⟨?_, he2, ?_⟩
      · exact ⟨pk, sk, c, key, pk', sk', hks,
          mem_support_encaps_of_encaps_rleak kem leak hck,
          mem_support_keygen_of_keygen_rleak kem leak hks',
          rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [preTraceB] at htrace ⊢
        omega
    · have hzEq : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩) := by
        simpa [CKAScheme.oracleSendB_rleak, hGuard, CKAScheme.allowCorrPCS, hPCS,
          stateT_run] using hz
      subst hzEq
      exact ⟨hshape, he2, htrace⟩

/-! ## The coupling relation, challenged party B

Mirror of `coupleRelA` with the roles of the two parties swapped.  Before the
injecting A-send the states are equal and satisfy the B-side pre-injection
invariant.  After the injecting send the states differ exactly in A's stored
secret (`skStar` on the injected side, the discarded fresh draw on the
reduction side), and the recorded message carries `pkStar` together with a
ciphertext that decapsulates correctly under B's current key.  After B
receives that message both sides sit at `sendReady pkStar` waiting for the
challenge query.  Once the challenged party's counter passes the challenge
epoch neither side can pause. -/

/-- Coupling relation between the injected state `σH` and reduction state `σR`
for the prefix-injection argument when party `B` is challenged; mirror of
`coupleRelA`. -/
def coupleRelB
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (skStar : SK)
    (σH σR : SecurityState K PK SK C) : Prop :=
  (σH = σR ∧ preInvB kem gp σR)
  ∨ (∃ skB cInj kInj skR,
      σR.stB = State.recvReady skB ∧ σR.stA = State.recvReady skR ∧
      σR.rhoA = some (cInj, pkStar) ∧ σR.keyA = some kInj ∧
      hDet.decapsDet skB cInj = some kInj ∧
      σR.lastAction = some .sendA ∧ σR.tA + 1 = gp.challengeEpoch ∧
      σR.tB + 2 = gp.challengeEpoch ∧
      σH = { σR with stA := State.recvReady skStar })
  ∨ (σR.stB = State.sendReady pkStar ∧ willChallengeB gp σR = true ∧
      epochCounterInv σR ∧ σH = { σR with stA := State.recvReady skStar })
  ∨ (challengePassed gp σH ∧ challengePassed gp σR)

/-- Postcondition of the B-side prefix coupling: either both runs finished, or
both paused at the challenge query with the same continuation, in the state
shapes the B-side challenge bridges expect. -/
def couplePostB
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (skStar : SK) {α : Type} :
    CKAChallengeStepResult leak α × SecurityState K PK SK C →
      CKAChallengeStepResult leak α × SecurityState K PK SK C → Prop :=
  fun z z' =>
    ((∃ a, z.1 = CKAChallengeStepResult.done a) ∧
      (∃ a', z'.1 = CKAChallengeStepResult.done a'))
    ∨ ∃ cont base,
        z = (.pausedB cont, preBToAHonestState base pkStar skStar) ∧
        z' = (.pausedB cont, preBToAReductionState base pkStar) ∧
        epochCounterInv base ∧ willChallengeB gp base = true

/-- One coupled oracle step from equal states inside the B-side pre-injection
invariant.  The injecting A-send is the transition into the injected phase;
every other oracle preserves the invariant. -/
private lemma coupleRelB_step_pre [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.B)
    (hΔ : 2 ≤ gp.ΔPCS)
    (heven : gp.challengeEpoch % 2 = 0)
    (pkStar : PK) (skStar : SK)
    (t : (securitySpec leak).Domain)
    (σ : SecurityState K PK SK C)
    (hpre : preInvB kem gp σ) :
    RelTriple
      ((securityImplWithChallengeKeyPair kem hDet leak gp false pkStar skStar t).run σ)
      ((prefixImpl kem hDet leak gp pkStar t).run σ)
      (fun p q => p.1 = q.1 ∧ coupleRelB kem hDet gp pkStar skStar p.2 q.2) := by
  have hWB : willChallengeB gp σ = false :=
    willChallengeB_eq_false_of_preInvB kem gp σ hpre
  have hWA : willChallengeA gp σ = false := by
    simp [willChallengeA, hparty]
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  all_goals
    try cases uSendA
    try cases uRecvA
    try cases uSendB
    try cases uRecvB
    try cases uChallA
    try cases uChallB
    try cases uCorrA
    try cases uCorrB
    try cases uRLeakA
    try cases uRLeakB
  · -- adversary randomness: the same lifted draw on both sides
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σ)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σ) _
    have hrun : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σ =
        (QueryImpl.ofLift unifSpec ProbComp n >>= fun y => pure (y, σ)) := by
      change (CKAScheme.oracleUnif (State PK SK) K (Message C PK) n).run σ = _
      simp [CKAScheme.oracleUnif, StateT.run_monadLift, monadLift_self]
    rw [hrun]
    refine relTriple_bind (relTriple_refl _) ?_
    intro y y' hy
    cases hy
    exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
  · -- O-Send-A: the injecting send when the guard fires, honest otherwise
    change RelTriple
      ((oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σ)
      ((oracleSendAWithChallengePk kem gp pkStar ()).run σ) _
    by_cases hgA : sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 } = true
    · by_cases hvalid : CKAScheme.validStep σ.lastAction .sendA = true
      · -- the injecting send: enter the injected phase
        obtain ⟨hshape, he2, htrace⟩ := hpre
        rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
        rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
          simp [CKAScheme.validStep] at hvalid
        all_goals (
          rcases (by simpa [securityShapeInv] using hshape) with
            ⟨pk, sk, hks, rfl, rfl, rfl, rfl, rfl, rfl⟩
          simp only [preTraceB] at htrace
          have htAe : tA + 1 = gp.challengeEpoch - 1 := by
            simpa [sendAInjectsChallengeKey, hparty] using hgA
          rw [oracleSendAWithChallengeKeyPair_run_sendReady kem gp pkStar skStar
              _ pk rfl rfl,
            oracleSendAWithChallengePk_run_sendReady kem gp pkStar _ pk rfl rfl]
          simp only [hgA, ↓reduceIte]
          refine relTriple_bind (relTriple_refl_support (kem.encaps pk)) ?_
          rintro ck ck' ⟨rfl, hck⟩
          obtain ⟨c, key⟩ := ck
          refine relTriple_bind (relTriple_refl_support kem.keygen) ?_
          rintro ks ks' ⟨rfl, hks'⟩
          obtain ⟨pkG, skG⟩ := ks
          have hdec : hDet.decapsDet sk c = some key :=
            decapsDet_eq_some_of_mem_support kem hDet hkem hks hck
          exact relTriple_pure_pure ⟨rfl, Or.inr (Or.inl ⟨sk, c, key, skG, rfl, rfl,
            rfl, rfl, hdec, rfl, (show tA + 1 + 1 = gp.challengeEpoch by omega),
            (show tB + 2 = gp.challengeEpoch by omega), rfl⟩)⟩)
      · -- the guard fired on an invalid step: both sides are no-ops
        have hF : CKAScheme.validStep σ.lastAction .sendA = false :=
          Bool.eq_false_of_not_eq_true hvalid
        have hH : (oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σ =
            pure (none, σ) := by
          simp [oracleSendAWithChallengeKeyPair, hF]
        have hR : (oracleSendAWithChallengePk kem gp pkStar ()).run σ =
            pure (none, σ) := by
          simp [oracleSendAWithChallengePk, hF]
        rw [hH, hR]
        exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
    · -- ordinary A-send: both sides generate honestly
      have hg : sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 } = false :=
        Bool.eq_false_of_not_eq_true hgA
      rw [oracleSendAWithChallengeKeyPair_run_eq_of_not_inject kem hDet leak gp pkStar
          skStar σ hg,
        oracleSendAWithChallengePk_run_eq_of_not_inject kem hDet leak gp pkStar σ hg]
      exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
        preInvB_preserved_sendA_of_not_inject kem hDet leak gp hparty heven σ hpre hg
          p hsup⟩⟩
  · -- O-Recv-A: the same oracle on the same state
    exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
      preInvB_preserved_recvA kem hDet leak hkem gp σ hpre p hsup⟩⟩
  · -- O-Send-B: the inject guard is off for a B-challenge
    change RelTriple
      ((oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σ)
      ((oracleSendBWithChallengePk kem gp pkStar ()).run σ) _
    have hg : sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 } = false := by
      simp [sendBInjectsChallengeKey, hparty]
    rw [oracleSendBWithChallengeKeyPair_run_eq_of_not_inject kem hDet leak gp pkStar
        skStar σ hg,
      oracleSendBWithChallengePk_run_eq_of_not_inject kem hDet leak gp pkStar σ hg]
    exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
      preInvB_preserved_sendB kem hDet leak gp σ hpre p hsup⟩⟩
  · -- O-Recv-B: the same oracle on the same state
    exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
      preInvB_preserved_recvB kem hDet leak hkem gp σ hpre p hsup⟩⟩
  · -- O-Chall-A: wrong party, the guard is false
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ) _
    rw [securityImpl_challA_run_of_not_will kem hDet leak gp false σ hWA]
    exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
  · -- O-Chall-B: the guard is false inside the invariant
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ) _
    rw [securityImpl_challB_run_of_not_will kem hDet leak gp false σ hWB]
    exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
  · -- O-Corrupt-A: never writes the state
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σ)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σ) _
    have hrun : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .A then some σ.stA else none, σ) := by
      change (CKAScheme.oracleCorruptA gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .A <;> simp [CKAScheme.oracleCorruptA, h]
    rw [hrun]
    exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
  · -- O-Corrupt-B: never writes the state
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σ)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σ) _
    have hrun : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .B then some σ.stB else none, σ) := by
      change (CKAScheme.oracleCorruptB gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .B <;> simp [CKAScheme.oracleCorruptB, h]
    rw [hrun]
    exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, hpre⟩⟩
  · -- O-Send-A-rleak: the same oracle on the same state
    exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
      preInvB_preserved_sendA_rleak kem hDet leak gp hΔ heven σ hpre p hsup⟩⟩
  · -- O-Send-B-rleak: the same oracle on the same state
    exact relTriple_refl_support_post fun p hsup => ⟨rfl, Or.inl ⟨rfl,
      preInvB_preserved_sendB_rleak kem hDet leak gp σ hpre p hsup⟩⟩

/-- One coupled oracle step in the injected phase.  The states differ exactly
in A's stored secret; B's receive of the injected message is the transition
into the challenge phase, every other oracle is a no-op or leaves the
divergent slot untouched. -/
private lemma coupleRelB_step_inj [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.B)
    (hΔ : 2 ≤ gp.ΔPCS)
    (hFS : gp.ΔFS = 0)
    (pkStar : PK) (skStar : SK)
    (skB : SK) (cInj : C) (kInj : K) (skR : SK)
    (ρB : Option (Message C PK)) (kB : Option K) (corr : Bool) (tA tB : ℕ)
    (hdec : hDet.decapsDet skB cInj = some kInj)
    (htA : tA + 1 = gp.challengeEpoch)
    (htB : tB + 2 = gp.challengeEpoch)
    (t : (securitySpec leak).Domain) :
    RelTriple
      ((securityImplWithChallengeKeyPair kem hDet leak gp false pkStar skStar t).run
        ⟨State.recvReady skStar, State.recvReady skB, some (cInj, pkStar), ρB,
          some kInj, kB, corr, some CKAScheme.CKAAction.sendA, tA, tB⟩)
      ((prefixImpl kem hDet leak gp pkStar t).run
        ⟨State.recvReady skR, State.recvReady skB, some (cInj, pkStar), ρB,
          some kInj, kB, corr, some CKAScheme.CKAAction.sendA, tA, tB⟩)
      (fun p q => p.1 = q.1 ∧ coupleRelB kem hDet gp pkStar skStar p.2 q.2) := by
  set σHl : SecurityState K PK SK C :=
    ⟨State.recvReady skStar, State.recvReady skB, some (cInj, pkStar), ρB,
      some kInj, kB, corr, some CKAScheme.CKAAction.sendA, tA, tB⟩ with hσHl
  set σRl : SecurityState K PK SK C :=
    ⟨State.recvReady skR, State.recvReady skB, some (cInj, pkStar), ρB,
      some kInj, kB, corr, some CKAScheme.CKAAction.sendA, tA, tB⟩ with hσRl
  have hrelSame : coupleRelB kem hDet gp pkStar skStar σHl σRl :=
    Or.inr (Or.inl ⟨skB, cInj, kInj, skR, rfl, rfl, rfl, rfl, hdec, rfl, htA, htB, rfl⟩)
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  all_goals
    try cases uSendA
    try cases uRecvA
    try cases uSendB
    try cases uRecvB
    try cases uChallA
    try cases uChallB
    try cases uCorrA
    try cases uCorrB
    try cases uRLeakA
    try cases uRLeakB
  · -- adversary randomness
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σRl) _
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σ =
        (QueryImpl.ofLift unifSpec ProbComp n >>= fun y => pure (y, σ)) := by
      intro σ
      change (CKAScheme.oracleUnif (State PK SK) K (Message C PK) n).run σ = _
      simp [CKAScheme.oracleUnif, StateT.run_monadLift, monadLift_self]
    rw [hrun σHl, hrun σRl]
    refine relTriple_bind (relTriple_refl _) ?_
    intro y y' hy
    cases hy
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-A: not A's turn
    change RelTriple
      ((oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σHl)
      ((oracleSendAWithChallengePk kem gp pkStar ()).run σRl) _
    have hH : (oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σHl =
        pure (none, σHl) := by
      simp [oracleSendAWithChallengeKeyPair, CKAScheme.validStep, hσHl]
    have hR : (oracleSendAWithChallengePk kem gp pkStar ()).run σRl =
        pure (none, σRl) := by
      simp [oracleSendAWithChallengePk, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Recv-A: not a receive slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σRl) _
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σHl =
        pure ((), σHl) := by
      change (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleRecvA, CKAScheme.validStep, hσHl]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σRl =
        pure ((), σRl) := by
      change (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleRecvA, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-B: not B's turn
    change RelTriple
      ((oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σHl)
      ((oracleSendBWithChallengePk kem gp pkStar ()).run σRl) _
    have hH : (oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σHl =
        pure (none, σHl) := by
      simp [oracleSendBWithChallengeKeyPair, CKAScheme.validStep, hσHl]
    have hR : (oracleSendBWithChallengePk kem gp pkStar ()).run σRl =
        pure (none, σRl) := by
      simp [oracleSendBWithChallengePk, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Recv-B: B receives the injected message; enter the challenge phase
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σRl) _
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σHl =
        pure ((), ⟨State.recvReady skStar, State.sendReady pkStar, none, ρB,
          none, kB, corr, some CKAScheme.CKAAction.recvB, tA, tB + 1⟩) := by
      change (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleRecvB, CKAScheme.validStep, scheme, recv, hdec, hσHl]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σRl =
        pure ((), ⟨State.recvReady skR, State.sendReady pkStar, none, ρB,
          none, kB, corr, some CKAScheme.CKAAction.recvB, tA, tB + 1⟩) := by
      change (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleRecvB, CKAScheme.validStep, scheme, recv, hdec, hσRl]
    rw [hH, hR]
    refine relTriple_pure_pure ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_, rfl⟩))⟩
    · simp [willChallengeB, CKAScheme.validStep, hparty]
      omega
    · simp only [epochCounterInv]
      omega
  · -- O-Chall-A: wrong party
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σRl) _
    have hWAH : willChallengeA gp σHl = false := by
      simp [willChallengeA, hparty]
    have hWAR : willChallengeA gp σRl = false := by
      simp [willChallengeA, hparty]
    rw [securityImpl_challA_run_of_not_will kem hDet leak gp false σHl hWAH,
      securityImpl_challA_run_of_not_will kem hDet leak gp false σRl hWAR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Chall-B: the guard is false right after the injecting send
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σRl) _
    have hWBH : willChallengeB gp σHl = false := by
      simp [willChallengeB, CKAScheme.validStep, hσHl]
    have hWBR : willChallengeB gp σRl = false := by
      simp [willChallengeB, CKAScheme.validStep, hσRl]
    rw [securityImpl_challB_run_of_not_will kem hDet leak gp false σHl hWBH,
      securityImpl_challB_run_of_not_will kem hDet leak gp false σRl hWBR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Corrupt-A: gated off one epoch before the challenge
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σRl) _
    have htApred : tA = gp.challengeEpoch - 1 := by omega
    have hpcs : CKAScheme.allowCorrPCS gp σRl = false :=
      allowCorrPCS_false_of_two_le_deltaPCS_of_tA_pred gp σRl hΔ htApred
    have hcA : CKAScheme.allowCorr gp σRl .A = false := by
      simp [CKAScheme.allowCorr, hpcs, CKAScheme.allowCorrFS, hFS,
        (show σRl.tA = tA from rfl)]
      omega
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .A then some σ.stA else none, σ) := by
      intro σ
      change (CKAScheme.oracleCorruptA gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .A <;> simp [CKAScheme.oracleCorruptA, h]
    rw [hrun σHl, hrun σRl,
      show CKAScheme.allowCorr gp σHl .A = CKAScheme.allowCorr gp σRl .A from rfl,
      hcA]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Corrupt-B: B's state is shared; the outputs agree
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σRl) _
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .B then some σ.stB else none, σ) := by
      intro σ
      change (CKAScheme.oracleCorruptB gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .B <;> simp [CKAScheme.oracleCorruptB, h]
    rw [hrun σHl, hrun σRl,
      show (if CKAScheme.allowCorr gp σHl .B then some σHl.stB else none) =
        (if CKAScheme.allowCorr gp σRl .B then some σRl.stB else none) from rfl]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-A-rleak: not a send slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run σRl)
      _
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run
        σHl = pure (none, σHl) := by
      change (CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleSendA_rleak, CKAScheme.validStep, hσHl]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run
        σRl = pure (none, σRl) := by
      change (CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleSendA_rleak, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-B-rleak: not a send slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run σRl)
      _
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run
        σHl = pure (none, σHl) := by
      change (CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleSendB_rleak, CKAScheme.validStep, hσHl]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run
        σRl = pure (none, σRl) := by
      change (CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleSendB_rleak, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩

/-- One coupled oracle step in the challenge phase.  Both sides sit at
`sendReady pkStar`; an ordinary B-send or a fired challenge query moves both
past the challenge epoch, everything else is a no-op or leaves the divergent
slot untouched. -/
private lemma coupleRelB_step_chall [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.B)
    (hΔ : 2 ≤ gp.ΔPCS)
    (hFS : gp.ΔFS = 0)
    (pkStar : PK) (skStar : SK)
    (sA : State PK SK) (ρA ρB : Option (Message C PK)) (kA kB : Option K)
    (corr : Bool) (last : Option CKAScheme.CKAAction) (tA tB : ℕ)
    (hWill : willChallengeB gp
      (⟨sA, State.sendReady pkStar, ρA, ρB, kA, kB, corr, last, tA, tB⟩ :
        SecurityState K PK SK C) = true)
    (hInv : epochCounterInv
      (⟨sA, State.sendReady pkStar, ρA, ρB, kA, kB, corr, last, tA, tB⟩ :
        SecurityState K PK SK C))
    (t : (securitySpec leak).Domain) :
    RelTriple
      ((securityImplWithChallengeKeyPair kem hDet leak gp false pkStar skStar t).run
        ⟨State.recvReady skStar, State.sendReady pkStar, ρA, ρB, kA, kB, corr,
          last, tA, tB⟩)
      ((prefixImpl kem hDet leak gp pkStar t).run
        ⟨sA, State.sendReady pkStar, ρA, ρB, kA, kB, corr, last, tA, tB⟩)
      (fun p q => p.1 = q.1 ∧ coupleRelB kem hDet gp pkStar skStar p.2 q.2) := by
  obtain ⟨hvalidChall, htBe⟩ : CKAScheme.validStep last .challB = true ∧
      tB + 1 = gp.challengeEpoch := by
    simpa [willChallengeB, hparty] using hWill
  have hlastD : last = some CKAScheme.CKAAction.recvB := by
    cases hl : last with
    | none => simp [CKAScheme.validStep, hl] at hvalidChall
    | some act =>
        cases act <;> simp [CKAScheme.validStep, hl] at hvalidChall
        rfl
  subst hlastD
  set σHl : SecurityState K PK SK C :=
    ⟨State.recvReady skStar, State.sendReady pkStar, ρA, ρB, kA, kB, corr,
      some CKAScheme.CKAAction.recvB, tA, tB⟩ with hσHl
  set σRl : SecurityState K PK SK C :=
    ⟨sA, State.sendReady pkStar, ρA, ρB, kA, kB, corr,
      some CKAScheme.CKAAction.recvB, tA, tB⟩ with hσRl
  have hrelSame : coupleRelB kem hDet gp pkStar skStar σHl σRl :=
    Or.inr (Or.inr (Or.inl ⟨rfl, hWill, hInv, rfl⟩))
  have htAB : tA = tB := by
    simpa [epochCounterInv] using hInv
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  all_goals
    try cases uSendA
    try cases uRecvA
    try cases uSendB
    try cases uRecvB
    try cases uChallA
    try cases uChallB
    try cases uCorrA
    try cases uCorrB
    try cases uRLeakA
    try cases uRLeakB
  · -- adversary randomness
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σRl) _
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OUnif n : (securitySpec leak).Domain)).run σ =
        (QueryImpl.ofLift unifSpec ProbComp n >>= fun y => pure (y, σ)) := by
      intro σ
      change (CKAScheme.oracleUnif (State PK SK) K (Message C PK) n).run σ = _
      simp [CKAScheme.oracleUnif, StateT.run_monadLift, monadLift_self]
    rw [hrun σHl, hrun σRl]
    refine relTriple_bind (relTriple_refl _) ?_
    intro y y' hy
    cases hy
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-A: not A's turn
    change RelTriple
      ((oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σHl)
      ((oracleSendAWithChallengePk kem gp pkStar ()).run σRl) _
    have hH : (oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σHl =
        pure (none, σHl) := by
      simp [oracleSendAWithChallengeKeyPair, CKAScheme.validStep, hσHl]
    have hR : (oracleSendAWithChallengePk kem gp pkStar ()).run σRl =
        pure (none, σRl) := by
      simp [oracleSendAWithChallengePk, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Recv-A: not a receive slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σRl) _
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σHl =
        pure ((), σHl) := by
      change (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleRecvA, CKAScheme.validStep, hσHl]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvA : (securitySpec leak).Domain)).run σRl =
        pure ((), σRl) := by
      change (CKAScheme.oracleRecvA (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleRecvA, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-B: the adversary skips the challenge; both counters pass the epoch
    change RelTriple
      ((oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σHl)
      ((oracleSendBWithChallengePk kem gp pkStar ()).run σRl) _
    have hgH : sendBInjectsChallengeKey gp { σHl with tB := σHl.tB + 1 } = false := by
      simp [sendBInjectsChallengeKey, hparty]
    have hgR : sendBInjectsChallengeKey gp { σRl with tB := σRl.tB + 1 } = false := by
      simp [sendBInjectsChallengeKey, hparty]
    rw [oracleSendBWithChallengeKeyPair_run_sendReady kem gp pkStar skStar σHl pkStar
        rfl rfl,
      oracleSendBWithChallengePk_run_sendReady kem gp pkStar σRl pkStar rfl rfl]
    simp only [hgH, hgR, Bool.false_eq_true, ↓reduceIte]
    refine relTriple_bind (relTriple_refl_support (kem.encaps pkStar)) ?_
    rintro ck ck' ⟨rfl, hck⟩
    obtain ⟨c, key⟩ := ck
    refine relTriple_bind (relTriple_refl_support kem.keygen) ?_
    rintro ks ks' ⟨rfl, hks'⟩
    obtain ⟨pkG, skG⟩ := ks
    refine relTriple_pure_pure ⟨rfl, Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))⟩ <;>
      · simp only [challengePassed, hparty, hσHl, hσRl]
        omega
  · -- O-Recv-B: not a receive slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σRl) _
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σHl =
        pure ((), σHl) := by
      change (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleRecvB, CKAScheme.validStep, hσHl]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.ORecvB : (securitySpec leak).Domain)).run σRl =
        pure ((), σRl) := by
      change (CKAScheme.oracleRecvB (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleRecvB, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Chall-A: wrong party
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σRl) _
    have hWAH : willChallengeA gp σHl = false := by
      simp [willChallengeA, hparty]
    have hWAR : willChallengeA gp σRl = false := by
      simp [willChallengeA, hparty]
    rw [securityImpl_challA_run_of_not_will kem hDet leak gp false σHl hWAH,
      securityImpl_challA_run_of_not_will kem hDet leak gp false σRl hWAR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Chall-B: the challenge fires at the implementation level on both sides
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σRl) _
    have hrun : ∀ st : State PK SK,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
          ⟨st, State.sendReady pkStar, ρA, ρB, kA, kB, corr,
            some CKAScheme.CKAAction.recvB, tA, tB⟩ =
        (do
          let (c, key) ← kem.encaps pkStar
          let (pkG, skG) ← kem.keygen
          pure (some ((c, pkG), key),
            (⟨st, State.recvReady skG, ρA, some (c, pkG), kA, some key, corr,
              some CKAScheme.CKAAction.challB, tA, tB + 1⟩ :
              SecurityState K PK SK C))) := by
      intro st
      change (CKAScheme.oracleChallB gp false (scheme kem hDet leak) ()).run _ = _
      simp [CKAScheme.oracleChallB, hvalidChall, CKAScheme.isChallengeEpoch,
        CKAScheme.GameState.tP, hparty, htBe, scheme, send]
      rfl
    rw [show σHl = ⟨State.recvReady skStar, State.sendReady pkStar, ρA, ρB, kA, kB,
        corr, some CKAScheme.CKAAction.recvB, tA, tB⟩ from rfl,
      show σRl = ⟨sA, State.sendReady pkStar, ρA, ρB, kA, kB, corr,
        some CKAScheme.CKAAction.recvB, tA, tB⟩ from rfl,
      hrun (State.recvReady skStar), hrun sA]
    refine relTriple_bind (relTriple_refl_support (kem.encaps pkStar)) ?_
    rintro ck ck' ⟨rfl, hck⟩
    obtain ⟨c, key⟩ := ck
    refine relTriple_bind (relTriple_refl_support kem.keygen) ?_
    rintro ks ks' ⟨rfl, hks'⟩
    obtain ⟨pkG, skG⟩ := ks
    refine relTriple_pure_pure ⟨rfl, Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))⟩ <;>
      · simp only [challengePassed, hparty]
        omega
  · -- O-Corrupt-A: gated off one epoch before the challenge
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σRl) _
    have htApred : tA = gp.challengeEpoch - 1 := by omega
    have hpcs : CKAScheme.allowCorrPCS gp σRl = false :=
      allowCorrPCS_false_of_two_le_deltaPCS_of_tA_pred gp σRl hΔ htApred
    have hcA : CKAScheme.allowCorr gp σRl .A = false := by
      simp [CKAScheme.allowCorr, hpcs, CKAScheme.allowCorrFS, hFS,
        (show σRl.tA = tA from rfl)]
      omega
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OCorruptA : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .A then some σ.stA else none, σ) := by
      intro σ
      change (CKAScheme.oracleCorruptA gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .A <;> simp [CKAScheme.oracleCorruptA, h]
    rw [hrun σHl, hrun σRl,
      show CKAScheme.allowCorr gp σHl .A = CKAScheme.allowCorr gp σRl .A from rfl,
      hcA]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Corrupt-B: B's state is shared; the outputs agree
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σRl) _
    have hrun : ∀ σ : SecurityState K PK SK C,
        (securityImpl kem hDet leak gp false
          (CKAScheme.ckaSecuritySpec.OCorruptB : (securitySpec leak).Domain)).run σ =
        pure (if CKAScheme.allowCorr gp σ .B then some σ.stB else none, σ) := by
      intro σ
      change (CKAScheme.oracleCorruptB gp (State PK SK) K (Message C PK) ()).run σ = _
      cases h : CKAScheme.allowCorr gp σ .B <;> simp [CKAScheme.oracleCorruptB, h]
    rw [hrun σHl, hrun σRl,
      show (if CKAScheme.allowCorr gp σHl .B then some σHl.stB else none) =
        (if CKAScheme.allowCorr gp σRl .B then some σRl.stB else none) from rfl]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-A-rleak: not a send slot
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run σRl)
      _
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run
        σHl = pure (none, σHl) := by
      change (CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleSendA_rleak, CKAScheme.validStep, hσHl]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendA_rleak : (securitySpec leak).Domain)).run
        σRl = pure (none, σRl) := by
      change (CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleSendA_rleak, CKAScheme.validStep, hσRl]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩
  · -- O-Send-B-rleak: the PCS gate fails at the challenge epoch
    change RelTriple
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run σHl)
      ((securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run σRl)
      _
    have hpcs : ¬ (max tA (tB + 1) + gp.ΔPCS ≤ gp.challengeEpoch) := by omega
    have hH : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run
        σHl = pure (none, σHl) := by
      change (CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σHl = _
      simp [CKAScheme.oracleSendB_rleak, CKAScheme.validStep, CKAScheme.allowCorrPCS,
        hσHl, hpcs]
    have hR : (securityImpl kem hDet leak gp false
        (CKAScheme.ckaSecuritySpec.OSendB_rleak : (securitySpec leak).Domain)).run
        σRl = pure (none, σRl) := by
      change (CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ()).run σRl = _
      simp [CKAScheme.oracleSendB_rleak, CKAScheme.validStep, CKAScheme.allowCorrPCS,
        hσRl, hpcs]
    rw [hH, hR]
    exact relTriple_pure_pure ⟨rfl, hrelSame⟩

/-- The injected prefix at bit `false` couples with the reduction prefix, for a
challenged party B.

One induction over the adversary: the phase analysis of each oracle step is in
the three step lemmas; here the splitters are unfolded, the challenge guards
are evaluated, and the paused and finished runs are collected. -/
lemma injectedPrefix_couples_challengePrefix_B
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.B)
    (hΔ : 2 ≤ gp.ΔPCS)
    (heven : gp.challengeEpoch % 2 = 0)
    (hFS : gp.ΔFS = 0)
    (pkStar : PK) (skStar : SK)
    {α : Type}
    (adv : OracleComp (securitySpec leak) α)
    (σH σR : SecurityState K PK SK C) :
    coupleRelB kem hDet gp pkStar skStar σH σR →
    RelTriple
      ((injectedChallengePrefix kem hDet leak gp false pkStar skStar adv).run σH)
      ((challengePrefix kem hDet leak gp pkStar adv).run σR)
      (couplePostB leak gp pkStar skStar) := by
  induction adv using OracleComp.inductionOn generalizing σH σR with
  | pure a =>
      intro _
      simp only [injectedChallengePrefix, challengePrefix, construct_pure,
        StateT.run_pure]
      exact relTriple_pure_pure (Or.inl ⟨⟨a, rfl⟩, ⟨a, rfl⟩⟩)
  | query_bind t cont ih =>
      intro hrel
      have hcont : ∀ p q : (securitySpec leak).Range t × SecurityState K PK SK C,
          p.1 = q.1 ∧ coupleRelB kem hDet gp pkStar skStar p.2 q.2 →
          RelTriple
            ((injectedChallengePrefix kem hDet leak gp false pkStar skStar
              (cont p.1)).run p.2)
            ((challengePrefix kem hDet leak gp pkStar (cont q.1)).run q.2)
            (couplePostB leak gp pkStar skStar) := by
        rintro ⟨u, σH'⟩ ⟨v, σR'⟩ ⟨huv, hrel'⟩
        obtain rfl : u = v := huv
        exact ih u σH' σR' hrel'
      rcases hrel with ⟨rfl, hpre⟩ | hInj | hChall | hDead
      · -- the equal-states case: the challenge guards are false; every arm steps
        have hWB : willChallengeB gp σH = false :=
          willChallengeB_eq_false_of_preInvB kem gp σH hpre
        have hWA : willChallengeA gp σH = false := by
          simp [willChallengeA, hparty]
        rcases t with
          (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
            uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
        all_goals
          try cases uSendA
          try cases uRecvA
          try cases uSendB
          try cases uRecvB
          try cases uChallA
          try cases uChallB
          try cases uCorrA
          try cases uCorrB
          try cases uRLeakA
          try cases uRLeakB
        all_goals
          simp only [injectedChallengePrefix, challengePrefix, construct_query_bind,
            stateT_run, hWA, hWB, Bool.false_eq_true,
            ↓reduceIte]
        all_goals
          exact relTriple_bind
            (coupleRelB_step_pre kem hDet hkem leak gp hparty hΔ heven pkStar skStar _
              σH hpre) hcont
      · -- the injected case: normalize the two states to literals, then step
        obtain ⟨skB, cInj, kInj, skR, hstB, hstA, hrhoA, hkeyA, hdec, hlast, htA, htB,
          hσH⟩ := hInj
        rcases σR with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
        obtain rfl : sB = State.recvReady skB := hstB
        obtain rfl : sA = State.recvReady skR := hstA
        obtain rfl : ρA = some (cInj, pkStar) := hrhoA
        obtain rfl : kA = some kInj := hkeyA
        obtain rfl : last = some CKAScheme.CKAAction.sendA := hlast
        subst hσH
        have htA' : tA + 1 = gp.challengeEpoch := htA
        have htB' : tB + 2 = gp.challengeEpoch := htB
        rw [show ({ (⟨State.recvReady skR, State.recvReady skB,
              some (cInj, pkStar), ρB, some kInj, kB, corr,
              some CKAScheme.CKAAction.sendA, tA, tB⟩ :
              SecurityState K PK SK C) with stA := State.recvReady skStar } :
            SecurityState K PK SK C) =
            ⟨State.recvReady skStar, State.recvReady skB, some (cInj, pkStar), ρB,
              some kInj, kB, corr, some CKAScheme.CKAAction.sendA, tA, tB⟩ from rfl]
        have hWA' : ∀ st : State PK SK, willChallengeA gp
            (⟨st, State.recvReady skB, some (cInj, pkStar), ρB, some kInj, kB, corr,
              some CKAScheme.CKAAction.sendA, tA, tB⟩ :
              SecurityState K PK SK C) = false := fun st => by
          simp [willChallengeA, hparty]
        have hWB' : ∀ st : State PK SK, willChallengeB gp
            (⟨st, State.recvReady skB, some (cInj, pkStar), ρB, some kInj, kB, corr,
              some CKAScheme.CKAAction.sendA, tA, tB⟩ :
              SecurityState K PK SK C) = false := fun st => by
          simp [willChallengeB, CKAScheme.validStep]
        rcases t with
          (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
            uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
        all_goals
          try cases uSendA
          try cases uRecvA
          try cases uSendB
          try cases uRecvB
          try cases uChallA
          try cases uChallB
          try cases uCorrA
          try cases uCorrB
          try cases uRLeakA
          try cases uRLeakB
        all_goals
          simp only [injectedChallengePrefix, challengePrefix, construct_query_bind,
            stateT_run, hWA', hWB', Bool.false_eq_true,
            ↓reduceIte]
        all_goals
          exact relTriple_bind
            (coupleRelB_step_inj kem hDet leak gp hparty hΔ hFS pkStar skStar skB cInj
              kInj skR ρB kB corr tA tB hdec htA' htB' _) hcont
      · -- the pre-challenge case: the challenge query pauses; every other arm steps
        obtain ⟨hstB, hWill, hInv, hσH⟩ := hChall
        rcases σR with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
        obtain rfl : sB = State.sendReady pkStar := hstB
        subst hσH
        rw [show ({ (⟨sA, State.sendReady pkStar, ρA, ρB, kA, kB, corr, last, tA, tB⟩ :
              SecurityState K PK SK C) with stA := State.recvReady skStar } :
            SecurityState K PK SK C) =
            ⟨State.recvReady skStar, State.sendReady pkStar, ρA, ρB, kA, kB, corr,
              last, tA, tB⟩ from rfl]
        have hWill' : ∀ st : State PK SK, willChallengeB gp
            (⟨st, State.sendReady pkStar, ρA, ρB, kA, kB, corr, last, tA, tB⟩ :
              SecurityState K PK SK C) = true := fun st => hWill
        have hWA' : ∀ st : State PK SK, willChallengeA gp
            (⟨st, State.sendReady pkStar, ρA, ρB, kA, kB, corr, last, tA, tB⟩ :
              SecurityState K PK SK C) = false := fun st => by
          simp [willChallengeA, hparty]
        rcases t with
          (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
            uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
        all_goals
          try cases uSendA
          try cases uRecvA
          try cases uSendB
          try cases uRecvB
          try cases uChallA
          try cases uChallB
          try cases uCorrA
          try cases uCorrB
          try cases uRLeakA
          try cases uRLeakB
        all_goals
          simp only [injectedChallengePrefix, challengePrefix, construct_query_bind,
            stateT_run, hWill', hWA',
            Bool.false_eq_true, ↓reduceIte]
        all_goals
          first
            | exact relTriple_bind
                (coupleRelB_step_chall kem hDet leak gp hparty hΔ hFS pkStar skStar sA
                  ρA ρB kA kB corr last tA tB hWill hInv _) hcont
            | exact relTriple_pure_pure (Or.inr ⟨cont,
                ⟨sA, State.sendReady pkStar, ρA, ρB, kA, kB, corr, last, tA, tB⟩,
                rfl, rfl, hInv, hWill⟩)
      · -- the passed-challenge case: neither prefix can pause
        refine relTriple_post_mono
          (relTriple_prod
            (P := fun z => ∃ a, z.1 = CKAChallengeStepResult.done a)
            (Q := fun z' => ∃ a', z'.1 = CKAChallengeStepResult.done a')
            (fun z hz =>
              injectedChallengePrefix_run_done_of_challengePassed kem hDet leak gp
                false pkStar skStar _ σH z hDead.1 hz)
            (fun z' hz' =>
              challengePrefix_run_done_of_challengePassed kem hDet leak gp pkStar
                _ σR z' hDead.2 hz')) ?_
        intro z z' hzz
        exact Or.inl hzz

end kemCKA
