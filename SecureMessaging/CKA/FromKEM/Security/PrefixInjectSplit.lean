/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.PrefixInjectSim

/-!
# CKA from KEM — Prefix Injection Splitter

The honest fixed-bit branch `ckaSecurityFixedBranchWithChallengeKey` samples the
challenge KEM key pair up front and never uses it (in the general, non-initial
case), while `ckaSecurityFixedBranchWithInjectedChallengeKey` installs that pair
at the predecessor send.  This file shows the two branches induce the same
Boolean output distribution.

The argument splits each run at the first send that installs the challenge key
pair.  Before that send the injecting and honest implementations agree, so the
prefix is shared; at the send the up-front key draw is coupled with the send's
fresh key draw; after the send `injectionPassed` holds, so the post-injection
equivalence (`probOutput_simulateQ_securityImplWithChallengeKeyPair_run_eq_of_injectionPassed`)
finishes the suffix.
-/

open OracleSpec OracleComp ENNReal KEMScheme
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-! ## The injecting send -/

/-- The next A-send installs the challenge key pair: it is a valid send from a
send-ready state at the epoch preceding a B-challenge.  This is exactly the
configuration in which `oracleSendAWithChallengeKeyPair` differs from the honest
A-send. -/
private def sendAEffectivelyInjects
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  CKAScheme.validStep σ.lastAction .sendA &&
    (match σ.stA with | .sendReady _ => true | _ => false) &&
    sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 }

/-- The next B-send installs the challenge key pair, the mirror of
`sendAEffectivelyInjects` for the send preceding an A-challenge. -/
private def sendBEffectivelyInjects
    (gp : CKAScheme.GameParams)
    (σ : SecurityState K PK SK C) : Bool :=
  CKAScheme.validStep σ.lastAction .sendB &&
    (match σ.stB with | .sendReady _ => true | _ => false) &&
    sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 }

/-! ## The prefix simulation -/

/-- Simulate the honest fixed-bit game up to the first send that would install
the challenge key pair, recording the adversary's remaining continuation.

The result is `.pausedA`/`.pausedB`, carrying the continuation interrupted at
that send, or `.done` when the adversary halts before any such send.  Up to that
send the injecting and honest implementations coincide, so this prefix runs the
honest implementation `securityImpl` and is common to both branches. -/
private def injectPrefix [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    {α : Type} :
    OracleComp (securitySpec leak) α →
      StateT (SecurityState K PK SK C) ProbComp
        (CKAChallengeStepResult leak α) :=
  OracleComp.construct
    (fun a => pure (.done a))
    (fun t oa rec => do
      match t with
      | CKAScheme.ckaSecuritySpec.OSendA =>
          let σ ← get
          if sendAEffectivelyInjects gp σ then
            pure (.pausedA oa)
          else
            let out ← securityImpl kem hDet leak gp isRandom
              (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)
            rec out
      | CKAScheme.ckaSecuritySpec.OSendB =>
          let σ ← get
          if sendBEffectivelyInjects gp σ then
            pure (.pausedB oa)
          else
            let out ← securityImpl kem hDet leak gp isRandom
              (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)
            rec out
      | other =>
          let out ← securityImpl kem hDet leak gp isRandom other
          rec out)

/-- The injecting and honest implementations agree on every oracle that is not
the installing send.

Only the send oracles can differ, and only when they install the challenge key
pair; the `sendAEffectivelyInjects`/`sendBEffectivelyInjects` guards exclude that
case here, and every other oracle coincides definitionally. -/
private lemma securityImplWithChallengeKeyPair_run_eq_securityImpl_of_step
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pkStar : PK) (skStar : SK)
    (t : (securitySpec leak).Domain)
    (σ : SecurityState K PK SK C)
    (hA : t = (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain) →
      sendAEffectivelyInjects gp σ = false)
    (hB : t = (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain) →
      sendBEffectivelyInjects gp σ = false) :
    (securityImplWithChallengeKeyPair kem hDet leak gp isRandom pkStar skStar t).run σ =
      (securityImpl kem hDet leak gp isRandom t).run σ := by
  rcases t with
    (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
      uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
  · rfl
  · -- O-Send-A
    cases uSendA
    change (oracleSendAWithChallengeKeyPair kem gp pkStar skStar ()).run σ = _
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendA = true
    · cases hst : σ.stA with
      | sendReady pk =>
          have hnotInj : sendAInjectsChallengeKey gp { σ with tA := σ.tA + 1 } = false := by
            simpa [sendAEffectivelyInjects, hvalid, hst] using hA rfl
          rw [oracleSendAWithChallengeKeyPair_run_sendReady kem gp pkStar skStar σ pk hvalid hst,
            securityImpl_OSendA_run_sendReady kem hDet leak gp isRandom σ pk hvalid hst]
          simp only [hnotInj]; rfl
      | recvReady sk =>
          change _ = (CKAScheme.oracleSendA (scheme kem hDet leak) ()).run σ
          simp only [oracleSendAWithChallengeKeyPair, CKAScheme.oracleSendA, scheme, send,
            hvalid, ↓reduceIte, hst, stateT_run]
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendA = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change _ = (CKAScheme.oracleSendA (scheme kem hDet leak) ()).run σ
      simp only [oracleSendAWithChallengeKeyPair, CKAScheme.oracleSendA, hvalidFalse,
        Bool.false_eq_true, ↓reduceIte, stateT_run]
  · rfl
  · -- O-Send-B
    cases uSendB
    change (oracleSendBWithChallengeKeyPair kem gp pkStar skStar ()).run σ = _
    by_cases hvalid : CKAScheme.validStep σ.lastAction .sendB = true
    · cases hst : σ.stB with
      | sendReady pk =>
          have hnotInj : sendBInjectsChallengeKey gp { σ with tB := σ.tB + 1 } = false := by
            simpa [sendBEffectivelyInjects, hvalid, hst] using hB rfl
          rw [oracleSendBWithChallengeKeyPair_run_sendReady kem gp pkStar skStar σ pk hvalid hst,
            securityImpl_OSendB_run_sendReady kem hDet leak gp isRandom σ pk hvalid hst]
          simp only [hnotInj]; rfl
      | recvReady sk =>
          change _ = (CKAScheme.oracleSendB (scheme kem hDet leak) ()).run σ
          simp only [oracleSendBWithChallengeKeyPair, CKAScheme.oracleSendB, scheme, send,
            hvalid, ↓reduceIte, hst, stateT_run]
    · have hvalidFalse : CKAScheme.validStep σ.lastAction .sendB = false :=
        Bool.eq_false_of_not_eq_true hvalid
      change _ = (CKAScheme.oracleSendB (scheme kem hDet leak) ()).run σ
      simp only [oracleSendBWithChallengeKeyPair, CKAScheme.oracleSendB, hvalidFalse,
        Bool.false_eq_true, ↓reduceIte, stateT_run]
  all_goals rfl

/-! ## Resuming after the pause -/

/-- Complete a split run from a recorded `CKAChallengeStepResult`.

For `.pausedA`/`.pausedB`, run the installing send under `impl` and simulate the
recorded continuation on the resulting state.  For `.done`, the run already
finished, so its result and final state are returned unchanged. -/
private def injectResume [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (leak : RandLeak kem)
    (impl : QueryImpl (securitySpec leak) (StateT (SecurityState K PK SK C) ProbComp))
    (res : CKAChallengeStepResult leak Bool)
    (σ : SecurityState K PK SK C) :
    ProbComp (Bool × SecurityState K PK SK C) :=
  match res with
  | .done g => pure (g, σ)
  | .pausedA cont =>
      (impl (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)).run σ >>=
        fun x => (simulateQ impl (cont x.1)).run x.2
  | .pausedB cont =>
      (impl (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)).run σ >>=
        fun x => (simulateQ impl (cont x.1)).run x.2

/-- Factor a simulated run through `injectPrefix`.

Any implementation that agrees with the honest one except at the installing send
splits into the shared prefix `injectPrefix` followed by `injectResume`, which
performs that send and finishes the run. -/
private lemma simulateQ_run_eq_injectPrefix_bind [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (impl : QueryImpl (securitySpec leak) (StateT (SecurityState K PK SK C) ProbComp))
    (hstep : ∀ (t : (securitySpec leak).Domain) (σ : SecurityState K PK SK C),
      (t = (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain) →
        sendAEffectivelyInjects gp σ = false) →
      (t = (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain) →
        sendBEffectivelyInjects gp σ = false) →
      (impl t).run σ = (securityImpl kem hDet leak gp isRandom t).run σ)
    (adv : OracleComp (securitySpec leak) Bool)
    (σ : SecurityState K PK SK C) :
    (simulateQ impl adv).run σ =
      (injectPrefix kem hDet leak gp isRandom adv).run σ >>=
        fun x => injectResume kem leak impl x.1 x.2 := by
  induction adv using OracleComp.inductionOn generalizing σ with
  | pure g =>
      simp [injectPrefix, injectResume, simulateQ_pure, StateT.run_pure]
  | query_bind t cont ih =>
      rcases t with
        (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
          uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
      all_goals
        try cases uSendA
        try cases uRecvA
        try cases uSendB
        try cases uRecvB
        try cases uCorrA
        try cases uCorrB
        try cases uRLeakA
        try cases uRLeakB
      all_goals
        try
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, bind_assoc, stateT_run, injectPrefix,
            construct_query_bind]
          rw [hstep _ _ (by simp) (by simp)]
          refine bind_congr (m := ProbComp) fun a => ?_
          simpa using ih a.1 a.2
      · -- O-Send-A
        by_cases heff : sendAEffectivelyInjects gp σ = true
        · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, stateT_run,
            injectPrefix, construct_query_bind, heff, ↓reduceIte, injectResume]
        · have heffFalse : sendAEffectivelyInjects gp σ = false :=
            Bool.eq_false_of_not_eq_true heff
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, bind_assoc,
            stateT_run, injectPrefix, construct_query_bind,
            heffFalse, Bool.false_eq_true, ↓reduceIte]
          rw [hstep _ _ (fun _ => heffFalse) (by simp)]
          refine bind_congr (m := ProbComp) fun a => ?_
          simpa using ih a.1 a.2
      · -- O-Send-B
        by_cases heff : sendBEffectivelyInjects gp σ = true
        · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map,
            stateT_run, injectPrefix, construct_query_bind,
            heff, ↓reduceIte, injectResume]
        · have heffFalse : sendBEffectivelyInjects gp σ = false :=
            Bool.eq_false_of_not_eq_true heff
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, bind_assoc,
            stateT_run, injectPrefix, construct_query_bind,
            heffFalse, Bool.false_eq_true, ↓reduceIte]
          rw [hstep _ _ (by simp) (fun _ => heffFalse)]
          refine bind_congr (m := ProbComp) fun a => ?_
          simpa using ih a.1 a.2

/-- A run that stops at an installing send stops in a state where that send is
indeed installing.

`injectPrefix` only emits `.pausedA`/`.pausedB` when the guard
`sendAEffectivelyInjects`/`sendBEffectivelyInjects` holds, so every paused state
in its support satisfies that guard. -/
private lemma injectPrefix_run_support_effInject [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (res : CKAChallengeStepResult leak Bool)
    (σ' : SecurityState K PK SK C)
    (adv : OracleComp (securitySpec leak) Bool)
    (σ : SecurityState K PK SK C) :
    (res, σ') ∈ support ((injectPrefix kem hDet leak gp isRandom adv).run σ) →
      (match res with
        | .done _ => True
        | .pausedA _ => sendAEffectivelyInjects gp σ' = true
        | .pausedB _ => sendBEffectivelyInjects gp σ' = true) := by
  induction adv using OracleComp.inductionOn generalizing σ with
  | pure g =>
      intro hmem
      simp only [injectPrefix, construct_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, -⟩ := hmem
      trivial
  | query_bind t cont ih =>
      rcases t with
        (((((((((n | uSendA) | uRecvA) | uSendB) | uRecvB) |
          uChallA) | uChallB) | uCorrA) | uCorrB) | uRLeakA) | uRLeakB
      all_goals
        try cases uSendA
        try cases uRecvA
        try cases uSendB
        try cases uRecvB
        try cases uCorrA
        try cases uCorrB
        try cases uRLeakA
        try cases uRLeakB
      all_goals
        try
          intro hmem
          simp only [injectPrefix, construct_query_bind, stateT_run, support_bind,
            Set.mem_iUnion₂] at hmem
          obtain ⟨p, -, hmem'⟩ := hmem
          exact ih p.1 p.2 hmem'
      · -- O-Send-A
        intro hmem
        by_cases heff : sendAEffectivelyInjects gp σ = true
        · simp only [injectPrefix, construct_query_bind, stateT_run, heff] at hmem
          obtain ⟨rfl, rfl⟩ := hmem
          exact heff
        · have heffFalse : sendAEffectivelyInjects gp σ = false :=
            Bool.eq_false_of_not_eq_true heff
          simp only [injectPrefix, construct_query_bind, stateT_run, heffFalse,
            Bool.false_eq_true, ↓reduceIte, support_bind, Set.mem_iUnion₂] at hmem
          obtain ⟨p, -, hmem'⟩ := hmem
          exact ih p.1 p.2 hmem'
      · -- O-Send-B
        intro hmem
        by_cases heff : sendBEffectivelyInjects gp σ = true
        · simp only [injectPrefix, construct_query_bind, stateT_run, heff] at hmem
          obtain ⟨rfl, rfl⟩ := hmem
          exact heff
        · have heffFalse : sendBEffectivelyInjects gp σ = false :=
            Bool.eq_false_of_not_eq_true heff
          simp only [injectPrefix, construct_query_bind, stateT_run, heffFalse,
            Bool.false_eq_true, ↓reduceIte, support_bind, Set.mem_iUnion₂] at hmem
          obtain ⟨p, -, hmem'⟩ := hmem
          exact ih p.1 p.2 hmem'

/-! ## Combining the split at the installing send -/

/-- Two state-output computations with the same output distribution have the same
distribution on their Boolean component. -/
private lemma probOutput_fst_true_eq_of_run_eq
    {X Y : ProbComp (Bool × SecurityState K PK SK C)}
    (h : ∀ z, Pr[= z | X] = Pr[= z | Y]) :
    Pr[= true | X >>= fun x => pure x.1] = Pr[= true | Y >>= fun x => pure x.1] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  exact tsum_congr fun z => by rw [h z]

/-- The keygen commute at an installing send, abstracted over the post-send state.

After the installing send is reduced to its normal form, the injecting branch
draws the challenge key pair up front and an unused fresh pair at the send, while
the honest branch draws only the pair it installs.  Commuting the up-front draw
past the encapsulation, dropping the unused draw, and finishing the suffix with
the post-injection equivalence (which applies because `injectionPassed` holds at
the post-send state) identifies the two.  The A- and B-side combines differ only
in how the post-send state `mkState` is built, so both reduce to this lemma. -/
private lemma keygen_commute_after_install_tail [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (pk : PK)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool)
    (mkState : PK → SK → C → K → SecurityState K PK SK C)
    (hpass : ∀ (p : PK × SK) (ck : C × K),
      injectionPassed gp (mkState p.1 p.2 ck.1 ck.2)) :
    Pr[= true | kem.keygen >>= fun p =>
        kem.encaps pk >>= fun ck =>
          kem.keygen >>= fun _unused =>
            (simulateQ (securityImplWithChallengeKeyPair kem hDet leak gp isRandom p.1 p.2)
                (cont (some ((ck.1, p.1), ck.2)))).run (mkState p.1 p.2 ck.1 ck.2) >>=
              fun x => pure x.1]
      = Pr[= true | kem.encaps pk >>= fun ck =>
          kem.keygen >>= fun p =>
            (simulateQ (securityImpl kem hDet leak gp isRandom)
                (cont (some ((ck.1, p.1), ck.2)))).run (mkState p.1 p.2 ck.1 ck.2) >>=
              fun x => pure x.1] := by
  rw [probOutput_bind_bind_swap (mx := kem.keygen) (my := kem.encaps pk)]
  refine probOutput_bind_congr fun ck _ => ?_
  refine probOutput_bind_congr fun p _ => ?_
  rw [probOutput_bind_const]
  simp only [HasEvalPMF.probFailure_eq_zero, tsub_zero, one_mul]
  exact probOutput_fst_true_eq_of_run_eq fun z =>
    probOutput_simulateQ_securityImplWithChallengeKeyPair_run_eq_of_injectionPassed
      kem hDet leak gp isRandom p.1 p.2 (cont (some ((ck.1, p.1), ck.2)))
      (mkState p.1 p.2 ck.1 ck.2) (hpass p ck) z

/-- The keygen commute at the installing A-send.

On the injected branch the up-front challenge key draw supplies the installed
pair while the send draws an unused fresh pair; on the honest branch the send
draws the pair it installs.  Dropping the unused draw, coupling the up-front draw
with the honest send's draw, and finishing the post-injection suffix with the
`injectionPassed` equivalence identifies the two. -/
private lemma injectResume_pausedA_combine [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool)
    (σ_p : SecurityState K PK SK C)
    (heff : sendAEffectivelyInjects gp σ_p = true) :
    Pr[= true | kem.keygen >>= fun p =>
        injectResume kem leak (securityImplWithChallengeKeyPair kem hDet leak gp isRandom p.1 p.2)
          (.pausedA cont) σ_p >>= fun x => pure x.1]
      = Pr[= true | injectResume kem leak (securityImpl kem hDet leak gp isRandom)
          (.pausedA cont) σ_p >>= fun x => pure x.1] := by
  simp only [sendAEffectivelyInjects, Bool.and_eq_true] at heff
  obtain ⟨⟨hvalid, hsr⟩, hinj⟩ := heff
  cases hst : σ_p.stA with
  | recvReady sk => rw [hst] at hsr; exact absurd hsr (by simp)
  | sendReady pk =>
    -- the A-side post-send state, installing the challenge pair at this send
    let mkState : PK → SK → C → K → SecurityState K PK SK C :=
      fun pkNext skNext c key =>
        { σ_p with
            tA := σ_p.tA + 1,
            stA := State.recvReady skNext,
            rhoA := some (c, pkNext),
            keyA := some key,
            lastAction := some .sendA }
    -- the post-send state (counter `σ_p.tA + 1`) has `injectionPassed`
    have hpass : ∀ s : SecurityState K PK SK C, s.tA = σ_p.tA + 1 → injectionPassed gp s := by
      intro s hs
      simp only [sendAInjectsChallengeKey, Bool.and_eq_true, beq_iff_eq] at hinj
      obtain ⟨hcp, hta⟩ := hinj
      simp only [injectionPassed, hcp]
      omega
    -- the injecting A-send under the up-front draw, reduced for every `p`
    have hWCKSend : ∀ p : PK × SK,
        (securityImplWithChallengeKeyPair kem hDet leak gp isRandom p.1 p.2
            (CKAScheme.ckaSecuritySpec.OSendA : (securitySpec leak).Domain)).run σ_p =
          (do
            let (c, key) ← kem.encaps pk
            let (_pkGen, _skGen) ← kem.keygen
            pure (some ((c, p.1), key),
              ({ σ_p with
                  tA := σ_p.tA + 1,
                  stA := State.recvReady p.2,
                  rhoA := some (c, p.1),
                  keyA := some key,
                  lastAction := some .sendA } : SecurityState K PK SK C))) := by
      intro p
      change (oracleSendAWithChallengeKeyPair kem gp p.1 p.2 ()).run σ_p = _
      simp only [oracleSendAWithChallengeKeyPair_run_sendReady kem gp p.1 p.2 σ_p pk hvalid hst,
        hinj, ↓reduceIte]
      simp_all only [bind_pure_comp]
      obtain ⟨fst, snd⟩ := p
      simp_all only
      rfl
    -- after reducing the A-send to normal form, close with the shared tail
    simp only [injectResume, hWCKSend,
      securityImpl_OSendA_run_sendReady kem hDet leak gp isRandom σ_p pk hvalid hst, bind_assoc]
    exact keygen_commute_after_install_tail kem hDet leak gp isRandom pk cont mkState
      (fun p ck => hpass _ rfl)

/-- The keygen commute at the installing B-send, the mirror of
`injectResume_pausedA_combine`. -/
private lemma injectResume_pausedB_combine [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool)
    (σ_p : SecurityState K PK SK C)
    (heff : sendBEffectivelyInjects gp σ_p = true) :
    Pr[= true | kem.keygen >>= fun p =>
        injectResume kem leak (securityImplWithChallengeKeyPair kem hDet leak gp isRandom p.1 p.2)
          (.pausedB cont) σ_p >>= fun x => pure x.1]
      = Pr[= true | injectResume kem leak (securityImpl kem hDet leak gp isRandom)
          (.pausedB cont) σ_p >>= fun x => pure x.1] := by
  simp only [sendBEffectivelyInjects, Bool.and_eq_true] at heff
  obtain ⟨⟨hvalid, hsr⟩, hinj⟩ := heff
  cases hst : σ_p.stB with
  | recvReady sk => rw [hst] at hsr; exact absurd hsr (by simp)
  | sendReady pk =>
    -- the B-side post-send state, installing the challenge pair at this send
    let mkState : PK → SK → C → K → SecurityState K PK SK C :=
      fun pkNext skNext c key =>
        { σ_p with
            tB := σ_p.tB + 1,
            stB := State.recvReady skNext,
            rhoB := some (c, pkNext),
            keyB := some key,
            lastAction := some .sendB }
    -- the post-send state (counter `σ_p.tB + 1`) has `injectionPassed`
    have hpass : ∀ s : SecurityState K PK SK C, s.tB = σ_p.tB + 1 → injectionPassed gp s := by
      intro s hs
      simp only [sendBInjectsChallengeKey, Bool.and_eq_true, beq_iff_eq] at hinj
      obtain ⟨hcp, hta⟩ := hinj
      simp only [injectionPassed, hcp]
      omega
    -- the injecting B-send under the up-front draw, reduced for every `p`
    have hWCKSend : ∀ p : PK × SK,
        (securityImplWithChallengeKeyPair kem hDet leak gp isRandom p.1 p.2
            (CKAScheme.ckaSecuritySpec.OSendB : (securitySpec leak).Domain)).run σ_p =
          (do
            let (c, key) ← kem.encaps pk
            let (_pkGen, _skGen) ← kem.keygen
            pure (some ((c, p.1), key),
              ({ σ_p with
                  tB := σ_p.tB + 1,
                  stB := State.recvReady p.2,
                  rhoB := some (c, p.1),
                  keyB := some key,
                  lastAction := some .sendB } : SecurityState K PK SK C))) := by
      intro p
      change (oracleSendBWithChallengeKeyPair kem gp p.1 p.2 ()).run σ_p = _
      simp only [oracleSendBWithChallengeKeyPair_run_sendReady kem gp p.1 p.2 σ_p pk hvalid hst,
        hinj, ↓reduceIte]
      simp_all only [bind_pure_comp]
      obtain ⟨fst, snd⟩ := p
      simp_all only
      rfl
    -- after reducing the B-send to normal form, close with the shared tail
    simp only [injectResume, hWCKSend,
      securityImpl_OSendB_run_sendReady kem hDet leak gp isRandom σ_p pk hvalid hst, bind_assoc]
    exact keygen_commute_after_install_tail kem hDet leak gp isRandom pk cont mkState
      (fun p ck => hpass _ rfl)

/-! ## Moving the challenge key draw across the simulation -/

/-- From any starting state, drawing the challenge key pair up front and running
the injecting implementation gives the same Boolean output as running the honest
implementation.

Both runs split through `injectPrefix`; the shared prefix commutes past the
up-front draw, and at the installing send the draw couples with the send. -/
private lemma probOutput_simulateQ_keygen_commute [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool)
    (adv : Adversary (kem := kem) leak)
    (σ0 : SecurityState K PK SK C) :
    Pr[= true | kem.keygen >>= fun p =>
        (simulateQ
        (securityImplWithChallengeKeyPair kem hDet leak gp isRandom p.1 p.2) adv).run σ0 >>=
          fun x => pure x.1]
      = Pr[= true | (simulateQ (securityImpl kem hDet leak gp isRandom) adv).run σ0 >>=
          fun x => pure x.1] := by
  have hsplitWCK : ∀ p : PK × SK,
      (simulateQ (securityImplWithChallengeKeyPair kem hDet leak gp isRandom p.1 p.2) adv).run σ0 =
        (injectPrefix kem hDet leak gp isRandom adv).run σ0 >>= fun x =>
          injectResume kem leak (securityImplWithChallengeKeyPair kem hDet leak gp isRandom p.1 p.2)
            x.1 x.2 :=
    fun p => simulateQ_run_eq_injectPrefix_bind kem hDet leak gp isRandom _
      (securityImplWithChallengeKeyPair_run_eq_securityImpl_of_step
        kem hDet leak gp isRandom p.1 p.2)
      adv σ0
  have hsplitH :
      (simulateQ (securityImpl kem hDet leak gp isRandom) adv).run σ0 =
        (injectPrefix kem hDet leak gp isRandom adv).run σ0 >>= fun x =>
          injectResume kem leak (securityImpl kem hDet leak gp isRandom) x.1 x.2 :=
    simulateQ_run_eq_injectPrefix_bind kem hDet leak gp isRandom _ (fun _ _ _ _ => rfl) adv σ0
  simp only [hsplitWCK, hsplitH, bind_assoc]
  rw [probOutput_bind_bind_swap (mx := kem.keygen)
    (my := (injectPrefix kem hDet leak gp isRandom adv).run σ0)]
  refine probOutput_bind_congr fun rs hrs => ?_
  obtain ⟨res, σ_p⟩ := rs
  cases res with
  | done g =>
      simp only [injectResume, pure_bind, probOutput_bind_const,
        HasEvalPMF.probFailure_eq_zero, tsub_zero, one_mul]
  | pausedA cont =>
      exact injectResume_pausedA_combine kem hDet leak gp isRandom cont σ_p
        (injectPrefix_run_support_effInject kem hDet leak gp isRandom
          (.pausedA cont) σ_p adv σ0 hrs)
  | pausedB cont =>
      exact injectResume_pausedB_combine kem hDet leak gp isRandom cont σ_p
        (injectPrefix_run_support_effInject kem hDet leak gp isRandom
          (.pausedB cont) σ_p adv σ0 hrs)

/-- Running `securityImpl` from a state with the challenge key installed agrees
with injecting that key pair through `securityImplWithChallengeKeyPair`, per bit.

When the challenge is the very first A-send the key pair is already in the
initial state, so `injectionPassed` holds at the start and the post-injection
equivalence closes it directly.  Otherwise the installing send happens later, the
challenge key draw is unused up front, and the keygen-commute identity moves it
into place. -/
private lemma ckaSecurityFixedBranchWithChallengeKey_injected_probOutput_true_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (isRandom : Bool) :
    Pr[= true |
        ckaSecurityFixedBranchWithChallengeKey kem hDet leak adv gp isRandom] =
      Pr[= true |
        ckaSecurityFixedBranchWithInjectedChallengeKey
          kem hDet leak adv gp isRandom] := by
  unfold ckaSecurityFixedBranchWithChallengeKey
    ckaSecurityFixedBranchWithInjectedChallengeKey ckaSecurityFixedFromState
  by_cases hinit :
      (gp.challengeEpoch == 1 && gp.challengedParty == .A) = true
  · simp only [hinit, ↓reduceIte]
    refine probOutput_bind_congr' kem.keygen true fun pk0sk0 => ?_
    refine probOutput_bind_congr' kem.keygen true fun pkStar_skStar => ?_
    have hpass : injectionPassed gp
        (CKAScheme.initGameState
          (State.sendReady pkStar_skStar.1)
          (State.recvReady pkStar_skStar.2) :
          SecurityState K PK SK C) := by
      obtain ⟨hce, hcp⟩ := (Bool.and_eq_true _ _).mp hinit
      rw [beq_iff_eq] at hce hcp
      simp only [injectionPassed, hcp, CKAScheme.initGameState]
      omega
    exact (probOutput_fst_true_eq_of_run_eq fun z =>
      probOutput_simulateQ_securityImplWithChallengeKeyPair_run_eq_of_injectionPassed
        kem hDet leak gp isRandom pkStar_skStar.1 pkStar_skStar.2 adv _ hpass z).symm
  · have hinitFalse :
        (gp.challengeEpoch == 1 && gp.challengedParty == .A) = false :=
      Bool.eq_false_of_not_eq_true hinit
    simp only [hinitFalse, Bool.false_eq_true, ↓reduceIte]
    refine probOutput_bind_congr' kem.keygen true fun pk0sk0 => ?_
    rw [probOutput_bind_const]
    simp only [HasEvalPMF.probFailure_eq_zero, tsub_zero, one_mul]
    exact (probOutput_simulateQ_keygen_commute
      kem hDet leak gp isRandom adv
      (CKAScheme.initGameState
        (State.sendReady pk0sk0.1)
        (State.recvReady pk0sk0.2))).symm

/-- The challenge-key and injected-challenge-key fixed branches have the same
true-output gap across the two fixed bits. -/
lemma ckaSecurityFixedBranchWithChallengeKey_injected_gap_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams) :
    |(Pr[= true |
        ckaSecurityFixedBranchWithChallengeKey kem hDet leak adv gp true]).toReal -
      (Pr[= true |
        ckaSecurityFixedBranchWithChallengeKey kem hDet leak adv gp false]).toReal| =
    |(Pr[= true |
        ckaSecurityFixedBranchWithInjectedChallengeKey
          kem hDet leak adv gp true]).toReal -
      (Pr[= true |
        ckaSecurityFixedBranchWithInjectedChallengeKey
          kem hDet leak adv gp false]).toReal| := by
  rw [ckaSecurityFixedBranchWithChallengeKey_injected_probOutput_true_eq]
  rw [ckaSecurityFixedBranchWithChallengeKey_injected_probOutput_true_eq]

end kemCKA
