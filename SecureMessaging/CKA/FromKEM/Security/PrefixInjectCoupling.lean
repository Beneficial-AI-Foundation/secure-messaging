/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Security.PrefixInjectCouplingA
import SecureMessaging.CKA.FromKEM.Security.PrefixInjectCouplingB
import ToVCVio.EvalDist.Monad.Basic

/-!
# CKA from KEM — Injected-Prefix Coupling

`ckaSecurityFixedBranchWithInjectedChallengeKey` and
`ckaReductionINDCPABranchRawKeygenSwapped` behave the same up to the first
challenge query whose `willChallengeA`/`willChallengeB` guard holds.
Splitting both games at that query, the runs that never reach such a query are
bit-independent and cancel inside each game's own gap, while the paused runs
land in the challenge-bridge shapes.  The party-specific couplings live in
`PrefixInjectCouplingA` and `PrefixInjectCouplingB`; this file assembles them
into the gap equality `cka_injected_honest_gap_eq_keygen_swapped_raw_gap`,
the final hop in the top-level advantage chain.
-/

open OracleSpec OracleComp ENNReal KEMScheme
open OracleComp.ProgramLogic.Relational

namespace kemCKA

variable {K PK SK C : Type}

/-! ## Splitting a success probability over the first pause

Both split games are a prefix bound to a resume.  Replacing the resume's
finished-run guesses by `false` isolates the paused runs' contribution; the
finished runs' contribution is bit-free because the prefix runs at bit
`false`.  The success probability of the game is the sum of the two. -/

/-- As resuming with `injectedChallengeResume`, with finished runs' guesses
replaced by `false`: the paused runs' contribution to the success
probability. -/
private def injResumeKilled [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK) (skStar : SK)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    ProbComp Bool :=
  match z.1 with
  | .done _ => pure false
  | _ => Prod.fst <$>
      injectedChallengeResume kem hDet leak gp b pkStar skStar z.1 z.2

/-- The finished runs' guesses; paused runs contribute `false`. -/
private def injDone
    {kem : KEMScheme ProbComp K PK SK C}
    (leak : RandLeak kem)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    ProbComp Bool :=
  match z.1 with
  | .done g => pure g
  | _ => pure false

/-- The reduction game's continuation after its prefix: the challenge
ciphertext draw, the random key draw, and `finishChallengeStepRaw` at the
selected key. -/
private def rawResume [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    ProbComp Bool := do
  let ck ← kem.encaps pkStar
  let kRand ← ($ᵗ K : ProbComp K)
  finishChallengeStepRaw kem hDet leak gp z.1 z.2 ck.1 (if b then ck.2 else kRand)

/-- As `rawResume`, with finished runs' guesses replaced by `false`. -/
private def rawResumeKilled [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    ProbComp Bool :=
  match z.1 with
  | .done _ => pure false
  | _ => rawResume kem hDet leak gp b pkStar z

/-- Pointwise split of the injected game's resume into its paused and
finished contributions. -/
private lemma injResume_probOutput_decomp [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK) (skStar : SK)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    Pr[= true |
        Prod.fst <$> injectedChallengeResume kem hDet leak gp b pkStar skStar
          z.1 z.2] =
      Pr[= true | injResumeKilled kem hDet leak gp b pkStar skStar z] +
        Pr[= true | injDone leak z] := by
  rcases z with ⟨res, σ⟩
  cases res with
  | done g => simp [injectedChallengeResume, injResumeKilled, injDone]
  | pausedA cont => simp [injResumeKilled, injDone]
  | pausedB cont => simp [injResumeKilled, injDone]

/-- Pointwise split of the reduction game's resume into its paused and
finished contributions.  In the finished case the unused challenge and key
draws integrate out. -/
private lemma rawResume_probOutput_decomp [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK)
    (z : CKAChallengeStepResult leak Bool × SecurityState K PK SK C) :
    Pr[= true | rawResume kem hDet leak gp b pkStar z] =
      Pr[= true | rawResumeKilled kem hDet leak gp b pkStar z] +
        Pr[= true | injDone leak z] := by
  rcases z with ⟨res, σ⟩
  cases res with
  | done g =>
      simp only [rawResume, finishChallengeStepRaw, rawResumeKilled, injDone]
      rw [probOutput_bind_const]
      simp only [HasEvalPMF.probFailure_eq_zero, tsub_zero, one_mul]
      rw [probOutput_bind_const]
      simp [HasEvalPMF.probFailure_eq_zero]
  | pausedA cont => simp [rawResumeKilled, injDone]
  | pausedB cont => simp [rawResumeKilled, injDone]

/-! ## The four sub-games

Each split game decomposes into a paused part (the resume with finished
guesses replaced by `false`) and a finished part.  The finished parts read
nothing bit-dependent: the prefixes run at bit `false` and `injDone` ignores
the challenge bit, so the two finished sub-games are bit-free terms. -/

private def injectedKilledGame [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pkStar, skStar) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.recvReady skStar
      else
        State.recvReady sk0)
  let z ← (injectedChallengePrefix kem hDet leak gp false pkStar skStar adv).run σ0
  injResumeKilled kem hDet leak gp b pkStar skStar z

private def injectedDoneGame [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pkStar, skStar) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.recvReady skStar
      else
        State.recvReady sk0)
  let z ← (injectedChallengePrefix kem hDet leak gp false pkStar skStar adv).run σ0
  injDone leak z

private def reductionKilledGame [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pkStar, _skStar) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (State.recvReady sk0)
  let z ← (challengePrefix kem hDet leak gp pkStar adv).run σ0
  rawResumeKilled kem hDet leak gp b pkStar z

private def reductionDoneGame [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams) : ProbComp Bool := do
  let (pk0, sk0) ← kem.keygen
  let (pkStar, _skStar) ← kem.keygen
  let σ0 :=
    CKAScheme.initGameState
      (if gp.challengeEpoch == 1 && gp.challengedParty == .A then
        State.sendReady pkStar
      else
        State.sendReady pk0)
      (State.recvReady sk0)
  let z ← (challengePrefix kem hDet leak gp pkStar adv).run σ0
  injDone leak z

/-- The injected game's success probability splits over the first pause. -/
private lemma injected_probOutput_eq_killed_add_done
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) :
    Pr[= true | ckaSecurityFixedBranchWithInjectedChallengeKey kem hDet leak adv gp b] =
      Pr[= true | injectedKilledGame kem hDet leak adv gp b] +
        Pr[= true | injectedDoneGame kem hDet leak adv gp] := by
  rw [ckaSecurityFixedBranchWithInjectedChallengeKey_eq_split]
  simp only [injectedKilledGame, injectedDoneGame]
  refine probOutput_true_bind_add_of_pointwise kem.keygen _ _ _ fun ks0 => ?_
  obtain ⟨pk0, sk0⟩ := ks0
  refine probOutput_true_bind_add_of_pointwise kem.keygen _ _ _ fun ksS => ?_
  obtain ⟨pkStar, skStar⟩ := ksS
  refine probOutput_true_bind_add_of_pointwise _ _ _ _ fun z => ?_
  exact injResume_probOutput_decomp kem hDet leak gp b pkStar skStar z

/-- The reduction game's success probability splits over the first pause. -/
private lemma reduction_probOutput_eq_killed_add_done
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (b : Bool) :
    Pr[= true | ckaReductionINDCPABranchRawKeygenSwapped kem hDet leak adv gp b] =
      Pr[= true | reductionKilledGame kem hDet leak adv gp b] +
        Pr[= true | reductionDoneGame kem hDet leak adv gp] := by
  simp only [ckaReductionINDCPABranchRawKeygenSwapped, reductionKilledGame,
    reductionDoneGame]
  refine probOutput_true_bind_add_of_pointwise kem.keygen _ _ _ fun ks0 => ?_
  obtain ⟨pk0, sk0⟩ := ks0
  refine probOutput_true_bind_add_of_pointwise kem.keygen _ _ _ fun ksS => ?_
  obtain ⟨pkStar, skStar⟩ := ksS
  refine probOutput_true_bind_add_of_pointwise _ _ _ _ fun z => ?_
  exact rawResume_probOutput_decomp kem hDet leak gp b pkStar z

/-! ## Toward the paused-run chains

For Boolean computations without failure, equal success probabilities give the
equality-relation triple, which is the form the killed-game chain composes.
The two support lemmas pin the counters after a fired challenge query: the
challenged party's counter is bumped once, the other counter is unchanged.
The apexes' `injectionPassed`/`challengePassed` hypotheses follow from them at
the paused states. -/

private lemma relTriple_eqRel_of_probOutput_true_eq
    {mx my : ProbComp Bool}
    (h : Pr[= true | mx] = Pr[= true | my]) :
    RelTriple mx my (EqRel Bool) := by
  refine relTriple_eqRel_of_probOutput_eq fun x => ?_
  cases x
  · simp only [probOutput_false_eq_sub, HasEvalPMF.probFailure_eq_zero, h]
  · exact h

private lemma challA_run_support_counters [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hstA : σ.stA = State.sendReady pk)
    (hWill : willChallengeA gp σ = true)
    (z : Option (Message C PK × K) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp b
      (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run σ)) :
    z.2.tA = σ.tA + 1 ∧ z.2.tB = σ.tB := by
  have hWill' := hWill
  simp only [willChallengeA, Bool.and_eq_true, beq_iff_eq] at hWill'
  obtain ⟨⟨hvalid, hpartyEq⟩, htA⟩ := hWill'
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  obtain rfl : sA = State.sendReady pk := hstA
  have hrun : (securityImpl kem hDet leak gp b
      (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
      ⟨State.sendReady pk, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩ =
      (do
        let ck ← kem.encaps pk
        let ks ← kem.keygen
        let outKey ← if b then ($ᵗ K : ProbComp K) else pure ck.2
        pure (some ((ck.1, ks.1), outKey),
          (⟨State.recvReady ks.2, sB, some (ck.1, ks.1), ρB, some ck.2, kB, corr,
            some CKAScheme.CKAAction.challA, tA + 1, tB⟩ :
            SecurityState K PK SK C))) := by
    change (CKAScheme.oracleChallA gp b (scheme kem hDet leak) ()).run _ = _
    cases b <;>
      simp [CKAScheme.oracleChallA, hvalid, CKAScheme.isChallengeEpoch,
        CKAScheme.GameState.tP, hpartyEq, htA, scheme, send]
    all_goals rfl
  rw [hrun] at hz
  cases b
  all_goals (
    simp only [↓reduceIte] at hz
    vcv_support hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact ⟨rfl, rfl⟩)

private lemma challB_run_support_counters [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (σ : SecurityState K PK SK C) (pk : PK)
    (hstB : σ.stB = State.sendReady pk)
    (hWill : willChallengeB gp σ = true)
    (z : Option (Message C PK × K) × SecurityState K PK SK C)
    (hz : z ∈ support ((securityImpl kem hDet leak gp b
      (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run σ)) :
    z.2.tB = σ.tB + 1 ∧ z.2.tA = σ.tA := by
  have hWill' := hWill
  simp only [willChallengeB, Bool.and_eq_true, beq_iff_eq] at hWill'
  obtain ⟨⟨hvalid, hpartyEq⟩, htB⟩ := hWill'
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, corr, last, tA, tB⟩
  obtain rfl : sB = State.sendReady pk := hstB
  have hrun : (securityImpl kem hDet leak gp b
      (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
      ⟨sA, State.sendReady pk, ρA, ρB, kA, kB, corr, last, tA, tB⟩ =
      (do
        let ck ← kem.encaps pk
        let ks ← kem.keygen
        let outKey ← if b then ($ᵗ K : ProbComp K) else pure ck.2
        pure (some ((ck.1, ks.1), outKey),
          (⟨sA, State.recvReady ks.2, ρA, some (ck.1, ks.1), kA, some ck.2, corr,
            some CKAScheme.CKAAction.challB, tA, tB + 1⟩ :
            SecurityState K PK SK C))) := by
    change (CKAScheme.oracleChallB gp b (scheme kem hDet leak) ()).run _ = _
    cases b <;>
      simp [CKAScheme.oracleChallB, hvalid, CKAScheme.isChallengeEpoch,
        CKAScheme.GameState.tP, hpartyEq, htB, scheme, send]
    all_goals rfl
  rw [hrun] at hz
  cases b
  all_goals (
    simp only [↓reduceIte] at hz
    vcv_support hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact ⟨rfl, rfl⟩)

/-! ## Normalizing the reduction continuation after a fired challenge

Once `reductionBranchImpl` has consumed its challenge query the rest of the
run is `postChallengeImpl` under an unchanging `.post` wrapper.  Composed with
the challenge step itself this is the paused branch of
`finishChallengeStepRaw`, the program the killed reduction resume runs. -/

private lemma reductionBranch_challA_cont_eq_finishChallengeStepRaw
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeA gp σ = true)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool) :
    ((reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (ReductionBranchState.pre σ) >>= fun q =>
      (simulateQ (reductionBranchImpl kem hDet leak gp pkStar cStar kStar)
        (cont q.1)).run' q.2) =
      finishChallengeStepRaw kem hDet leak gp (.pausedA cont) σ cStar kStar := by
  rw [reductionBranchImpl_pre_challA_run_of_will kem hDet leak gp pkStar cStar kStar
    σ hWill]
  simp only [finishChallengeStepRaw, bind_assoc]
  refine bind_congr (m := ProbComp) fun ks => ?_
  obtain ⟨pkNext, skNext⟩ := ks
  simp only [pure_bind]
  rw [StateT.run'_eq, reductionBranchImpl_post_simulateQ_run]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr (m := ProbComp) fun p => ?_
  obtain ⟨guess, ps'⟩ := p
  simp

private lemma reductionBranch_challB_cont_eq_finishChallengeStepRaw
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (pkStar : PK) (cStar : C) (kStar : K)
    (σ : SecurityState K PK SK C)
    (hWill : willChallengeB gp σ = true)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool) :
    ((reductionBranchImpl kem hDet leak gp pkStar cStar kStar
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (ReductionBranchState.pre σ) >>= fun q =>
      (simulateQ (reductionBranchImpl kem hDet leak gp pkStar cStar kStar)
        (cont q.1)).run' q.2) =
      finishChallengeStepRaw kem hDet leak gp (.pausedB cont) σ cStar kStar := by
  rw [reductionBranchImpl_pre_challB_run_of_will kem hDet leak gp pkStar cStar kStar
    σ hWill]
  simp only [finishChallengeStepRaw, bind_assoc]
  refine bind_congr (m := ProbComp) fun ks => ?_
  obtain ⟨pkNext, skNext⟩ := ks
  simp only [pure_bind]
  rw [StateT.run'_eq, reductionBranchImpl_post_simulateQ_run]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr (m := ProbComp) fun p => ?_
  obtain ⟨guess, ps'⟩ := p
  simp

/-! ## The paused killed resumes

A paused injected resume is the challenge step at the resume bit followed by
the continuation under `securityImplWithChallengeKeyPair`.  At a paused state
the challenged counter is one short of the challenge epoch, so after the step
`injectionPassed` holds at every reachable state and the first apex erases the
installed key pair from the continuation; at the resume bit `true` the bumped
counter gives `challengePassed` and the second apex erases the bit.  The
result is the challenge bridges' left-hand side. -/

private lemma injResumeKilled_pausedA_probOutput_true_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK) (skStar : SK)
    (base : SecurityState K PK SK C)
    (hInv : epochCounterInv base)
    (hWill : willChallengeA gp base = true)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool) :
    Pr[= true | injResumeKilled kem hDet leak gp b pkStar skStar
        (.pausedA cont, preAToBHonestState base pkStar skStar)] =
      Pr[= true |
        ((securityImpl kem hDet leak gp b
          (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
          (preAToBHonestState base pkStar skStar)) >>= fun p =>
            (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2] := by
  have hWill' := hWill
  simp only [willChallengeA, Bool.and_eq_true, beq_iff_eq] at hWill'
  obtain ⟨⟨_hvalid, hpartyEq⟩, htA⟩ := hWill'
  have htAB : base.tA = base.tB := by
    rcases lastAction_of_willChallengeA gp base hWill with hl | hl <;>
      simpa [epochCounterInv, hl] using hInv
  have hWillH : willChallengeA gp (preAToBHonestState base pkStar skStar) = true := by
    simpa [willChallengeA, preAToBHonestState] using hWill
  simp only [injResumeKilled, injectedChallengeResume, map_bind]
  rw [show (securityImplWithChallengeKeyPair kem hDet leak gp b pkStar skStar
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (preAToBHonestState base pkStar skStar) =
      (securityImpl kem hDet leak gp b
        (CKAScheme.ckaSecuritySpec.OChallA : (securitySpec leak).Domain)).run
        (preAToBHonestState base pkStar skStar) from rfl]
  refine probOutput_bind_congr fun p hp => ?_
  obtain ⟨hpA, hpB⟩ := challA_run_support_counters kem hDet leak gp b
    (preAToBHonestState base pkStar skStar) pkStar rfl hWillH p hp
  simp only [preAToBHonestState] at hpA hpB
  have hinj : injectionPassed gp p.2 := by
    simp only [injectionPassed, hpartyEq]
    omega
  change Pr[= true | (simulateQ (securityImplWithChallengeKeyPair kem hDet leak gp b
      pkStar skStar) (cont p.1)).run' p.2] = _
  cases b with
  | false =>
      exact probOutput_simulateQ_wck_run'_eq_of_injectionPassed kem hDet leak gp
        false pkStar skStar (cont p.1) p.2 hinj
  | true =>
      have hpass : challengePassed gp p.2 := by
        simp only [challengePassed, hpartyEq]
        omega
      exact (probOutput_simulateQ_wck_run'_eq_of_injectionPassed kem hDet leak gp
        true pkStar skStar (cont p.1) p.2 hinj).trans
        (probOutput_simulateQ_true_false_run'_eq_of_challengePassed kem hDet leak
          gp (cont p.1) p.2 hpass)

private lemma injResumeKilled_pausedB_probOutput_true_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (b : Bool)
    (pkStar : PK) (skStar : SK)
    (base : SecurityState K PK SK C)
    (hInv : epochCounterInv base)
    (hWill : willChallengeB gp base = true)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool) :
    Pr[= true | injResumeKilled kem hDet leak gp b pkStar skStar
        (.pausedB cont, preBToAHonestState base pkStar skStar)] =
      Pr[= true |
        ((securityImpl kem hDet leak gp b
          (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
          (preBToAHonestState base pkStar skStar)) >>= fun p =>
            (simulateQ (securityImpl kem hDet leak gp false) (cont p.1)).run' p.2] := by
  have hWill' := hWill
  simp only [willChallengeB, Bool.and_eq_true, beq_iff_eq] at hWill'
  obtain ⟨⟨_hvalid, hpartyEq⟩, htB⟩ := hWill'
  have hl := lastAction_of_willChallengeB gp base hWill
  have htAB : base.tA = base.tB := by
    simpa [epochCounterInv, hl] using hInv
  have hWillH : willChallengeB gp (preBToAHonestState base pkStar skStar) = true := by
    simpa [willChallengeB, preBToAHonestState] using hWill
  simp only [injResumeKilled, injectedChallengeResume, map_bind]
  rw [show (securityImplWithChallengeKeyPair kem hDet leak gp b pkStar skStar
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (preBToAHonestState base pkStar skStar) =
      (securityImpl kem hDet leak gp b
        (CKAScheme.ckaSecuritySpec.OChallB : (securitySpec leak).Domain)).run
        (preBToAHonestState base pkStar skStar) from rfl]
  refine probOutput_bind_congr fun p hp => ?_
  obtain ⟨hpB, hpA⟩ := challB_run_support_counters kem hDet leak gp b
    (preBToAHonestState base pkStar skStar) pkStar rfl hWillH p hp
  simp only [preBToAHonestState] at hpA hpB
  have hinj : injectionPassed gp p.2 := by
    simp only [injectionPassed, hpartyEq]
    omega
  change Pr[= true | (simulateQ (securityImplWithChallengeKeyPair kem hDet leak gp b
      pkStar skStar) (cont p.1)).run' p.2] = _
  cases b with
  | false =>
      exact probOutput_simulateQ_wck_run'_eq_of_injectionPassed kem hDet leak gp
        false pkStar skStar (cont p.1) p.2 hinj
  | true =>
      have hpass : challengePassed gp p.2 := by
        simp only [challengePassed, hpartyEq]
        omega
      exact (probOutput_simulateQ_wck_run'_eq_of_injectionPassed kem hDet leak gp
        true pkStar skStar (cont p.1) p.2 hinj).trans
        (probOutput_simulateQ_true_false_run'_eq_of_challengePassed kem hDet leak
          gp (cont p.1) p.2 hpass)

/-! ## The paused chains

At a paused pair of the coupling postcondition the two killed resumes have
equal success probability with the bit reversed: the challenge bridge carries
the hidden-state move, and the reduction side normalizes to
`finishChallengeStepRaw`.  At the resume bit `false` the bridge consumes the
encapsulated key and the unused uniform draw integrates out; at `true` the
bridge draws the uniform key itself. -/

private lemma pausedA_killed_probOutput_true_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (b : Bool)
    (pkStar : PK) (skStar : SK)
    (base : SecurityState K PK SK C)
    (hInv : epochCounterInv base)
    (hWill : willChallengeA gp base = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool) :
    Pr[= true | injResumeKilled kem hDet leak gp b pkStar skStar
        (.pausedA cont, preAToBHonestState base pkStar skStar)] =
      Pr[= true | rawResumeKilled kem hDet leak gp (!b) pkStar
        (.pausedA cont, preAToBReductionState base pkStar)] := by
  rw [injResumeKilled_pausedA_probOutput_true_eq kem hDet leak gp b pkStar skStar
    base hInv hWill cont]
  have hWillR : willChallengeA gp (preAToBReductionState base pkStar) = true := by
    simpa [willChallengeA, preAToBReductionState] using hWill
  cases b with
  | false =>
      rw [challA_sampled_reduction_cont_probOutput_true_eq kem hDet hkem leak gp
        hgp base hInv hWill hks cont]
      simp only [Bool.not_false, rawResumeKilled, rawResume, ↓reduceIte]
      refine probOutput_bind_congr fun ck _ => ?_
      obtain ⟨cStar, kReal⟩ := ck
      rw [reductionBranch_challA_cont_eq_finishChallengeStepRaw kem hDet leak gp
        pkStar cStar kReal (preAToBReductionState base pkStar) hWillR cont]
      rw [probOutput_bind_const]
      simp [HasEvalPMF.probFailure_eq_zero]
  | true =>
      rw [challA_sampled_reduction_random_cont_probOutput_true_eq kem hDet hkem
        leak gp hgp base hInv hWill hks cont]
      simp only [Bool.not_true, rawResumeKilled, rawResume, Bool.false_eq_true,
        ↓reduceIte]
      refine probOutput_bind_congr fun ck _ => ?_
      obtain ⟨cStar, _kReal⟩ := ck
      refine probOutput_bind_congr fun kRand _ => ?_
      rw [reductionBranch_challA_cont_eq_finishChallengeStepRaw kem hDet leak gp
        pkStar cStar kRand (preAToBReductionState base pkStar) hWillR cont]

private lemma pausedB_killed_probOutput_true_eq
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (b : Bool)
    (pkStar : PK) (skStar : SK)
    (base : SecurityState K PK SK C)
    (hInv : epochCounterInv base)
    (hWill : willChallengeB gp base = true)
    (hks : (pkStar, skStar) ∈ support kem.keygen)
    (cont : Option (Message C PK × K) → OracleComp (securitySpec leak) Bool) :
    Pr[= true | injResumeKilled kem hDet leak gp b pkStar skStar
        (.pausedB cont, preBToAHonestState base pkStar skStar)] =
      Pr[= true | rawResumeKilled kem hDet leak gp (!b) pkStar
        (.pausedB cont, preBToAReductionState base pkStar)] := by
  rw [injResumeKilled_pausedB_probOutput_true_eq kem hDet leak gp b pkStar skStar
    base hInv hWill cont]
  have hWillR : willChallengeB gp (preBToAReductionState base pkStar) = true := by
    simpa [willChallengeB, preBToAReductionState] using hWill
  cases b with
  | false =>
      rw [challB_sampled_reduction_cont_probOutput_true_eq kem hDet hkem leak gp
        hgp base hInv hWill hks cont]
      simp only [Bool.not_false, rawResumeKilled, rawResume, ↓reduceIte]
      refine probOutput_bind_congr fun ck _ => ?_
      obtain ⟨cStar, kReal⟩ := ck
      rw [reductionBranch_challB_cont_eq_finishChallengeStepRaw kem hDet leak gp
        pkStar cStar kReal (preBToAReductionState base pkStar) hWillR cont]
      rw [probOutput_bind_const]
      simp [HasEvalPMF.probFailure_eq_zero]
  | true =>
      rw [challB_sampled_reduction_random_cont_probOutput_true_eq kem hDet hkem
        leak gp hgp base hInv hWill hks cont]
      simp only [Bool.not_true, rawResumeKilled, rawResume, Bool.false_eq_true,
        ↓reduceIte]
      refine probOutput_bind_congr fun ck _ => ?_
      obtain ⟨cStar, _kReal⟩ := ck
      refine probOutput_bind_congr fun kRand _ => ?_
      rw [reductionBranch_challB_cont_eq_finishChallengeStepRaw kem hDet leak gp
        pkStar cStar kRand (preBToAReductionState base pkStar) hWillR cont]

/-! ## The killed games agree with the bit reversed

The two killed sub-games are the coupled prefixes bound to the killed
resumes.  The coupling inductions relate the prefix runs; on finished pairs
both killed resumes return `false`, and on paused pairs the chains above
apply.  The initial states are equal inside the pre-injection invariant,
except that party A with challenge epoch `1` starts at the challenge phase of
`coupleRelA`. -/

private lemma injectedKilledGame_probOutput_true_eq_A
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.A)
    (b : Bool) :
    Pr[= true | injectedKilledGame kem hDet leak adv gp b] =
      Pr[= true | reductionKilledGame kem hDet leak adv gp (!b)] := by
  have hodd : gp.challengeEpoch % 2 = 1 := by
    simpa [challengeEpochCompatible, hparty] using hgp.challenge_epoch_compatible
  refine probOutput_true_eq_of_relTriple_eqRel ?_
  simp only [injectedKilledGame, reductionKilledGame]
  refine relTriple_bind (relTriple_refl_support kem.keygen) ?_
  rintro ⟨pk0, sk0⟩ _ ⟨rfl, h0⟩
  refine relTriple_bind (relTriple_refl_support kem.keygen) ?_
  rintro ⟨pkStar, skStar⟩ _ ⟨rfl, hks⟩
  refine relTriple_bind
    (injectedPrefix_couples_challengePrefix_A kem hDet hkem leak gp hparty
      hgp.two_le_deltaPCS hodd hgp.deltaFS_zero pkStar skStar adv _ _ ?_) ?_
  · by_cases he : gp.challengeEpoch = 1
    · have hcond : (gp.challengeEpoch == 1 &&
          gp.challengedParty == CKAScheme.CKAParty.A) = true := by
        simp [he, hparty]
      simp only [hcond, ↓reduceIte]
      refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_, rfl⟩))
      · simp [willChallengeA, CKAScheme.initGameState, CKAScheme.validStep,
          hparty, he]
      · simp [epochCounterInv, CKAScheme.initGameState]
    · have hcond : (gp.challengeEpoch == 1 &&
          gp.challengedParty == CKAScheme.CKAParty.A) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        exact Or.inl he
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      exact Or.inl ⟨rfl, ⟨pk0, sk0, h0, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        by omega, rfl, rfl⟩
  · intro z z' hpost
    simp only [couplePostA] at hpost
    rcases hpost with ⟨⟨a, hz⟩, ⟨a', hz'⟩⟩ | ⟨cont, base, rfl, rfl, hInv, hWill⟩
    · obtain ⟨res, σ⟩ := z
      obtain ⟨res', σ'⟩ := z'
      obtain rfl : res = CKAChallengeStepResult.done a := hz
      obtain rfl : res' = CKAChallengeStepResult.done a' := hz'
      simp only [injResumeKilled, rawResumeKilled]
      exact relTriple_pure_pure rfl
    · exact relTriple_eqRel_of_probOutput_true_eq
        (pausedA_killed_probOutput_true_eq kem hDet hkem leak gp hgp b
          pkStar skStar base hInv hWill hks cont)

private lemma injectedKilledGame_probOutput_true_eq_B
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp)
    (hparty : gp.challengedParty = CKAScheme.CKAParty.B)
    (b : Bool) :
    Pr[= true | injectedKilledGame kem hDet leak adv gp b] =
      Pr[= true | reductionKilledGame kem hDet leak adv gp (!b)] := by
  have heven : gp.challengeEpoch % 2 = 0 ∧ 0 < gp.challengeEpoch := by
    simpa [challengeEpochCompatible, hparty] using hgp.challenge_epoch_compatible
  refine probOutput_true_eq_of_relTriple_eqRel ?_
  simp only [injectedKilledGame, reductionKilledGame]
  refine relTriple_bind (relTriple_refl_support kem.keygen) ?_
  rintro ⟨pk0, sk0⟩ _ ⟨rfl, h0⟩
  refine relTriple_bind (relTriple_refl_support kem.keygen) ?_
  rintro ⟨pkStar, skStar⟩ _ ⟨rfl, hks⟩
  refine relTriple_bind
    (injectedPrefix_couples_challengePrefix_B kem hDet hkem leak gp hparty
      hgp.two_le_deltaPCS heven.1 hgp.deltaFS_zero pkStar skStar adv _ _ ?_) ?_
  · have hcond : (gp.challengeEpoch == 1 &&
        gp.challengedParty == CKAScheme.CKAParty.A) = false := by
      simp [hparty]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    exact Or.inl ⟨rfl, ⟨pk0, sk0, h0, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      by omega, rfl, rfl⟩
  · intro z z' hpost
    simp only [couplePostB] at hpost
    rcases hpost with ⟨⟨a, hz⟩, ⟨a', hz'⟩⟩ | ⟨cont, base, rfl, rfl, hInv, hWill⟩
    · obtain ⟨res, σ⟩ := z
      obtain ⟨res', σ'⟩ := z'
      obtain rfl : res = CKAChallengeStepResult.done a := hz
      obtain rfl : res' = CKAChallengeStepResult.done a' := hz'
      simp only [injResumeKilled, rawResumeKilled]
      exact relTriple_pure_pure rfl
    · exact relTriple_eqRel_of_probOutput_true_eq
        (pausedB_killed_probOutput_true_eq kem hDet hkem leak gp hgp b
          pkStar skStar base hInv hWill hks cont)

/-! ## The gap bridge

Each game's success probability is its killed part plus its finished part.
The finished parts read nothing bit-dependent, so they cancel inside each
game's own gap; the killed parts agree across the games with the bit
reversed, so the two absolute gaps are equal. -/

lemma cka_injected_honest_gap_eq_keygen_swapped_raw_gap
    [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    |(Pr[= true |
        ckaSecurityFixedBranchWithInjectedChallengeKey
          kem hDet leak adv gp true]).toReal -
      (Pr[= true |
        ckaSecurityFixedBranchWithInjectedChallengeKey
          kem hDet leak adv gp false]).toReal| =
    |(Pr[= true |
        ckaReductionINDCPABranchRawKeygenSwapped
          kem hDet leak adv gp true]).toReal -
      (Pr[= true |
        ckaReductionINDCPABranchRawKeygenSwapped
          kem hDet leak adv gp false]).toReal| := by
  have hkill : ∀ b : Bool,
      Pr[= true | injectedKilledGame kem hDet leak adv gp b] =
        Pr[= true | reductionKilledGame kem hDet leak adv gp (!b)] := by
    intro b
    cases hcp : gp.challengedParty with
    | A =>
        exact injectedKilledGame_probOutput_true_eq_A kem hDet hkem leak adv
          gp hgp hcp b
    | B =>
        exact injectedKilledGame_probOutput_true_eq_B kem hDet hkem leak adv
          gp hgp hcp b
  have h1 := hkill true
  have h0 := hkill false
  simp only [Bool.not_true, Bool.not_false] at h1 h0
  rw [injected_probOutput_eq_killed_add_done kem hDet leak adv gp true,
    injected_probOutput_eq_killed_add_done kem hDet leak adv gp false,
    reduction_probOutput_eq_killed_add_done kem hDet leak adv gp true,
    reduction_probOutput_eq_killed_add_done kem hDet leak adv gp false,
    h1, h0]
  rw [ENNReal.toReal_add probOutput_ne_top probOutput_ne_top,
    ENNReal.toReal_add probOutput_ne_top probOutput_ne_top,
    ENNReal.toReal_add probOutput_ne_top probOutput_ne_top,
    ENNReal.toReal_add probOutput_ne_top probOutput_ne_top]
  rw [add_sub_add_right_eq_sub, add_sub_add_right_eq_sub]
  exact abs_sub_comm _ _

end kemCKA
