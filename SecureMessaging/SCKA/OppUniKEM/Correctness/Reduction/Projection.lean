import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.OneStep
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.SendA
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.RecvB
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.SendB
import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect.RecvA
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Opp-UniKEM-CKA Tracked-State Projection

Forgetting the failure bit projects the tracked game onto the ordinary one:

* `trackedCorrectnessImpl_project`, `tracked_run_project` — one query, and
  a whole `simulateQ` run, have the same visible result and game state
  after projection;
* `correctnessExp_eq_final_map` — the correctness experiment as a
  final-state map over the simulated run;
* `trackedCorrectnessImpl_preserves` — the tracked invariant survives
  every query, by the `Perfect` preservation theorems.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

open SCKAScheme.sckaCorrectnessSpec

namespace Reduction.Internal

/-- Forgetting the sticky failure bit after one tracked query recovers the
corresponding ordinary correctness-game query. -/
lemma trackedCorrectnessImpl_project [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    Prod.map id Prod.fst <$>
        ((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p =
      ((SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run p.1 := by
  unfold trackedCorrectnessImpl
  change Prod.map id Prod.fst <$> (do
      let z ← ((SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run p.1
      pure (z.1, (z.2, p.2 || currentKEMFailure kem onoff hDet z.2))) = _
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp

/-- The per-query state projection lifts through `simulateQ`, projecting a
complete tracked adversary run to the ordinary correctness-game run. -/
lemma tracked_run_project [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    Prod.map id Prod.fst <$>
        (simulateQ
          (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) adv).run p =
      (simulateQ
        (SCKAScheme.sckaCorrectnessImpl
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run p.1 := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.sckaCorrectnessImpl
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
    Prod.fst
    (trackedCorrectnessImpl_project kem onoff hDet ecEk ecCt0 ecCt1 leak)
    adv p

/-- The ordinary correctness experiment is the final state's correctness bit
mapped over the simulated correctness-game run from its initial state. -/
lemma correctnessExp_eq_final_map [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) :
    SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv =
      (fun z => z.2.correct) <$>
        (simulateQ
          (SCKAScheme.sckaCorrectnessImpl
            (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run
          (initialGame kem onoff) := by
  simp [SCKAScheme.correctnessExp, scheme, initKeyGen, initA, initB,
    initialGame, initialA, initialB, map_eq_bind_pure_comp]

/-- Every tracked correctness query preserves the tracked invariant, using the
Perfect oracle theorem for the query's uniform, send, or receive transition. -/
lemma trackedCorrectnessImpl_preserves
    [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff) :
    QueryImpl.PreservesInv
      (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (trackedInv kem onoff hDet ecEk ecCt0 ecCt1) := by
  intro t p hp z hz
  unfold trackedCorrectnessImpl at hz
  change z ∈ support (do
    let y ← ((SCKAScheme.sckaCorrectnessImpl
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run p.1
    pure (y.1, (y.2, p.2 || currentKEMFailure kem onoff hDet y.2))) at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  simp only [mem_support_pure_iff] at hz
  subst z
  rcases hp with hbad | ⟨hreach, hfailOld⟩
  · left
    simp [hbad]
  have hcurrent : CurrentKEMCorrect kem onoff hDet p.1 :=
    currentKEMFailure_eq_false_implies_current kem onoff hDet ecEk ecCt0 ecCt1
      p.1 hreach hfailOld
  have hreach' : reachableInv kem onoff ecEk ecCt0 ecCt1 y.2 := by
    match t with
    | OUnif n =>
        exact oracleUnif_preserves_reachableInv kem onoff ecEk ecCt0 ecCt1
          n p.1 hreach y hy
    | OSendA =>
        exact oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1
          leak hEkPos () p.1 hreach y hy
    | OSendB =>
        exact oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 hCt0Pos
          ecCt1 hCt1Pos leak () p.1 hreach y hy
    | ORecvA n =>
        exact oracleRecvA_preserves_reachableInv_of_current kem onoff hDet ecEk ecCt0
          hCt0Correct ecCt1 hCt1Correct hCt1Pos leak n p.1 hreach hcurrent y hy
    | ORecvB n =>
        exact oracleRecvB_preserves_reachableInv kem onoff hDet ecEk hEkCorrect hEkPos
          ecCt0 ecCt1 leak n p.1 hreach y hy
  by_cases hfail : currentKEMFailure kem onoff hDet y.2 = true
  · left
    simp [hfail]
  · right
    have hfailFalse : currentKEMFailure kem onoff hDet y.2 = false := by
      cases h : currentKEMFailure kem onoff hDet y.2 <;> simp [h] at hfail ⊢
    exact ⟨hreach', hfailFalse⟩

end Reduction.Internal

end oppUniKemCKA
