/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Projection
import ToVCVio.OracleComp.ExpectedPayoff

/-!
# Opp-UniKEM-CKA Adversary Composition

Composes the one-query facts over an adaptive adversary, by induction over
its oracle-computation tree.  Two routes, with matching query budgets:

* score route (`tracked_score_adversary_le`, budget `SendQueryBound`
  counting `SendA` and `SendB`) — each send may spend one copy of the step
  error; the expected-payoff bind laws accumulate the allowance to
  `q · epsilon`;
* stepwise route (`tracked_bad_probability_le`, budget `SendBQueryBound`
  counting only `SendB`) — a union bound charges `δ` per `SendB` and zero
  to every other query.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

open SCKAScheme.sckaCorrectnessSpec
open Reduction.Internal

/-- From a state whose current KEM material is consistent, one `SendB` call
produces a state with `currentKEMFailure` with probability at most `δ`. -/
def SendBFailureBound [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) (δ : ℝ≥0∞) : Prop :=
  ∀ s, CurrentKEMCorrect kem onoff hDet s →
    Pr[fun z => currentKEMFailure kem onoff hDet z.2 = true |
      (SCKAScheme.oracleSendB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s] ≤ δ

/-- From a state whose current KEM material is consistent, no oracle other
than `SendB` can produce a state with `currentKEMFailure`. -/
def NonSendBPreservesCurrent [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff) : Prop :=
  ∀ t, t ≠ (OSendB : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain) →
    ∀ s, CurrentKEMCorrect kem onoff hDet s →
      Pr[fun z => currentKEMFailure kem onoff hDet z.2 = true |
        ((SCKAScheme.sckaCorrectnessImpl
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run s] = 0

/-- Syntactic bound on the number of `SendB` queries made by a correctness
adversary. -/
def SendBQueryBound (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) : Prop :=
  adv.IsQueryBoundP
    (fun t => t = (OSendB : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)) q

/-- Syntactic bound on the total number of send queries.  Both send oracles
count: either party may draw the first sample of a fresh epoch. -/
def SendQueryBound (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) : Prop :=
  adv.IsQueryBoundP (IsSendQuery (Sym := Sym)) q

namespace Reduction.Internal

/-- Combine the oracle-specific one-step bounds into a uniform score increase
bound that charges exactly the send queries. -/
lemma tracked_score_step_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool)
    (hp : trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p) :
    expectedPayoff
        (((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p)
        (fun z => trackedFailureScore kem onoff hDet z.2) ≤
      trackedFailureScore kem onoff hDet p +
        if IsSendQuery t
        then factorCorrectnessError kem onoff hDet
        else 0 := by
  cases hbad : p.2 with
  | true =>
      exact tracked_step_score_le_of_bad kem onoff hDet ecEk ecCt0 ecCt1 leak
        t p hbad _
  | false =>
      have hgood : reachableInv kem onoff ecEk ecCt0 ecCt1 p.1 ∧
          currentKEMFailure kem onoff hDet p.1 = false := by
        rcases hp with hpbad | hpGood
        · simp [hbad] at hpbad
        · exact hpGood
      have hpEq : p = (p.1, false) := Prod.ext rfl hbad
      rw [hpEq]
      match t with
      | OUnif n =>
          simpa [IsSendQuery, isSendQuery] using
            tracked_nonSend_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak
              (OUnif n) (by simp [IsSendQuery, isSendQuery]) _ hgood.1 hgood.2
      | OSendA =>
          simpa [IsSendQuery, isSendQuery] using
            tracked_sendA_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak
              _ hgood.1 hgood.2
      | OSendB =>
          simpa [IsSendQuery, isSendQuery] using
            tracked_sendB_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak
              _ hgood.1 hgood.2
      | ORecvA n =>
          simpa [IsSendQuery, isSendQuery] using
            tracked_nonSend_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak
              (ORecvA n) (by simp [IsSendQuery, isSendQuery]) _ hgood.1 hgood.2
      | ORecvB n =>
          simpa [IsSendQuery, isSendQuery] using
            tracked_nonSend_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak
              (ORecvB n) (by simp [IsSendQuery, isSendQuery]) _ hgood.1 hgood.2

omit [DecidableEq Sym] in
/-- Bound the probability that the sticky bad bit is set by the tracked
failure score's expected payoff. -/
lemma tracked_bad_probability_le_score [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (oa : ProbComp
      (Bool ×
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) ×
          Bool))) :
    Pr[fun z => z.2.2 = true | oa] ≤
      expectedPayoff oa (fun z => trackedFailureScore kem onoff hDet z.2) := by
  classical
  unfold expectedPayoff
  calc
    Pr[fun z => z.2.2 = true | oa] ≤
        ∑' z, Pr[= z | oa] * trackedFailureScore kem onoff hDet z.2 := by
      apply probEvent_le_tsum_probOutput_mul_cost
      intro z hz
      simp [trackedFailureScore, hz]
    _ ≤ Pr[⊥ | oa] +
        ∑' z, Pr[= z | oa] * trackedFailureScore kem onoff hDet z.2 :=
      le_add_left le_rfl

/-- Lift a per-query tracked-score bound through an adaptive adversary with at
most `q` send queries by induction on its oracle-computation tree. -/
lemma tracked_score_adversary_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) (q : ℕ)
    (hq : SendQueryBound adv q) (epsilon : ℝ≥0∞)
    (hpres : QueryImpl.PreservesInv
      (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (trackedInv kem onoff hDet ecEk ecCt0 ecCt1))
    (hstep : ∀ t p,
      trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p →
      expectedPayoff
          (((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p)
          (fun z => trackedFailureScore kem onoff hDet z.2) ≤
        trackedFailureScore kem onoff hDet p +
          if IsSendQuery t then epsilon else 0) :
    ∀ p, trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p →
      expectedPayoff
          ((simulateQ
            (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) adv).run p)
          (fun z => trackedFailureScore kem onoff hDet z.2) ≤
        trackedFailureScore kem onoff hDet p + (q : ℝ≥0∞) * epsilon := by
  let tracked := trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  let score := trackedFailureScore (Sym := Sym) kem onoff hDet
  unfold SendQueryBound at hq
  induction adv using OracleComp.inductionOn generalizing q with
  | pure x =>
      intro p hp
      simp [simulateQ_pure, StateT.run_pure, expectedPayoff_pure]
  | @query_bind t cont ih =>
      intro p hp
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcont⟩ := hq
      rw [simulateQ_query_bind, StateT.run_bind, expectedPayoff_bind]
      by_cases ht : IsSendQuery t
      · have hqpos : 0 < q := hcan.resolve_left (not_not_intro ht)
        have htail : ∀ z ∈ support ((tracked t).run p),
            expectedPayoff
                ((simulateQ tracked (cont z.1)).run z.2)
                (fun w => score w.2) ≤
              score z.2 + (((q - 1 : ℕ) : ℝ≥0∞) * epsilon) := by
          intro z hz
          exact ih z.1 (q - 1) (by simpa [ht] using hcont z.1) z.2
            (hpres t p hp z hz)
        calc
          (Pr[⊥ | (tracked t).run p] +
            ∑' z, Pr[= z | (tracked t).run p] *
              expectedPayoff ((simulateQ tracked (cont z.1)).run z.2)
                (fun w => score w.2)) ≤
              Pr[⊥ | (tracked t).run p] +
                ∑' z, Pr[= z | (tracked t).run p] *
                (score z.2 + (((q - 1 : ℕ) : ℝ≥0∞) * epsilon)) := by
            exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun z => by
              by_cases hz : z ∈ support ((tracked t).run p)
              · exact mul_le_mul' le_rfl (htail z hz)
              · simp [(probOutput_eq_zero_iff _ _).2 hz])
          _ ≤ expectedPayoff ((tracked t).run p) (fun z => score z.2) +
                (((q - 1 : ℕ) : ℝ≥0∞) * epsilon) :=
            expectedPayoff_add_const_le _ _ _
          _ ≤ (score p + epsilon) +
                (((q - 1 : ℕ) : ℝ≥0∞) * epsilon) := by
            exact add_le_add (by simpa [tracked, Inv, score, ht] using hstep t p hp) le_rfl
          _ = score p + (q : ℝ≥0∞) * epsilon := by
            have hcast : (((q - 1 : ℕ) : ℝ≥0∞) + 1) = (q : ℝ≥0∞) := by
              exact_mod_cast Nat.sub_add_cancel hqpos
            rw [← hcast, add_mul, one_mul]
            ac_rfl
      · have htail : ∀ z ∈ support ((tracked t).run p),
            expectedPayoff
                ((simulateQ tracked (cont z.1)).run z.2)
                (fun w => score w.2) ≤
              score z.2 + ((q : ℝ≥0∞) * epsilon) := by
          intro z hz
          exact ih z.1 q (by simpa [ht] using hcont z.1) z.2
            (hpres t p hp z hz)
        calc
          (Pr[⊥ | (tracked t).run p] +
            ∑' z, Pr[= z | (tracked t).run p] *
              expectedPayoff ((simulateQ tracked (cont z.1)).run z.2)
                (fun w => score w.2)) ≤
              Pr[⊥ | (tracked t).run p] +
                ∑' z, Pr[= z | (tracked t).run p] *
                (score z.2 + ((q : ℝ≥0∞) * epsilon)) := by
            exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun z => by
              by_cases hz : z ∈ support ((tracked t).run p)
              · exact mul_le_mul' le_rfl (htail z hz)
              · simp [(probOutput_eq_zero_iff _ _).2 hz])
          _ ≤ expectedPayoff ((tracked t).run p) (fun z => score z.2) +
                ((q : ℝ≥0∞) * epsilon) :=
            expectedPayoff_add_const_le _ _ _
          _ ≤ score p + ((q : ℝ≥0∞) * epsilon) := by
            simpa [tracked, Inv, score, ht] using
              add_le_add (hstep t p hp) (le_refl ((q : ℝ≥0∞) * epsilon))

/-- Relate the tracked bad-event probability for one query from a clear sticky
bit to the ordinary game's `currentKEMFailure` probability. -/
lemma tracked_step_bad_probability [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr[fun z => z.2.2 = true |
      ((trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run
        (s, false)] =
    Pr[fun z => currentKEMFailure kem onoff hDet z.2 = true |
      ((SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run s] := by
  change Pr[fun z => z.2.2 = true | do
      let y ← ((SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))] = _
  rw [show (do
      let y ← ((SCKAScheme.sckaCorrectnessImpl
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) =
      (fun y => (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) <$>
        ((SCKAScheme.sckaCorrectnessImpl
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run s from
      (map_eq_bind_pure_comp _ _ _).symm]
  rw [probEvent_map]
  congr 1

/-- Accumulate the stepwise `SendB` failure premise over an adversary with at
most `q` `SendB` queries while all other queries preserve consistency. -/
lemma tracked_bad_probability_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (δ : ℝ≥0∞)
    (hSend : SendBFailureBound kem onoff hDet ecEk ecCt0 ecCt1 leak δ)
    (hFree : NonSendBPreservesCurrent kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) {q : ℕ}
    (hq : SendBQueryBound adv q) :
    ∀ p, trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p → p.2 = false →
      Pr[fun z => z.2.2 = true |
        (simulateQ
          (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) adv).run p] ≤
        (q : ℝ≥0∞) * δ := by
  let tracked := trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  have hpres : QueryImpl.PreservesInv tracked Inv :=
    trackedCorrectnessImpl_preserves kem onoff hDet ecEk hEkCorrect hEkPos
      ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak
  unfold SendBQueryBound at hq
  induction adv using OracleComp.inductionOn generalizing q with
  | pure x =>
      intro p hp hpbad
      simp [hpbad]
  | @query_bind t cont ih =>
      intro p hp hpbad
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcont⟩ := hq
      have hrun :
          (simulateQ tracked (query t >>= cont)).run p =
            (tracked t).run p >>= fun z => (simulateQ tracked (cont z.1)).run z.2 := by
        simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, StateT.run_bind]
      change Pr[fun z => z.2.2 = true |
        (simulateQ tracked (query t >>= cont)).run p] ≤ (q : ℝ≥0∞) * δ
      rw [hrun]
      have hpGood : CurrentKEMCorrect kem onoff hDet p.1 := by
        rcases hp with hbad | hgood
        · simp [hpbad] at hbad
        · exact currentKEMFailure_eq_false_implies_current kem onoff hDet
            ecEk ecCt0 ecCt1 p.1 hgood.1 hgood.2
      by_cases ht : t = (OSendB :
          (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
      · have hqpos : 0 < q := hcan.resolve_left (not_not_intro ht)
        subst t
        have hp_eq : p = (p.1, false) := Prod.ext rfl hpbad
        have hhead : Pr[fun z => ¬z.2.2 = false | (tracked OSendB).run p] ≤ δ := by
          calc
            Pr[fun z => ¬z.2.2 = false | (tracked OSendB).run p] =
                Pr[fun z => z.2.2 = true | (tracked OSendB).run p] := by
              refine probEvent_congr' (fun z _ => ?_) rfl
              cases z.2.2 <;> simp
            _ = Pr[fun z => currentKEMFailure kem onoff hDet z.2 = true |
                ((SCKAScheme.sckaCorrectnessImpl
                  (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) OSendB).run p.1] := by
              rw [hp_eq]
              exact tracked_step_bad_probability kem onoff hDet ecEk ecCt0 ecCt1 leak
                OSendB p.1
            _ ≤ δ := hSend p.1 hpGood
        have htail : ∀ z ∈ support ((tracked OSendB).run p), z.2.2 = false →
            Pr[fun w => ¬w.2.2 = false |
              (simulateQ tracked (cont z.1)).run z.2] ≤ ((q - 1 : ℕ) : ℝ≥0∞) * δ := by
          intro z hz hzbad
          calc
            Pr[fun w => ¬w.2.2 = false |
                (simulateQ tracked (cont z.1)).run z.2] =
                Pr[fun w => w.2.2 = true |
                  (simulateQ tracked (cont z.1)).run z.2] := by
              refine probEvent_congr' (fun w _ => ?_) rfl
              cases w.2.2 <;> simp
            _ ≤ ((q - 1 : ℕ) : ℝ≥0∞) * δ :=
              ih z.1 (by simpa using hcont z.1) z.2
                (hpres OSendB p hp z hz) hzbad
        have hunion := probEvent_bind_le_add hhead htail
        have hunion' : Pr[fun z => z.2.2 = true |
            (tracked OSendB).run p >>= fun z =>
              (simulateQ tracked (cont z.1)).run z.2] ≤
              δ + ((q - 1 : ℕ) : ℝ≥0∞) * δ := by
          calc
            Pr[fun z => z.2.2 = true | (tracked OSendB).run p >>= fun z =>
                (simulateQ tracked (cont z.1)).run z.2] =
                Pr[fun z => ¬z.2.2 = false | (tracked OSendB).run p >>= fun z =>
                  (simulateQ tracked (cont z.1)).run z.2] := by
              refine probEvent_congr' (fun z _ => ?_) rfl
              cases z.2.2 <;> simp
            _ ≤ δ + ((q - 1 : ℕ) : ℝ≥0∞) * δ := hunion
        refine hunion'.trans ?_
        have hcast : (((q - 1 : ℕ) : ℝ≥0∞) + 1) = (q : ℝ≥0∞) := by
          exact_mod_cast Nat.sub_add_cancel hqpos
        rw [← hcast]
        rw [add_mul, one_mul, add_comm]
      · have hp_eq : p = (p.1, false) := Prod.ext rfl hpbad
        have hhead : Pr[fun z => ¬z.2.2 = false | (tracked t).run p] ≤ 0 := by
          calc
            Pr[fun z => ¬z.2.2 = false | (tracked t).run p] =
                Pr[fun z => z.2.2 = true | (tracked t).run p] := by
              refine probEvent_congr' (fun z _ => ?_) rfl
              cases z.2.2 <;> simp
            _ = Pr[fun z => currentKEMFailure kem onoff hDet z.2 = true |
                ((SCKAScheme.sckaCorrectnessImpl
                  (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) t).run p.1] := by
              rw [hp_eq]
              exact tracked_step_bad_probability kem onoff hDet ecEk ecCt0 ecCt1 leak
                t p.1
            _ ≤ 0 := le_of_eq (hFree t ht p.1 hpGood)
        have htail : ∀ z ∈ support ((tracked t).run p), z.2.2 = false →
            Pr[fun w => ¬w.2.2 = false |
              (simulateQ tracked (cont z.1)).run z.2] ≤ (q : ℝ≥0∞) * δ := by
          intro z hz hzbad
          calc
            Pr[fun w => ¬w.2.2 = false |
                (simulateQ tracked (cont z.1)).run z.2] =
                Pr[fun w => w.2.2 = true |
                  (simulateQ tracked (cont z.1)).run z.2] := by
              refine probEvent_congr' (fun w _ => ?_) rfl
              cases w.2.2 <;> simp
            _ ≤ (q : ℝ≥0∞) * δ :=
              ih z.1 (by simpa [ht] using hcont z.1) z.2
                (hpres t p hp z hz) hzbad
        have hunion := probEvent_bind_le_add hhead htail
        calc
          Pr[fun z => z.2.2 = true | (tracked t).run p >>= fun z =>
              (simulateQ tracked (cont z.1)).run z.2] =
              Pr[fun z => ¬z.2.2 = false | (tracked t).run p >>= fun z =>
                (simulateQ tracked (cont z.1)).run z.2] := by
            refine probEvent_congr' (fun z _ => ?_) rfl
            cases z.2.2 <;> simp
          _ ≤ 0 + (q : ℝ≥0∞) * δ := hunion
          _ = (q : ℝ≥0∞) * δ := zero_add _

end Reduction.Internal

/-- Correctness of Opp-UniKEM-CKA from stepwise premises: if one `SendB`
step introduces inconsistent current-epoch KEM material with probability at
most `δ` and no other oracle can, then an adversary making at most `q`
`SendB` queries makes the correctness experiment fail with probability at
most `q * δ`.  Receive queries, including delayed, reordered, duplicated,
and replayed deliveries, are not counted. -/
-- ANCHOR: correctnessFailureLe
theorem correctness_failure_le_of_sendBFailureBound [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (δ : ℝ≥0∞)
    (hSend : SendBFailureBound kem onoff hDet ecEk ecCt0 ecCt1 leak δ)
    (hFree : NonSendBPreservesCurrent kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (hq : SendBQueryBound adv q) :
    Pr[= false |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] ≤
      (q : ℝ≥0∞) * δ
-- ANCHOR_END: correctnessFailureLe
    := by
  let tracked := trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  let s₀ := initialGame (Sym := Sym) kem onoff
  have hpres : QueryImpl.PreservesInv tracked Inv :=
    trackedCorrectnessImpl_preserves kem onoff hDet ecEk hEkCorrect hEkPos
      ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak
  have hinit : Inv (s₀, false) := by
    right
    refine ⟨?_, ?_⟩
    · simpa [s₀, initialGame, initialA, initialB] using
        reachableInv_init kem onoff ecEk ecCt0 ecCt1 hEkPos hCt0Pos
    · simp [currentKEMFailure, s₀, initialGame, initialA, initialB,
        SCKAScheme.initGameState]
  have hmono :
      Pr[fun z => z.2.1.correct = false |
          (simulateQ tracked adv).run (s₀, false)] ≤
        Pr[fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] := by
    refine probEvent_mono ?_
    intro z hz hincorrect
    have hzInv : Inv z.2 :=
      OracleComp.simulateQ_run_preservesInv tracked Inv hpres adv
        (s₀, false) hinit z hz
    rcases hzInv with hbad | ⟨hreach, _hcurrent⟩
    · exact hbad
    · rcases hreach with ⟨_T, hConsistent⟩
      simp [hConsistent.correct] at hincorrect
  have hbad :
      Pr[fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] ≤
        (q : ℝ≥0∞) * δ := by
    exact tracked_bad_probability_le kem onoff hDet ecEk hEkCorrect hEkPos
      ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak δ
      hSend hFree adv hq (s₀, false) hinit rfl
  calc
    Pr[= false |
        SCKAScheme.correctnessExp
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] =
        Pr[fun z => z.2.1.correct = false |
          (simulateQ tracked adv).run (s₀, false)] := by
      rw [correctnessExp_eq_final_map]
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      have hproject := tracked_run_project kem onoff hDet ecEk ecCt0 ecCt1
        leak adv (s₀, false)
      rw [← hproject, probEvent_map]
      congr 1
    _ ≤ Pr[fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] := hmono
    _ ≤ (q : ℝ≥0∞) * δ := hbad

end oppUniKemCKA
