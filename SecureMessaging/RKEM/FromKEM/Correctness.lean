/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.FromKEM.Construction
import ToVCVio.CryptoFoundations.KeyEncapMech
import ToVCVio.EvalDist.Monad.Basic
import ToVCVio.EvalDist.TVDist

/-!
# RKEM from KEM — Correctness

This file proves `RKEMScheme.deltaCorrect` for the generic RKEM-from-KEM construction of
`SecureMessaging.RKEM.FromKEM.Construction`: if the underlying KEM is `δ`-correct and its
decapsulation is total (`KEMScheme.TotalDecaps`), the construction is `(δ, 0)`-correct in the
sense of [TripleRatchet, Def. 5.3] — sharper than the `(δ, δ)` one would get by just reusing `δ`
for both halves. Perfect correctness of the construction (`δ = 0`) is a corollary.

The `(δ, 0)` split reflects a genuine asymmetry between the two halves of Def. 5.3. The second
half — closeness of the ratcheted key distribution to sampling directly — holds with error
*exactly* zero, for any KEM, whether or not it is correct: `ratchetRoundOutputA` returns the very
key pair `rencA` samples internally, and decapsulation's (always-defined) output is otherwise
fully discarded (`evalDistEq_ratchetRoundOutputA_keygen`). So the underlying KEM's own
correctness is never needed for this half, and the `0` cannot be improved to depend on `δ` in the
other direction either — it already is the tightest possible bound. The first half (`K = K'`) has
no such shortcut and genuinely inherits `δ` from the underlying KEM.
-/

open ToVCVio OracleSpec OracleComp ENNReal KEMScheme RKEMScheme

namespace kemRKEM

variable {K PK SK C : Type}

/-- `correctExpA` at the RKEM-from-KEM scheme has the same distribution as the underlying KEM's
own correctness experiment: the extra independent key pairs sampled along the way (`A`'s own fresh
pair, and the fresh pair generated inside `rencA`) don't affect the comparison. Holds
unconditionally, for any KEM (not just a correct one). -/
theorem evalDistEq_correctExpA_correctnessExperiment [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem) :
    RKEMScheme.correctExpA (scheme kem total) =ᵈ kem.correctnessExperiment := by
  unfold RKEMScheme.correctExpA KEMScheme.correctnessExperiment
  simp only [scheme, rkeygen, renc, rdec, total.decaps_eq,
    map_eq_bind_pure_comp, Function.comp, pure_bind, bind_assoc]
  refine (EvalDistEq.bind_const kem.keygen _).trans ?_
  refine EvalDistEq.bind_right kem.keygen fun p : PK × SK =>
    EvalDistEq.bind_right (kem.encaps p.1) fun q : C × K => ?_
  simp only [Option.some.injEq, eq_comm (a := q.2)]
  exact EvalDistEq.bind_const _ _

/-- `ratchetRoundOutputA` at the RKEM-from-KEM scheme has exactly the same distribution as `A`'s
own fresh key generation: the pair it returns is literally the fresh key pair sampled inside
`rencA`, and decapsulation's output — always defined, thanks to `total` — is otherwise discarded.
Holds unconditionally, for any KEM (not just a correct one), which is why the construction's
update-key-distribution error is always exactly zero. -/
theorem evalDistEq_ratchetRoundOutputA_keygen
    (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem) :
    RKEMScheme.ratchetRoundOutputA (scheme kem total) =ᵈ kem.keygen := by
  unfold RKEMScheme.ratchetRoundOutputA
  simp only [scheme, rkeygen, renc, rdec, pure_bind, bind_assoc, Prod.mk.eta]
  have hdrop (dk : SK) (ct : C) :
      (kem.keygen >>= fun b => total.decapsTotal dk ct >>= fun _ => pure b) =ᵈ kem.keygen := by
    conv_rhs => rw [← bind_pure kem.keygen]
    exact EvalDistEq.bind_right _ fun b => EvalDistEq.bind_const _ (pure b)
  refine (EvalDistEq.bind_const kem.keygen _).trans ?_
  refine (EvalDistEq.bind_right kem.keygen fun p : PK × SK =>
    EvalDistEq.bind_right (kem.encaps p.1) fun q : C × K => hdrop p.2 q.1).trans ?_
  refine (EvalDistEq.bind_right kem.keygen fun p : PK × SK =>
    EvalDistEq.bind_const (kem.encaps p.1) kem.keygen).trans ?_
  exact EvalDistEq.bind_const kem.keygen kem.keygen

/-- **Quantitative correctness** (Def. 5.3) of the RKEM-from-KEM construction: if the underlying
KEM is `δ`-correct, the construction is `(δ, 0)`-correct — the update-key-distribution error is
exactly zero regardless of `δ`, by `evalDistEq_ratchetRoundOutputA_keygen`; only the
`K = K'` error inherits `δ` from the underlying KEM. -/
-- ANCHOR: deltaCorrect
theorem deltaCorrect [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (total : TotalDecaps kem) (δ : ℝ≥0∞) (hkem : kem.deltaCorrect ProbCompRuntime.probComp δ) :
    RKEMScheme.deltaCorrect (scheme kem total) ProbCompRuntime.probComp δ 0
-- ANCHOR_END: deltaCorrect
    := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold RKEMScheme.correctnessErrorA
    rw [ProbCompRuntime.probComp_evalDist,
      (evalDistEq_correctExpA_correctnessExperiment kem total).evalDist_eq,
      ← ProbCompRuntime.probComp_evalDist]
    exact hkem
  · unfold RKEMScheme.correctnessErrorB
    rw [show (scheme kem total).correctExpB = (scheme kem total).correctExpA by rfl,
      ProbCompRuntime.probComp_evalDist,
      (evalDistEq_correctExpA_correctnessExperiment kem total).evalDist_eq,
      ← ProbCompRuntime.probComp_evalDist]
    exact hkem
  · unfold RKEMScheme.updateKeyDistErrorA
    let : MeasurableSpace (PK × SK) := ⊤
    rw [show (scheme kem total).rsetup >>= (scheme kem total).rkeygenAUpdated = kem.keygen from by
      simp [scheme, rkeygen], ProbCompRuntime.probComp_evalDist,
      ProbCompRuntime.probComp_evalDist,
      (evalDistEq_ratchetRoundOutputA_keygen kem total).evalDist_eq,
      MeasureTheory.Measure.etvDist_self]
  · unfold RKEMScheme.updateKeyDistErrorB
    let : MeasurableSpace (PK × SK) := ⊤
    rw [show (scheme kem total).ratchetRoundOutputB = (scheme kem total).ratchetRoundOutputA
        by rfl,
      show (scheme kem total).rsetup >>= (scheme kem total).rkeygenBUpdated = kem.keygen from by
      simp [scheme, rkeygen], ProbCompRuntime.probComp_evalDist,
      ProbCompRuntime.probComp_evalDist,
      (evalDistEq_ratchetRoundOutputA_keygen kem total).evalDist_eq,
      MeasureTheory.Measure.etvDist_self]

/-- **Perfect correctness** of the RKEM-from-KEM construction, as the `δ = 0` special case of
`deltaCorrect`: if the underlying KEM is perfectly correct, so is the construction. -/
theorem deltaCorrect_of_perfectlyCorrect [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (total : TotalDecaps kem) (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    RKEMScheme.deltaCorrect (scheme kem total) ProbCompRuntime.probComp 0 0 :=
  deltaCorrect kem total 0
    ((correctnessError_eq_zero_iff_perfectlyCorrect kem ProbCompRuntime.probComp).mpr hkem).le

end kemRKEM
