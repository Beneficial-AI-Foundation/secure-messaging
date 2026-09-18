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
decapsulation is total (`KEMScheme.TotalDecaps`), the construction is `(δ, δ)`-correct in the
sense of [TripleRatchet, Def. 5.3]. Perfect correctness of the construction (`δ = 0`) is a
corollary.

Totality of decapsulation makes the second half of Def. 5.3 — closeness of the ratcheted key
distribution to sampling directly — hold with error *exactly* zero, for any KEM, whether or not
it is correct: `ratchetRoundOutputA` returns the very key pair `rencA` samples internally, and
decapsulation's (always-defined) output is otherwise fully discarded
(`evalDist_ratchetRoundOutputA_eq_evalDist_keygen`). So the underlying KEM's own perfect
correctness is never needed for this half; it only matters, as before, for the `K = K'` half.
-/

open ToVCVio OracleSpec OracleComp ENNReal KEMScheme RKEMScheme

namespace kemRKEM

variable {K PK SK C : Type}

/-- `correctExpA` at the KEM-from-KEM scheme agrees on the shared key exactly as often as the
underlying KEM's own correctness experiment: the extra independent key pairs sampled along the
way (`A`'s own fresh pair, and the fresh pair generated inside `rencA`) don't affect the
comparison. Holds unconditionally, for any KEM (not just a correct one). -/
theorem probOutput_correctExpA_eq_probOutput_CorrectExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem) :
    Pr[= true | RKEMScheme.correctExpA (scheme kem total)] = Pr[= true | kem.CorrectExp] := by
  unfold RKEMScheme.correctExpA KEMScheme.CorrectExp
  simp only [scheme, rkeygen, renc, rdec_eq_rdec', rdec', total.decaps_eq,
    map_eq_bind_pure_comp, Function.comp, pure_bind, bind_assoc]
  refine probOutput_bind_of_const' kem.keygen fun _ _ => ?_
  refine probOutput_bind_congr fun p _ => ?_
  obtain ⟨ekB, dkB⟩ := p
  refine probOutput_bind_congr fun q _ => ?_
  obtain ⟨ct, key⟩ := q
  refine probOutput_bind_of_const' kem.keygen fun _ _ => ?_
  refine probOutput_bind_congr fun key' _ => ?_
  simp [eq_comm]

/-- `ratchetRoundOutputA` at the KEM-from-KEM scheme has exactly the same distribution as `A`'s
own fresh key generation: the pair it returns is literally the fresh key pair sampled inside
`rencA`, and decapsulation's output — always defined, thanks to `total` — is otherwise discarded.
Holds unconditionally, for any KEM (not just a correct one), which is why the construction's
update-key-distribution error is always exactly zero. -/
theorem evalDist_ratchetRoundOutputA_eq_evalDist_keygen
    (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem) :
    ProbCompRuntime.probComp.evalDist (RKEMScheme.ratchetRoundOutputA (scheme kem total)) =
      ProbCompRuntime.probComp.evalDist kem.keygen := by
  change (𝒟[RKEMScheme.ratchetRoundOutputA (scheme kem total)] : SPMF (PK × SK)) = 𝒟[kem.keygen]
  unfold RKEMScheme.ratchetRoundOutputA
  simp only [scheme, rkeygen, renc, rdec_eq_rdec', rdec', pure_bind, bind_assoc]
  refine evalDist_ext fun y => ?_
  refine probOutput_bind_of_const' kem.keygen fun _ _ => ?_
  refine probOutput_bind_of_const' kem.keygen fun p _ => ?_
  obtain ⟨ekB, dkB⟩ := p
  refine probOutput_bind_of_const' (kem.encaps ekB) fun q _ => ?_
  obtain ⟨ct, key⟩ := q
  rw [probOutput_bind_bind_swap]
  refine probOutput_bind_of_const' (total.decapsTotal dkB ct) fun _ _ => ?_
  simp

/-- **Quantitative correctness** (Def. 5.3) of the RKEM-from-KEM construction: if the underlying
KEM is `δ`-correct, the construction is `(δ, 0)`-correct — the update-key-distribution error is
exactly zero regardless of `δ`, by `evalDist_ratchetRoundOutputA_eq_evalDist_keygen`; only the
`K = K'` error inherits `δ` from the underlying KEM. -/
-- ANCHOR: deltaCorrect
theorem deltaCorrect [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (total : TotalDecaps kem) (δ : ℝ≥0∞) (hkem : kem.deltaCorrect ProbCompRuntime.probComp δ) :
    RKEMScheme.deltaCorrect (scheme kem total) ProbCompRuntime.probComp δ 0
-- ANCHOR_END: deltaCorrect
    := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold RKEMScheme.correctnessErrorA
    change 1 - Pr[= true | RKEMScheme.correctExpA (scheme kem total)] ≤ δ
    rw [probOutput_correctExpA_eq_probOutput_CorrectExp]
    exact hkem
  · unfold RKEMScheme.correctnessErrorB
    change 1 - Pr[= true | RKEMScheme.correctExpB (scheme kem total)] ≤ δ
    rw [show (scheme kem total).correctExpB = (scheme kem total).correctExpA by rfl,
        probOutput_correctExpA_eq_probOutput_CorrectExp]
    exact hkem
  · unfold RKEMScheme.updateKeyDistErrorA
    rw [show (scheme kem total).rsetup >>= (scheme kem total).rkeygenAUpdated = kem.keygen from by
      simp [scheme, rkeygen],
      evalDist_ratchetRoundOutputA_eq_evalDist_keygen, SPMF.tvDist_self]
    simp
  · unfold RKEMScheme.updateKeyDistErrorB
    rw [show (scheme kem total).ratchetRoundOutputB = (scheme kem total).ratchetRoundOutputA
        by rfl,
      show (scheme kem total).rsetup >>= (scheme kem total).rkeygenBUpdated = kem.keygen from by
      simp [scheme, rkeygen],
      evalDist_ratchetRoundOutputA_eq_evalDist_keygen, SPMF.tvDist_self]
    simp

/-- **Perfect correctness** of the RKEM-from-KEM construction, as the `δ = 0` special case of
`deltaCorrect`: if the underlying KEM is perfectly correct, so is the construction. -/
theorem deltaCorrect_of_perfectlyCorrect [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (total : TotalDecaps kem) (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    RKEMScheme.deltaCorrect (scheme kem total) ProbCompRuntime.probComp 0 0 :=
  deltaCorrect kem total 0
    ((correctnessError_eq_zero_iff_perfectlyCorrect kem ProbCompRuntime.probComp).mpr hkem).le

end kemRKEM
