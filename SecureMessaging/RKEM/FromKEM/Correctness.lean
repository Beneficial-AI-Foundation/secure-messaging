/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.FromKEM.Construction
import ToVCVio.CryptoFoundations.KeyEncapMech
import ToVCVio.EvalDist.Monad.Basic

/-!
# RKEM from KEM — Correctness

This file proves `RKEMScheme.deltaCorrect` for the generic RKEM-from-KEM construction of
`SecureMessaging.RKEM.FromKEM.Construction`: if the underlying KEM is `δ`-correct, the
construction is `(δ, δ)`-correct in the sense of [TripleRatchet, Def. 5.3]. Perfect correctness
of the construction (`δ = 0`) is a corollary.
-/

open ToVCVio OracleSpec OracleComp ENNReal KEMScheme RKEMScheme

namespace kemRKEM

variable {K PK SK C : Type}

/-- `correctExpA` at the KEM-from-KEM scheme agrees on the shared key exactly as often as the
underlying KEM's own correctness experiment: the extra independent key pairs sampled along the
way (`A`'s own fresh pair, and the fresh pair generated inside `rencA`) don't affect the
comparison. Holds unconditionally, for any KEM (not just a correct one). -/
theorem probOutput_correctExpA_eq_probOutput_CorrectExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) :
    Pr[= true | RKEMScheme.correctExpA (scheme kem)] = Pr[= true | kem.CorrectExp] := by
  unfold RKEMScheme.correctExpA KEMScheme.CorrectExp
  simp only [scheme, rkeygen, renc, rdec, pure_bind, bind_assoc]
  refine probOutput_bind_of_const' kem.keygen fun _ _ => ?_
  refine probOutput_bind_congr fun p hks => ?_
  obtain ⟨ekB, dkB⟩ := p
  refine probOutput_bind_congr fun q hck => ?_
  obtain ⟨ct, key⟩ := q
  refine probOutput_bind_of_const' kem.keygen fun _ _ => ?_
  refine probOutput_bind_congr fun r _ => ?_
  rcases r with _ | key'
  · rfl
  · simp [eq_comm]

/-- Decapsulating an honestly-generated ciphertext fails no more often than the underlying KEM's
own correctness experiment returns `false`: whenever decapsulation returns `none`, it certainly
doesn't recover the encapsulated key. Holds unconditionally, for any KEM. -/
theorem probOutput_none_decaps_le_probOutput_false_CorrectExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) :
    Pr[= (none : Option K) |
        do let (pk, sk) ← kem.keygen; let (c, _k) ← kem.encaps pk; kem.decaps sk c] ≤
      Pr[= false | kem.CorrectExp] := by
  unfold KEMScheme.CorrectExp
  refine probOutput_bind_mono (mx := kem.keygen) fun p _ => ?_
  obtain ⟨pk, sk⟩ := p
  refine probOutput_bind_mono (mx := kem.encaps pk) fun q _ => ?_
  obtain ⟨c, k⟩ := q
  dsimp only
  conv_lhs => rw [← bind_pure (kem.decaps sk c)]
  refine probOutput_bind_mono (mx := kem.decaps sk c) fun r _ => ?_
  rcases r with _ | k'
  · simp
  · simp

/-- `ratchetRoundOutputA` has the same distribution as first running the underlying
"success chain" (`B`'s keys, encapsulation, decapsulation) to a raw result `r`, then generating
`A`'s fresh updated key pair independently and returning it wrapped in `r`'s success/failure. -/
private lemma evalDist_ratchetRoundOutputA_eq_prefixBind
    (kem : KEMScheme ProbComp K PK SK C) :
    (𝒟[RKEMScheme.ratchetRoundOutputA (scheme kem)] : SPMF (Option (PK × SK))) =
      𝒟[(do let (ekB, dkB) ← kem.keygen
            let (ct, _key) ← kem.encaps ekB
            let r ← kem.decaps dkB ct
            kem.keygen >>= fun (ekAHat, dkAHat) =>
              match r with
              | none => pure none
              | some _ => pure (some (ekAHat, dkAHat)) : ProbComp (Option (PK × SK)))] := by
  unfold RKEMScheme.ratchetRoundOutputA
  simp only [scheme, rkeygen, renc, rdec, pure_bind, bind_assoc]
  refine evalDist_ext fun y => ?_
  refine probOutput_bind_of_const' kem.keygen fun _ _ => ?_
  refine probOutput_bind_congr fun p _ => ?_
  obtain ⟨ekB, dkB⟩ := p
  refine probOutput_bind_congr fun q _ => ?_
  obtain ⟨ct, key⟩ := q
  rw [probOutput_bind_bind_swap]
  refine probOutput_bind_congr fun b _ => ?_
  rcases b with _ | k <;> rfl

/-- `tvDist`-level restatement of `evalDist_ratchetRoundOutputA_eq_prefixBind`, rewriting
`ratchetRoundOutputA` on the left of a total-variation distance against any fixed right-hand
computation `my`. -/
private lemma tvDist_ratchetRoundOutputA_eq_prefixBind
    (kem : KEMScheme ProbComp K PK SK C) (my : ProbComp (Option (PK × SK))) :
    tvDist (RKEMScheme.ratchetRoundOutputA (scheme kem)) my =
      tvDist (do let (ekB, dkB) ← kem.keygen
                 let (ct, _key) ← kem.encaps ekB
                 let r ← kem.decaps dkB ct
                 kem.keygen >>= fun (ekAHat, dkAHat) =>
                   match r with
                   | none => pure none
                   | some _ => pure (some (ekAHat, dkAHat)) : ProbComp (Option (PK × SK))) my := by
  unfold tvDist
  rw [evalDist_ratchetRoundOutputA_eq_prefixBind]

/-- Total-variation distance is unaffected by a trailing bind whose result is discarded: `mx`
never fails, so `mx >>= fun _ => my` has exactly the same distribution as `my`. -/
private lemma tvDist_bind_const_right {α β : Type} (mx' : ProbComp β) (mx : ProbComp α)
    (my : ProbComp β) :
    tvDist mx' (mx >>= fun _ => my) = tvDist mx' my := by
  unfold tvDist; rw [evalDist_ext (mx := mx >>= fun _ => my) (mx':= my) fun y => by simp]

/-- The distribution of `ratchetRoundOutputA` is within total-variation distance
`Pr[= false | kem.CorrectExp]` of sampling a fresh pair of keys directly: the two only differ
when the underlying decapsulation fails. Holds unconditionally, for any KEM. -/
theorem tvDist_ratchetRoundOutputA_le [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C) :
    ENNReal.ofReal (tvDist (RKEMScheme.ratchetRoundOutputA (scheme kem))
      (do let keys ← kem.keygen; pure (some keys) : ProbComp (Option (PK × SK)))) ≤
      Pr[= false | kem.CorrectExp] := by
  rw [tvDist_ratchetRoundOutputA_eq_prefixBind,
    ← tvDist_bind_const_right _
      (do let (ekB, dkB) ← kem.keygen; let (ct, _key) ← kem.encaps ekB; kem.decaps dkB ct :
        ProbComp (Option K))
      (do let keys ← kem.keygen; pure (some keys) : ProbComp (Option (PK × SK)))]
  dsimp only
  simp only [bind_assoc]
  have hbound := ofReal_tvDist_bind_left_event_le
    (do let x ← kem.keygen; let y ← kem.encaps x.1; kem.decaps x.2 y.1 : ProbComp (Option K))
    (fun r => kem.keygen >>= fun x =>
      match r with | none => pure none | some _ => pure (some (x.1, x.2)))
    (fun _ => (do let keys ← kem.keygen; pure (some keys) : ProbComp (Option (PK × SK))))
    (fun r => r = none)
    (fun r hr => by
      rcases r with _ | k
      · exact absurd rfl hr
      · rfl)
  simp only [bind_assoc] at hbound
  refine hbound.trans ?_
  rw [probEvent_eq_eq_probOutput]
  exact probOutput_none_decaps_le_probOutput_false_CorrectExp kem

/-- **Quantitative correctness** (Def. 5.3) of the RKEM-from-KEM construction: if the underlying
KEM is `δ`-correct, the construction is `(δ, δ)`-correct. -/
-- ANCHOR: deltaCorrect
theorem deltaCorrect [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (δ : ℝ≥0∞) (hkem : kem.deltaCorrect ProbCompRuntime.probComp δ) :
    RKEMScheme.deltaCorrect (scheme kem) ProbCompRuntime.probComp δ δ
-- ANCHOR_END: deltaCorrect
    := by
  have hdelta : Pr[= false | kem.CorrectExp] ≤ δ := by
    have heq : kem.correctnessError ProbCompRuntime.probComp =
        Pr[= false | kem.CorrectExp] + Pr[⊥ | kem.CorrectExp] :=
      correctnessError_eq_probOutput_false_add_probFailure kem ProbCompRuntime.probComp
    calc Pr[= false | kem.CorrectExp]
        ≤ Pr[= false | kem.CorrectExp] + Pr[⊥ | kem.CorrectExp] := le_self_add
      _ = kem.correctnessError ProbCompRuntime.probComp := heq.symm
      _ ≤ δ := hkem
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold RKEMScheme.correctnessErrorA
    change 1 - Pr[= true | RKEMScheme.correctExpA (scheme kem)] ≤ δ
    rw [probOutput_correctExpA_eq_probOutput_CorrectExp]
    exact hkem
  · unfold RKEMScheme.correctnessErrorB
    change 1 - Pr[= true | RKEMScheme.correctExpB (scheme kem)] ≤ δ
    rw [show (scheme kem).correctExpB = (scheme kem).correctExpA by rfl,
        probOutput_correctExpA_eq_probOutput_CorrectExp]
    exact hkem
  · unfold RKEMScheme.updateKeyDistErrorA
    change ‖SPMF.tvDist (𝒟[RKEMScheme.ratchetRoundOutputA (scheme kem)])
      (𝒟[(do let keys ← kem.keygen; pure (some keys) : ProbComp (Option (PK × SK)))])‖ₑ ≤ δ
    rw [Real.enorm_eq_ofReal (SPMF.tvDist_nonneg _ _)]
    exact (tvDist_ratchetRoundOutputA_le kem).trans hdelta
  · unfold RKEMScheme.updateKeyDistErrorB
    change ‖SPMF.tvDist (𝒟[RKEMScheme.ratchetRoundOutputB (scheme kem)])
      (𝒟[(do let keys ← kem.keygen; pure (some keys) : ProbComp (Option (PK × SK)))])‖ₑ ≤ δ
    rw [show (scheme kem).ratchetRoundOutputB = (scheme kem).ratchetRoundOutputA by rfl,
        Real.enorm_eq_ofReal (SPMF.tvDist_nonneg _ _)]
    exact (tvDist_ratchetRoundOutputA_le kem).trans hdelta

/-- **Perfect correctness** of the RKEM-from-KEM construction, as the `δ = 0` special case of
`deltaCorrect`: if the underlying KEM is perfectly correct, so is the construction. -/
theorem deltaCorrect_of_perfectlyCorrect [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp) :
    RKEMScheme.deltaCorrect (scheme kem) ProbCompRuntime.probComp 0 0 :=
  deltaCorrect kem 0
    ((correctnessError_eq_zero_iff_perfectlyCorrect kem ProbCompRuntime.probComp).mpr hkem).le

end kemRKEM
