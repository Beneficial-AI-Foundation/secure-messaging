/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Challenge.Model.Counts
import SecureMessaging.CKA.FromLWE.Frodo2016.Challenge.ExperimentLaw

/-!
# Exact challenge entry-noise law

This unit rearranges the independent samples in the challenge experiment and
proves the exact distribution of its integer entry noise.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace lweCKA.ChallengeCertificateModel

open ChallengeModelInternal

set_option Elab.async false in
section

private def entryNoiseIntExpAux (n : Nat) : ProbComp ℤ := do
  let s0 ← ProbComp.sampleIID n d1IntSampler
  let e0 ← ProbComp.sampleIID n d1IntSampler
  let s1 ← ProbComp.sampleIID n d1IntSampler
  let e1 ← ProbComp.sampleIID n d1IntSampler
  let extra ← d1IntSampler
  return (∑ k : Fin n, s1 k * e0 k) -
    (∑ k : Fin n, e1 k * s0 k) + extra

private theorem evalDist_bind_move_after_two
    {A B C D : Type} (ma : ProbComp A) (mb : ProbComp B) (mc : ProbComp C)
    (f : A → B → C → ProbComp D) :
    finiteLaw (do
      let a ← ma
      let b ← mb
      let c ← mc
      f a b c) =
    finiteLaw (do
      let b ← mb
      let c ← mc
      let a ← ma
      f a b c) := by
  calc
    _ = finiteLaw (do
          let b ← mb
          let a ← ma
          let c ← mc
          f a b c) := evalDist_bind_bind_swap ma mb _
    _ = _ := evalDist_bind_congr' mb fun b =>
      evalDist_bind_bind_swap ma mc (fun a c => f a b c)

private theorem evalDist_bind_move_after_three
    {A B C D E : Type} (ma : ProbComp A) (mb : ProbComp B) (mc : ProbComp C)
    (md : ProbComp D) (f : A → B → C → D → ProbComp E) :
    finiteLaw (do
      let a ← ma
      let b ← mb
      let c ← mc
      let d ← md
      f a b c d) =
    finiteLaw (do
      let b ← mb
      let c ← mc
      let d ← md
      let a ← ma
      f a b c d) := by
  calc
    _ = finiteLaw (do
          let b ← mb
          let a ← ma
          let c ← mc
          let d ← md
          f a b c d) := evalDist_bind_bind_swap ma mb _
    _ = _ := evalDist_bind_congr' mb fun b =>
      evalDist_bind_move_after_two ma mc md (fun a c d => f a b c d)

private theorem evalDist_bind_move_after_four
    {A B C D E F : Type} (ma : ProbComp A) (mb : ProbComp B) (mc : ProbComp C)
    (md : ProbComp D) (me : ProbComp E)
    (f : A → B → C → D → E → ProbComp F) :
    finiteLaw (do
      let a ← ma
      let b ← mb
      let c ← mc
      let d ← md
      let e ← me
      f a b c d e) =
    finiteLaw (do
      let b ← mb
      let c ← mc
      let d ← md
      let e ← me
      let a ← ma
      f a b c d e) := by
  calc
    _ = finiteLaw (do
          let b ← mb
          let a ← ma
          let c ← mc
          let d ← md
          let e ← me
          f a b c d e) := evalDist_bind_bind_swap ma mb _
    _ = _ := evalDist_bind_congr' mb fun b =>
      evalDist_bind_move_after_three ma mc md me (fun a c d e => f a b c d e)

private theorem evalDist_bind_rotate_four_heads
    {H0 T0 H1 T1 H2 T2 H3 T3 X R : Type}
    (h0 : ProbComp H0) (t0 : ProbComp T0) (h1 : ProbComp H1) (t1 : ProbComp T1)
    (h2 : ProbComp H2) (t2 : ProbComp T2) (h3 : ProbComp H3) (t3 : ProbComp T3)
    (mx : ProbComp X)
    (f : H0 → T0 → H1 → T1 → H2 → T2 → H3 → T3 → X → ProbComp R) :
    finiteLaw (do
      let a0 ← h0
      let b0 ← t0
      let a1 ← h1
      let b1 ← t1
      let a2 ← h2
      let b2 ← t2
      let a3 ← h3
      let b3 ← t3
      let x ← mx
      f a0 b0 a1 b1 a2 b2 a3 b3 x) =
    finiteLaw (do
      let b0 ← t0
      let b1 ← t1
      let b2 ← t2
      let b3 ← t3
      let x ← mx
      let a0 ← h0
      let a1 ← h1
      let a2 ← h2
      let a3 ← h3
      f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
  calc
    _ = finiteLaw (do
          let b0 ← t0
          let a0 ← h0
          let a1 ← h1
          let b1 ← t1
          let a2 ← h2
          let b2 ← t2
          let a3 ← h3
          let b3 ← t3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := evalDist_bind_bind_swap h0 t0 _
    _ = finiteLaw (do
          let b0 ← t0
          let b1 ← t1
          let a0 ← h0
          let a1 ← h1
          let a2 ← h2
          let b2 ← t2
          let a3 ← h3
          let b3 ← t3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
        refine evalDist_bind_congr' t0 fun b0 => ?_
        exact (evalDist_bind_move_after_two t1 h0 h1
          (fun b1 a0 a1 => do
            let a2 ← h2
            let b2 ← t2
            let a3 ← h3
            let b3 ← t3
            let x ← mx
            f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm
    _ = finiteLaw (do
          let b0 ← t0
          let b1 ← t1
          let b2 ← t2
          let a0 ← h0
          let a1 ← h1
          let a2 ← h2
          let a3 ← h3
          let b3 ← t3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
        refine evalDist_bind_congr' t0 fun b0 => ?_
        refine evalDist_bind_congr' t1 fun b1 => ?_
        exact (evalDist_bind_move_after_three t2 h0 h1 h2
          (fun b2 a0 a1 a2 => do
            let a3 ← h3
            let b3 ← t3
            let x ← mx
            f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm
    _ = finiteLaw (do
          let b0 ← t0
          let b1 ← t1
          let b2 ← t2
          let b3 ← t3
          let a0 ← h0
          let a1 ← h1
          let a2 ← h2
          let a3 ← h3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
        refine evalDist_bind_congr' t0 fun b0 => ?_
        refine evalDist_bind_congr' t1 fun b1 => ?_
        refine evalDist_bind_congr' t2 fun b2 => ?_
        exact (evalDist_bind_move_after_four t3 h0 h1 h2 h3
          (fun b3 a0 a1 a2 a3 => do
            let x ← mx
            f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm
    _ = _ := by
        refine evalDist_bind_congr' t0 fun b0 => ?_
        refine evalDist_bind_congr' t1 fun b1 => ?_
        refine evalDist_bind_congr' t2 fun b2 => ?_
        refine evalDist_bind_congr' t3 fun b3 => ?_
        exact (evalDist_bind_move_after_four mx h0 h1 h2 h3
          (fun x a0 a1 a2 a3 => f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm

private theorem evalDist_entryNoiseIntExpAux_succ (n : Nat) :
    finiteLaw (entryNoiseIntExpAux (n + 1)) =
      finiteLaw (do
        let rest ← entryNoiseIntExpAux n
        let step ← d1DifferenceBlock
        return rest + step) := by
  let tail : ProbComp (Fin n → ℤ) := Fin.mOfFn n fun _ => d1IntSampler
  let finish (s0 : ℤ) (s0s : Fin n → ℤ) (e0 : ℤ) (e0s : Fin n → ℤ)
      (s1 : ℤ) (s1s : Fin n → ℤ) (e1 : ℤ) (e1s : Fin n → ℤ)
      (extra : ℤ) : ProbComp ℤ :=
    pure ((∑ k, Fin.cons s1 s1s k * Fin.cons e0 e0s k) -
      (∑ k, Fin.cons e1 e1s k * Fin.cons s0 s0s k) + extra)
  simp only [entryNoiseIntExpAux, d1DifferenceBlock, ProbComp.sampleIID,
    Fin.mOfFn, bind_assoc, pure_bind]
  change finiteLaw (do
      let s0 ← d1IntSampler
      let s0s ← tail
      let e0 ← d1IntSampler
      let e0s ← tail
      let s1 ← d1IntSampler
      let s1s ← tail
      let e1 ← d1IntSampler
      let e1s ← tail
      let extra ← d1IntSampler
      finish s0 s0s e0 e0s s1 s1s e1 e1s extra) = _
  calc
    _ = finiteLaw (do
          let s0s ← tail
          let e0s ← tail
          let s1s ← tail
          let e1s ← tail
          let extra ← d1IntSampler
          let s0 ← d1IntSampler
          let e0 ← d1IntSampler
          let s1 ← d1IntSampler
          let e1 ← d1IntSampler
          finish s0 s0s e0 e0s s1 s1s e1 e1s extra) :=
        evalDist_bind_rotate_four_heads
          d1IntSampler tail d1IntSampler tail d1IntSampler tail
          d1IntSampler tail d1IntSampler finish
    _ = _ := by
        refine evalDist_bind_congr' tail fun s0s => ?_
        refine evalDist_bind_congr' tail fun e0s => ?_
        refine evalDist_bind_congr' tail fun s1s => ?_
        refine evalDist_bind_congr' tail fun e1s => ?_
        refine evalDist_bind_congr' d1IntSampler fun extra => ?_
        refine evalDist_bind_congr' d1IntSampler fun s0 => ?_
        refine evalDist_bind_congr' d1IntSampler fun e0 => ?_
        refine evalDist_bind_congr' d1IntSampler fun s1 => ?_
        refine evalDist_bind_congr' d1IntSampler fun e1 => ?_
        simp only [finish, evalDist_pure]
        congr 1
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        ring

private theorem probOutput_entryNoiseIntExpAux (n : Nat) (z : ℤ) :
    Pr{let x ← entryNoiseIntExpAux n}[x = z] =
      (((productCounts ^ (2 * n)) * d1Counts) z : ℝ≥0∞) /
        256 ^ (4 * n + 1) := by
  induction n generalizing z with
  | zero =>
      simp [entryNoiseIntExpAux, ProbComp.sampleIID, Fin.mOfFn,
        probOutput_d1IntSampler, d1Counts_apply]
  | succ n ih =>
      rw [(evalDist_ext_iff.mp (evalDist_entryNoiseIntExpAux_succ n)) z]
      rw [show (do
          let rest ← entryNoiseIntExpAux n
          let step ← d1DifferenceBlock
          return rest + step) =
          (fun x y : ℤ => x + y) <$> entryNoiseIntExpAux n <*>
            d1DifferenceBlock by
        simp only [map_eq_bind_pure_comp, seq_eq_bind_map,
          Function.comp_def, bind_assoc, pure_bind]]
      have ihNat (u : ℤ) :
          Pr{let x ← entryNoiseIntExpAux n}[x = u] =
            (((productCounts ^ (2 * n)) * d1Counts) u : ℝ≥0∞) /
              ((256 ^ (4 * n + 1) : Nat) : ℝ≥0∞) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using ih u
      have hstepNat (u : ℤ) :
          Pr{let x ← d1DifferenceBlock}[x = u] =
            ((productCounts ^ 2) u : ℝ≥0∞) /
              ((65536 ^ 2 : Nat) : ℝ≥0∞) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          probOutput_d1DifferenceBlock u
      calc
        _ = (((productCounts ^ (2 * n) * d1Counts) * productCounts ^ 2) z :
              ℝ≥0∞) /
            (((256 ^ (4 * n + 1)) * 65536 ^ 2 : Nat) : ℝ≥0∞) := by
          simpa only [Nat.cast_mul] using probOutput_add_counts
            (entryNoiseIntExpAux n) d1DifferenceBlock
            (productCounts ^ (2 * n) * d1Counts) (productCounts ^ 2)
            (256 ^ (4 * n + 1)) (65536 ^ 2) ihNat hstepNat z
        _ = (((productCounts ^ (2 * (n + 1))) * d1Counts) z : ℝ≥0∞) /
            256 ^ (4 * (n + 1) + 1) := by
          have hmeasure :
              (productCounts ^ (2 * n) * d1Counts) * productCounts ^ 2 =
                productCounts ^ (2 * (n + 1)) * d1Counts := by
            rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
            ring
          rw [hmeasure]
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          have hden :
              (256 : ℝ≥0∞) ^ (4 * n + 1) * 65536 ^ 2 =
                256 ^ (4 * (n + 1) + 1) := by
            rw [show (65536 : ℝ≥0∞) = 256 ^ 2 by norm_num,
              ← pow_mul, ← pow_add]
            congr 1
          rw [hden]

private theorem challengeEntryNoiseIntExp_eq_aux :
    challengeEntryNoiseIntExp = entryNoiseIntExpAux 352 := by
  rfl

theorem ChallengeModelInternal.probOutput_challengeEntryNoiseIntExp_counts (z : ℤ) :
    Pr{let x ← challengeEntryNoiseIntExp}[x = z] =
      (((productCounts ^ 704) * d1Counts) z : ℝ≥0∞) / 256 ^ 1409 := by
  rw [challengeEntryNoiseIntExp_eq_aux, probOutput_entryNoiseIntExpAux]


end

end lweCKA.ChallengeCertificateModel
