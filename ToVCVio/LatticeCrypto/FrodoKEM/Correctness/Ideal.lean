import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Deterministic
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Sampling
import VCVio.EvalDist.ProbabilityBounds

/-! Honest decryption in the ideal model with independent uniform error streams.
No distributional claim about deterministic SHAKE expansion is made here. -/
namespace FrodoKEM.Ideal
open OracleComp LatticeCrypto ToVCVio
open scoped ENNReal
/-- The five integer error matrices used by ideal key generation and encryption. -/
structure NoiseSamples (ps : ParameterSet) where
  /-- Transposed secret matrix sampled during key generation. -/
  st : Matrix (Fin nbar) (Fin ps.params.n) ℤ
  /-- Error matrix added to the public-key matrix. -/
  e : Matrix (Fin ps.params.n) (Fin nbar) ℤ
  /-- Ephemeral secret matrix sampled during encryption. -/
  sp : Matrix (Fin mbar) (Fin ps.params.n) ℤ
  /-- Error matrix added to the first ciphertext component. -/
  ep : Matrix (Fin mbar) (Fin ps.params.n) ℤ
  /-- Error matrix added to the second ciphertext component. -/
  epp : Matrix (Fin mbar) (Fin nbar) ℤ

/-- Sample all five error matrices from independent uniform bit streams. -/
def sampleNoise (ps : ParameterSet) : ProbComp (NoiseSamples ps) := do
  let rst ← $ᵗ (Bits (nbar * ps.params.n * lenChi))
  let re ← $ᵗ (Bits (ps.params.n * nbar * lenChi))
  let rsp ← $ᵗ (Bits (mbar * ps.params.n * lenChi))
  let rep ← $ᵗ (Bits (mbar * ps.params.n * lenChi))
  let repp ← $ᵗ (Bits (mbar * nbar * lenChi))
  return {
    st := SampleMatrix ps.errorTable nbar ps.params.n rst
    e := SampleMatrix ps.errorTable ps.params.n nbar re
    sp := SampleMatrix ps.errorTable mbar ps.params.n rsp
    ep := SampleMatrix ps.errorTable mbar ps.params.n rep
    epp := SampleMatrix ps.errorTable mbar nbar repp
  }

/-- Integer decryption residual `S′ E + E″ - E′ S` before reduction modulo `q`. -/
def residual {ps : ParameterSet} (t : NoiseSamples ps) :
    Matrix (Fin mbar) (Fin nbar) ℤ :=
  t.sp * t.e + t.epp - t.ep * t.st.transpose

/-- Reduce the ideal transposed secret matrix modulo the scheme modulus. -/
def secretTranspose {ps : ParameterSet} (t : NoiseSamples ps) :
    PKESecretKey ps :=
  t.st.map (fun z : ℤ => (z : ZMod ps.params.q))

/-- Construct an ideal PKE ciphertext from a fixed public matrix, message, and error matrices. -/
def ciphertext {ps : ParameterSet}
    (A : FrodoMatrix ps.params ps.params.n ps.params.n)
    (message : MessageBits ps) (t : NoiseSamples ps) :
    PKECiphertext ps :=
  let st := secretTranspose t
  let e := t.e.map (fun z : ℤ => (z : ZMod ps.params.q))
  let sp := t.sp.map (fun z : ℤ => (z : ZMod ps.params.q))
  let ep := t.ep.map (fun z : ℤ => (z : ZMod ps.params.q))
  let epp := t.epp.map (fun z : ℤ => (z : ZMod ps.params.q))
  let b := A * st.transpose + e
  {
    c1 := sp * A + ep
    c2 := sp * b + epp +
      Encode ps.params (message.cast (messageBits_length ps))
  }

/-- Integer half-width of the sufficient decoding interval. -/
def threshold (ps : ParameterSet) : ℕ :=
  ps.params.q / 2 ^ (ps.params.B + 1)

/-- An integer residual entry lies outside the decoding interval `[-threshold, threshold)`. -/
def entryBad (ps : ParameterSet) (z : ℤ) : Prop :=
  z < -(threshold ps : ℤ) ∨ (threshold ps : ℤ) ≤ z

private instance (ps : ParameterSet) : DecidablePred (entryBad ps) :=
  fun z => inferInstanceAs (Decidable (z < -(threshold ps : ℤ) ∨ (threshold ps : ℤ) ≤ z))

/-- Sample one integer residual entry as two independent product sums and one extra error. -/
def entryNoiseExp (ps : ParameterSet) : ProbComp ℤ := do
  let s0 ← ProbComp.sampleIID ps.params.n (sampleError ps)
  let e0 ← ProbComp.sampleIID ps.params.n (sampleError ps)
  let s1 ← ProbComp.sampleIID ps.params.n (sampleError ps)
  let e1 ← ProbComp.sampleIID ps.params.n (sampleError ps)
  let extra ← sampleError ps
  return (∑ k, s1 k * e0 k) - (∑ k, e1 k * s0 k) + extra

/-- Probability that the ideal integer residual entry lies outside its decoding interval. -/
noncomputable def entryFailureProb (ps : ParameterSet) : ℝ≥0∞ :=
  Pr{let z ← entryNoiseExp ps}[entryBad ps z]

/-- Probability that the ideal modular residual violates the matrix noise bound. -/
noncomputable def noiseBadProb (ps : ParameterSet) : ℝ≥0∞ :=
  Pr{let t ← sampleNoise ps}[
    ¬ NoiseBound ps.params
      ((residual t).map (fun z : ℤ => (z : ZMod ps.params.q)))]

/-- Ideal PKE decryption failure probability for a fixed public matrix and message. -/
noncomputable def pkeFailureProb (ps : ParameterSet)
    (A : FrodoMatrix ps.params ps.params.n ps.params.n)
    (message : MessageBits ps) : ℝ≥0∞ :=
  Pr{let t ← sampleNoise ps}[
    PKE.decrypt (secretTranspose t) (ciphertext A message t) ≠ message]


theorem decryptionMatrix_eq {ps : ParameterSet}
    (A : FrodoMatrix ps.params ps.params.n ps.params.n)
    (message : MessageBits ps) (t : NoiseSamples ps) :
    (ciphertext A message t).c2 -
        (ciphertext A message t).c1 * (secretTranspose t).transpose =
      Encode ps.params (message.cast (messageBits_length ps)) +
        (residual t).map (fun z : ℤ => (z : ZMod ps.params.q)) := by
  have hmap : (residual t).map (fun z : ℤ => (z : ZMod ps.params.q)) =
      t.sp.map (fun z : ℤ => (z : ZMod ps.params.q)) *
        t.e.map (fun z : ℤ => (z : ZMod ps.params.q)) +
      t.epp.map (fun z : ℤ => (z : ZMod ps.params.q)) -
      t.ep.map (fun z : ℤ => (z : ZMod ps.params.q)) * (secretTranspose t).transpose := by
    ext i j
    simp [residual, secretTranspose, Matrix.mul_apply, Matrix.map_apply,
      Matrix.transpose_apply, Int.cast_sum, Int.cast_add, Int.cast_sub, Int.cast_mul]
  rw [hmap]
  dsimp only [ciphertext]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

theorem decrypt_eq_of_noiseBound {ps : ParameterSet}
    (A : FrodoMatrix ps.params ps.params.n ps.params.n)
    (message : MessageBits ps) (t : NoiseSamples ps)
    (hnoise : NoiseBound ps.params
      ((residual t).map (fun z : ℤ => (z : ZMod ps.params.q)))) :
    PKE.decrypt (secretTranspose t) (ciphertext A message t) = message := by
  rw [PKE.decrypt, decryptionMatrix_eq]
  rw [Decode_Encode_add ps.params ps.params_wellFormed _ _ hnoise.1 hnoise.2]
  simp

private theorem centered_bound_of_not_entryBad (ps : ParameterSet) (z : ℤ)
    (hz : ¬ entryBad ps z) :
    -(ps.params.q : ℤ) ≤ 2 ^ (ps.params.B + 1) * centeredRepr (z : ZMod ps.params.q) ∧
      2 ^ (ps.params.B + 1) * centeredRepr (z : ZMod ps.params.q) < (ps.params.q : ℤ) := by
  have hzlo : -(threshold ps : ℤ) ≤ z := by simp only [entryBad, not_or, not_lt] at hz; exact hz.1
  have hzhi : z < (threshold ps : ℤ) := by simp only [entryBad, not_or, not_le] at hz; exact hz.2
  have hsmall : 2 * threshold ps < ps.params.q := by cases ps <;> decide
  have : NeZero ps.params.q := ⟨by rw [ps.params_wellFormed.q_eq]; positivity⟩
  have hcast := centeredRepr_intCast_eq_of_natAbs_le z
    (show z.natAbs ≤ threshold ps by omega) hsmall
  rw [hcast]
  have hscale : (2 : ℤ) ^ (ps.params.B + 1) * (threshold ps : ℤ) = (ps.params.q : ℤ) := by
    cases ps <;> decide
  have hpos : (0 : ℤ) < 2 ^ (ps.params.B + 1) := by positivity
  constructor <;> nlinarith

private theorem noiseBound_of_good_entries (ps : ParameterSet) (t : NoiseSamples ps)
    (h : ∀ i j, ¬ entryBad ps (residual t i j)) :
    NoiseBound ps.params ((residual t).map (fun z : ℤ => (z : ZMod ps.params.q))) := by
  constructor
  · intro i j; exact (centered_bound_of_not_entryBad ps _ (h i j)).1
  · intro i j; exact (centered_bound_of_not_entryBad ps _ (h i j)).2


private theorem finiteLaw_bind_head {α β : Type} {mx my : ProbComp α}
    (h : finiteLaw mx = finiteLaw my) (k : α → ProbComp β) :
    finiteLaw (mx >>= k) = finiteLaw (my >>= k) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact ((EvalDistEq.of_evalDist_eq h).bind (fun _ => EvalDistEq.refl _)).evalDist_eq

theorem finiteLaw_residual_entry (ps : ParameterSet)
    (i : Fin mbar) (j : Fin nbar) :
    finiteLaw ((fun t => residual t i j) <$> sampleNoise ps) =
      finiteLaw (entryNoiseExp ps) := by
  let projected : ProbComp ℤ := do
    let s0 ← (fun M => M j) <$>
      (SampleMatrix ps.errorTable nbar ps.params.n <$>
        ($ᵗ (Bits (nbar * ps.params.n * lenChi))))
    let e0 ← (fun M => fun k => M k j) <$>
      (SampleMatrix ps.errorTable ps.params.n nbar <$>
        ($ᵗ (Bits (ps.params.n * nbar * lenChi))))
    let s1 ← (fun M => M i) <$>
      (SampleMatrix ps.errorTable mbar ps.params.n <$>
        ($ᵗ (Bits (mbar * ps.params.n * lenChi))))
    let e1 ← (fun M => M i) <$>
      (SampleMatrix ps.errorTable mbar ps.params.n <$>
        ($ᵗ (Bits (mbar * ps.params.n * lenChi))))
    let extra ← (fun M => M i j) <$>
      (SampleMatrix ps.errorTable mbar nbar <$>
        ($ᵗ (Bits (mbar * nbar * lenChi))))
    return (∑ k, s1 k * e0 k) - (∑ k, e1 k * s0 k) + extra
  have hProjected : finiteLaw ((fun t => residual t i j) <$> sampleNoise ps) =
      finiteLaw projected := by
    simp only [sampleNoise, projected, residual, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.mul_apply, Matrix.transpose_apply]
    refine finiteLaw_bind_congr _ fun _ => ?_
    refine finiteLaw_bind_congr _ fun _ => ?_
    refine finiteLaw_bind_congr _ fun _ => ?_
    refine finiteLaw_bind_congr _ fun _ => ?_
    refine finiteLaw_bind_congr _ fun _ => ?_
    congr 2
    ring
  have hrow (rows cols : ℕ) (r : Fin rows) :
      finiteLaw ((fun M => M r) <$>
        (SampleMatrix ps.errorTable rows cols <$>
          ($ᵗ (Bits (rows * cols * lenChi))))) =
      finiteLaw (ProbComp.sampleIID cols (sampleError ps)) :=
    (finiteLaw_map_congr (finiteLaw_SampleMatrix ps rows cols) _).trans
      (finiteLaw_sampleMatrix_row rows cols (sampleError ps) (prFail_sampleError ps) r)
  have hcol (rows cols : ℕ) (r : Fin cols) :
      finiteLaw ((fun M => fun k => M k r) <$>
        (SampleMatrix ps.errorTable rows cols <$>
          ($ᵗ (Bits (rows * cols * lenChi))))) =
      finiteLaw (ProbComp.sampleIID rows (sampleError ps)) :=
    (finiteLaw_map_congr (finiteLaw_SampleMatrix ps rows cols) _).trans
      (finiteLaw_sampleMatrix_col rows cols (sampleError ps) (prFail_sampleError ps) r)
  have hentry :
      finiteLaw ((fun M => M i j) <$>
        (SampleMatrix ps.errorTable mbar nbar <$>
          ($ᵗ (Bits (mbar * nbar * lenChi))))) = finiteLaw (sampleError ps) :=
    (finiteLaw_map_congr (finiteLaw_SampleMatrix ps mbar nbar) _).trans
      (finiteLaw_sampleMatrix_entry mbar nbar (sampleError ps) (prFail_sampleError ps) i j)
  apply hProjected.trans
  dsimp only [projected, entryNoiseExp]
  refine (finiteLaw_bind_head (hrow nbar ps.params.n j) _).trans ?_
  refine finiteLaw_bind_congr _ fun _ => ?_
  refine (finiteLaw_bind_head (hcol ps.params.n nbar j) _).trans ?_
  refine finiteLaw_bind_congr _ fun _ => ?_
  refine (finiteLaw_bind_head (hrow mbar ps.params.n i) _).trans ?_
  refine finiteLaw_bind_congr _ fun _ => ?_
  refine (finiteLaw_bind_head (hrow mbar ps.params.n i) _).trans ?_
  refine finiteLaw_bind_congr _ fun _ => ?_
  exact finiteLaw_bind_head hentry _

theorem noiseBadProb_le (ps : ParameterSet) :
    noiseBadProb ps ≤ 64 * entryFailureProb ps := by
  have hentry (ij : Fin mbar × Fin nbar) :
      Pr{let t ← sampleNoise ps}[entryBad ps (residual t ij.1 ij.2)] = entryFailureProb ps := by
    have h := finiteLaw_residual_entry ps ij.1 ij.2
    let : MeasurableSpace ℤ := ⊤
    have heq := (EvalDistEq.of_evalDist_eq h).prEvent_eq (entryBad ps)
    simpa only [prEvent_map, entryFailureProb] using heq
  have hcontain : noiseBadProb ps ≤
      Pr{let t ← sampleNoise ps}[∃ ij : Fin mbar × Fin nbar,
        entryBad ps (residual t ij.1 ij.2)] := by
    apply prEvent_mono
    intro t ht
    by_contra h
    apply ht
    apply noiseBound_of_good_entries ps t
    intro i j hb
    exact h ⟨(i,j),hb⟩
  apply hcontain.trans
  have h := prEvent_exists_le_card_mul (sampleNoise ps)
    (fun (ij : Fin mbar × Fin nbar) t => entryBad ps (residual t ij.1 ij.2))
    (fun ij => (hentry ij).le)
  have hc : Fintype.card (Fin mbar × Fin nbar) = 64 := by decide
  rw [hc] at h
  exact h

theorem pkeFailureProb_le_noiseBadProb (ps : ParameterSet)
    (A : FrodoMatrix ps.params ps.params.n ps.params.n)
    (message : MessageBits ps) :
    pkeFailureProb ps A message ≤ noiseBadProb ps := by
  apply prEvent_mono
  intro t hfail hnoise
  exact hfail (decrypt_eq_of_noiseBound A message t hnoise)

end FrodoKEM.Ideal
