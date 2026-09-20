import SecureMessaging.SCKA.MLKEMBraid.Correctness.Provenance
import ToVCVio.OracleComp.ExpectedPayoff
import VCVio.EvalDist.Defs.NeverFails

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec
open ENNReal

namespace MLKEMBraid

noncomputable def componentFailureRisk
    (P : Parameters ProbComp) [DecidableEq P.K]
    (hdr : P.inc.PKheader) (vec : P.inc.PKvector) (sk : P.SK) : ℝ≥0∞ :=
  expectedPayoff (P.inc.encaps1 hdr)
    (fun c =>
      if P.hDet.decapsDet sk
          (P.inc.splitC.symm
            (c.2.1, P.hEnc2.encaps2Det c.1 hdr vec)) = some c.2.2
      then 0 else 1)

def derivedKeyFailure
    (P : Parameters ProbComp) [DecidableEq P.EpochKey]
    (e : ℕ) (sk : P.SK) (ct1 : P.inc.C₁) (ct2 : P.inc.C₂)
    (key : P.EpochKey) : ℝ≥0∞ :=
  if (P.hDet.decapsDet sk (P.inc.splitC.symm (ct1, ct2))).map
      (fun k => P.kdfOK k e) = some key
  then 0 else 1

noncomputable def currentFailurePotential
    (P : Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey] {AuthState : Type}
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym)) : ℝ≥0∞ :=
  let gen := if s.stA.controlPosition.1 then s.stA else s.stB
  let encap := if s.stA.controlPosition.1 then s.stB else s.stA
  let keys := if s.stA.controlPosition.1 then s.keyB else s.keyA
  if gen.epoch ≠ encap.epoch then 0 else
    let test := fun sk ct1 ct2 =>
      match keys gen.epoch with
      | none => 0
      | some key => derivedKeyFailure P gen.epoch sk ct1 ct2 key
    match gen, encap with
    | .keysSampled _ _ sk vec enc, .noHeaderReceived .. =>
        componentFailureRisk P enc.payload.1 vec sk
    | .keysSampled _ _ sk vec enc, .headerReceived .. =>
        componentFailureRisk P enc.payload.1 vec sk
    | .keysSampled _ _ sk vec _, .ct1Sampled _ _ hdr st ct1 _ _ =>
        test sk ct1 (P.hEnc2.encaps2Det st hdr vec)
    | .headerSent _ _ sk _ enc, .ct1Sampled _ _ hdr st ct1 _ _ =>
        test sk ct1 (P.hEnc2.encaps2Det st hdr enc.payload)
    | .ct1Received _ _ sk _ enc, .ct1Sampled _ _ hdr st ct1 _ _ =>
        test sk ct1 (P.hEnc2.encaps2Det st hdr enc.payload)
    | .headerSent _ _ sk _ _, .ekReceivedCt1Sampled _ _ st ct1 hdr vec _ =>
        test sk ct1 (P.hEnc2.encaps2Det st hdr vec)
    | .ct1Received _ _ sk _ _, .ekReceivedCt1Sampled _ _ st ct1 hdr vec _ =>
        test sk ct1 (P.hEnc2.encaps2Det st hdr vec)
    | .ct1Received _ _ sk _ enc, .ct1Acknowledged _ _ hdr st ct1 _ =>
        test sk ct1 (P.hEnc2.encaps2Det st hdr enc.payload)
    | .ct1Received _ _ sk ct1 _, .ct2Sampled _ _ enc =>
        test sk ct1 enc.payload.1
    | .ekSentCt1Received _ _ sk ct1 _, .ct2Sampled _ _ enc =>
        test sk ct1 enc.payload.1
    | _, _ => 0

noncomputable def correctnessScore
    (P : Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey] {AuthState : Type}
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym)) : ℝ≥0∞ :=
  if s.correct then currentFailurePotential P s else 1

theorem componentFailureRisk_mean
    (P : Parameters ProbComp) [DecidableEq P.K] :
    expectedPayoff P.kem.keygen
        (fun kp => componentFailureRisk P
          (P.inc.toHeader kp.1) (P.inc.toVector kp.1) kp.2) =
      P.kem.correctnessError ProbCompRuntime.probComp := by
  rw [P.kem.correctnessError_eq_probOutput_false_add_probFailure]
  rw [← P.inc.correctExp_eq]
  change _ = Pr[= false | P.inc.CorrectExp] + Pr[⊥ | P.inc.CorrectExp]
  unfold KEMScheme.IncrementalStructure.CorrectExp
  rw [probOutput_false_add_probFailure_bind]
  unfold componentFailureRisk expectedPayoff
  congr 1
  refine tsum_congr fun kp => ?_
  congr 1
  unfold KEMScheme.IncrementalStructure.stagedEncaps
  simp only [P.hEnc2.encaps2_eq, P.hDet.decaps_eq, bind_assoc, pure_bind]
  rw [probOutput_false_add_probFailure_bind]
  congr 1
  refine tsum_congr fun c : P.inc.St × P.inc.C₁ × P.K => ?_
  congr 1
  split_ifs <;> simp_all

end MLKEMBraid
