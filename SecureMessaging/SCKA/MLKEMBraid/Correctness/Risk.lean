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

theorem currentFailurePotential_eq_transcript
    (P : Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym))
    (hT : TranscriptConsistent P auth ik T s) :
    currentFailurePotential P s =
      if s.stA.epoch = s.stB.epoch then
        let e := s.stA.epoch
        match (T e).keypair, (T e).encaps1 with
        | none, _ => 0
        | some kp, none =>
            componentFailureRisk P
              (P.inc.toHeader kp.1) (P.inc.toVector kp.1) kp.2
        | some kp, some c =>
            derivedKeyFailure P e kp.2 c.2.1
              (P.hEnc2.encaps2Det c.1
                (P.inc.toHeader kp.1) (P.inc.toVector kp.1))
              (P.kdfOK c.2.2 e)
      else 0 := by
  rcases hT with ⟨_, hControl, hPair, _, _, _, hEncaps,
    hLocalA, hLocalB, _, hKeys⟩
  let localPotential := fun
      (gen encap : State P AuthState) (keys : ℕ → Option P.EpochKey) =>
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
  let transcriptPotential := fun e =>
    match (T e).keypair, (T e).encaps1 with
    | none, _ => 0
    | some kp, none =>
        componentFailureRisk P
          (P.inc.toHeader kp.1) (P.inc.toVector kp.1) kp.2
    | some kp, some c =>
        derivedKeyFailure P e kp.2 c.2.1
          (P.hEnc2.encaps2Det c.1
            (P.inc.toHeader kp.1) (P.inc.toVector kp.1))
          (P.kdfOK c.2.2 e)
  have hRecover : ∀
      (gen encap : State P AuthState) (keys : ℕ → Option P.EpochKey) (e : ℕ),
      gen.epoch = e →
      encap.epoch = e →
      (match gen, encap with
      | .keysUnsampled .., .noHeaderReceived .. => True
      | .keysSampled .., .noHeaderReceived .. => True
      | .keysSampled .., .headerReceived .. => True
      | .keysSampled .., .ct1Sampled .. => True
      | .headerSent .., .ct1Sampled .. => True
      | .headerSent .., .ekReceivedCt1Sampled .. => True
      | .ct1Received .., .ct1Sampled .. => True
      | .ct1Received .., .ekReceivedCt1Sampled .. => True
      | .ct1Received .., .ct1Acknowledged .. => True
      | .ct1Received .., .ct2Sampled .. => True
      | .ekSentCt1Received .., .ct2Sampled .. => True
      | _, _ => False) →
      LocalPayloadInv P auth ik T gen →
      LocalPayloadInv P auth ik T encap →
      (keys e =
        if 0 < e ∧ e ≤ encap.completedEpoch then
          (T e).encaps1.map (fun c => P.kdfOK c.2.2 e)
        else none) →
      (∀ {c : P.inc.St × P.inc.C₁ × P.K},
        (T e).encaps1 = some c →
          0 < e ∧ e ≤ encap.completedEpoch ∧
            ∃ kp, (T e).keypair = some kp) →
      localPotential gen encap keys = transcriptPotential e := by
    intro gen encap keys e hGenEpoch hEncapEpoch hAllowed
      hLocalGen hLocalEncap hKeyPeer hEncapsCurrent
    cases hg : gen <;> simp [hg] at hAllowed
    all_goals cases he : encap
    all_goals simp [he] at hAllowed
    next =>
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      rw [hGenEpoch] at hLocalGen
      rcases hLocalGen with ⟨_, hkp, henc⟩
      simp [localPotential, transcriptPotential, State.epoch,
        hGenEpoch, hEncapEpoch, hkp, henc]
    next =>
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      rw [hGenEpoch] at hLocalGen
      rcases hLocalGen with ⟨_, pk, hkp, hvec, _, hpayload⟩
      cases hc : (T e).encaps1 with
      | none =>
      simp [localPotential, transcriptPotential, State.epoch,
            hGenEpoch, hEncapEpoch, hkp, hc, hvec, hpayload]
      | some c =>
          have hf := hEncapsCurrent hc
          simp [he, State.completedEpoch, State.epoch, hEncapEpoch] at hf
          omega
    next =>
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      simp only [he, LocalPayloadInv] at hLocalEncap
      rw [hGenEpoch] at hLocalGen
      rw [hEncapEpoch] at hLocalEncap
      rcases hLocalGen with ⟨_, pk, hkp, hvec, _, hpayload⟩
      rcases hLocalEncap with ⟨_, henc, _⟩
      simp [localPotential, transcriptPotential, State.epoch,
        hGenEpoch, hEncapEpoch, hkp, henc, hvec, hpayload]
    next =>
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      simp only [he, LocalPayloadInv] at hLocalEncap
      rw [hGenEpoch] at hLocalGen
      rw [hEncapEpoch] at hLocalEncap
      rcases hLocalGen with ⟨_, pk, hkp, hvec, _, _⟩
      rcases hLocalEncap with ⟨_, kp, key, hkp', henc, hhdr, _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      simp [localPotential, transcriptPotential, State.epoch,
        hGenEpoch, hEncapEpoch, hKeyPeer, hkp, henc, hvec, hhdrGen]
    next =>
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      simp only [he, LocalPayloadInv] at hLocalEncap
      rw [hGenEpoch] at hLocalGen
      rw [hEncapEpoch] at hLocalEncap
      rcases hLocalGen with ⟨_, pk, c, hkp, henc', _, hEncOK⟩
      have hvec := hEncOK.2
      rcases hLocalEncap with ⟨_, kp, key, hkp', henc, hhdr, _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      simp [localPotential, transcriptPotential, State.epoch,
        hGenEpoch, hEncapEpoch, hKeyPeer, hkp, henc', hvec, hhdrGen, hencEq]
    next =>
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      simp only [he, LocalPayloadInv] at hLocalEncap
      rw [hGenEpoch] at hLocalGen
      rw [hEncapEpoch] at hLocalEncap
      rcases hLocalGen with ⟨_, pk, c, hkp, henc', _, _⟩
      rcases hLocalEncap with
        ⟨_, kp, key, hkp', henc, hhdr, hvec', _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      have hvecGen := hvec'.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toVector x.1) hkpEq).symm
      simp [localPotential, transcriptPotential, State.epoch,
        hGenEpoch, hEncapEpoch, hKeyPeer, hkp, henc', hhdrGen, hvecGen, hencEq]
    next =>
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      simp only [he, LocalPayloadInv] at hLocalEncap
      rw [hGenEpoch] at hLocalGen
      rw [hEncapEpoch] at hLocalEncap
      rcases hLocalGen with ⟨_, pk, c, hkp, henc', hct1, hEncOK⟩
      have hvec := hEncOK.2
      rcases hLocalEncap with ⟨_, kp, key, hkp', henc, hhdr, _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      simp [localPotential, transcriptPotential, State.epoch,
        hGenEpoch, hEncapEpoch, hKeyPeer, hkp, henc', hct1, hvec,
        hhdrGen, hencEq]
    next =>
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      simp only [he, LocalPayloadInv] at hLocalEncap
      rw [hGenEpoch] at hLocalGen
      rw [hEncapEpoch] at hLocalEncap
      rcases hLocalGen with ⟨_, pk, c, hkp, henc', hct1, _⟩
      rcases hLocalEncap with
        ⟨_, kp, key, hkp', henc, hhdr, hvec', _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      have hvecGen := hvec'.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toVector x.1) hkpEq).symm
      simp [localPotential, transcriptPotential, State.epoch,
        hGenEpoch, hEncapEpoch, hKeyPeer, hkp, henc', hct1, hhdrGen,
        hvecGen, hencEq]
    next =>
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      simp only [he, LocalPayloadInv] at hLocalEncap
      rw [hGenEpoch] at hLocalGen
      rw [hEncapEpoch] at hLocalEncap
      rcases hLocalGen with ⟨_, pk, c, hkp, henc', hct1, hEncOK⟩
      have hvec := hEncOK.2
      rcases hLocalEncap with ⟨_, kp, key, hkp', henc, hhdr, _⟩
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      have hhdrGen := hhdr.trans
        (congrArg (fun x : P.PK × P.SK => P.inc.toHeader x.1) hkpEq).symm
      simp [localPotential, transcriptPotential, State.epoch,
        hGenEpoch, hEncapEpoch, hKeyPeer, hkp, henc', hct1, hvec,
        hhdrGen, hencEq]
    next =>
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      simp only [he, LocalPayloadInv] at hLocalEncap
      rw [hGenEpoch] at hLocalGen
      rw [hEncapEpoch] at hLocalEncap
      rcases hLocalGen with ⟨_, pk, c, hkp, henc', hct1, hEncOK⟩
      have hvec := hEncOK.2
      rcases hLocalEncap with ⟨_, kp, c', hkp', henc, hEncOK'⟩
      have hpayload := hEncOK'.2
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hskEq := congrArg Prod.snd hkpEq
      dsimp at hskEq
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      rw [hskEq]
      simp [localPotential, transcriptPotential, State.epoch,
        hGenEpoch, hEncapEpoch, hKeyPeer, hkp, henc', hct1, hpayload,
        hkpEq, hencEq]
    next =>
      simp only [hg, State.epoch] at hGenEpoch
      simp only [he, State.epoch] at hEncapEpoch
      simp only [hg, LocalPayloadInv] at hLocalGen
      simp only [he, LocalPayloadInv] at hLocalEncap
      rw [hGenEpoch] at hLocalGen
      rw [hEncapEpoch] at hLocalEncap
      rcases hLocalGen with ⟨_, pk, c, hkp, henc', hct1, _⟩
      rcases hLocalEncap with ⟨_, kp, c', hkp', henc, hEncOK'⟩
      have hpayload := hEncOK'.2
      have hf := hEncapsCurrent henc
      simp [he, State.completedEpoch, hEncapEpoch, hf.1, henc] at hKeyPeer
      have hkpEq := Option.some.inj (hkp.symm.trans hkp')
      have hskEq := congrArg Prod.snd hkpEq
      dsimp at hskEq
      have hencEq := Option.some.inj (henc'.symm.trans henc)
      rw [hskEq]
      simp [localPotential, transcriptPotential, State.epoch,
        hGenEpoch, hEncapEpoch, hKeyPeer, hkp, henc', hct1, hpayload,
        hkpEq, hencEq]
  by_cases hepoch : s.stA.epoch = s.stB.epoch
  · rw [if_pos hepoch]
    by_cases hrole : s.stA.controlPosition.1 = true
    · have hAllowed := (hPair true).1 hepoch hrole
      have hKeyPeer := hKeys false s.stA.epoch
      simp only [Bool.false_eq_true, ↓reduceIte] at hKeyPeer
      have hParityA := (hControl.2.2.2.2 true).1
      simp only [if_true] at hParityA
      rw [hrole] at hParityA
      have hOdd : s.stA.epoch % 2 = 1 :=
        of_decide_eq_true hParityA.symm
      have hEncapsCurrent :
          ∀ {c : P.inc.St × P.inc.C₁ × P.K},
            (T s.stA.epoch).encaps1 = some c →
              0 < s.stA.epoch ∧
              s.stA.epoch ≤ s.stB.completedEpoch ∧
                ∃ kp, (T s.stA.epoch).keypair = some kp := by
        intro c hc
        rcases hEncaps s.stA.epoch c.1 c.2.1 c.2.2 hc with
          ⟨hpos, hbound, pk, sk, hkp, _, _⟩
        have hbound' : s.stA.epoch ≤ s.stB.completedEpoch := by
          simpa [hOdd] using hbound
        exact ⟨hpos, hbound', (pk, sk), hkp⟩
      simp only [currentFailurePotential, hrole, if_true]
      rw [if_neg (not_ne_iff.mpr hepoch)]
      change localPotential s.stA s.stB s.keyB =
        transcriptPotential s.stA.epoch
      exact hRecover s.stA s.stB s.keyB s.stA.epoch rfl hepoch.symm
        hAllowed hLocalA hLocalB hKeyPeer hEncapsCurrent
    · have hroleFalse : s.stA.controlPosition.1 = false :=
        Bool.eq_false_of_not_eq_true hrole
      have hParityA := (hControl.2.2.2.2 true).1
      simp only [if_true] at hParityA
      rw [hroleFalse] at hParityA
      have hmod := Nat.mod_two_eq_zero_or_one s.stA.epoch
      have hEven : s.stA.epoch % 2 = 0 := by
        rcases hmod with hzero | hone
        · exact hzero
        · simp [hone] at hParityA
      have hParityB := (hControl.2.2.2.2 false).1
      simp only [Bool.false_eq_true, ↓reduceIte] at hParityB
      have hroleB : s.stB.controlPosition.1 = true := by
        simpa [← hepoch, hEven] using hParityB
      have hAllowed := (hPair false).1 hepoch.symm hroleB
      have hKeyPeer := hKeys true s.stA.epoch
      simp only [if_true] at hKeyPeer
      have hEncapsCurrent :
          ∀ {c : P.inc.St × P.inc.C₁ × P.K},
            (T s.stA.epoch).encaps1 = some c →
              0 < s.stA.epoch ∧
              s.stA.epoch ≤ s.stA.completedEpoch ∧
                ∃ kp, (T s.stA.epoch).keypair = some kp := by
        intro c hc
        rcases hEncaps s.stA.epoch c.1 c.2.1 c.2.2 hc with
          ⟨hpos, hbound, pk, sk, hkp, _, _⟩
        have hbound' : s.stA.epoch ≤ s.stA.completedEpoch := by
          simpa [hEven] using hbound
        exact ⟨hpos, hbound', (pk, sk), hkp⟩
      simp only [currentFailurePotential, hroleFalse,
        Bool.false_eq_true, ↓reduceIte]
      rw [if_neg (not_ne_iff.mpr hepoch.symm)]
      change localPotential s.stB s.stA s.keyA =
        transcriptPotential s.stA.epoch
      exact hRecover s.stB s.stA s.keyA s.stA.epoch hepoch.symm rfl
        hAllowed hLocalB hLocalA hKeyPeer hEncapsCurrent
  · rw [if_neg hepoch]
    by_cases hrole : s.stA.controlPosition.1 = true
    · simp only [currentFailurePotential, hrole, if_true]
      rw [if_pos hepoch]
    · have hroleFalse : s.stA.controlPosition.1 = false :=
        Bool.eq_false_of_not_eq_true hrole
      simp only [currentFailurePotential, hroleFalse,
        Bool.false_eq_true, ↓reduceIte]
      rw [if_pos (Ne.symm hepoch)]


end MLKEMBraid
