import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Core

/-!
# Opp-UniKEM-CKA Send Transitions

This module establishes the transition laws for the failure potential `V` and
tracked failure score `S` under `SendA` and `SendB`.
-/

open ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec

namespace Reduction.Internal

/-- Install a sampled KEM key pair in A's current local state. -/
def installAKeypair
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (pk : PK) (sk : SK) :=
  { s with stA := { s.stA with ekA := some pk, dkA := some sk } }

/-- Build the SendA state produced after key generation and optional public-key chunk emission. -/
def sendAKeygenState
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (kp : PK × SK) :=
  let ich := if s.stA.ack.ekRec then 0 else 1
  let ch? : Option (ℕ × Sym) :=
    if s.stA.ack.ekRec then none else some (ecEk.encode kp.1 ich)
  let msg : Message Sym := (ch?, s.stA.ack, s.stA.t, none)
  { s with
    stA := { s.stA with ekA := some kp.1, dkA := some kp.2, ich := ich }
    tcurA := s.stA.t - 1
    msgA := Function.update s.msgA (s.nA + 1) (some (msg, s.stA.t - 1))
    nA := s.nA + 1
    correct := s.correct && decide (s.tcurA ≤ s.stA.t - 1) }

/-- Build a SendB state that emits a message without installing a shared key. -/
def sendBNoneState
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (stB' : StB onoff Sym) (msg : Message Sym) :=
  { s with
    stB := stB'
    tcurB := s.stB.t - 1
    msgB := Function.update s.msgB (s.nB + 1) (some (msg, s.stB.t - 1))
    nB := s.nB + 1
    correct := s.correct && decide (s.tcurB ≤ s.stB.t - 1) }

/-- Build a SendB state that installs the sampled key and checks key-history consistency. -/
def sendBKeyState [DecidableEq K]
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (stB' : StB onoff Sym) (msg : Message Sym) (key : K) :=
  let keyB' := Function.update s.keyB s.stB.t (some key)
  { s with
    stB := stB'
    tcurB := s.stB.t - 1
    keyB := keyB'
    msgB := Function.update s.msgB (s.nB + 1) (some (msg, s.stB.t - 1))
    nB := s.nB + 1
    correct := s.correct
      && decide (s.tcurB ≤ s.stB.t - 1)
      && (s.keyB s.stB.t).isNone
      && ((s.keyA s.stB.t).isNone || s.keyA s.stB.t == some key)
      && (List.range (s.stB.t - 1 + 1)).all (fun t =>
        t = 0 || (keyB' t).isSome) }

/-- Build the SendB state for a newly sampled offline encapsulation. -/
def sendBOffState
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (off : onoff.St × onoff.C₀) (ich : ℕ) (msg : Message Sym) :=
  sendBNoneState onoff s
    { s.stB with stCt := some off.1, ct0 := some off.2, ich := ich } msg

/-- Build the SendB state for online encapsulation from an existing offline sample. -/
def sendBOnState [DecidableEq K]
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (ct1 : onoff.C₁) (key : K) (msg : Message Sym) :=
  sendBKeyState onoff s { s.stB with ct1 := some ct1, ich := 1 } msg key

/-- Build the SendB state when offline and online encapsulation are sampled together. -/
def sendBOffOnState [DecidableEq K]
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (off : onoff.St × onoff.C₀) (ct1 : onoff.C₁) (key : K)
    (msg : Message Sym) :=
  sendBKeyState onoff s
    { s.stB with
      stCt := some off.1
      ct0 := some off.2
      ct1 := some ct1
      ich := 1 } msg key

/-- The expected failure potential after fresh key generation is at most the
current potential plus `factorCorrectnessError`. -/
lemma keygen_failurePotential_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hdk : s.stA.dkA = none) :
    (Pr[⊥ | kem.keygen] + ∑' kp : PK × SK, Pr[= kp | kem.keygen] *
      currentFailurePotential kem onoff
        (installAKeypair onoff s kp.1 kp.2)) ≤
      currentFailurePotential kem onoff s +
        factorCorrectnessError kem onoff := by
  classical
  rcases hs with ⟨T, hInv⟩
  have hek : s.stA.ekA = none := by
    have hshape := hInv.keypairAShape
    simpa [hdk] using hshape
  by_cases ht : s.stA.t = s.stB.t
  · have hkpnone : (T s.stA.t).keypair = none := by
      simpa [hdk, hek, optionPair] using hInv.keypairA
    have honnone : (T s.stA.t).on = none := by
      by_contra hne
      have his := (T s.stA.t).on_keypair (Option.isSome_iff_ne_none.mpr hne)
      simp [hkpnone] at his
    have hct1 : s.stB.ct1 = none := by
      have hmap := hInv.onB
      rw [← ht, honnone] at hmap
      simpa using hmap.symm
    cases hct0 : s.stB.ct0 with
    | none =>
        have hst : s.stB.stCt = none := by
          have hshape := hInv.offBShape
          simpa [hct0] using hshape
        simpa [currentFailurePotential, installAKeypair, ht, hct1, hdk, hek,
          hct0, hst, optionPair] using
          (le_of_eq (factorCorrectnessError_eq_avg_keypair kem onoff).symm)
    | some ct0 =>
        have hstSome : s.stB.stCt.isSome := by
          simpa [hct0] using hInv.offBShape
        obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp hstSome
        simp [currentFailurePotential, installAKeypair, ht, hct1, hdk, hek,
          hct0, hst, optionPair, failureAfterOff]
  · have hepoch : s.stA.t = s.stB.t + 1 := by
      have hepochBounds := hInv.epochs
      omega
    simpa [currentFailurePotential, installAKeypair, ht, hdk, hek, optionPair] using
      (le_of_eq (factorCorrectnessError_eq_avg_keypair kem onoff).symm)

/-- Installing A's first key pair leaves `currentKEMFailure` equal to `false`. -/
lemma installAKeypair_currentKEMFailure_false [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hdk : s.stA.dkA = none)
    (pk : PK) (sk : SK) :
    currentKEMFailure kem onoff hDet (installAKeypair onoff s pk sk) = false := by
  classical
  rcases hs with ⟨T, hInv⟩
  by_cases ht : s.stA.t = s.stB.t
  · have hek : s.stA.ekA = none := by
      have hshape := hInv.keypairAShape
      simpa [hdk] using hshape
    have hkpnone : (T s.stA.t).keypair = none := by
      simpa [hdk, hek, optionPair] using hInv.keypairA
    have honnone : (T s.stA.t).on = none := by
      by_contra hne
      have his := (T s.stA.t).on_keypair (Option.isSome_iff_ne_none.mpr hne)
      simp [hkpnone] at his
    have hct1 : s.stB.ct1 = none := by
      have hmap := hInv.onB
      rw [← ht, honnone] at hmap
      simpa using hmap.symm
    simp [currentKEMFailure, installAKeypair, ht, hct1]
  · simp [currentKEMFailure, installAKeypair, ht]

/-- Install B's sampled offline state and first ciphertext component. -/
def installBOff
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (st : onoff.St) (ct0 : onoff.C₀) :=
  { s with stB := { s.stB with stCt := some st, ct0 := some ct0 } }

/-- The expected failure potential after fresh offline encapsulation is at
most the current potential plus `factorCorrectnessError`. -/
lemma off_failurePotential_le [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s) (hct0 : s.stB.ct0 = none) :
    (Pr[⊥ | onoff.encapsOff] +
      ∑' off : onoff.St × onoff.C₀, Pr[= off | onoff.encapsOff] *
      currentFailurePotential kem onoff
        (installBOff onoff s off.1 off.2)) ≤
      currentFailurePotential kem onoff s +
        factorCorrectnessError kem onoff := by
  classical
  rcases hs with ⟨T, hInv⟩
  have hst : s.stB.stCt = none := by
    have hshape := hInv.offBShape
    simpa [hct0] using hshape
  have hoffnone : (T s.stB.t).off = none := by
    simpa [hct0, hst, optionPair] using hInv.offB
  have ht : s.stA.t = s.stB.t := by
    by_contra hne
    have hepochBounds := hInv.epochs
    have hlt : s.stB.t < s.stA.t := by omega
    have hcomplete := hInv.pastComplete s.stB.t hInv.epochPosB hlt
    have honSome : (T s.stB.t).on.isSome := by
      simpa [EpochTranscript.key] using hcomplete
    have hoffSome := (T s.stB.t).on_off honSome
    simp [hoffnone] at hoffSome
  have hct1 : s.stB.ct1 = none := by
    have honnone : (T s.stB.t).on = none := by
      by_contra hne
      have honSome := Option.isSome_iff_ne_none.mpr hne
      simpa [hoffnone] using (T s.stB.t).on_off honSome
    have hmap := hInv.onB
    rw [honnone] at hmap
    simpa using hmap.symm
  cases hdk : s.stA.dkA with
  | none =>
      have hek : s.stA.ekA = none := by
        have hshape := hInv.keypairAShape
        simpa [hdk] using hshape
      simpa [currentFailurePotential, installBOff, ht, hct1, hdk, hek,
        hct0, hst, optionPair] using
        (le_of_eq (factorCorrectnessError_eq_avg_off kem onoff).symm)
  | some sk =>
      have hekSome : s.stA.ekA.isSome := by
        simpa [hdk] using hInv.keypairAShape
      obtain ⟨pk, hek⟩ := Option.isSome_iff_exists.mp hekSome
      simp [currentFailurePotential, installBOff, ht, hct1, hdk, hek,
        hct0, hst, optionPair, failureAfterKeypair]

/-- If B stores `pk` and an incomplete offline sample, then both parties are
in the same epoch and A stores `(pk, sk)` for some `sk`. -/
lemma online_source_shape
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (pk : PK) (st : onoff.St) (ct0 : onoff.C₀)
    (hekB : s.stB.ekA = some pk) (_hst : s.stB.stCt = some st)
    (_hct0 : s.stB.ct0 = some ct0) (hct1 : s.stB.ct1 = none) :
    ∃ sk, s.stA.t = s.stB.t ∧ s.stA.ekA = some pk ∧
      s.stA.dkA = some sk := by
  classical
  rcases hs with ⟨T, hInv⟩
  obtain ⟨sk, hkpB⟩ := hInv.decodedEk pk hekB
  have honnone : (T s.stB.t).on = none := by
    have hmap := hInv.onB
    rw [hct1] at hmap
    cases hon : (T s.stB.t).on with
    | none => rfl
    | some pair => simp [hon] at hmap
  have ht : s.stA.t = s.stB.t := by
    by_contra hne
    have hbounds := hInv.epochs
    have hlt : s.stB.t < s.stA.t := by omega
    have hcomplete := hInv.pastComplete s.stB.t hInv.epochPosB hlt
    simp [EpochTranscript.key, honnone] at hcomplete
  have hkpA : (T s.stA.t).keypair = optionPair s.stA.ekA s.stA.dkA :=
    hInv.keypairA
  rw [ht, hkpB] at hkpA
  cases hekA : s.stA.ekA <;> cases hdkA : s.stA.dkA <;>
    simp_all only [optionPair, Option.some.injEq, Prod.mk.injEq,
      Option.some_ne_none, exists_and_left, existsAndEq, and_true]

/-- If B stores `pk` before sampling a new offline component, then both parties
are in the same epoch and A stores `(pk, sk)` for some `sk`. -/
lemma newOff_source_shape
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (pk : PK) (hekB : s.stB.ekA = some pk) (hct0 : s.stB.ct0 = none) :
    ∃ sk, s.stA.t = s.stB.t ∧ s.stA.ekA = some pk ∧
      s.stA.dkA = some sk := by
  classical
  rcases hs with ⟨T, hInv⟩
  obtain ⟨sk, hkpB⟩ := hInv.decodedEk pk hekB
  have hst : s.stB.stCt = none := by
    have hshape := hInv.offBShape
    simpa [hct0] using hshape
  have hoffnone : (T s.stB.t).off = none := by
    simpa [hct0, hst, optionPair] using hInv.offB
  have ht : s.stA.t = s.stB.t := by
    by_contra hne
    have hbounds := hInv.epochs
    have hlt : s.stB.t < s.stA.t := by omega
    have hcomplete := hInv.pastComplete s.stB.t hInv.epochPosB hlt
    have honSome : (T s.stB.t).on.isSome := by
      simpa [EpochTranscript.key] using hcomplete
    have hoffSome := (T s.stB.t).on_off honSome
    simp [hoffnone] at hoffSome
  have hkpA := hInv.keypairA
  rw [ht, hkpB] at hkpA
  cases hekA : s.stA.ekA <;> cases hdkA : s.stA.dkA <;>
    simp_all only [optionPair, Option.some.injEq, Prod.mk.injEq,
      Option.some_ne_none, exists_and_left, existsAndEq, and_true]

/-- Install B's online ciphertext component and sampled shared key. -/
def installBOn
    {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (ct1 : onoff.C₁) (key : K) :=
  { s with
    stB := { s.stB with ct1 := some ct1 }
    keyB := Function.update s.keyB s.stB.t (some key) }

/-- After installing the online sample, the tracked failure score equals the
indicator that decapsulation disagrees with the sampled key. -/
lemma installBOn_score [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (sk : SK) (st : onoff.St) (ct0 : onoff.C₀) (ct1 : onoff.C₁) (key : K)
    (ht : s.stA.t = s.stB.t) (hdk : s.stA.dkA = some sk)
    (_hst : s.stB.stCt = some st) (hct0 : s.stB.ct0 = some ct0) :
    trackedFailureScore kem onoff
        (installBOn onoff s ct1 key,
          currentKEMFailure kem onoff hDet (installBOn onoff s ct1 key)) =
      if hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) ≠ some key
      then 1 else 0 := by
  by_cases hbad : hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) ≠ some key
  · simp [trackedFailureScore, currentKEMFailure, installBOn, ht, hdk, hct0,
      hbad, Function.update]
  · simp [trackedFailureScore, currentKEMFailure, currentFailurePotential,
      installBOn, ht, hdk, hct0, hbad, Function.update]

/-- The tracked failure score after `sendBOffState` equals the failure
potential after `installBOff`. -/
lemma sendBOffState_score [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (off : onoff.St × onoff.C₀) (ich : ℕ) (msg : Message Sym)
    (hct1 : s.stB.ct1 = none) :
    trackedFailureScore kem onoff
        (sendBOffState onoff s off ich msg,
          currentKEMFailure kem onoff hDet (sendBOffState onoff s off ich msg)) =
      currentFailurePotential kem onoff
        (installBOff onoff s off.1 off.2) := by
  simp [trackedFailureScore, currentKEMFailure, currentFailurePotential,
    sendBOffState, sendBNoneState, installBOff, hct1]

/-- The tracked failure score after `sendBOnState` equals the indicator that
decapsulation disagrees with the sampled key. -/
lemma sendBOnState_score [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (sk : SK) (ct0 : onoff.C₀) (ct1 : onoff.C₁) (key : K)
    (msg : Message Sym) (ht : s.stA.t = s.stB.t)
    (hdk : s.stA.dkA = some sk) (hct0 : s.stB.ct0 = some ct0) :
    trackedFailureScore kem onoff
        (sendBOnState onoff s ct1 key msg,
          currentKEMFailure kem onoff hDet (sendBOnState onoff s ct1 key msg)) =
      if hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) ≠ some key
      then 1 else 0 := by
  by_cases hbad : hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) ≠ some key
  · simp [trackedFailureScore, currentKEMFailure, sendBOnState, sendBKeyState,
      ht, hdk, hct0, hbad, Function.update]
  · simp [trackedFailureScore, currentKEMFailure, currentFailurePotential,
      sendBOnState, sendBKeyState, ht, hdk, hct0, hbad, Function.update]

/-- The tracked failure score after `sendBOffOnState` equals the indicator that
decapsulation disagrees with the sampled key. -/
lemma sendBOffOnState_score [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (sk : SK) (off : onoff.St × onoff.C₀) (ct1 : onoff.C₁) (key : K)
    (msg : Message Sym) (ht : s.stA.t = s.stB.t)
    (hdk : s.stA.dkA = some sk) :
    trackedFailureScore kem onoff
        (sendBOffOnState onoff s off ct1 key msg,
          currentKEMFailure kem onoff hDet
            (sendBOffOnState onoff s off ct1 key msg)) =
      if hDet.decapsDet sk (onoff.split.symm (off.2, ct1)) ≠ some key
      then 1 else 0 := by
  by_cases hbad : hDet.decapsDet sk (onoff.split.symm (off.2, ct1)) ≠ some key
  · simp [trackedFailureScore, currentKEMFailure, sendBOffOnState, sendBKeyState,
      ht, hdk, hbad, Function.update]
  · simp [trackedFailureScore, currentKEMFailure, currentFailurePotential,
      sendBOffOnState, sendBKeyState, ht, hdk, hbad, Function.update]

end Reduction.Internal

end oppUniKemCKA
