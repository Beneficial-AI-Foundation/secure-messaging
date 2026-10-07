/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.Quantitative.RecvStep
import SecureMessaging.SCKA.OppBiKEM.Correctness.Quantitative.SendDist
import SecureMessaging.SCKA.OppBiKEM.Correctness.SendFacts

/-!
# Opp-BiKEM-CKA — One-step score bound for send queries

This module proves the send case of the one-step bound of `Quantitative.Main`, whose notation
it uses (`ε`, `φ`, `V`, `S`). From a state satisfying the main invariant that is not bad, with
the flag clear, `SendA` and `SendB` raise the expected tracked score `S` by at most `ε`
(`tracked_sendA_score_le`, `tracked_sendB_score_le`); `tracked_step_score_le` combines this
with the non-send case of `Quantitative.RecvStep`. Plain sends, advances, and encapsulations
are handled for either role through `pairPotential` and `pairFailure`, which list the sender
first.
-/

open OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

section Pair

variable {kem : KEMScheme ProbComp K PK SK C} (hDet : kem.DeterministicDecaps) [DecidableEq K]

/-- Both parties' pending potentials, with the party `stS` listed first. -/
noncomputable def pairPotential (stS stR : State PK SK C Sym) (keyS keyR : ℕ → Option K) : ℝ≥0∞ :=
  pendingPotential hDet stS stR keyR + pendingPotential hDet stR stS keyS

/-- Both parties' `kemFailureAt`, with the party `stS` listed first. -/
def pairFailure (stS stR : State PK SK C Sym) (keyS keyR : ℕ → Option K) : Bool :=
  kemFailureAt hDet stS stR keyR || kemFailureAt hDet stR stS keyS

/-- `V(s)` is the pair potential with A listed first. -/
theorem failurePotential_eq_pairA
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    failurePotential hDet s = pairPotential hDet s.stA s.stB s.keyA s.keyB := rfl

/-- `V(s)` is the pair potential with B listed first. -/
theorem failurePotential_eq_pairB
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    failurePotential hDet s = pairPotential hDet s.stB s.stA s.keyB s.keyA := by
  simp only [failurePotential, pairPotential, add_comm]

/-- `bad s` is the pair failure with A listed first. -/
theorem kemFailure_eq_pairA
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    kemFailure hDet s = pairFailure hDet s.stA s.stB s.keyA s.keyB := rfl

/-- `bad s` is the pair failure with B listed first. -/
theorem kemFailure_eq_pairB
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    kemFailure hDet s = pairFailure hDet s.stB s.stA s.keyB s.keyA := by
  simp only [kemFailure, pairFailure, Bool.or_comm]

end Pair

/-! ### The two averaging steps -/

section Average

variable {kem : KEMScheme ProbComp K PK SK C} (hDet : kem.DeterministicDecaps) [DecidableEq K]

/-- Averaging `V + φ(pk, sk)` over key generation gives at most `V + ε`. -/
theorem expectedPayoff_keygen_le {A : Type} (f : PK × SK → A) (score : A → ℝ≥0∞) (V : ℝ≥0∞)
    (hscore : ∀ kp, score (f kp) = V + keypairFailure kem hDet kp.1 kp.2) :
    expectedPayoff (kem.keygen >>= fun kp => pure (f kp)) score ≤
      V + kem.correctnessError ProbCompRuntime.probComp := by
  rw [expectedPayoff_bind]
  simp only [expectedPayoff_pure, hscore, correctnessError_eq_avg_keypair kem hDet]
  calc Pr[⊥ | kem.keygen] + ∑' kp : PK × SK, Pr[= kp | kem.keygen] *
          (V + keypairFailure kem hDet kp.1 kp.2)
        = Pr[⊥ | kem.keygen] + ((∑' kp : PK × SK, Pr[= kp | kem.keygen]) * V +
            ∑' kp : PK × SK, Pr[= kp | kem.keygen] * keypairFailure kem hDet kp.1 kp.2) := by
          congr 1
          rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
          refine tsum_congr fun kp => ?_
          rw [mul_add]
      _ ≤ Pr[⊥ | kem.keygen] + (1 * V +
            ∑' kp : PK × SK, Pr[= kp | kem.keygen] * keypairFailure kem hDet kp.1 kp.2) := by
          gcongr
          exact tsum_probOutput_le_one
      _ = V + (Pr[⊥ | kem.keygen] +
            ∑' kp : PK × SK, Pr[= kp | kem.keygen] * keypairFailure kem hDet kp.1 kp.2) := by
          rw [one_mul]; ring

/-- If the score after encapsulating to `pk` is `1` when decapsulation with `sk` disagrees with
the encapsulated key and `V` otherwise, its expected value is at most `V + φ(pk, sk)`. -/
theorem expectedPayoff_encaps_le {A : Type} (pk : PK) (sk : SK) (g : C × K → A)
    (score : A → ℝ≥0∞) (V : ℝ≥0∞)
    (hscore : ∀ ck : C × K, score (g ck) =
      if hDet.decapsDet sk ck.1 ≠ some ck.2 then 1 else V) :
    expectedPayoff (kem.encaps pk >>= fun ck => pure (g ck)) score ≤
      V + keypairFailure kem hDet pk sk := by
  classical
  rw [expectedPayoff_bind]
  simp only [expectedPayoff_pure, hscore]
  rw [keypairFailure_eq_probEvent, probEvent_eq_tsum_ite]
  calc Pr[⊥ | kem.encaps pk] + ∑' ck : C × K, Pr[= ck | kem.encaps pk] *
          (if hDet.decapsDet sk ck.1 ≠ some ck.2 then 1 else V)
        ≤ Pr[⊥ | kem.encaps pk] + ∑' ck : C × K,
            ((if hDet.decapsDet sk ck.1 ≠ some ck.2 then Pr[= ck | kem.encaps pk] else 0) +
              Pr[= ck | kem.encaps pk] * V) := by
          gcongr with ck
          split_ifs <;> simp
      _ = Pr[⊥ | kem.encaps pk] +
          ((∑' ck : C × K, if hDet.decapsDet sk ck.1 ≠ some ck.2 then Pr[= ck | kem.encaps pk]
              else 0) + (∑' ck : C × K, Pr[= ck | kem.encaps pk]) * V) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      _ ≤ Pr[⊥ | kem.encaps pk] +
          ((∑' ck : C × K, if hDet.decapsDet sk ck.1 ≠ some ck.2 then Pr[= ck | kem.encaps pk]
              else 0) + 1 * V) := by
          gcongr
          exact tsum_probOutput_le_one
      _ = V + ((∑' ck : C × K, if hDet.decapsDet sk ck.1 ≠ some ck.2 then Pr[= ck | kem.encaps pk]
              else 0) + Pr[⊥ | kem.encaps pk]) := by
          rw [one_mul]; ring

end Average

/-! ### Local facts for the three kinds of send -/

/-- A supported send that changes the responder epoch starts from a state without a retained
own public key (the advance gate of `sendWith`). -/
theorem send_advance_ek (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈ support (send role kem ecEk ecCt st))
    (hadv : st'.res.resEpoch ≠ st.res.resEpoch) :
    st.req.ek = none := by
  rw [send, mem_support_bind_iff] at hout
  obtain ⟨out, hmem, hout⟩ := hout
  cases out with
  | none => simp at hout
  | some out =>
    rcases out with ⟨key, msg, epoch, state, rand⟩
    simp only [support_pure, Set.mem_singleton_iff, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hout
    unfold sendWith at hmem
    dsimp only at hmem
    repeat' first
      | split at hmem
      | (rw [mem_support_bind_iff] at hmem; obtain ⟨x, _, hmem⟩ := hmem)
    all_goals simp only [support_pure, Set.mem_singleton_iff,
      Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hmem
    all_goals obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hmem
    all_goals simp_all

section Local

variable {kem : KEMScheme ProbComp K PK SK C} {hDet : kem.DeterministicDecaps} [DecidableEq K]
  {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
  {T : Transcript kem} {roleS : Role} {stS stR : State PK SK C Sym}
  {msgsS msgsR : ℕ → Option (Message Sym × ℕ)} {keyS keyR : ℕ → Option K}
  {tcurS tcurR : ℕ}
  (hS : PartyInv roleS ecEk ecCt T stS stR msgsS keyS keyR tcurS)
  (hR : PartyInv roleS.peer ecEk ecCt T stR stS msgsR keyR keyS tcurR)

include hS hR

omit [DecidableEq K] in
/-- If both ciphertext acknowledgements of the advance gate are present, the new key epoch is
not in `ekRec` and the sender retains no secret key. -/
theorem advance_prereqs
    (hgate : stS.res.resEpoch ∈ stS.ack.ctRec ∧ stS.res.resEpoch + roleS.offset ∈ stS.ack.ctRec) :
    stS.res.resEpoch + 2 + roleS.offset ∉ stS.ack.ekRec ∧ stS.req.dk = [] := by
  have hpar : (stS.res.resEpoch + 2 + roleS.offset) % 2 = roleS.reqParity := by
    have := hS.res_parity
    cases roleS <;> simp only [Role.offset, Role.reqParity, Role.resParity] at this ⊢ <;> omega
  refine ⟨?_, ?_⟩
  · intro hack
    have hsome := hS.ekRec_req _ hack hpar
    obtain ⟨pk, hpk⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨sk, hkp⟩ := hR.ekPeer_T _ pk hpk
    have := hS.keypair_future _ hpar (by omega)
    rw [this] at hkp; cases hkp
  · rcases hS.dk_shape with hnil | ⟨sk, hone⟩
    · exact hnil
    · exfalso
      have hmem : (stS.res.resEpoch + roleS.offset, sk) ∈ stS.req.dk := by
        rw [hone]; exact List.mem_singleton_self _
      obtain ⟨hp, hpos, -, hkey, -⟩ := hS.dk_T _ sk hmem
      have henc := hS.ctRec_req_enc _ hgate.2 hpos hp
      have := hS.key_req _ hpos hp
      rw [if_pos hgate.2, EpochTranscript.key] at this
      obtain ⟨⟨c, k⟩, hck⟩ := Option.isSome_iff_exists.mp henc
      rw [hck] at this
      rw [this] at hkey
      cases hkey

/-- An advance with key pair `kp = (pk, sk)` adds `φ(pk, sk)` to the pair potential: the sender
retained no secret key before, and the peer's pending potential is unchanged. -/
theorem pairPotential_advance (ecEk' : ErasureCodePayload PK Sym) (kp : PK × SK)
    (hgate : stS.res.resEpoch ∈ stS.ack.ctRec ∧ stS.res.resEpoch + roleS.offset ∈ stS.ack.ctRec) :
    pairPotential hDet (advanceSend (K := K) roleS ecEk' stS kp).2.2.2 stR keyS keyR =
      pairPotential hDet stS stR keyS keyR + keypairFailure kem hDet kp.1 kp.2 := by
  obtain ⟨-, hnil⟩ := advance_prereqs hS hR hgate
  set e' := stS.res.resEpoch + 2 + roleS.offset with he'
  have hepar : e' % 2 = roleS.reqParity := by
    have := hS.res_parity
    cases roleS <;> simp only [he', Role.offset, Role.reqParity, Role.resParity] at this ⊢ <;> omega
  have hepos : 0 < e' := by
    have h1 := hS.res_lower
    have h2 := hS.res_parity
    cases roleS <;> simp only [he', Role.offset, Role.resParity] at h1 h2 ⊢ <;> omega
  have hkeyR : keyR e'.toNat = none := by
    have hp' : e' % 2 = roleS.peer.resParity := by simpa using hepar
    rw [hR.key_res e' hepos hp', EpochTranscript.key]
    have hkp : (T e').keypair = none := hS.keypair_future e' hepar (by omega)
    have henc : (T e').enc = none := by
      by_contra h
      have := (T e').enc_keypair (Option.isSome_iff_ne_none.mpr h)
      rw [hkp] at this; cases this
    rw [henc]; rfl
  have hpeer : stR.res.ekPeer e' = none := by
    by_contra h
    have hle := hR.ekPeer_le e' (Option.isSome_iff_ne_none.mpr h)
    have := hS.peer_req_le_res
    have hoff := Role.peer_offset roleS
    omega
  unfold pairPotential
  rw [pendingPotential_nil hDet hnil, zero_add]
  have hdk' : (advanceSend (K := K) roleS ecEk' stS kp).2.2.2.req.dk = [(e', kp.2)] := by
    simp [advanceSend, hnil, he']
  rw [pendingPotential_singleton hDet hdk']
  have h1 : pendingTerm hDet (advanceSend (K := K) roleS ecEk' stS kp).2.2.2 stR keyR (e', kp.2) =
      keypairFailure kem hDet kp.1 kp.2 :=
    pendingTerm_of_ek hDet hkeyR hpeer (by simp [advanceSend])
  have h2 : pendingPotential hDet stR (advanceSend (K := K) roleS ecEk' stS kp).2.2.2 keyS =
      pendingPotential hDet stR stS keyS := rfl
  rw [h1, h2, add_comm]

/-- After an advance, `kemFailureAt` holds for neither party. -/
theorem pairFailure_advance (ecEk' : ErasureCodePayload PK Sym) (kp : PK × SK)
    (hgate : stS.res.resEpoch ∈ stS.ack.ctRec ∧ stS.res.resEpoch + roleS.offset ∈ stS.ack.ctRec) :
    pairFailure hDet (advanceSend (K := K) roleS ecEk' stS kp).2.2.2 stR keyS keyR = false := by
  obtain ⟨-, hnil⟩ := advance_prereqs hS hR hgate
  set e' := stS.res.resEpoch + 2 + roleS.offset with he'
  have hepar : e' % 2 = roleS.reqParity := by
    have := hS.res_parity
    cases roleS <;> simp only [he', Role.offset, Role.reqParity, Role.resParity] at this ⊢ <;> omega
  have hepos : 0 < e' := by
    have h1 := hS.res_lower
    have h2 := hS.res_parity
    cases roleS <;> simp only [he', Role.offset, Role.resParity] at h1 h2 ⊢ <;> omega
  have hkeyR : keyR e'.toNat = none := by
    have hp' : e' % 2 = roleS.peer.resParity := by simpa using hepar
    rw [hR.key_res e' hepos hp', EpochTranscript.key]
    have hkp : (T e').keypair = none := hS.keypair_future e' hepar (by omega)
    have henc : (T e').enc = none := by
      by_contra h
      have := (T e').enc_keypair (Option.isSome_iff_ne_none.mpr h)
      rw [hkp] at this; cases this
    rw [henc]; rfl
  have hct : stS.res.ct = none := hS.ct_acked hgate.1
  unfold pairFailure
  apply Bool.or_eq_false_iff.mpr
  refine ⟨?_, ?_⟩
  · -- the sender's single key is for `e'`, to which the peer has not encapsulated
    apply kemFailureAt_eq_false_of
    by_cases h : stR.res.resEpoch = e'
    · right; right
      rw [h]; exact hkeyR
    · left
      have hne : (stR.res.resEpoch == e') = false := beq_eq_false_iff_ne.mpr h
      rw [he'] at hne
      simp [advanceSend, hnil, List.lookup, hne]
  · apply kemFailureAt_eq_false_of
    right; left
    simp [advanceSend, hct]

/-- If the sender's current responder epoch `e` is unacknowledged, it retains no ciphertext,
and it has decoded the peer's key `pk` for `e`, then: the transcript's key pair of `e` is
`(pk, sk)`, the peer retains exactly `sk`, the transcript has no encapsulation at `e`, the
sender's key table has no entry at `e`, and the peer's pending term is `φ(pk, sk)`. -/
theorem encaps_prereqs (hnot : stS.res.resEpoch ∉ stS.ack.ctRec) (hct : stS.res.ct = none)
    {pk : PK} (hpk : stS.res.ekPeer stS.res.resEpoch = some pk) :
    ∃ sk, (T stS.res.resEpoch).keypair = some (pk, sk) ∧
      stR.req.dk = [(stS.res.resEpoch, sk)] ∧
      (T stS.res.resEpoch).enc = none ∧
      keyS stS.res.resEpoch.toNat = none ∧
      pendingTerm hDet stR stS keyS (stS.res.resEpoch, sk) =
        keypairFailure kem hDet pk sk := by
  obtain ⟨sk, hkp⟩ := hS.ekPeer_T _ pk hpk
  have hpar : stS.res.resEpoch % 2 = roleS.peer.reqParity := by simpa using hS.res_parity
  have hpos : 0 < stS.res.resEpoch := hR.keypair_pos _ hpar (by rw [hkp]; rfl)
  have henc : (T stS.res.resEpoch).enc = none := by
    cases h : (T stS.res.resEpoch).enc with
    | none => rfl
    | some ck =>
        exfalso
        rcases hS.enc_current ck.1 ck.2 h with h1 | h1
        · rw [hct] at h1; cases h1
        · exact hnot h1
  have hnotR : stS.res.resEpoch ∉ stR.ack.ctRec := by
    intro hin
    have := hR.ctRec_req_enc _ hin hpos hpar
    rw [henc] at this; cases this
  have hmem := hR.T_dk _ pk sk hkp hpar hnotR
  have hdk : stR.req.dk = [(stS.res.resEpoch, sk)] := by
    rcases hR.dk_shape with hnil | ⟨sk', hone⟩
    · rw [hnil] at hmem; cases hmem
    · rw [hone] at hmem
      simp only [List.mem_singleton, Prod.mk.injEq] at hmem
      rw [hone, hmem.1, hmem.2]
  have hkey : keyS stS.res.resEpoch.toNat = none := by
    rw [hS.key_res _ hpos hS.res_parity, EpochTranscript.key, henc]; rfl
  refine ⟨sk, hkp, hdk, henc, hkey, ?_⟩
  exact pendingTerm_of_ekPeer hDet hkey hpk

/-- An encapsulation removes the peer's pending term and leaves everything else: before, the
pair potential is the sender's own potential plus `φ(pk, sk)`; after, whatever was sampled, it
is the sender's own potential. -/
theorem pairPotential_encaps (ecCt' : ErasureCodePayload C Sym)
    (hnot : stS.res.resEpoch ∉ stS.ack.ctRec) (hct : stS.res.ct = none)
    {pk : PK} (hpk : stS.res.ekPeer stS.res.resEpoch = some pk) :
    ∃ sk, (T stS.res.resEpoch).keypair = some (pk, sk) ∧
      stR.req.dk = [(stS.res.resEpoch, sk)] ∧
      pairPotential hDet stS stR keyS keyR =
        pendingPotential hDet stS stR keyR + keypairFailure kem hDet pk sk ∧
      ∀ ck : C × K,
        pairPotential hDet (encapsSend (K := K) roleS ecCt' stS ck).2.2.2 stR
          (Function.update keyS stS.res.resEpoch.toNat (some ck.2)) keyR =
          pendingPotential hDet stS stR keyR := by
  obtain ⟨sk, hkp, hdk, -, hkey, hterm⟩ := encaps_prereqs hS hR hnot hct hpk
  refine ⟨sk, hkp, hdk, ?_, ?_⟩
  · unfold pairPotential
    rw [pendingPotential_singleton hDet hdk, hterm]
  · intro ck
    unfold pairPotential
    rw [pendingPotential_singleton hDet hdk, pendingTerm_of_key_some hDet (by simp), add_zero]
    rfl

omit hS hR in
/-- If `kemFailureAt` held for neither party before, then after encapsulating `ck = (c, k)` the
pair failure is exactly whether decapsulating `c` with the peer's retained `sk` disagrees with
`k`. -/
theorem pairFailure_encaps (ecCt' : ErasureCodePayload C Sym) (ck : C × K) (sk : SK)
    (hdk : stR.req.dk = [(stS.res.resEpoch, sk)])
    (hfail : pairFailure hDet stS stR keyS keyR = false) :
    pairFailure hDet (encapsSend (K := K) roleS ecCt' stS ck).2.2.2 stR
        (Function.update keyS stS.res.resEpoch.toNat (some ck.2)) keyR =
      decide (hDet.decapsDet sk ck.1 ≠ some ck.2) := by
  unfold pairFailure at hfail ⊢
  rw [Bool.or_eq_false_iff] at hfail
  have h1 : kemFailureAt hDet (encapsSend (K := K) roleS ecCt' stS ck).2.2.2 stR keyR =
      kemFailureAt hDet stS stR keyR :=
    kemFailureAt_congr hDet rfl (by simp [encapsSend]) rfl rfl
  rw [h1, hfail.1, Bool.false_or]
  apply kemFailureAt_eq_decide hDet
  · simp [encapsSend, hdk]
  · simp [encapsSend]
  · simp [encapsSend]

omit hS hR in
/-- A supported send that emits no key and keeps the responder epoch leaves the pair potential
and the pair failure unchanged. -/
theorem pair_plain (kem' : KEMScheme ProbComp K PK SK C) (ecEk' : ErasureCodePayload PK Sym)
    (ecCt' : ErasureCodePayload C Sym) {ρ : Message Sym} {tsnd : ℕ} {stS' : State PK SK C Sym}
    (hout : some (none, ρ, tsnd, stS') ∈ support (send roleS kem' ecEk' ecCt' stS))
    (hres : stS'.res.resEpoch = stS.res.resEpoch) :
    pairPotential hDet stS' stR keyS keyR = pairPotential hDet stS stR keyS keyR ∧
      pairFailure hDet stS' stR keyS keyR = pairFailure hDet stS stR keyS keyR := by
  have hp := send_provenance roleS kem' ecEk' ecCt' stS none ρ tsnd stS' hout
  have hct : stS'.res.ct = stS.res.ct := hp.no_key_ciphertext rfl
  have hpeer := hp.peer_keys
  obtain ⟨hdk, hek⟩ : stS'.req.dk = stS.req.dk ∧ stS'.req.ek = stS.req.ek := by
    rcases hp.keygen_transition with ⟨-, h1, h2⟩ | ⟨-, -, -, h, -, -⟩
    · exact ⟨h1, h2⟩
    · omega
  refine ⟨?_, ?_⟩
  · unfold pairPotential pendingPotential
    rw [hdk]
    congr 1
    · congr 1
      apply List.map_congr_left
      intro p _
      exact pendingTerm_congr hDet p rfl rfl hek
    · congr 1
      apply List.map_congr_left
      intro p _
      exact pendingTerm_congr hDet p rfl (by rw [hpeer]) rfl
  · unfold pairFailure
    rw [kemFailureAt_congr hDet (st := stS) (st' := stS') (peer := stR) (peer' := stR)
        (peerKey := keyR) (peerKey' := keyR) rfl (by rw [hdk]) rfl rfl,
      kemFailureAt_congr hDet (st := stR) (st' := stR) (peer := stS) (peer' := stS')
        (peerKey := keyS) (peerKey' := keyS) hres rfl hct rfl]

omit [DecidableEq K] hS hR in
/-- Outside the gate and the encapsulation conditions, a supported send emits no key and keeps
the responder epoch. -/
theorem send_plain_of_not (kem' : KEMScheme ProbComp K PK SK C)
    (ecEk' : ErasureCodePayload PK Sym) (ecCt' : ErasureCodePayload C Sym)
    (hgate : ¬ (stS.req.ek = none ∧ stS.res.resEpoch ∈ stS.ack.ctRec ∧
      stS.res.resEpoch + roleS.offset ∈ stS.ack.ctRec))
    (hencaps : ¬ (stS.res.resEpoch + roleS.offset ∈ stS.ack.ekRec ∧
      stS.res.resEpoch ∉ stS.ack.ctRec ∧ stS.res.ct = none ∧ stS.res.resEpoch ∈ stS.ack.ekRec))
    {key? : Option (ℕ × K)} {ρ : Message Sym} {tsnd : ℕ} {stS' : State PK SK C Sym}
    (hout : some (key?, ρ, tsnd, stS') ∈ support (send roleS kem' ecEk' ecCt' stS)) :
    key? = none ∧ stS'.res.resEpoch = stS.res.resEpoch := by
  have hp := send_provenance roleS kem' ecEk' ecCt' stS key? ρ tsnd stS' hout
  have hres : stS'.res.resEpoch = stS.res.resEpoch := by
    rcases hp.keygen_transition with ⟨h, -, -⟩ | ⟨-, -, -, h, -, -⟩
    · exact h
    · exfalso
      have hg := send_advance_guard roleS kem' ecEk' ecCt' stS key? ρ tsnd stS' hout (by omega)
      have hek : stS.req.ek = none :=
        send_advance_ek roleS kem' ecEk' ecCt' stS key? ρ tsnd stS' hout (by omega)
      exact hgate ⟨hek, hg⟩
  refine ⟨?_, hres⟩
  rcases key? with _ | ⟨tI, k⟩
  · rfl
  · exfalso
    obtain ⟨-, -, -, -, hkeys⟩ :=
      send_support_facts roleS kem' ecEk' ecCt' stS (some (tI, k)) ρ tsnd stS' hout
    obtain ⟨-, hnot, hct, -⟩ := hkeys tI k rfl
    obtain ⟨hpeerAck, hacked⟩ :=
      send_emittedKey_peerAck roleS kem' ecEk' ecCt' stS tI k ρ tsnd stS' hout
    rw [hres] at hnot hpeerAck hacked
    exact hencaps ⟨hacked, hnot, hct, hpeerAck⟩

end Local

/-! ### The send oracles -/

section Oracle

variable [DecidableEq K] [DecidableEq Sym]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

omit [DecidableEq Sym] in
/-- The game-state outcome of `SendA` for a local send result: the function that
`SCKAScheme.oracleSendA_run_eq` maps over A's local send. -/
private def sendAOutcome
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    Option (Option (ℕ × K) × Message Sym × ℕ × StA PK SK C Sym) →
      Option (ℕ × Option ℕ × Message Sym) ×
        SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
  | none => (none, s)
  | some (keyOpt, ρ, tsnd, stA') =>
      (some (tsnd, keyOpt.map Prod.fst, ρ), SCKAScheme.sendAUpdate s keyOpt ρ tsnd stA')

omit [DecidableEq Sym] in
/-- The game-state outcome of `SendB` for a local send result: the function that
`SCKAScheme.oracleSendB_run_eq` maps over B's local send. -/
private def sendBOutcome
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    Option (Option (ℕ × K) × Message Sym × ℕ × StB PK SK C Sym) →
      Option (ℕ × Option ℕ × Message Sym) ×
        SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
  | none => (none, s)
  | some (keyOpt, ρ, tsnd, stB') =>
      (some (tsnd, keyOpt.map Prod.fst, ρ), SCKAScheme.sendBUpdate s keyOpt ρ tsnd stB')

open SCKAScheme.sckaCorrectnessSpec in
/-- `Ô SendA` run from `(s, false)` is A's local `send` followed by the game's `sendAOutcome`
and the flag update. -/
theorem trackedBiKem_sendA_run
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (trackedBiKem kem hDet ecEk ecCt leak OSendA).run (s, false) =
      send .A kem ecEk ecCt s.stA >>= fun out =>
        pure ((sendAOutcome s out).1,
          ((sendAOutcome s out).2,
            kemFailure hDet (sendAOutcome s out).2)) := by
  change ((SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak) ()).run s >>=
    fun y => pure (y.1, (y.2, false || kemFailure hDet y.2))) = _
  rw [SCKAScheme.oracleSendA_run_eq, map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun out => ?_
  rcases out with _ | ⟨keyOpt, ρ, tsnd, st'⟩ <;> simp [sendAOutcome]

open SCKAScheme.sckaCorrectnessSpec in
/-- `Ô SendB` run from `(s, false)` is B's local `send` followed by the game's `sendBOutcome`
and the flag update. -/
theorem trackedBiKem_sendB_run
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (trackedBiKem kem hDet ecEk ecCt leak OSendB).run (s, false) =
      send .B kem ecEk ecCt s.stB >>= fun out =>
        pure ((sendBOutcome s out).1,
          ((sendBOutcome s out).2,
            kemFailure hDet (sendBOutcome s out).2)) := by
  change ((SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak) ()).run s >>=
    fun y => pure (y.1, (y.2, false || kemFailure hDet y.2))) = _
  rw [SCKAScheme.oracleSendB_run_eq, map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun out => ?_
  rcases out with _ | ⟨keyOpt, ρ, tsnd, st'⟩ <;> simp [sendBOutcome]

omit [DecidableEq Sym] in
/-- `sendAOutcome` on a successful send, as the game update `SCKAScheme.sendAUpdate`. -/
theorem sendAOutcome_some (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K
    (Message Sym)) (t : Option (ℕ × K) × Message Sym × ℕ × StA PK SK C Sym) :
    sendAOutcome s (some t) =
      (some (t.2.2.1, t.1.map Prod.fst, t.2.1),
        SCKAScheme.sendAUpdate s t.1 t.2.1 t.2.2.1 t.2.2.2) :=
  rfl

omit [DecidableEq Sym] in
/-- `sendBOutcome` on a successful send, as the game update `SCKAScheme.sendBUpdate`. -/
theorem sendBOutcome_some (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K
    (Message Sym)) (t : Option (ℕ × K) × Message Sym × ℕ × StB PK SK C Sym) :
    sendBOutcome s (some t) =
      (some (t.2.2.1, t.1.map Prod.fst, t.2.1),
        SCKAScheme.sendBUpdate s t.1 t.2.1 t.2.2.1 t.2.2.2) :=
  rfl

open SCKAScheme.sckaCorrectnessSpec in
/-- From `(s, false)` with `s` satisfying the main invariant and not bad, `SendA` raises the
expected tracked score by at most `ε`. -/
theorem tracked_sendA_score_le
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false) :
    expectedPayoff ((trackedBiKem kem hDet ecEk ecCt leak OSendA).run (s, false))
        (fun z => trackedScore hDet z.2) ≤
      trackedScore hDet (s, false) + kem.correctnessError ProbCompRuntime.probComp := by
  obtain ⟨-, T, hA, hB⟩ := hs
  have hfailA : pairFailure hDet s.stA s.stB s.keyA s.keyB = false := by
    rwa [kemFailure_eq_pairA] at hfail
  rw [trackedBiKem_sendA_run, trackedScore_false, failurePotential_eq_pairA]
  by_cases hgate : s.stA.req.ek = none ∧ s.stA.res.resEpoch ∈ s.stA.ack.ctRec ∧
      s.stA.res.resEpoch + Role.A.offset ∈ s.stA.ack.ctRec
  · obtain ⟨hfresh, -⟩ := advance_prereqs hA hB hgate.2
    rw [send_eq_advance .A kem ecEk ecCt s.stA hgate.1 hgate.2 hfresh, bind_assoc]
    simp only [pure_bind]
    apply expectedPayoff_keygen_le hDet _ _ (pairPotential hDet s.stA s.stB s.keyA s.keyB)
    intro kp
    rw [sendAOutcome_some]
    have h1 : (advanceSend (K := K) .A ecEk s.stA kp).1 = none := rfl
    simp only [h1, kemFailure_eq_pairA, SCKAScheme.sendAUpdate_stA, SCKAScheme.sendAUpdate_stB,
      SCKAScheme.sendAUpdate_keyA_none, SCKAScheme.sendAUpdate_keyB]
    rw [pairFailure_advance hA hB ecEk kp hgate.2]
    simp only [trackedScore, Bool.false_eq_true, if_false, failurePotential_eq_pairA,
      SCKAScheme.sendAUpdate_stA, SCKAScheme.sendAUpdate_stB, SCKAScheme.sendAUpdate_keyA_none,
      SCKAScheme.sendAUpdate_keyB]
    exact pairPotential_advance hA hB ecEk kp hgate.2
  · by_cases henc : s.stA.res.resEpoch + Role.A.offset ∈ s.stA.ack.ekRec ∧
        s.stA.res.resEpoch ∉ s.stA.ack.ctRec ∧ s.stA.res.ct = none ∧
        s.stA.res.resEpoch ∈ s.stA.ack.ekRec
    · obtain ⟨hacked, hnot, hct, hpeerAck⟩ := henc
      obtain ⟨pk, hpk⟩ := Option.isSome_iff_exists.mp (hA.ekRec_res _ hpeerAck hA.res_parity)
      obtain ⟨sk, -, hdk, hbefore, hafter⟩ := pairPotential_encaps hA hB ecCt hnot hct hpk
      rw [send_eq_encaps .A kem ecEk ecCt s.stA hnot hacked hct hpeerAck hpk, bind_assoc]
      simp only [pure_bind]
      refine (expectedPayoff_encaps_le hDet pk sk _ _
        (pendingPotential hDet s.stA s.stB s.keyB) ?_).trans ?_
      · intro ck
        rw [sendAOutcome_some]
        have h1 : (encapsSend (K := K) .A ecCt s.stA ck).1 =
            some (s.stA.res.resEpoch.toNat, ck.2) := rfl
        simp only [h1, kemFailure_eq_pairA, SCKAScheme.sendAUpdate_stA, SCKAScheme.sendAUpdate_stB,
          SCKAScheme.sendAUpdate_keyA_some, SCKAScheme.sendAUpdate_keyB]
        rw [pairFailure_encaps ecCt ck sk hdk hfailA]
        simp only [trackedScore, decide_eq_true_eq, failurePotential_eq_pairA,
          SCKAScheme.sendAUpdate_stA, SCKAScheme.sendAUpdate_stB, SCKAScheme.sendAUpdate_keyA_some,
          SCKAScheme.sendAUpdate_keyB]
        split_ifs
        · rfl
        · exact hafter ck
      · rw [hbefore]
        exact le_self_add (α := ℝ≥0∞)
    · refine expectedPayoff_le_const_of_support _ _ _
        (by rw [← trackedBiKem_sendA_run kem hDet ecEk ecCt leak s]; exact probFailure_eq_zero) ?_
      intro z hz
      obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
      obtain rfl := eq_of_mem_support_pure _ hz
      rcases out with _ | ⟨key?, ρ, tsnd, stA'⟩
      · simp [sendAOutcome, trackedScore, hfail, failurePotential_eq_pairA]
      · obtain ⟨rfl, hres⟩ := send_plain_of_not kem ecEk ecCt hgate henc hout
        obtain ⟨hpot, hfl⟩ := pair_plain kem ecEk ecCt hout hres
        rw [sendAOutcome_some]
        simp only [kemFailure_eq_pairA, SCKAScheme.sendAUpdate_stA, SCKAScheme.sendAUpdate_stB,
          SCKAScheme.sendAUpdate_keyA_none, SCKAScheme.sendAUpdate_keyB]
        rw [hfl, hfailA]
        simp only [trackedScore, Bool.false_eq_true, if_false, failurePotential_eq_pairA,
          SCKAScheme.sendAUpdate_stA, SCKAScheme.sendAUpdate_stB, SCKAScheme.sendAUpdate_keyA_none,
          SCKAScheme.sendAUpdate_keyB]
        rw [hpot]
        exact le_self_add

open SCKAScheme.sckaCorrectnessSpec in
/-- From `(s, false)` with `s` satisfying the main invariant and not bad, `SendB` raises the
expected tracked score by at most `ε`. -/
theorem tracked_sendB_score_le
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false) :
    expectedPayoff ((trackedBiKem kem hDet ecEk ecCt leak OSendB).run (s, false))
        (fun z => trackedScore hDet z.2) ≤
      trackedScore hDet (s, false) + kem.correctnessError ProbCompRuntime.probComp := by
  obtain ⟨-, T, hA, hB⟩ := hs
  have hfailB : pairFailure hDet s.stB s.stA s.keyB s.keyA = false := by
    rwa [kemFailure_eq_pairB] at hfail
  rw [trackedBiKem_sendB_run, trackedScore_false, failurePotential_eq_pairB]
  by_cases hgate : s.stB.req.ek = none ∧ s.stB.res.resEpoch ∈ s.stB.ack.ctRec ∧
      s.stB.res.resEpoch + Role.B.offset ∈ s.stB.ack.ctRec
  · obtain ⟨hfresh, -⟩ := advance_prereqs hB hA hgate.2
    rw [send_eq_advance .B kem ecEk ecCt s.stB hgate.1 hgate.2 hfresh, bind_assoc]
    simp only [pure_bind]
    apply expectedPayoff_keygen_le hDet _ _ (pairPotential hDet s.stB s.stA s.keyB s.keyA)
    intro kp
    rw [sendBOutcome_some]
    have h1 : (advanceSend (K := K) .B ecEk s.stB kp).1 = none := rfl
    simp only [h1, kemFailure_eq_pairB, SCKAScheme.sendBUpdate_stA, SCKAScheme.sendBUpdate_stB,
      SCKAScheme.sendBUpdate_keyB_none, SCKAScheme.sendBUpdate_keyA]
    rw [pairFailure_advance hB hA ecEk kp hgate.2]
    simp only [trackedScore, Bool.false_eq_true, if_false, failurePotential_eq_pairB,
      SCKAScheme.sendBUpdate_stA, SCKAScheme.sendBUpdate_stB, SCKAScheme.sendBUpdate_keyB_none,
      SCKAScheme.sendBUpdate_keyA]
    exact pairPotential_advance hB hA ecEk kp hgate.2
  · by_cases henc : s.stB.res.resEpoch + Role.B.offset ∈ s.stB.ack.ekRec ∧
        s.stB.res.resEpoch ∉ s.stB.ack.ctRec ∧ s.stB.res.ct = none ∧
        s.stB.res.resEpoch ∈ s.stB.ack.ekRec
    · obtain ⟨hacked, hnot, hct, hpeerAck⟩ := henc
      obtain ⟨pk, hpk⟩ := Option.isSome_iff_exists.mp (hB.ekRec_res _ hpeerAck hB.res_parity)
      obtain ⟨sk, -, hdk, hbefore, hafter⟩ := pairPotential_encaps hB hA ecCt hnot hct hpk
      rw [send_eq_encaps .B kem ecEk ecCt s.stB hnot hacked hct hpeerAck hpk, bind_assoc]
      simp only [pure_bind]
      refine (expectedPayoff_encaps_le hDet pk sk _ _
        (pendingPotential hDet s.stB s.stA s.keyA) ?_).trans ?_
      · intro ck
        rw [sendBOutcome_some]
        have h1 : (encapsSend (K := K) .B ecCt s.stB ck).1 =
            some (s.stB.res.resEpoch.toNat, ck.2) := rfl
        simp only [h1, kemFailure_eq_pairB, SCKAScheme.sendBUpdate_stA, SCKAScheme.sendBUpdate_stB,
          SCKAScheme.sendBUpdate_keyB_some, SCKAScheme.sendBUpdate_keyA]
        rw [pairFailure_encaps ecCt ck sk hdk hfailB]
        simp only [trackedScore, decide_eq_true_eq, failurePotential_eq_pairB,
          SCKAScheme.sendBUpdate_stA, SCKAScheme.sendBUpdate_stB, SCKAScheme.sendBUpdate_keyB_some,
          SCKAScheme.sendBUpdate_keyA]
        split_ifs
        · rfl
        · exact hafter ck
      · rw [hbefore]
        exact le_self_add (α := ℝ≥0∞)
    · refine expectedPayoff_le_const_of_support _ _ _
        (by rw [← trackedBiKem_sendB_run kem hDet ecEk ecCt leak s]; exact probFailure_eq_zero) ?_
      intro z hz
      obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
      obtain rfl := eq_of_mem_support_pure _ hz
      rcases out with _ | ⟨key?, ρ, tsnd, stB'⟩
      · simp [sendBOutcome, trackedScore, hfail, failurePotential_eq_pairB]
      · obtain ⟨rfl, hres⟩ := send_plain_of_not kem ecEk ecCt hgate henc hout
        obtain ⟨hpot, hfl⟩ := pair_plain kem ecEk ecCt hout hres
        rw [sendBOutcome_some]
        simp only [kemFailure_eq_pairB, SCKAScheme.sendBUpdate_stA, SCKAScheme.sendBUpdate_stB,
          SCKAScheme.sendBUpdate_keyB_none, SCKAScheme.sendBUpdate_keyA]
        rw [hfl, hfailB]
        simp only [trackedScore, Bool.false_eq_true, if_false, failurePotential_eq_pairB,
          SCKAScheme.sendBUpdate_stA, SCKAScheme.sendBUpdate_stB, SCKAScheme.sendBUpdate_keyB_none,
          SCKAScheme.sendBUpdate_keyA]
        rw [hpot]
        exact le_self_add

/-- From every tracked state satisfying `J`, one query raises the expected tracked score by at
most `ε` if it is a send query, and does not raise it otherwise. -/
theorem tracked_step_score_le (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (p : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) × Bool)
    (hp : trackedInv (GameInv kem ecEk ecCt) (kemFailure hDet) p) :
    expectedPayoff ((trackedBiKem kem hDet ecEk ecCt leak t).run p)
        (fun z => trackedScore hDet z.2) ≤
      trackedScore hDet p +
        if SCKAScheme.isSendQuery t then kem.correctnessError ProbCompRuntime.probComp else 0 := by
  obtain ⟨s, b⟩ := p
  rcases b with _ | _
  · rcases hp with h | ⟨hs, hfail⟩
    · exact absurd h Bool.false_ne_true
    · by_cases hsend : SCKAScheme.isSendQuery t = true
      · rw [if_pos hsend]
        rcases t with (((m | ⟨⟩) | ⟨⟩) | m) | m
        · exact absurd hsend (by simp [SCKAScheme.isSendQuery])
        · exact tracked_sendA_score_le kem hDet ecEk ecCt leak s hs hfail
        · exact tracked_sendB_score_le kem hDet ecEk ecCt leak s hs hfail
        · exact absurd hsend (by simp [SCKAScheme.isSendQuery])
        · exact absurd hsend (by simp [SCKAScheme.isSendQuery])
      · rw [if_neg hsend, add_zero]
        exact tracked_nonSend_score_le kem hDet ecEk ecCt hEk hCt leak t hsend s hs hfail
  · exact tracked_step_score_le_of_flag kem hDet ecEk ecCt leak t s _

end Oracle

end oppBiKemCKA
