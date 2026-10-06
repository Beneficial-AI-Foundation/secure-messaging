/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness.Tracked
import SecureMessaging.SCKA.OppBiKEM.Correctness.Quantitative.Core
import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant.Game
import SecureMessaging.SCKA.OppBiKEM.Correctness.PublicKeyEpochHistory
import SecureMessaging.SCKA.OppBiKEM.Correctness.RoleParity

/-!
# Opp-BiKEM — the failure score does not grow on non-send queries

A receive changes neither the failure potential nor the failure flag: it removes a secret key
only for an epoch the peer has already encapsulated to (whose pending term is `0`), installs a
peer key only for the epoch whose own copy is still retained (same public key), and clears
the own public key only once the peer holds a copy (same public key again). The uniform
oracle changes nothing. Hence every non-send query has expected score at most its initial
score (`tracked_nonSend_score_le`), and a query from a flagged state keeps the score at `1`
(`tracked_step_score_le_of_flag`).
-/

open OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

section Local

variable {kem : KEMScheme ProbComp K PK SK C} {hDet : kem.DeterministicDecaps}
  {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
  {T : Transcript kem} {roleR : Role} {stR stS : State PK SK C Sym}
  {msgsR msgsS : ℕ → Option (Message Sym × ℕ)} {keyR keyS : ℕ → Option K}
  {tcurR tcurS : ℕ}

/-- A successful receive leaves the retained ciphertext in place or clears it. -/
theorem recv_ct_eq_or_none [DecidableEq Sym] (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (stR' : State PK SK C Sym)
    (hout : recv roleR kem hDet ecEk ecCt stR ρ = some (key?, trcv, stR')) :
    stR'.res.ct = stR.res.ct ∨ stR'.res.ct = none := by
  have hfin : ∀ (q : ℤ) (ekPeer' : ℤ → Option PK) (dk' : List (ℤ × SK))
      (chunks' : Finset (ℕ × Sym)) (ack' : Acknowledgements),
      (recvFinish roleR stR q ekPeer' dk' chunks' ack').res.ct = stR.res.ct ∨
        (recvFinish roleR stR q ekPeer' dk' chunks' ack').res.ct = none := by
    intro q ekPeer' dk' chunks' ack'
    simp only [recvFinish]
    split_ifs <;> simp
  rw [recv_eq_recvSpec] at hout
  unfold recvSpec at hout
  dsimp only at hout
  split_ifs at hout with h1 h2 h3
  · simp only [Option.some.injEq, Prod.mk.injEq] at hout
    obtain ⟨-, -, rfl⟩ := hout
    exact Or.inl rfl
  · rcases hd : (insertChunkAndDecode ecEk stR.req.receivedChunks ρ.ch).2 with _ | pk <;>
      simp only [hd, Option.some.injEq, Prod.mk.injEq] at hout <;>
      obtain ⟨-, -, rfl⟩ := hout <;>
      exact hfin _ _ _ _ _
  · rcases hd : (insertChunkAndDecode ecCt stR.req.receivedChunks ρ.ch).2 with _ | c <;>
      simp only [hd] at hout
    · simp only [Option.some.injEq, Prod.mk.injEq] at hout
      obtain ⟨-, -, rfl⟩ := hout
      exact hfin _ _ _ _ _
    · rcases hl : stR.req.dk.lookup (recvReq stR ρ) with _ | sk <;>
        simp only [hl, Option.bind_eq_bind, Option.bind] at hout
      · exact absurd hout (by simp)
      · rcases hk : hDet.decapsDet sk c with _ | k <;> simp only [hk] at hout
        · exact absurd hout (by simp)
        · simp only [Option.some.injEq, Prod.mk.injEq] at hout
          obtain ⟨-, -, rfl⟩ := hout
          exact hfin _ _ _ _ _
  · simp only [Option.some.injEq, Prod.mk.injEq] at hout
    obtain ⟨-, -, rfl⟩ := hout
    exact hfin _ _ _ _ _

variable (hR : PartyInv roleR ecEk ecCt T stR stS msgsR keyR keyS tcurR)
  (hS : PartyInv roleR.peer ecEk ecCt T stS stR msgsS keyS keyR tcurS)

include hR hS

/-- The receiver's pending potential is unchanged by a receive. -/
theorem pendingPotential_recv_receiver [DecidableEq K] [DecidableEq Sym]
    {n : ℕ} {ρ : Message Sym} {tsnd : ℕ} (_hmsg : msgsS n = some (ρ, tsnd))
    (key? : Option (ℕ × K)) (trcv : ℕ) (stR' : State PK SK C Sym)
    (hout : recv roleR kem hDet ecEk ecCt stR ρ = some (key?, trcv, stR'))
    {tcur' : ℕ} (hR' : PartyInv roleR ecEk ecCt T stR' stS msgsR (recordKey keyR key?) keyS tcur') :
    pendingPotential hDet stR' stS keyS = pendingPotential hDet stR stS keyS := by
  have hfacts := recv_success_state_facts roleR kem hDet ecEk ecCt stR ρ key? trcv stR' hout
  obtain ⟨-, hres, -, -, -, -, -, -, hdknone⟩ := hfacts
  have hek := recv_local_publicKey_eq_or_none roleR kem hDet ecEk ecCt stR ρ key? trcv stR' hout
  -- a retained key's term is unchanged: the peer's copy or the own copy supply the same key
  have hterm : ∀ e sk, (e, sk) ∈ stR'.req.dk → (e, sk) ∈ stR.req.dk →
      pendingTerm hDet stR' stS keyS (e, sk) = pendingTerm hDet stR stS keyS (e, sk) := by
    intro e sk hmem' hmem
    rcases hek with hek | hek
    · exact pendingTerm_congr hDet (e, sk) rfl rfl hek
    · obtain ⟨-, -, -, -, pk, hkp⟩ := hR'.dk_T e sk hmem'
      have he : e = stR'.res.resEpoch + roleR.offset := by
        rcases hR'.dk_shape with hnil | ⟨sk', hone⟩
        · rw [hnil] at hmem'; cases hmem'
        · rw [hone] at hmem'
          simp only [List.mem_singleton, Prod.mk.injEq] at hmem'
          exact hmem'.1
      rcases hR'.ek_acked hek with hnone | hack
      · rw [← he, hkp] at hnone; cases hnone
      · rw [← he] at hack
        have hsome := hR'.ekRec_req e hack (hR'.dk_T e sk hmem').1
        obtain ⟨pk', hpk'⟩ := Option.isSome_iff_exists.mp hsome
        exact pendingTerm_congr_of_ekPeer hDet (e, sk) rfl hpk' hpk'
  rcases key? with _ | ⟨tI, k⟩
  · have hdk : stR'.req.dk = stR.req.dk := hdknone rfl
    unfold pendingPotential
    rw [hdk]
    congr 1
    apply List.map_congr_left
    intro p hp
    obtain ⟨e, sk⟩ := p
    exact hterm e sk (by rw [hdk]; exact hp) hp
  · obtain ⟨-, -, -, -, hin, hfilter, -, -, -⟩ :=
      recv_emitted_key_facts roleR kem hDet ecEk ecCt stR ρ tI k trcv stR' hout
    rcases hR.dk_shape with hnil | ⟨sk, hone⟩
    · rw [pendingPotential_nil hDet (by rw [hfilter, hnil]; rfl), pendingPotential_nil hDet hnil]
    · -- the single retained key is the decapsulated one, and its term was already `0`
      have hq : stR.res.resEpoch + roleR.offset = stR'.req.reqEpoch := by
        obtain ⟨-, -, -, -, -, -, -, -, sk', c, hlk, -, -⟩ :=
          recv_emitted_key_facts roleR kem hDet ecEk ecCt stR ρ tI k trcv stR' hout
        rw [hone] at hlk
        by_contra hne
        have hne' : (stR'.req.reqEpoch == stR.res.resEpoch + roleR.offset) = false :=
          beq_eq_false_iff_ne.mpr (fun h => hne h.symm)
        simp [List.lookup, hne'] at hlk
      have hdk' : stR'.req.dk = [] := by
        rw [hfilter, hone]
        simp [hq]
      rw [pendingPotential_nil hDet hdk', pendingPotential_singleton hDet hone]
      refine (pendingTerm_of_key_some hDet ?_).symm
      -- the peer has encapsulated to the decapsulated epoch
      have henc := hR'.ctRec_req_enc _ hin (by
          have := hR.dk_T _ sk (by rw [hone]; exact List.mem_singleton_self _)
          rw [hq] at this; exact this.2.1) hR'.req_parity
      obtain ⟨⟨c, k'⟩, hck⟩ := Option.isSome_iff_exists.mp henc
      have hkey := peerKey_eq_key_of_dk hR hS _ sk (by rw [hone]; exact List.mem_singleton_self _)
      rw [hkey, EpochTranscript.key, hq, hck]
      simp

/-- The peer's pending potential is unchanged by the receiver's receive. -/
theorem pendingPotential_recv_peer [DecidableEq K] [DecidableEq Sym] {ρ : Message Sym}
    (key? : Option (ℕ × K)) (trcv : ℕ) (stR' : State PK SK C Sym)
    (hout : recv roleR kem hDet ecEk ecCt stR ρ = some (key?, trcv, stR'))
    {tcur' : ℕ} (hR' : PartyInv roleR ecEk ecCt T stR' stS msgsR (recordKey keyR key?) keyS tcur') :
    pendingPotential hDet stS stR' (recordKey keyR key?) = pendingPotential hDet stS stR keyR := by
  rcases hS.dk_shape with hnil | ⟨sk, hone⟩
  · rw [pendingPotential_nil hDet hnil, pendingPotential_nil hDet hnil]
  rw [pendingPotential_singleton hDet hone, pendingPotential_singleton hDet hone]
  set e := stS.res.resEpoch + roleR.peer.offset with he
  have hmem : (e, sk) ∈ stS.req.dk := by rw [hone]; exact List.mem_singleton_self _
  obtain ⟨hpar, hpos, -, -, pk, hkp⟩ := hS.dk_T e sk hmem
  -- the receiver's key table at the peer's key epoch is unchanged
  have hkey : recordKey keyR key? e.toNat = keyR e.toNat := by
    rcases key? with _ | ⟨tI, k⟩
    · rfl
    · obtain ⟨-, -, htI, -, -, -, -, -, -⟩ :=
        recv_emitted_key_facts roleR kem hDet ecEk ecCt stR ρ tI k trcv stR' hout
      have hqpar := hR'.req_parity
      have hqpos : 0 < stR'.req.reqEpoch := by
        have := hR'.dk_T  -- unused; positivity comes from the emitted key's epoch below
        obtain ⟨-, -, -, -, hin, -, -, -, sk', c, hlk, -, -⟩ :=
          recv_emitted_key_facts roleR kem hDet ecEk ecCt stR ρ tI k trcv stR' hout
        have hmem' : (stR'.req.reqEpoch, sk') ∈ stR.req.dk := by
          obtain ⟨before, after, hlist, -⟩ := List.lookup_eq_some_iff.mp hlk
          simp only [hlist, List.mem_append, List.mem_cons, true_or, or_true]
        exact (hR.dk_T _ sk' hmem').2.1
      have hne : e.toNat ≠ tI := by
        rw [htI]
        intro h
        have h1 := Int.toNat_of_nonneg (le_of_lt hpos)
        have h2 := Int.toNat_of_nonneg (le_of_lt hqpos)
        have : e = stR'.req.reqEpoch := by omega
        rw [this] at hpar
        cases roleR <;> simp only [Role.peer, Role.reqParity] at hpar hqpar <;> omega
      simp only [recordKey, Function.update_of_ne hne]
  rcases recv_peerKeys_origin roleR kem hDet ecEk ecCt stR ρ key? trcv stR' hout e with heq | hpe
  · exact pendingTerm_congr hDet (e, sk) hkey heq rfl
  · -- the receiver may have installed the peer's key at exactly this epoch
    cases hbefore : stR.res.ekPeer e with
    | some pk₀ =>
        have hstable := recv_peerKeys_stable roleR kem hDet ecEk ecCt stR ρ key? trcv stR' hout e
          (by rw [hbefore]; rfl)
        exact pendingTerm_congr hDet (e, sk) hkey hstable rfl
    | none =>
        by_cases hk : keyR e.toNat = none
        · -- the own copy is retained, and the installed copy is the same public key
          have hek : stS.req.ek = some pk := by
            cases hx : stS.req.ek with
            | some pk' =>
                obtain ⟨sk', hkp'⟩ := hS.ek_T pk' hx
                rw [← he, hkp] at hkp'
                simp only [Option.some.injEq, Prod.mk.injEq] at hkp'
                rw [hkp'.1]
            | none =>
                exfalso
                rcases hS.ek_acked hx with hnone | hack
                · rw [← he, hkp] at hnone; cases hnone
                · rw [← he] at hack
                  have := hS.ekRec_req e hack hpar
                  rw [hbefore] at this; cases this
          have hbefore' : pendingTerm hDet stS stR keyR (e, sk) =
              keypairFailure kem hDet pk sk :=
            pendingTerm_of_ek hDet hk hbefore hek
          rw [hbefore']
          cases hafter : stR'.res.ekPeer e with
          | none => exact pendingTerm_of_ek hDet (by rw [hkey]; exact hk) hafter hek
          | some pk' =>
              obtain ⟨sk', hkp'⟩ := hR'.ekPeer_T e pk' hafter
              rw [hkp] at hkp'
              simp only [Option.some.injEq, Prod.mk.injEq] at hkp'
              rw [pendingTerm_of_ekPeer hDet (by rw [hkey]; exact hk) hafter, hkp'.1]
        · rw [pendingTerm_of_key_some hDet (peerKey := recordKey keyR key?)
              (by rw [hkey]; exact hk),
            pendingTerm_of_key_some hDet (peerKey := keyR) hk]

/-- The failure flag stays clear through a receive. -/
theorem kemFailure_recv [DecidableEq K] [DecidableEq Sym] {ρ : Message Sym}
    (key? : Option (ℕ × K)) (trcv : ℕ) (stR' : State PK SK C Sym)
    (hout : recv roleR kem hDet ecEk ecCt stR ρ = some (key?, trcv, stR'))
    {tcur' : ℕ} (hR' : PartyInv roleR ecEk ecCt T stR' stS msgsR (recordKey keyR key?) keyS tcur')
    (hfailR : kemFailureAt hDet stR stS keyS = false)
    (hfailS : kemFailureAt hDet stS stR keyR = false) :
    kemFailureAt hDet stR' stS keyS = false ∧
      kemFailureAt hDet stS stR' (recordKey keyR key?) = false := by
  obtain ⟨-, hres, -, -, -, -, -, -, hdknone⟩ :=
    recv_success_state_facts roleR kem hDet ecEk ecCt stR ρ key? trcv stR' hout
  refine ⟨?_, ?_⟩
  · -- the receiver's secret keys only shrink
    rcases hR'.dk_shape with hnil | ⟨sk, hone⟩
    · exact kemFailureAt_eq_false_of hDet (Or.inl (by rw [hnil]; rfl))
    · have hsub : stR'.req.dk = stR.req.dk := by
        rcases key? with _ | ⟨tI, k⟩
        · exact hdknone rfl
        · obtain ⟨-, -, -, -, -, hfilter, -, -, -⟩ :=
            recv_emitted_key_facts roleR kem hDet ecEk ecCt stR ρ tI k trcv stR' hout
          exfalso
          -- after a decapsulation the key list is empty
          rcases hR.dk_shape with hnil₀ | ⟨sk₀, hone₀⟩
          · rw [hfilter, hnil₀] at hone; cases hone
          · obtain ⟨-, -, -, -, -, -, -, -, sk', c, hlk, -, -⟩ :=
              recv_emitted_key_facts roleR kem hDet ecEk ecCt stR ρ tI k trcv stR' hout
            rw [hone₀] at hlk
            have hq : stR.res.resEpoch + roleR.offset = stR'.req.reqEpoch := by
              by_contra hne
              have hne' : (stR'.req.reqEpoch == stR.res.resEpoch + roleR.offset) = false :=
                beq_eq_false_iff_ne.mpr (fun h => hne h.symm)
              simp [List.lookup, hne'] at hlk
            rw [hfilter, hone₀] at hone
            simp [hq] at hone
      rw [← hfailR]
      exact kemFailureAt_congr hDet rfl (by rw [hsub]) rfl rfl
  · rcases recv_ct_eq_or_none ρ key? trcv stR' hout with hct | hct
    · rw [← hfailS]
      refine kemFailureAt_congr hDet hres rfl hct ?_
      -- the receiver writes its table only at its requester parity, the peer reads its
      -- responder epoch
      rcases key? with _ | ⟨tI, k⟩
      · rfl
      · obtain ⟨-, -, htI, -, -, -, -, -, sk', c, hlk, -, -⟩ :=
          recv_emitted_key_facts roleR kem hDet ecEk ecCt stR ρ tI k trcv stR' hout
        have hmem' : (stR'.req.reqEpoch, sk') ∈ stR.req.dk := by
          obtain ⟨before, after, hlist, -⟩ := List.lookup_eq_some_iff.mp hlk
          simp only [hlist, List.mem_append, List.mem_cons, true_or, or_true]
        obtain ⟨hqpar, hqpos, -, -, -⟩ := hR.dk_T _ sk' hmem'
        have hrespar := hR.res_parity
        have hlow := hR.res_lower
        have hne : stR.res.resEpoch.toNat ≠ tI := by
          rw [htI]
          intro h
          by_cases hneg : stR.res.resEpoch ≤ 0
          · have : stR.res.resEpoch.toNat = 0 := Int.toNat_eq_zero.mpr hneg
            rw [this] at h
            have := Int.toNat_of_nonneg (le_of_lt hqpos)
            omega
          · have h1 := Int.toNat_of_nonneg (le_of_lt (not_le.mp hneg))
            have h2 := Int.toNat_of_nonneg (le_of_lt hqpos)
            have : stR.res.resEpoch = stR'.req.reqEpoch := by omega
            rw [this] at hrespar
            cases roleR <;> simp only [Role.reqParity, Role.resParity] at hrespar hqpar <;> omega
        simp only [recordKey, Function.update_of_ne hne]
    · exact kemFailureAt_eq_false_of hDet (Or.inr (Or.inl hct))

end Local

/-! ### The step bounds for non-send queries -/

section Step

variable [DecidableEq K] [DecidableEq Sym]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)

/-- The tracked correctness game of Opp-BiKEM. -/
abbrev trackedBiKem :=
  trackedImpl (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) (kemFailure hDet)

omit [DecidableEq Sym] in
/-- When the flag is clear, the transcript consistent with the state is decapsulation-ready
for both parties. -/
theorem decapsReady_of_noFailure
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hfail : kemFailure hDet s = false) (T : Transcript kem)
    (hA : PartyInv .A ecEk ecCt T s.stA s.stB s.msgA s.keyA s.keyB s.tcurA)
    (hB : PartyInv .B ecEk ecCt T s.stB s.stA s.msgB s.keyB s.keyA s.tcurB) :
    DecapsReady .A hDet T s.stA ∧ DecapsReady .B hDet T s.stB := by
  obtain ⟨hfA, hfB⟩ := (kemFailure_eq_false_iff hDet s).mp hfail
  exact ⟨fun q hq hp => decaps_of_noFailure hA hB hfA q hq hp,
    fun q hq hp => decaps_of_noFailure hB hA hfB q hq hp⟩

include hEk hCt in
/-- One step from an unflagged invariant state keeps the invariant (the step hypothesis of
`trackedImpl_preserves`). -/
theorem gameInv_step_of_noFailure (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false) :
    ∀ z ∈ support ((SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak) t).run s),
      GameInv kem ecEk ecCt z.2 :=
  gameInv_step_of kem hDet ecEk ecCt hEk hCt leak t s hs
    (fun T hA hB => decapsReady_of_noFailure kem hDet ecEk ecCt s hfail T hA hB)

/-- From a flagged state the score stays `1`. -/
theorem tracked_step_score_le_of_flag (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (ε : ℝ≥0∞) :
    expectedPayoff ((trackedBiKem kem hDet ecEk ecCt leak t).run (s, true))
        (fun z => trackedScore hDet z.2) ≤
      trackedScore hDet (s, true) + ε := by
  rw [trackedScore_true]
  refine le_add_right ?_
  refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero ?_
  intro z hz
  change z ∈ support
    ((SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak) t).run s >>=
      fun y => pure (y.1, (y.2, true || kemFailure hDet y.2))) at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, -, hz⟩ := hz
  simp only [mem_support_pure_iff] at hz
  subst hz
  simp [trackedScore]

include hEk hCt in
/-- A receive by `A` from an unflagged invariant state leaves potential and flag unchanged. -/
theorem recvA_score_eq (n : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false)
    (y : Option (ℕ × Option ℕ) × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K
      (Message Sym))
    (hy : y ∈ support ((SCKAScheme.oracleRecvA (scheme kem hDet ecEk ecCt leak) n).run s)) :
    failurePotential hDet y.2 = failurePotential hDet s ∧ kemFailure hDet y.2 = false := by
  obtain ⟨hcorrect, T, hA, hB⟩ := hs
  obtain ⟨hfA, hfB⟩ := (kemFailure_eq_false_iff hDet s).mp hfail
  rcases SCKAScheme.oracleRecvA_run_cases _ n s y hy with ⟨-, rfl⟩ | ⟨ρ, tsnd, hmsg, hrecv, rfl⟩ |
    ⟨ρ, tsnd, key?, trcv, stA', hmsg, hrecv, rfl⟩
  · exact ⟨rfl, hfail⟩
  · exact ⟨rfl, hfail⟩
  · have hrecv' : recv .A kem hDet ecEk ecCt s.stA ρ = some (key?, trcv, stA') := hrecv
    have hready := decapsReady_of_noFailure kem hDet ecEk ecCt s hfail T hA hB
    obtain ⟨-, hall⟩ := partyInv_recv_step hA hB hmsg hEk hCt
      (fun hq => hready.1 _ hq (recv_tRes_parity (roleR := .A) hB hmsg))
    obtain ⟨-, -, -, hA', -⟩ := hall key? trcv stA' hrecv'
    have h1 := pendingPotential_recv_receiver hA hB hmsg key? trcv stA' hrecv' hA'
    have h2 := pendingPotential_recv_peer hA hB key? trcv stA' hrecv' hA'
    have h3 := kemFailure_recv hA hB key? trcv stA' hrecv' hA' hfA hfB
    refine ⟨?_, ?_⟩
    · rcases key? with _ | ⟨tI, k⟩ <;>
        simp only [failurePotential, SCKAScheme.applyRecvA] <;>
        simp only [recordKey] at h1 h2 <;>
        rw [h1, h2]
    · rcases key? with _ | ⟨tI, k⟩ <;>
        simp only [kemFailure, SCKAScheme.applyRecvA] <;>
        simp only [recordKey] at h3 <;>
        simp [h3.1, h3.2]

include hEk hCt in
/-- A receive by `B` from an unflagged invariant state leaves potential and flag unchanged. -/
theorem recvB_score_eq (n : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false)
    (y : Option (ℕ × Option ℕ) × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K
      (Message Sym))
    (hy : y ∈ support ((SCKAScheme.oracleRecvB (scheme kem hDet ecEk ecCt leak) n).run s)) :
    failurePotential hDet y.2 = failurePotential hDet s ∧ kemFailure hDet y.2 = false := by
  obtain ⟨hcorrect, T, hA, hB⟩ := hs
  obtain ⟨hfA, hfB⟩ := (kemFailure_eq_false_iff hDet s).mp hfail
  rcases SCKAScheme.oracleRecvB_run_cases _ n s y hy with ⟨-, rfl⟩ | ⟨ρ, tsnd, hmsg, hrecv, rfl⟩ |
    ⟨ρ, tsnd, key?, trcv, stB', hmsg, hrecv, rfl⟩
  · exact ⟨rfl, hfail⟩
  · exact ⟨rfl, hfail⟩
  · have hrecv' : recv .B kem hDet ecEk ecCt s.stB ρ = some (key?, trcv, stB') := hrecv
    have hready := decapsReady_of_noFailure kem hDet ecEk ecCt s hfail T hA hB
    obtain ⟨-, hall⟩ := partyInv_recv_step hB hA hmsg hEk hCt
      (fun hq => hready.2 _ hq (recv_tRes_parity (roleR := .B) hA hmsg))
    obtain ⟨-, -, -, hB', -⟩ := hall key? trcv stB' hrecv'
    have h1 := pendingPotential_recv_receiver hB hA hmsg key? trcv stB' hrecv' hB'
    have h2 := pendingPotential_recv_peer hB hA key? trcv stB' hrecv' hB'
    have h3 := kemFailure_recv hB hA key? trcv stB' hrecv' hB' hfB hfA
    refine ⟨?_, ?_⟩
    · rcases key? with _ | ⟨tI, k⟩ <;>
        simp only [failurePotential, SCKAScheme.applyRecvB] <;>
        simp only [recordKey] at h1 h2 <;>
        rw [h1, h2]
    · rcases key? with _ | ⟨tI, k⟩ <;>
        simp only [kemFailure, SCKAScheme.applyRecvB] <;>
        simp only [recordKey] at h3 <;>
        simp [h3.1, h3.2]

include hEk hCt in
/-- From an unflagged invariant state, every non-send query keeps the expected score at most
its initial value. -/
theorem tracked_nonSend_score_le (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (hNonSend : ¬ SCKAScheme.IsSendQuery t)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false) :
    expectedPayoff ((trackedBiKem kem hDet ecEk ecCt leak t).run (s, false))
        (fun z => trackedScore hDet z.2) ≤
      trackedScore hDet (s, false) := by
  refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero ?_
  intro z hz
  change z ∈ support
    ((SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak) t).run s >>=
      fun y => pure (y.1, (y.2, false || kemFailure hDet y.2))) at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  simp only [mem_support_pure_iff] at hz
  subst hz
  rw [trackedScore_false]
  rcases t with (((m | ⟨⟩) | ⟨⟩) | m) | m
  · have hy₀ : y ∈ support ((SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K
        (Message Sym) m).run s) := hy
    have hy' : y ∈ Set.range fun a : unifSpec.Range m => (a, s) := by
      simpa [SCKAScheme.oracleUnif] using hy₀
    obtain ⟨r, hr⟩ := Set.mem_range.mp hy'
    subst hr
    simp [trackedScore, hfail]
  · exact absurd (by simp [SCKAScheme.IsSendQuery, SCKAScheme.isSendQuery]) hNonSend
  · exact absurd (by simp [SCKAScheme.IsSendQuery, SCKAScheme.isSendQuery]) hNonSend
  · obtain ⟨h1, h2⟩ := recvA_score_eq kem hDet ecEk ecCt hEk hCt leak m s hs hfail y hy
    simp [trackedScore, h1, h2]
  · obtain ⟨h1, h2⟩ := recvB_score_eq kem hDet ecEk ecCt hEk hCt leak m s hs hfail y hy
    simp [trackedScore, h1, h2]

end Step

end oppBiKemCKA
