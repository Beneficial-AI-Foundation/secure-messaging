/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Tracked

/-!
# Opp-BiKEM — Ideal receive

**Setting.** The *ideal game* `I_b := idealSecurityExp … b adv` is the SCKA security game of
Opp-BiKEM with challenge bit `b` in which each party's receive copies the peer's recorded key
for the received epoch instead of decapsulating (`idealRecover`, `oracleRecvAIdeal`,
`oracleRecvBIdeal`). Its oracles `idealSecurityImpl b` are the security oracles over the ideal
correctness oracles `idealCorrectnessImpl`, with the fixed-bit challenge, the exposure policy
and the honest leaking sends and corruptions.

**Main results.**

- On every state satisfying `GameInv` without current KEM failure, the real and ideal oracles
  have the same query computation (`securityImpl_eq_ideal_of_noFailure`).
- With correct erasure codes, every ideal security query preserves `GameInv`, with no KEM
  correctness and no no-failure premise (`idealSecurityImpl_preservesInv`): the ideal receive
  returns the peer's recorded key, which is the transcript key.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Recovery by the peer's recorded key: ignore the secret key and ciphertext and return the
peer's table entry for the received epoch. -/
def idealRecover (peerKey : ℕ → Option K) : ℤ → SK → C → Option K :=
  fun q _ _ => peerKey q.toNat

/-- The Opp-BiKEM scheme with both receive algorithms replaced. -/
def schemeWithRecv [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (recvA' : StA PK SK C Sym → Message Sym → Option (Option (ℕ × K) × ℕ × StA PK SK C Sym))
    (recvB' : StB PK SK C Sym → Message Sym → Option (Option (ℕ × K) × ℕ × StB PK SK C Sym)) :
    SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) :=
  { scheme kem hDet ecEk ecCt leak with recvA := recvA', recvB := recvB' }

/-- A's ideal receive oracle: A receives with B's recorded keys of the current game state in
place of decapsulation. -/
def oracleRecvAIdeal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  fun n => do
    let s ← get
    SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
      (recvWith .A (idealRecover s.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n

/-- B's ideal receive oracle: B receives with A's recorded keys of the current game state in
place of decapsulation. -/
def oracleRecvBIdeal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  fun n => do
    let s ← get
    SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
      (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover s.keyA) ecEk ecCt)) n

/-- The ideal correctness oracles: the real sends and uniform sampling, with both receives
ideal. -/
def idealCorrectnessImpl [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak) :
    QueryImpl (SCKAScheme.sckaCorrectnessSpec (Message Sym))
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    + SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak)
    + SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak)
    + oracleRecvAIdeal kem hDet ecEk ecCt leak + oracleRecvBIdeal kem hDet ecEk ecCt leak

/-- The ideal security oracles: `securityImplOf` over the ideal correctness oracles, with the
fixed-bit challenge, the Opp-BiKEM exposure policy and the real leaking sends and corruptions. -/
def idealSecurityImpl [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.securityImplOf (idealCorrectnessImpl kem hDet ecEk ecCt leak)
    (SCKAScheme.oracleChall b _ _ _ _) (exposure .A leak) (exposure .B leak)
    (scheme kem hDet ecEk ecCt leak)

/-- The ideal fixed-bit security experiment: the adversary's guess after the ideal security
oracles run from the initial game state. -/
def idealSecurityExp [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (b : Bool) (adv : SecurityAdversary leak Sym) : ProbComp Bool :=
  (simulateQ (idealSecurityImpl kem hDet ecEk ecCt leak b) adv).run'
    (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))

/-! ## Agreement with the real receive -/

/-- On a state satisfying `GameInv` without current KEM failure, A's real receive of a message
recorded in B's log equals the ideal receive with B's recorded keys. -/
lemma recvA_eq_ideal_of_noFailure [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (hCt : ecCt.ec.Correct)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false)
    (n : ℕ) (ρ : Message Sym) (tsnd : ℕ) (hmsg : s.msgB n = some (ρ, tsnd)) :
    recvA kem hDet ecEk ecCt s.stA ρ = recvWith .A (idealRecover s.keyB) ecEk ecCt s.stA ρ := by
  rw [recvA, recv_eq_recvWith]
  apply recvWith_eq_of_agree
  intro sk c hns hbit hqnot' hlk hdec
  obtain ⟨-, T, hA, hB⟩ := hs
  have hq : recvReq s.stA ρ = ρ.tRes := recvReq_eq_tRes hA hB hmsg hns
  rw [hq] at hqnot' hlk
  have hqnot : ρ.tRes ∉ s.stA.ack.ctRec := fun h => hqnot' (recvAck_ctRec_subset _ _ _ h)
  obtain ⟨pk, k, hkp, henc, hkey, -, hpar⟩ :=
    recv_ciphertext_point hA hB hmsg hCt hns hbit hqnot c hdec sk hlk
  have hready := (decapsReady_of_noFailure kem hDet ecEk ecCt s hfail T hA hB).1
  change hDet.decapsDet sk c = s.keyB (recvReq s.stA ρ).toNat
  rw [hq, hready ρ.tRes hqnot hpar pk sk c k hkp henc, hkey]

/-- On a state satisfying `GameInv` without current KEM failure, B's real receive of a message
recorded in A's log equals the ideal receive with A's recorded keys. -/
lemma recvB_eq_ideal_of_noFailure [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (hCt : ecCt.ec.Correct)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false)
    (n : ℕ) (ρ : Message Sym) (tsnd : ℕ) (hmsg : s.msgA n = some (ρ, tsnd)) :
    recvB kem hDet ecEk ecCt s.stB ρ = recvWith .B (idealRecover s.keyA) ecEk ecCt s.stB ρ := by
  rw [recvB, recv_eq_recvWith]
  apply recvWith_eq_of_agree
  intro sk c hns hbit hqnot' hlk hdec
  obtain ⟨-, T, hA, hB⟩ := hs
  have hq : recvReq s.stB ρ = ρ.tRes := recvReq_eq_tRes hB hA hmsg hns
  rw [hq] at hqnot' hlk
  have hqnot : ρ.tRes ∉ s.stB.ack.ctRec := fun h => hqnot' (recvAck_ctRec_subset _ _ _ h)
  obtain ⟨pk, k, hkp, henc, hkey, -, hpar⟩ :=
    recv_ciphertext_point hB hA hmsg hCt hns hbit hqnot c hdec sk hlk
  have hready := (decapsReady_of_noFailure kem hDet ecEk ecCt s hfail T hA hB).2
  change hDet.decapsDet sk c = s.keyA (recvReq s.stB ρ).toNat
  rw [hq, hready ρ.tRes hqnot hpar pk sk c k hkp henc, hkey]

/-- On a state satisfying `GameInv` without current KEM failure, A's real and ideal receive
oracles have the same query computation. -/
lemma oracleRecvA_eq_ideal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (hCt : ecCt.ec.Correct)
    (leak : kem.RandLeak) (n : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false) :
    (SCKAScheme.oracleRecvA (scheme kem hDet ecEk ecCt leak) n).run s =
      (oracleRecvAIdeal kem hDet ecEk ecCt leak n).run s := by
  change (SCKAScheme.oracleRecvA _ n).run s =
    (SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
      (recvWith .A (idealRecover s.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n).run s
  cases hentry : s.msgB n with
  | none => simp [SCKAScheme.oracleRecvA, hentry]
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    have heq := recvA_eq_ideal_of_noFailure kem hDet ecEk ecCt hCt s hs hfail n ρ tsnd hentry
    simp only [SCKAScheme.oracleRecvA, scheme, schemeWithRecv, StateT.run_bind, StateT.run_get,
      pure_bind, hentry, heq]

/-- On a state satisfying `GameInv` without current KEM failure, B's real and ideal receive
oracles have the same query computation. -/
lemma oracleRecvB_eq_ideal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (hCt : ecCt.ec.Correct)
    (leak : kem.RandLeak) (n : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false) :
    (SCKAScheme.oracleRecvB (scheme kem hDet ecEk ecCt leak) n).run s =
      (oracleRecvBIdeal kem hDet ecEk ecCt leak n).run s := by
  change (SCKAScheme.oracleRecvB _ n).run s =
    (SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
      (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover s.keyA) ecEk ecCt)) n).run s
  cases hentry : s.msgA n with
  | none => simp [SCKAScheme.oracleRecvB, hentry]
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    have heq := recvB_eq_ideal_of_noFailure kem hDet ecEk ecCt hCt s hs hfail n ρ tsnd hentry
    simp only [SCKAScheme.oracleRecvB, scheme, schemeWithRecv, StateT.run_bind, StateT.run_get,
      pure_bind, hentry, heq]

/-- On a state satisfying `GameInv` without current KEM failure, every real security query has
the same computation as the ideal one. -/
lemma securityImpl_eq_ideal_of_noFailure [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (hCt : ecCt.ec.Correct)
    (leak : kem.RandLeak) (b : Bool) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hfail : kemFailure hDet s = false) :
    (SCKAScheme.sckaSecurityImpl b (exposure .A leak) (exposure .B leak)
      (scheme kem hDet ecEk ecCt leak) t).run s =
      (idealSecurityImpl kem hDet ecEk ecCt leak b t).run s := by
  rw [SCKAScheme.sckaSecurityImpl_eq_securityImplOf]
  refine SCKAScheme.securityImplOf_run_eq _ _ _ _ _ _ _ s ?_ (fun _ => rfl) t
  intro t
  rcases t with ((((n | u) | u) | n) | n)
  all_goals simp only [idealCorrectnessImpl, SCKAScheme.sckaCorrectnessImpl,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  · exact oracleRecvA_eq_ideal kem hDet ecEk ecCt hCt leak n s hs hfail
  · exact oracleRecvB_eq_ideal kem hDet ecEk ecCt hCt leak n s hs hfail

/-! ## The ideal invariant -/

/-- Every ideal correctness query preserves `GameInv`, with no KEM correctness or no-failure
premise: the ideal receive returns the peer's recorded key, which is the transcript key. -/
lemma gameInv_ideal_step [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) :
    ∀ z ∈ support ((idealCorrectnessImpl kem hDet ecEk ecCt leak t).run s),
      GameInv kem ecEk ecCt z.2 := by
  rcases t with (((n | ⟨⟩) | ⟨⟩) | n) | n
  · exact SCKAScheme.oracleUnif_preservesInv (GameInv kem ecEk ecCt) n s hs
  · exact gameInv_sendA_step kem hDet ecEk ecCt leak s hs
  · exact gameInv_sendB_step kem hDet ecEk ecCt leak s hs
  · intro z hz
    change z ∈ support ((SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
      (recvWith .A (idealRecover s.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n).run s) at hz
    refine gameInv_recvA_step_of kem ecEk ecCt hEk hCt _ _ (fun _ _ => rfl) n s hs ?_ z hz
    intro T hA hB ρ tsnd hmsg hqnot pk sk c k hkp henc
    have hpar := recv_tRes_parity (roleR := .A) hB hmsg
    have hpos : 0 < ρ.tRes := hA.keypair_pos _ hpar (by rw [hkp]; rfl)
    have hparS : ρ.tRes % 2 = Role.B.resParity := by simpa using hpar
    change s.keyB ρ.tRes.toNat = some k
    rw [hB.key_res _ hpos hparS, EpochTranscript.key, henc]
    rfl
  · intro z hz
    change z ∈ support ((SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
      (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover s.keyA) ecEk ecCt)) n).run s) at hz
    refine gameInv_recvB_step_of kem ecEk ecCt hEk hCt _ _ (fun _ _ => rfl) n s hs ?_ z hz
    intro T hA hB ρ tsnd hmsg hqnot pk sk c k hkp henc
    have hpar := recv_tRes_parity (roleR := .B) hA hmsg
    have hpos : 0 < ρ.tRes := hB.keypair_pos _ hpar (by rw [hkp]; rfl)
    have hparS : ρ.tRes % 2 = Role.A.resParity := by simpa using hpar
    change s.keyA ρ.tRes.toNat = some k
    rw [hA.key_res _ hpos hparS, EpochTranscript.key, henc]
    rfl

/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes.

Then, for either challenge bit `b`, every ideal security query preserves `GameInv`. No KEM
correctness and no no-failure premise is needed. -/
theorem idealSecurityImpl_preservesInv [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak) (b : Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem hDet ecEk ecCt leak b)
      (GameInv kem ecEk ecCt) := by
  intro t s hs z hz
  exact SCKAScheme.securityImplOf_preserves_at_of_book _ _ _ _ _ (GameInv kem ecEk ecCt)
    (fun _ E C h => gameInv_with_security_bookkeeping h E C)
    (sendWith_rleak_forget kem .A ecEk ecCt leak)
    (sendWith_rleak_forget kem .B ecEk ecCt leak) s hs
    (fun t => gameInv_ideal_step kem hDet ecEk ecCt hEk hCt leak t s hs)
    (fun t => SCKAScheme.oracleChall_preservesInv b _
      (fun s C h => by simpa using gameInv_with_security_bookkeeping h s.exposed C) t s hs)
    (gameInv_sendA_step kem hDet ecEk ecCt leak s hs)
    (gameInv_sendB_step kem hDet ecEk ecCt leak s hs) t z hz

/-- Every supported outcome of an ideal security run from the initial state satisfies `GameInv`,
for either challenge bit and for arbitrary adaptive computations over the security oracles. -/
lemma idealSecurity_gameInv_of_run [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak) (b : Bool)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (z : α × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ (idealSecurityImpl kem hDet ecEk ecCt leak b) adv).run
      (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)))) :
    GameInv kem ecEk ecCt z.2 :=
  simulateQ_run_preservesInv _ _
    (idealSecurityImpl_preservesInv kem hDet ecEk ecCt hEk hCt leak b) adv _
    (gameInv_init kem ecEk ecCt _ _ (by simp [initA, init, initialState])
      (by simp [initB, init, initialState])) z hz

end oppBiKemCKA
