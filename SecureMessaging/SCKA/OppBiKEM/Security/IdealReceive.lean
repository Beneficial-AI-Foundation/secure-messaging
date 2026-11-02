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
`oracleRecvBIdeal`, `Defs`). Its oracles `idealSecurityImpl b` are the security oracles over
the ideal correctness oracles `idealCorrectnessImpl`, with the fixed-bit challenge, the exposure
policy and the honest leaking sends and corruptions.

**Main results.**

- On every state satisfying `GameInv` without current KEM failure, the real and ideal oracles
  have the same query computation (`securityImpl_eq_ideal_of_noFailure`).
- With correct erasure codes, every ideal security query preserves `GameInv`, with no KEM
  correctness and no no-failure premise (`idealSecurityImpl_preservesInv`): the ideal receive
  returns the peer's recorded key, which is the transcript key.

`idealRecvSecurityImpl` also supports variants with modified ordinary sends and selected
random-key challenges. Query-comparison and state-preservation lemmas let later proofs
reuse these variants.
-/

open OracleSpec OracleComp KEMScheme SCKAScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

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

/-! ## Ideal receives with modified ordinary sends -/

section IdealRecvFamilies

variable (kem : KEMScheme ProbComp K PK SK C)

variable [DecidableEq K] [DecidableEq Sym] (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

/-- The correctness oracles with ordinary sends from `scka` and ideal receives.
Uniform sampling is unchanged. -/
def idealRecvCorrectnessImpl
    (scka : SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand)) :
    QueryImpl (SCKAScheme.sckaCorrectnessSpec (Message Sym))
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    + SCKAScheme.oracleSendA scka + SCKAScheme.oracleSendB scka
    + oracleRecvAIdeal kem hDet ecEk ecCt leak + oracleRecvBIdeal kem hDet ecEk ecCt leak

variable [SampleableType K]

/-- The common oracle family for ideal-receive games with modified ordinary sends.
The scheme `scka` supplies the ordinary sends, and `random` selects random-key challenges.
Leaking sends, corruptions, and the exposure policy use the honest Opp-BiKEM scheme. -/
def idealRecvSecurityImpl
    (scka : SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand)) (random : ℕ → Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.securityImplOf (idealRecvCorrectnessImpl kem hDet ecEk ecCt leak scka)
    (SCKAScheme.oracleChallOn random _ _ _ _) (exposure .A leak) (exposure .B leak)
    (scheme kem hDet ecEk ecCt leak)

end IdealRecvFamilies

section IdealRecvQueries

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

/-- A's ordinary send query of the ideal-receive oracles is A's send oracle. -/
lemma idealRecvSecurityImpl_run_OSendA
    (scka : SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand)) (random : ℕ → Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) (u : Unit) :
    (idealRecvSecurityImpl kem hDet ecEk ecCt leak scka random
      (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl
        (Sum.inr u)))))))))).run s = (SCKAScheme.oracleSendA scka ()).run s :=
  rfl

/-- B's ordinary send query of the ideal-receive oracles is B's send oracle. -/
lemma idealRecvSecurityImpl_run_OSendB
    (scka : SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand)) (random : ℕ → Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) (u : Unit) :
    (idealRecvSecurityImpl kem hDet ecEk ecCt leak scka random
      (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr u))))))))).run s =
      (SCKAScheme.oracleSendB scka ()).run s :=
  rfl

/-- Matching ordinary sends give matching ideal-receive query computations.
Only the send selected by the current query needs to agree at the current state. -/
lemma idealRecvSecurityImpl_run_eq
    (scka scka' : SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand)) (random : ℕ → Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (q : (securitySpec leak Sym).Domain)
    (hA : q = sckaSecuritySpec.OCorrectness sckaCorrectnessSpec.OSendA →
      scka.sendA s.stA = scka'.sendA s.stA)
    (hB : q = sckaSecuritySpec.OCorrectness sckaCorrectnessSpec.OSendB →
      scka.sendB s.stB = scka'.sendB s.stB) :
    (idealRecvSecurityImpl kem hDet ecEk ecCt leak scka random q).run s =
      (idealRecvSecurityImpl kem hDet ecEk ecCt leak scka' random q).run s := by
  rcases q with (((((((((n | ⟨⟩) | ⟨⟩) | n) | n) | ⟨⟩) | ⟨⟩) | e) | ⟨⟩) | ⟨⟩) <;> (try rfl)
  · rw [idealRecvSecurityImpl_run_OSendA, idealRecvSecurityImpl_run_OSendA,
      SCKAScheme.oracleSendA_run_eq, SCKAScheme.oracleSendA_run_eq, hA rfl]
  · rw [idealRecvSecurityImpl_run_OSendB, idealRecvSecurityImpl_run_OSendB,
      SCKAScheme.oracleSendB_run_eq, SCKAScheme.oracleSendB_run_eq, hB rfl]

end IdealRecvQueries

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

/-! ## State preservation with modified ordinary sends -/

section PartyState

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
  (scka : SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
    (SendRand leak.KeygenRand leak.EncapsRand)) (random : ℕ → Bool)

/-- Lift preservation of a predicate on A's local state to every ideal-receive query.
It suffices to prove preservation for A's ordinary send, honest leaking send, and receive
with any recovery function. -/
lemma idealRecvSecurityImpl_stA_step (Q : State PK SK C Sym → Prop)
    (hsend : ∀ st key? ρ tsnd st', some (key?, ρ, tsnd, st') ∈ support (scka.sendA st) →
      Q st → Q st')
    (hrleak : ∀ st key? ρ tsnd st' (rand : SendRand leak.KeygenRand leak.EncapsRand),
      some (key?, ρ, tsnd, st', rand) ∈
        support (sendWith .A leak.keygenRleak leak.encapsRleak ecEk ecCt st) → Q st → Q st')
    (hrecv : ∀ (recover : ℤ → SK → C → Option K) st ρ key? trcv st',
      recvWith .A recover ecEk ecCt st ρ = some (key?, trcv, st') → Q st → Q st')
    (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hQ : Q s.stA) :
    ∀ z ∈ support ((idealRecvSecurityImpl kem hDet ecEk ecCt leak scka random q).run s),
      Q z.2.stA := by
  intro z hz
  rcases q with (((((((((n | ⟨⟩) | ⟨⟩) | n) | n) | ⟨⟩) | ⟨⟩) | e) | ⟨⟩) | ⟨⟩)
  · exact SCKAScheme.oracleUnif_preservesInv (fun u => Q u.stA) n s hQ z hz
  · obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendA_run_iff _ s z).1 hz
    rcases out with _ | ⟨key?, ρ, tsnd, stA'⟩
    · exact hQ
    · rcases key? with _ | ⟨tI, k⟩ <;> exact hsend s.stA _ _ _ _ hout hQ
  · obtain ⟨out, -, rfl⟩ := (SCKAScheme.mem_support_oracleSendB_run_iff _ s z).1 hz
    rcases out with _ | ⟨_ | ⟨tI, k⟩, ρ, tsnd, stB'⟩ <;> exact hQ
  · change z ∈ support ((SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
      (recvWith .A (idealRecover s.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n).run s) at hz
    rcases (SCKAScheme.mem_support_oracleRecvA_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, key?, trcv, stA', -, hrecv', rfl⟩
    · exact hQ
    · exact hQ
    · rcases key? with _ | ⟨tI, k⟩ <;> exact hrecv _ s.stA ρ _ trcv stA' hrecv' hQ
  · change z ∈ support ((SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
      (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover s.keyA) ecEk ecCt)) n).run s) at hz
    rcases (SCKAScheme.mem_support_oracleRecvB_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, key?, trcv, stB', -, -, rfl⟩
    · exact hQ
    · exact hQ
    · rcases key? with _ | ⟨tI, k⟩ <;> exact hQ
  · rcases SCKAScheme.oracleSendArleak_run_cases _ _ s z hz with
      rfl | ⟨key?, ρ, tsnd, stA', rand, hout, -, hz2⟩
    · exact hQ
    · rw [hz2]
      rcases key? with _ | ⟨tI, k⟩ <;> exact hrleak s.stA _ _ _ _ rand hout hQ
  · rcases SCKAScheme.oracleSendBrleak_run_cases _ _ s z hz with
      rfl | ⟨key?, ρ, tsnd, stB', rand, -, -, hz2⟩
    · exact hQ
    · rw [hz2]
      rcases key? with _ | ⟨tI, k⟩ <;> exact hQ
  · rcases SCKAScheme.oracleChall_support (random e) s e z hz with ⟨rfl, -⟩ | ⟨-, -, h⟩
    · exact hQ
    · rw [h]
      exact hQ
  · rcases SCKAScheme.oracleCorruptA_support _ s z hz with rfl | ⟨-, rfl⟩ <;> exact hQ
  · rcases SCKAScheme.oracleCorruptB_support _ s z hz with rfl | ⟨-, rfl⟩ <;> exact hQ

/-- Lift preservation of a predicate on B's local state to every ideal-receive query.
This is the B version of `idealRecvSecurityImpl_stA_step`. -/
lemma idealRecvSecurityImpl_stB_step (Q : State PK SK C Sym → Prop)
    (hsend : ∀ st key? ρ tsnd st', some (key?, ρ, tsnd, st') ∈ support (scka.sendB st) →
      Q st → Q st')
    (hrleak : ∀ st key? ρ tsnd st' (rand : SendRand leak.KeygenRand leak.EncapsRand),
      some (key?, ρ, tsnd, st', rand) ∈
        support (sendWith .B leak.keygenRleak leak.encapsRleak ecEk ecCt st) → Q st → Q st')
    (hrecv : ∀ (recover : ℤ → SK → C → Option K) st ρ key? trcv st',
      recvWith .B recover ecEk ecCt st ρ = some (key?, trcv, st') → Q st → Q st')
    (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hQ : Q s.stB) :
    ∀ z ∈ support ((idealRecvSecurityImpl kem hDet ecEk ecCt leak scka random q).run s),
      Q z.2.stB := by
  intro z hz
  rcases q with (((((((((n | ⟨⟩) | ⟨⟩) | n) | n) | ⟨⟩) | ⟨⟩) | e) | ⟨⟩) | ⟨⟩)
  · exact SCKAScheme.oracleUnif_preservesInv (fun u => Q u.stB) n s hQ z hz
  · obtain ⟨out, -, rfl⟩ := (SCKAScheme.mem_support_oracleSendA_run_iff _ s z).1 hz
    rcases out with _ | ⟨_ | ⟨tI, k⟩, ρ, tsnd, stA'⟩ <;> exact hQ
  · obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendB_run_iff _ s z).1 hz
    rcases out with _ | ⟨key?, ρ, tsnd, stB'⟩
    · exact hQ
    · rcases key? with _ | ⟨tI, k⟩ <;> exact hsend s.stB _ _ _ _ hout hQ
  · change z ∈ support ((SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
      (recvWith .A (idealRecover s.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n).run s) at hz
    rcases (SCKAScheme.mem_support_oracleRecvA_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, key?, trcv, stA', -, -, rfl⟩
    · exact hQ
    · exact hQ
    · rcases key? with _ | ⟨tI, k⟩ <;> exact hQ
  · change z ∈ support ((SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
      (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover s.keyA) ecEk ecCt)) n).run s) at hz
    rcases (SCKAScheme.mem_support_oracleRecvB_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, key?, trcv, stB', -, hrecv', rfl⟩
    · exact hQ
    · exact hQ
    · rcases key? with _ | ⟨tI, k⟩ <;> exact hrecv _ s.stB ρ _ trcv stB' hrecv' hQ
  · rcases SCKAScheme.oracleSendArleak_run_cases _ _ s z hz with
      rfl | ⟨key?, ρ, tsnd, stA', rand, -, -, hz2⟩
    · exact hQ
    · rw [hz2]
      rcases key? with _ | ⟨tI, k⟩ <;> exact hQ
  · rcases SCKAScheme.oracleSendBrleak_run_cases _ _ s z hz with
      rfl | ⟨key?, ρ, tsnd, stB', rand, hout, -, hz2⟩
    · exact hQ
    · rw [hz2]
      rcases key? with _ | ⟨tI, k⟩ <;> exact hrleak s.stB _ _ _ _ rand hout hQ
  · rcases SCKAScheme.oracleChall_support (random e) s e z hz with ⟨rfl, -⟩ | ⟨-, -, h⟩
    · exact hQ
    · rw [h]
      exact hQ
  · rcases SCKAScheme.oracleCorruptA_support _ s z hz with rfl | ⟨-, rfl⟩ <;> exact hQ
  · rcases SCKAScheme.oracleCorruptB_support _ s z hz with rfl | ⟨-, rfl⟩ <;> exact hQ

variable (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)

include hEk hCt in
/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes;
* each ordinary send of `scka` has support contained in the corresponding honest send
  support.

Then every ideal-receive security query preserves `GameInv`. -/
lemma gameInv_idealRecv_step
    (hA : ∀ st, support (scka.sendA st) ⊆ support (send .A kem ecEk ecCt st))
    (hB : ∀ st, support (scka.sendB st) ⊆ support (send .B kem ecEk ecCt st)) :
    QueryImpl.PreservesInv (idealRecvSecurityImpl kem hDet ecEk ecCt leak scka random)
      (GameInv kem ecEk ecCt) := by
  intro q s hs z hz
  refine SCKAScheme.securityImplOf_preserves_at_of_book _ _ _ _ _ (GameInv kem ecEk ecCt)
    (fun _ E C h => gameInv_with_security_bookkeeping h E C)
    (sendWith_rleak_forget kem .A ecEk ecCt leak)
    (sendWith_rleak_forget kem .B ecEk ecCt leak) s hs (fun q z hz => ?_)
    (fun e => SCKAScheme.oracleChallOn_preservesInv random _
      (fun s C h => by simpa using gameInv_with_security_bookkeeping h s.exposed C) e s hs)
    (gameInv_sendA_step kem hDet ecEk ecCt leak s hs)
    (gameInv_sendB_step kem hDet ecEk ecCt leak s hs) q z hz
  rcases q with (((n | ⟨⟩) | ⟨⟩) | n) | n
  · exact SCKAScheme.oracleUnif_preservesInv (GameInv kem ecEk ecCt) n s hs z hz
  · obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendA_run_iff _ s z).1 hz
    exact gameInv_sendA_step kem hDet ecEk ecCt leak s hs _
      ((SCKAScheme.mem_support_oracleSendA_run_iff _ s _).2 ⟨out, hA s.stA hout, rfl⟩)
  · obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendB_run_iff _ s z).1 hz
    exact gameInv_sendB_step kem hDet ecEk ecCt leak s hs _
      ((SCKAScheme.mem_support_oracleSendB_run_iff _ s _).2 ⟨out, hB s.stB hout, rfl⟩)
  · exact gameInv_ideal_step kem hDet ecEk ecCt hEk hCt leak (Sum.inl (Sum.inr n)) s hs z hz
  · exact gameInv_ideal_step kem hDet ecEk ecCt hEk hCt leak (Sum.inr n) s hs z hz

end PartyState

end oppBiKemCKA
