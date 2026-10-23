/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.IdealReceive
import ToVCVio.OracleComp.QueryTracking.StateBudget

/-!
# Opp-BiKEM — Epoch counter

`advances s` counts the epoch advances both parties have committed: half the sum of A's
responder epoch plus one and B's responder epoch. Every security query raises it by at most one
if it is an ordinary or leaking send and not at all otherwise, on every state, so after `q`
sends it is at most `q` (`advances_le_of_run_real`, `advances_le_of_run_ideal`). On states
satisfying `GameInv`, every epoch with a recorded key is at most `2 · advances s`
(`keyed_epoch_le_two_mul_advances`), which bounds the challengeable epochs of a run by `2q`.

Run-level uniqueness facts (one key generation and at most one encapsulation per epoch) are
deliberately left to the KEM reduction, whose simulation relation fixes their shape.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- The number of committed epoch advances: half the sum of A's responder epoch plus one and B's
responder epoch, both clamped at zero. -/
def advances (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : ℕ :=
  ((s.stA.res.resEpoch + 1).toNat + s.stB.res.resEpoch.toNat) / 2

/-- The initial game state has no advances. -/
lemma advances_init :
    advances (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) = 0 := by
  simp [advances, initState, SCKAScheme.initGameState, initialState]

/-- Advancing A's responder epoch by zero or two raises `advances` by at most one. -/
lemma advances_le_of_resEpochA
    (s s' : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hA : s'.stA.res.resEpoch = s.stA.res.resEpoch ∨
      s'.stA.res.resEpoch = s.stA.res.resEpoch + 2)
    (hB : s'.stB.res.resEpoch = s.stB.res.resEpoch) :
    advances s' ≤ advances s + 1 := by
  unfold advances
  omega

/-- Advancing B's responder epoch by zero or two raises `advances` by at most one. -/
lemma advances_le_of_resEpochB
    (s s' : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hA : s'.stA.res.resEpoch = s.stA.res.resEpoch)
    (hB : s'.stB.res.resEpoch = s.stB.res.resEpoch ∨
      s'.stB.res.resEpoch = s.stB.res.resEpoch + 2) :
    advances s' ≤ advances s + 1 := by
  unfold advances
  omega

/-- Unchanged responder epochs leave `advances` unchanged. -/
lemma advances_eq_of_resEpoch
    (s s' : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hA : s'.stA.res.resEpoch = s.stA.res.resEpoch)
    (hB : s'.stB.res.resEpoch = s.stB.res.resEpoch) :
    advances s' = advances s := by
  unfold advances
  rw [hA, hB]

section Steps

variable [DecidableEq K] [DecidableEq Sym]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

/-- A's ordinary send raises `advances` by at most one. -/
lemma advances_sendA_le
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z)
    (hz : z ∈ support ((SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak) ()).run s)) :
    advances z.2 ≤ advances s + 1 := by
  obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendA_run_iff _ s z).1 hz
  rcases out with _ | ⟨key?, ρ, tsnd, stA'⟩
  · exact Nat.le_succ _
  · dsimp only
    have hout' : some (key?, ρ, tsnd, stA') ∈ support (send .A kem ecEk ecCt s.stA) := hout
    obtain ⟨-, -, hres, -, -⟩ := send_support_facts .A kem ecEk ecCt s.stA key? ρ tsnd stA' hout'
    refine advances_le_of_resEpochA s _ ?_ ?_
    · rcases hres with h | h
      · exact Or.inl (by simpa [SCKAScheme.sendAUpdate_stA] using h)
      · exact Or.inr (by simpa [SCKAScheme.sendAUpdate_stA] using h)
    · simp [SCKAScheme.sendAUpdate_stB]

/-- B's ordinary send raises `advances` by at most one. -/
lemma advances_sendB_le
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z)
    (hz : z ∈ support ((SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak) ()).run s)) :
    advances z.2 ≤ advances s + 1 := by
  obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendB_run_iff _ s z).1 hz
  rcases out with _ | ⟨key?, ρ, tsnd, stB'⟩
  · exact Nat.le_succ _
  · dsimp only
    have hout' : some (key?, ρ, tsnd, stB') ∈ support (send .B kem ecEk ecCt s.stB) := hout
    obtain ⟨-, -, hres, -, -⟩ := send_support_facts .B kem ecEk ecCt s.stB key? ρ tsnd stB' hout'
    refine advances_le_of_resEpochB s _ ?_ ?_
    · simp [SCKAScheme.sendBUpdate_stA]
    · rcases hres with h | h
      · exact Or.inl (by simpa [SCKAScheme.sendBUpdate_stB] using h)
      · exact Or.inr (by simpa [SCKAScheme.sendBUpdate_stB] using h)

/-- A's leaking send raises `advances` by at most one. -/
lemma advances_sendArleak_le
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z)
    (hz : z ∈ support ((SCKAScheme.oracleSendArleak (exposure .A leak).rleak
      (scheme kem hDet ecEk ecCt leak) ()).run s)) :
    advances z.2 ≤ advances s + 1 :=
  SCKAScheme.oracleSendArleak_preservesInv_at (scheme kem hDet ecEk ecCt leak) _
    (sendWith_rleak_forget kem .A ecEk ecCt leak) (fun z => advances z ≤ advances s + 1)
    (fun _ _ h => h) s (Nat.le_succ _) (advances_sendA_le kem hDet ecEk ecCt leak s) z hz

/-- B's leaking send raises `advances` by at most one. -/
lemma advances_sendBrleak_le
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z)
    (hz : z ∈ support ((SCKAScheme.oracleSendBrleak (exposure .B leak).rleak
      (scheme kem hDet ecEk ecCt leak) ()).run s)) :
    advances z.2 ≤ advances s + 1 :=
  SCKAScheme.oracleSendBrleak_preservesInv_at (scheme kem hDet ecEk ecCt leak) _
    (sendWith_rleak_forget kem .B ecEk ecCt leak) (fun z => advances z ≤ advances s + 1)
    (fun _ _ h => h) s (Nat.le_succ _) (advances_sendB_le kem hDet ecEk ecCt leak s) z hz

omit [DecidableEq Sym] hDet leak in
/-- A's receive through any scheme whose receive keeps the responder epoch leaves `advances`
unchanged. -/
lemma advances_recvA_eq {IK Rand : Type}
    (scka : SCKAScheme ProbComp IK (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) Rand)
    (hres : ∀ st ρ key? trcv st', scka.recvA st ρ = some (key?, trcv, st') →
      st'.res.resEpoch = st.res.resEpoch)
    (n : ℕ) (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z)
    (hz : z ∈ support ((SCKAScheme.oracleRecvA scka n).run s)) :
    advances z.2 = advances s := by
  rcases (SCKAScheme.mem_support_oracleRecvA_run_iff _ s n z).1 hz with
    ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, key?, trcv, stA', -, hrecv, rfl⟩
  · rfl
  · rfl
  · refine advances_eq_of_resEpoch s _ ?_ ?_
    · rcases key? with _ | ⟨tI, k⟩ <;> simpa [SCKAScheme.recvAUpdate] using hres _ _ _ _ _ hrecv
    · rcases key? with _ | ⟨tI, k⟩ <;> simp [SCKAScheme.recvAUpdate]

omit [DecidableEq Sym] hDet leak in
/-- B's receive through any scheme whose receive keeps the responder epoch leaves `advances`
unchanged. -/
lemma advances_recvB_eq {IK Rand : Type}
    (scka : SCKAScheme ProbComp IK (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) Rand)
    (hres : ∀ st ρ key? trcv st', scka.recvB st ρ = some (key?, trcv, st') →
      st'.res.resEpoch = st.res.resEpoch)
    (n : ℕ) (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z)
    (hz : z ∈ support ((SCKAScheme.oracleRecvB scka n).run s)) :
    advances z.2 = advances s := by
  rcases (SCKAScheme.mem_support_oracleRecvB_run_iff _ s n z).1 hz with
    ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, key?, trcv, stB', -, hrecv, rfl⟩
  · rfl
  · rfl
  · refine advances_eq_of_resEpoch s _ ?_ ?_
    · rcases key? with _ | ⟨tI, k⟩ <;> simp [SCKAScheme.recvBUpdate]
    · rcases key? with _ | ⟨tI, k⟩ <;> simpa [SCKAScheme.recvBUpdate] using hres _ _ _ _ _ hrecv

/-- Every real security query raises `advances` by at most one if it is an ordinary or leaking
send and not at all otherwise, on every state. -/
lemma advances_step_real [SampleableType K] (b : Bool) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z)
    (hz : z ∈ support ((SCKAScheme.sckaSecurityImpl b (exposure .A leak) (exposure .B leak)
      (scheme kem hDet ecEk ecCt leak) t).run s)) :
    advances z.2 ≤ advances s +
      if SCKAScheme.sckaSecuritySpec.isSendQuery t = true then 1 else 0 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with (((n | ⟨⟩) | ⟨⟩) | n) | n
    · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, SCKAScheme.isSendQuery,
        Bool.false_eq_true, ↓reduceIte, add_zero]
      exact (SCKAScheme.oracleUnif_preservesInv (fun z => advances z ≤ advances s) n s le_rfl z hz)
    · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, SCKAScheme.isSendQuery, ↓reduceIte]
      exact advances_sendA_le kem hDet ecEk ecCt leak s z hz
    · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, SCKAScheme.isSendQuery, ↓reduceIte]
      exact advances_sendB_le kem hDet ecEk ecCt leak s z hz
    · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, SCKAScheme.isSendQuery,
        Bool.false_eq_true, ↓reduceIte, add_zero]
      exact (advances_recvA_eq _ (fun st ρ key? trcv st' h =>
        (recv_success_state_facts .A kem hDet ecEk ecCt st ρ key? trcv st' h).2.1) n s z hz).le
    · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, SCKAScheme.isSendQuery,
        Bool.false_eq_true, ↓reduceIte, add_zero]
      exact (advances_recvB_eq _ (fun st ρ key? trcv st' h =>
        (recv_success_state_facts .B kem hDet ecEk ecCt st ρ key? trcv st' h).2.1) n s z hz).le
  · cases u
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte]
    exact advances_sendArleak_le kem hDet ecEk ecCt leak s z hz
  · cases u
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte]
    exact advances_sendBrleak_le kem hDet ecEk ecCt leak s z hz
  · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact SCKAScheme.oracleChall_preservesInv b (fun z => advances z ≤ advances s)
      (fun _ _ h => h) t s le_rfl z hz
  · cases u
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact SCKAScheme.oracleCorruptA_preservesInv _ (fun z => advances z ≤ advances s)
      (fun _ _ h => h) () s le_rfl z hz
  · cases u
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact SCKAScheme.oracleCorruptB_preservesInv _ (fun z => advances z ≤ advances s)
      (fun _ _ h => h) () s le_rfl z hz

/-- Every ideal security query raises `advances` by at most one if it is an ordinary or leaking
send and not at all otherwise, on every state. -/
lemma advances_step_ideal [SampleableType K] (b : Bool) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z)
    (hz : z ∈ support ((idealSecurityImpl kem hDet ecEk ecCt leak b t).run s)) :
    advances z.2 ≤ advances s +
      if SCKAScheme.sckaSecuritySpec.isSendQuery t = true then 1 else 0 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with (((n | ⟨⟩) | ⟨⟩) | n) | n
    · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, SCKAScheme.isSendQuery,
        Bool.false_eq_true, ↓reduceIte, add_zero]
      exact (SCKAScheme.oracleUnif_preservesInv (fun z => advances z ≤ advances s) n s le_rfl z hz)
    · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, SCKAScheme.isSendQuery, ↓reduceIte]
      exact advances_sendA_le kem hDet ecEk ecCt leak s z hz
    · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, SCKAScheme.isSendQuery, ↓reduceIte]
      exact advances_sendB_le kem hDet ecEk ecCt leak s z hz
    · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, SCKAScheme.isSendQuery,
        Bool.false_eq_true, ↓reduceIte, add_zero]
      change z ∈ support ((SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
        (recvWith .A (idealRecover s.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n).run s) at hz
      exact (advances_recvA_eq _ (fun st ρ key? trcv st' h =>
        recvWith_resEpoch .A _ ecEk ecCt st ρ key? trcv st' h) n s z hz).le
    · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, SCKAScheme.isSendQuery,
        Bool.false_eq_true, ↓reduceIte, add_zero]
      change z ∈ support ((SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
        (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover s.keyA) ecEk ecCt)) n).run s) at hz
      exact (advances_recvB_eq _ (fun st ρ key? trcv st' h =>
        recvWith_resEpoch .B _ ecEk ecCt st ρ key? trcv st' h) n s z hz).le
  · cases u
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte]
    exact advances_sendArleak_le kem hDet ecEk ecCt leak s z hz
  · cases u
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte]
    exact advances_sendBrleak_le kem hDet ecEk ecCt leak s z hz
  · simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact SCKAScheme.oracleChall_preservesInv b (fun z => advances z ≤ advances s)
      (fun _ _ h => h) t s le_rfl z hz
  · cases u
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact SCKAScheme.oracleCorruptA_preservesInv _ (fun z => advances z ≤ advances s)
      (fun _ _ h => h) () s le_rfl z hz
  · cases u
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact SCKAScheme.oracleCorruptB_preservesInv _ (fun z => advances z ≤ advances s)
      (fun _ _ h => h) () s le_rfl z hz

/-- After a real security run of an adversary making at most `q` ordinary or leaking sends, at
most `q` epoch advances have been committed. -/
theorem advances_le_of_run_real [SampleableType K] (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q)
    (z : Bool × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ (SCKAScheme.sckaSecurityImpl b (exposure .A leak)
      (exposure .B leak) (scheme kem hDet ecEk ecCt leak)) adv).run
      (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)))) :
    advances z.2 ≤ q :=
  (stateCounter_simulateQ_run_le _ advances
    (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true)
    (advances_step_real kem hDet ecEk ecCt leak b) adv q hq _ z hz).trans_eq
    (by rw [advances_init, zero_add])

/-- After an ideal security run of an adversary making at most `q` ordinary or leaking sends, at
most `q` epoch advances have been committed. -/
theorem advances_le_of_run_ideal [SampleableType K] (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q)
    (z : Bool × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ (idealSecurityImpl kem hDet ecEk ecCt leak b) adv).run
      (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)))) :
    advances z.2 ≤ q :=
  (stateCounter_simulateQ_run_le _ advances
    (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true)
    (advances_step_ideal kem hDet ecEk ecCt leak b) adv q hq _ z hz).trans_eq
    (by rw [advances_init, zero_add])

end Steps

/-- On a state satisfying `GameInv`, every epoch with a recorded key in either table is at most
twice the number of committed advances. -/
lemma keyed_epoch_le_two_mul_advances
    (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s)
    (t : ℕ) (ht : (s.keyA t).isSome = true ∨ (s.keyB t).isSome = true) :
    t ≤ 2 * advances s := by
  obtain ⟨-, T, hA, hB⟩ := hs
  have hresA := hA.res_parity
  have hresB := hB.res_parity
  have hlowA := hA.res_lower
  have hlowB := hB.res_lower
  simp only [Role.resParity] at hresA hresB
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · exact Nat.zero_le _
  have hposZ : (0 : ℤ) < t := by exact_mod_cast hpos
  have hkey_enc : ∀ (tr : EpochTranscript kem), tr.key.isSome = true → tr.enc.isSome = true := by
    intro tr h
    simpa [EpochTranscript.key, Option.isSome_map] using h
  -- bound the keyed epoch by the owner's responder epoch (plus one for A)
  have hboundA : (s.keyA t).isSome = true → (t : ℤ) ≤ s.stA.res.resEpoch + 1 := by
    intro hk
    rcases Int.emod_two_eq_zero_or_one (t : ℤ) with h0 | h1
    · -- requester parity of A: written at decapsulation
      have := hA.key_req (t : ℤ) hposZ (by simpa [Role.reqParity] using h0)
      rw [Int.toNat_natCast] at this
      rw [this] at hk
      split_ifs at hk with hin
      · have henc := hkey_enc _ hk
        have hkp := (T (t : ℤ)).enc_keypair henc
        by_contra hlt
        rw [not_le] at hlt
        have := hA.keypair_future (t : ℤ) (by simpa [Role.reqParity] using h0)
          (by simpa [Role.offset] using hlt)
        rw [this] at hkp
        cases hkp
      · cases hk
    · -- responder parity of A: written at encapsulation
      have := hA.key_res (t : ℤ) hposZ (by simpa [Role.resParity] using h1)
      rw [Int.toNat_natCast] at this
      rw [this] at hk
      have henc := hkey_enc _ hk
      by_contra hlt
      rw [not_le] at hlt
      have := hA.enc_future (t : ℤ) (by simpa [Role.resParity] using h1) (by omega)
      rw [this] at henc
      cases henc
  have hboundB : (s.keyB t).isSome = true → (t : ℤ) ≤ s.stB.res.resEpoch := by
    intro hk
    rcases Int.emod_two_eq_zero_or_one (t : ℤ) with h0 | h1
    · -- responder parity of B: written at encapsulation
      have := hB.key_res (t : ℤ) hposZ (by simpa [Role.resParity] using h0)
      rw [Int.toNat_natCast] at this
      rw [this] at hk
      have henc := hkey_enc _ hk
      by_contra hlt
      rw [not_le] at hlt
      have := hB.enc_future (t : ℤ) (by simpa [Role.resParity] using h0) hlt
      rw [this] at henc
      cases henc
    · -- requester parity of B: written at decapsulation
      have := hB.key_req (t : ℤ) hposZ (by simpa [Role.reqParity] using h1)
      rw [Int.toNat_natCast] at this
      rw [this] at hk
      split_ifs at hk with hin
      · have henc := hkey_enc _ hk
        have hkp := (T (t : ℤ)).enc_keypair henc
        by_contra hlt
        rw [not_le] at hlt
        have := hB.keypair_future (t : ℤ) (by simpa [Role.reqParity] using h1)
          (by simp only [Role.offset]; omega)
        rw [this] at hkp
        cases hkp
      · cases hk
  unfold advances
  rcases ht with hk | hk
  · have := hboundA hk
    omega
  · have := hboundB hk
    omega

end oppBiKemCKA
