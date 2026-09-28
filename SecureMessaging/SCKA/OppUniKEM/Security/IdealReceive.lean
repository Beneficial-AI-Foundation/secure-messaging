/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Ideal

/-!
# Equality of real and auxiliary receives

**Statement.** Fix deterministic decapsulation and a correct erasure code
for the online ciphertext component. For every state `s` satisfying
`reachableInv` and `CurrentKEMCorrect`, and every sent-message index `n`,
`oracleRecvA(n, s) = oracleRecvAIdeal(n, s)` as response/state computations.
The auxiliary receive records B's encapsulated key. Index `n` may select
any message in the honest history, including an old or repeated delivery.

**Proof.** For the branch completing an online ciphertext, transcript
consistency and erasure-code correctness identify the decoded ciphertext
with its epoch's encapsulation. `CurrentKEMCorrect` identifies decapsulation
with B's key. The remaining branches execute the same operations in both
computations. `IdealGame` lifts this equality to the full oracle family.
-/

open OracleSpec OracleComp KEMScheme ErasureCodePayload

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type} [DecidableEq Sym]

/-- Replacing decapsulation by `key` leaves a receive unchanged if every
decapsulation reached by this particular message returns `key`. Messages
that leave the current online ciphertext incomplete agree directly. -/
theorem recvA_eq_keyDecaps_of_agrees
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : StA onoff Sym) (msg : Message Sym) (key : Option K)
    (hdec : ∀ dk ct0 ch ct1 ack,
      s.dkA = some dk → s.ct0 = some ct0 →
      msg = (some ch, ack, s.t, some 1) →
      ecCt1.decode (insert ch s.lch) = some ct1 →
      hDet.decapsDet dk (onoff.split.symm (ct0, ct1)) = key) :
    recvA kem onoff hDet ecCt0 ecCt1 s msg =
      recvA (keyDecapsKEM kem key) (keyDecapsOnOff kem onoff key)
        (keyDecapsDet kem key) ecCt0 ecCt1 s msg := by
  rcases msg with ⟨ch, ack, t, bit⟩
  by_cases ht : t = s.t
  · subst t
    cases hc : ch with
    | none =>
      cases hct : s.ct0 <;> simp [recvA, hct]
    | some chunk =>
      cases hb : bit with
      | none =>
        cases hct : s.ct0 <;> simp [recvA, hct]
      | some bit =>
        fin_cases bit
        · cases hct : s.ct0 <;> cases hdecode : ecCt0.decode (insert chunk s.lch) <;>
            simp [recvA, hct, hdecode]
        · cases hd : s.dkA with
          | none => cases hct : s.ct0 <;> simp [recvA, hd, hct]
          | some dk =>
            cases hct : s.ct0 with
            | none => simp [recvA, hd, hct]
            | some ct0 =>
              cases hct1 : ecCt1.decode (insert chunk s.lch) with
              | none => simp [recvA, hd, hct, hct1]
              | some ct1 =>
                have heq := hdec dk ct0 chunk ct1 ack hd hct
                  (by simp [hc, hb]) hct1
                simp [recvA, hd, hct, hct1, heq]
  · have ht' : s.t ≠ t := Ne.symm ht
    simp [recvA, ht']

/-- For an honestly sent message, every reached online decapsulation
returns B's current recorded key whenever the correctness transcript and
current KEM consistency hold. This covers delayed and duplicated chunks. -/
theorem honest_recvA_decapsulation_eq_recorded
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hc : CurrentKEMCorrect kem onoff hDet s)
    (n : ℕ) (msg : Message Sym) (epoch : ℕ) (hentry : s.msgB n = some (msg, epoch))
    (dk : SK) (ct0 : onoff.C₀) (ch : ℕ × Sym) (ct1 : onoff.C₁) (ack : Ack)
    (hdk : s.stA.dkA = some dk) (hct0 : s.stA.ct0 = some ct0)
    (hmsg : msg = (some ch, ack, s.stA.t, some 1))
    (hdecode : ecCt1.decode (insert ch s.stA.lch) = some ct1) :
    hDet.decapsDet dk (onoff.split.symm (ct0, ct1)) = s.keyB s.stA.t := by
  obtain ⟨T, hT⟩ := hs
  subst msg
  have hhon := hT.msgB n _ hentry
  obtain ⟨online, key, i, hon, hch⟩ : ∃ online key i,
      (T s.stA.t).on = some (online, key) ∧ ch = ecCt1.encode online i := by
    simpa [HonestMessageB] using hhon.2
  obtain ⟨_, I, hlch, hcard⟩ :
      (∃ st, (T s.stA.t).off = some (st, ct0)) ∧
      ∃ I, s.stA.lch = payloadChunks ecCt1 online I ∧ I.card < ecCt1.ec.nchunk := by
    simpa [ChunksAConsistent, hct0, hon] using hT.chunksA
  have hstep := decode_insert_honest ecCt1 hCt1 online I i hcard
  have heq : online = ct1 := by
    rw [hch, hlch] at hdecode
    rcases hstep with ⟨_, hn⟩ | ⟨_, hsome⟩
    · simp [hn] at hdecode
    · exact Option.some.inj (hsome.symm.trans hdecode)
  subst ct1
  have htbound := hT.msgBEpoch n _ epoch hentry
  change s.stA.t ≤ s.stB.t at htbound
  have htAB := Nat.le_antisymm htbound hT.epochs.1
  have hct1B : s.stB.ct1 = some online := by
    have h := hT.onB
    rw [← htAB, hon] at h
    exact h.symm
  have hk : s.keyB s.stA.t = some key := by
    rw [hT.keyB]
    simp [EpochTranscript.key, hon]
  exact (hc dk ct0 online key hdk hct0 hct1B hk).trans hk.symm

/-- Assume a correct online-component erasure code. For every state `s`
satisfying `reachableInv` and `CurrentKEMCorrect`, and delivery index `n`,
the real and auxiliary A-receive response/state computations from `s` are equal. -/
theorem oracleRecvA_eq_ideal [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (n : ℕ) (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hc : CurrentKEMCorrect kem onoff hDet s) :
    (SCKAScheme.oracleRecvA (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s =
      (oracleRecvAIdeal kem onoff ecEk ecCt0 ecCt1 leak n).run s := by
  change (SCKAScheme.oracleRecvA _ n).run s =
    (SCKAScheme.oracleRecvA (scheme (keyDecapsKEM kem (s.keyB s.stA.t))
      (keyDecapsOnOff kem onoff (s.keyB s.stA.t))
      (keyDecapsDet kem (s.keyB s.stA.t)) ecEk ecCt0 ecCt1
      (keyDecapsLeak kem onoff leak (s.keyB s.stA.t))) n).run s
  cases hentry : s.msgB n with
  | none => simp [SCKAScheme.oracleRecvA, hentry]
  | some entry =>
    rcases entry with ⟨msg, epoch⟩
    have heq := recvA_eq_keyDecaps_of_agrees kem onoff hDet ecCt0 ecCt1 s.stA msg
      (s.keyB s.stA.t)
      (honest_recvA_decapsulation_eq_recorded kem onoff hDet ecEk ecCt0 ecCt1 hCt1
        s hs hc n msg epoch hentry)
    simp only [SCKAScheme.oracleRecvA, scheme, StateT.run_bind,
      StateT.run_get, pure_bind, hentry, heq]

end oppUniKemCKA.Security
