/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromKEM.Construction

/-!
# CKA from KEM — Basic Results for Correctness and Security

The randomness-leaking send and send oracles agree with their ordinary
counterparts once the leaked sender randomness is projected away. This file
proves these facts by lifting the `KEMScheme.RandLeak` fields `keygen_fst`
and `encaps_fst` from the two KEM calls to the CKA send algorithm and then to
the game oracles.
-/

open OracleSpec OracleComp ENNReal KEMScheme

universe u

namespace kemCKA

/-- Project a randomness-leaking send output to the ordinary send output. -/
def sendWithRandFst {K PK SK C Rand : Type}
    (out? : Option (K × Message C PK × State PK SK × Rand)) :
    Option (K × Message C PK × State PK SK) :=
  out?.map fun | (key, msg, st, _rand) => (key, msg, st)

/-- Project a randomness-leaking send-oracle output to the ordinary send-oracle
output. The oracle layer returns `(message, key, rand)` rather than the
algorithm-level `(key, message, state, rand)`.
-/
def sendOracleWithRandFst {K Rho Rand : Type}
    (out? : Option (Rho × K × Rand)) : Option (Rho × K) :=
  out?.map fun | (rho, key, _rand) => (rho, key)

/-- The randomness-leaking send agrees with the ordinary send after projecting
away the leaked sender randomness. This lifts the `RandLeak` fields
`encaps_fst` and `keygen_fst` to the CKA send algorithm.
-/
theorem send_rleak_fst_eq_send
    {m : Type → Type u} [Monad m] [LawfulMonad m]
    {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (leak : RandLeak kem)
    (st : State PK SK) :
    sendWithRandFst <$> send_rleak kem leak st = send kem st := by
  cases st with
  | sendReady pk =>
      simp only [send, send_rleak]
      rw [← leak.encaps_fst pk]
      simp only [map_bind, bind_assoc, pure_bind]
      refine bind_congr fun ⟨⟨c, key⟩, rEnc⟩ => ?_
      rw [← leak.keygen_fst]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun ⟨⟨pk', sk'⟩, rKeygen⟩ => ?_
      simp [sendWithRandFst]
  | recvReady sk => simp [send, send_rleak, sendWithRandFst]

/-- When the turn check succeeds and the PCS leakage check allows a randomness-
leak query, the A-side rleak send oracle agrees with the ordinary A-side send
oracle after projecting away sender randomness.

The `allowCorrPCS` hypothesis is necessary because the rleak oracle returns
`none` when randomness leakage is too close to the challenge epoch, while the
ordinary send oracle has no leakage check.
-/
theorem oracleSendA_rleak_fst_eq_oracleSendA
    {K PK SK C : Type}
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    (hValid : CKAScheme.validStep s.lastAction .sendA = true)
    (hPCS : CKAScheme.allowCorrPCS gp { s with tA := s.tA + 1 } = true) :
    (sendOracleWithRandFst <$>
        (CKAScheme.oracleSendA_rleak gp (scheme kem hDet leak) ())).run s =
      (CKAScheme.oracleSendA (scheme kem hDet leak) ()).run s := by
  cases hst : s.stA with
  | recvReady sk =>
      simp [CKAScheme.oracleSendA_rleak, CKAScheme.oracleSendA, hValid,
        scheme, sendOracleWithRandFst, send_rleak, send, hst]
  | sendReady pk =>
      rw [hst] at hPCS
      simp only [CKAScheme.oracleSendA_rleak, scheme, send_rleak, bind_pure_comp,
        map_bind, StateT.run_bind, StateT.run_get, StateT.run_map,
        sendOracleWithRandFst, pure_bind, hValid, if_true, hst, hPCS,
        liftM_bind, liftM_map, bind_assoc, bind_map_left, StateT.run_monadLift,
        monadLift_self, StateT.run_set, map_pure, Functor.map_map,
        Option.map_some, CKAScheme.oracleSendA, send]
      rw [← leak.encaps_fst pk, ← leak.keygen_fst]
      simp

/-- When the turn check succeeds and the PCS leakage check allows a randomness-
leak query, the B-side rleak send oracle agrees with the ordinary B-side send
oracle after projecting away sender randomness.

The `allowCorrPCS` hypothesis is necessary because the rleak oracle returns
`none` when randomness leakage is too close to the challenge epoch, while the
ordinary send oracle has no leakage check.
-/
theorem oracleSendB_rleak_fst_eq_oracleSendB
    {K PK SK C : Type}
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (gp : CKAScheme.GameParams)
    (s : CKAScheme.GameState (State PK SK) K (Message C PK))
    (hValid : CKAScheme.validStep s.lastAction .sendB = true)
    (hPCS : CKAScheme.allowCorrPCS gp { s with tB := s.tB + 1 } = true) :
    (sendOracleWithRandFst <$>
        (CKAScheme.oracleSendB_rleak gp (scheme kem hDet leak) ())).run s =
      (CKAScheme.oracleSendB (scheme kem hDet leak) ()).run s := by
  cases hst : s.stB with
  | recvReady sk =>
      simp [CKAScheme.oracleSendB_rleak, CKAScheme.oracleSendB, hValid,
        scheme, sendOracleWithRandFst, send_rleak, send, hst]
  | sendReady pk =>
      rw [hst] at hPCS
      simp only [CKAScheme.oracleSendB_rleak, scheme, send_rleak, bind_pure_comp,
        map_bind, StateT.run_bind, StateT.run_get, StateT.run_map,
        sendOracleWithRandFst, pure_bind, hValid, if_true, hst, hPCS,
        liftM_bind, liftM_map, bind_assoc, bind_map_left, StateT.run_monadLift,
        monadLift_self, StateT.run_set, map_pure, Functor.map_map,
        Option.map_some, CKAScheme.oracleSendB, send]
      rw [← leak.encaps_fst pk, ← leak.keygen_fst]
      simp

end kemCKA
