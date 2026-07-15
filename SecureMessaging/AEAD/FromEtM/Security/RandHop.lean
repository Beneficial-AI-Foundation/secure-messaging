/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromEtM.Security.Games

/-!
# Encrypt-then-MAC — random-experiment hop (`game3` = random)

`game3_eq_rand`: `game3` equals the random AEAD experiment (given lossless PRF keygen).
-/

open OracleSpec OracleComp ENNReal PRFScheme AEADScheme

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]
  [Inhabited C_e] [Inhabited T]
  [SampleableType C_e] [SampleableType T]

omit [Inhabited C_e] [Inhabited T] in
/-- `game3` (the final endpoint of the game-hop sequence) coincides with the real
random-ciphertext AEAD experiment (`securityExpFixedBit … true`).

`game3` and the real experiment differ only in that the real experiment generates the scheme's
whole key pair — including the tag key, which sits idle on the random side — while the simplified
`game3` never generates it. That extra key generation leaves the output distribution unchanged
precisely when it cannot fail, which is the `NeverFail prf.keygen` hypothesis. (Every standard
PRF keygen qualifies; why this is benign: see `etmAEAD_security`.) -/
theorem game3_eq_rand
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTimeCCAAdversary AD M (C_e × T))
    [NeverFail prf.keygen] :
    Pr[= true | game3 se adv] =
      Pr[= true | AEADScheme.securityExpFixedBit (etmAEAD se prf) adv true] := by
  -- NRS14 Figure 4, right column: ideal nAE experiment.
  have hkg : (etmAEAD se prf).keygen
      = (se.keygen >>= fun ke => prf.keygen >>= fun km =>
          (pure (ke, km) : ProbComp (K_e × K_m))) := rfl
  unfold game3 etmGameSkeleton AEADScheme.securityExpFixedBit
  rw [hkg]
  simp only [bind_assoc, pure_bind]
  simp only [bind_pure_comp, ← StateT.run'_eq]
  -- Both sides start with `se.keygen`; descend it.
  refine probOutput_bind_congr' se.keygen true (fun ke => ?_)
  -- RHS samples a dead `km`; its body is constant in `km` (= the LHS value by projection).
  rw [probOutput_bind_of_const prf.keygen
        (my := fun km => (simulateQ (AEADScheme.aeadSecurityImpl (etmAEAD se prf)
          true (ke, km)) adv).run' none)
        (fun km _ => congrArg (fun o => Pr[= true | o])
          (run'_simulateQ_eq_of_query_map_eq _
            (AEADScheme.aeadSecurityImpl (etmAEAD se prf) true (ke, km))
            Prod.fst ?_ adv ((none, ∅) : EtmGameState AD C_e T)).symm)]
  · -- `prf.keygen` is lossless, so the `(1 - Pr[⊥]) ·` factor is `1`; `rfl` pins `impl₁`.
    rw [NeverFail.probFailure_eq_zero, tsub_zero, one_mul]
  · -- per-query projection (`impl₁` now pinned to game3's oracle implementation)
    intro t s
    obtain ⟨ch, qc⟩ := s
    rcases t with (n | am) | ac
    · -- uniform-sampling oracle
      simp [AEADScheme.aeadSecurityImpl, gameUnifImpl, AEADScheme.oracleUnif,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, Prod.map]
    · -- encryption oracle: random `(c, t)` vs `$ᵗ (C_e × T)` (product sampling)
      obtain ⟨ad, m⟩ := am
      cases ch <;>
        simp [AEADScheme.aeadSecurityImpl, AEADScheme.oracleEncrypt, etmAEAD,
          QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          uniformSample_prod_eq_bind, bind_assoc, map_pure, Prod.map]
    · -- decryption oracle: both always reject
      obtain ⟨ad, c, t⟩ := ac
      cases ch <;>
        simp [AEADScheme.aeadSecurityImpl, AEADScheme.oracleDecrypt, etmAEAD,
          QueryImpl.add_apply_inr,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          map_pure, Prod.map]
      split_ifs <;> simp [StateT.run_set, StateT.run_pure, map_pure, Prod.map]

