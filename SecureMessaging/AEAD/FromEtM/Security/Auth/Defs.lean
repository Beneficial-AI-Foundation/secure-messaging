/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromEtM.Security.Games

/-!
# Encrypt-then-MAC — auth hop: instrumented games and forge reduction

Bad-flag-instrumented oracle handlers (`authInstImpl` and components) and the forgery reduction
(`forgeReduction`, `forgeJointImpl`) used to bound the `game1` → `game2` gap.
-/

open OracleSpec OracleComp ENNReal PRFScheme AEADScheme

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]
  [Inhabited C_e] [Inhabited T]
  [SampleableType C_e] [SampleableType T]

/-! ### Auth hop: bad-flag-instrumented games

For the identical-until-bad step we instrument `game1`/`game2'` with a monotone `forged : Bool`
flag set whenever a (non-challenge) decrypt query's tag verifies against the random oracle —
the "forgery" event. The state becomes `EtmGameState × Bool`. The parameter `b` selects the
return behaviour on a successful verify: `b = true` returns the real decryption (= `game1`),
`b = false` rejects (= `game2'`); both set the flag identically, so the two impls agree on
every non-bad transition (`tvDist_simulateQ_le_probEvent_output_bad_probComp`). -/

/-- Uniform-sampling oracle on the flag-augmented state. -/
noncomputable def authUnifImpl :
    QueryImpl unifSpec (StateT (EtmGameState AD C_e T × Bool) ProbComp) :=
  unifLiftStateT (EtmGameState AD C_e T × Bool) unifSpec

/-- Encryption oracle on the flag-augmented state (real encryption, random-oracle tag);
the flag is threaded unchanged. -/
noncomputable def authEncImpl (se : DetSEAlg K_e M C_e) (ke : K_e) :
    QueryImpl (AD × M →ₒ Option (C_e × T))
      (StateT (EtmGameState AD C_e T × Bool) ProbComp) :=
  fun (ad, m) => do
    let ((challenge, qc), forged) ← get
    match challenge with
    | some _ => pure none
    | none => do
      let (t, qc') ← (((AD × C_e) →ₒ T).randomOracle (ad, se.encrypt ke m)).run qc
      set ((some (se.encrypt ke m, t), qc'), forged)
      return some (se.encrypt ke m, t)

/-- Decryption oracle on the flag-augmented state. The challenge-ciphertext guard rejects;
otherwise the random oracle is queried, the `forged` flag is set on a successful verify, and
(`b = true`) the real decryption is returned or (`b = false`) the query is rejected. -/
noncomputable def authDecImpl (se : DetSEAlg K_e M C_e) (b : Bool) (ke : K_e) :
    QueryImpl (AD × (C_e × T) →ₒ Option M)
      (StateT (EtmGameState AD C_e T × Bool) ProbComp) :=
  fun (ad, (c, t)) => do
    let ((challenge, qc), forged) ← get
    if challenge == some (c, t) then pure none
    else do
      let (t', qc') ← (((AD × C_e) →ₒ T).randomOracle (ad, c)).run qc
      let ok := t == t'
      set ((challenge, qc'), forged || ok)
      if ok then (if b then pure (se.decrypt ke c) else pure none) else pure none

/-- Complete flag-instrumented oracle set for the auth hop (`b = true` ≈ `game1`,
`b = false` ≈ `game2'`). -/
noncomputable def authInstImpl (se : DetSEAlg K_e M C_e) (b : Bool) (ke : K_e) :
    QueryImpl (aeadOneTimeCCASpec AD M (C_e × T))
      (StateT (EtmGameState AD C_e T × Bool) ProbComp) :=
  authUnifImpl (AD := AD) (C_e := C_e) (T := T) + authEncImpl (AD := AD) (T := T) se ke +
    authDecImpl (AD := AD) (T := T) se b ke

/-- Forge reduction: a `etmAEAD.ForgeAdversary` over `forgeSpec (AD × C_e) T` built from the
AEAD adversary at a fixed key `ke`. It is a skeleton instantiation (`spec = forgeSpec`) that
forwards the EtM tag computation to the **eval** oracle (`D →ₒ R`) and the EtM verification to
the **verify** oracle (`D × R →ₒ Bool`), discarding the final guess bit (only the `forged` flag
in the forge experiment's state matters). Structurally analogous to `prfReduction`.

NRS14 Appendix A.2: the reduction `B(A)` witnessing the forge bound. Each decrypt query becomes
one verify query, so `B`'s verify-query count matches `A`'s decrypt-query count `q_d`. -/
noncomputable def forgeReduction
    (se : DetSEAlg K_e M C_e)
    (adv : OneTimeCCAAdversary AD M (C_e × T))
    (ke : K_e) : etmAEAD.ForgeAdversary (AD × C_e) T :=
  let spec := etmAEAD.forgeSpec (AD × C_e) T
  let unifImpl : QueryImpl unifSpec
      (StateT (EtmGameState AD C_e T) (OracleComp spec)) :=
    unifLiftStateT (EtmGameState AD C_e T) spec
  (Function.const Bool () <$>
    etmGameSkeleton (spec := spec)
      (pure ke)
      se.decrypt ∅
      (fun _ke m => pure (se.encrypt ke m))
      (fun q => do
        let t ← liftM (liftM (spec.query (Sum.inl (Sum.inr q))) : OracleComp spec T)
        pure t)
      (fun (ad, c) t => do
        let ok ← liftM (liftM (spec.query (Sum.inr ((ad, c), t))) : OracleComp spec Bool)
        pure ok)
      unifImpl
      adv : OracleComp spec Unit)

/-- Combined (collapsed) handler for the forge reduction: the AEAD oracle interface implemented
directly on the joint state `EtmGameState × ForgeState`, threading the reduction's local
`EtmGameState` (challenge + an unused, always-`∅` `TagCache`) alongside the forge experiment's
`ForgeState` (lazy-RO cache + eval'd points + `forged` flag).

This is the `simulateQ`-collapse target for `(simulateQ forgeImpl (forgeReduction se adv ke)).run`:
pushing `forgeImpl` through the reduction's inner skeleton handler (`mapStateTBase`) and flattening
the nested `StateT` yields exactly this handler (cf. the PRF hop's `hideal`). The encrypt oracle
forwards the tag computation to the forge **eval** oracle (recording the challenge point as the
unique eval'd point); the decrypt oracle forwards verification to the forge **verify** oracle
(setting `forged` on a successful verify at a not-eval'd point). -/
noncomputable def forgeJointImpl (se : DetSEAlg K_e M C_e) (ke : K_e) :
    QueryImpl (aeadOneTimeCCASpec AD M (C_e × T))
      (StateT (EtmGameState AD C_e T × etmAEAD.ForgeState (AD × C_e) T) ProbComp) :=
  -- unif oracle: thread both states unchanged
  ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (EtmGameState AD C_e T × etmAEAD.ForgeState (AD × C_e) T) ProbComp))
  -- encrypt oracle
  + (fun (ad, m) => do
      let (eg, fs) ← get
      match eg.1 with
      | some _ => pure none
      | none => do
        let c := se.encrypt ke m
        let (t, cache') ← (((AD × C_e) →ₒ T).randomOracle (ad, c)).run fs.1
        set (((some (c, t), eg.2) : EtmGameState AD C_e T),
          ((cache', insert (ad, c) fs.2.1, fs.2.2) : etmAEAD.ForgeState (AD × C_e) T))
        return some (c, t) :
      QueryImpl (AD × M →ₒ Option (C_e × T))
        (StateT (EtmGameState AD C_e T × etmAEAD.ForgeState (AD × C_e) T) ProbComp))
  -- decrypt oracle
  + (fun (ad, (c, t)) => do
      let (eg, fs) ← get
      if eg.1 == some (c, t) then pure none
      else do
        let (resp, cache') ← (((AD × C_e) →ₒ T).randomOracle (ad, c)).run fs.1
        let hit : Bool := t == resp
        let fs' : etmAEAD.ForgeState (AD × C_e) T :=
          (cache', fs.2.1, fs.2.2 || (hit && decide ((ad, c) ∉ fs.2.1)))
        set ((eg, fs') : EtmGameState AD C_e T × etmAEAD.ForgeState (AD × C_e) T)
        if hit then pure (se.decrypt ke c) else pure none :
      QueryImpl (AD × (C_e × T) →ₒ Option M)
        (StateT (EtmGameState AD C_e T × etmAEAD.ForgeState (AD × C_e) T) ProbComp))
