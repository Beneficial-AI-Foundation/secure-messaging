/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.AEAD.FromEtM.Construction
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.Coercions.Add

/-!
# Encrypt-then-MAC — Security

Security theorem for the EtM construction: the one-time IND-CCA advantage of
`etmAEAD se prf` is bounded by the PRF advantage of `prf`, the IND$-CPA
advantage of `se`, and `q_d/|T|` (tag-guessing probability per decryption
query, where `q_d` upper-bounds the adversary's decryption queries).

## Paper References

Our construction adapts **scheme A5** (= A2.100_111) from NRS14 Figure 2.
The security proof adapts **Theorem 1** (for A5), with:
- Concrete bound from **Figure 9**: `Adv^nAE ≤ Adv^prf + Adv^ivE + q_d/2^τ`
- Proof structure from **Lemma 3** (common opening) + **Appendix A.2** (auth bound)

## Structure

The proof uses an **OracleSpec-polymorphic game skeleton** so that games
(instantiated with `spec = unifSpec` = `ProbComp`) and reductions
(instantiated with `spec = PRFOracleSpec` or the IND$-CPA spec) are direct
instantiations of the same definition. Phase 2b proofs use `simulateQ`
compositionality.

Note: intermediate games cannot be `AEADScheme` instances because game hops
change internal components (e.g., replacing PRF with random oracle) while
preserving the oracle interface.

## NRS14 Correspondence

| Lean definition | NRS14 reference |
|---|---|
| `etmAEAD` | Figure 2, scheme A5, adapted: no nonce, one-time keys |
| `DetSEAlg` / `distAdvantage` | Section 2, ivE scheme / `Adv^ivE` (one query) |
| `PRFScheme` / `prfAdvantage` | Section 2, function family F / `Adv^prf` |
| `decryptQueryBound` / `q_d` | `q_d` in Appendix A.2; `IsQueryBoundP` on decrypt index |
| `game0` | Lemma 3 starting game (Figure 4 left: `Enc` + `Dec`) |
| `game1` | Lemma 3 eq. (4): replace F^tag with random ρ |
| `game2` | Appendix A.2: disable decryption (forgery bound) |
| `game3` | Figure 4 right column: `$` + `⊥` oracles |
| `game0_game1_le_prf` | Lemma 3 eq. (4): PRF hop, cost `Adv^prf` |
| `game1_game2_le_auth` | Appendix A.2, A5 Case 1: auth bound `q_d/2^τ` |
| `game2_game3_le_enc` | Lemma 3, privacy reduction D₁: cost `Adv^ivE` |
| `etmAEAD_security` | Theorem 1 for A5; Figure 9 bound |
| `prfReduction` | Lemma 3: adversary B(A) |
| `encReduction` | Lemma 3: privacy reduction D₁(A) |
-/

open OracleSpec OracleComp ENNReal PRFScheme AEADScheme

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]
  [Inhabited C_e] [Inhabited T]
  [SampleableType C_e] [SampleableType T]

/-! ## Type abbreviations -/

/-- Random oracle cache for the tag function `(AD × C_e) → T`. -/
abbrev TagCache (AD C_e T : Type) [DecidableEq (AD × C_e)] [SampleableType T] :=
  ((AD × C_e) →ₒ T).QueryCache

/-- Game state for the EtM security games: the challenge ciphertext (if
encryption was called) paired with the random oracle cache. -/
abbrev EtmGameState (AD C_e T : Type) [DecidableEq (AD × C_e)] [SampleableType T] :=
  Option (C_e × T) × TagCache AD C_e T

/-! ## Game skeleton -/

section Skeleton

/-- Parameterized EtM security game skeleton, polymorphic over the oracle spec.

Games instantiate with `spec := unifSpec` (= ProbComp).
Reductions instantiate with `spec := PRFOracleSpec` etc., forwarding
oracle queries through the parameters.

Additional setup (e.g., sampling a PRF key) happens OUTSIDE the skeleton
via closures captured by the oracle parameters.

The `unifImpl` parameter forwards the adversary's `unifSpec` queries to
`OracleComp spec`. For games (`spec = unifSpec`), this is the identity lift.
For reductions, this lifts through the SubSpec coercion.

NRS14 Lemma 3 + Appendix A.2: game-hopping proof structure for A5. -/
noncomputable def etmGameSkeleton
    {ι : Type} {spec : OracleSpec ι}
    (keygen_e : OracleComp spec K_e)
    (decrypt_c : K_e → C_e → Option M)
    (initCache : TagCache AD C_e T)
    (encryptMsg : K_e → M → StateT (TagCache AD C_e T) (OracleComp spec) C_e)
    (computeTag : AD × C_e → StateT (TagCache AD C_e T) (OracleComp spec) T)
    (verifyTag : AD × C_e → T → StateT (TagCache AD C_e T) (OracleComp spec) Bool)
    (unifImpl : QueryImpl unifSpec
        (StateT (EtmGameState AD C_e T) (OracleComp spec)))
    (adversary : OneTime_CCA_Adversary AD M (C_e × T))
    : OracleComp spec Bool := do
  let ke ← keygen_e
  let encImpl : QueryImpl (AD × M →ₒ Option (C_e × T))
      (StateT (EtmGameState AD C_e T) (OracleComp spec)) :=
    fun (ad, m) => do
      let (challenge, qc) ← get
      match challenge with
      | some _ => pure none
      | none => do
        let (c, qc1) ← (encryptMsg ke m).run qc
        let (t, qc2) ← (computeTag (ad, c)).run qc1
        set (some (c, t), qc2)
        return some (c, t)
  let decImpl : QueryImpl (AD × (C_e × T) →ₒ Option M)
      (StateT (EtmGameState AD C_e T) (OracleComp spec)) :=
    fun (ad, (c, t)) => do
      let (challenge, qc) ← get
      if challenge == some (c, t) then pure none
      else do
        let (ok, qc') ← (verifyTag (ad, c) t).run qc
        set (challenge, qc')
        if ok then pure (decrypt_c ke c) else pure none
  let impl := unifImpl + encImpl + decImpl
  let (b', _) ← (simulateQ impl adversary).run (none, initCache)
  return b'

end Skeleton

/-! ## Uniform oracle implementation (for games with spec = unifSpec) -/

/-- Forward `unifSpec` queries through `ProbComp` to `StateT GameState ProbComp`. -/
noncomputable def gameUnifImpl :
    QueryImpl unifSpec
      (StateT (EtmGameState AD C_e T) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (EtmGameState AD C_e T) ProbComp)

/-! ## Game instantiations (spec = unifSpec = ProbComp)

Each game is a skeleton instantiation with `spec := unifSpec`. All use state
type `TagCache` (empty cache `∅` when the random oracle is not needed).
Most hops change exactly one conceptual component. The game2 → game3 hop
changes both `encryptMsg` and `computeTag`, but the `computeTag` change
is distributional equality (the cache is written but never read once verify
is disabled, and a one-time fresh RO query is uniform). -/

/-- Game 0: real EtM. PRF key sampled outside skeleton, closed over in tag operations.

NRS14 Lemma 3: starting game (real nAE experiment). -/
noncomputable def game0
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) : ProbComp Bool := do
  let km ← prf.keygen
  etmGameSkeleton (spec := unifSpec)
    se.keygen se.decrypt ∅
    (fun ke m => pure (se.encrypt ke m))
    (fun (ad, c) => pure (prf.eval km (ad, c)))
    (fun (ad, c) t => pure (t == prf.eval km (ad, c)))
    gameUnifImpl
    adv

/-- Game 1: PRF replaced with lazy random oracle.

NRS14 Lemma 3, eq. (4): replace F^tag with random ρ.
Deviation: single encryption query (q_e = 1). -/
noncomputable def game1
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) : ProbComp Bool :=
  etmGameSkeleton (spec := unifSpec)
    se.keygen se.decrypt ∅
    (fun ke m => pure (se.encrypt ke m))
    (fun q => ((AD × C_e) →ₒ T).randomOracle q)
    (fun (ad, c) t => do
      let t' ← ((AD × C_e) →ₒ T).randomOracle (ad, c)
      pure (t == t'))
    gameUnifImpl
    adv

/-- Game 2: decrypt always rejects. Real encryption, random oracle tag.

NRS14 Appendix A.2: disable decryption by bounding forgery probability.
Each decrypt query at a fresh random oracle point verifies with probability
`1/|T|`; union bound over `q_d` queries gives `q_d/|T|`. -/
noncomputable def game2
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) : ProbComp Bool :=
  etmGameSkeleton (spec := unifSpec)
    se.keygen se.decrypt ∅
    (fun ke m => pure (se.encrypt ke m))
    (fun q => ((AD × C_e) →ₒ T).randomOracle q)
    (fun _ _ => pure false)
    gameUnifImpl
    adv

/-- Game 3: decrypt always rejects (random encrypt, random tag, no decryption).
Cache unused but present for type uniformity.

NRS14 Figure 4, right column: `$` oracle (random bits) + `⊥` oracle
(always reject). This is the ideal nAE experiment. -/
noncomputable def game3
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) : ProbComp Bool :=
  etmGameSkeleton (spec := unifSpec)
    se.keygen se.decrypt ∅
    (fun _ _ => liftM ($ᵗ C_e : ProbComp C_e))
    (fun _ => liftM ($ᵗ T : ProbComp T))
    (fun _ _ => pure false)
    gameUnifImpl
    adv

/-! ## Reduction instantiations

Reductions are skeleton instantiations with different `spec`, so they can
serve as adversaries for the underlying primitive's security game.

- `prfReduction`: game0 → game1 hop. Instantiates the skeleton with
  `spec = PRFOracleSpec`, forwarding tag queries to the external oracle.
- `encReduction`: game2 → game3 hop. Instantiates the skeleton with
  `spec = indCPASpec`, forwarding encryption to its oracle, sampling tags
  uniformly, and always rejecting decrypt (since `verifyTag = pure false`
  in both game2 and game3, no `ke` or `se.decrypt` access is needed).

The reduction bodies require VCVio's `PRFOracleSpec`/`indCPASpec` to be
`abbrev`s (or have registered `SubSpec`/`HasQuery` instances) for typeclass
synthesis. Since they are currently `def`s, we defer the bodies to Phase 2b.
The types are correct and sufficient for stating the security theorem. -/

/-- PRF reduction: skeleton with `spec = PRFOracleSpec`, tag queries forwarded
to the external oracle (which is either the real PRF or a random function).

NRS14 Lemma 3, eq. (4): reduction B(A) that distinguishes F^tag from ρ.

The body is a skeleton instantiation where `computeTag` and `verifyTag` forward
their queries to `OracleSpec.query (Sum.inr (ad, c))` — the PRF/random oracle
provided by the experiment. Phase 2b fills this in once VCVio's `PRFOracleSpec`
has the necessary typeclass instances. -/
noncomputable def prfReduction
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    : PRFAdversary (AD × C_e) T := by
  exact sorry

/-- IND$-CPA reduction: skeleton with `spec = indCPASpec`, encryption queries
forwarded to the external oracle (which is either real encryption or random).

NRS14 Lemma 3, privacy reduction D₁(A).

The reduction forwards encryption to `OracleSpec.query (Sum.inr m)` — the
real/random encryption oracle — samples tags uniformly, and always rejects
decrypt (since `verifyTag = pure false` in both game2 and game3). No access
to `ke` or `se.decrypt` is needed. Phase 2b fills in the body once VCVio's
oracle spec definitions have the necessary typeclass instances. -/
noncomputable def encReduction
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    : DetSEAlg.IndCPA_Adversary M C_e := by
  exact sorry

/-! ## Game-hop lemma signatures (Phase 2a: sorry'd, proved in Phase 2b) -/

/-- Game 0 equals the real AEAD experiment. -/
theorem game0_eq_real
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    [Fintype C_e] [Fintype T] :
    game0 se prf adv =
      AEADScheme.securityExpFixedBit (etmAEAD se prf) adv false := by
  sorry

/-- Game 0 → 1: PRF hop. Gap bounded by PRF advantage.

NRS14 Lemma 3, eq. (4): replace F^tag with random ρ. -/
theorem game0_game1_le_prf
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) :
    |(Pr[= true | game0 se prf adv]).toReal -
     (Pr[= true | game1 se adv]).toReal| ≤
      PRFScheme.prfAdvantage prf (prfReduction se adv) := by
  sorry

/-- Game 1 → 2: auth bound. Gap bounded by `q_d` times tag-guessing probability.

NRS14 Appendix A.2, A5 Case 1: each decrypt query at a fresh random oracle
point verifies with probability `1/|T|`. Union bound over `q_d` decrypt
queries gives `q_d/|T|`. The hypothesis `hqd` ties `q_d` to the adversary
via `IsQueryBoundP`: `adv` makes at most `q_d` decrypt-oracle queries
(structurally, on every execution path). -/
theorem game1_game2_le_auth
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    (q_d : ℕ) [Fintype T]
    (hqd : AEADScheme.decryptQueryBound adv q_d) :
    |(Pr[= true | game1 se adv]).toReal -
     (Pr[= true | game2 se adv]).toReal| ≤
      ↑q_d * (Fintype.card T : ℝ)⁻¹ := by
  sorry

/-- Game 2 → 3: IND$-CPA hop. Gap bounded by encryption advantage.

NRS14 Lemma 3, privacy reduction D₁(A). Since `verifyTag = pure false` in
both game2 and game3, no decrypt query ever reaches `se.decrypt`. The
IND$-CPA reduction only needs to simulate encryption (forward to its oracle)
and decryption (always reject). The `computeTag` change from random oracle
to `$ᵗ T` is distributional equality: the cache is written but never read
(verify disabled), and a one-time fresh RO query is uniformly distributed. -/
theorem game2_game3_le_enc
    (se : DetSEAlg K_e M C_e)
    (adv : OneTime_CCA_Adversary AD M (C_e × T)) :
    |(Pr[= true | game2 se adv]).toReal -
     (Pr[= true | game3 se adv]).toReal| ≤
      DetSEAlg.distAdvantage se (encReduction se adv) := by
  sorry

/-- Game 3 equals the random AEAD experiment. -/
theorem game3_eq_rand
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    [Fintype C_e] [Fintype T] :
    game3 se adv =
      AEADScheme.securityExpFixedBit (etmAEAD se prf) adv true := by
  sorry

/-! ## Main security theorem -/

/-- **EtM one-time IND-CCA security** (NRS14 Theorem 1 for A5, adapted).

The one-time IND-CCA distinguishing advantage of `etmAEAD se prf` is bounded
by the PRF advantage, the tag-guessing probability per decryption query, and
the IND$-CPA advantage:

  `Adv^{ot-cca-ror}_{EtM}(A) ≤ Adv^{prf}(B) + q_d/|T| + Adv^{ind$}(D)`

where `B = prfReduction se adv` and `D = encReduction se adv` are explicit
reductions (skeleton instantiations), and `q_d` upper-bounds the adversary's
number of decryption queries (tied to `adv` via `decryptQueryBound`, i.e.
`IsQueryBoundP` on the decrypt-oracle index).

NRS14 Figure 9 bound: `Adv^nAE ≤ Adv^prf_F(B) + Adv^ivE_E(D₁) + q_d/2^τ`.
Our one-time adaptation: `Adv^ivE → Adv^{ind$-cpa}`, `2^τ → |T|`. -/
theorem etmAEAD_security
    (se : DetSEAlg K_e M C_e) (prf : PRFScheme K_m (AD × C_e) T)
    (adv : OneTime_CCA_Adversary AD M (C_e × T))
    (q_d : ℕ) [Fintype C_e] [Fintype T]
    (hqd : AEADScheme.decryptQueryBound adv q_d) :
    AEADScheme.distAdvantage (etmAEAD se prf) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction se adv) +
      ↑q_d * (Fintype.card T : ℝ)⁻¹ +
      DetSEAlg.distAdvantage se (encReduction se adv) := by
  sorry
