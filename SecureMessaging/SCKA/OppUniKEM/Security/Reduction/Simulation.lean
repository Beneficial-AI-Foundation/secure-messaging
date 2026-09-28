/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Invariant
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Oracle
import ToVCVio.OracleComp.SimSemantics.StateT.OptionOutput

/-!
# Adaptive simulation with fixed selected-epoch material

**Parameters.** Fix `m ∈ support (sampleMaterial leak)`, selected epoch `e`,
challenge key `kStar`, and adversary `A` using the full security interface.
Assume deterministic decapsulation and correct erasure codes.

**Statement.** The reduction run with tuple `(m.pk, m.ciphertext, kStar)`
and the honest intermediate game stopped on exposure of `e` have equal
acceptance probabilities.

**Proof.** The relation maps an honest state through `markState e`.
`Invariant` preserves the honest transcript and selected source fields;
continuing stopped queries keep `e` unexposed. `Oracle.oracle_mark` gives
the joint response/state equality for each query. The generic state-map
simulation theorem lifts these facts to every adaptive adversary.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every supported material value, supplied key, and adversary, the
symbolic and stopped honest runs have equal acceptance probabilities from
related states satisfying transcript consistency, `pinnedSources`, and
non-exposure of the selected epoch. -/
theorem optionRun_mark_eq
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ) (kStar : K)
    (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s)
    (hsrc : pinnedSources m e s) (he : e ∉ s.exposed) :
    Pr[= true | optionRun
      (oracle base onoff ecEk ecCt0 ecCt1 leak e m.keygen.1.1 m.ciphertext kStar)
      adv (markState e s)] =
    Pr[= true | optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak m e kStar)
      adv s] := by
  apply probOutput_optionRun_eq_of_state_map _ _ (markState e)
    (fun s => (reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ pinnedSources m e s) ∧
      e ∉ s.exposed)
  · intro t s hs z hz hcont
    change z ∈ support (do
      let out ← (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e kStar t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain rfl := (mem_support_pure_iff _ _).mp hz
    have hex : e ∉ out.2.exposed := by
      by_contra h
      simp only [h, decide_true, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at hcont
    exact ⟨honestOracle_preserves_simulationInv base onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak m hm e kStar t s hs.1 out hout, hex⟩
  · intro t s hs
    exact oracle_mark base onoff ecEk ecCt0 ecCt1 leak m e kStar t s hs.1.1 hs.2
  · exact ⟨⟨hs, hsrc⟩, he⟩

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] in
/-- For every selected epoch, marking the honest initial state yields
exactly the simulator's initial state. All private fields and key tables
are absent, so every marker is absent as well. -/
theorem markState_initial
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure) (e : ℕ) :
    markState e (oppUniKemCKA.Reduction.Internal.initialGame (Sym := Sym) base onoff) =
      initial onoff := by
  simp [markState, markA, markB, initial, oppUniKemCKA.Reduction.Internal.initialGame,
    oppUniKemCKA.Reduction.Internal.initialA, oppUniKemCKA.Reduction.Internal.initialB,
    SCKAScheme.initGameState]

/-- Assume deterministic decapsulation and correct erasure codes. For every
supported material value, selected epoch, supplied key, and adversary, the
explicit simulator's acceptance probability equals that of the stopped
honest intermediate game from its initial state. -/
theorem run_eq_honestStopped
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ) (kStar : K)
    (adv : SecurityAdversary leak Sym) :
    Pr[= true | run base onoff ecEk ecCt0 ecCt1 leak adv e m.keygen.1.1 m.ciphertext kStar] =
    Pr[= true | optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak m e kStar)
      adv (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  have hrun : run base onoff ecEk ecCt0 ecCt1 leak adv e m.keygen.1.1 m.ciphertext kStar =
      optionRun (oracle base onoff ecEk ecCt0 ecCt1 leak e
        m.keygen.1.1 m.ciphertext kStar) adv (initial onoff) := by
    simp [run, optionRun, StateT.run'_eq, bind_pure_comp, Functor.map_map]
  rw [hrun, ← markState_initial base onoff e]
  exact optionRun_mark_eq base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak m hm e kStar adv _
    (reachableInv_init base onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
    (pinnedSources_initial base onoff leak m e)
    (by simp [oppUniKemCKA.Reduction.Internal.initialGame, SCKAScheme.initGameState])


/-- For every adversary, selected epoch, and KEM bit `b`, the reduction's
fixed branch has the same acceptance probability as: sample complete
material and a uniform key, then run the stopped honest game with the
material key for `b = true` and the uniform key for `b = false`. -/
theorem fixedBranch_eq_honestStopped
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (e : ℕ) (b : Bool) :
    Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b] =
    Pr[= true | do
      let m ← sampleMaterial leak
      let k ← ($ᵗ K : ProbComp K)
      optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak m e
        (if b then m.on.1.2 else k)) adv
        (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  rw [fixedBranch_eq_material]
  apply probOutput_bind_congr
  intro m hm
  apply probOutput_bind_congr
  intro k _
  exact run_eq_honestStopped base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak m hm e _ adv

end oppUniKemCKA.Security.Embedding
