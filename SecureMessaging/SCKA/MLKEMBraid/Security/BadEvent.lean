/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Risk
import SecureMessaging.SCKA.MLKEMBraid.Security.Hybrids
import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Stopping
import SecureMessaging.SCKA.MLKEMBraid.Security.Installed.Sampling

/-!
# Compatibility imports for trace analysis and installed games

The implementation is separated into trace instrumentation, conditional risk, endpoint hybrids
and installed operations. Historical stopped-step and sampling names below are exact-type thin
compatibility declarations; internal modules use their canonical lower-level interfaces.
-/

open OracleSpec OracleComp ENNReal

namespace MLKEMBraid.NoAuth

/-- Compatibility name for discarding an independent total sample in distribution. -/
theorem evalDist_bind_ignore {α β : Type} (mx : ProbComp α) (my : ProbComp β) :
    𝒟[mx >>= fun _ => my] = 𝒟[my] :=
  OracleComp.ProgramLogic.Relational.evalDist_bind_const_of_no_failure mx my

/-- Compatibility name for the joint run equation of a stopped oracle step. -/
theorem stopOnState_run {ι σ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool) (t : spec.Domain) (s : σ) :
    ((stopOnState impl stop t).run).run s =
      (fun w => (if stop w.2 then none else some w.1, w.2)) <$> (impl t).run s :=
  OracleComp.stopOnState_run impl stop t s

/-- Compatibility name for support of a stopped oracle step. -/
theorem mem_support_stopOnState {ι σ : Type} {spec : OracleSpec ι}
    {impl : QueryImpl spec (StateT σ ProbComp)} {stop : σ → Bool} {t : spec.Domain} {s : σ}
    {z : Option (spec.Range t) × σ}
    (hz : z ∈ support (((stopOnState impl stop t).run).run s)) :
    ∃ w ∈ support ((impl t).run s), z = (if stop w.2 then none else some w.1, w.2) :=
  OracleComp.mem_support_stopOnState hz

/-- Compatibility name for a discarded independent total sample at one output. -/
theorem probOutput_bind_const' {α β : Type} (mx : ProbComp α) (my : ProbComp β) (y : β) :
    Pr[= y | mx >>= fun _ => my] = Pr[= y | my] :=
  ToVCVio.probOutput_bind_of_const' mx (fun _ _ => rfl)

/-- Compatibility name for stopping congruence of joint step distributions. -/
theorem stopped_congr {ι σ : Type} {spec : OracleSpec ι}
    {I L : QueryImpl spec (StateT σ ProbComp)} (stop : σ → Bool) (q : spec.Domain) (s : σ)
    (h : 𝒟[(I q).run s] = 𝒟[(L q).run s]) :
    𝒟[((stopOnState I stop q).run).run s] = 𝒟[((stopOnState L stop q).run).run s] :=
  OracleComp.stopped_congr stop q s h

/-- Compatibility name for sampling a parameter before one stopped step. -/
theorem stopped_bind {ι σ α : Type} {spec : OracleSpec ι} (sample : ProbComp α)
    {I : α → QueryImpl spec (StateT σ ProbComp)} {L : QueryImpl spec (StateT σ ProbComp)}
    (stop : σ → Bool) (q : spec.Domain) (s : σ)
    (h : 𝒟[(L q).run s] = 𝒟[sample >>= fun a => (I a q).run s]) :
    𝒟[((stopOnState L stop q).run).run s] =
      𝒟[sample >>= fun a => ((stopOnState (I a) stop q).run).run s] :=
  OracleComp.stopped_bind sample stop q s h

/-- Compatibility name for the canonical once-used-sample installation comparison. -/
theorem optionRun_install {ι σ α : Type} {spec : OracleSpec ι} (sample : ProbComp α)
    (I : α → QueryImpl spec (OptionT (StateT σ ProbComp)))
    (L : QueryImpl spec (OptionT (StateT σ ProbComp))) (Inv used : σ → Prop)
    (hit : spec.Domain → σ → Bool)
    (hpres : ∀ a ∈ support sample, ∀ t s, Inv s →
      ∀ z ∈ support (((I a t).run).run s), z.1.isSome → Inv z.2)
    (hused : ∀ a ∈ support sample, ∀ t s, Inv s → used s →
      ∀ z ∈ support (((I a t).run).run s), z.1.isSome → used z.2)
    (hnohit : ∀ t s, Inv s → used s → hit t s = false)
    (hfirst : ∀ a ∈ support sample, ∀ t s, Inv s → hit t s = true →
      ∀ z ∈ support (((I a t).run).run s), z.1.isSome → used z.2)
    (hoff : ∀ t s, Inv s → hit t s = false → ∀ a ∈ support sample,
      𝒟[((I a t).run).run s] = 𝒟[((L t).run).run s])
    (hon : ∀ t s, Inv s → hit t s = true →
      𝒟[((L t).run).run s] = 𝒟[sample >>= fun a => ((I a t).run).run s])
    (oa : OracleComp spec Bool) (s : σ) (hs : Inv s) :
    Pr[= true | sample >>= fun a => optionRun (I a) oa s] = Pr[= true | optionRun L oa s] :=
  OracleComp.optionRun_install sample I L Inv used hit hpres hused hnohit hfirst hoff hon oa s hs

end MLKEMBraid.NoAuth
