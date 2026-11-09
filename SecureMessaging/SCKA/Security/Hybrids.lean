/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.Security
public import SecureMessaging.SCKA.Security.CorrectnessOracles
public import ToVCVio.OracleComp.QueryTracking.OneUseSampling
public import ToVCVio.OracleComp.SimSemantics.StateT.Stop
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Epoch hybrids over state-dependent security oracles

Let `schemeOf` assign an SCKA scheme to each game state, `chall` be a challenge oracle on game
states, `vulnA`, `vulnB` exposure policies, and `adv` an SCKA adversary. The security oracles
`securityImplAt schemeOf chall vulnA vulnB` answer a query from a game state `s` by running the
security oracles `securityImplOf` over the instance `schemeOf s` (`securityImplAt_run`), with the
challenge oracle `chall` and the corruption oracles of the policies.

A *challenge mode* `μ : ℕ → Bool` decides which epochs' challenges get random keys: the oracles
`modeImpl μ` answer an eligible challenge at `t` with an independent uniform key if `μ t` and the
recorded key otherwise (`challOf μ`). The *hybrid* `H_i` runs `adv` against
`hybridImpl i := modeImpl μ_i`; the hybrids switch from real to uniform keys one epoch at a time.
For `e > 0`, the *stopped hybrids* `S_e^real` and `S_e^random` are the hybrids adjacent at `e`,
returning `false` at the first exposure of `e`:

```text
μ_i(t)     := (0 < t ≤ i)             -- H_i: uniform keys at epochs 1, …, i
S_e^real   := H_{e-1} stopped at e    -- real key at e
S_e^random := H_e     stopped at e    -- uniform key at e
```

The modes of `H_{e-1}` and `H_e` are `adjacentMode e false` and `adjacentMode e true`. For an
epoch `e` and a key `k*`, the *pinned challenge* `pinnedChallenge e k*` answers an eligible
challenge at `t` with a uniform key if `0 < t < e`, with `k*` if `t = e`, and with the recorded
key otherwise.

**Results.**

- *Oracles.* A predicate that ignores the exposed and challenged epochs and is preserved by the
  correctness queries of each instance is preserved by every query, when the ordinary sends
  forget the coins of the leaking sends and `chall` records challenges
  (`securityImplAt_preservesInv`); in particular, a message recorded at an index at most the
  party's send counter is kept (`securityImplAt_preserves_recordedA`,
  `securityImplAt_preserves_recordedB`). Averaging over a sampled family of instances whose sends
  have the distributions of those of a target instance, and whose receives agree with the
  target's, gives the target query (`securityImplAt_sample_eq`); two families that agree on the
  algorithm that a query runs give related queries (`securityImplAt_congr`).
- *Endpoints.* `H_0` is the real-key game: `μ_0` randomizes no epoch (`hybridMode_zero`). Let `adv`
  make at most `q` ordinary and leaking sends on every response path
  (`SecuritySendQueryBound adv q`, `SCKA.Defs`). If an invariant preserved by every mode places
  every epoch with a recorded key in `1, …, nA + nB`, then `H_q` and the uniform-key game (mode
  `fun _ => true`) accept equally often from an initial state that satisfies the invariant and has
  no sends (`prEvent_hybridImpl_last_eq`).
- *Stopping.* From a state with `Disjoint exposed challenged`, stopping at the first exposure of
  `e` preserves the difference between adjacent hybrids (`hybridImpl_signed_gap_stop_eq`, stated
  for `e = i + 1`):

  ```text
  Pr[S_e^random = true] - Pr[S_e^real = true] = Pr[H_e = true] - Pr[H_{e-1} = true]
  ```

- *Pinned challenge.* From a state whose keys recorded at `e` equal `k*`, the pinned challenge
  answers as the oracles of `H_{e-1}` (`securityImplAt_pinnedChallenge_eq_recorded`). For `e > 0`,
  drawing `k*` uniformly and stopping at the first exposure of `e` gives `S_e^random`
  (`stoppedRun_pinnedChallenge_sample_eq`).
-/

@[expose] public section

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type}

/-! ### Send counters -/

section Counters

variable [DecidableEq I]

/-- Every possible successor `s'` of a correctness query `t` from `s` has
`s'.nA + s'.nB ≤ s.nA + s.nB + (if t is a send then 1 else 0)`. -/
private theorem correctnessImpl_sends_step
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (t : (sckaCorrectnessSpec Rho).Domain) (s : GameState StA StB I Rho)
    (z : (sckaCorrectnessSpec Rho).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((sckaCorrectnessImpl scka t).run s)) :
    z.2.nA + z.2.nB ≤ s.nA + s.nB + if isSendQuery t then 1 else 0 := by
  rcases t with ((((n | u) | u) | n) | n)
  · rw [mem_support_oracleUnif_run n s z hz]
    simp [isSendQuery]
  · cases u
    obtain ⟨out, _, rfl⟩ := (mem_support_oracleSendA_run_iff scka s z).mp hz
    rcases out with _ | ⟨_ | ⟨_, _⟩, _, _, _⟩
    · simp [isSendQuery]
    all_goals simp only [sendAUpdate, isSendQuery, ↓reduceIte]; omega
  · cases u
    obtain ⟨out, _, rfl⟩ := (mem_support_oracleSendB_run_iff scka s z).mp hz
    rcases out with _ | ⟨_ | ⟨_, _⟩, _, _, _⟩
    · simp [isSendQuery]
    all_goals simp only [sendBUpdate, isSendQuery, ↓reduceIte]; omega
  · rcases (mem_support_oracleRecvA_run_iff scka s n z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _ | ⟨_, _⟩, _, _, _, _, rfl⟩
    all_goals simp [recvAUpdate, isSendQuery]
  · rcases (mem_support_oracleRecvB_run_iff scka s n z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _ | ⟨_, _⟩, _, _, _, _, rfl⟩
    all_goals simp [recvBUpdate, isSendQuery]

/-- If `base` raises `nA + nB` by at most one on sends and not otherwise, and `chall` records
challenges, every possible successor `s'` of a family query `t` from `s` has
`s'.nA + s'.nB ≤ s.nA + s.nB + (if t is a send then 1 else 0)`. -/
private theorem securityImplOf_sends_step
    (base : QueryImpl (sckaCorrectnessSpec Rho) (StateT (GameState StA StB I Rho) ProbComp))
    (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
    (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (hbase : ∀ t s z, z ∈ support ((base t).run s) →
      z.2.nA + z.2.nB ≤ s.nA + s.nB + if isSendQuery t then 1 else 0)
    (hchall : RecordsChallenges chall)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    z.2.nA + z.2.nB ≤ s.nA + s.nB + if sckaSecuritySpec.isSendQuery t then 1 else 0 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [sckaSecuritySpec.isSendQuery_OCorrectness]
    exact hbase t s z hz
  · cases u
    rcases oracleSendArleak_run_cases scka vulnA.rleak s z hz with
      rfl | ⟨_ | ⟨_, _⟩, _, _, _, _, -, -, h⟩
    · simp [sckaSecuritySpec.isSendQuery]
    all_goals rw [h]; simp only [sendAUpdate, sckaSecuritySpec.isSendQuery, ↓reduceIte]; omega
  · cases u
    rcases oracleSendBrleak_run_cases scka vulnB.rleak s z hz with
      rfl | ⟨_ | ⟨_, _⟩, _, _, _, _, -, -, h⟩
    · simp [sckaSecuritySpec.isSendQuery]
    all_goals rw [h]; simp only [sendBUpdate, sckaSecuritySpec.isSendQuery, ↓reduceIte]; omega
  · rcases hchall t s z hz with h | ⟨_, h⟩ <;> rw [h] <;> simp [sckaSecuritySpec.isSendQuery]
  · cases u
    rcases oracleCorruptA_support vulnA.corrupt s z hz with rfl | ⟨_, rfl⟩ <;>
      simp [sckaSecuritySpec.isSendQuery]
  · cases u
    rcases oracleCorruptB_support vulnB.corrupt s z hz with rfl | ⟨_, rfl⟩ <;>
      simp [sckaSecuritySpec.isSendQuery]

/-! ### Recorded messages are kept -/

/-- A message recorded by A at an index at most `nA` is kept, with the index bound, by every
correctness query. -/
private theorem correctnessImpl_preserves_recordedA
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (n : ℕ) (x : Rho × ℕ)
    (t : (sckaCorrectnessSpec Rho).Domain) (s : GameState StA StB I Rho)
    (h : n ≤ s.nA ∧ s.msgA n = some x)
    (z : (sckaCorrectnessSpec Rho).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((sckaCorrectnessImpl scka t).run s)) :
    n ≤ z.2.nA ∧ z.2.msgA n = some x := by
  rcases t with ((((m | u) | u) | m) | m)
  · rw [mem_support_oracleUnif_run m s z hz]
    exact h
  · cases u
    obtain ⟨out, _, rfl⟩ := (mem_support_oracleSendA_run_iff scka s z).mp hz
    rcases out with _ | ⟨_ | ⟨tI, key⟩, ρ, tsnd, stA'⟩
    · exact h
    all_goals
      simp only [sendAUpdate, Function.update_of_ne (show n ≠ s.nA + 1 by omega), h.2]
      exact ⟨by omega, trivial⟩
  · cases u
    obtain ⟨out, _, rfl⟩ := (mem_support_oracleSendB_run_iff scka s z).mp hz
    rcases out with _ | ⟨_ | ⟨tI, key⟩, ρ, tsnd, stB'⟩
    · exact h
    all_goals simpa [sendBUpdate] using h
  · rcases (mem_support_oracleRecvA_run_iff scka s m z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _ | ⟨_, _⟩, _, _, _, _, rfl⟩
    all_goals simpa [recvAUpdate] using h
  · rcases (mem_support_oracleRecvB_run_iff scka s m z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _ | ⟨_, _⟩, _, _, _, _, rfl⟩
    all_goals simpa [recvBUpdate] using h

/-- B version of `correctnessImpl_preserves_recordedA`. -/
private theorem correctnessImpl_preserves_recordedB
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (n : ℕ) (x : Rho × ℕ)
    (t : (sckaCorrectnessSpec Rho).Domain) (s : GameState StA StB I Rho)
    (h : n ≤ s.nB ∧ s.msgB n = some x)
    (z : (sckaCorrectnessSpec Rho).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((sckaCorrectnessImpl scka t).run s)) :
    n ≤ z.2.nB ∧ z.2.msgB n = some x := by
  rcases t with ((((m | u) | u) | m) | m)
  · rw [mem_support_oracleUnif_run m s z hz]
    exact h
  · cases u
    obtain ⟨out, _, rfl⟩ := (mem_support_oracleSendA_run_iff scka s z).mp hz
    rcases out with _ | ⟨_ | ⟨tI, key⟩, ρ, tsnd, stA'⟩
    · exact h
    all_goals simpa [sendAUpdate] using h
  · cases u
    obtain ⟨out, _, rfl⟩ := (mem_support_oracleSendB_run_iff scka s z).mp hz
    rcases out with _ | ⟨_ | ⟨tI, key⟩, ρ, tsnd, stB'⟩
    · exact h
    all_goals
      simp only [sendBUpdate, Function.update_of_ne (show n ≠ s.nB + 1 by omega), h.2]
      exact ⟨by omega, trivial⟩
  · rcases (mem_support_oracleRecvA_run_iff scka s m z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _ | ⟨_, _⟩, _, _, _, _, rfl⟩
    all_goals simpa [recvAUpdate] using h
  · rcases (mem_support_oracleRecvB_run_iff scka s m z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _ | ⟨_, _⟩, _, _, _, _, rfl⟩
    all_goals simpa [recvBUpdate] using h

end Counters

/-! ### The state-dependent family -/

section StateDependent

variable [DecidableEq I]
variable (schemeOf : GameState StA StB I Rho → SCKAScheme ProbComp IK StA StB I Rho Rand)
variable (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
variable (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)

/-- SCKA security oracles, where each query runs the protocol instance chosen from the current game
state, challenges are answered by `chall`, and corruptions and leaking sends are guarded by the
exposure policies `vulnA`, `vulnB`. -/
def securityImplAt :
    QueryImpl (sckaSecuritySpec StA StB I Rho Rand) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun t => (get : StateT (GameState StA StB I Rho) ProbComp (GameState StA StB I Rho)) >>= fun s =>
    securityImplOf (sckaCorrectnessImpl (schemeOf s)) chall vulnA vulnB (schemeOf s) t

/-- Unfolding of `securityImplAt`: from a game state `s`, each query runs the security oracles
`securityImplOf` over the instance `schemeOf s` chosen from `s`, kept fixed for the whole query. -/
theorem securityImplAt_run (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (s : GameState StA StB I Rho) :
    (securityImplAt schemeOf chall vulnA vulnB t).run s =
      (securityImplOf (sckaCorrectnessImpl (schemeOf s)) chall vulnA vulnB
        (schemeOf s) t).run s := by
  simp only [securityImplAt, StateT.run_bind, StateT.run_get, pure_bind]

/-- Let `Inv` ignore `exposed` and `challenged`, the ordinary sends of each `schemeOf s` forget
the coins of its leaking sends, and `chall` record challenges. If the correctness queries of each
`schemeOf s` preserve `Inv` from `s`, then every query of
`securityImplAt schemeOf chall vulnA vulnB` preserves `Inv`. -/
theorem securityImplAt_preservesInv
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed challenged, Inv s →
      Inv { s with exposed := exposed, challenged := challenged })
    (hmA : ∀ s st, (do
      let out ← (schemeOf s).sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendA st)
    (hmB : ∀ s st, (do
      let out ← (schemeOf s).sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendB st)
    (hchall : RecordsChallenges chall)
    (hbase : ∀ s, Inv s → ∀ t z,
      z ∈ support ((sckaCorrectnessImpl (schemeOf s) t).run s) → Inv z.2) :
    QueryImpl.PreservesInv (securityImplAt schemeOf chall vulnA vulnB) Inv := by
  intro t s hs z hz
  rw [securityImplAt_run] at hz
  exact securityImplOf_preserves_at_of_book _ _ _ _ _ Inv hbook (hmA s) (hmB s) s hs (hbase s hs)
    (fun t => hchall.preservesInv Inv (fun s C h => by simpa using hbook s s.exposed C h) t s hs)
    (hbase s hs sckaCorrectnessSpec.OSendA) (hbase s hs sckaCorrectnessSpec.OSendB) t z hz

/-- If `chall` records challenges, no query removes an exposed epoch. -/
private theorem securityImplAt_preserves_exposed (hchall : RecordsChallenges chall) (e : ℕ) :
    QueryImpl.PreservesInv (securityImplAt schemeOf chall vulnA vulnB)
      (fun s => e ∈ s.exposed) := by
  intro t s hs z hz
  rw [securityImplAt_run] at hz
  exact securityImplOf_exposed_subset _ _ _ _ _
    (fun t s z hz => (correctnessImpl_securitySets_eq _ t s z hz).1) hchall t s z hz hs

/-- If `chall` records challenges, no query removes a challenged epoch. -/
private theorem securityImplAt_preserves_challenged (hchall : RecordsChallenges chall) (e : ℕ) :
    QueryImpl.PreservesInv (securityImplAt schemeOf chall vulnA vulnB)
      (fun s => e ∈ s.challenged) := by
  intro t s hs z hz
  rw [securityImplAt_run] at hz
  exact securityImplOf_challenged_subset _ _ _ _ _
    (fun t s z hz => (correctnessImpl_securitySets_eq _ t s z hz).2) hchall t s z hz hs

/-- If `chall` records challenges, every query preserves `Disjoint exposed challenged`. -/
private theorem securityImplAt_preserves_disjoint (hchall : RecordsChallenges chall) :
    QueryImpl.PreservesInv (securityImplAt schemeOf chall vulnA vulnB)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro t s hs z hz
  rw [securityImplAt_run] at hz
  exact securityImplOf_preserves_disjoint _ _ _ _ _
    (fun t s z hz => correctnessImpl_securitySets_eq _ t s z hz) hchall t s hs z hz

/-- If `chall` records challenges, every possible successor `s'` of a query `t` from `s` has
`s'.nA + s'.nB ≤ s.nA + s.nB + (if t is a send then 1 else 0)`. -/
private theorem securityImplAt_sends_step (hchall : RecordsChallenges chall)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplAt schemeOf chall vulnA vulnB t).run s)) :
    z.2.nA + z.2.nB ≤ s.nA + s.nB + if sckaSecuritySpec.isSendQuery t then 1 else 0 := by
  rw [securityImplAt_run] at hz
  exact securityImplOf_sends_step _ _ _ _ _ (correctnessImpl_sends_step _) hchall t s z hz

/-- Fix `s`. If, averaged over `a ← sample`, the four sends of
`schemeOf a s` have the distributions of those of `target s`, and the receives agree for every
`a ∈ support sample`, then averaging `securityImplAt (schemeOf a) chall vulnA vulnB t` from `s`
over `a` gives the joint response/state distribution of `securityImplAt target chall vulnA vulnB t`
from `s`. -/
theorem securityImplAt_sample_eq {τ : Type} (sample : ProbComp τ)
    (schemeOf : τ → GameState StA StB I Rho → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : GameState StA StB I Rho → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (s : GameState StA StB I Rho)
    (hsendA : (do let a ← sample; (schemeOf a s).sendA s.stA) =ᵈ (target s).sendA s.stA)
    (hsendB : (do let a ← sample; (schemeOf a s).sendB s.stB) =ᵈ (target s).sendB s.stB)
    (hsendArleak : (do let a ← sample; (schemeOf a s).sendArleak s.stA) =ᵈ
      (target s).sendArleak s.stA)
    (hsendBrleak : (do let a ← sample; (schemeOf a s).sendBrleak s.stB) =ᵈ
      (target s).sendBrleak s.stB)
    (hrecvA : ∀ a ∈ support sample, ∀ ρ,
      (schemeOf a s).recvA s.stA ρ = (target s).recvA s.stA ρ)
    (hrecvB : ∀ a ∈ support sample, ∀ ρ,
      (schemeOf a s).recvB s.stB ρ = (target s).recvB s.stB ρ)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) :
    (do let a ← sample; (securityImplAt (schemeOf a) chall vulnA vulnB t).run s) =ᵈ
      (securityImplAt target chall vulnA vulnB t).run s := by
  simp only [securityImplAt_run]
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · exact OracleComp.EvalDistEq.bind_const_of_support sample fun _ _ => rfl
    · cases u
      simp only [securityImplOf, sckaCorrectnessImpl, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr]
      exact oracleSendA_sample_eq _ _ _ s hsendA
    · cases u
      simp only [securityImplOf, sckaCorrectnessImpl, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr]
      exact oracleSendB_sample_eq _ _ _ s hsendB
    · simp only [securityImplOf, sckaCorrectnessImpl, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr]
      exact OracleComp.EvalDistEq.bind_const_of_support sample fun a ha =>
        oracleRecvA_run_congr _ _ s (hrecvA a ha) n
    · simp only [securityImplOf, sckaCorrectnessImpl, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr]
      exact OracleComp.EvalDistEq.bind_const_of_support sample fun a ha =>
        oracleRecvB_run_congr _ _ s (hrecvB a ha) n
  · cases u
    simp only [securityImplOf, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    exact oracleSendArleak_sample_eq _ _ _ _ s hsendArleak
  · cases u
    simp only [securityImplOf, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    exact oracleSendBrleak_sample_eq _ _ _ _ s hsendBrleak
  all_goals exact OracleComp.EvalDistEq.bind_const_of_support sample fun _ _ => rfl

open sckaSecuritySpec sckaCorrectnessSpec in
/-- Congruence at one query. Let `R` be a reflexive relation on computations, `target` a second
assignment of instances, `s` a game state and `t` a query. Assume that `schemeOf s` and `target s`
agree on the algorithm that `t` runs from the local states of `s`: the send of an ordinary send,
and the receive on the message delivered by a receive. Assume also that, for a leaking send `t`,
the leaking-send queries of the two instances from `s` are related by `R`. Then the queries `t`
from `s` of `securityImplAt schemeOf` and `securityImplAt target`, with the same `chall`, are
related by `R`. -/
theorem securityImplAt_congr {R : {α : Type} → ProbComp α → ProbComp α → Prop}
    (hrefl : ∀ {α} (p : ProbComp α), R p p)
    (target : GameState StA StB I Rho → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (s : GameState StA StB I Rho) (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (hsendA : t = OCorrectness OSendA → (schemeOf s).sendA s.stA = (target s).sendA s.stA)
    (hsendB : t = OCorrectness OSendB → (schemeOf s).sendB s.stB = (target s).sendB s.stB)
    (hrecvA : ∀ n, t = OCorrectness (ORecvA n) → ∀ ρ tsnd, s.msgB n = some (ρ, tsnd) →
      (schemeOf s).recvA s.stA ρ = (target s).recvA s.stA ρ)
    (hrecvB : ∀ n, t = OCorrectness (ORecvB n) → ∀ ρ tsnd, s.msgA n = some (ρ, tsnd) →
      (schemeOf s).recvB s.stB ρ = (target s).recvB s.stB ρ)
    (hleakA : t = OSendArleak →
      R ((oracleSendArleak vulnA.rleak (schemeOf s) ()).run s)
        ((oracleSendArleak vulnA.rleak (target s) ()).run s))
    (hleakB : t = OSendBrleak →
      R ((oracleSendBrleak vulnB.rleak (schemeOf s) ()).run s)
        ((oracleSendBrleak vulnB.rleak (target s) ()).run s)) :
    R ((securityImplAt schemeOf chall vulnA vulnB t).run s)
      ((securityImplAt target chall vulnA vulnB t).run s) := by
  rcases t with (((((t | u) | u) | n) | u) | u) <;>
    try rcases t with ((((n | u) | u) | n) | n)
  all_goals try cases u
  all_goals simp only [securityImplAt_run, securityImplOf, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, sckaCorrectnessImpl]
  · exact hrefl _
  · rw [oracleSendA_run_congr _ _ s (hsendA rfl)]
    exact hrefl _
  · rw [oracleSendB_run_congr _ _ s (hsendB rfl)]
    exact hrefl _
  · have h : (oracleRecvA (schemeOf s) n).run s = (oracleRecvA (target s) n).run s := by
      simp only [oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
      cases hm : s.msgB n with
      | none => rfl
      | some entry =>
        rcases entry with ⟨ρ, tsnd⟩
        simp only
        rw [hrecvA n rfl ρ tsnd hm]
    rw [h]
    exact hrefl _
  · have h : (oracleRecvB (schemeOf s) n).run s = (oracleRecvB (target s) n).run s := by
      simp only [oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind]
      cases hm : s.msgA n with
      | none => rfl
      | some entry =>
        rcases entry with ⟨ρ, tsnd⟩
        simp only
        rw [hrecvB n rfl ρ tsnd hm]
    rw [h]
    exact hrefl _
  · exact hleakA rfl
  · exact hleakB rfl
  · exact hrefl _
  · exact hrefl _
  · exact hrefl _

/-- A message recorded by A at an index at most `nA` is kept, with the index bound, by every
query of `securityImplAt`, when the ordinary sends of each instance forget the coins of its leaking
sends and `chall` records challenges. -/
theorem securityImplAt_preserves_recordedA
    (hmA : ∀ s st, (do
      let out ← (schemeOf s).sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendA st)
    (hmB : ∀ s st, (do
      let out ← (schemeOf s).sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendB st)
    (hchall : RecordsChallenges chall) (n : ℕ) (x : Rho × ℕ) :
    QueryImpl.PreservesInv (securityImplAt schemeOf chall vulnA vulnB)
      (fun s => n ≤ s.nA ∧ s.msgA n = some x) :=
  securityImplAt_preservesInv schemeOf chall vulnA vulnB _ (fun _ _ _ h => h) hmA hmB hchall
    fun s hs t z hz => correctnessImpl_preserves_recordedA _ n x t s hs z hz

/-- B version of `securityImplAt_preserves_recordedA`. -/
theorem securityImplAt_preserves_recordedB
    (hmA : ∀ s st, (do
      let out ← (schemeOf s).sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendA st)
    (hmB : ∀ s st, (do
      let out ← (schemeOf s).sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        (schemeOf s).sendB st)
    (hchall : RecordsChallenges chall) (n : ℕ) (x : Rho × ℕ) :
    QueryImpl.PreservesInv (securityImplAt schemeOf chall vulnA vulnB)
      (fun s => n ≤ s.nB ∧ s.msgB n = some x) :=
  securityImplAt_preservesInv schemeOf chall vulnA vulnB _ (fun _ _ _ h => h) hmA hmB hchall
    fun s hs t z hz => correctnessImpl_preserves_recordedB _ n x t s hs z hz

end StateDependent

open ENNReal

/-! ### Challenge modes and epoch hybrids -/

/-- Challenge mode of the hybrid `H_i`: a challenge at epoch `t` returns a uniform key iff
`0 < t ∧ t ≤ i`, and the recorded key otherwise. -/
def hybridMode (i t : ℕ) : Bool := decide (0 < t ∧ t ≤ i)

/-- `H_0` randomizes no epoch. -/
theorem hybridMode_zero : hybridMode 0 = fun _ => false := by
  funext t
  simp only [hybridMode, decide_eq_false_iff_not]
  omega

/-- Challenge mode of the hybrids adjacent at `e`: `adjacentMode e false` is the mode of `H_{e-1}`
and `adjacentMode e true` that of `H_e`, so a challenge at epoch `t` returns a uniform key (`U`)
iff `0 < t < e`, or `t = e` and `b = true`, and the recorded key (`R`) otherwise:

```text
epoch                  1   …   e-1   e   e+1  …
adjacentMode e false   U   …   U     R   R    …      (H_{e-1}, version real)
adjacentMode e true    U   …   U     U   R    …      (H_e, version random)
```
-/
def adjacentMode (e : ℕ) (b : Bool) : ℕ → Bool := hybridMode (if b then e else e - 1)

/-- `adjacentMode e b t` randomizes `t` iff `0 < t < e`, or `t = e` and `b = true`. -/
theorem adjacentMode_apply (e : ℕ) (b : Bool) (t : ℕ) :
    adjacentMode e b t = decide (0 < t ∧ (t < e ∨ (b = true ∧ t = e))) := by
  cases b <;> simp only [adjacentMode, hybridMode, Bool.false_eq_true, ↓reduceIte, false_and,
    or_false, true_and, decide_eq_decide] <;> omega

/-- For `t ≠ i + 1`, the challenge oracles of `H_{i+1}` and `H_i` agree on `t`. -/
private theorem hybridMode_challenge_eq_of_ne [SampleableType I] (i t : ℕ) (hne : t ≠ i + 1) :
    oracleChall (hybridMode (i + 1) t) StA StB I Rho t =
      oracleChall (hybridMode i t) StA StB I Rho t := by
  have h : (0 < t ∧ t ≤ i + 1) ↔ (0 < t ∧ t ≤ i) := by omega
  simp only [hybridMode, h]

section Hybrids

variable [DecidableEq I] [SampleableType I]
variable (schemeOf : GameState StA StB I Rho → SCKAScheme ProbComp IK StA StB I Rho Rand)
variable (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)

/-- The oracles of the proof game with challenge mode `mode`. -/
abbrev modeImpl (mode : ℕ → Bool) :=
  securityImplAt schemeOf (challOf mode) vulnA vulnB

/-- The oracles of the hybrid `H_i`. -/
abbrev hybridImpl (i : ℕ) := modeImpl schemeOf vulnA vulnB (hybridMode i)

/-- If `i + 1` is exposed, `H_{i+1}` and `H_i` answer every query by equal response/state
computations. -/
private theorem hybridImpl_query_eq_of_exposed (i : ℕ)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (hs : i + 1 ∈ s.exposed) :
    (hybridImpl schemeOf vulnA vulnB (i + 1) t).run s =
      (hybridImpl schemeOf vulnA vulnB i t).run s := by
  simp only [securityImplAt_run]
  refine securityImplOf_run_eq _ _ _ _ _ _ _ s (fun _ => rfl) ?_ t
  intro t
  by_cases ht : t = i + 1
  · subst t
    exact oracleChall_run_eq_of_rejected _ _ s _ (Or.inl (Or.inl hs))
  · simp only [challOf]
    rw [hybridMode_challenge_eq_of_ne i t ht]

/-- If `i + 1` is exposed, `H_{i+1}` and `H_i` give equal output/state computations for every
continuation `adv`. -/
private theorem hybridImpl_run_eq_of_exposed (i : ℕ) {α : Type}
    (adv : OracleComp (sckaSecuritySpec StA StB I Rho Rand) α) (s : GameState StA StB I Rho)
    (hs : i + 1 ∈ s.exposed) :
    (simulateQ (hybridImpl schemeOf vulnA vulnB (i + 1)) adv).run s =
      (simulateQ (hybridImpl schemeOf vulnA vulnB i) adv).run s := by
  have h := map_run_simulateQ_eq_of_query_map_eq_inv'
    (hybridImpl schemeOf vulnA vulnB (i + 1)) (hybridImpl schemeOf vulnA vulnB i)
    (fun state => i + 1 ∈ state.exposed) id
    (securityImplAt_preserves_exposed schemeOf _ vulnA vulnB (challOf_recordsChallenges _) (i + 1))
    (fun t state hstate => by
      simpa using hybridImpl_query_eq_of_exposed schemeOf vulnA vulnB i t state hstate)
    adv s hs
  simpa using h

/-- From `s` with `Disjoint s.exposed s.challenged`, either `H_{i+1}` and `H_i` answer `t` by equal
response/state computations, or every possible successor of either satisfies
`Disjoint exposed challenged ∧ i + 1 ∈ challenged`. -/
private theorem hybridImpl_query_eq_or_committed (i : ℕ)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (hs : Disjoint s.exposed s.challenged) :
    (hybridImpl schemeOf vulnA vulnB (i + 1) t).run s =
        (hybridImpl schemeOf vulnA vulnB i t).run s ∨
    ((∀ z ∈ support ((hybridImpl schemeOf vulnA vulnB (i + 1) t).run s),
        Disjoint z.2.exposed z.2.challenged ∧ i + 1 ∈ z.2.challenged) ∧
     (∀ z ∈ support ((hybridImpl schemeOf vulnA vulnB i t).run s),
        Disjoint z.2.exposed z.2.challenged ∧ i + 1 ∈ z.2.challenged)) := by
  simp only [securityImplAt_run]
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals try exact Or.inl rfl
  by_cases ht : t = i + 1
  · subst t
    by_cases helig : i + 1 ∈ s.exposed ∨ i + 1 ∈ s.challenged
    · left
      exact (oracleChall_rejected _ s _ helig).trans (oracleChall_rejected _ s _ helig).symm
    · by_cases hk : (s.keyA (i + 1)).isSome ∨ (s.keyB (i + 1)).isSome
      · right
        constructor
        all_goals
          intro z hz
          exact ⟨(challOf_recordsChallenges (hybridMode _)).preserves_disjoint (i + 1) s hs z hz,
            oracleChall_adds_challenged _ s _ helig hk z hz⟩
      · simp only [not_or, Option.not_isSome_iff_eq_none] at hk
        left
        exact (oracleChall_unavailable _ s _ hk.1 hk.2).trans
          (oracleChall_unavailable _ s _ hk.1 hk.2).symm
  · left
    change (oracleChall (hybridMode (i + 1) t) _ _ _ _ t).run s =
      (oracleChall (hybridMode i t) _ _ _ _ t).run s
    rw [hybridMode_challenge_eq_of_ne i t ht]

/-- From `s` with `Disjoint s.exposed s.challenged`, stopping at the first exposure of `i + 1`
preserves `Pr[H_{i+1} = true] - Pr[H_i = true]`. -/
theorem hybridImpl_signed_gap_stop_eq (i : ℕ) (adv : SCKAAdversary StA StB I Rho Rand)
    (s : GameState StA StB I Rho) (hs : Disjoint s.exposed s.challenged) :
    (Pr{let x ← ((simulateQ (hybridImpl schemeOf vulnA vulnB (i + 1)) adv).run'
        s)}[x = true]).toReal -
    (Pr{let x ← (simulateQ (hybridImpl schemeOf vulnA vulnB i) adv).run' s}[x = true]).toReal =
    (Pr{let x ← (stoppedRun (hybridImpl schemeOf vulnA vulnB (i + 1))
      (fun u => decide (i + 1 ∈ u.exposed)) adv s)}[x = true]).toReal -
    (Pr{let x ← (stoppedRun (hybridImpl schemeOf vulnA vulnB i)
      (fun u => decide (i + 1 ∈ u.exposed)) adv s)}[x = true]).toReal := by
  -- A query of the two hybrids is identical or an answered challenge at `i + 1`; afterwards
  -- `i + 1` stays challenged, hence unexposed.
  apply signed_gap_stoppedRun_eq _ _
    (fun s => Disjoint s.exposed s.challenged)
    (fun s => Disjoint s.exposed s.challenged ∧ i + 1 ∈ s.challenged)
    (fun u => decide (i + 1 ∈ u.exposed))
    (securityImplAt_preserves_disjoint schemeOf _ vulnA vulnB (challOf_recordsChallenges _))
    ((securityImplAt_preserves_disjoint schemeOf _ vulnA vulnB (challOf_recordsChallenges _)).and
      (securityImplAt_preserves_challenged schemeOf _ vulnA vulnB (challOf_recordsChallenges _) _))
    ((securityImplAt_preserves_disjoint schemeOf _ vulnA vulnB (challOf_recordsChallenges _)).and
      (securityImplAt_preserves_challenged schemeOf _ vulnA vulnB (challOf_recordsChallenges _) _))
    _ (hybridImpl_query_eq_or_committed schemeOf vulnA vulnB i) _ adv s hs
  · intro u hu
    simp only [decide_eq_false_iff_not]
    exact fun he => Finset.disjoint_left.mp hu.1 he hu.2
  · intro u _ hu cont
    have he : i + 1 ∈ u.exposed := of_decide_eq_true hu
    have h := hybridImpl_run_eq_of_exposed schemeOf vulnA vulnB i cont u he
    simp only [StateT.run'_eq, h]

/-- If every epoch with a recorded key in `s` is positive and at most `q`, `H_q` and the
uniform-key game answer every query from `s` by equal response/state computations. -/
private theorem hybridImpl_query_eq_random (q : ℕ)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (hkey : ∀ t, (s.keyA t).isSome ∨ (s.keyB t).isSome → 0 < t ∧ t ≤ q) :
    (hybridImpl schemeOf vulnA vulnB q t).run s =
      (modeImpl schemeOf vulnA vulnB (fun _ => true) t).run s := by
  simp only [securityImplAt_run]
  refine securityImplOf_run_eq _ _ _ _ _ _ _ s (fun _ => rfl) ?_ t
  intro t
  by_cases hk : (s.keyA t).isSome ∨ (s.keyB t).isSome
  · obtain ⟨htpos, htq⟩ := hkey t hk
    simp only [challOf, hybridMode, htpos, htq, and_self, decide_true]
  · simp only [not_or, Option.not_isSome_iff_eq_none] at hk
    exact oracleChall_run_eq_of_rejected _ _ s t (Or.inr hk)

/-- Let `Inv` be preserved by `modeImpl mode` for every mode, and let every epoch with a recorded
key in a state `s` with `Inv s` be positive and at most `s.nA + s.nB`. If
`SecuritySendQueryBound adv q`, then from an initial state `s₀` with `Inv s₀` and no sends,
`H_q` and the uniform-key game accept equally often. -/
theorem prEvent_hybridImpl_last_eq (Inv : GameState StA StB I Rho → Prop)
    (hpres : ∀ mode, QueryImpl.PreservesInv (modeImpl schemeOf vulnA vulnB mode) Inv)
    (hkeys : ∀ s, Inv s → ∀ t, (s.keyA t).isSome ∨ (s.keyB t).isSome → 0 < t ∧ t ≤ s.nA + s.nB)
    (adv : SCKAAdversary StA StB I Rho Rand) (q : ℕ) (hq : SecuritySendQueryBound adv q)
    (s₀ : GameState StA StB I Rho) (h0 : Inv s₀) (hcount : s₀.nA + s₀.nB = 0) :
    Pr{let x ← (simulateQ (hybridImpl schemeOf vulnA vulnB q) adv).run' s₀}[x = true] =
      Pr{let x ← ((simulateQ (modeImpl schemeOf vulnA vulnB (fun _ => true)) adv).run'
          s₀)}[x = true] := by
  -- VCVio's query-bounded transport, with the remaining send budget `b` in the invariant.
  have h := OracleComp.ProgramLogic.Relational.evalDistEq_simulateQ_run_of_impl_eq_queryBound
    (modeImpl schemeOf vulnA vulnB (fun _ => true))
    (hybridImpl schemeOf vulnA vulnB q)
    (fun s b => Inv s ∧ s.nA + s.nB + b ≤ q)
    (fun t b => ¬ (sckaSecuritySpec.isSendQuery t = true) ∨ 0 < b)
    (fun t b => if sckaSecuritySpec.isSendQuery t = true then b - 1 else b)
    adv q hq
    (fun t s b hs _ => by
      have hb := hs.2
      exact (hybridImpl_query_eq_random schemeOf vulnA vulnB q t s (fun t hk => by
        obtain ⟨hpos, hle⟩ := hkeys s hs.1 t hk
        exact ⟨hpos, by omega⟩)).symm)
    (fun t s b hs hcan z hz => by
      refine ⟨hpres _ t s hs.1 z hz, ?_⟩
      have hb := hs.2
      have hc := securityImplAt_sends_step schemeOf _ vulnA vulnB
        (challOf_recordsChallenges _) t s z hz
      by_cases ht : sckaSecuritySpec.isSendQuery t = true
      · have hpos : 0 < b := hcan.resolve_left (not_not_intro ht)
        simp only [ht, ↓reduceIte] at hc ⊢
        omega
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hc ⊢
        omega)
    s₀ ⟨h0, by omega⟩
  simp only [StateT.run'_eq]
  exact (h.symm.map Prod.fst).prEvent_eq _

end Hybrids

/-! ### The pinned challenge -/

section Oracle

variable [SampleableType I]

/-- The pinned challenge on game states whose key-table entries have type `κ`, read as keys by
`toKey`: it rejects an ineligible challenge at `t`, and otherwise records `t` and returns a uniform
key if `0 < t < e`, `kStar` if `t = e`, and `toKey` of the recorded entry otherwise;
`pinnedChallenge e kStar := pinnedChallengeWith id e kStar`. -/
def pinnedChallengeWith {κ : Type} (toKey : κ → I) (e : ℕ) (kStar : I) :
    QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB κ Rho) ProbComp) :=
  fun t => do
    let s ← get
    if t ∈ s.exposed ∨ t ∈ s.challenged then pure none
    else
      let key := match s.keyA t with
        | some k => some k
        | none => s.keyB t
      match key with
      | none => pure none
      | some honest =>
        let k ← if 0 < t ∧ t < e then liftM ($ᵗ I : ProbComp I)
          else pure (if t = e then kStar else toKey honest)
        set { s with challenged := insert t s.challenged }
        pure (some k)

/-- The pinned challenge on game states whose tables hold keys: an eligible challenge at `t`
returns a uniform key if `0 < t < e`, `kStar` if `t = e`, and the recorded key otherwise. -/
def pinnedChallenge (e : ℕ) (kStar : I) :
    QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp) :=
  pinnedChallengeWith id e kStar

/-- Whether `query` is an eligible challenge at `e` from `s`. -/
private def usesChallengeKey {κ : Type} (e : ℕ)
    (query : (sckaSecuritySpec Unit Unit Unit Unit Unit).Domain)
    (s : GameState StA StB κ Rho) : Bool :=
  match query with
  | sckaSecuritySpec.OChall t => decide (t = e ∧ e ∉ s.exposed ∧ e ∉ s.challenged ∧
      ((s.keyA e).isSome ∨ (s.keyB e).isSome))
  | _ => false

/-- Once `e` is challenged, no query is an eligible challenge at `e`. -/
private theorem usesChallengeKey_eq_false_of_challenged {κ : Type} (e : ℕ)
    (query : (sckaSecuritySpec Unit Unit Unit Unit Unit).Domain)
    (s : GameState StA StB κ Rho) (hs : e ∈ s.challenged) : usesChallengeKey e query s = false := by
  rcases query with (((((t | a) | a) | t) | a) | a) <;> simp [usesChallengeKey, hs]

variable (e : ℕ) (kStar : I)

/-- For an eligible `e`, `pinnedChallenge e kStar e` from `s` is `pure (some kStar, s')`, where
`s'` adds `e` to `challenged`. -/
private theorem pinnedChallenge_selected (s : GameState StA StB I Rho)
    (helig : ¬(e ∈ s.exposed ∨ e ∈ s.challenged))
    (hkey : (s.keyA e).isSome ∨ (s.keyB e).isSome) :
    (pinnedChallenge e kStar e).run s =
      pure (some kStar, { s with challenged := insert e s.challenged }) := by
  cases hA : s.keyA e <;> cases hB : s.keyB e
  all_goals try simp [hA, hB] at hkey
  all_goals simp [pinnedChallenge, pinnedChallengeWith, helig, hA, hB, StateT.run_bind,
    StateT.run_get, StateT.run_set]

/-- Unless `t = e` and `e` is eligible, `pinnedChallenge e kStar t` and `pinnedChallenge e k' t`
are equal computations from `s`. -/
private theorem pinnedChallenge_eq_of_unused (k' : I) (t : ℕ) (s : GameState StA StB I Rho)
    (h : ¬(t = e ∧ e ∉ s.exposed ∧ e ∉ s.challenged ∧
      ((s.keyA e).isSome ∨ (s.keyB e).isSome))) :
    (pinnedChallenge e kStar t).run s = (pinnedChallenge e k' t).run s := by
  by_cases ht : t = e
  · subst t
    by_cases hg : e ∈ s.exposed ∨ e ∈ s.challenged
    · simp [pinnedChallenge, pinnedChallengeWith, hg, StateT.run_bind, StateT.run_get]
    · have hk : s.keyA e = none ∧ s.keyB e = none := by
        cases hA : s.keyA e <;> cases hB : s.keyB e <;> simp_all
      simp [pinnedChallenge, pinnedChallengeWith, hg, hk, StateT.run_bind, StateT.run_get]
  · simp only [pinnedChallenge, pinnedChallengeWith, ht, ↓reduceIte]

/-- A query leaves the state unchanged or adds its unexposed epoch to `challenged`
(`RecordsChallenges`). -/
theorem pinnedChallenge_recordsChallenges :
    RecordsChallenges (pinnedChallenge (StA := StA) (StB := StB) (Rho := Rho) e kStar) := by
  intro t s z hz
  by_cases helig : t ∈ s.exposed ∨ t ∈ s.challenged
  · left
    simp only [pinnedChallenge, pinnedChallengeWith, StateT.run_bind, StateT.run_get, pure_bind,
      helig, ↓reduceIte, StateT.run_pure, mem_support_pure_iff] at hz
    rw [hz]
  · simp only [pinnedChallenge, pinnedChallengeWith, StateT.run_bind, StateT.run_get, pure_bind,
      helig, ↓reduceIte] at hz
    repeat' split at hz
    all_goals
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_map, StateT.run_set,
        StateT.run_monadLift, monadLift_self, bind_pure_comp, map_pure, Functor.map_map,
        mem_support_pure_iff, support_map, support_uniformSample, Set.image_univ,
        Set.mem_range] at hz
    all_goals
      first
      | (obtain rfl := hz; exact Or.inl rfl)
      | (obtain ⟨_, rfl⟩ := hz; exact Or.inr ⟨fun h => helig (Or.inl h), rfl⟩)

/-- If every key recorded at `e` in `s` equals `kStar`, `pinnedChallenge e kStar` and the challenge
oracle of `H_{e-1}` (mode `adjacentMode e false`) give equal computations from `s`. -/
private theorem pinnedChallenge_eq_recorded (t : ℕ) (s : GameState StA StB I Rho)
    (hkey : ∀ k, s.keyA e = some k ∨ s.keyB e = some k → k = kStar) :
    (pinnedChallenge e kStar t).run s =
      (oracleChall (adjacentMode e false t) StA StB I Rho t).run s := by
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [pinnedChallenge, pinnedChallengeWith, oracleChall, hg]
  · by_cases ht : t = e
    · subst t
      cases hA : s.keyA e with
      | none =>
        cases hB : s.keyB e with
        | none => simp [pinnedChallenge, pinnedChallengeWith, oracleChall, hg, hA, hB]
        | some k =>
          have hk := hkey k (.inr hB)
          subst k
          simp [pinnedChallenge, pinnedChallengeWith, oracleChall, adjacentMode_apply, hg, hA, hB]
      | some k =>
        have hk := hkey k (.inl hA)
        subst k
        simp [pinnedChallenge, pinnedChallengeWith, oracleChall, adjacentMode_apply, hg, hA]
    · cases hA : s.keyA t <;> cases hB : s.keyB t <;> by_cases hr : 0 < t ∧ t < e <;>
        simp [pinnedChallenge, pinnedChallengeWith, oracleChall, adjacentMode_apply, hg, hA, hB, ht,
          hr]

/-- For `e > 0`, drawing the key at `e` uniformly gives, from every state, the response/state
distribution of the challenge oracle of `H_e` (mode `adjacentMode e true`), which answers eligible
challenges at epochs `1, …, e` with uniform keys and all others with recorded keys. -/
private theorem pinnedChallenge_sample_uniform (he : 0 < e) (t : ℕ) (s : GameState StA StB I Rho) :
    (do
      let k ← ($ᵗ I : ProbComp I)
      (pinnedChallenge e k t).run s) =ᵈ
    (oracleChall (adjacentMode e true t) StA StB I Rho t).run s := by
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [OracleComp.EvalDistEq.map_const, pinnedChallenge, pinnedChallengeWith, oracleChall, hg]
  · by_cases ht : t = e
    · subst t
      cases hA : s.keyA e <;> cases hB : s.keyB e <;>
        simp [OracleComp.EvalDistEq.map_const, pinnedChallenge, pinnedChallengeWith, oracleChall,
          adjacentMode_apply, hg, hA, hB, he]
    · cases hA : s.keyA t <;> cases hB : s.keyB t <;> by_cases hr : 0 < t ∧ t < e <;>
        simp [OracleComp.EvalDistEq.bind_const, OracleComp.EvalDistEq.map_const, pinnedChallenge,
          pinnedChallengeWith, oracleChall, adjacentMode_apply, hg, hA, hB, ht, hr]

end Oracle

section PinnedOracles

variable [SampleableType I] [DecidableEq I] (e : ℕ) (kStar : I)
variable (schemeOf : GameState StA StB I Rho → SCKAScheme ProbComp IK StA StB I Rho Rand)
  (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)

/-- If `usesChallengeKey e t s = false`, the oracles with `pinnedChallenge e kStar` and those with
`pinnedChallenge e k'` answer `t` by equal computations from `s`. -/
private theorem securityImplAt_pinnedChallenge_eq_of_unused (k' : I)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (s : GameState StA StB I Rho) (h : usesChallengeKey e t s = false) :
    (securityImplAt schemeOf (pinnedChallenge e kStar) vulnA vulnB t).run s =
      (securityImplAt schemeOf (pinnedChallenge e k') vulnA vulnB t).run s := by
  rcases t with (((((t | a) | a) | t) | a) | a)
  all_goals try rfl
  simp only [securityImplAt_run, securityImplOf, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  exact pinnedChallenge_eq_of_unused e kStar k' t s (of_decide_eq_false h)

/-- If `usesChallengeKey e t s = true`, every possible successor of query `t` of the oracles with
`pinnedChallenge e kStar` from `s` has `e ∈ challenged`. -/
private theorem securityImplAt_pinnedChallenge_use_records_challenge
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (s : GameState StA StB I Rho) (h : usesChallengeKey e t s = true)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplAt schemeOf (pinnedChallenge e kStar) vulnA vulnB t).run s)) :
    e ∈ z.2.challenged := by
  rcases t with (((((t | a) | a) | t) | a) | a)
  all_goals try simp only [usesChallengeKey, Bool.false_eq_true, decide_eq_true_eq] at h
  obtain ⟨ht, he, hc, hk⟩ := h
  subst t
  simp only [securityImplAt_run, securityImplOf, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr] at hz
  rw [pinnedChallenge_selected e kStar s (by simp [he, hc]) hk] at hz
  obtain rfl := (mem_support_pure_iff _ _).mp hz
  exact Finset.mem_insert_self _ _

/-- Version `real` of the pinned challenge: from a state `s` in which every key recorded at `e` is
`kStar`, answering challenges at `e` with `kStar` or with the recorded key gives the same query
computation, that is, the oracles with `pinnedChallenge e kStar` and those of mode
`adjacentMode e false` (`H_{e-1}`) agree from `s`. -/
theorem securityImplAt_pinnedChallenge_eq_recorded
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (hkey : ∀ k, s.keyA e = some k ∨ s.keyB e = some k → k = kStar) :
    (securityImplAt schemeOf (pinnedChallenge e kStar) vulnA vulnB t).run s =
      (modeImpl schemeOf vulnA vulnB (adjacentMode e false) t).run s := by
  simp only [securityImplAt_run]
  exact securityImplOf_run_eq _ _ _ _ _ _ _ s (fun _ => rfl)
    (fun t => pinnedChallenge_eq_recorded e kStar t s hkey) t

/-- For `e > 0`, drawing `k ←$ I` before a query of the oracles with `pinnedChallenge e k` gives,
from every state, the joint answer/state distribution of the query in mode `adjacentMode e true`. -/
private theorem securityImplAt_pinnedChallenge_sample_uniform (he : 0 < e)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho) :
    (do
      let k ← ($ᵗ I : ProbComp I)
      (securityImplAt schemeOf (pinnedChallenge e k) vulnA vulnB t).run s) =ᵈ
    (modeImpl schemeOf vulnA vulnB (adjacentMode e true) t).run s := by
  rcases t with (((((t | a) | a) | t) | a) | a)
  all_goals
    first
    | simpa only [securityImplAt_run, securityImplOf, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr, challOf] using pinnedChallenge_sample_uniform e he t s
    | exact OracleComp.EvalDistEq.bind_const_of_support _ fun _ _ => rfl

/-- Version `random` of the pinned challenge: for `e > 0`, drawing a uniform challenge key before
the run or at the eligible challenge at `e` gives the same acceptance probability from every state
`s`, that is, the run with `pinnedChallenge e k` for `k ←$ I` drawn in advance and the run in mode
`adjacentMode e true` (`H_e`), both stopped at the first exposure of `e`. -/
theorem stoppedRun_pinnedChallenge_sample_eq (he : 0 < e) (adv : SCKAAdversary StA StB I Rho Rand)
    (s : GameState StA StB I Rho) :
    Pr{let x ← (do
      let k ← ($ᵗ I : ProbComp I)
      stoppedRun (securityImplAt schemeOf (pinnedChallenge e k) vulnA vulnB)
        (fun u => decide (e ∈ u.exposed)) adv s)}[x = true] =
    Pr{let x ← (stoppedRun (modeImpl schemeOf vulnA vulnB (adjacentMode e true))
      (fun u => decide (e ∈ u.exposed)) adv s)}[x = true] :=
  stoppedRun_sample_once_eq ($ᵗ I)
    (fun k => securityImplAt schemeOf (pinnedChallenge e k) vulnA vulnB)
    (modeImpl schemeOf vulnA vulnB (adjacentMode e true)) (fun u => decide (e ∈ u.exposed))
    (fun _ => True) (fun s => e ∈ s.challenged) (usesChallengeKey e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun k _ t s _ hs z hz _ => securityImplAt_preserves_challenged schemeOf _ vulnA vulnB
      (pinnedChallenge_recordsChallenges e k) e t s hs z hz)
    (fun t s _ h k _ k' _ => ToVCVio.evalDistEq_of_eq
      (securityImplAt_pinnedChallenge_eq_of_unused e k schemeOf vulnA vulnB k' t s h))
    (fun t s _ hs => usesChallengeKey_eq_false_of_challenged e t s hs)
    (fun k _ t s _ h z hz _ => securityImplAt_pinnedChallenge_use_records_challenge e k
      schemeOf vulnA vulnB t s h z hz)
    (fun t s _ => securityImplAt_pinnedChallenge_sample_uniform e schemeOf vulnA vulnB he t s)
    adv s trivial

end PinnedOracles

end SCKAScheme
