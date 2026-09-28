/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation

/-!
# Challenge responses under marked states

**Construction.** Fix a selected epoch `e` and supplied key `kStar`.
`pinnedChallenge` uses honest key tables: an eligible challenge below `e`
returns a uniform key, at `e` returns `kStar`, and above `e` returns its
recorded key. It retains both honest key tables.

**Statement.** For every honest state `s` and queried epoch `t`, the
simulator's challenge from `markState e s` has the same response/state
computation as `pinnedChallenge` from `s` followed by marking its successor.

**Proof.** Marking preserves table availability and the exposed/challenged
sets. Each eligible response follows the same epoch comparison in both
computations. Inserting `t` into the challenged set commutes with marking.
This establishes the challenge case of the reduction's simulation relation.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Challenge operation on honest states for selected epoch `e` and supplied
key `kStar`. Eligible epochs `0 < t < e` use uniform responses, epoch `e`
uses `kStar`, and other eligible epochs use their recorded key. Exposed,
repeated, and unavailable challenges return `none`. -/
def pinnedChallenge [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
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
        let k ← if 0 < t ∧ t < e then liftM ($ᵗ K : ProbComp K)
          else pure (if t = e then kStar else honest)
        set { s with challenged := insert t s.challenged }
        pure (some k)

/-- For every selected epoch `e`, supplied key `kStar`, queried epoch `t`,
and honest state `s`, the symbolic challenge from `markState e s` equals
the honest pinned challenge followed by marking its successor state. -/
theorem challenge_mark [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) (t : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (challenge onoff e kStar t).run (markState e s) =
      Prod.map id (markState e) <$> (pinnedChallenge onoff e kStar t).run s := by
  simp only [challenge, pinnedChallenge, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [markState, hg, StateT.run_pure, Prod.map]
  · cases hA : s.keyA t <;> cases hB : s.keyB t
    all_goals
      simp only [markState, hA, hB, Option.map_none, Option.map_some, hg, ↓reduceIte]
    all_goals
      by_cases hr : 0 < t ∧ t < e <;> by_cases ht : t = e <;>
        simp [hr, ht, mark, StateT.run_bind, StateT.run_set, StateT.run_pure,
          StateT.run_monadLift, monadLift_self,
          markState, Prod.map]

/-- For every selected epoch, supplied key, queried epoch, and state, the
pinned challenge preserves membership of every previously challenged epoch. -/
theorem pinnedChallenge_preserves_challenged [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) (u : ℕ) :
    QueryImpl.PreservesInv (pinnedChallenge (Sym := Sym) onoff e kStar)
      (fun s => u ∈ s.challenged) := by
  intro t s hs z hz
  simp only [pinnedChallenge, StateT.run_bind, StateT.run_get, pure_bind] at hz
  repeat' split at hz
  all_goals
    simp only [StateT.run_pure, StateT.run_bind, StateT.run_map, StateT.run_set,
      StateT.run_monadLift, monadLift_self, bind_pure_comp,
      map_pure, Functor.map_map, mem_support_pure_iff,
      support_map, support_uniformSample, Set.image_univ, Set.mem_range] at hz
  all_goals
    first
    | obtain rfl := hz
    | obtain ⟨_, rfl⟩ := hz
  all_goals first | exact hs | exact Finset.mem_insert_of_mem hs

/-- For every selected epoch, supplied key, queried epoch, and initial
state, every supported pinned-challenge successor retains the exposed set. -/
theorem pinnedChallenge_exposed_eq [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) (t : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : Option K × SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((pinnedChallenge onoff e kStar t).run s)) :
    z.2.exposed = s.exposed := by
  simp only [pinnedChallenge, StateT.run_bind, StateT.run_get, pure_bind] at hz
  repeat' split at hz
  all_goals
    simp only [StateT.run_pure, StateT.run_bind, StateT.run_map, StateT.run_set,
      StateT.run_monadLift, monadLift_self, bind_pure_comp,
      map_pure, Functor.map_map, mem_support_pure_iff,
      support_map, support_uniformSample, Set.image_univ, Set.mem_range] at hz
  all_goals
    first
    | obtain rfl := hz
    | obtain ⟨_, rfl⟩ := hz
  all_goals rfl

/-- For every eligible challenge at the selected epoch with an available
recorded key, the pinned challenge returns the supplied key and records
the selected epoch in `challenged`. -/
theorem pinnedChallenge_selected [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (helig : ¬(e ∈ s.exposed ∨ e ∈ s.challenged))
    (hkey : (s.keyA e).isSome ∨ (s.keyB e).isSome) :
    (pinnedChallenge onoff e kStar e).run s =
      pure (some kStar, { s with challenged := insert e s.challenged }) := by
  cases hA : s.keyA e <;> cases hB : s.keyB e
  all_goals try simp [hA, hB] at hkey
  all_goals simp [pinnedChallenge, helig, hA, hB, StateT.run_bind,
    StateT.run_get, StateT.run_set]

/-- For every state and queried epoch, two supplied keys give the same
pinned challenge computation whenever the queried epoch differs from `e`,
or the selected challenge is exposed, repeated, or unavailable. -/
theorem pinnedChallenge_eq_of_unused [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e t : ℕ) (k k' : K)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (h : ¬(t = e ∧ e ∉ s.exposed ∧ e ∉ s.challenged ∧
      ((s.keyA e).isSome ∨ (s.keyB e).isSome))) :
    (pinnedChallenge onoff e k t).run s = (pinnedChallenge onoff e k' t).run s := by
  by_cases ht : t = e
  · subst t
    by_cases hg : e ∈ s.exposed ∨ e ∈ s.challenged
    · simp [pinnedChallenge, hg, StateT.run_bind, StateT.run_get]
    · have hk : s.keyA e = none ∧ s.keyB e = none := by
        cases hA : s.keyA e <;> cases hB : s.keyB e <;> simp_all
      simp [pinnedChallenge, hg, hk, StateT.run_bind, StateT.run_get]
  · simp only [pinnedChallenge, ht, ↓reduceIte]

end oppUniKemCKA.Security.Embedding
