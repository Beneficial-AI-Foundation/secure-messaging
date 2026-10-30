/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness
import ToVCVio.OracleComp.SimSemantics.StateT.Stop
import ToVCVio.ProgramLogic.Unary.WP

/-!
# SCKA security oracles

Generic results on the security oracles of an SCKA scheme over `ProbComp`. A game state is

```text
s = (stA, stB, keyA, keyB, msgA, msgB, nA, nB, tcurA, tcurB,
     exposed, challenged, correct),
```

where `exposed` holds the epochs exposed by corruption or leakage and `challenged` the answered
challenges.

- **Individual oracles:** possible results of challenge, corruption, and leaking-send queries;
  challenge oracles that record challenges (`RecordsChallenges`).
- **Epoch-dependent challenges:** the challenge oracle `oracleChallOn`, whose query at epoch
  `t` is the fixed-bit challenge with bit `random t`.
- **Expected scores:** ordinary-send bounds extend to leaking sends.
- **Send distributions:** rejection and stopping of leaking sends with a fixed exposure set;
  equal local-send distributions give equal query distributions.
- **Full family** `securityImplOf base chall vulnA vulnB scka`: invariants, bookkeeping (no
  exposed or challenged epoch is removed; only sends increase `nA`, by at most one), and query
  equalities follow from those of the components.
-/

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type}

/-! ## Individual security oracles -/

/-! ### Challenge -/

section Challenge

variable [SampleableType I]

/-- Challenge oracle answering query `t` as `oracleChall (mode t)`: an eligible challenge
gets an independent uniform key if `mode t` and the recorded key otherwise. -/
def challOf (mode : ℕ → Bool) :
    QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun t => oracleChall (mode t) StA StB I Rho t

/-- Challenging an exposed or previously challenged epoch returns `none`
and preserves the state. -/
theorem oracleChall_rejected (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (h : t ∈ s.exposed ∨ t ∈ s.challenged) :
    (oracleChall b StA StB I Rho t).run s = pure (none, s) := by
  simp [oracleChall, h]

/-- If the game's epoch-key tables for A and B, `s.keyA` and `s.keyB`, both contain `none`
at epoch `t`, challenging `t` returns `none` and leaves `s` unchanged, regardless of
`exposed` and `challenged`. -/
theorem oracleChall_unavailable (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (hA : s.keyA t = none) (hB : s.keyB t = none) :
    (oracleChall b StA StB I Rho t).run s = pure (none, s) := by
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · exact oracleChall_rejected b s t h
  · simp [oracleChall, h, hA, hB]

/-- If `t` is exposed, challenged, or has no recorded key in `s`, every bit gives the same
challenge computation on `t` from `s`. -/
theorem oracleChall_run_eq_of_rejected (b b' : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (h : (t ∈ s.exposed ∨ t ∈ s.challenged) ∨ (s.keyA t = none ∧ s.keyB t = none)) :
    (oracleChall b StA StB I Rho t).run s = (oracleChall b' StA StB I Rho t).run s := by
  rcases h with h | ⟨hA, hB⟩
  · rw [oracleChall_rejected b s t h, oracleChall_rejected b' s t h]
  · rw [oracleChall_unavailable b s t hA hB, oracleChall_unavailable b' s t hA hB]

/-- Every possible result `z = (answer, s')` of a challenge at epoch `t` from state `s` satisfies
one of two cases:

- **Rejected or unavailable:** `t` is exposed or already challenged, or neither of the game's
  tables `s.keyA`, `s.keyB` records a key at `t`. Then `answer = none` and `s' = s`.
- **Eligible:** `t` is neither exposed nor already challenged, and at least one table records
  a key at `t`. Then `s' = { s with challenged := insert t s.challenged }`. -/
theorem oracleChall_support (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (z : Option I × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleChall b StA StB I Rho t).run s)) :
    (z = (none, s) ∧
      ((t ∈ s.exposed ∨ t ∈ s.challenged) ∨
        (s.keyA t = none ∧ s.keyB t = none))) ∨
    (¬(t ∈ s.exposed ∨ t ∈ s.challenged) ∧
      ((s.keyA t).isSome ∨ (s.keyB t).isSome) ∧
      z.2 = { s with challenged := insert t s.challenged }) := by
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · rw [oracleChall_rejected b s t h] at hz
    exact Or.inl ⟨(mem_support_pure_iff _ _).mp hz, Or.inl h⟩
  by_cases hkey : (s.keyA t).isSome ∨ (s.keyB t).isSome
  · refine Or.inr ⟨h, hkey, ?_⟩
    cases hA : s.keyA t <;> cases hB : s.keyB t <;> cases b <;>
      simp only [oracleChall, Bool.false_eq_true, ↓reduceIte, bind_pure_comp,
        pure_bind, StateT.run_bind, StateT.run_get, h, hA, hB, StateT.run_pure,
        StateT.run_map, StateT.run_set, StateT.run_monadLift, monadLift_self,
        map_pure, Functor.map_map, support_pure, Set.mem_singleton_iff,
        support_map, support_uniformSample, Set.image_univ, Set.mem_range] at hz
    all_goals
      first
      | (obtain rfl := hz; rfl)
      | (obtain ⟨k, rfl⟩ := hz; rfl)
      | simp [hA, hB] at hkey
  · have hA : s.keyA t = none := by cases hA : s.keyA t <;> simp_all
    have hB : s.keyB t = none := by cases hB : s.keyB t <;> simp_all
    rw [oracleChall_unavailable b s t hA hB] at hz
    exact Or.inl ⟨(mem_support_pure_iff _ _).mp hz, Or.inr ⟨hA, hB⟩⟩

/-- Two challenge bits give the same query computation at epoch `t` from `s` whenever they
agree if `t` is eligible in `s`: not exposed, not already challenged, and keyed in one of the
game's tables. On an ineligible epoch both bits return `none` and leave `s` unchanged. -/
theorem oracleChall_run_eq_of_eligible_imp (b b' : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (h : ¬(t ∈ s.exposed ∨ t ∈ s.challenged) →
      ((s.keyA t).isSome = true ∨ (s.keyB t).isSome = true) → b = b') :
    (oracleChall b StA StB I Rho t).run s = (oracleChall b' StA StB I Rho t).run s := by
  by_cases hrej : t ∈ s.exposed ∨ t ∈ s.challenged
  · rw [oracleChall_rejected b s t hrej, oracleChall_rejected b' s t hrej]
  by_cases hkey : (s.keyA t).isSome = true ∨ (s.keyB t).isSome = true
  · rw [h hrej hkey]
  · have hA : s.keyA t = none := by cases hA : s.keyA t <;> simp_all
    have hB : s.keyB t = none := by cases hB : s.keyB t <;> simp_all
    rw [oracleChall_unavailable b s t hA hB, oracleChall_unavailable b' s t hA hB]

/-- An eligible challenge `t` puts `t` into `challenged` in every possible successor. -/
theorem oracleChall_adds_challenged (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (helig : ¬(t ∈ s.exposed ∨ t ∈ s.challenged))
    (hkey : (s.keyA t).isSome ∨ (s.keyB t).isSome)
    (z : Option I × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleChall b StA StB I Rho t).run s)) :
    t ∈ z.2.challenged := by
  rcases oracleChall_support b s t z hz with ⟨_, hrej | ⟨hA, hB⟩⟩ | ⟨_, _, h⟩
  · exact absurd hrej helig
  · simp [hA, hB] at hkey
  · rw [h]; exact Finset.mem_insert_self _ _

end Challenge

/-- Bookkeeping condition on a challenge oracle `chall`: every possible successor of a challenge
at epoch `t` from `s` is `s` itself, or, when `t ∉ s.exposed`, `s` with `t` added to
`challenged`. In particular, `chall` changes neither the party states nor the recorded keys. -/
def RecordsChallenges
    (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp)) : Prop :=
  ∀ (t : ℕ) s z, z ∈ support ((chall t).run s) →
    z.2 = s ∨ (t ∉ s.exposed ∧ z.2 = { s with challenged := insert t s.challenged })

namespace RecordsChallenges

variable {chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp)}

/-- If `chall` records challenges and `Inv` is insensitive to `challenged`
(`Inv s → Inv { s with challenged := C }` for every `C`), then `chall` preserves `Inv`. -/
theorem preservesInv (h : RecordsChallenges chall) (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s challenged, Inv s → Inv { s with challenged := challenged }) :
    QueryImpl.PreservesInv chall Inv := by
  intro t s hs z hz
  rcases h t s z hz with h | ⟨_, h⟩
  · rw [h]; exact hs
  · rw [h]; exact hbook s _ hs

/-- If `chall` records challenges, then `chall` preserves `Disjoint s.exposed s.challenged`. -/
theorem preserves_disjoint (h : RecordsChallenges chall) :
    QueryImpl.PreservesInv chall (fun s => Disjoint s.exposed s.challenged) := by
  intro t s hs z hz
  rcases h t s z hz with h | ⟨ht, h⟩
  · rw [h]; exact hs
  · rw [h]
    exact Finset.disjoint_insert_right.mpr ⟨ht, hs⟩

/-- If `chall` records challenges, then every possible successor `z.2` of a challenge at `t` from
`s` satisfies `s.challenged ⊆ z.2.challenged`. -/
theorem challenged_subset (h : RecordsChallenges chall) (t : ℕ) (s : GameState StA StB I Rho)
    (z : Option I × GameState StA StB I Rho) (hz : z ∈ support ((chall t).run s)) :
    s.challenged ⊆ z.2.challenged := by
  rcases h t s z hz with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact Finset.subset_insert _ _

/-- If `chall` records challenges, then every possible successor `z.2` of a challenge at `t` from
`s` satisfies `z.2.exposed = s.exposed` and `z.2.nA = s.nA`. -/
theorem exposed_nA_eq (h : RecordsChallenges chall) (t : ℕ) (s : GameState StA StB I Rho)
    (z : Option I × GameState StA StB I Rho) (hz : z ∈ support ((chall t).run s)) :
    z.2.exposed = s.exposed ∧ z.2.nA = s.nA := by
  rcases h t s z hz with h | ⟨_, h⟩ <;> rw [h] <;> exact ⟨rfl, rfl⟩

end RecordsChallenges

/-- For every challenge mode, `challOf mode` records challenges. -/
theorem challOf_recordsChallenges [SampleableType I] (mode : ℕ → Bool) :
    RecordsChallenges (challOf (StA := StA) (StB := StB) (I := I) (Rho := Rho) mode) := by
  intro t s z hz
  rcases oracleChall_support (mode t) s t z hz with ⟨h, _⟩ | ⟨helig, _, h⟩
  · exact Or.inl (by rw [h])
  · exact Or.inr ⟨fun ht => helig (Or.inl ht), h⟩

/-- The challenge oracle `oracleChall` preserves every predicate `Inv` on game states that is
insensitive to `challenged`: `Inv s → Inv { s with challenged := C }` for every `C`. -/
theorem oracleChall_preservesInv [SampleableType I] (b : Bool)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s challenged, Inv s → Inv { s with challenged := challenged }) :
    QueryImpl.PreservesInv (oracleChall b StA StB I Rho) Inv :=
  (challOf_recordsChallenges (fun _ => b)).preservesInv Inv hbook

/-! ### Epoch-dependent challenge -/

section ChallengeOn

variable [SampleableType I]

/-- The challenge oracle whose eligible answers are random exactly at the epochs selected by
`random`: the query at epoch `t` is `oracleChall (random t)` at `t`, with the same guards and
bookkeeping. -/
def oracleChallOn (random : ℕ → Bool) (StA StB I Rho : Type) [SampleableType I] :
    QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun t => oracleChall (random t) StA StB I Rho t

@[simp]
lemma oracleChallOn_apply (random : ℕ → Bool) (t : ℕ) :
    oracleChallOn random StA StB I Rho t = oracleChall (random t) StA StB I Rho t := rfl

/-- A constant selection is the fixed-bit challenge oracle. -/
lemma oracleChallOn_const (b : Bool) :
    oracleChallOn (fun _ => b) StA StB I Rho = oracleChall b StA StB I Rho := rfl

/-- `oracleChallOn` preserves every predicate on game states that is insensitive to
`challenged`. -/
theorem oracleChallOn_preservesInv (random : ℕ → Bool)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s challenged, Inv s → Inv { s with challenged := challenged }) :
    QueryImpl.PreservesInv (oracleChallOn random StA StB I Rho) Inv :=
  fun t => oracleChall_preservesInv (random t) Inv hbook t

end ChallengeOn

/-! ### Challenge with an arbitrary answer function -/

/-- The challenge oracle whose eligible answer at epoch `t` with recorded key `k` is drawn from
`answer t k`: the same guards and bookkeeping as `oracleChall`, which is the instance
`answer t k = if b then $ᵗ I else pure k`. -/
def oracleChallWith (answer : ℕ → I → ProbComp I) (StA StB Rho : Type) :
    QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun (t : ℕ) => do
    let state ← get
    if t ∈ state.exposed ∨ t ∈ state.challenged then pure none
    else
      let key? := match state.keyA t with
        | some k => some k
        | none => state.keyB t
      match key? with
      | none => pure none
      | some k =>
        let outK ← liftM (answer t k)
        set { state with challenged := insert t state.challenged }
        return some outK

section ChallengeWith

variable (answer : ℕ → I → ProbComp I)

/-- Challenging an exposed or previously challenged epoch returns `none` and keeps the state. -/
lemma oracleChallWith_rejected (s : GameState StA StB I Rho) (t : ℕ)
    (h : t ∈ s.exposed ∨ t ∈ s.challenged) :
    (oracleChallWith answer StA StB Rho t).run s = pure (none, s) := by
  simp [oracleChallWith, h]

/-- Challenging an epoch without a recorded key returns `none` and keeps the state. -/
lemma oracleChallWith_unavailable (s : GameState StA StB I Rho) (t : ℕ)
    (hA : s.keyA t = none) (hB : s.keyB t = none) :
    (oracleChallWith answer StA StB Rho t).run s = pure (none, s) := by
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · exact oracleChallWith_rejected answer s t h
  · simp [oracleChallWith, h, hA, hB]

/-- The eligible challenge at epoch `t` from `s`, with recorded key `k` (A's table first): draw
the answer, record the challenge, return the answer. -/
lemma oracleChallWith_eligible (s : GameState StA StB I Rho) (t : ℕ)
    (h : ¬(t ∈ s.exposed ∨ t ∈ s.challenged)) (k : I)
    (hk : s.keyA t = some k ∨ (s.keyA t = none ∧ s.keyB t = some k)) :
    (oracleChallWith answer StA StB Rho t).run s = (do
      let outK ← answer t k
      pure (some outK, { s with challenged := insert t s.challenged })) := by
  rcases hk with hA | ⟨hA, hB⟩
  · simp [oracleChallWith, h, hA, StateT.run_bind, StateT.run_set, StateT.run_monadLift,
      monadLift_self]
  · simp [oracleChallWith, h, hA, hB, StateT.run_bind, StateT.run_set, StateT.run_monadLift,
      monadLift_self]

/-- Every result of `oracleChallWith` at epoch `t` from `s` is a rejection, with `t` exposed,
challenged or unkeyed and the state kept, or an accepted challenge with `t` added to the
challenged set. -/
lemma oracleChallWith_support (s : GameState StA StB I Rho) (t : ℕ)
    (z : Option I × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleChallWith answer StA StB Rho t).run s)) :
    (z = (none, s) ∧
      ((t ∈ s.exposed ∨ t ∈ s.challenged) ∨
        (s.keyA t = none ∧ s.keyB t = none))) ∨
    (¬(t ∈ s.exposed ∨ t ∈ s.challenged) ∧
      ((s.keyA t).isSome ∨ (s.keyB t).isSome) ∧
      z.2 = { s with challenged := insert t s.challenged }) := by
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · rw [oracleChallWith_rejected answer s t h] at hz
    exact Or.inl ⟨(mem_support_pure_iff _ _).mp hz, Or.inl h⟩
  by_cases hkey : (s.keyA t).isSome ∨ (s.keyB t).isSome
  · refine Or.inr ⟨h, hkey, ?_⟩
    have hk : ∃ k, s.keyA t = some k ∨ (s.keyA t = none ∧ s.keyB t = some k) := by
      cases hA : s.keyA t with
      | some k => exact ⟨k, Or.inl rfl⟩
      | none =>
        cases hB : s.keyB t with
        | some k => exact ⟨k, Or.inr ⟨rfl, rfl⟩⟩
        | none => simp [hA, hB] at hkey
    obtain ⟨k, hk⟩ := hk
    rw [oracleChallWith_eligible answer s t h k hk, mem_support_bind_iff] at hz
    obtain ⟨outK, -, hz⟩ := hz
    rw [(mem_support_pure_iff _ _).mp hz]
  · have hA : s.keyA t = none := by cases hA : s.keyA t <;> simp_all
    have hB : s.keyB t = none := by cases hB : s.keyB t <;> simp_all
    rw [oracleChallWith_unavailable answer s t hA hB] at hz
    exact Or.inl ⟨(mem_support_pure_iff _ _).mp hz, Or.inr ⟨hA, hB⟩⟩

/-- Two answer functions give the same query computation at epoch `t` from `s` whenever they
agree at `t` on every key if `t` is eligible in `s`. -/
lemma oracleChallWith_run_eq_of_eligible_imp (answer' : ℕ → I → ProbComp I)
    (s : GameState StA StB I Rho) (t : ℕ)
    (h : ¬(t ∈ s.exposed ∨ t ∈ s.challenged) →
      ((s.keyA t).isSome = true ∨ (s.keyB t).isSome = true) → ∀ k, answer t k = answer' t k) :
    (oracleChallWith answer StA StB Rho t).run s =
      (oracleChallWith answer' StA StB Rho t).run s := by
  by_cases hrej : t ∈ s.exposed ∨ t ∈ s.challenged
  · rw [oracleChallWith_rejected answer s t hrej, oracleChallWith_rejected answer' s t hrej]
  by_cases hkey : (s.keyA t).isSome = true ∨ (s.keyB t).isSome = true
  · have hk : ∃ k, s.keyA t = some k ∨ (s.keyA t = none ∧ s.keyB t = some k) := by
      cases hA : s.keyA t with
      | some k => exact ⟨k, Or.inl rfl⟩
      | none =>
        cases hB : s.keyB t with
        | some k => exact ⟨k, Or.inr ⟨rfl, rfl⟩⟩
        | none => simp [hA, hB] at hkey
    obtain ⟨k, hk⟩ := hk
    rw [oracleChallWith_eligible answer s t hrej k hk,
      oracleChallWith_eligible answer' s t hrej k hk, h hrej hkey k]
  · have hA : s.keyA t = none := by cases hA : s.keyA t <;> simp_all
    have hB : s.keyB t = none := by cases hB : s.keyB t <;> simp_all
    rw [oracleChallWith_unavailable answer s t hA hB,
      oracleChallWith_unavailable answer' s t hA hB]

/-- Drawing a value first and answering an eligible challenge with it is answering the
challenge with the draw. -/
lemma oracleChallWith_bind_eq_of_eligible {τ : Type} (sample : ProbComp τ)
    (answerOf : τ → ℕ → I → ProbComp I) (f : τ → I)
    (s : GameState StA StB I Rho) (t : ℕ)
    (h : ¬(t ∈ s.exposed ∨ t ∈ s.challenged))
    (hkey : (s.keyA t).isSome = true ∨ (s.keyB t).isSome = true)
    (hans : ∀ a k, answerOf a t k = pure (f a)) :
    (do let a ← sample; (oracleChallWith (answerOf a) StA StB Rho t).run s) =
      (oracleChallWith (fun _ _ => f <$> sample) StA StB Rho t).run s := by
  have hk : ∃ k, s.keyA t = some k ∨ (s.keyA t = none ∧ s.keyB t = some k) := by
    cases hA : s.keyA t with
    | some k => exact ⟨k, Or.inl rfl⟩
    | none =>
      cases hB : s.keyB t with
      | some k => exact ⟨k, Or.inr ⟨rfl, rfl⟩⟩
      | none => simp [hA, hB] at hkey
  obtain ⟨k, hk⟩ := hk
  rw [oracleChallWith_eligible _ s t h k hk]
  simp only [oracleChallWith_eligible _ s t h k hk, hans, pure_bind, map_eq_bind_pure_comp,
    bind_assoc, Function.comp]

/-- The fixed-bit challenge oracle computes as the instance of `oracleChallWith` that answers
a random key if the bit is set and the recorded key otherwise. -/
lemma oracleChall_run_eq_oracleChallWith [SampleableType I] (b : Bool)
    (s : GameState StA StB I Rho) (t : ℕ) :
    (oracleChall b StA StB I Rho t).run s =
      (oracleChallWith (fun _ k => if b then ($ᵗ I : ProbComp I) else pure k) StA StB Rho
        t).run s := by
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · rw [oracleChall_rejected b s t h, oracleChallWith_rejected _ s t h]
  cases hA : s.keyA t with
  | some k =>
    rw [oracleChallWith_eligible _ s t h k (Or.inl hA)]
    cases b <;> simp [oracleChall, h, hA, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      StateT.run_set, monadLift_self]
  | none =>
    cases hB : s.keyB t with
    | some k =>
      rw [oracleChallWith_eligible _ s t h k (Or.inr ⟨hA, hB⟩)]
      cases b <;> simp [oracleChall, h, hA, hB, StateT.run_bind, StateT.run_get,
        StateT.run_monadLift, StateT.run_set, monadLift_self]
    | none => rw [oracleChall_unavailable b s t hA hB, oracleChallWith_unavailable _ s t hA hB]

/-- The selection-indexed challenge oracle computes as the instance of `oracleChallWith` that
answers a random key at the selected epochs and the recorded key otherwise. -/
lemma oracleChallOn_run_eq_oracleChallWith [SampleableType I] (random : ℕ → Bool)
    (s : GameState StA StB I Rho) (t : ℕ) :
    (oracleChallOn random StA StB I Rho t).run s =
      (oracleChallWith (fun t k => if random t then ($ᵗ I : ProbComp I) else pure k)
        StA StB Rho t).run s := by
  rw [oracleChallOn_apply, oracleChall_run_eq_oracleChallWith]
  exact oracleChallWith_run_eq_of_eligible_imp _ _ s t (fun _ _ _ => rfl)

end ChallengeWith


/-! ### Corruption -/

/-- The corruption of A is a deterministic update: rejection returns `(none, s)`;
acceptance returns A's state and adds its vulnerable set to `exposed`. -/
theorem oracleCorruptA_run (vuln : StA → Finset ℕ) (s : GameState StA StB I Rho) :
    (oracleCorruptA vuln StB I Rho ()).run s =
      if vuln s.stA ∩ s.challenged ≠ ∅ then pure (none, s)
      else pure (some s.stA, { s with exposed := s.exposed ∪ vuln s.stA }) := by
  by_cases h : vuln s.stA ∩ s.challenged ≠ ∅
  · simp [oracleCorruptA, h]
  · simp [oracleCorruptA, not_not.mp h]

/-- Corrupting A either:

- returns `none` and leaves the game state unchanged; or
- returns `s.stA` and adds `vuln s.stA` to `exposed`, with none of these epochs challenged. -/
theorem oracleCorruptA_support (vuln : StA → Finset ℕ) (s : GameState StA StB I Rho)
    (z : Option StA × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptA vuln StB I Rho ()).run s)) :
    z = (none, s) ∨
      (vuln s.stA ∩ s.challenged = ∅ ∧
        z = (some s.stA, { s with exposed := s.exposed ∪ vuln s.stA })) := by
  rw [oracleCorruptA_run] at hz
  split_ifs at hz with h
  · exact Or.inl ((mem_support_pure_iff _ _).mp hz)
  · exact Or.inr ⟨not_not.mp h, (mem_support_pure_iff _ _).mp hz⟩

/-- Corruption of A preserves every invariant preserved by arbitrary changes to `exposed`. -/
theorem oracleCorruptA_preservesInv (vuln : StA → Finset ℕ)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed }) :
    QueryImpl.PreservesInv (oracleCorruptA vuln StB I Rho) Inv := by
  intro _ s hs z hz
  rcases oracleCorruptA_support vuln s z hz with h | ⟨_, h⟩
  · rw [h]; exact hs
  · rw [h]; exact hbook _ _ hs

/-- The corruption of A preserves `Disjoint exposed challenged`. -/
theorem oracleCorruptA_preserves_disjoint (vuln : StA → Finset ℕ) :
    QueryImpl.PreservesInv (oracleCorruptA vuln StB I Rho)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro _ s hs z hz
  rcases oracleCorruptA_support vuln s z hz with h | ⟨hv, h⟩
  · rw [h]; exact hs
  · rw [h]
    exact Finset.disjoint_union_left.mpr ⟨hs, Finset.disjoint_iff_inter_eq_empty.mpr hv⟩

/-- The corruption of A never removes an exposed epoch. -/
theorem oracleCorruptA_exposed_subset (vuln : StA → Finset ℕ) (u : Unit)
    (s : GameState StA StB I Rho) (z : Option StA × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptA vuln StB I Rho u).run s)) :
    s.exposed ⊆ z.2.exposed := by
  cases u
  rcases oracleCorruptA_support vuln s z hz with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact Finset.subset_union_left

/-- The corruption of A changes neither the challenged set nor A's send counter. -/
theorem oracleCorruptA_challenged_nA_eq (vuln : StA → Finset ℕ) (u : Unit)
    (s : GameState StA StB I Rho) (z : Option StA × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptA vuln StB I Rho u).run s)) :
    z.2.challenged = s.challenged ∧ z.2.nA = s.nA := by
  cases u
  rcases oracleCorruptA_support vuln s z hz with h | ⟨_, h⟩ <;> rw [h] <;> exact ⟨rfl, rfl⟩

/-- The corruption of B is a deterministic update: rejection returns `(none, s)`;
acceptance returns B's state and adds its vulnerable set to `exposed`. -/
theorem oracleCorruptB_run (vuln : StB → Finset ℕ) (s : GameState StA StB I Rho) :
    (oracleCorruptB vuln StA I Rho ()).run s =
      if vuln s.stB ∩ s.challenged ≠ ∅ then pure (none, s)
      else pure (some s.stB, { s with exposed := s.exposed ∪ vuln s.stB }) := by
  by_cases h : vuln s.stB ∩ s.challenged ≠ ∅
  · simp [oracleCorruptB, h]
  · simp [oracleCorruptB, not_not.mp h]

/-- Corrupting B either:

- returns `none` and leaves the game state unchanged; or
- returns `s.stB` and adds `vuln s.stB` to `exposed`, with none of these epochs challenged. -/
theorem oracleCorruptB_support (vuln : StB → Finset ℕ) (s : GameState StA StB I Rho)
    (z : Option StB × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptB vuln StA I Rho ()).run s)) :
    z = (none, s) ∨
      (vuln s.stB ∩ s.challenged = ∅ ∧
        z = (some s.stB, { s with exposed := s.exposed ∪ vuln s.stB })) := by
  rw [oracleCorruptB_run] at hz
  split_ifs at hz with h
  · exact Or.inl ((mem_support_pure_iff _ _).mp hz)
  · exact Or.inr ⟨not_not.mp h, (mem_support_pure_iff _ _).mp hz⟩

/-- Corruption of B preserves every invariant preserved by arbitrary changes to `exposed`. -/
theorem oracleCorruptB_preservesInv (vuln : StB → Finset ℕ)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed }) :
    QueryImpl.PreservesInv (oracleCorruptB vuln StA I Rho) Inv := by
  intro _ s hs z hz
  rcases oracleCorruptB_support vuln s z hz with h | ⟨_, h⟩
  · rw [h]; exact hs
  · rw [h]; exact hbook _ _ hs

/-- B version of `oracleCorruptA_preserves_disjoint`. -/
theorem oracleCorruptB_preserves_disjoint (vuln : StB → Finset ℕ) :
    QueryImpl.PreservesInv (oracleCorruptB vuln StA I Rho)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro _ s hs z hz
  rcases oracleCorruptB_support vuln s z hz with h | ⟨hv, h⟩
  · rw [h]; exact hs
  · rw [h]
    exact Finset.disjoint_union_left.mpr ⟨hs, Finset.disjoint_iff_inter_eq_empty.mpr hv⟩

/-- B version of `oracleCorruptA_exposed_subset`. -/
theorem oracleCorruptB_exposed_subset (vuln : StB → Finset ℕ) (u : Unit)
    (s : GameState StA StB I Rho) (z : Option StB × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptB vuln StA I Rho u).run s)) :
    s.exposed ⊆ z.2.exposed := by
  cases u
  rcases oracleCorruptB_support vuln s z hz with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact Finset.subset_union_left

/-- B version of `oracleCorruptA_challenged_nA_eq`. -/
theorem oracleCorruptB_challenged_nA_eq (vuln : StB → Finset ℕ) (u : Unit)
    (s : GameState StA StB I Rho) (z : Option StB × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptB vuln StA I Rho u).run s)) :
    z.2.challenged = s.challenged ∧ z.2.nA = s.nA := by
  cases u
  rcases oracleCorruptB_support vuln s z hz with h | ⟨_, h⟩ <;> rw [h] <;> exact ⟨rfl, rfl⟩

/-! ### Leaking sends -/

section LeakingSend

variable [DecidableEq I]

/-- Run A's leaking send, reject without changing `s` if it exposes a challenged epoch, and
otherwise apply `sendAUpdate`, add the exposed epochs, and return the send report and coins. -/
theorem oracleSendArleak_run_eq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ) (s : GameState StA StB I Rho) :
    (oracleSendArleak leak scka ()).run s =
      (fun out => match out with
        | none => (none, s)
        | some (keyOpt, ρ, tsnd, stA', coins) =>
            let E := leak s.stA coins
            if E ∩ s.challenged ≠ ∅ then (none, s)
            else (some (tsnd, keyOpt.map Prod.fst, ρ, coins),
              { sendAUpdate s keyOpt ρ tsnd stA' with exposed := s.exposed ∪ E })) <$>
        scka.sendArleak s.stA := by
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc, map_eq_bind_pure_comp]
  refine bind_congr fun out => ?_
  rcases out with _ | ⟨keyOpt, ρ, tsnd, stA', coins⟩
  · rfl
  · by_cases h : leak s.stA coins ∩ s.challenged ≠ ∅
    · simp [h, StateT.run_pure]
    · cases keyOpt <;> simp [h, sendAUpdate, knownPrefix, StateT.run_set]

/-- The version of `oracleSendArleak_run_eq` for B. -/
theorem oracleSendBrleak_run_eq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ) (s : GameState StA StB I Rho) :
    (oracleSendBrleak leak scka ()).run s =
      (fun out => match out with
        | none => (none, s)
        | some (keyOpt, ρ, tsnd, stB', coins) =>
            let E := leak s.stB coins
            if E ∩ s.challenged ≠ ∅ then (none, s)
            else (some (tsnd, keyOpt.map Prod.fst, ρ, coins),
              { sendBUpdate s keyOpt ρ tsnd stB' with exposed := s.exposed ∪ E })) <$>
        scka.sendBrleak s.stB := by
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc, map_eq_bind_pure_comp]
  refine bind_congr fun out => ?_
  rcases out with _ | ⟨keyOpt, ρ, tsnd, stB', coins⟩
  · rfl
  · by_cases h : leak s.stB coins ∩ s.challenged ≠ ∅
    · simp [h, StateT.run_pure]
    · cases keyOpt <;> simp [h, sendBUpdate, knownPrefix, StateT.run_set]

/-- Every possible result of A's leaking send from `s` is `(none, s)`, or has a successor with
`exposed = s.exposed ∪ E` (`E ∩ s.challenged = ∅`), the same `challenged`, and `nA = s.nA + 1`. -/
theorem oracleSendArleak_support
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka ()).run s)) :
    z = (none, s) ∨
      ∃ E : Finset ℕ, E ∩ s.challenged = ∅ ∧ z.2.exposed = s.exposed ∪ E ∧
        z.2.challenged = s.challenged ∧ z.2.nA = s.nA + 1 := by
  rw [oracleSendArleak_run_eq, support_map, Set.mem_image] at hz
  obtain ⟨out, _, rfl⟩ := hz
  rcases out with _ | ⟨key, msg, epoch, state, coins⟩
  · exact Or.inl rfl
  · dsimp only
    split
    · exact Or.inl rfl
    · rename_i hguard
      refine Or.inr ⟨leak s.stA coins, not_not.mp hguard, ?_⟩
      cases key <;> exact ⟨rfl, rfl, rfl⟩

/-- A's leaking send preserves `Disjoint exposed challenged`. -/
theorem oracleSendArleak_preserves_disjoint
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ) :
    QueryImpl.PreservesInv (oracleSendArleak leak scka)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro u s hs z hz
  cases u
  rcases oracleSendArleak_support scka leak s z hz with h | ⟨E, hE, hex, hch, _⟩
  · rw [h]; exact hs
  · show Disjoint z.2.exposed z.2.challenged
    rw [hex, hch]
    exact Finset.disjoint_union_left.mpr ⟨hs, Finset.disjoint_iff_inter_eq_empty.mpr hE⟩

/-- A's leaking send never changes the challenged set. -/
theorem oracleSendArleak_challenged_eq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka u).run s)) :
    z.2.challenged = s.challenged := by
  cases u
  rcases oracleSendArleak_support scka leak s z hz with h | ⟨_, _, _, hch, _⟩
  · rw [h]
  · exact hch

/-- A's leaking send never removes an exposed epoch. -/
theorem oracleSendArleak_exposed_subset
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka u).run s)) :
    s.exposed ⊆ z.2.exposed := by
  cases u
  rcases oracleSendArleak_support scka leak s z hz with h | ⟨E, _, hex, _, _⟩
  · rw [h]
  · rw [hex]; exact Finset.subset_union_left

/-- A's leaking send increases `nA` by at most one. -/
theorem oracleSendArleak_nA_le
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka u).run s)) :
    z.2.nA ≤ s.nA + 1 := by
  cases u
  rcases oracleSendArleak_support scka leak s z hz with h | ⟨_, _, _, _, hn⟩
  · rw [h]; exact Nat.le_succ _
  · exact hn.le

/-- B version of `oracleSendArleak_support`, with `nA` unchanged. -/
theorem oracleSendBrleak_support
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka ()).run s)) :
    z = (none, s) ∨
      ∃ E : Finset ℕ, E ∩ s.challenged = ∅ ∧ z.2.exposed = s.exposed ∪ E ∧
        z.2.challenged = s.challenged ∧ z.2.nA = s.nA := by
  rw [oracleSendBrleak_run_eq, support_map, Set.mem_image] at hz
  obtain ⟨out, _, rfl⟩ := hz
  rcases out with _ | ⟨key, msg, epoch, state, coins⟩
  · exact Or.inl rfl
  · dsimp only
    split
    · exact Or.inl rfl
    · rename_i hguard
      refine Or.inr ⟨leak s.stB coins, not_not.mp hguard, ?_⟩
      cases key <;> exact ⟨rfl, rfl, rfl⟩

/-- B version of `oracleSendArleak_preserves_disjoint`. -/
theorem oracleSendBrleak_preserves_disjoint
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ) :
    QueryImpl.PreservesInv (oracleSendBrleak leak scka)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro u s hs z hz
  cases u
  rcases oracleSendBrleak_support scka leak s z hz with h | ⟨E, hE, hex, hch, _⟩
  · rw [h]; exact hs
  · show Disjoint z.2.exposed z.2.challenged
    rw [hex, hch]
    exact Finset.disjoint_union_left.mpr ⟨hs, Finset.disjoint_iff_inter_eq_empty.mpr hE⟩

/-- B version of `oracleSendArleak_challenged_eq`. -/
theorem oracleSendBrleak_challenged_eq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka u).run s)) :
    z.2.challenged = s.challenged := by
  cases u
  rcases oracleSendBrleak_support scka leak s z hz with h | ⟨_, _, _, hch, _⟩
  · rw [h]
  · exact hch

/-- B version of `oracleSendArleak_exposed_subset`. -/
theorem oracleSendBrleak_exposed_subset
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka u).run s)) :
    s.exposed ⊆ z.2.exposed := by
  cases u
  rcases oracleSendBrleak_support scka leak s z hz with h | ⟨E, _, hex, _, _⟩
  · rw [h]
  · rw [hex]; exact Finset.subset_union_left

/-- B's leaking send preserves A's send counter. -/
theorem oracleSendBrleak_nA_eq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka u).run s)) :
    z.2.nA = s.nA := by
  cases u
  rcases oracleSendBrleak_support scka leak s z hz with h | ⟨_, _, _, _, hn⟩
  · rw [h]
  · exact hn

/-- Assume that discarding the coins returned by A's leaking send recovers its ordinary send for
every local state, and that `Inv` holds at `s` and does not depend on `exposed`. If every
ordinary-send successor from `s` satisfies `Inv`, then so does every leaking-send successor. -/
theorem oracleSendArleak_preservesInv_at
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed })
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hplain : ∀ z ∈ support ((oracleSendA scka ()).run s), Inv z.2)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka ()).run s)) : Inv z.2 := by
  rw [oracleSendArleak_run_eq, support_map, Set.mem_image] at hz
  obtain ⟨out, hout, rfl⟩ := hz
  rcases out with _ | ⟨key, msg, epoch, state, coins⟩
  · exact hs
  · dsimp only
    split
    · exact hs
    · apply hbook
      apply hplain (some (epoch, key.map Prod.fst, msg), sendAUpdate s key msg epoch state)
      rw [mem_support_oracleSendA_run_iff]
      refine ⟨some (key, msg, epoch, state), ?_, rfl⟩
      rw [← hm]
      exact (mem_support_bind_iff _ _ _).mpr ⟨_, hout, by simp⟩

/-- The version of `oracleSendArleak_preservesInv_at` for B. -/
theorem oracleSendBrleak_preservesInv_at
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed })
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hplain : ∀ z ∈ support ((oracleSendB scka ()).run s), Inv z.2)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka ()).run s)) : Inv z.2 := by
  rw [oracleSendBrleak_run_eq, support_map, Set.mem_image] at hz
  obtain ⟨out, hout, rfl⟩ := hz
  rcases out with _ | ⟨key, msg, epoch, state, coins⟩
  · exact hs
  · dsimp only
    split
    · exact hs
    · apply hbook
      apply hplain (some (epoch, key.map Prod.fst, msg), sendBUpdate s key msg epoch state)
      rw [mem_support_oracleSendB_run_iff]
      refine ⟨some (key, msg, epoch, state), ?_, rfl⟩
      rw [← hm]
      exact (mem_support_bind_iff _ _ _).mpr ⟨_, hout, by simp⟩

/-- Bookkeeping of A's leaking-send query from `s`: the challenged set is unchanged, and the
exposed set grows by a set disjoint from the challenged set (empty on rejection). -/
theorem oracleSendArleak_bookkeeping
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka ()).run s)) :
    z.2.challenged = s.challenged ∧
      ∃ E : Finset ℕ, E ∩ s.challenged = ∅ ∧ z.2.exposed = s.exposed ∪ E := by
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, -, hz⟩ := hz
  cases out with
  | none =>
      obtain rfl : z = (none, s) := by simpa using (mem_support_pure_iff _ _).mp hz
      exact ⟨rfl, ∅, by simp, by simp⟩
  | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      dsimp only at hz
      split at hz
      · obtain rfl : z = (none, s) := by simpa using (mem_support_pure_iff _ _).mp hz
        exact ⟨rfl, ∅, by simp, by simp⟩
      · rename_i hvuln
        cases key <;>
          simp only [StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals
          obtain rfl := hz
          exact ⟨rfl, leak s.stA coins, not_not.mp hvuln, rfl⟩

/-- The version of `oracleSendArleak_bookkeeping` for B. -/
theorem oracleSendBrleak_bookkeeping
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka ()).run s)) :
    z.2.challenged = s.challenged ∧
      ∃ E : Finset ℕ, E ∩ s.challenged = ∅ ∧ z.2.exposed = s.exposed ∪ E := by
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, -, hz⟩ := hz
  cases out with
  | none =>
      obtain rfl : z = (none, s) := by simpa using (mem_support_pure_iff _ _).mp hz
      exact ⟨rfl, ∅, by simp, by simp⟩
  | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      dsimp only at hz
      split at hz
      · obtain rfl : z = (none, s) := by simpa using (mem_support_pure_iff _ _).mp hz
        exact ⟨rfl, ∅, by simp, by simp⟩
      · rename_i hvuln
        cases key <;>
          simp only [StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals
          obtain rfl := hz
          exact ⟨rfl, leak s.stB coins, not_not.mp hvuln, rfl⟩
end LeakingSend

/-! ## Expected scores of leaking sends -/

section ExpectedScores

variable [DecidableEq I]

/-- Let `s` be a game state, `score` a function from game states to `ℝ≥0∞`, and `c : ℝ≥0∞`.
Assume:

- for every local state, discarding A's returned send coins recovers its ordinary send;
- every successful execution of A's leaking send from `s.stA` gives the same exposure set `E`;
- changing `exposed` does not change `score`;
- `score s ≤ c`;
- the expected score after A's ordinary-send query from `s` is at most `c`.

Then the expected score after A's leaking-send query from `s` is also at most `c`. -/
theorem oracleSendArleak_wp_le
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch state coins,
      some (key, msg, epoch, state, coins) ∈ support (scka.sendArleak s.stA) →
      leak s.stA coins = E)
    (score : GameState StA StB I Rho → ℝ≥0∞)
    (hbook : ∀ state exposed, score { state with exposed := exposed } = score state)
    (c : ℝ≥0∞) (hs : score s ≤ c)
    (hplain : wp ((oracleSendA scka ()).run s) (fun z => score z.2) ≤ c) :
    wp ((oracleSendArleak leak scka ()).run s) (fun z => score z.2) ≤ c := by
  by_cases hguard : E ∩ s.challenged ≠ ∅
  · rw [oracleSendArleak_run_eq, wp_map]
    apply wp_le_const_of_support _
    intro out hout
    rcases out with _ | ⟨key, msg, epoch, state, coins⟩
    · exact hs
    · dsimp only [Function.comp_def]
      rw [hE key msg epoch state coins hout, ite_eq_left hguard]
      exact hs
  · suffices heq : wp ((oracleSendArleak leak scka ()).run s)
        (fun z => score z.2) =
        wp ((oracleSendA scka ()).run s) (fun z => score z.2) by
      exact heq ▸ hplain
    simp only [oracleSendArleak_run_eq, oracleSendA_run_eq, map_eq_bind_pure_comp,
      Function.comp_def]
    rw [← hm s.stA]
    simp only [bind_assoc, pure_bind, wp_bind_eq_tsum]
    apply tsum_congr
    intro out
    by_cases hout : out ∈ support (scka.sendArleak s.stA)
    · cases out with
      | none => simp only [wp_pure, Option.map_none]
      | some out =>
        rcases out with ⟨key, msg, epoch, state, coins⟩
        simp only [Option.map_some, hE key msg epoch state coins hout, hguard, ↓reduceIte, wp_pure]
        rw [hbook]
    · have hz : Pr{let x ← scka.sendArleak s.stA}[x = out] = 0 := by
        exact (prEvent_eq_zero_of_not_mem_support _) hout
      simp only [hz, zero_mul]

/-- The expected-score bound of `oracleSendArleak_wp_le` for B. -/
theorem oracleSendBrleak_wp_le
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch state coins,
      some (key, msg, epoch, state, coins) ∈ support (scka.sendBrleak s.stB) →
      leak s.stB coins = E)
    (score : GameState StA StB I Rho → ℝ≥0∞)
    (hbook : ∀ state exposed, score { state with exposed := exposed } = score state)
    (c : ℝ≥0∞) (hs : score s ≤ c)
    (hplain : wp ((oracleSendB scka ()).run s) (fun z => score z.2) ≤ c) :
    wp ((oracleSendBrleak leak scka ()).run s) (fun z => score z.2) ≤ c := by
  by_cases hguard : E ∩ s.challenged ≠ ∅
  · rw [oracleSendBrleak_run_eq, wp_map]
    apply wp_le_const_of_support _
    intro out hout
    rcases out with _ | ⟨key, msg, epoch, state, coins⟩
    · exact hs
    · dsimp only [Function.comp_def]
      rw [hE key msg epoch state coins hout, ite_eq_left hguard]
      exact hs
  · suffices heq : wp ((oracleSendBrleak leak scka ()).run s)
        (fun z => score z.2) =
        wp ((oracleSendB scka ()).run s) (fun z => score z.2) by
      exact heq ▸ hplain
    simp only [oracleSendBrleak_run_eq, oracleSendB_run_eq, map_eq_bind_pure_comp,
      Function.comp_def]
    rw [← hm s.stB]
    simp only [bind_assoc, pure_bind, wp_bind_eq_tsum]
    apply tsum_congr
    intro out
    by_cases hout : out ∈ support (scka.sendBrleak s.stB)
    · cases out with
      | none => simp only [wp_pure, Option.map_none]
      | some out =>
        rcases out with ⟨key, msg, epoch, state, coins⟩
        simp only [Option.map_some, hE key msg epoch state coins hout, hguard, ↓reduceIte, wp_pure]
        rw [hbook]
    · have hz : Pr{let x ← scka.sendBrleak s.stB}[x = out] = 0 := by
        exact (prEvent_eq_zero_of_not_mem_support _) hout
      simp only [hz, zero_mul]

omit [DecidableEq I] in
/-- A challenge query does not raise any score that is insensitive to `challenged`. -/
theorem oracleChall_wp_le [SampleableType I] (b : Bool) (t : ℕ)
    (s : GameState StA StB I Rho) (score : GameState StA StB I Rho → ℝ≥0∞)
    (hbook : ∀ state challenged, score { state with challenged := challenged } = score state) :
    wp ((oracleChall b StA StB I Rho t).run s) (fun z => score z.2) ≤ score s := by
  refine wp_le_const_of_support _ ?_
  intro z hz
  rcases oracleChall_support b s t z hz with ⟨h, -⟩ | ⟨-, -, h⟩
  · simp [h]
  · simp [h, hbook]

omit [DecidableEq I] in
/-- Corrupting A does not raise any score that is insensitive to `exposed`. -/
theorem oracleCorruptA_wp_le (vuln : StA → Finset ℕ)
    (s : GameState StA StB I Rho) (score : GameState StA StB I Rho → ℝ≥0∞)
    (hbook : ∀ state exposed, score { state with exposed := exposed } = score state) :
    wp ((oracleCorruptA vuln StB I Rho ()).run s) (fun z => score z.2) ≤ score s := by
  refine wp_le_const_of_support _ ?_
  intro z hz
  rcases oracleCorruptA_support vuln s z hz with h | ⟨-, h⟩
  · simp [h]
  · simp [h, hbook]

omit [DecidableEq I] in
/-- Corrupting B does not raise any score that is insensitive to `exposed`. -/
theorem oracleCorruptB_wp_le (vuln : StB → Finset ℕ)
    (s : GameState StA StB I Rho) (score : GameState StA StB I Rho → ℝ≥0∞)
    (hbook : ∀ state exposed, score { state with exposed := exposed } = score state) :
    wp ((oracleCorruptB vuln StA I Rho ()).run s) (fun z => score z.2) ≤ score s := by
  refine wp_le_const_of_support _ ?_
  intro z hz
  rcases oracleCorruptB_support vuln s z hz with h | ⟨-, h⟩
  · simp [h]
  · simp [h, hbook]

end ExpectedScores

/-! ## Send distributions under exposure guards -/

section SendDistributions

variable [DecidableEq I] {τ : Type}

/-- If `E ∩ s.challenged ≠ ∅` and `leak s.stA r = E` for the coins `r` of every possible
successful local leaking A-send, A's leaking-send query from `s` is `(none, s)` with probability
one. -/
theorem oracleSendArleak_rejected_evalDistEq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendArleak s.stA) →
      leak s.stA coins = E)
    (hguard : E ∩ s.challenged ≠ ∅) :
    (oracleSendArleak leak scka ()).run s =ᵈ (pure (none, s) : ProbComp _) := by
  rw [oracleSendArleak_run_eq, map_eq_bind_pure_comp]
  refine OracleComp.EvalDistEq.bind_const_of_support _ fun out hout => ?_
  cases out with
  | none => rfl
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    dsimp only [Function.comp_def]
    rw [hE key msg epoch next coins hout, ite_eq_left hguard]

/-- If every local leaking A-send from `s.stA` succeeds with coins `r` such that
`leak s.stA r = E`, `E ∩ s.challenged = ∅`, and `e ∈ E`, then the query from `s`, stopped at
`e ∈ exposed`, answers `none` on every possible result. -/
theorem oracleSendArleak_stop_of_exposure
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ) (e : ℕ)
    (hsuccess : none ∉ support (scka.sendArleak s.stA))
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendArleak s.stA) →
      leak s.stA coins = E)
    (hguard : E ∩ s.challenged = ∅) (he : e ∈ E)
    (z : Option (Option (ℕ × Option ℕ × Rho × Rand)) × GameState StA StB I Rho)
    (hz : z ∈ support (((stopOnState (oracleSendArleak leak scka)
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) :
    z.1 = none := by
  rw [stopOnState_run_eq_map, oracleSendArleak_run_eq, Functor.map_map,
    support_map, Set.mem_image] at hz
  obtain ⟨out, hout, rfl⟩ := hz
  cases out with
  | none => exact False.elim (hsuccess hout)
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    simp only [hE key msg epoch next coins hout, hguard, ne_eq,
      not_true_eq_false, ↓reduceIte, Finset.mem_union, he, or_true, decide_true]

/-- B version of `oracleSendArleak_rejected_evalDistEq`. -/
theorem oracleSendBrleak_rejected_evalDistEq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendBrleak s.stB) →
      leak s.stB coins = E)
    (hguard : E ∩ s.challenged ≠ ∅) :
    (oracleSendBrleak leak scka ()).run s =ᵈ (pure (none, s) : ProbComp _) := by
  rw [oracleSendBrleak_run_eq, map_eq_bind_pure_comp]
  refine OracleComp.EvalDistEq.bind_const_of_support _ fun out hout => ?_
  cases out with
  | none => rfl
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    dsimp only [Function.comp_def]
    rw [hE key msg epoch next coins hout, ite_eq_left hguard]

/-- B version of `oracleSendArleak_stop_of_exposure`. -/
theorem oracleSendBrleak_stop_of_exposure
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ) (e : ℕ)
    (hsuccess : none ∉ support (scka.sendBrleak s.stB))
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendBrleak s.stB) →
      leak s.stB coins = E)
    (hguard : E ∩ s.challenged = ∅) (he : e ∈ E)
    (z : Option (Option (ℕ × Option ℕ × Rho × Rand)) × GameState StA StB I Rho)
    (hz : z ∈ support (((stopOnState (oracleSendBrleak leak scka)
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) :
    z.1 = none := by
  rw [stopOnState_run_eq_map, oracleSendBrleak_run_eq, Functor.map_map,
    support_map, Set.mem_image] at hz
  obtain ⟨out, hout, rfl⟩ := hz
  cases out with
  | none => exact False.elim (hsuccess hout)
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    simp only [hE key msg epoch next coins hout, hguard, ne_eq,
      not_true_eq_false, ↓reduceIte, Finset.mem_union, he, or_true, decide_true]

/-- If `(a ← sample; (family a).sendA s.stA) =ᵈ target.sendA s.stA`, the A-send queries
from `s` satisfy the same equality of joint response/state distributions. -/
theorem oracleSendA_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : (do let a ← sample; (family a).sendA s.stA) =ᵈ target.sendA s.stA) :
    (do let a ← sample; (oracleSendA (family a) ()).run s) =ᵈ
      (oracleSendA target ()).run s := by
  simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [← bind_assoc]
  exact h.bind_left _

/-- B version of `oracleSendA_sample_eq`. -/
theorem oracleSendB_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : (do let a ← sample; (family a).sendB s.stB) =ᵈ target.sendB s.stB) :
    (do let a ← sample; (oracleSendB (family a) ()).run s) =ᵈ
      (oracleSendB target ()).run s := by
  simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [← bind_assoc]
  exact h.bind_left _

/-- Leaking-send version of `oracleSendA_sample_eq`, for a common exposure function `leak`. -/
theorem oracleSendArleak_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ) (s : GameState StA StB I Rho)
    (h : (do let a ← sample; (family a).sendArleak s.stA) =ᵈ
      target.sendArleak s.stA) :
    (do let a ← sample; (oracleSendArleak leak (family a) ()).run s) =ᵈ
      (oracleSendArleak leak target ()).run s := by
  simp only [oracleSendArleak_run_eq, map_eq_bind_pure_comp]
  rw [← bind_assoc]
  exact h.bind_left _

/-- B version of `oracleSendArleak_sample_eq`. -/
theorem oracleSendBrleak_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ) (s : GameState StA StB I Rho)
    (h : (do let a ← sample; (family a).sendBrleak s.stB) =ᵈ
      target.sendBrleak s.stB) :
    (do let a ← sample; (oracleSendBrleak leak (family a) ()).run s) =ᵈ
      (oracleSendBrleak leak target ()).run s := by
  simp only [oracleSendBrleak_run_eq, map_eq_bind_pure_comp]
  rw [← bind_assoc]
  exact h.bind_left _

/-- Equal local A-sends from `s.stA` give equal A-send queries from `s`. -/
theorem oracleSendA_run_congr
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : scka.sendA s.stA = scka'.sendA s.stA) :
    (oracleSendA scka ()).run s = (oracleSendA scka' ()).run s := by
  simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
    monadLift_self, bind_assoc]
  rw [h]

/-- B version of `oracleSendA_run_congr`. -/
theorem oracleSendB_run_congr
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : scka.sendB s.stB = scka'.sendB s.stB) :
    (oracleSendB scka ()).run s = (oracleSendB scka' ()).run s := by
  simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
    monadLift_self, bind_assoc]
  rw [h]

/-- Leaking-send version of `oracleSendA_run_congr`, for a common exposure function `leak`. -/
theorem oracleSendArleak_run_congr
    (leak : StA → Rand → Finset ℕ)
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : scka.sendArleak s.stA = scka'.sendArleak s.stA) :
    (oracleSendArleak leak scka ()).run s = (oracleSendArleak leak scka' ()).run s := by
  simp only [oracleSendArleak_run_eq, h]

/-- B version of `oracleSendArleak_run_congr`. -/
theorem oracleSendBrleak_run_congr
    (leak : StB → Rand → Finset ℕ)
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : scka.sendBrleak s.stB = scka'.sendBrleak s.stB) :
    (oracleSendBrleak leak scka ()).run s = (oracleSendBrleak leak scka' ()).run s := by
  simp only [oracleSendBrleak_run_eq, h]

/-- If two schemes' A-receives agree on `s.stA`, their A-receive queries from `s` agree. -/
theorem oracleRecvA_run_congr
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : ∀ ρ, scka.recvA s.stA ρ = scka'.recvA s.stA ρ) (n : ℕ) :
    (oracleRecvA scka n).run s = (oracleRecvA scka' n).run s := by
  simp only [oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgB n with
  | none => rfl
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    simp only
    rw [h ρ]

/-- B version of `oracleRecvA_run_congr`. -/
theorem oracleRecvB_run_congr
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : ∀ ρ, scka.recvB s.stB ρ = scka'.recvB s.stB ρ) (n : ℕ) :
    (oracleRecvB scka n).run s = (oracleRecvB scka' n).run s := by
  simp only [oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgA n with
  | none => rfl
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    simp only
    rw [h ρ]

end SendDistributions

/-! ## Full security oracle family -/

section SecurityFamily

variable [DecidableEq I]

/-- Assemble the security oracles for a proof game. `base` supplies uniform sampling,
ordinary sends, and receives; `chall` supplies challenges. Leaking sends and corruptions
use the given scheme and exposure functions. -/
def securityImplOf
    (base : QueryImpl (sckaCorrectnessSpec Rho) (StateT (GameState StA StB I Rho) ProbComp))
    (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
    (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (sckaSecuritySpec StA StB I Rho Rand)
      (StateT (GameState StA StB I Rho) ProbComp) :=
  base
    + oracleSendArleak vulnA.rleak scka + oracleSendBrleak vulnB.rleak scka
    + chall
    + oracleCorruptA vulnA.corrupt StB I Rho + oracleCorruptB vulnB.corrupt StA I Rho

/-- `sckaSecurityImpl b` is `securityImplOf` over the correctness oracles and the fixed-bit
challenge oracle. -/
theorem sckaSecurityImpl_eq_securityImplOf [SampleableType I] (b : Bool)
    (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    sckaSecurityImpl b vulnA vulnB scka =
      securityImplOf (sckaCorrectnessImpl scka) (oracleChall b StA StB I Rho) vulnA vulnB scka :=
  rfl

variable (base : QueryImpl (sckaCorrectnessSpec Rho) (StateT (GameState StA StB I Rho) ProbComp))
variable (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
variable (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)
variable (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)

/-- If each component query from `s` produces only states satisfying `Inv`, then every
assembled security query from `s` does too. -/
theorem securityImplOf_preserves_at (Inv : GameState StA StB I Rho → Prop)
    (s : GameState StA StB I Rho)
    (hbase : ∀ t z, z ∈ support ((base t).run s) → Inv z.2)
    (hA : ∀ z ∈ support ((oracleSendArleak vulnA.rleak scka ()).run s), Inv z.2)
    (hB : ∀ z ∈ support ((oracleSendBrleak vulnB.rleak scka ()).run s), Inv z.2)
    (hC : ∀ (t : ℕ) z, z ∈ support ((chall t).run s) → Inv z.2)
    (hcA : ∀ z ∈ support ((oracleCorruptA vulnA.corrupt StB I Rho ()).run s), Inv z.2)
    (hcB : ∀ z ∈ support ((oracleCorruptB vulnB.corrupt StA I Rho ()).run s), Inv z.2)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    -- `hz` says that `z = (answer, nextState)` can result from query `t` in state `s`.
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    Inv z.2 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · exact hbase t z hz
  · cases u; exact hA z hz
  · cases u; exact hB z hz
  · exact hC t z hz
  · cases u; exact hcA z hz
  · cases u; exact hcB z hz

/-- If every component preserves `Inv`, so does `securityImplOf base chall vulnA vulnB scka`. -/
theorem securityImplOf_preservesInv (Inv : GameState StA StB I Rho → Prop)
    (hbase : QueryImpl.PreservesInv base Inv)
    (hA : QueryImpl.PreservesInv (oracleSendArleak vulnA.rleak scka) Inv)
    (hB : QueryImpl.PreservesInv (oracleSendBrleak vulnB.rleak scka) Inv)
    (hC : QueryImpl.PreservesInv chall Inv)
    (hcA : QueryImpl.PreservesInv (oracleCorruptA vulnA.corrupt StB I Rho) Inv)
    (hcB : QueryImpl.PreservesInv (oracleCorruptB vulnB.corrupt StA I Rho) Inv) :
    QueryImpl.PreservesInv (securityImplOf base chall vulnA vulnB scka) Inv :=
  ((((hbase.add hA).add hB).add hC).add hcA).add hcB

/-- Let `Inv` be a predicate on game states and `s` a game state. Assume:

- `Inv s`;
- replacing `exposed` and `challenged` by any finite sets preserves `Inv`;
- for each party and local state, discarding the returned send coins recovers the ordinary send;
- every query of `base` or `chall`, and both ordinary-send queries, produces only states
  satisfying `Inv` when run from `s`.

Then every query of the full oracle family `securityImplOf` from `s` produces only states
satisfying `Inv`. -/
theorem securityImplOf_preserves_at_of_book (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed challenged, Inv s →
      Inv { s with exposed := exposed, challenged := challenged })
    (hmA : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (hmB : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hbase : ∀ t z, z ∈ support ((base t).run s) → Inv z.2)
    (hchall : ∀ (t : ℕ) z, z ∈ support ((chall t).run s) → Inv z.2)
    (hsendA : ∀ z ∈ support ((oracleSendA scka ()).run s), Inv z.2)
    (hsendB : ∀ z ∈ support ((oracleSendB scka ()).run s), Inv z.2)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    Inv z.2 := by
  have hexp : ∀ s exposed, Inv s → Inv { s with exposed := exposed } :=
    fun s exposed h => by simpa using hbook s exposed s.challenged h
  refine securityImplOf_preserves_at base chall vulnA vulnB scka Inv s hbase
    (fun z hz => oracleSendArleak_preservesInv_at scka vulnA.rleak hmA Inv hexp s hs hsendA z hz)
    (fun z hz => oracleSendBrleak_preservesInv_at scka vulnB.rleak hmB Inv hexp s hs hsendB z hz)
    hchall
    (fun z hz => oracleCorruptA_preservesInv vulnA.corrupt Inv hexp () s hs z hz)
    (fun z hz => oracleCorruptB_preservesInv vulnB.corrupt Inv hexp () s hs z hz) t z hz

/-- The special case of `securityImplOf_preserves_at_of_book` for `sckaSecurityImpl`. Its
ordinary sends are correctness queries, so the two send hypotheses are instances of `hbase`. -/
theorem sckaSecurityImpl_preserves_at_of_book [SampleableType I] (b : Bool)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed challenged, Inv s →
      Inv { s with exposed := exposed, challenged := challenged })
    (hmA : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (hmB : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hbase : ∀ t z, z ∈ support ((sckaCorrectnessImpl scka t).run s) → Inv z.2)
    (hchall : ∀ (t : ℕ) z, z ∈ support ((oracleChall b StA StB I Rho t).run s) → Inv z.2)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((sckaSecurityImpl b vulnA vulnB scka t).run s)) :
    Inv z.2 :=
  securityImplOf_preserves_at_of_book (sckaCorrectnessImpl scka) (oracleChall b StA StB I Rho)
    vulnA vulnB scka Inv hbook hmA hmB s hs hbase hchall
    (hbase sckaCorrectnessSpec.OSendA) (hbase sckaCorrectnessSpec.OSendB) t z hz

/-- If dropping the coins of each leaking send gives the ordinary send and `chall` records
challenges, the family preserves every `Inv` preserved by `base`, both ordinary sends, and
arbitrary changes to `exposed` and `challenged`. -/
theorem securityImplOf_preservesInv_of_book (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed challenged, Inv s →
      Inv { s with exposed := exposed, challenged := challenged })
    (hmA : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (hmB : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (hchall : RecordsChallenges chall)
    (hbase : QueryImpl.PreservesInv base Inv)
    (hsendA : QueryImpl.PreservesInv (oracleSendA scka) Inv)
    (hsendB : QueryImpl.PreservesInv (oracleSendB scka) Inv) :
    QueryImpl.PreservesInv (securityImplOf base chall vulnA vulnB scka) Inv :=
  fun t s hs z hz => securityImplOf_preserves_at_of_book base chall vulnA vulnB scka Inv
    hbook hmA hmB s hs (fun t => hbase t s hs)
    (fun t => hchall.preservesInv Inv (fun s C h => by simpa using hbook s s.exposed C h) t s hs)
    (hsendA () s hs) (hsendB () s hs) t z hz

/-- If `base` keeps `exposed` and `chall` records challenges, every possible successor `s'` of
a family query from `s` has `s.exposed ⊆ s'.exposed`. -/
theorem securityImplOf_exposed_subset
    (hbase : ∀ t s z, z ∈ support ((base t).run s) → z.2.exposed = s.exposed)
    (hchall : RecordsChallenges chall)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    s.exposed ⊆ z.2.exposed := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [hbase t s z hz]
  · exact oracleSendArleak_exposed_subset scka vulnA.rleak u s z hz
  · exact oracleSendBrleak_exposed_subset scka vulnB.rleak u s z hz
  · rw [(hchall.exposed_nA_eq t s z hz).1]
  · exact oracleCorruptA_exposed_subset vulnA.corrupt u s z hz
  · exact oracleCorruptB_exposed_subset vulnB.corrupt u s z hz

/-- `challenged` version of `securityImplOf_exposed_subset`. -/
theorem securityImplOf_challenged_subset
    (hbase : ∀ t s z, z ∈ support ((base t).run s) → z.2.challenged = s.challenged)
    (hchall : RecordsChallenges chall)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    s.challenged ⊆ z.2.challenged := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [hbase t s z hz]
  · rw [oracleSendArleak_challenged_eq scka vulnA.rleak u s z hz]
  · rw [oracleSendBrleak_challenged_eq scka vulnB.rleak u s z hz]
  · exact hchall.challenged_subset t s z hz
  · rw [(oracleCorruptA_challenged_nA_eq vulnA.corrupt u s z hz).1]
  · rw [(oracleCorruptB_challenged_nA_eq vulnB.corrupt u s z hz).1]

/-- If `base` keeps both bookkeeping sets and `chall` records challenges, the assembled
oracles preserve `Disjoint exposed challenged`. -/
theorem securityImplOf_preserves_disjoint
    (hbase : ∀ t s z, z ∈ support ((base t).run s) →
      z.2.exposed = s.exposed ∧ z.2.challenged = s.challenged)
    (hchall : RecordsChallenges chall) :
    QueryImpl.PreservesInv (securityImplOf base chall vulnA vulnB scka)
      (fun s => Disjoint s.exposed s.challenged) := by
  refine securityImplOf_preservesInv base chall vulnA vulnB scka _ ?_
    (oracleSendArleak_preserves_disjoint scka vulnA.rleak)
    (oracleSendBrleak_preserves_disjoint scka vulnB.rleak)
    hchall.preserves_disjoint
    (oracleCorruptA_preserves_disjoint vulnA.corrupt)
    (oracleCorruptB_preserves_disjoint vulnB.corrupt)
  intro t s hs z hz
  obtain ⟨he, hc⟩ := hbase t s z hz
  show Disjoint z.2.exposed z.2.challenged
  rw [he, hc]; exact hs

/-- If `base` increases `nA` by at most one on sends and not otherwise, and `chall` records
challenges, every possible successor `s'` of a family query `t` from `s` has
`s'.nA ≤ s.nA + (if t is a send then 1 else 0)`. -/
theorem securityImplOf_nA_step
    (hbase : ∀ t s z, z ∈ support ((base t).run s) →
      z.2.nA ≤ s.nA + if isSendQuery t then 1 else 0)
    (hchall : RecordsChallenges chall)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    z.2.nA ≤ s.nA + if sckaSecuritySpec.isSendQuery t then 1 else 0 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [sckaSecuritySpec.isSendQuery_OCorrectness]
    exact hbase t s z hz
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using oracleSendArleak_nA_le scka vulnA.rleak () s z hz
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using
      (oracleSendBrleak_nA_eq scka vulnB.rleak () s z hz).le.trans (Nat.le_succ _)
  · simpa [sckaSecuritySpec.isSendQuery] using (hchall.exposed_nA_eq t s z hz).2.le
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using
      (oracleCorruptA_challenged_nA_eq vulnA.corrupt () s z hz).2.le
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using
      (oracleCorruptB_challenged_nA_eq vulnB.corrupt () s z hz).2.le

/-- If `base` and `base'` have equal query computations from `s`, and so do `chall` and
`chall'`, the two assembled security implementations have equal query computations from `s`. -/
theorem securityImplOf_run_eq
    (base' : QueryImpl (sckaCorrectnessSpec Rho) (StateT (GameState StA StB I Rho) ProbComp))
    (chall' : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
    (s : GameState StA StB I Rho)
    (hbase : ∀ t, (base t).run s = (base' t).run s)
    (hchall : ∀ t : ℕ, (chall t).run s = (chall' t).run s)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) :
    (securityImplOf base chall vulnA vulnB scka t).run s =
      (securityImplOf base' chall' vulnA vulnB scka t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · exact hbase t
  · rfl
  · rfl
  · exact hchall t
  · rfl
  · rfl


/-- Bookkeeping of one assembled security query from `s`. Assume that base queries from `s` keep
both `exposed` and `challenged`, and that challenge queries from `s` keep `exposed` and do not
shrink `challenged`. Then the query shrinks neither set, and every newly exposed epoch was not
challenged in `s`. -/
theorem securityImplOf_bookkeeping (s : GameState StA StB I Rho)
    (hbase : ∀ t z, z ∈ support ((base t).run s) →
      z.2.exposed = s.exposed ∧ z.2.challenged = s.challenged)
    (hchall : ∀ (t : ℕ) z, z ∈ support ((chall t).run s) →
      z.2.exposed = s.exposed ∧ s.challenged ⊆ z.2.challenged)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    s.exposed ⊆ z.2.exposed ∧ s.challenged ⊆ z.2.challenged ∧
      ∀ e ∈ z.2.exposed, e ∉ s.exposed → e ∉ s.challenged := by
  have hgrow : ∀ (E : Finset ℕ) (u : GameState StA StB I Rho), E ∩ s.challenged = ∅ →
      u.challenged = s.challenged → u.exposed = s.exposed ∪ E →
      s.exposed ⊆ u.exposed ∧ s.challenged ⊆ u.challenged ∧
        ∀ e ∈ u.exposed, e ∉ s.exposed → e ∉ s.challenged := by
    intro E u hE hc he
    refine ⟨by rw [he]; exact Finset.subset_union_left, by rw [hc], fun e he' hnot hchal => ?_⟩
    rw [he, Finset.mem_union] at he'
    have hmem : e ∈ E ∩ s.challenged := Finset.mem_inter.2 ⟨he'.resolve_left hnot, hchal⟩
    rw [hE] at hmem
    exact Finset.notMem_empty e hmem
  rcases t with (((((t | u) | u) | t) | u) | u)
  · obtain ⟨he, hc⟩ := hbase t z hz
    exact hgrow ∅ z.2 (by simp) hc (by rw [he, Finset.union_empty])
  · cases u
    obtain ⟨hc, E, hE, he⟩ := oracleSendArleak_bookkeeping scka vulnA.rleak s z hz
    exact hgrow E z.2 hE hc he
  · cases u
    obtain ⟨hc, E, hE, he⟩ := oracleSendBrleak_bookkeeping scka vulnB.rleak s z hz
    exact hgrow E z.2 hE hc he
  · obtain ⟨he, hc⟩ := hchall t z hz
    exact ⟨by rw [he], hc, fun e he' hnot => by rw [he] at he'; exact absurd he' hnot⟩
  · cases u
    rcases oracleCorruptA_support vulnA.corrupt s z hz with h | ⟨hE, h⟩
    · rw [h]; exact hgrow ∅ s (by simp) rfl (by simp)
    · rw [h]; exact hgrow _ _ hE rfl rfl
  · cases u
    rcases oracleCorruptB_support vulnB.corrupt s z hz with h | ⟨hE, h⟩
    · rw [h]; exact hgrow ∅ s (by simp) rfl (by simp)
    · rw [h]; exact hgrow _ _ hE rfl rfl

end SecurityFamily

end SCKAScheme
