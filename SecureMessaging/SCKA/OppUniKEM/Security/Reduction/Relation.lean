/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic
import SecureMessaging.SCKA.OppUniKEM.Correctness.Invariant
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator
import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import SecureMessaging.SCKA.Security
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Material

/-!
# Marking honest states

**Setting.** Fix a selected epoch `e`, complete material `m`, and a candidate key `kStar`.
Honest local and game states contain private values; the simulator's states contain marked
values.

**Definitions.**

- `mark`, `markA`, `markB`, `markState e s`: mark the private values of an honest state, making
  those of epoch `e` and the keys recorded at `e` unavailable and all others known; public fields,
  message tables, counters, and bookkeeping sets are kept. `markCoins` marks send coins.
- `pinnedChallenge e kStar := challengeWith id e kStar`: the challenge oracle on honest states,
  answering an eligible challenge at `t` with a uniform key if `0 < t < e`, with `kStar` if
  `t = e`, and with the recorded key otherwise. The simulator's `challenge` is `challengeWith`
  reading marked keys.

**Results.** Each local send and receive of the simulator, run from a marked state over the
marked KEM with the public key and ciphertext of `m`, equals the same operation over
`Pinned.kem m` from the honest state followed by marking its outputs. The simulator's challenge
from `markState e s` is `pinnedChallenge e kStar` from `s` followed by marking. For a local state
`s`, unmarking its marked state fails exactly when a corruption of `s` exposes `e`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- A's send outputs no key: every possible successful result of `sendA s` has key component
`none`. -/
theorem sendA_key_none
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (s : StA onoff Sym)
    (key : Option (ℕ × K)) (msg : Message Sym) (t : ℕ) (next : StA onoff Sym)
    (hout : some (key, msg, t, next) ∈ support (sendA base onoff ecEk s)) :
    key = none := by
  cases hd : s.dkA <;> cases hp : s.ekA <;> cases ha : s.ack.ekRec <;>
    simp only [sendA, hd, hp, ha, Bool.false_eq_true, ↓reduceIte,
      pure_bind, mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at hout
  all_goals aesop

/-- If a possible result of `sendB s` outputs the key `(t, k)`, then `t = s.t` and
`s.ct1 = none`: the key comes from online encapsulation in this send. -/
theorem sendB_key_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (s : StB onoff Sym)
    (t : ℕ) (k : K) (msg : Message Sym) (tsnd : ℕ) (next : StB onoff Sym)
    (hout : some (some (t, k), msg, tsnd, next) ∈
      support (sendB base onoff ecCt0 ecCt1 s)) :
    t = s.t ∧ s.ct1 = none := by
  cases hc0 : s.ct0 <;> cases hp : s.ekA <;> cases hc1 : s.ct1 <;>
    cases hst : s.stCt <;> cases ha : s.ack.ctRec <;>
    simp only [sendB, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind, mem_support_bind_iff,
      mem_support_pure_iff, Prod.exists, Option.some.injEq, Prod.mk.injEq,
      Option.some_ne_none] at hout
  all_goals aesop

/-- Every possible successful result of `sendArleak s` outputs no key and returns either no coins
or key-generation coins. -/
theorem sendArleak_shape
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (s : StA onoff Sym) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StA onoff Sym)
    (coins : SendRand leak.KeygenRand leak.OffRand leak.OnRand)
    (hout : some (key, msg, t, next, coins) ∈ support (sendArleak base onoff ecEk leak s)) :
    key = none ∧ (coins = .none ∨ ∃ r, coins = .keygen r) := by
  cases hd : s.dkA <;> cases hp : s.ekA <;> cases ha : s.ack.ekRec <;>
    simp only [sendArleak, hd, hp, ha, Bool.false_eq_true, ↓reduceIte,
      pure_bind, mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at hout
  all_goals aesop

/-- Every possible successful result of `sendBrleak s` returns no coins, offline coins, online
coins, or a pair of offline and online coins. -/
theorem sendBrleak_coins
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (s : StB onoff Sym) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StB onoff Sym)
    (coins : SendRand leak.KeygenRand leak.OffRand leak.OnRand)
    (hout : some (key, msg, t, next, coins) ∈
      support (sendBrleak base onoff ecCt0 ecCt1 leak s)) :
    coins = .none ∨ (∃ r, coins = .off r) ∨ (∃ r, coins = .on r) ∨
      (∃ r₀ r₁, coins = .offOn r₀ r₁) := by
  cases hc0 : s.ct0 <;> cases hp : s.ekA <;> cases hc1 : s.ct1 <;>
    cases hst : s.stCt <;> cases ha : s.ack.ctRec <;>
    simp only [sendBrleak, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind, mem_support_bind_iff,
      mem_support_pure_iff, Prod.exists, Option.some.injEq, Prod.mk.injEq] at hout
  all_goals aesop

/-- The version of `sendB_key_fresh` for `sendBrleak`. -/
theorem sendBrleak_key_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (s : StB onoff Sym) (t : ℕ) (k : K) (msg : Message Sym)
    (tsnd : ℕ) (next : StB onoff Sym)
    (coins : SendRand leak.KeygenRand leak.OffRand leak.OnRand)
    (hout : some (some (t, k), msg, tsnd, next, coins) ∈
      support (sendBrleak base onoff ecCt0 ecCt1 leak s)) :
    t = s.t ∧ s.ct1 = none := by
  apply sendB_key_fresh base onoff ecCt0 ecCt1 s t k msg tsnd next
  rw [← sendBrleak_forget base onoff ecCt0 ecCt1 leak s]
  exact (mem_support_bind_iff _ _ _).mpr ⟨_, hout, by simp⟩

/-- If `s` satisfies `reachableInv` and `s.stB.ct1 = none`, then no key is recorded for B's current
epoch: `s.keyA s.stB.t = none` and `s.keyB s.stB.t = none`. -/
theorem keys_none_before_online
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hc : s.stB.ct1 = none) :
    s.keyA s.stB.t = none ∧ s.keyB s.stB.t = none := by
  classical
  obtain ⟨T, hT⟩ := hs
  have hon : (T s.stB.t).on = none := by
    have h := hT.onB
    rw [hc] at h
    simpa using h
  have hk : (T s.stB.t).key = none := by simp [EpochTranscript.key, hon]
  rw [hT.keyA, hT.keyB, hk]
  simp

end oppUniKemCKA.Security.Embedding

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Mark a value `value` of epoch `t`: unavailable (`none`) if `t = e`, and known
(`some value`) otherwise. -/
def mark {α : Type} (e t : ℕ) (value : α) : Option α :=
  if t = e then none else some value

/-- A's marked state: a present secret key is marked with A's epoch `s.t`; all other fields are
unchanged. -/
def markA {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (e : ℕ) (s : StA onoff Sym) : StateA (Option SK) PK onoff.C₀ Sym where
  dkA := s.dkA.map (mark e s.t)
  ekA := s.ekA
  ct0 := s.ct0
  t := s.t
  ich := s.ich
  lch := s.lch
  ack := s.ack

/-- B's marked state: a present offline state is marked with B's epoch `s.t`; all other fields are
unchanged. -/
def markB {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (e : ℕ) (s : StB onoff Sym) : StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym where
  ekA := s.ekA
  ct0 := s.ct0
  ct1 := s.ct1
  stCt := s.stCt.map (mark e s.t)
  t := s.t
  ich := s.ich
  lch := s.lch
  ack := s.ack

/-- Marked game state of an honest game state `s`: both local states are marked, each recorded key
of epoch `t` is marked with `t`, and the message tables, counters, and exposure and challenge sets
are unchanged. -/
def markState {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (e : ℕ) (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    SimState onoff Sym where
  stA := markA e s.stA
  stB := markB e s.stB
  keyA t := (s.keyA t).map (mark e t)
  keyB t := (s.keyB t).map (mark e t)
  msgA := s.msgA
  msgB := s.msgB
  nA := s.nA
  nB := s.nB
  tcurA := s.tcurA
  tcurB := s.tcurB
  exposed := s.exposed
  challenged := s.challenged
  correct := s.correct

/-- Marking a key table commutes with recording a key `k` at epoch `t`; the new entry is
`mark e t k`. -/
theorem mark_update (e t : ℕ) (table : ℕ → Option K) (k : K) :
    (fun u => (Function.update table t (some k) u).map (mark e u)) =
      Function.update (fun u => (table u).map (mark e u)) t (some (mark e t k)) := by
  funext u
  by_cases h : u = t <;> simp [h, Function.update_of_ne]

/-- `revealA (markA e s)` is `none` if `e ∈ vulnCorrA s`, and `some s` otherwise. -/
theorem revealA_markA_eq {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} (e : ℕ) (s : StA onoff Sym) :
    revealA (markA e s) = if e ∈ vulnCorrA kem onoff s then none else some s := by
  rcases s with ⟨dk, pk, ct, t, ich, lch, ack⟩
  cases dk <;> by_cases ht : t = e <;>
    simp_all [revealA, revealField, markA, mark, vulnCorrA, eq_comm]

/-- The version of `revealA_markA_eq` for B. -/
theorem revealB_markB_eq {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} (e : ℕ) (s : StB onoff Sym) :
    revealB (markB e s) = if e ∈ vulnCorrB kem onoff s then none else some s := by
  rcases s with ⟨pk, ct0, ct1, st, t, ich, lch, ack⟩
  cases st <;> by_cases ht : t = e <;>
    simp_all [revealB, revealField, markB, mark, vulnCorrB, eq_comm]

/-- Marking preserves A's corruption-vulnerable epochs: the set `{(markA e s).t}` if `markA e s`
has a secret key, and `∅` otherwise, equals `vulnCorrA s`. -/
theorem markA_vulnerable {base : KEMScheme ProbComp K PK SK C}
    {onoff : base.OnOffStructure} (e : ℕ) (s : StA onoff Sym) :
    (if (markA e s).dkA.isSome then {(markA e s).t} else ∅) = vulnCorrA base onoff s := by
  cases h : s.dkA <;> simp [markA, vulnCorrA, h]

/-- The version of `markA_vulnerable` for B. -/
theorem markB_vulnerable {base : KEMScheme ProbComp K PK SK C}
    {onoff : base.OnOffStructure} (e : ℕ) (s : StB onoff Sym) :
    (if (markB e s).stCt.isSome then {(markB e s).t} else ∅) = vulnCorrB base onoff s := by
  cases h : s.stCt <;> simp [markB, vulnCorrB, h]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq Sym]

/-- B's receive outputs no key: if `recvB s msg = some (key, t, next)`, then `key = none`. -/
theorem recvB_key_none
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (s : StB onoff Sym) (msg : Message Sym)
    (key : Option (ℕ × K)) (t : ℕ) (next : StB onoff Sym)
    (h : recvB base onoff ecEk s msg = some (key, t, next)) : key = none := by
  unfold recvB at h
  repeat' split at h
  all_goals simp_all

/-- If A's receive with constant decapsulation result `key` outputs the key `(t, k)`, then `t = s.t`
(A's epoch before the receive) and `key = some k`. -/
theorem recvA_key_source
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (key : Option K)
    (s : StA onoff Sym) (msg : Message Sym)
    (t : ℕ) (k : K) (trcv : ℕ) (next : StA onoff Sym)
    (h : recvA base onoff (fun _ _ => key) ecCt0 ecCt1 s msg =
      some (some (t, k), trcv, next)) :
    t = s.t ∧ key = some k := by
  rcases msg with ⟨ch, ack, epoch, bit⟩
  by_cases ht : s.t = epoch
  all_goals
    simp only [recvA, ht, ↓reduceIte] at h
    repeat' split at h
    all_goals simp_all

set_option backward.dsimp.instances true in
/-- For every B-state `s` and message `msg`, B's receive over the marked KEM from `markB e s`
equals `recvB s msg` followed by marking the successor state; the output key is `none`. -/
theorem recvB_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (e : ℕ)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K))
    (s : StB onoff Sym) (msg : Message Sym) :
    recvB (kem base onoff selectedA selectedB pkStar ctStar key)
      (onOff base onoff selectedA selectedB pkStar ctStar key) ecEk (markB e s) msg =
      (recvB base onoff ecEk s msg).map (fun (_, t, u) => (none, t, markB e u)) := by
  rcases msg with ⟨ch, ack, t, b⟩
  by_cases hadv : s.t < t
  all_goals
    simp only [recvB, markB, hadv, ↓reduceIte]
    repeat' (split <;> simp_all only [Option.map_none, Option.map_some])

set_option maxHeartbeats 800000 in
-- Splitting the receive branches also expands the state-marking equations.
set_option backward.dsimp.instances true in
/-- For every A-state `s`, message `msg`, and `key : Option K`, A's receive over the marked KEM
with decapsulation result `key.map (mark e s.t)` from `markA e s` equals A's receive with
constant decapsulation result `key` from `s`, followed by marking the output key and the
successor state. -/
theorem recvA_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (e : ℕ)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option K)
    (s : StA onoff Sym) (msg : Message Sym) :
    recvA (kem base onoff selectedA selectedB pkStar ctStar (key.map (mark e s.t)))
      (onOff base onoff selectedA selectedB pkStar ctStar (key.map (mark e s.t)))
      (deterministic base onoff selectedA selectedB pkStar ctStar (key.map (mark e s.t))).decapsDet
      ecCt0 ecCt1 (markA e s) msg =
      (recvA base onoff (fun _ _ => key) ecCt0 ecCt1 s msg).map
        (fun (out, t, u) =>
          (out.map (fun (epoch, k) => (epoch, mark e epoch k)), t, markA e u)) := by
  rcases msg with ⟨ch, ack, t, b⟩
  cases b
  all_goals try (rename_i bit; fin_cases bit)
  all_goals cases ch
  all_goals cases hd : s.dkA <;> cases hc : s.ct0 <;> cases hk : key
  all_goals
    simp only [recvA, markA, hd, hc, Option.bind_eq_bind, Option.pure_def]
    repeat' (split <;> simp_all only [Option.bind_some, Option.bind_none,
      Option.map_none, Option.map_some])
  all_goals
    simp_all only [Fin.mk_one, Fin.isValue, Bool.and_eq_true, beq_iff_eq]
    repeat' (split <;> simp_all only [Option.map_none, Option.map_some, and_true,
      Bool.not_eq_true, Nat.add_eq_left, one_ne_zero, and_false, ↓reduceIte])

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Challenge oracle on honest game states for selected epoch `e` and candidate key `kStar`:
`challengeWith` reading each recorded key directly. -/
def pinnedChallenge [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  challengeWith id e kStar

/-- For every query `t` and honest game state `s`, `challenge e kStar t` from `markState e s`
equals `pinnedChallenge e kStar t` from `s` followed by marking the successor state. -/
theorem challenge_mark [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) (t : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (challenge onoff e kStar t).run (markState e s) =
      Prod.map id (markState e) <$> (pinnedChallenge onoff e kStar t).run s := by
  simp only [challenge, pinnedChallenge, challengeWith, StateT.run_bind, StateT.run_get, pure_bind]
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

/-- The pinned challenge records challenges: each query either keeps the state or inserts the
queried epoch, which is then unexposed, into `challenged`. -/
theorem pinnedChallenge_recordsChallenges [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) :
    SCKAScheme.RecordsChallenges (pinnedChallenge (Sym := Sym) onoff e kStar) := by
  intro t s z hz
  by_cases helig : t ∈ s.exposed ∨ t ∈ s.challenged
  · left
    simp only [pinnedChallenge, challengeWith, StateT.run_bind, StateT.run_get, pure_bind, helig,
      ↓reduceIte, StateT.run_pure, mem_support_pure_iff] at hz
    rw [hz]
  · simp only [pinnedChallenge, challengeWith, StateT.run_bind, StateT.run_get, pure_bind, helig,
      ↓reduceIte] at hz
    repeat' split at hz
    all_goals
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_map, StateT.run_set,
        StateT.run_monadLift, monadLift_self, bind_pure_comp,
        map_pure, Functor.map_map, mem_support_pure_iff,
        support_map, support_uniformSample, Set.image_univ, Set.mem_range] at hz
    all_goals
      first
      | (obtain rfl := hz; exact Or.inl rfl)
      | (obtain ⟨_, rfl⟩ := hz; exact Or.inr ⟨fun h => helig (Or.inl h), rfl⟩)

/-- If `e` is neither exposed nor challenged in `s` and a key is recorded for `e`, then
`pinnedChallenge e kStar e` from `s` is `pure (some kStar, s')`, where `s'` inserts `e` into
`challenged`. -/
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
  all_goals simp [pinnedChallenge, challengeWith, helig, hA, hB, StateT.run_bind,
    StateT.run_get, StateT.run_set]

/-- Unless `t = e` and `e` is unexposed, unchallenged, and has a recorded key, the computations
`pinnedChallenge e k t` and `pinnedChallenge e k' t` from `s` are equal. -/
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
    · simp [pinnedChallenge, challengeWith, hg, StateT.run_bind, StateT.run_get]
    · have hk : s.keyA e = none ∧ s.keyB e = none := by
        cases hA : s.keyA e <;> cases hB : s.keyB e <;> simp_all
      simp [pinnedChallenge, challengeWith, hg, hk, StateT.run_bind, StateT.run_get]
  · simp only [pinnedChallenge, challengeWith, ht, ↓reduceIte]

/-- If every key recorded by A or B at epoch `e` in `s` equals `kStar`, then for every
challenged epoch `t`, `pinnedChallenge e kStar t` and
`oracleChall (decide (0 < t ∧ t < e)) t` are equal computations from `s`. -/
theorem pinnedChallenge_eq_recorded [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) (t : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hkey : ∀ k, s.keyA e = some k ∨ s.keyB e = some k → k = kStar) :
    (pinnedChallenge onoff e kStar t).run s =
      (SCKAScheme.oracleChall (decide (0 < t ∧ t < e))
        (StA onoff Sym) (StB onoff Sym) K (Message Sym) t).run s := by
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, hg]
  · by_cases ht : t = e
    · subst t
      cases hA : s.keyA e with
      | none =>
        cases hB : s.keyB e with
        | none => simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, hg, hA, hB]
        | some k =>
          have hk := hkey k (.inr hB)
          subst k
          simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, hg, hA, hB]
      | some k =>
        have hk := hkey k (.inl hA)
        subst k
        simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, hg, hA]
    · cases hA : s.keyA t <;> cases hB : s.keyB t <;> by_cases hr : 0 < t ∧ t < e <;>
        simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, hg, hA, hB, ht, hr]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Mark each coin returned by a send in epoch `t` with `mark e t`; `SendRand.none` is
unchanged. -/
def markCoins {KG OFF ON : Type} (e t : ℕ) :
    SendRand KG OFF ON → SendRand (Option KG) (Option OFF) (Option ON)
  | .none => .none
  | .keygen r => .keygen (mark e t r)
  | .off r => .off (mark e t r)
  | .on r => .on (mark e t r)
  | .offOn r₀ r₁ => .offOn (mark e t r₀) (mark e t r₁)

set_option maxHeartbeats 1000000 in
-- Both leakage witnesses expand through different secret and coin types.
/-- For every A-state `s`, flag `selectedB`, and decapsulation results `keyS`, `keyH`, A's leaking
send over the marked KEM from `markA e s`, with A selected if `s.t = e`, equals A's leaking send
over `Pinned.kem m` from `s`, followed by marking the successor state and coins; the output key
is `none`. -/
theorem sendArleak_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (selectedB : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (s : StA onoff Sym) :
    sendArleak (kem base onoff (decide (s.t = e)) selectedB m.keygen.1.1 m.ciphertext keyS)
      (onOff base onoff (decide (s.t = e)) selectedB m.keygen.1.1 m.ciphertext keyS)
      ecEk (leakage base onoff leak (decide (s.t = e)) selectedB
        m.keygen.1.1 m.ciphertext keyS) (markA e s) =
    (fun out => out.map (fun (_, msg, epoch, next, coins) =>
      (none, msg, epoch, markA e next, markCoins e s.t coins))) <$>
      sendArleak (Pinned.kem m (decide (s.t = e)) selectedB selectedB keyH)
        (Pinned.onOff m (decide (s.t = e)) selectedB selectedB keyH) ecEk
        (Pinned.leakage leak m (decide (s.t = e)) selectedB selectedB keyH) s := by
  by_cases he : s.t = e <;> cases hd : s.dkA
  all_goals
    simp only [sendArleak, markA, hd, Option.map_none, Option.map_some]
    try dsimp only [leakage, Pinned.leakage]
    simp [keygenLeak, markCoins, mark, he, monad_norm]

set_option maxHeartbeats 2000000 in
-- Each leakage phase expands its output, coin conversion, and state update.
/-- For every B-state `s`, flag `selectedA`, and decapsulation results `keyS`, `keyH`, B's leaking
send over the marked KEM from `markB e s`, with B selected if `s.t = e`, equals B's leaking send
over `Pinned.kem m` from `s`, followed by marking the output key, successor state, and coins. -/
theorem sendBrleak_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (selectedA : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (s : StB onoff Sym) :
    sendBrleak (kem base onoff selectedA (decide (s.t = e)) m.keygen.1.1 m.ciphertext keyS)
      (onOff base onoff selectedA (decide (s.t = e)) m.keygen.1.1 m.ciphertext keyS)
      ecCt0 ecCt1 (leakage base onoff leak selectedA (decide (s.t = e))
        m.keygen.1.1 m.ciphertext keyS) (markB e s) =
    (fun out => out.map (fun (key, msg, epoch, next, coins) =>
      (key.map (fun (t, k) => (t, mark e t k)), msg, epoch,
        markB e next, markCoins e s.t coins))) <$>
      sendBrleak (Pinned.kem m selectedA (decide (s.t = e)) (decide (s.t = e)) keyH)
        (Pinned.onOff m selectedA (decide (s.t = e)) (decide (s.t = e)) keyH) ecCt0 ecCt1
        (Pinned.leakage leak m selectedA (decide (s.t = e)) (decide (s.t = e)) keyH) s := by
  by_cases he : s.t = e <;> cases hct0 : s.ct0 <;> cases hek : s.ekA <;>
    cases hct1 : s.ct1 <;> cases hst : s.stCt <;> cases hack : s.ack.ctRec
  all_goals
    simp only [sendBrleak, markB, hct0, hek, hct1, hst, Option.map_none, Option.map_some]
    try dsimp only [leakage, Pinned.leakage]
    simp [offLeak, onLeak, Material.ciphertext, markCoins, mark,
      he, hct0, hek, hct1, hst, hack, monad_norm]

/-- The version of `sendArleak_mark` for `sendA`, without coins. -/
theorem sendA_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (selectedB : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (s : StA onoff Sym) :
    sendA (kem base onoff (decide (s.t = e)) selectedB m.keygen.1.1 m.ciphertext keyS)
      (onOff base onoff (decide (s.t = e)) selectedB m.keygen.1.1 m.ciphertext keyS)
      ecEk (markA e s) =
    (fun out => out.map (fun (_, msg, epoch, next) => (none, msg, epoch, markA e next))) <$>
      sendA (Pinned.kem m (decide (s.t = e)) selectedB selectedB keyH)
        (Pinned.onOff m (decide (s.t = e)) selectedB selectedB keyH) ecEk s := by
  rw [sendA_eq_map_sendArleak _ _ ecEk
      (leakage base onoff leak (decide (s.t = e)) selectedB m.keygen.1.1 m.ciphertext keyS),
    sendA_eq_map_sendArleak _ _ ecEk
      (Pinned.leakage leak m (decide (s.t = e)) selectedB selectedB keyH),
    sendArleak_mark base onoff ecEk leak m e selectedB keyS keyH s,
    Functor.map_map, Functor.map_map]
  congr 1
  funext out
  rcases out with _ | ⟨key, msg, epoch, next, coins⟩ <;> rfl

/-- The version of `sendBrleak_mark` for `sendB`, without coins. -/
theorem sendB_mark
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (selectedA : Bool)
    (keyS : Option (Option K)) (keyH : Option K) (s : StB onoff Sym) :
    sendB (kem base onoff selectedA (decide (s.t = e)) m.keygen.1.1 m.ciphertext keyS)
      (onOff base onoff selectedA (decide (s.t = e)) m.keygen.1.1 m.ciphertext keyS)
      ecCt0 ecCt1 (markB e s) =
    (fun out => out.map (fun (key, msg, epoch, next) =>
      (key.map (fun (t, k) => (t, mark e t k)), msg, epoch, markB e next))) <$>
      sendB (Pinned.kem m selectedA (decide (s.t = e)) (decide (s.t = e)) keyH)
        (Pinned.onOff m selectedA (decide (s.t = e)) (decide (s.t = e)) keyH) ecCt0 ecCt1 s := by
  rw [sendB_eq_map_sendBrleak
      (kem base onoff selectedA (decide (s.t = e)) m.keygen.1.1 m.ciphertext keyS)
      (onOff base onoff selectedA (decide (s.t = e)) m.keygen.1.1 m.ciphertext keyS) ecCt0 ecCt1
      (leakage base onoff leak selectedA (decide (s.t = e)) m.keygen.1.1 m.ciphertext keyS),
    sendB_eq_map_sendBrleak
      (Pinned.kem m selectedA (decide (s.t = e)) (decide (s.t = e)) keyH)
      (Pinned.onOff m selectedA (decide (s.t = e)) (decide (s.t = e)) keyH) ecCt0 ecCt1
      (Pinned.leakage leak m selectedA (decide (s.t = e)) (decide (s.t = e)) keyH),
    sendBrleak_mark base onoff ecCt0 ecCt1 leak m e selectedA keyS keyH s,
    Functor.map_map, Functor.map_map]
  congr 1
  funext out
  rcases out with _ | ⟨key, msg, epoch, next, coins⟩ <;> rfl

end oppUniKemCKA.Security.Embedding
