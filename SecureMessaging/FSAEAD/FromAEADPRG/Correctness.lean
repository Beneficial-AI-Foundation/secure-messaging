/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.FSAEAD.Correctness
import SecureMessaging.FSAEAD.FromAEADPRG.Construction

/-!
# FS-AEAD from AEAD and PRG — Correctness

Correctness of the FS-AEAD construction of [ACD19, Figure 6]. Let the AEAD scheme be
correct. Then:
- `fromAEADPRG_noFirstDeliverWin`: in the game of Figure 5, `O-Deliver-B` never changes
  `win` from false to true (`NoFirstDeliverWin`). With `securityExp_eq_noDeliverWin`, this
  removes the `win` of `O-Deliver-B` from the real game `H0`, before the PRG step. ACD19
  removes it in the step from `H1` to `H2`, where the keys are uniform.
- `rcvAll_honest_initR`: without an adversary, B outputs `(j, m)` for every
  `(j, Enc(K_j, (j, a), m))` with `j ≥ 1`, in any order and each `j` at most once. By
  `sendAll_eq`, A's `j`-th ciphertext has this form.

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — §4.2.2, Figure 6, proof of Theorem 5 (step from H1 to H2).

The proof follows B's state along the PRG chain `w_0 = k`, `(w_j, K_j) = G(w_{j-1})`.
`GameInv` is the invariant of the game: A and B are on the chain, every record in `trans`
is A's honest ciphertext, and while `win` is false, B still has the key of every record.
Every oracle keeps `GameInv`, so every reachable state satisfies it.
-/

namespace FSAEADScheme

variable {W Kae : Type}

namespace FromAEADPRG

/-! ## The PRG chain -/

/-- The seed `w_j` of the chain from `w`:
```text
w_0 = w,   (w_j, K_j) = G(w_{j-1})   for j ≥ 1
``` -/
def chainState (prg : PRGScheme W (W × Kae)) (w : W) (j : ℕ) : W :=
  (fun w => (prg.gen w).1)^[j] w

/-- The key `K_j` of the chain from `w`, for `j ≥ 1`:
```text
(w_j, K_j) = G(w_{j-1})
```
The chain has no key at position 0. `chainKey prg w 0` is `K_1`, a junk value. -/
def chainKey (prg : PRGScheme W (W × Kae)) (w : W) (j : ℕ) : Kae :=
  (prg.gen (chainState prg w (j - 1))).2

/-- Let `w_0, w_1, …` be the chain from `w`. Then `w_0 = w`. -/
@[simp]
theorem chainState_zero (prg : PRGScheme W (W × Kae)) (w : W) : chainState prg w 0 = w :=
  rfl

/-- Let `w_0, w_1, …` be the chain from `w`. Then for every `j`, `w_{j+1}` is the first
component of `G(w_j)`. -/
theorem chainState_succ (prg : PRGScheme W (W × Kae)) (w : W) (j : ℕ) :
    chainState prg w (j + 1) = (prg.gen (chainState prg w j)).1 :=
  Function.iterate_succ_apply' _ j w

/-! ## Skipping -/

/-- Let `(w', i', D')` be the state after `n` steps of `skip` from `(w_B, i_B, D)`. Then
`w' = w_n`, the `n`-th seed of the chain from `w_B`. -/
theorem skipSteps_w (prg : PRGScheme W (W × Kae)) (n : ℕ) (st : RecvState W Kae) :
    (skipSteps prg n st).w = chainState prg st.w n := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => exact ih _

/-- Let `(w', i', D')` be the state after `n` steps of `skip` from `(w_B, i_B, D)`. Then
`i' = i_B + n`. -/
theorem skipSteps_iB (prg : PRGScheme W (W × Kae)) (n : ℕ) (st : RecvState W Kae) :
    (skipSteps prg n st).iB = st.iB + n := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => simp only [skipSteps, ih]; omega

/-- Let `(w', i', D')` be the state after `n` steps of `skip` from `(w_B, i_B, D)`, and let
`K_1, K_2, …` be the keys of the chain from `w_B`. Then for every `j`:
```text
D'[j] = K_{j - i_B}   if i_B < j ≤ i_B + n
D'[j] = D[j]          otherwise
``` -/
theorem skipSteps_D (prg : PRGScheme W (W × Kae)) (n : ℕ) (st : RecvState W Kae) (j : ℕ) :
    (skipSteps prg n st).D j =
      if st.iB < j ∧ j ≤ st.iB + n then some (chainKey prg st.w (j - st.iB)) else st.D j := by
  induction n generalizing st with
  | zero => simp only [skipSteps]; split_ifs <;> first | rfl | omega
  | succ n ih =>
    simp only [skipSteps, ih, Function.update_apply]
    split_ifs <;> try first | rfl | omega
    · obtain ⟨k, hk₁, hk₂⟩ : ∃ k, j - (st.iB + 1) = k + 1 ∧ j - st.iB = k + 2 :=
        ⟨j - st.iB - 2, by omega, by omega⟩
      rw [hk₁, hk₂]
      rfl
    · rw [show j - st.iB = 1 by omega]
      rfl

/-- Let `i_B < u`, and let `(w', i', D')` be the result of `skip(u)` on `(w_B, i_B, D)`.
Then `i' = u - 1`, and `w'` is the `(u - 1 - i_B)`-th seed of the chain from `w_B`. -/
theorem skip_w_iB (prg : PRGScheme W (W × Kae)) (u : ℕ) (st : RecvState W Kae)
    (h : st.iB < u) :
    (skip prg u st).w = chainState prg st.w (u - 1 - st.iB) ∧ (skip prg u st).iB = u - 1 := by
  refine ⟨skipSteps_w prg _ st, ?_⟩
  simp only [skip, skipSteps_iB]
  omega

/-- Let `w_0, w_1, …` be the chain from `w`. Then the `n`-th seed of the chain from `w_o`
is `w_{o + n}`. -/
theorem chainState_add (prg : PRGScheme W (W × Kae)) (w : W) (o n : ℕ) :
    chainState prg (chainState prg w o) n = chainState prg w (o + n) := by
  simp only [chainState, Nat.add_comm o n, Function.iterate_add_apply]

/-- Let `K_1, K_2, …` be the keys of the chain from `w`, and let `n ≥ 1`. Then the `n`-th
key of the chain from `w_o` is `K_{o + n}`. -/
theorem chainKey_add (prg : PRGScheme W (W × Kae)) (w : W) (o n : ℕ) (hn : 1 ≤ n) :
    chainKey prg (chainState prg w o) n = chainKey prg w (o + n) := by
  simp only [chainKey, chainState_add]
  rw [show o + (n - 1) = o + n - 1 by omega]

/-! ## Receiving -/

/-- B's state is on the chain from `k`: `w_B = w_{i_B}`, every entry of `D` is `⊥` or the
key `K_j` of its index, and `D[j] = ⊥` for `j = 0` and for `j > i_B`. -/
structure OnChain (prg : PRGScheme W (W × Kae)) (k : W) (st : RecvState W Kae) : Prop where
  w_eq : st.w = chainState prg k st.iB
  D_key : ∀ j K, st.D j = some K → K = chainKey prg k j
  D_none : ∀ j, (j = 0 ∨ st.iB < j) → st.D j = none

/-- Let `w_B = w_{i_B}` on the chain from `k`, and let `i_B < i`. Then one step of `G` after
`skip(i)` gives `(w_i, K_i)`. -/
theorem skip_gen (prg : PRGScheme W (W × Kae)) {k : W} {st : RecvState W Kae} {i : ℕ}
    (hw : st.w = chainState prg k st.iB) (hlt : st.iB < i) :
    prg.gen (skip prg i st).w = (chainState prg k i, chainKey prg k i) := by
  have h1 : chainState prg st.w (i - 1 - st.iB + 1) = chainState prg k i := by
    rw [hw, chainState_add]
    congr 1
    omega
  have h2 : chainKey prg st.w (i - 1 - st.iB + 1) = chainKey prg k i := by
    rw [hw, chainKey_add _ _ _ _ (by omega)]
    congr 1
    omega
  rw [(skip_w_iB prg i st hlt).1, ← h1, ← h2, chainState_succ]
  rfl

variable {Cae AD M : Type}

/-- Let B's state `v_B = (w_B, i_B, D)` be on the chain from `k`, and let `FS-Rcv` accept
`(i, e)` with associated data `a`, with output `(v_B', i', m')`. Then:
- `i' = i ≥ 1`, and `m' = Dec(K_i, (i, a), e)`;
- `v_B'` is on the chain from `k`, with `i_B' = max(i_B, i)`;
- `D'[i] = ⊥`, and for `j ≠ i`, `D'[j] = K_j` if `i_B < j < i`, and `D'[j] = D[j]`
  otherwise. -/
theorem rcv_some (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    {k : W} {st st' : RecvState W Kae} (hst : OnChain prg k st) {a : AD} {i i' : ℕ}
    {e : Cae} {m' : M} (h : rcv ae prg st a (i, e) = some (st', i', m')) :
    i' = i ∧ 1 ≤ i ∧ ae.decrypt (chainKey prg k i) (i, a) e = some m' ∧
      OnChain prg k st' ∧ st'.iB = max st.iB i ∧ st'.D i = none ∧
      ∀ j, j ≠ i → st'.D j =
        if st.iB < j ∧ j < i then some (chainKey prg k j) else st.D j := by
  rcases hD : st.D i with _ | K
  · simp only [rcv, trySkipped, hD] at h
    have hlt : st.iB < i := by
      by_contra hle
      simp only [Nat.le_of_not_lt hle, ↓reduceIte, Option.pure_def, Option.bind_eq_bind,
          Option.bind_some, Option.bind_none, reduceCtorEq] at h
    simp only [Nat.not_le_of_lt hlt, ↓reduceIte] at h
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some,
      Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨m, hm, rfl, rfl, rfl⟩ := h
    have hG := skip_gen prg (st := { w := st.w, iB := st.iB, D := Function.update st.D i none })
      hst.w_eq hlt
    have hD1 : ∀ j, (skip prg i { w := st.w, iB := st.iB, D := Function.update st.D i none }).D j
        = if st.iB < j ∧ j < i then some (chainKey prg k j)
          else Function.update st.D i none j := by
      intro j
      unfold skip
      rw [skipSteps_D]
      dsimp only
      split_ifs with c1 c2 c2 <;> try omega
      · rw [hst.w_eq, chainKey_add _ _ _ _ (by omega)]
        congr 2
        omega
      · rfl
    refine ⟨rfl, by omega, (congrArg (ae.decrypt · (i, a) e) (congrArg Prod.snd hG)).symm.trans hm,
      ⟨congrArg Prod.fst hG, ?_, ?_⟩, by simp only; omega, ?_, ?_⟩
    · intro j K hj
      simp only [hD1] at hj
      split_ifs at hj with c
      · exact (Option.some.inj hj).symm
      · by_cases hji : j = i
        · simp only [hji, Function.update_self, reduceCtorEq] at hj
        · rw [Function.update_of_ne hji] at hj
          exact hst.D_key j K hj
    · intro j hj
      dsimp only at hj ⊢
      rw [hD1, ite_eq_right (by omega)]
      by_cases hji : j = i
      · simp only [hji, Function.update_self]
      · rw [Function.update_of_ne hji]
        exact hst.D_none j (by omega)
    · simp only [hD1]
      simp only [lt_self_iff_false, and_false, ↓reduceIte, Function.update_self]
    · intro j hji
      simp only [hD1, Function.update_of_ne hji]
  · simp only [rcv, trySkipped, hD] at h
    have hK := hst.D_key i K hD
    have hi : i ≠ 0 ∧ i ≤ st.iB := by
      constructor <;> by_contra hc <;>
        simp only [hst.D_none i (by omega), reduceCtorEq] at hD
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some,
      Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨m, hm, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, by omega, hK ▸ hm, ⟨hst.w_eq, ?_, ?_⟩, by simp only; omega,
        by simp only [Function.update_self], ?_⟩
    · intro j K' hj
      dsimp only at hj
      by_cases hji : j = i
      · simp only [hji, Function.update_self, reduceCtorEq] at hj
      · rw [Function.update_of_ne hji] at hj
        exact hst.D_key j K' hj
    · intro j hj
      dsimp only at hj ⊢
      by_cases hji : j = i
      · simp only [hji, Function.update_self]
      · rw [Function.update_of_ne hji]
        exact hst.D_none j hj
    · intro j hji
      dsimp only
      rw [Function.update_of_ne hji, ite_eq_right (by omega)]

/-- Let B's state be on the chain from `k`, let `D[i] = K_i` or `i > i_B`, and let
`Dec(K_i, (i, a), e) = m`. Then `FS-Rcv` accepts `(i, e)` with associated data `a`, with
output index `i` and message `m`. -/
theorem exists_rcv_eq_some (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (prg : PRGScheme W (W × Kae))
    {k : W} {st : RecvState W Kae} (hst : OnChain prg k st) {a : AD} {i : ℕ} {e : Cae}
    {m : M} (hk : st.D i = some (chainKey prg k i) ∨ st.iB < i)
    (hd : ae.decrypt (chainKey prg k i) (i, a) e = some m) :
    ∃ st', rcv ae prg st a (i, e) = some (st', i, m) := by
  rcases hr : rcv ae prg st a (i, e) with _ | ⟨st', i', m'⟩
  · exfalso
    rcases hk with hk | hk
    · simp only [rcv, trySkipped, hk, Option.bind_eq_bind, Option.pure_def, Option.bind_some,
        hd] at hr
      exact Option.some_ne_none _ hr
    · simp only [rcv, trySkipped, hst.D_none i (Or.inr hk), Nat.not_le_of_lt hk, ↓reduceIte,
        Option.bind_eq_bind, Option.pure_def, Option.bind_some, Option.bind_eq_none_iff] at hr
      have hG := skip_gen prg (st := { w := st.w, iB := st.iB, D := Function.update st.D i none })
        hst.w_eq hk
      exact Option.some_ne_none _
        (hr m ((congrArg (ae.decrypt · (i, a) e) (congrArg Prod.snd hG)).trans hd))
  · obtain ⟨rfl, -, hd', -⟩ := rcv_some ae prg hst hr
    rw [hd, Option.some.injEq] at hd'
    exact ⟨st', hd' ▸ rfl⟩

/-- B accepts `(i, e)` at an index `i`, and `j ≠ i`. If B had the key of `j` before, then it
has it after: `j > i_B` or `D[j] = K_j`. -/
theorem key_after_rcv (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    {k : W} {st st' : RecvState W Kae} (hst : OnChain prg k st) {a : AD} {i i' j : ℕ} {e : Cae}
    {m' : M} (hr : rcv ae prg st a (i, e) = some (st', i', m')) (hji : j ≠ i)
    (hj : st.iB < j ∨ st.D j = some (chainKey prg k j)) :
    st'.iB < j ∨ st'.D j = some (chainKey prg k j) := by
  obtain ⟨-, -, -, -, hiB, -, hDj⟩ := rcv_some ae prg hst hr
  rw [hDj j hji, hiB]
  rcases hj with h | h
  · by_cases hlt : j < i
    · exact .inr (by rw [ite_eq_left ⟨h, hlt⟩])
    · exact .inl (by omega)
  · refine .inr ?_
    split_ifs
    · rfl
    · exact h

/-! ## The game invariant -/

/-- `FS-Send` from `v_A = (w_A, i_A)`: A moves to `(G(w_A).1, i_A + 1)` and sends
`(i_A + 1, Enc(G(w_A).2, (i_A + 1, a), m))`. -/
theorem send_eq (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    (st : SendState W) (a : AD) (m : M) :
    send ae prg st a m = ({ w := (prg.gen st.w).1, iA := st.iA + 1 },
      (st.iA + 1, ae.encrypt (prg.gen st.w).2 (st.iA + 1, a) m)) :=
  rfl

/-- The invariant of the FS-AEAD game for `fromAEADPRG ae prg` with key `k`. Write `w_j` and
`K_j` for the seeds and keys of the chain from `k`.
- A is at `w_{i_A}`, and its counter is the game counter `i_A`.
- B's state is on the chain from `k`.
- Every record `(i, a, m, e)` in `trans` has `1 ≤ i ≤ i_A` and
  `e = (i, Enc(K_i, (i, a), m))`.
- Only a corrupted A has compromised indices.
- While `win` is false, B has the key of every record: `i > i_B` or `D[i] = K_i`. Every
  index `j` with `i_A < j ≤ i_B` has `D[j] = K_j`, or A is corrupted and `j` is not
  compromised. In the second case an injection consumed `j`, so `record` drops A's later
  ciphertext at `j`. -/
structure GameInv (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    (k : W) (st : GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) : Prop where
  vA_w : st.vA.w = chainState prg k st.iA
  vA_iA : st.vA.iA = st.iA
  vB : OnChain prg k st.vB
  trans_honest : ∀ r ∈ st.trans, 1 ≤ r.1 ∧ r.1 ≤ st.iA ∧
    r.2.2.2 = (r.1, ae.encrypt (chainKey prg k r.1) (r.1, r.2.1) r.2.2.1)
  comp_corrA : ∀ j, st.comp j = true → st.corrA = true
  trans_key : st.win = false → ∀ r ∈ st.trans,
    st.vB.iB < r.1 ∨ st.vB.D r.1 = some (chainKey prg k r.1)
  future_key : st.win = false → ∀ j, st.iA < j → j ≤ st.vB.iB →
    st.vB.D j = some (chainKey prg k j) ∨ (st.corrA = true ∧ st.comp j = false)

variable {ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae} {prg : PRGScheme W (W × Kae)} {k : W}
  {st : GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae)}

/-- The initial game state satisfies the invariant. -/
theorem gameInv_init : GameInv ae prg k (.init (fromAEADPRG ae prg) k) where
  vA_w := rfl
  vA_iA := rfl
  vB := ⟨rfl, fun _ _ h => (nomatch h), fun _ _ => rfl⟩
  trans_honest := fun _ h => (nomatch h)
  comp_corrA := fun _ h => (nomatch h)
  trans_key := fun _ _ h => (nomatch h)
  future_key := fun _ _ h₁ h₂ => absurd (Nat.lt_of_lt_of_le h₁ h₂) (Nat.lt_irrefl 0)

/-- A sends. `record` stores the ciphertext unless A is corrupted and its index is not in
`comp`. -/
theorem gameInv_send (hinv : GameInv ae prg k st) (isChall : Bool) (a : AD) (m : M) :
    GameInv ae prg k ({ st with vA := (send ae prg st.vA a m).1, iA := st.iA + 1 }.record
      isChall a m (send ae prg st.vA a m).2) := by
  have hG : prg.gen st.vA.w = (chainState prg k (st.iA + 1), chainKey prg k (st.iA + 1)) := by
    rw [hinv.vA_w, chainState_succ]
    rfl
  rw [send_eq, hG, hinv.vA_iA]
  unfold GameState.record
  by_cases hskip : st.corrA = true ∧ st.comp (st.iA + 1) = false
  · rw [ite_eq_left (by simp only [hskip, Bool.not_false, Bool.and_self])]
    exact { vA_w := rfl, vA_iA := rfl, vB := hinv.vB
            trans_honest := fun r hr => by
              obtain ⟨h1, h2, h3⟩ := hinv.trans_honest r hr
              exact ⟨h1, by simp only; omega, h3⟩
            comp_corrA := hinv.comp_corrA, trans_key := hinv.trans_key
            future_key := fun hw j hj => hinv.future_key hw j (by simp only at hj; omega) }
  · rw [ite_eq_right (by simpa only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        not_and, Bool.not_eq_false] using hskip)]
    refine { vA_w := rfl, vA_iA := rfl, vB := hinv.vB, trans_honest := ?_
             comp_corrA := hinv.comp_corrA, trans_key := ?_
             future_key := fun hw j hj => hinv.future_key hw j (by simp only at hj; omega) }
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨h1, h2, h3⟩ := hinv.trans_honest r hr
        exact ⟨h1, by simp only; omega, h3⟩
      · obtain rfl := List.mem_singleton.mp hr
        exact ⟨Nat.succ_pos _, le_rfl, rfl⟩
    · intro hw r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hinv.trans_key hw r hr
      · obtain rfl := List.mem_singleton.mp hr
        by_cases hlt : st.vB.iB < st.iA + 1
        · exact Or.inl hlt
        · rcases hinv.future_key hw (st.iA + 1) (by omega) (by omega) with h | h
          · exact Or.inr h
          · exact absurd h hskip

/-- `O-Corr-A` keeps the invariant. -/
theorem gameInv_corrA (hinv : GameInv ae prg k st) :
    GameInv ae prg k { st with
      corrA := true
      comp := (if st.corrA then st.comp else fun i => decide (st.iA < i)) } := by
  by_cases hc : st.corrA = true
  · rw [ite_eq_left hc]
    exact { vA_w := hinv.vA_w, vA_iA := hinv.vA_iA, vB := hinv.vB
            trans_honest := hinv.trans_honest, comp_corrA := fun _ _ => rfl
            trans_key := hinv.trans_key
            future_key := fun hw j h₁ h₂ => by
              rcases hinv.future_key hw j h₁ h₂ with h | ⟨-, h⟩
              · exact .inl h
              · exact .inr ⟨rfl, h⟩ }
  · rw [ite_eq_right hc]
    exact { vA_w := hinv.vA_w, vA_iA := hinv.vA_iA, vB := hinv.vB
            trans_honest := hinv.trans_honest, comp_corrA := fun _ _ => rfl
            trans_key := hinv.trans_key
            future_key := fun hw j h₁ h₂ => by
              rcases hinv.future_key hw j h₁ h₂ with h | ⟨h, -⟩
              · exact .inl h
              · exact absurd h hc }

/-- B accepts `(i, e)` and the game runs `delete(i)`, with a new `win` flag `w'`. Let `w'` be
false only if `win` was false and either `i ≤ i_A` or A is corrupted. Then the invariant
holds after the step. -/
theorem gameInv_rcv (hinv : GameInv ae prg k st) {a : AD} {i i' : ℕ} {e : Cae}
    {vB' : RecvState W Kae} {m' : M} (hr : rcv ae prg st.vB a (i, e) = some (vB', i', m'))
    (w' : Bool) (hw : w' = false → st.win = false ∧ (i ≤ st.iA ∨ st.corrA = true)) :
    GameInv ae prg k ({ st with vB := vB', win := w' }.delete i') := by
  obtain ⟨hii, -, -, hon, hiB, hDi, hDj⟩ := rcv_some ae prg hinv.vB hr
  subst i'
  refine { vA_w := hinv.vA_w, vA_iA := hinv.vA_iA, vB := hon, trans_honest := ?_
           comp_corrA := ?_, trans_key := ?_, future_key := ?_ }
  · intro r hr
    exact hinv.trans_honest r (List.mem_filter.mp hr).1
  · intro j hj
    simp only [GameState.delete, Bool.and_eq_true, bne_iff_ne, ne_eq] at hj
    exact hinv.comp_corrA j hj.2
  · intro hw' r hmem
    simp only [GameState.delete, List.mem_filter, decide_eq_true_eq] at hmem hw'
    exact key_after_rcv ae prg hinv.vB hr hmem.2 (hinv.trans_key (hw hw').1 r hmem.1)
  · intro hw' j hj₁ hj₂
    simp only [GameState.delete] at hw' hj₁ hj₂ ⊢
    rw [hiB] at hj₂
    obtain ⟨hwin, hcase⟩ := hw hw'
    by_cases hji : j = i
    · subst hji
      refine .inr ⟨hcase.resolve_left (by omega), by simp only [bne_self_eq_false, Bool.false_and]⟩
    · rw [hDj j hji]
      split_ifs with h
      · exact .inl rfl
      · rcases hinv.future_key hwin j hj₁ (by omega) with h' | ⟨hc, h'⟩
        · exact .inl h'
        · exact .inr ⟨hc, by simp only [h', Bool.and_false]⟩

/-- Setting `win` keeps the invariant. -/
theorem gameInv_win (hinv : GameInv ae prg k st) : GameInv ae prg k { st with win := true } :=
  ⟨hinv.vA_w, hinv.vA_iA, hinv.vB, hinv.trans_honest, hinv.comp_corrA, fun h => (nomatch h),
    fun h => (nomatch h)⟩

section Oracles

variable [DecidableEq AD] [DecidableEq M] [DecidableEq Cae]

/-- Every oracle of the game for `fromAEADPRG ae prg` keeps the invariant. -/
theorem gameInv_step (hinv : GameInv ae prg k st) (len : M → ℕ) (b : Bool)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain) {z}
    (hz : z ∈ support ((fsaeadSecurityImpl (fromAEADPRG ae prg) len b t).run st)) :
    GameInv ae prg k z.2 := by
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩)
  · change z ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hz
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hz
    obtain ⟨x, rfl⟩ := hz
    exact hinv
  · change z ∈ support ((oracleTransmitA (fromAEADPRG ae prg) (a, m)).run st) at hz
    simp only [oracleTransmitA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hinv
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact gameInv_send hinv false a m
  · change z ∈ support ((oracleChallA (fromAEADPRG ae prg) len b (a, m₀, m₁)).run st) at hz
    simp only [oracleChallA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hinv
    all_goals
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact gameInv_send hinv true a _
  · change z ∈ support ((oracleCorrA _ _ _ _ _ ()).run st) at hz
    simp only [oracleCorrA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hinv
    all_goals
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      have := gameInv_corrA hinv
    · rwa [ite_eq_left ‹_›] at this
    · rwa [ite_eq_right ‹_›] at this
  · change z ∈ support ((oracleCorrB _ _ _ _ _ ()).run st) at hz
    simp only [oracleCorrB, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hinv
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hinv.vA_w, hinv.vA_iA, hinv.vB, hinv.trans_honest, hinv.comp_corrA,
        hinv.trans_key, hinv.future_key⟩
  · change z ∈ support ((oracleDeliverB (fromAEADPRG ae prg) (a, c)).run st) at hz
    simp only [oracleDeliverB, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hinv
    rcases hf : st.findTrans a c with _ | ⟨i, a', m, c'⟩
    · simp only [hf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hinv
    obtain ⟨hmem, rfl, rfl⟩ := GameState.findTrans_spec hf
    obtain ⟨-, hiA, hc⟩ := hinv.trans_honest _ hmem
    simp only at hiA hc
    subst hc
    rcases hr : rcv ae prg st.vB a' (i, ae.encrypt (chainKey prg k i) (i, a') m)
      with _ | ⟨vB, i', m'⟩
    · simp only [hf, fromAEADPRG, hr, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact gameInv_win hinv
    · obtain ⟨hii, -⟩ := rcv_some ae prg hinv.vB hr
      subst hii
      simp only [hf, fromAEADPRG, hr, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact gameInv_rcv hinv hr _ fun hw => ⟨by simp_all only [Bool.not_eq_true, decide_true,
          Bool.true_and, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
          decide_eq_true_eq], .inl hiA⟩
  · change z ∈ support ((oracleInjectB (fromAEADPRG ae prg) (a, c)).run st) at hz
    simp only [oracleInjectB, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hinv
    obtain ⟨j, e⟩ := c
    rcases hr : rcv ae prg st.vB a (j, e) with _ | ⟨vB, i', m'⟩
    · simp only [fromAEADPRG, hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hinv
    · simp only [fromAEADPRG, hr, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine gameInv_rcv hinv hr _ fun hw => ?_
      simp only [Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hw
      exact ⟨hw.1, .inr (hinv.comp_corrA _ hw.2)⟩

/-- Let `st` be reachable in the game for `fromAEADPRG ae prg` with key `k`. Then `st`
satisfies the invariant. -/
theorem gameInv_of_reachable {len : M → ℕ} {b : Bool}
    (h : Reachable (fromAEADPRG ae prg) len b k st) : GameInv ae prg k st := by
  induction h with
  | init => exact gameInv_init
  | step t _ hz ih => exact gameInv_step ih len b t hz

/-- Let `ae` be correct, and let `st` satisfy the invariant with `win = false`. Then
`O-Deliver-B` keeps `win = false`. If its guards pass, B receives the record that
`findTrans` returns, with the recorded index and message. -/
theorem deliver_win_false (hae : ae.Correct) (hinv : GameInv ae prg k st)
    (hw : st.win = false) (q : AD × (ℕ × Cae)) {z}
    (hz : z ∈ support ((oracleDeliverB (fromAEADPRG ae prg) q).run st)) :
    z.2.win = false := by
  obtain ⟨a, c⟩ := q
  simp only [oracleDeliverB, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  rcases hf : st.findTrans a c with _ | ⟨i, a', m, c'⟩
  · simp only [hf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  obtain ⟨hmem, rfl, rfl⟩ := GameState.findTrans_spec hf
  obtain ⟨-, -, hc⟩ := hinv.trans_honest _ hmem
  simp only at hc
  subst hc
  obtain ⟨vB, hr⟩ := exists_rcv_eq_some ae prg hinv.vB (hinv.trans_key hw _ hmem).symm
    (hae (chainKey prg k i) (i, a') m)
  simp only [hf, fromAEADPRG, hr, StateT.run_bind, StateT.run_set, StateT.run_pure,
    pure_bind, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp only [GameState.delete, hw, decide_true, Bool.and_self, Bool.not_true, Bool.or_self, ne_eq,
      decide_not]

end Oracles

/-! ## Honest delivery -/

/-- A sends the messages `(a, m)` in order. -/
def sendAll (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    (st : SendState W) : List (AD × M) → List (ℕ × Cae)
  | [] => []
  | (a, m) :: ms => let (st', c) := send ae prg st a m; c :: sendAll ae prg st' ms

/-- B receives the ciphertexts `(a, c)` in order. It keeps its state after a rejection and
records `none` for it. -/
def rcvAll (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    (st : RecvState W Kae) : List (AD × (ℕ × Cae)) → List (Option (ℕ × M)) × RecvState W Kae
  | [] => ([], st)
  | (a, c) :: cs =>
    match rcv ae prg st a c with
    | none => let r := rcvAll ae prg st cs; (none :: r.1, r.2)
    | some (st', i, m) => let r := rcvAll ae prg st' cs; (some (i, m) :: r.1, r.2)

/-- Let A be at `(w_n, n)` on the chain from `k`, and let A send `(a_1, m_1), …, (a_l, m_l)`.
Then A's `j`-th ciphertext is `(n + j, Enc(K_{n+j}, (n + j, a_j), m_j))`. -/
theorem sendAll_eq (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    {k : W} (msgs : List (AD × M)) {st : SendState W} (hst : st.w = chainState prg k st.iA) :
    sendAll ae prg st msgs = msgs.mapIdx fun j am =>
      (st.iA + j + 1, ae.encrypt (chainKey prg k (st.iA + j + 1)) (st.iA + j + 1, am.1) am.2) := by
  induction msgs generalizing st with
  | nil => rfl
  | cons am ms ih =>
    obtain ⟨a, m⟩ := am
    have hG : prg.gen st.w = (chainState prg k (st.iA + 1), chainKey prg k (st.iA + 1)) := by
      rw [hst, chainState_succ]
      rfl
    rw [List.mapIdx_cons]
    simp only [sendAll, send_eq, hG]
    rw [ih rfl]
    dsimp only
    congr 2
    funext j am
    rw [show st.iA + 1 + j = st.iA + (j + 1) by omega]

/-- Let `ae` be correct, let B's state be on the chain from `k`, and let B have the key of
every index `j` in the list: `j > i_B` or `D[j] = K_j`. Let the indices be distinct. Then B
receives each `(a, (j, Enc(K_j, (j, a), m)))` of the list with output `(j, m)`, in any
order. -/
theorem rcvAll_honest (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (prg : PRGScheme W (W × Kae)) (hae : ae.Correct) {k : W} (del : List (ℕ × AD × M))
    {st : RecvState W Kae} (hst : OnChain prg k st) (hnd : (del.map (·.1)).Nodup)
    (hkey : ∀ x ∈ del, st.iB < x.1 ∨ st.D x.1 = some (chainKey prg k x.1)) :
    (rcvAll ae prg st (del.map fun x =>
      (x.2.1, (x.1, ae.encrypt (chainKey prg k x.1) (x.1, x.2.1) x.2.2)))).1 =
      del.map fun x => some (x.1, x.2.2) := by
  induction del generalizing st with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨i, a, m⟩ := x
    obtain ⟨st', hr⟩ := exists_rcv_eq_some ae prg hst (hkey _ List.mem_cons_self).symm
      (hae (chainKey prg k i) (i, a) m)
    simp only [List.map_cons, rcvAll, hr, List.cons.injEq, true_and]
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    refine ih (rcv_some ae prg hst hr).2.2.2.1 hnd.2 fun y hy => ?_
    exact key_after_rcv ae prg hst hr (fun h => hnd.1 ⟨y, hy, h⟩)
      (hkey y (List.mem_cons_of_mem _ hy))

/-- Let `ae` be correct, and let `del` be a list of `(j, a, m)` with distinct indices
`j ≥ 1`. Let B start from `Init-B(k)` and receive `(j, Enc(K_j, (j, a), m))` with associated
data `a` for each entry, in the order of `del`. Then B outputs `(j, m)` for each entry. By
`sendAll_eq`, A's `j`-th ciphertext from `Init-A(k)` has this form. -/
-- ANCHOR: rcvAll_honest_initR
theorem rcvAll_honest_initR (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (prg : PRGScheme W (W × Kae)) (hae : ae.Correct) (k : W) (del : List (ℕ × AD × M))
    (hnd : (del.map (·.1)).Nodup) (hpos : ∀ x ∈ del, 1 ≤ x.1) :
    (rcvAll ae prg (initR k) (del.map fun x =>
      (x.2.1, (x.1, ae.encrypt (chainKey prg k x.1) (x.1, x.2.1) x.2.2)))).1 =
      del.map fun x => some (x.1, x.2.2)
-- ANCHOR_END: rcvAll_honest_initR
  := rcvAll_honest ae prg hae del ⟨rfl, fun _ _ h => (nomatch h), fun _ _ => rfl⟩ hnd
    fun x hx => .inl (hpos x hx)

end FromAEADPRG

open FromAEADPRG

/-- Let `ae` be a correct AEAD scheme. Then `fromAEADPRG ae prg` satisfies
`NoFirstDeliverWin`: in the FS-AEAD game, `O-Deliver-B` never changes `win` from false to
true. -/
-- ANCHOR: fromAEADPRG_noFirstDeliverWin
theorem fromAEADPRG_noFirstDeliverWin {Cae AD M : Type} [DecidableEq AD] [DecidableEq M]
    [DecidableEq Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (prg : PRGScheme W (W × Kae)) (hae : ae.Correct) (len : M → ℕ) :
    (fromAEADPRG ae prg).NoFirstDeliverWin len
-- ANCHOR_END: fromAEADPRG_noFirstDeliverWin
  := fun _ _ _ hst hw _ _ hz => deliver_win_false hae (gameInv_of_reachable hst) hw _ hz

namespace FromAEADPRG.Toy

/-! ## Sanity checks on a toy instance

`W = Kae = ℕ` and `G(w) = (w + 1, w)`, so from `w₀ = 0` the key of position `j` is
`K_j = j - 1`, and all keys differ. The toy AEAD ciphertext carries the key, the header and
the message. `Dec` returns the message only if the key and the header match, so a wrong
derived or cached key fails. -/

/-- The toy AEAD ciphertext: key, header `(i, a)` and message. -/
abbrev ToyC := ℕ × (ℕ × ℕ) × ℕ

/-- The toy AEAD, which checks the key and the header. -/
def ae : AEADScheme ProbComp ℕ (ℕ × ℕ) ℕ ToyC where
  keygen := pure 0
  encrypt K h m := (K, h, m)
  decrypt K h e := if e.1 = K ∧ e.2.1 = h then some e.2.2 else none

/-- The toy PRG `G(w) = (w + 1, w)`. -/
def prg : PRGScheme ℕ (ℕ × ℕ) := ⟨fun w => (w + 1, w)⟩

/-- The toy FS-AEAD scheme, with `AD = M = ℕ`. -/
abbrev fs := fromAEADPRG ae prg

/-- `FromAEADPRG.sendAll` for the toy scheme. -/
abbrev sendAll := FromAEADPRG.sendAll ae prg

/-- `FromAEADPRG.rcvAll` for the toy scheme. -/
abbrev rcvAll := FromAEADPRG.rcvAll ae prg

/-- A's four ciphertexts from key 0: message `100 + j - 1` with associated data `10 + j - 1`
at index `j`. -/
def cts : List (ℕ × ToyC) := sendAll (fs.initS 0) [(10, 100), (11, 101), (12, 102), (13, 103)]

/-- A's `j`-th ciphertext, with its associated data. -/
def c (j : ℕ) : ℕ × ℕ × ToyC := (9 + j, cts[j - 1]!)

/-- The initial receiver state. -/
abbrev B₀ : RecvState ℕ ℕ := fs.initR 0

/-- A uses the key `K_j = j - 1` and the header `(j, a)`. -/
example : cts = [(1, 0, (1, 10), 100), (2, 1, (2, 11), 101), (3, 2, (3, 12), 102),
    (4, 3, (4, 13), 103)] := by decide

/-- Out-of-order delivery `4, 2, 1, 3`, then a replay of each, which B rejects. -/
example : (rcvAll B₀ [c 4, c 2, c 1, c 3, c 4, c 2, c 1, c 3]).1 =
    [some (4, 103), some (2, 101), some (1, 100), some (3, 102), none, none, none, none] := by
  decide

/-- Correction 1: after B receives message 4 first, `D[j] = K_j = j - 1` for the skipped
indices `j = 1, 2, 3`. -/
example : let st := (rcvAll B₀ [c 4]).2
    st.w = 4 ∧ st.iB = 4 ∧ st.D 0 = none ∧ st.D 1 = some 0 ∧ st.D 2 = some 1 ∧
      st.D 3 = some 2 ∧ st.D 4 = none ∧ st.D 5 = none := by decide

/-- After all four, the entries 0 to 7 of `D` are empty again. -/
example : let st := (rcvAll B₀ [c 4, c 2, c 1, c 3]).2
    st.w = 4 ∧ st.iB = 4 ∧ ∀ j < 8, st.D j = none := by decide

/-- A failed `Dec` under a key in `D` keeps the key, and the honest ciphertext at that index
is then accepted. -/
example : (rcvAll B₀ [c 2, (10, 1, 7, (1, 10), 100), c 1]).1 =
    [some (2, 101), none, some (1, 100)] := by decide

/-- A failed `Dec` after a forward skip rolls the skip back, and both the skipped and the
target honest ciphertexts are then accepted. -/
example : (rcvAll B₀ [(11, 2, 7, (2, 11), 101), c 2, c 1]).1 =
    [none, some (2, 101), some (1, 100)] := by decide

/-- A changed associated data and a changed outer index are both rejected. Both use the
key of their index, so only the AEAD header `(i, a)` differs. -/
example : (rcvAll B₀ [(99, (c 1).2), (10, 2, 1, (1, 10), 100), c 1]).1 =
    [none, none, some (1, 100)] := by decide

/-- Correction 2: B rejects a miss at index 0 and at an index up to `i_B`, even under the
next chain key `K_{i_B + 1}`. The second conjunct is the attack trace of correction 2:
B is at `w₁`, and the adversary injects at index 0 under `K₂ = 1`. -/
example : (rcvAll B₀ [(10, 0, 0, (0, 10), 7)]).1 = [none] ∧
    (rcvAll B₀ [c 1, (10, 0, 1, (0, 10), 7), (10, 1, 1, (1, 10), 7)]).1 =
      [some (1, 100), none, none] ∧
    (rcvAll B₀ [c 2, c 1, (10, 1, 2, (1, 10), 7)]).1 =
      [some (2, 101), some (1, 100), none] := by decide

end FromAEADPRG.Toy

end FSAEADScheme
