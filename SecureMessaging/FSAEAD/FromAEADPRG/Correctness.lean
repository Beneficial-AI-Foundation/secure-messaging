/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.Correctness
public import SecureMessaging.FSAEAD.FromAEADPRG.Construction

/-!
# FS-AEAD from AEAD and PRG — Correctness

Correctness of the FS-AEAD construction of [ACD19, Figure 6], built from an AEAD scheme
`ae` and a PRG `G : W → W × K`. A and B derive their keys from the PRG chain that starts at
the shared key `k`:
```text
w_0 = k,   (w_j, K_j) = G(w_{j-1})   for j ≥ 1
```
A's `j`-th ciphertext for associated data `a` and message `m` is `(j, Enc(K_j, (j, a), m))`
(`sendAll_eq`).

Let the AEAD scheme be correct. Then:
- `fromAEADPRG_correct`: the construction is correct (`FSAEADScheme.Correct`).
- `fromAEADPRG_securityExp_eq_noDeliverWin`: its security experiment equals the experiment
  without the delivery check (`FSAEADScheme.securityExpNoDeliverWin`).
- `rcvAll_honest_initR`: without an adversary, B outputs `(j, m)` for every
  `(j, Enc(K_j, (j, a), m))` with `j ≥ 1`, in any order and each `j` at most once.

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — §4.2.2, Figure 6.
-/

@[expose] public section

namespace FSAEADScheme

variable {W Kae : Type}

namespace FromAEADPRG

/-! ## The chain -/

/-- The seed `w_j` of the chain from `k`, with generator `G_j` at position `j`:
```text
w_0 = k,   (w_j, K_j) = G_j(w_{j-1})   for j ≥ 1
``` -/
def chainState (G : ℕ → W → W × Kae) (k : W) : ℕ → W
  | 0 => k
  | j + 1 => (G (j + 1) (chainState G k j)).1

/-- The key `K_j` of the chain from `k`, for `j ≥ 1`:
```text
(w_j, K_j) = G_j(w_{j-1})
```
The chain has no key at position 0. `chainKey G k 0` is a junk value. -/
def chainKey (G : ℕ → W → W × Kae) (k : W) (j : ℕ) : Kae :=
  (G j (chainState G k (j - 1))).2

/-- Let `w_0, w_1, …` be the chain from `k`. Then `w_0 = k`. -/
@[simp]
theorem chainState_zero (G : ℕ → W → W × Kae) (k : W) : chainState G k 0 = k :=
  rfl

/-- Let `w_0, w_1, …` and `K_1, K_2, …` be the chain from `k`. Then for every `j`,
`G_{j+1}(w_j) = (w_{j+1}, K_{j+1})`. -/
theorem gen_chainState (G : ℕ → W → W × Kae) (k : W) (j : ℕ) :
    G (j + 1) (chainState G k j) = (chainState G k (j + 1), chainKey G k (j + 1)) :=
  rfl

/-! ## Skipping -/

/-- Let `w_B = w_{i_B}` on the chain from `k`, and let `(w', i', D')` be the state after `n`
steps of `skip` from `(w_B, i_B, D)`. Then `w' = w_{i_B + n}`. -/
theorem skipSteps_w (G : ℕ → W → W × Kae) {k : W} (n : ℕ) (st : RecvState W Kae)
    (hw : st.w = chainState G k st.iB) :
    (skipSteps G n st).w = chainState G k (st.iB + n) := by
  induction n generalizing st with
  | zero => exact hw
  | succ n ih =>
    rw [skipSteps, ih _ (by rw [hw]; rfl)]
    dsimp only
    congr 1
    omega

/-- Let `(w', i', D')` be the state after `n` steps of `skip` from `(w_B, i_B, D)`. Then
`i' = i_B + n`. -/
theorem skipSteps_iB (G : ℕ → W → W × Kae) (n : ℕ) (st : RecvState W Kae) :
    (skipSteps G n st).iB = st.iB + n := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => simp only [skipSteps, ih]; omega

/-- Let `w_B = w_{i_B}` on the chain from `k`, with keys `K_1, K_2, …`, and let
`(w', i', D')` be the state after `n` steps of `skip` from `(w_B, i_B, D)`. Then for
every `j`:
```text
D'[j] = K_j    if i_B < j ≤ i_B + n
D'[j] = D[j]   otherwise
``` -/
theorem skipSteps_D (G : ℕ → W → W × Kae) {k : W} (n : ℕ) (st : RecvState W Kae)
    (hw : st.w = chainState G k st.iB) (j : ℕ) :
    (skipSteps G n st).D j =
      if st.iB < j ∧ j ≤ st.iB + n then some (chainKey G k j) else st.D j := by
  induction n generalizing st with
  | zero => simp only [skipSteps]; split_ifs <;> first | rfl | omega
  | succ n ih =>
    rw [skipSteps, ih _ (by rw [hw]; rfl)]
    simp only [Function.update_apply]
    split_ifs <;> try first | rfl | omega
    subst j
    rw [hw]
    rfl

/-- Let `w_B = w_{i_B}` on the chain from `k`, let `i_B < u`, and let `(w', i', D')` be the
result of `skip(u)` on `(w_B, i_B, D)`. Then `i' = u - 1` and `w' = w_{u-1}`. -/
theorem skip_w_iB (G : ℕ → W → W × Kae) {k : W} (u : ℕ) (st : RecvState W Kae)
    (hw : st.w = chainState G k st.iB) (h : st.iB < u) :
    (skip G u st).w = chainState G k (u - 1) ∧ (skip G u st).iB = u - 1 := by
  refine ⟨?_, ?_⟩
  · rw [skip, skipSteps_w G _ st hw]
    congr 1
    omega
  · simp only [skip, skipSteps_iB]
    omega

/-! ## Receiving -/

/-- B's state is on the chain from `k`: `w_B = w_{i_B}`, every entry of `D` is `⊥` or the
key `K_j` of its index, and `D[j] = ⊥` for `j = 0` and for `j > i_B`. -/
structure OnChain (G : ℕ → W → W × Kae) (k : W) (st : RecvState W Kae) : Prop where
  w_eq : st.w = chainState G k st.iB
  D_key : ∀ j K, st.D j = some K → K = chainKey G k j
  D_none : ∀ j, (j = 0 ∨ st.iB < j) → st.D j = none

/-- Let `w_B = w_{i_B}` on the chain from `k`, and let `i_B < i`. Then one step of `G_i`
after `skip(i)` gives `(w_i, K_i)`. -/
theorem skip_gen (G : ℕ → W → W × Kae) {k : W} {st : RecvState W Kae} {i : ℕ}
    (hw : st.w = chainState G k st.iB) (hlt : st.iB < i) :
    G i (skip G i st).w = (chainState G k i, chainKey G k i) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [(skip_w_iB G _ st hw hlt).1, Nat.add_sub_cancel]
  rfl

/-- `rcvKey` rejects index `i` exactly when `D[i] = ⊥` and `i ≤ i_B`: B has used index `i`. -/
theorem rcvKey_eq_none_iff (G : ℕ → W → W × Kae) (st : RecvState W Kae) (i : ℕ) :
    rcvKey G st i = none ↔ st.D i = none ∧ i ≤ st.iB := by
  rcases hD : st.D i with _ | K
  · by_cases hle : i ≤ st.iB
    · simp only [rcvKey, trySkipped, hD, hle, ↓reduceIte, Option.bind_eq_bind, Option.bind_none,
        and_self]
    · simp only [rcvKey, trySkipped, hD, hle, ↓reduceIte, and_false, iff_false]
      exact Option.some_ne_none _
  · simp only [rcvKey, trySkipped, hD, reduceCtorEq, false_and]

/-- Let B's state `v_B = (w_B, i_B, D)` be on the chain from `k`, and let `rcvKey` find the key
`K` of index `i`, with new state `v_B'`. Then:
- `K = K_i` and `i ≥ 1`;
- `v_B'` is on the chain from `k`, with `i_B' = max(i_B, i)`;
- `D'[i] = ⊥`, and for `j ≠ i`, `D'[j] = K_j` if `i_B < j < i`, and `D'[j] = D[j]`
  otherwise. -/
theorem rcvKey_some (G : ℕ → W → W × Kae) {k : W} {st st' : RecvState W Kae}
    (hst : OnChain G k st) {i : ℕ} {K : Kae} (h : rcvKey G st i = some (st', K)) :
    K = chainKey G k i ∧ 1 ≤ i ∧ OnChain G k st' ∧ st'.iB = max st.iB i ∧ st'.D i = none ∧
      ∀ j, j ≠ i → st'.D j =
        if st.iB < j ∧ j < i then some (chainKey G k j) else st.D j := by
  rcases hD : st.D i with _ | K'
  · simp only [rcvKey, trySkipped, hD] at h
    have hlt : st.iB < i := by
      by_contra hle
      simp only [Nat.le_of_not_lt hle, ↓reduceIte, Option.bind_eq_bind, Option.bind_none,
        reduceCtorEq] at h
    simp only [Nat.not_le_of_lt hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hG := skip_gen G (st := { w := st.w, iB := st.iB, D := Function.update st.D i none })
      hst.w_eq hlt
    have hD1 : ∀ j, (skip G i { w := st.w, iB := st.iB, D := Function.update st.D i none }).D j
        = if st.iB < j ∧ j < i then some (chainKey G k j)
          else Function.update st.D i none j := by
      intro j
      unfold skip
      rw [skipSteps_D G _ { w := st.w, iB := st.iB, D := Function.update st.D i none } hst.w_eq]
      dsimp only
      split_ifs with c1 c2 c2 <;> first | rfl | omega
    refine ⟨by rw [hG], by omega, ⟨congrArg Prod.fst hG, ?_, ?_⟩, by simp only; omega,
      ?_, ?_⟩
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
  · simp only [rcvKey, trySkipped, hD, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hK := hst.D_key i K' hD
    have hi : i ≠ 0 ∧ i ≤ st.iB := by
      constructor <;> by_contra hc <;>
        simp only [hst.D_none i (by omega), reduceCtorEq] at hD
    refine ⟨hK, by omega, ⟨hst.w_eq, ?_, ?_⟩, by simp only; omega,
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

variable {Cae AD M : Type}

/-- Let `FS-Rcv` accept `(i, e)` with output `(v_B', i', m')`. Then `rcvKey` finds a key `K` of
index `i` with new state `v_B'`, `i' = i`, and `m' = Dec(K, (i, a), e)`. -/
theorem rcvKey_of_rcv_eq_some (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) {st st' : RecvState W Kae} {a : AD} {i i' : ℕ} {e : Cae} {m' : M}
    (h : rcv ae G st a (i, e) = some (st', i', m')) :
    ∃ K, rcvKey G st i = some (st', K) ∧ i' = i ∧ ae.decrypt K (i, a) e = some m' := by
  simp only [rcv, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨st'', K⟩, hk, m, hm, rfl, rfl, rfl⟩ := h
  exact ⟨K, hk, rfl, hm⟩

/-- Let B's state `v_B = (w_B, i_B, D)` be on the chain from `k`, and let `FS-Rcv` accept
`(i, e)` with associated data `a`, with output `(v_B', i', m')`. Then:
- `i' = i ≥ 1`, and `m' = Dec(K_i, (i, a), e)`;
- `v_B'` is on the chain from `k`, with `i_B' = max(i_B, i)`;
- `D'[i] = ⊥`, and for `j ≠ i`, `D'[j] = K_j` if `i_B < j < i`, and `D'[j] = D[j]`
  otherwise. -/
theorem rcv_some (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    {k : W} {st st' : RecvState W Kae} (hst : OnChain G k st) {a : AD} {i i' : ℕ}
    {e : Cae} {m' : M} (h : rcv ae G st a (i, e) = some (st', i', m')) :
    i' = i ∧ 1 ≤ i ∧ ae.decrypt (chainKey G k i) (i, a) e = some m' ∧
      OnChain G k st' ∧ st'.iB = max st.iB i ∧ st'.D i = none ∧
      ∀ j, j ≠ i → st'.D j =
        if st.iB < j ∧ j < i then some (chainKey G k j) else st.D j := by
  obtain ⟨K, hk, rfl, hm⟩ := rcvKey_of_rcv_eq_some ae G h
  obtain ⟨rfl, h1, h2⟩ := rcvKey_some G hst hk
  exact ⟨rfl, h1, hm, h2⟩

/-- Let B's state be on the chain from `k`, let `D[i] = K_i` or `i > i_B`, and let
`Dec(K_i, (i, a), e) = m`. Then `FS-Rcv` accepts `(i, e)` with associated data `a`, with
output index `i` and message `m`. -/
theorem exists_rcv_eq_some (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae)
    {k : W} {st : RecvState W Kae} (hst : OnChain G k st) {a : AD} {i : ℕ} {e : Cae}
    {m : M} (hk : st.D i = some (chainKey G k i) ∨ st.iB < i)
    (hd : ae.decrypt (chainKey G k i) (i, a) e = some m) :
    ∃ st', rcv ae G st a (i, e) = some (st', i, m) := by
  rcases hr : rcv ae G st a (i, e) with _ | ⟨st', i', m'⟩
  · exfalso
    rcases hk with hk | hk
    · simp only [rcv, rcvKey, trySkipped, hk, Option.bind_eq_bind, Option.pure_def,
        Option.bind_some, hd] at hr
      exact Option.some_ne_none _ hr
    · simp only [rcv, rcvKey, trySkipped, hst.D_none i (Or.inr hk), Nat.not_le_of_lt hk,
        ↓reduceIte, Option.bind_eq_bind, Option.pure_def, Option.bind_some,
        Option.bind_eq_none_iff] at hr
      have hG := skip_gen G (st := { w := st.w, iB := st.iB, D := Function.update st.D i none })
        hst.w_eq hk
      exact Option.some_ne_none _
        (hr m ((congrArg (ae.decrypt · (i, a) e) (congrArg Prod.snd hG)).trans hd))
  · obtain ⟨rfl, -, hd', -⟩ := rcv_some ae G hst hr
    rw [hd, Option.some.injEq] at hd'
    exact ⟨st', hd' ▸ rfl⟩

/-- B accepts `(i, e)` at an index `i`, and `j ≠ i`. If B had the key of `j` before, then it
has it after: `j > i_B` or `D[j] = K_j`. -/
theorem key_after_rcv (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    {k : W} {st st' : RecvState W Kae} (hst : OnChain G k st) {a : AD} {i i' j : ℕ} {e : Cae}
    {m' : M} (hr : rcv ae G st a (i, e) = some (st', i', m')) (hji : j ≠ i)
    (hj : st.iB < j ∨ st.D j = some (chainKey G k j)) :
    st'.iB < j ∨ st'.D j = some (chainKey G k j) := by
  obtain ⟨-, -, -, -, hiB, -, hDj⟩ := rcv_some ae G hst hr
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

/-- Let `v_A = (w_A, i_A)` and `(w', K) = G_{i_A + 1}(w_A)`. Then `FS-Send` moves A to
`(w', i_A + 1)` and sends `(i_A + 1, Enc(K, (i_A + 1, a), m))`. -/
theorem send_eq (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (st : SendState W) (a : AD) (m : M) :
    send ae G st a m = ({ w := (G (st.iA + 1) st.w).1, iA := st.iA + 1 },
      (st.iA + 1, ae.encrypt (G (st.iA + 1) st.w).2 (st.iA + 1, a) m)) :=
  rfl

/-- The invariant of the FS-AEAD game for `fromAEADChain ae G` with key `k`. Write `w_j` and
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
structure GameInv (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (k : W) (st : GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) : Prop where
  vA_w : st.vA.w = chainState G k st.iA
  vA_iA : st.vA.iA = st.iA
  vB : OnChain G k st.vB
  trans_honest : ∀ r ∈ st.trans, 1 ≤ r.1 ∧ r.1 ≤ st.iA ∧
    r.2.2.2 = (r.1, ae.encrypt (chainKey G k r.1) (r.1, r.2.1) r.2.2.1)
  comp_corrA : ∀ j, st.comp j = true → st.corrA = true
  trans_key : st.win = false → ∀ r ∈ st.trans,
    st.vB.iB < r.1 ∨ st.vB.D r.1 = some (chainKey G k r.1)
  future_key : st.win = false → ∀ j, st.iA < j → j ≤ st.vB.iB →
    st.vB.D j = some (chainKey G k j) ∨ (st.corrA = true ∧ st.comp j = false)

variable {ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae} {G : ℕ → W → W × Kae} {k : W}
  {st : GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae)}

/-- The initial game state satisfies the invariant. -/
theorem gameInv_init : GameInv ae G k (.init (fromAEADChain ae G) k) where
  vA_w := rfl
  vA_iA := rfl
  vB := ⟨rfl, fun _ _ h => (nomatch h), fun _ _ => rfl⟩
  trans_honest := fun _ h => (nomatch h)
  comp_corrA := fun _ h => (nomatch h)
  trans_key := fun _ _ h => (nomatch h)
  future_key := fun _ _ h₁ h₂ => absurd (Nat.lt_of_lt_of_le h₁ h₂) (Nat.lt_irrefl 0)

/-- A sends `(a, m)`, and the game increments `i_A` and runs `record`. Then the invariant
holds after the step. -/
theorem gameInv_send (hinv : GameInv ae G k st) (isChall : Bool) (a : AD) (m : M) :
    GameInv ae G k ({ st with vA := (send ae G st.vA a m).1, iA := st.iA + 1 }.record
      isChall a m (send ae G st.vA a m).2) := by
  have hG : G (st.iA + 1) st.vA.w = (chainState G k (st.iA + 1), chainKey G k (st.iA + 1)) := by
    rw [hinv.vA_w]
    rfl
  rw [send_eq, hinv.vA_iA, hG]
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
theorem gameInv_corrA (hinv : GameInv ae G k st) :
    GameInv ae G k { st with
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
theorem gameInv_rcv (hinv : GameInv ae G k st) {a : AD} {i i' : ℕ} {e : Cae}
    {vB' : RecvState W Kae} {m' : M} (hr : rcv ae G st.vB a (i, e) = some (vB', i', m'))
    (w' : Bool) (hw : w' = false → st.win = false ∧ (i ≤ st.iA ∨ st.corrA = true)) :
    GameInv ae G k ({ st with vB := vB', win := w' }.delete i') := by
  obtain ⟨hii, -, -, hon, hiB, hDi, hDj⟩ := rcv_some ae G hinv.vB hr
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
    exact key_after_rcv ae G hinv.vB hr hmem.2 (hinv.trans_key (hw hw').1 r hmem.1)
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
theorem gameInv_win (hinv : GameInv ae G k st) : GameInv ae G k { st with win := true } :=
  ⟨hinv.vA_w, hinv.vA_iA, hinv.vB, hinv.trans_honest, hinv.comp_corrA, fun h => (nomatch h),
    fun h => (nomatch h)⟩

section Oracles

variable [DecidableEq AD] [DecidableEq M] [DecidableEq Cae]

/-- Every oracle of the game for `fromAEADChain ae G` keeps the invariant. -/
theorem gameInv_step (hinv : GameInv ae G k st) (len : M → ℕ) (b : Bool)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain) {z}
    (hz : z ∈ support ((fsaeadSecurityImpl (fromAEADChain ae G) len b t).run st)) :
    GameInv ae G k z.2 := by
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩)
  · change z ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hz
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hz
    obtain ⟨x, rfl⟩ := hz
    exact hinv
  · change z ∈ support ((oracleTransmitA (fromAEADChain ae G) (a, m)).run st) at hz
    simp only [oracleTransmitA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hinv
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact gameInv_send hinv false a m
  · change z ∈ support ((oracleChallA (fromAEADChain ae G) len b (a, m₀, m₁)).run st) at hz
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
  · change z ∈ support ((oracleDeliverB (fromAEADChain ae G) (a, c)).run st) at hz
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
    rcases hr : rcv ae G st.vB a' (i, ae.encrypt (chainKey G k i) (i, a') m)
      with _ | ⟨vB, i', m'⟩
    · simp only [hf, fromAEADChain, hr, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact gameInv_win hinv
    · obtain ⟨hii, -⟩ := rcv_some ae G hinv.vB hr
      subst hii
      simp only [hf, fromAEADChain, hr, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact gameInv_rcv hinv hr _ fun hw => ⟨by simp_all only [Bool.not_eq_true, decide_true,
          Bool.true_and, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
          decide_eq_true_eq], .inl hiA⟩
  · change z ∈ support ((oracleInjectB (fromAEADChain ae G) (a, c)).run st) at hz
    simp only [oracleInjectB, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hinv
    obtain ⟨j, e⟩ := c
    rcases hr : rcv ae G st.vB a (j, e) with _ | ⟨vB, i', m'⟩
    · simp only [fromAEADChain, hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hinv
    · simp only [fromAEADChain, hr, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine gameInv_rcv hinv hr _ fun hw => ?_
      simp only [Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hw
      exact ⟨hw.1, .inr (hinv.comp_corrA _ hw.2)⟩

/-- Let `ae` be correct, and let `st` satisfy the invariant with `win = false`. Then every
outcome of `O-Deliver-B` from `st` has `win = false`. -/
theorem gameInv_deliverB_win_false (hae : ae.Correct) (hinv : GameInv ae G k st)
    (hw : st.win = false) (q : AD × (ℕ × Cae)) :
    ∀ z ∈ support ((oracleDeliverB (fromAEADChain ae G) q).run st), z.2.win = false := by
  intro z hz
  obtain ⟨a, e⟩ := q
  simp only [oracleDeliverB, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with hend
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
  · simp only [hf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  obtain ⟨hmem, rfl, rfl⟩ := GameState.findTrans_spec hf
  obtain ⟨-, -, he⟩ := hinv.trans_honest _ hmem
  simp only at he
  obtain ⟨vB, hr⟩ := exists_rcv_eq_some ae G hinv.vB (hinv.trans_key hw _ hmem).symm
    (hae (chainKey G k i) (i, a') m)
  rw [← he] at hr
  simp only [hf, fromAEADChain, hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
    support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp only [GameState.delete, hw, decide_true, Bool.and_self, Bool.not_true, Bool.or_self]

/-- Let `ae` be correct. Then `GameInv ae G` is a `DeliverInv` for `fromAEADChain ae G`. -/
theorem deliverInv (hae : ae.Correct) : DeliverInv (fromAEADChain ae G) (GameInv ae G) where
  init _ := gameInv_init
  step len b _ t _ _ hinv hz := gameInv_step hinv len b t hz
  deliverB _ _ q hinv hw := gameInv_deliverB_win_false hae hinv hw q

end Oracles

/-! ## Honest delivery -/

/-- A sends the messages `(a, m)` in order. -/
def sendAll (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (st : SendState W) : List (AD × M) → List (ℕ × Cae)
  | [] => []
  | (a, m) :: ms => let (st', c) := send ae G st a m; c :: sendAll ae G st' ms

/-- B receives the ciphertexts `(a, c)` in order. It keeps its state after a rejection and
records `none` for it. -/
def rcvAll (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (st : RecvState W Kae) : List (AD × (ℕ × Cae)) → List (Option (ℕ × M)) × RecvState W Kae
  | [] => ([], st)
  | (a, c) :: cs =>
    match rcv ae G st a c with
    | none => let r := rcvAll ae G st cs; (none :: r.1, r.2)
    | some (st', i, m) => let r := rcvAll ae G st' cs; (some (i, m) :: r.1, r.2)

/-- Let A be at `(w_n, n)` on the chain from `k`, and let A send
`(a_0, m_0), …, (a_{l-1}, m_{l-1})`. Then A's `j`-th ciphertext is
`(n + j + 1, Enc(K_{n+j+1}, (n + j + 1, a_j), m_j))`. -/
theorem sendAll_eq (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    {k : W} (msgs : List (AD × M)) {st : SendState W} (hst : st.w = chainState G k st.iA) :
    sendAll ae G st msgs = msgs.mapIdx fun j am =>
      (st.iA + j + 1, ae.encrypt (chainKey G k (st.iA + j + 1)) (st.iA + j + 1, am.1) am.2) := by
  induction msgs generalizing st with
  | nil => rfl
  | cons am ms ih =>
    obtain ⟨a, m⟩ := am
    have hG : G (st.iA + 1) st.w = (chainState G k (st.iA + 1), chainKey G k (st.iA + 1)) := by
      rw [hst]
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
    (G : ℕ → W → W × Kae) (hae : ae.Correct) {k : W} (del : List (ℕ × AD × M))
    {st : RecvState W Kae} (hst : OnChain G k st) (hnd : (del.map (·.1)).Nodup)
    (hkey : ∀ x ∈ del, st.iB < x.1 ∨ st.D x.1 = some (chainKey G k x.1)) :
    (rcvAll ae G st (del.map fun x =>
      (x.2.1, (x.1, ae.encrypt (chainKey G k x.1) (x.1, x.2.1) x.2.2)))).1 =
      del.map fun x => some (x.1, x.2.2) := by
  induction del generalizing st with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨i, a, m⟩ := x
    obtain ⟨st', hr⟩ := exists_rcv_eq_some ae G hst (hkey _ List.mem_cons_self).symm
      (hae (chainKey G k i) (i, a) m)
    simp only [List.map_cons, rcvAll, hr, List.cons.injEq, true_and]
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    refine ih (rcv_some ae G hst hr).2.2.2.1 hnd.2 fun y hy => ?_
    exact key_after_rcv ae G hst hr (fun h => hnd.1 ⟨y, hy, h⟩)
      (hkey y (List.mem_cons_of_mem _ hy))

/-- Let `ae` be correct, and let `del` be a list of `(j, a, m)` with distinct indices
`j ≥ 1`. Let B start from `Init-B(k)` and receive `(j, Enc(K_j, (j, a), m))` with associated
data `a` for each entry, in the order of `del`. Then B outputs `(j, m)` for each entry. By
`sendAll_eq`, A's `j`-th ciphertext from `Init-A(k)` has this form. -/
theorem rcvAll_honest_initR (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (hae : ae.Correct) (k : W) (del : List (ℕ × AD × M))
    (hnd : (del.map (·.1)).Nodup) (hpos : ∀ x ∈ del, 1 ≤ x.1) :
    (rcvAll ae G (initR k) (del.map fun x =>
      (x.2.1, (x.1, ae.encrypt (chainKey G k x.1) (x.1, x.2.1) x.2.2)))).1 =
      del.map fun x => some (x.1, x.2.2)
  := rcvAll_honest ae G hae del ⟨rfl, fun _ _ h => (nomatch h), fun _ _ => rfl⟩ hnd
    fun x hx => .inl (hpos x hx)

end FromAEADPRG

open FromAEADPRG

/-- Let `ae` be a correct AEAD scheme. Then `fromAEADPRG ae prg` is (perfectly) correct. -/
-- ANCHOR: fromAEADPRG_correct
theorem fromAEADPRG_correct {W Kae Cae AD M : Type} [SampleableType W] [DecidableEq AD]
    [DecidableEq M] [DecidableEq Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (prg : PRGScheme W (W × Kae)) (hae : ae.Correct) :
    (fromAEADPRG ae prg).Correct
-- ANCHOR_END: fromAEADPRG_correct
  := (deliverInv (G := fun _ => prg.gen) hae).correct

/-- Let `ae` be a correct AEAD scheme. Then for every length function and every adversary,
the security experiment for `fromAEADPRG ae prg` equals the experiment of `fs-aead-nd`. -/
theorem fromAEADPRG_securityExp_eq_noDeliverWin {W Kae Cae AD M : Type} [SampleableType W]
    [DecidableEq AD] [DecidableEq M] [DecidableEq Cae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    (hae : ae.Correct) (len : M → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    securityExp (fromAEADPRG ae prg) len adversary =
      securityExpNoDeliverWin (fromAEADPRG ae prg) len adversary :=
  (deliverInv (G := fun _ => prg.gen) hae).securityExp_eq_noDeliverWin len adversary

end FSAEADScheme
