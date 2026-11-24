/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.ConfGame

/-!
# FS-AEAD from AEAD and PRG — moving `G_conf^s` to another chain

The confidentiality analogue of `SecureMessaging.FSAEAD.FromAEADPRG.Security.Transfer`. Let two
chains `G₁` from `k₁` and `G₂` from `k₂` have the same seeds from position `s` on, and the same
keys outside a set of hidden positions. Let the two games encrypt every challenge the same way
(`ChalMode.eff`). Let every hidden position `q` satisfy `q ≤ s`, and let `O-Transmit-A` be blocked
at `q`. Then `normSt G₂ k₂` carries the runs of `G_conf^s` for `G₁` to the runs for `G₂`
(`confRun_map_normSt`).

The game uses the key of a hidden position `q` only to store it in B's dictionary `D`. Before A
sends at `q`, B has not passed `q`, because `G_conf^s` stops at a corruption of A below `s`. A
challenge at `q` is in transit while `D[q]` holds the key, so `O-Corr-B` does not reveal it
(`HidInv`).

- The PRG reductions use this with no hidden position: the seeds below `s` differ.
- The step that replaces the key of a challenge at `j` by an independent key uses it with the
  hidden position `j`.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type}

/-! ## Challenge modes on a chain -/

/-- The challenge mode `c` at position `p` of the chain `G` from `k`, with the chain key for
`real`. -/
def ChalMode.eff (G : ℕ → W → W × Kae) (k : W) (p : ℕ) : ChalMode Kae → ChalMode Kae
  | .real => .key (chainKey G k p)
  | c => c

/-- A's state after `FS-Send` from a normalized state is the normalized state after `FS-Send`. -/
theorem send_fst_normS (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G₁ G₂ : ℕ → W → W × Kae)
    (k₂ : W) (vA : SendState W) (a : AD) (m : M) :
    normS G₂ k₂ (send ae G₁ vA a m).1 = (send ae G₂ (normS G₂ k₂ vA) a m).1 := by
  simp only [send_eq, normS_w, normS_iA]
  rfl

/-- On the chain from `k`, a challenge in mode `c` is a challenge in mode `c.eff`. -/
theorem chalSend_eff [LenSampleable Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) {k : W} (len : M → ℕ) (clen : ℕ → ℕ) (c : ChalMode Kae)
    {vA : SendState W} (hw : vA.w = chainState G k vA.iA) (a : AD) (m : M) :
    chalSend ae G len clen c vA a m = chalSend ae G len clen (c.eff G k (vA.iA + 1)) vA a m := by
  cases c with
  | real =>
    simp only [chalSend, ChalMode.eff, send_eq, hw, gen_chainState]
  | key K => rfl
  | rand => rfl

/-- `ChalMode.eff` is never `real`. -/
theorem ChalMode.eff_ne_real (G : ℕ → W → W × Kae) (k : W) (p : ℕ) (c : ChalMode Kae) :
    c.eff G k p ≠ .real := by
  cases c <;> simp only [ChalMode.eff, ne_eq, reduceCtorEq, not_false_eq_true]

/-- Every outcome of a challenge moves A as `FS-Send` does. -/
theorem fst_of_mem_support_chalSend [LenSampleable Cae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) (len : M → ℕ)
    (clen : ℕ → ℕ) (c : ChalMode Kae) (vA : SendState W) (a : AD) (m : M) {r}
    (hr : r ∈ support (chalSend ae G len clen c vA a m)) : r.1 = (send ae G vA a m).1 := by
  cases c with
  | real =>
    simp only [chalSend, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
  | key K =>
    simp only [chalSend, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
  | rand =>
    simp only [chalSend, support_map, Set.mem_image] at hr
    obtain ⟨e, -, rfl⟩ := hr
    rfl

/-- A challenge in a mode other than `real` commutes with `normS`. -/
theorem chalSend_map_normS [LenSampleable Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) (k₂ : W) (len : M → ℕ) (clen : ℕ → ℕ) (c : ChalMode Kae)
    (hc : c ≠ .real) (vA : SendState W) (a : AD) (m : M) :
    Prod.map (normS G₂ k₂) id <$> chalSend ae G₁ len clen c vA a m =
      chalSend ae G₂ len clen c (normS G₂ k₂ vA) a m := by
  cases c with
  | real => exact absurd rfl hc
  | key K =>
    simp only [chalSend, map_pure, Prod.map_apply, send_fst_normS, id_eq, normS_iA]
  | rand =>
    simp only [chalSend, Functor.map_map, Prod.map_apply, send_fst_normS, id_eq, normS_iA]

/-! ## The invariant of a hidden position -/

/-- The facts about a hidden position `q` that the game keeps when `q ≤ s` and `O-Transmit-A` is
blocked at `q`.
- A corruption of A that did not stop the game comes after A sent at `q`, and every compromised
  index is above `q`.
- Before A sends at `q`, B has not passed `q`.
- After A sent at `q` (a challenge), the challenge is in transit until B passes `q`, and while
  `D[q]` holds a key. -/
structure HidInv (q : ℕ) (st : CState W Kae AD M Cae) : Prop where
  corrA : st.corrA = true → st.end_ = true ∨ q ≤ st.iA
  comp : ∀ i, st.comp i = true → st.end_ = true ∨ q < i
  comp_corrA : ∀ i, st.comp i = true → st.corrA = true
  trans_le : ∀ r ∈ st.trans, r.1 ≤ st.iA
  iB_lt : st.iA < q → st.vB.iB < q
  chall : q ≤ st.iA → st.vB.iB < q → q ∈ st.chall
  D : st.vB.D q ≠ none → q ∈ st.chall

/-- The invariant of the source run of the transfer: the state is on the chain `G` from `k`, and
`HidInv q` holds for every hidden position `q`. -/
def TransInv (G : ℕ → W → W × Kae) (k : W) (hid : ℕ → Prop) (st : CState W Kae AD M Cae) :
    Prop :=
  SeedInv G k st ∧ ∀ q, hid q → HidInv q st

/-- The initial state satisfies the invariant. -/
theorem transInv_init (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (k : W) (hid : ℕ → Prop) :
    TransInv G k hid (GameState.init (fromAEADChain ae G) k : CState W Kae AD M Cae) :=
  ⟨⟨rfl, rfl, ⟨rfl, fun _ _ h => (nomatch h), fun _ _ => rfl⟩⟩, fun q _ =>
    ⟨fun h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h),
      fun _ h => (nomatch h), id, fun h₁ h₂ => absurd h₂ (by
        change ¬0 < q
        simp only [GameState.init, fromAEADChain, FromAEADPRG.initS] at h₁
        omega),
      fun h => absurd rfl h⟩⟩

end FromAEADPRG

end FSAEADScheme

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type}

/-! ## The oracles of `G_conf^s` -/

/-- One call of `O-Chall-A^cm`: `⊥` if a guard fails, and A's step with a challenge from
`chalSend` otherwise. -/
theorem oracleChallMode_run [LenSampleable Cae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) (len : M → ℕ)
    (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (b : Bool) (a : AD) (m₀ m₁ : M)
    (st : CState W Kae AD M Cae) :
    (oracleChallMode ae G len clen cm b (a, m₀, m₁)).run st =
      if (st.end_ || st.corrA || decide (len m₀ ≠ len m₁)) = true then pure (none, st) else
        (fun r => (some r.2, { st with vA := r.1, iA := st.iA + 1 }.record true a
          (if b then m₁ else m₀) r.2)) <$>
          chalSend ae G len clen (cm (st.iA + 1)) st.vA a (if b then m₁ else m₀) := by
  simp only [oracleChallMode, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hg : (st.end_ || st.corrA || decide (len m₀ ≠ len m₁)) = true
  · rw [ite_eq_left hg, ite_eq_left hg]
    rfl
  · rw [ite_eq_right hg, ite_eq_right hg]
    simp only [liftM, StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc,
      pure_bind, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def]

/-- The outcomes of `O-Chall-A^cm`: `⊥` with the state unchanged, or A's step with a challenge
from `chalSend`. -/
theorem mem_support_oracleChallMode [LenSampleable Cae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) (len : M → ℕ)
    (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (b : Bool) (a : AD) (m₀ m₁ : M)
    (st : CState W Kae AD M Cae) {z}
    (hz : z ∈ support ((oracleChallMode ae G len clen cm b (a, m₀, m₁)).run st)) :
    z = (none, st) ∨ (st.end_ = false ∧ st.corrA = false ∧ len m₀ = len m₁ ∧
      ∃ r ∈ support (chalSend ae G len clen (cm (st.iA + 1)) st.vA a (if b then m₁ else m₀)),
        z = (some r.2, { st with vA := r.1, iA := st.iA + 1 }.record true a
          (if b then m₁ else m₀) r.2)) := by
  rw [oracleChallMode_run] at hz
  by_cases hg : (st.end_ || st.corrA || decide (len m₀ ≠ len m₁)) = true
  · rw [ite_eq_left hg, support_pure, Set.mem_singleton_iff] at hz
    exact .inl hz
  · rw [ite_eq_right hg, support_map] at hz
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, not_not] at hg
    obtain ⟨r, hr, rfl⟩ := hz
    exact .inr ⟨hg.1.1, hg.1.2, hg.2, r, hr, rfl⟩

/-! ## The invariants in `G_conf^s` -/

variable [LenSampleable Cae] [DecidableEq AD] [DecidableEq Cae]

/-- Every step of `G_conf^s` for the chain `G` keeps `SeedInv G k`. -/
theorem seedInv_confStep (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (k : W) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (blk : ℕ → Bool) (s : ℕ)
    (b : Bool) (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (st : CState W Kae AD M Cae) (h : SeedInv G k st) :
    ∀ z ∈ support ((confImplWith ae G len clen cm blk s b t).run st), SeedInv G k z.2 := by
  intro z hz
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, e⟩) | ⟨a, e⟩)
  · exact seedInv_oracleUnif n st h z hz
  · change z ∈ support ((oracleTransmitBlk ae G blk (a, m)).run st) at hz
    simp only [oracleTransmitBlk, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact (h.send ae a m).record _ _ _ _
  · change z ∈ support ((oracleChallMode ae G len clen cm b (a, m₀, m₁)).run st) at hz
    rcases mem_support_oracleChallMode ae G len clen cm b a m₀ m₁ st hz with
      rfl | ⟨-, -, -, r, hr, rfl⟩
    · exact h
    · have hr₁ := fst_of_mem_support_chalSend ae G len clen _ st.vA a _ hr
      obtain ⟨r₁, r₂⟩ := r
      simp only at hr₁ ⊢
      subst hr₁
      exact (h.send ae a _).record _ _ _ _
  · exact seedInv_oracleCorrALow s st h z hz
  · change z ∈ support ((oracleCorrBLow W Kae AD M Cae s ()).run st) at hz
    simp only [oracleCorrBLow, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    all_goals
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨h.vA_w, h.vA_iA, h.vB⟩
  · exact seedInv_oracleDeliverBLookup (a, e) st h z hz
  · change z ∈ support ((oracleInjectBRej (fromAEADChain ae G) Prod.fst false (a, e)).run st)
      at hz
    simp only [oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    obtain ⟨i, e⟩ := e
    rcases hr : rcv ae G st.vB a (i, e) with _ | ⟨vB', i', m'⟩
    · simp only [fromAEADChain, hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    · simp only [fromAEADChain, hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨h.vA_w, h.vA_iA, (rcv_some ae G h.vB hr).2.2.2.1⟩

/-- A step of `G_conf^s` keeps `i_A`, or it is a call of `O-Transmit-A` or `O-Chall-A` that
increments `i_A`. -/
theorem iA_confStep (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (blk : ℕ → Bool) (s : ℕ) (b : Bool)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (st : CState W Kae AD M Cae) :
    ∀ z ∈ support ((confImplWith ae G len clen cm blk s b t).run st),
      z.2.iA = st.iA ∨ (fsaeadSpec.isSendQuery t = true ∧ z.2.iA = st.iA + 1) := by
  intro z hz
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, e⟩) | ⟨a, e⟩)
  · change z ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hz
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hz
    obtain ⟨x, rfl⟩ := hz
    exact .inl rfl
  · change z ∈ support ((oracleTransmitBlk ae G blk (a, m)).run st) at hz
    simp only [oracleTransmitBlk, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact .inl rfl
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact .inr ⟨rfl, GameState.record_iA _ _ _ _ _⟩
  · change z ∈ support ((oracleChallMode ae G len clen cm b (a, m₀, m₁)).run st) at hz
    rcases mem_support_oracleChallMode ae G len clen cm b a m₀ m₁ st hz with
      rfl | ⟨-, -, -, r, -, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨rfl, GameState.record_iA _ _ _ _ _⟩
  · change z ∈ support ((oracleCorrALow _ _ _ _ _ s ()).run st) at hz
    simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz <;>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz <;>
      subst hz <;>
      exact .inl rfl
  · change z ∈ support ((oracleCorrBLow W Kae AD M Cae s ()).run st) at hz
    simp only [oracleCorrBLow, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz <;>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz <;>
      subst hz <;>
      exact .inl rfl
  · change z ∈ support ((oracleDeliverBLookup G (a, e)).run st) at hz
    simp only [oracleDeliverBLookup, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact .inl rfl
    rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
    · simp only [hf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact .inl rfl
    · simp only [hf, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact .inl rfl
  · change z ∈ support ((oracleInjectBRej (fromAEADChain ae G) Prod.fst false (a, e)).run st)
      at hz
    simp only [oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact .inl rfl
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact .inl rfl
    rcases hr : (fromAEADChain ae G).rcv st.vB a e with _ | ⟨vB', i', m'⟩
    · simp only [hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact .inl rfl
    · simp only [hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact .inl rfl

omit [LenSampleable Cae] [DecidableEq AD] [DecidableEq Cae] in
/-- `delete` and a new state of B keep `HidInv q` if B does not pass `q` while a challenge at `q`
is not in transit, and `D[q]` gets a key only at such a pass. -/
theorem HidInv.delete {q : ℕ} {st : CState W Kae AD M Cae} (hI : HidInv q st)
    {vB : RecvState W Kae} (i : ℕ)
    (hiB : st.iA < q → vB.iB < q)
    (hchall : q ≤ st.iA → vB.iB < q → q ∈ st.chall ∧ q ≠ i)
    (hD : vB.D q ≠ none → q ∈ st.chall ∧ q ≠ i) :
    HidInv q ({ st with vB }.delete i) where
  corrA := hI.corrA
  comp j hj := by
    simp only [GameState.delete, Bool.and_eq_true, bne_iff_ne, ne_eq] at hj
    exact hI.comp j hj.2
  comp_corrA j hj := by
    simp only [GameState.delete, Bool.and_eq_true, bne_iff_ne, ne_eq] at hj
    exact hI.comp_corrA j hj.2
  trans_le r hr := hI.trans_le r (List.mem_filter.mp hr).1
  iB_lt := hiB
  chall h₁ h₂ := by
    obtain ⟨hc, hqi⟩ := hchall h₁ h₂
    exact Finset.mem_erase.mpr ⟨hqi, hc⟩
  D h := by
    obtain ⟨hc, hqi⟩ := hD h
    exact Finset.mem_erase.mpr ⟨hqi, hc⟩

/-- Let `q ≤ s` and let `O-Transmit-A` be blocked at `q`. Then every step of `G_conf^s` on the
chain `G` keeps `HidInv q`. -/
theorem hidInv_confStep (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (k : W) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (blk : ℕ → Bool) (s : ℕ)
    (b : Bool) {q : ℕ} (hqb : blk q = true) (hqs : q ≤ s)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (st : CState W Kae AD M Cae) (h : SeedInv G k st) (hI : HidInv q st) :
    ∀ z ∈ support ((confImplWith ae G len clen cm blk s b t).run st), HidInv q z.2 := by
  intro z hz
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, e⟩) | ⟨a, e⟩)
  · change z ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hz
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hz
    obtain ⟨x, rfl⟩ := hz
    exact hI
  · change z ∈ support ((oracleTransmitBlk ae G blk (a, m)).run st) at hz
    simp only [oracleTransmitBlk, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz with hg
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hI
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      have hq : st.iA + 1 ≠ q := fun h' => by
        simp only [h', hqb, Bool.or_true, not_true_eq_false] at hg
      refine ⟨fun hc => ?_, fun j hj => ?_, fun j hj => ?_, fun r hr => ?_, fun h₁ => ?_,
        fun h₁ h₂ => ?_, fun hD => ?_⟩
      · simp only [GameState.record_corrA, GameState.record_end_, GameState.record_iA] at hc ⊢
        rcases hI.corrA hc with h' | h'
        · exact .inl h'
        · exact .inr (by omega)
      · simp only [GameState.record_comp, GameState.record_end_] at hj ⊢
        exact hI.comp j hj
      · simp only [GameState.record_comp, GameState.record_corrA] at hj ⊢
        exact hI.comp_corrA j hj
      · simp only [GameState.record_iA]
        rcases GameState.mem_record_trans hr with hr | rfl
        · have := hI.trans_le r hr
          omega
        · exact le_rfl
      · simp only [GameState.record_iA, GameState.record_vB] at h₁ ⊢
        exact hI.iB_lt (by omega)
      · simp only [GameState.record_iA, GameState.record_vB] at h₁ h₂
        exact GameState.mem_record_chall (hI.chall (by omega) h₂)
      · simp only [GameState.record_vB] at hD
        exact GameState.mem_record_chall (hI.D hD)
  · change z ∈ support ((oracleChallMode ae G len clen cm b (a, m₀, m₁)).run st) at hz
    rcases mem_support_oracleChallMode ae G len clen cm b a m₀ m₁ st hz with
      rfl | ⟨hend, hcorr, -, r, -, rfl⟩
    · exact hI
    refine ⟨fun hc => ?_, fun j hj => ?_, fun j hj => ?_, fun r' hr => ?_, fun h₁ => ?_,
      fun h₁ h₂ => ?_, fun hD => ?_⟩
    · simp only [GameState.record_corrA, hcorr, Bool.false_eq_true] at hc
    · simp only [GameState.record_comp, GameState.record_end_] at hj ⊢
      exact hI.comp j hj
    · simp only [GameState.record_comp, GameState.record_corrA] at hj ⊢
      exact hI.comp_corrA j hj
    · simp only [GameState.record_iA]
      rcases GameState.mem_record_trans hr with hr | rfl
      · have := hI.trans_le r' hr
        omega
      · exact le_rfl
    · simp only [GameState.record_iA, GameState.record_vB] at h₁ ⊢
      exact hI.iB_lt (by omega)
    · simp only [GameState.record_iA, GameState.record_vB] at h₁ h₂
      rcases Nat.lt_or_ge st.iA q with hlt | hle
      · obtain rfl : q = st.iA + 1 := by omega
        exact GameState.iA_mem_record_chall (st := { st with vA := r.1, iA := st.iA + 1 }) hcorr
          a _ _
      · exact GameState.mem_record_chall (hI.chall hle h₂)
    · simp only [GameState.record_vB] at hD
      exact GameState.mem_record_chall (hI.D hD)
  · change z ∈ support ((oracleCorrALow _ _ _ _ _ s ()).run st) at hz
    by_cases hend : st.end_ = true
    · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, ↓reduceIte,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hI
    by_cases hlt : st.iA < s
    · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, hlt,
        Bool.false_eq_true, ↓reduceIte, StateT.run_set, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨fun _ => .inl rfl, fun _ _ => .inl rfl, fun _ _ => rfl, hI.trans_le, hI.iB_lt,
        hI.chall, hI.D⟩
    · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, hlt,
        Bool.false_eq_true, ↓reduceIte, StateT.run_set, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨fun _ => .inr (show q ≤ st.iA by omega), fun j hj => ?_, fun _ _ => rfl,
        hI.trans_le, hI.iB_lt, hI.chall, hI.D⟩
      cases hc : st.corrA
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hj
        exact .inr (by omega)
      · simp only [hc, ↓reduceIte] at hj
        exact .inr ((hI.comp j hj).resolve_left hend)
  · change z ∈ support ((oracleCorrBLow W Kae AD M Cae s ()).run st) at hz
    simp only [oracleCorrBLow, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hI
    all_goals
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨fun _ => .inl rfl, fun _ _ => .inl rfl, hI.comp_corrA, hI.trans_le, hI.iB_lt,
        hI.chall, hI.D⟩
  · change z ∈ support ((oracleDeliverBLookup G (a, e)).run st) at hz
    simp only [oracleDeliverBLookup, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hI
    rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
    · simp only [hf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hI
    simp only [hf, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    have hiA : i ≤ st.iA := hI.trans_le _ (GameState.findTrans_spec hf).1
    rcases hr : rcvKey G st.vB i with _ | ⟨vB', K⟩
    · obtain ⟨hDi, hiB⟩ := (rcvKey_eq_none_iff G st.vB i).1 hr
      simp only [Option.map_none, Option.getD_none]
      refine hI.delete i hI.iB_lt (fun h₁ h₂ => ⟨hI.chall h₁ h₂, by omega⟩)
        (fun hD => ⟨hI.D hD, fun hqi => hD (hqi ▸ hDi)⟩)
    · obtain ⟨-, -, -, hiB', hDi, hDj⟩ := rcvKey_some G h.vB hr
      simp only [Option.map_some, Option.getD_some]
      refine hI.delete i (fun h₁ => ?_) (fun h₁ h₂ => ?_) (fun hD => ?_)
      · have := hI.iB_lt h₁
        omega
      · exact ⟨hI.chall h₁ (by omega), by omega⟩
      · have hqi : q ≠ i := fun hqi => hD (hqi ▸ hDi)
        rw [hDj q hqi] at hD
        split_ifs at hD with hlt
        · exact ⟨hI.chall (by omega) hlt.1, hqi⟩
        · exact ⟨hI.D hD, hqi⟩
  · change z ∈ support ((oracleInjectBRej (fromAEADChain ae G) Prod.fst false (a, e)).run st)
      at hz
    simp only [oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte] at hz
    split_ifs at hz with h₁ h₂
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hI
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hI
    obtain ⟨i, e⟩ := e
    rcases hr : rcv ae G st.vB a (i, e) with _ | ⟨vB', i', m'⟩
    · simp only [fromAEADChain, hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hI
    simp only [fromAEADChain, hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h₁
    simp only [Bool.not_eq_true', Bool.not_eq_false] at h₂
    obtain ⟨hii, -, -, -, hiB', -, hDj⟩ := rcv_some ae G h.vB hr
    subst i'
    have hqi : q < i := (hI.comp i h₂).resolve_left (by simp only [h₁.1, Bool.false_eq_true,
      not_false_eq_true])
    have hqA : q ≤ st.iA := (hI.corrA (hI.comp_corrA i h₂)).resolve_left (by
      simp only [h₁.1, Bool.false_eq_true, not_false_eq_true])
    refine hI.delete i (fun h₃ => absurd h₃ (by omega)) (fun _ h₃ => by omega) (fun hD => ?_)
    rw [hDj q (by omega)] at hD
    split_ifs at hD with hlt
    · exact ⟨hI.chall hqA hlt.1, by omega⟩
    · exact ⟨hI.D hD, by omega⟩

/-! ## Moving a run to another chain -/

omit [LenSampleable Cae] [DecidableEq AD] [DecidableEq Cae] in
/-- Let B's state be on the chain `G₁` from `k₁`, let `G₂` from `k₂` have the same seed at `i_B`,
and the same key at every position where `D` holds a key. Then `normR G₂ k₂` does not change B's
state. -/
theorem normR_eq_self {G₁ G₂ : ℕ → W → W × Kae} {k₁ k₂ : W} {vB : RecvState W Kae}
    (hon : OnChain G₁ k₁ vB) (hw : chainState G₁ k₁ vB.iB = chainState G₂ k₂ vB.iB)
    (hD : ∀ q K, vB.D q = some K → chainKey G₁ k₁ q = chainKey G₂ k₂ q) :
    normR G₂ k₂ vB = vB := by
  obtain ⟨w, iB, D⟩ := vB
  have hw' := hon.w_eq
  simp only at hw hw' hD
  simp only [normR, RecvState.mk.injEq, true_and]
  refine ⟨by rw [← hw, ← hw'], funext fun q => ?_⟩
  rcases hq : D q with _ | K
  · rfl
  · simp only [Option.map_some, Option.some.injEq]
    rw [← hD q K hq, hon.D_key q K hq]

omit [LenSampleable Cae] [DecidableEq AD] [DecidableEq Cae] in
/-- `O-Transmit-A^blk` commutes with `normSt` if the chains have the same key at the position of
every transmission that is not blocked. -/
theorem oracleTransmitBlk_map_normSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) {k₁ : W} (k₂ : W) (blk : ℕ → Bool) {st : CState W Kae AD M Cae}
    (hinv : SeedInv G₁ k₁ st)
    (hkey : blk (st.iA + 1) = false → chainKey G₁ k₁ (st.iA + 1) = chainKey G₂ k₂ (st.iA + 1))
    (q : AD × M) :
    Prod.map id (normSt G₂ k₂) <$> (oracleTransmitBlk ae G₁ blk q).run st =
      (oracleTransmitBlk ae G₂ blk q).run (normSt G₂ k₂ st) := by
  obtain ⟨a, m⟩ := q
  simp only [oracleTransmitBlk, StateT.run_bind, StateT.run_get, pure_bind, normSt_end_,
    normSt_iA]
  by_cases hg : (st.end_ || blk (st.iA + 1)) = true
  · rw [ite_eq_left hg, ite_eq_left hg]
    simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  · rw [ite_eq_right hg, ite_eq_right hg]
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hg
    have h := send_normS ae G₁ G₂ k₂ (by rw [hinv.vA_iA]; exact hkey hg.2) hinv.vA_w a m
    simp only [normSt_vA, ← h, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      map_pure, Prod.map_apply, id_eq, normSt_record]
    rfl

omit [DecidableEq AD] [DecidableEq Cae] in
/-- `O-Chall-A^cm` commutes with `normSt` if the two games encrypt the challenge at `i_A + 1` the
same way. -/
theorem oracleChallMode_map_normSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) {k₁ : W} (k₂ : W) (len : M → ℕ) (clen : ℕ → ℕ)
    (cm₁ cm₂ : ℕ → ChalMode Kae) (b : Bool) {st : CState W Kae AD M Cae}
    (hinv : SeedInv G₁ k₁ st)
    (heff : (cm₁ (st.iA + 1)).eff G₁ k₁ (st.iA + 1) = (cm₂ (st.iA + 1)).eff G₂ k₂ (st.iA + 1))
    (q : AD × M × M) :
    Prod.map id (normSt G₂ k₂) <$> (oracleChallMode ae G₁ len clen cm₁ b q).run st =
      (oracleChallMode ae G₂ len clen cm₂ b q).run (normSt G₂ k₂ st) := by
  obtain ⟨a, m₀, m₁⟩ := q
  rw [oracleChallMode_run, oracleChallMode_run]
  simp only [normSt_end_, normSt_corrA, normSt_iA, normSt_vA]
  by_cases hg : (st.end_ || st.corrA || decide (len m₀ ≠ len m₁)) = true
  · rw [ite_eq_left hg, ite_eq_left hg]
    simp only [map_pure, Prod.map_apply, id_eq]
  · rw [ite_eq_right hg, ite_eq_right hg]
    generalize (if b = true then m₁ else m₀) = m
    have hi := hinv.vA_iA
    rw [chalSend_eff ae G₁ len clen _ hinv.vA_w,
      chalSend_eff ae G₂ (k := k₂) (vA := normS G₂ k₂ st.vA) len clen _ rfl, normS_iA, hi, heff,
      ← chalSend_map_normS ae G₁ G₂ k₂ len clen _ (ChalMode.eff_ne_real _ _ _ _),
      Functor.map_map, Functor.map_map]
    congr 1
    funext r
    simp only [Prod.map_apply, id_eq, normSt_record]
    rfl

omit [LenSampleable Cae] [DecidableEq AD] [DecidableEq Cae] in
/-- `O-Corr-B^s` commutes with `normSt` if `normSt` does not change the states that it reveals. -/
theorem oracleCorrBLow_map_normSt (G₂ : ℕ → W → W × Kae) (k₂ : W) (s : ℕ)
    {st : CState W Kae AD M Cae} (hA : s ≤ st.iA → normS G₂ k₂ st.vA = st.vA)
    (hB : st.chall = ∅ → s ≤ st.vB.iB → normR G₂ k₂ st.vB = st.vB) :
    Prod.map id (normSt G₂ k₂) <$> (oracleCorrBLow W Kae AD M Cae s ()).run st =
      (oracleCorrBLow W Kae AD M Cae s ()).run (normSt G₂ k₂ st) := by
  simp only [oracleCorrBLow, StateT.run_bind, StateT.run_get, pure_bind, normSt_end_,
    normSt_chall, normSt_iA, normSt_vB, normR_iB]
  by_cases hg : (st.end_ || decide (st.chall ≠ ∅)) = true
  · rw [ite_eq_left hg, ite_eq_left hg]
    simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  · rw [ite_eq_right hg, ite_eq_right hg]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, not_not] at hg
    by_cases hlt : min st.iA st.vB.iB < s
    · simp only [hlt, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        map_pure, Prod.map_apply, id_eq]
      rfl
    · simp only [hlt, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        map_pure, Prod.map_apply, id_eq, normSt_vA]
      simp only [normSt, hA (by omega), hB hg.2 (by omega)]

omit [LenSampleable Cae] in
/-- `O-Inject-B^rej` commutes with `normSt` if the chains have the same key at every compromised
index. -/
theorem oracleInjectBRej_map_normSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) {k₁ : W} (k₂ : W) {st : CState W Kae AD M Cae}
    (hinv : SeedInv G₁ k₁ st)
    (hkey : ∀ i, st.comp i = true → st.end_ = false → 1 ≤ i →
      chainKey G₁ k₁ i = chainKey G₂ k₂ i)
    (q : AD × (ℕ × Cae)) :
    Prod.map id (normSt G₂ k₂) <$>
        (oracleInjectBRej (fromAEADChain ae G₁) Prod.fst false q).run st =
      (oracleInjectBRej (fromAEADChain ae G₂) Prod.fst false q).run (normSt G₂ k₂ st) := by
  obtain ⟨a, e⟩ := q
  have hf : (normSt G₂ k₂ st).findTrans a e = st.findTrans a e := rfl
  simp only [oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, normSt_end_, normSt_comp, hf]
  by_cases hg : (st.end_ || (st.findTrans a e).isSome) = true
  · rw [ite_eq_left hg, ite_eq_left hg]
    simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  rw [ite_eq_right hg, ite_eq_right hg]
  by_cases hc : (!st.comp e.1) = true
  · rw [ite_eq_left hc, ite_eq_left hc]
    simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  rw [ite_eq_right hc, ite_eq_right hc]
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hg
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
  have h := rcv_normR ae G₁ G₂ k₂ hinv.vB a e (hkey _ hc hg.1)
  simp only [fromAEADChain, normSt_vB, ← h]
  rcases rcv ae G₁ st.vB a e with _ | ⟨vB', i', m'⟩
  · simp only [Option.map_none, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  · simp only [Option.map_some, Prod.map_apply, id_eq, StateT.run_bind, StateT.run_set,
      StateT.run_pure, pure_bind, map_pure]
    rfl

/-- Let the chains `G₁` from `k₁` and `G₂` from `k₂` have the same seeds from position `s` on and
the same keys outside the hidden positions, let the two games encrypt every challenge the same
way, and let `O-Transmit-A` be blocked at every hidden position. Then from a state with the
invariant, `normSt G₂ k₂` carries a step of `G_conf^s` for `G₁` to the step for `G₂`. -/
theorem confImplWith_map_normSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) {k₁ : W} (k₂ : W) (len : M → ℕ) (clen : ℕ → ℕ)
    (cm₁ cm₂ : ℕ → ChalMode Kae) (blk : ℕ → Bool) (s : ℕ) (b : Bool) (hid : ℕ → Prop)
    (hkey : ∀ q, 1 ≤ q → ¬hid q → chainKey G₁ k₁ q = chainKey G₂ k₂ q)
    (hseed : ∀ q, s ≤ q → chainState G₁ k₁ q = chainState G₂ k₂ q)
    (heff : ∀ p, (cm₁ p).eff G₁ k₁ p = (cm₂ p).eff G₂ k₂ p)
    (hhid : ∀ q, hid q → blk q = true)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    {st : CState W Kae AD M Cae} (h : TransInv G₁ k₁ hid st) :
    Prod.map id (normSt G₂ k₂) <$> (confImplWith ae G₁ len clen cm₁ blk s b t).run st =
      (confImplWith ae G₂ len clen cm₂ blk s b t).run (normSt G₂ k₂ st) := by
  rcases t with ((((((n | q) | q) | u) | u) | q) | q)
  · exact oracleUnif_map _ _ _ n st
  · refine oracleTransmitBlk_map_normSt ae G₁ G₂ k₂ blk h.1 (fun hb => ?_) q
    refine hkey _ (Nat.succ_pos _) fun hq => ?_
    simp only [hhid _ hq, Bool.true_eq_false] at hb
  · exact oracleChallMode_map_normSt ae G₁ G₂ k₂ len clen cm₁ cm₂ b h.1 (heff _) q
  · exact oracleCorrALow_map_normSt G₁ G₂ k₂ s hseed h.1
  · refine oracleCorrBLow_map_normSt G₂ k₂ s (fun hs => ?_) (fun hc hs => ?_)
    · rw [normS, ← hseed _ (by rw [h.1.vA_iA]; omega), ← h.1.vA_w]
    · refine normR_eq_self h.1.vB (hseed _ hs) fun q K hq => ?_
      refine hkey q ?_ fun hh => ?_
      · by_contra h0
        rw [h.1.vB.D_none q (.inl (by omega))] at hq
        exact nomatch hq
      · have := (h.2 q hh).D (by rw [hq]; exact Option.some_ne_none K)
        rw [hc] at this
        exact Finset.notMem_empty q this
  · exact oracleDeliverBLookup_map_normSt G₁ G₂ k₂ h.1 q
  · refine oracleInjectBRej_map_normSt ae G₁ G₂ k₂ h.1 (fun i hc he hi => ?_) q
    refine hkey i hi fun hh => ?_
    rcases (h.2 i hh).comp i hc with h' | h'
    · rw [he] at h'
      exact Bool.false_ne_true h'
    · exact lt_irrefl i h'

/-- **Moving a run of `G_conf^s` to another chain.** Let the chains `G₁` from `k₁` and `G₂` from
`k₂` have the same seeds `w_q` for `q ≥ s`, and the same keys `K_q` for `q ≥ 1` outside a set of
hidden positions. Let the challenge modes `cm₁` and `cm₂` encrypt every challenge the same way on
the two chains, and let every hidden position `q` have `q ≤ s` and a blocked `O-Transmit-A`. Then
the runs of `G_conf^s` for `G₁` from `k₁`, with `normSt G₂ k₂` on the final state, are the runs
for `G₂` from `k₂`. -/
theorem confRun_map_normSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G₁ G₂ : ℕ → W → W × Kae) (k₁ k₂ : W) (len : M → ℕ) (clen : ℕ → ℕ)
    (cm₁ cm₂ : ℕ → ChalMode Kae) (blk : ℕ → Bool) (s : ℕ) (b : Bool) (hid : ℕ → Prop)
    (hkey : ∀ q, 1 ≤ q → ¬hid q → chainKey G₁ k₁ q = chainKey G₂ k₂ q)
    (hseed : ∀ q, s ≤ q → chainState G₁ k₁ q = chainState G₂ k₂ q)
    (heff : ∀ p, (cm₁ p).eff G₁ k₁ p = (cm₂ p).eff G₂ k₂ p)
    (hhid : ∀ q, hid q → blk q = true ∧ q ≤ s)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    Prod.map id (Prod.map (normSt G₂ k₂) id) <$>
        confRun ae G₁ len clen cm₁ blk s b adversary k₁ =
      confRun ae G₂ len clen cm₂ blk s b adversary k₂ := by
  have hinit : Prod.map (normSt G₂ k₂) id
      ((GameState.init (fromAEADChain ae G₁) k₁ : CState W Kae AD M Cae), ConfHist.init) =
      (GameState.init (fromAEADChain ae G₂) k₂, ConfHist.init) := rfl
  rw [confRun, confRun, ← hinit]
  refine map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (fun x => TransInv G₁ k₁ hid x.1)
    (Prod.map (normSt G₂ k₂) id) ?_ ?_ adversary _ (transInv_init ae G₁ k₁ hid)
  · intro t x hx y hy
    obtain ⟨z, hz, rfl⟩ := QueryImpl.mem_support_extendState_run _ confAux t x.1 x.2 hy
    exact ⟨seedInv_confStep ae G₁ k₁ len clen cm₁ blk s b t x.1 hx.1 z hz, fun q hq =>
      hidInv_confStep ae G₁ k₁ len clen cm₁ blk s b (hhid q hq).1 (hhid q hq).2 t x.1 hx.1
        (hx.2 q hq) z hz⟩
  · intro t x hx
    obtain ⟨st, h⟩ := x
    refine QueryImpl.extendState_run_map_eq _ _ confAux confAux (normSt G₂ k₂) t st h
      (confImplWith_map_normSt ae G₁ G₂ k₂ len clen cm₁ cm₂ blk s b hid hkey hseed heff
        (fun q hq => (hhid q hq).1) t hx) fun u s' => ?_
    rcases t with ((((((n | q) | q) | u) | u) | q) | q) <;> rfl

end FromAEADPRG




end FSAEADScheme
