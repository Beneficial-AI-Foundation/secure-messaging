/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.ConfHybrid

/-!
# FS-AEAD from AEAD and PRG — an independent key for the challenge at `j`

The AEAD reduction `E'_j` of the confidentiality step gets the key of the challenge at position
`j` from the AEAD game, but it must store a key of its own in B's dictionary `D`: `O-Corr-B` can
reveal `D[j]` if A transmits a normal message at `j`. So the real world of `E'_j` is the hybrid
`G'_j` (`confHybKey`): the chain has uniform steps `1, …, j`, and the challenge at `j` is
encrypted under an independent uniform key `K*` instead of the chain key `K_j`.

`prEvent_confHybKey_eq` shows that `G'_j` and `G_{j,j-1}` give every event of `(b, b', history)`
the same probability, in the game `G_conf^j` that stops at a corruption below `j`. Write `T` for
"A tried to transmit at `j`" and `C` for "A sent a challenge at `j`". Then:
- on runs with `T`, the key `K*` is never used: the two games are identical until `C`;
- on runs without `T`, the chain key `K_j` is used only to fill `D[j]`, while the challenge at `j`
  is in transit, so `O-Corr-B` does not reveal it. With `O-Transmit-A` blocked at `j` (identical
  until `T`), `normSt` moves the run to the chain with `K_j = K*` (`confRun_map_normSt` with the
  hidden position `j`).
Both `K_j` and `K*` are uniform, so the two parts add up to `G_{j,j-1}`.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal OracleComp.ProgramLogic.Relational

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type}

/-! ## The history of the transmissions and challenges -/

/-- The history update keeps every recorded challenge. -/
theorem chal_confAux {p : ℕ}
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (st : CState W Kae AD M Cae) (u) (st' : CState W Kae AD M Cae) {h : ConfHist}
    (hp : h.chal p = true) : (confAux t st u st' h).chal p = true := by
  rcases t with ((((((n | q) | q) | u) | u) | q) | q)
  all_goals simp only [confAux]
  all_goals first
    | exact hp
    | (split_ifs <;> simp only [ConfHist.reveal, hp, Bool.true_or])

/-- The history update keeps every recorded transmission. -/
theorem tx_confAux {p : ℕ}
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (st : CState W Kae AD M Cae) (u) (st' : CState W Kae AD M Cae) {h : ConfHist}
    (hp : h.tx p = true) : (confAux t st u st' h).tx p = true := by
  rcases t with ((((((n | q) | q) | u) | u) | q) | q)
  all_goals simp only [confAux]
  all_goals first
    | exact hp
    | (split_ifs <;> simp only [ConfHist.reveal, hp, Bool.true_or])

/-! ## Transmissions and challenges in a game without blocked positions -/

/-- In a game without blocked positions, every recorded transmission and challenge is at a
position that A has sent, and no position has both. -/
structure TxInv (x : CState W Kae AD M Cae × ConfHist) : Prop where
  tx_le : ∀ p, x.2.tx p = true → p ≤ x.1.iA
  chal_le : ∀ p, x.2.chal p = true → p ≤ x.1.iA
  excl : ∀ p, x.2.tx p = true → x.2.chal p = false

/-- A step that keeps `i_A`, the transmissions and the challenges keeps `TxInv`. -/
theorem TxInv.of_eq {x y : CState W Kae AD M Cae × ConfHist} (hx : TxInv x)
    (hiA : y.1.iA = x.1.iA) (htx : y.2.tx = x.2.tx) (hchal : y.2.chal = x.2.chal) : TxInv y :=
  ⟨fun p hp => hiA ▸ hx.tx_le p (htx ▸ hp), fun p hp => hiA ▸ hx.chal_le p (hchal ▸ hp),
    fun p hp => hchal ▸ hx.excl p (htx ▸ hp)⟩

variable [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae]

/-- Every step of `G_conf^s` without blocked positions keeps `TxInv`. -/
theorem txInv_confStep (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (s : ℕ) (b : Bool)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (x : CState W Kae AD M Cae × ConfHist) (hx : TxInv x) :
    ∀ z ∈ support ((confImpl ae G len clen cm (fun _ => false) s b t).run x), TxInv z.2 := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := QueryImpl.mem_support_extendState_run _ confAux t x.1 x.2 hz
  obtain ⟨st, h⟩ := x
  have htx : ∀ p, h.tx p = true → p ≤ st.iA := hx.tx_le
  have hchal : ∀ p, h.chal p = true → p ≤ st.iA := hx.chal_le
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, e⟩) | ⟨a, e⟩)
  · change y ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hy
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hy
    obtain ⟨x, rfl⟩ := hy
    exact hx
  · change y ∈ support ((oracleTransmitBlk ae G (fun _ => false) (a, m)).run st) at hy
    simp only [oracleTransmitBlk, StateT.run_bind, StateT.run_get, pure_bind,
      Bool.or_false] at hy
    split_ifs at hy with hend
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [confAux, hend, ↓reduceIte] using hx
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy
      simp only [Bool.not_eq_true] at hend
      refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩ <;>
        simp only [confAux, hend, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true,
          decide_eq_true_eq, GameState.record_iA] at hp ⊢
      · rcases hp with hp | rfl
        · have := htx p hp
          omega
        · exact le_rfl
      · have := hchal p hp
        omega
      · rcases hp with hp | rfl
        · exact hx.excl p hp
        · cases hc : h.chal (st.iA + 1)
          · rfl
          · have := hchal _ hc
            omega
  · change y ∈ support ((oracleChallMode ae G len clen cm b (a, m₀, m₁)).run st) at hy
    rcases mem_support_oracleChallMode ae G len clen cm b a m₀ m₁ st hy with
      rfl | ⟨-, -, -, r, -, rfl⟩
    · simpa only [confAux, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using hx
    · refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩ <;>
        simp only [confAux, Option.isSome_some, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq,
          GameState.record_iA] at hp ⊢
      · have := htx p hp
        omega
      · rcases hp with hp | rfl
        · have := hchal p hp
          omega
        · exact le_rfl
      · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
        refine ⟨hx.excl p hp, fun h' => ?_⟩
        have := htx p hp
        omega
  all_goals
    refine hx.of_eq ?_ ?_ ?_
  all_goals try first
    | (simp only [confAux]; split_ifs <;> rfl)
    | rfl
  all_goals
    exact (iA_confStep ae G len clen cm (fun _ => false) s b _ st y hy).resolve_right
      fun h => Bool.false_ne_true h.1

/-! ## Identical until a challenge or a transmission at `j` -/

/-- Two challenge modes that differ only at positions in `B` give steps of `G_conf^s` that agree
until a challenge at a position in `B`. -/
theorem prEvent_confImpl_and_not_chal_eq (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (cm₁ cm₂ : ℕ → ChalMode Kae)
    (blk : ℕ → Bool) (s : ℕ) (b : Bool) (B : ℕ → Prop) (hcm : ∀ p, ¬B p → cm₁ p = cm₂ p)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (x : CState W Kae AD M Cae × ConfHist)
    (q : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Range t ×
      (CState W Kae AD M Cae × ConfHist) → Prop) :
    Pr{let z ← (confImpl ae G len clen cm₁ blk s b t).run x}[
        q z ∧ ¬∃ p, B p ∧ z.2.2.chal p = true] =
      Pr{let z ← (confImpl ae G len clen cm₂ blk s b t).run x}[
        q z ∧ ¬∃ p, B p ∧ z.2.2.chal p = true] := by
  rcases t with ((((((n | q') | ⟨a, m₀, m₁⟩) | u) | u) | q') | q')
  any_goals rfl
  obtain ⟨st, h⟩ := x
  simp only [confImpl, confImplWith, QueryImpl.extendState_apply, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr]
  rw [oracleChallMode_run, oracleChallMode_run]
  by_cases hg : (st.end_ || st.corrA || decide (len m₀ ≠ len m₁)) = true
  · rw [ite_eq_left hg, ite_eq_left hg]
  rw [ite_eq_right hg, ite_eq_right hg]
  by_cases hp : B (st.iA + 1)
  · have h0 (cm : ℕ → ChalMode Kae) :
        Pr{let z ← ((fun r => (some r.2, { st with vA := r.1, iA := st.iA + 1 }.record true a
          (if b = true then m₁ else m₀) r.2)) <$> chalSend ae G len clen (cm (st.iA + 1)) st.vA a
            (if b = true then m₁ else m₀)) >>= fun p =>
          pure (p.1, (p.2, confAux (fsaeadSpec.OChallA (a, m₀, m₁)) st p.1 p.2 h))}[
            q z ∧ ¬∃ p, B p ∧ z.2.2.chal p = true] = 0 := by
      refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hzq => hzq.2 ⟨st.iA + 1, hp, ?_⟩
      simp only [support_bind, support_map, Set.mem_image, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨_, ⟨r, -, rfl⟩, rfl⟩ := hz
      simp only [confAux, Option.isSome_some, ↓reduceIte, decide_true, Bool.or_true]
    erw [h0, h0]
  · rw [hcm _ hp]

/-- No blocked position and the position `j` blocked give steps of `G_conf^s` that agree until a
transmission at `j`. -/
theorem prEvent_confImpl_and_not_tx_eq (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (s : ℕ)
    (b : Bool) (j : ℕ) (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (x : CState W Kae AD M Cae × ConfHist)
    (q : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Range t ×
      (CState W Kae AD M Cae × ConfHist) → Prop) :
    Pr{let z ← (confImpl ae G len clen cm (fun _ => false) s b t).run x}[
        q z ∧ ¬z.2.2.tx j = true] =
      Pr{let z ← (confImpl ae G len clen cm (fun p => decide (p = j)) s b t).run x}[
        q z ∧ ¬z.2.2.tx j = true] := by
  rcases t with ((((((n | ⟨a, m⟩) | q') | u) | u) | q') | q')
  any_goals rfl
  obtain ⟨st, h⟩ := x
  simp only [confImpl, confImplWith, QueryImpl.extendState_apply, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr]
  by_cases hend : st.end_ = true
  · simp only [oracleTransmitBlk, StateT.run_bind, StateT.run_get, pure_bind, hend, Bool.true_or,
      ↓reduceIte, StateT.run_pure]
  by_cases hp : st.iA + 1 = j
  · have h0 (blk : ℕ → Bool) :
        Pr{let z ← ((oracleTransmitBlk ae G blk (a, m)).run st >>= fun p =>
          pure (p.1, (p.2, confAux (fsaeadSpec.OTransmitA (a, m)) st p.1 p.2 h)))}[
            q z ∧ ¬z.2.2.tx j = true] = 0 := by
      refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hzq => hzq.2 ?_
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
        exists_prop] at hz
      obtain ⟨_, -, rfl⟩ := hz
      simp only [confAux, hend, Bool.false_eq_true, ↓reduceIte, hp, decide_true, Bool.or_true]
    erw [h0, h0]
  · simp only [oracleTransmitBlk, StateT.run_bind, StateT.run_get, pure_bind, hp,
      decide_false]

/-! ## The key of the challenge at `n + 1` -/

/-- The challenge modes of `G'_{n+1}`: uniform ciphertexts at the positions `1, …, n`, and the key
`K` at `n + 1`. -/
def keyAt (n : ℕ) (K : Kae) : ℕ → ChalMode Kae := Function.update (randUpTo n) (n + 1) (.key K)

omit [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae] in
/-- The initial state satisfies `TxInv`. -/
theorem txInv_init (fs : FSAEADScheme W (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W) :
    TxInv ((GameState.init fs k : CState W Kae AD M Cae), ConfHist.init) :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ _ => rfl⟩

/-- On runs where A tried to transmit at `n + 1`, `G_conf^{n+1}` with the key `K` and with the
chain key for the challenge at `n + 1` agree: the challenge at `n + 1` never happens. -/
theorem prEvent_confRun_keyAt_tx (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (n : ℕ) (K : Kae) (b : Bool)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W)
    (E : Bool → ConfHist → Prop) :
    Pr{let z ← confRun ae G len clen (keyAt n K) (fun _ => false) (n + 1) b adversary k}[
        E z.1 z.2.2 ∧ z.2.2.tx (n + 1) = true] =
      Pr{let z ← confRun ae G len clen (randUpTo n) (fun _ => false) (n + 1) b adversary k}[
        E z.1 z.2.2 ∧ z.2.2.tx (n + 1) = true] := by
  have hc (cm : ℕ → ChalMode Kae) :
      Pr{let z ← confRun ae G len clen cm (fun _ => false) (n + 1) b adversary k}[
          E z.1 z.2.2 ∧ z.2.2.tx (n + 1) = true] =
        Pr{let z ← confRun ae G len clen cm (fun _ => false) (n + 1) b adversary k}[
          (E z.1 z.2.2 ∧ z.2.2.tx (n + 1) = true) ∧
            ¬∃ p, p = n + 1 ∧ z.2.2.chal p = true] :=
    prEvent_congr_of_support _ _ _ fun z hz => by
      have hI := simulateQ_run_preserves_inv_of_query _ TxInv
        (txInv_confStep ae G len clen cm (n + 1) b) adversary _ (txInv_init _ k) z hz
      refine ⟨fun h => ⟨h, ?_⟩, And.left⟩
      rintro ⟨p, rfl, hp⟩
      rw [hI.excl _ h.2] at hp
      exact Bool.false_ne_true hp
  have hmono (cm : ℕ → ChalMode Kae) (t) (x : CState W Kae AD M Cae × ConfHist)
      (hb : ∃ p, p = n + 1 ∧ x.2.chal p = true) :
      ∀ z ∈ support ((confImpl ae G len clen cm (fun _ => false) (n + 1) b t).run x),
        ∃ p, p = n + 1 ∧ z.2.2.chal p = true := fun z hz => by
    obtain ⟨y, -, rfl⟩ := QueryImpl.mem_support_extendState_run _ confAux t x.1 x.2 hz
    obtain ⟨p, hp, hc⟩ := hb
    exact ⟨p, hp, chal_confAux t x.1 y.1 y.2 hc⟩
  rw [hc, hc]
  exact prEvent_simulateQ_run_and_not_bad_eq _ _
    (fun x : CState W Kae AD M Cae × ConfHist => ∃ p, p = n + 1 ∧ x.2.chal p = true)
    (fun t x _ q => prEvent_confImpl_and_not_chal_eq ae G len clen _ _ _ (n + 1) b (· = n + 1)
      (fun p hp => by simp only [keyAt, Function.update_of_ne hp]) t x q)
    (hmono _) (hmono _) adversary _ _

/-- On runs where A did not try to transmit at `n + 1`, `G_conf^{n+1}` with the chain key `κ` at
`n + 1` and the key `K` for the challenge at `n + 1` agrees with `G_conf^{n+1}` with the chain key
`K` at `n + 1`. -/
theorem prEvent_confRun_keyAt_not_tx (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (prg : PRGScheme W (W × Kae)) (U : ℕ → Option (W × Kae)) (len : M → ℕ) (clen : ℕ → ℕ)
    (n : ℕ) (w : W) (κ K : Kae) (b : Bool)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W)
    (E : Bool → ConfHist → Prop) :
    Pr{let z ← confRun ae (hybGen prg (Function.update U (n + 1) (some (w, κ)))) len clen
        (keyAt n K) (fun _ => false) (n + 1) b adversary k}[
        E z.1 z.2.2 ∧ ¬z.2.2.tx (n + 1) = true] =
      Pr{let z ← confRun ae (hybGen prg (Function.update U (n + 1) (some (w, K)))) len
          clen (randUpTo n) (fun _ => false) (n + 1) b adversary k}[
        E z.1 z.2.2 ∧ ¬z.2.2.tx (n + 1) = true] := by
  have hblk (G : ℕ → W → W × Kae) (cm : ℕ → ChalMode Kae) :
      Pr{let z ← confRun ae G len clen cm (fun _ => false) (n + 1) b adversary k}[
          E z.1 z.2.2 ∧ ¬z.2.2.tx (n + 1) = true] =
        Pr{let z ← confRun ae G len clen cm (fun p => decide (p = n + 1)) (n + 1) b adversary k}[
          E z.1 z.2.2 ∧ ¬z.2.2.tx (n + 1) = true] := by
    have hmono (blk : ℕ → Bool) (t) (x : CState W Kae AD M Cae × ConfHist)
        (hb : x.2.tx (n + 1) = true) :
        ∀ z ∈ support ((confImpl ae G len clen cm blk (n + 1) b t).run x),
          z.2.2.tx (n + 1) = true := fun z hz => by
      obtain ⟨y, -, rfl⟩ := QueryImpl.mem_support_extendState_run _ confAux t x.1 x.2 hz
      exact tx_confAux t x.1 y.1 y.2 hb
    exact prEvent_simulateQ_run_and_not_bad_eq _ _
      (fun x : CState W Kae AD M Cae × ConfHist => x.2.tx (n + 1) = true)
      (fun t x _ q => prEvent_confImpl_and_not_tx_eq ae G len clen cm (n + 1) b (n + 1) t x q)
      (hmono _) (hmono _) adversary _ _
  rw [hblk, hblk, ← confRun_map_normSt ae _ _ k k len clen (keyAt n K) (randUpTo n) _ (n + 1) b
    (· = n + 1) (fun q _ hq => chainKey_update_key prg U (n + 1) w κ K k hq)
    (fun q _ => chainState_update_key prg U (n + 1) w κ K k q) ?_
    (fun q hq => ⟨by simp only [hq, decide_true], le_of_eq hq⟩) adversary, prEvent_map]
  · rfl
  · intro p
    by_cases hp : p = n + 1
    · subst hp
      have := (chain_hybGen_of_some prg (Function.update U (n + 1) (some (w, K))) k
        (q := n + 1) (by omega) (u := (w, K)) (Function.update_self _ _ _)).2
      simp only [keyAt, randUpTo, Function.update_self, ChalMode.eff, this,
        show ¬n + 1 ≤ n by omega, ↓reduceIte]
    · simp only [keyAt, Function.update_of_ne hp, randUpTo]
      split_ifs
      · rfl
      · simp only [ChalMode.eff, chainKey_update_key prg U (n + 1) w κ K k hp]

/-- **Mixing the two keys.** Fix the steps `1, …, n` and the seed `w` of step `n + 1`. Then the
chain key `κ` at `n + 1` with an independent key `K` for the challenge at `n + 1`, both uniform,
gives every event of `(b, b', history)` the probability of the chain key `κ` alone. -/
theorem prEvent_mix [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    (U : ℕ → Option (W × Kae)) (len : M → ℕ) (clen : ℕ → ℕ) (n : ℕ) (w : W)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (X : Bool × Bool × ConfHist → Prop) :
    Pr{let r ← (do
        let κ ← $ᵗ Kae
        let K ← $ᵗ Kae
        let k ← $ᵗ W
        let b ← $ᵗ Bool
        let z ← confRun ae (hybGen prg (Function.update U (n + 1) (some (w, κ)))) len clen
          (keyAt n K) (fun _ => false) (n + 1) b adversary k
        pure (b, z.1, z.2.2))}[X r] =
      Pr{let r ← (do
        let κ ← $ᵗ Kae
        let k ← $ᵗ W
        let b ← $ᵗ Bool
        let z ← confRun ae (hybGen prg (Function.update U (n + 1) (some (w, κ)))) len clen
          (randUpTo n) (fun _ => false) (n + 1) b adversary k
        pure (b, z.1, z.2.2))}[X r] := by
  let P : Kae → Kae → ProbComp (Bool × Bool × ConfHist) := fun κ K => do
    let k ← $ᵗ W
    let b ← $ᵗ Bool
    let z ← confRun ae (hybGen prg (Function.update U (n + 1) (some (w, κ)))) len clen
      (keyAt n K) (fun _ => false) (n + 1) b adversary k
    pure (b, z.1, z.2.2)
  let Q : Kae → ProbComp (Bool × Bool × ConfHist) := fun κ => do
    let k ← $ᵗ W
    let b ← $ᵗ Bool
    let z ← confRun ae (hybGen prg (Function.update U (n + 1) (some (w, κ)))) len clen
      (randUpTo n) (fun _ => false) (n + 1) b adversary k
    pure (b, z.1, z.2.2)
  have hT (κ K : Kae) : Pr{let r ← P κ K}[X r ∧ r.2.2.tx (n + 1) = true] =
      Pr{let r ← Q κ}[X r ∧ r.2.2.tx (n + 1) = true] := by
    refine prEvent_bind_congr _ _ _ _ _ fun k => prEvent_bind_congr _ _ _ _ _ fun b => ?_
    simp only [bind_pure_comp, prEvent_map]
    exact prEvent_confRun_keyAt_tx ae _ len clen n K b adversary k fun b' h => X (b, b', h)
  have hN (κ K : Kae) : Pr{let r ← P κ K}[X r ∧ ¬r.2.2.tx (n + 1) = true] =
      Pr{let r ← Q K}[X r ∧ ¬r.2.2.tx (n + 1) = true] := by
    refine prEvent_bind_congr _ _ _ _ _ fun k => prEvent_bind_congr _ _ _ _ _ fun b => ?_
    simp only [bind_pure_comp, prEvent_map]
    exact prEvent_confRun_keyAt_not_tx ae prg U len clen n w κ K b adversary k
      fun b' h => X (b, b', h)
  change Pr{let r ← (do let κ ← $ᵗ Kae; let K ← $ᵗ Kae; P κ K)}[X r] =
    Pr{let r ← (do let κ ← $ᵗ Kae; Q κ)}[X r]
  rw [prEvent_eq_prEvent_and_add_prEvent_and_not _ _ fun r => r.2.2.tx (n + 1) = true]
  conv_rhs => rw [prEvent_eq_prEvent_and_add_prEvent_and_not _ _ fun r => r.2.2.tx (n + 1) = true]
  congr 1
  · refine (prEvent_bind_congr _ _ _ _ _ fun κ => ?_)
    refine (prEvent_bind_congr _ _ (fun _ => Q κ) _ _ fun K => hT κ K).trans ?_
    exact (EvalDistEq.bind_const (spec := unifSpec) _ _).prEvent_eq _
  · refine (prEvent_bind_congr _ _ (fun _ => do let K ← $ᵗ Kae; Q K) _ _ fun κ =>
      prEvent_bind_congr _ _ _ _ _ fun K => hN κ K).trans ?_
    exact (EvalDistEq.bind_const (spec := unifSpec) _ _).prEvent_eq _

/-- **The hybrid `G'_{n+1}`.** `G_{n+1,n}^s`, but the challenge at `n + 1` is encrypted under an
independent uniform key `K` (`keyAt`). It is the real world of the AEAD reduction `E'_{n+1}`. -/
def confHybKey [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (s n : ℕ) : ProbComp (Bool × Bool × ConfHist) := do
  let K ← $ᵗ Kae
  let U ← sampleTab (n + 1)
  let k ← $ᵗ W
  let b ← $ᵗ Bool
  let z ← confRun ae (hybGen prg U) len clen (keyAt n K) (fun _ => false) s b adversary k
  pure (b, z.1, z.2.2)

/-- **An independent key for the challenge at `n + 1`.** `G'_{n+1}` and `G_{n+1,n}` give every
event of `(b, b', history)` the same probability in `G_conf^{n+1}`. -/
theorem prEvent_confHybKey_eq [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (n : ℕ) (X : Bool × Bool × ConfHist → Prop) :
    Pr{let r ← confHybKey ae prg len clen adversary (n + 1) n}[X r] =
      Pr{let r ← confHyb ae prg len clen adversary (n + 1) (n + 1) n}[X r] := by
  simp only [confHybKey, confHyb, sampleTab, SampleableType.uniformSample_prod_eq_bind, bind_assoc,
    pure_bind]
  rw [(EvalDistEq.bind_bind_swap (spec := unifSpec) _ _ _).prEvent_eq]
  refine prEvent_bind_congr _ _ _ _ _ fun U => ?_
  rw [(EvalDistEq.bind_bind_swap (spec := unifSpec) _ _ _).prEvent_eq]
  refine prEvent_bind_congr _ _ _ _ _ fun w => ?_
  rw [(EvalDistEq.bind_bind_swap (spec := unifSpec) _ _ _).prEvent_eq]
  exact prEvent_mix ae prg U len clen n w adversary X

end FromAEADPRG





end FSAEADScheme
