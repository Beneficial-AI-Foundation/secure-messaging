/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Hybrid

/-!
# FS-AEAD from AEAD and PRG — the confidentiality game

Step 4 of the proof of Theorem 5 of [ACD19] bounds `|Pr_{G_rej}[b = b'] - 1/2|`. Its hybrids
change how `O-Chall-A` encrypts, and its reductions stop when a corruption reveals a position
below the hybrid step. This file defines the game `G_conf^s` (`confImplWith`) for the construction
`fromAEADChain ae G`, with `O-Deliver-B^lk` for `O-Deliver-B` and `O-Inject-B^rej` for
`O-Inject-B`, and three more parameters:
- a challenge mode `cm p` for every position `p` (`ChalMode`): `O-Chall-A` at `p` encrypts under
  the chain key (`real`), under a given key (`key K`), or outputs a uniform ciphertext of length
  `clen(|m|)` (`rand`);
- a set `blk` of positions where `O-Transmit-A` returns `⊥` and does nothing;
- a stop position `s`: `O-Corr-A^s` (`oracleCorrALow`) and `O-Corr-B^s` (`oracleCorrBLow`) set
  `end` and return `⊥` if the call would reveal a position below `s`.

The history (`ConfHist`) records the smallest position `m` that a corruption reveals in
`G_conf^0` (`expo`), the positions of the challenges, and the positions of the attempts of
`O-Transmit-A`. `O-Corr-A` reveals A's position `i_A`, and `O-Corr-B` reveals `min(i_A, i_B)`.
A call that the cutoff `s` blocks is recorded too.

- `fsaeadRejLookupImpl_eq_confImplWith`: `G_conf^0` with real challenges and no blocked
  position is `G_rej` with `O-Deliver-B^lk`.
- `prEvent_confRun_eq_low`: `G_conf^0` and `G_conf^s` give an event the same probability if the
  event implies that no corruption revealed a position below `s`.

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Figure 5, Figure 6, Theorem 5.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal OracleComp.ProgramLogic.Relational

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type}

/-! ## The oracles -/

/-- How `O-Chall-A` encrypts the challenge at a position. -/
inductive ChalMode (Kae : Type) where
  /-- Under the key of the chain. -/
  | real
  /-- Under the key `K`. -/
  | key (K : Kae)
  /-- A uniform ciphertext of length `clen(|m|)`. -/
  | rand

/-- A's step with challenge mode `c`: A moves as in `FS-Send`, and the ciphertext at position
`i_A + 1` depends on `c`. The length of a uniform ciphertext is `clen(len(m))`. -/
def chalSend [LenSampleable Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (c : ChalMode Kae) (vA : SendState W)
    (a : AD) (m : M) : ProbComp (SendState W × (ℕ × Cae)) :=
  match c with
  | .real => pure (send ae G vA a m)
  | .key K => pure ((send ae G vA a m).1, (vA.iA + 1, ae.encrypt K (vA.iA + 1, a) m))
  | .rand => (fun e => ((send ae G vA a m).1, (vA.iA + 1, e))) <$>
      LenSampleable.unifOfLen (clen (len m))

/-- **O-Transmit-A^blk(a, m)**. `O-Transmit-A`, but at a position in `blk` it returns `⊥` and
does nothing.
```text
O-Transmit-A^blk(a, m):
  req i_A + 1 ∉ blk
  i_A++
  (v_A, e) ← FS-Send(v_A, a, m)
  record(good, a, m, e)
  return e
``` -/
def oracleTransmitBlk (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (blk : ℕ → Bool) :
    QueryImpl (AD × M →ₒ Option (ℕ × Cae))
      (GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :=
  fun (a, m) => do
    let st ← get
    if st.end_ || blk (st.iA + 1) then return none
    let (vA, e) := send ae G st.vA a m
    set ({ st with vA, iA := st.iA + 1 }.record false a m e)
    return some e

/-- **O-Chall-A^cm(a, m₀, m₁)**. `O-Chall-A`, with the ciphertext at position `i_A + 1` from the
challenge mode `cm(i_A + 1)` (`chalSend`).
```text
O-Chall-A^cm(a, m₀, m₁):
  req ¬corrA and |m₀| = |m₁|
  (v_A, e) ← chalSend(cm(i_A + 1), v_A, a, m_b)
  i_A++
  record(chall, a, m_b, e)
  return e
``` -/
def oracleChallMode [LenSampleable Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (b : Bool) :
    QueryImpl (AD × M × M →ₒ Option (ℕ × Cae))
      (GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :=
  fun (a, m₀, m₁) => do
    let st ← get
    if st.end_ || st.corrA || len m₀ ≠ len m₁ then return none
    let m := if b then m₁ else m₀
    let r ← (chalSend ae G len clen (cm (st.iA + 1)) st.vA a m : ProbComp _)
    set ({ st with vA := r.1, iA := st.iA + 1 }.record true a m r.2)
    return some r.2

/-- **O-Corr-B^s**. `O-Corr-B`, but if `min(i_A, i_B) < s` the oracle returns `⊥`. It sets `end`
in both cases.
```text
O-Corr-B^s:
  req chall = ∅
  end ← true
  if min(i_A, i_B) < s: return ⊥
  return (v_A, v_B)
``` -/
def oracleCorrBLow (W Kae AD M Cae : Type) (s : ℕ) :
    QueryImpl (Unit →ₒ Option (SendState W × RecvState W Kae))
      (GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :=
  fun () => do
    let st ← get
    if st.end_ || st.chall ≠ ∅ then return none
    set { st with end_ := true }
    if min st.iA st.vB.iB < s then return none
    return some (st.vA, st.vB)

variable [DecidableEq AD] [DecidableEq Cae]

/-- The oracles of `G_conf^s` for `fromAEADChain ae G`, with challenge modes `cm`, blocked
positions `blk` and bit `b`. -/
def confImplWith [LenSampleable Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae)
    (blk : ℕ → Bool) (s : ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :=
  oracleUnif (SendState W) (RecvState W Kae) AD M (ℕ × Cae)
    + oracleTransmitBlk ae G blk
    + oracleChallMode ae G len clen cm b
    + oracleCorrALow (SendState W) (RecvState W Kae) AD M (ℕ × Cae) s
    + oracleCorrBLow W Kae AD M Cae s
    + oracleDeliverBLookup (AD := AD) (M := M) (Cae := Cae) G
    + oracleInjectBRej (fromAEADChain ae G) Prod.fst false

/-! ## The history -/

/-- The history of a run of `G_conf^s`. -/
structure ConfHist where
  /-- The smallest position that a call of `O-Corr-A` or `O-Corr-B` before `end` reveals in
  `G_conf^0`. A call that the cutoff `s` blocks is recorded too. -/
  expo : Option ℕ
  /-- The positions of the challenges. -/
  chal : ℕ → Bool
  /-- The positions of the calls of `O-Transmit-A` before `end`. -/
  tx : ℕ → Bool

/-- The empty history. -/
def ConfHist.init : ConfHist := ⟨none, fun _ => false, fun _ => false⟩

/-- `expo` after a call that reveals position `r`. -/
def ConfHist.reveal (h : ConfHist) (r : ℕ) : ConfHist :=
  { h with expo := some (h.expo.elim r (min · r)) }

omit [DecidableEq AD] [DecidableEq Cae] in
/-- The history update of a query `t` from the state `st` with answer `u`. -/
def confAux : (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain) →
    CState W Kae AD M Cae → (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Range t →
    CState W Kae AD M Cae → ConfHist → ConfHist
  | .inl (.inl (.inl (.inl (.inl (.inr _))))), st, _, _, h =>
    if st.end_ then h else { h with tx := fun p => h.tx p || decide (p = st.iA + 1) }
  | .inl (.inl (.inl (.inl (.inr _)))), st, u, _, h =>
    if u.isSome then { h with chal := fun p => h.chal p || decide (p = st.iA + 1) } else h
  | .inl (.inl (.inl (.inr ()))), st, _, _, h => if st.end_ then h else h.reveal st.iA
  | .inl (.inl (.inr ())), st, _, _, h =>
    if st.end_ || st.chall ≠ ∅ then h else h.reveal (min st.iA st.vB.iB)
  | _, _, _, _, h => h

/-- `G_conf^s` with its history. -/
def confImpl [LenSampleable Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae)
    (blk : ℕ → Bool) (s : ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (StateT (CState W Kae AD M Cae × ConfHist) ProbComp) :=
  (confImplWith ae G len clen cm blk s b).extendState confAux

/-- The run of `G_conf^s` for `fromAEADChain ae G` from the initial state for the key `k`. -/
def confRun [LenSampleable Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae)
    (blk : ℕ → Bool) (s : ℕ) (b : Bool)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W) :
    ProbComp (Bool × (CState W Kae AD M Cae × ConfHist)) :=
  (simulateQ (confImpl ae G len clen cm blk s b) adversary).run
    (.init (fromAEADChain ae G) k, .init)

/-! ## The real game -/

omit [DecidableEq AD] [DecidableEq Cae] in
/-- `O-Transmit-A^blk` with no blocked position is `O-Transmit-A`. -/
theorem oracleTransmitBlk_false (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) :
    oracleTransmitBlk ae G (fun _ => false) = oracleTransmitA (fromAEADChain ae G) := by
  funext ⟨a, m⟩
  simp only [oracleTransmitBlk, oracleTransmitA, Bool.or_false]
  rfl

omit [DecidableEq AD] [DecidableEq Cae] in
/-- `O-Chall-A^cm` with real challenges is `O-Chall-A`. -/
theorem oracleChallMode_real [LenSampleable Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (b : Bool) :
    oracleChallMode ae G len clen (fun _ => .real) b = oracleChallA (fromAEADChain ae G) len b := by
  funext ⟨a, m₀, m₁⟩
  refine StateT.ext fun st => ?_
  simp only [oracleChallMode, oracleChallA, chalSend, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · rfl
  all_goals
    simp only [liftM, StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
      StateT.run_set, StateT.run_pure]
    rfl

omit [DecidableEq AD] [DecidableEq Cae] in
/-- `O-Corr-B^0` is `O-Corr-B`. -/
theorem oracleCorrBLow_zero :
    oracleCorrBLow W Kae AD M Cae 0 =
      oracleCorrB (SendState W) (RecvState W Kae) AD M (ℕ × Cae) := by
  funext u
  refine StateT.ext fun st => ?_
  simp only [oracleCorrBLow, oracleCorrB, StateT.run_bind, StateT.run_get, pure_bind,
    Nat.not_lt_zero, ↓reduceIte]

/-- `G_conf^0` with real challenges and no blocked position is `G_rej` with `O-Deliver-B^lk`. -/
theorem fsaeadRejLookupImpl_eq_confImplWith [LenSampleable Cae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) (len : M → ℕ)
    (clen : ℕ → ℕ) (b : Bool) :
    fsaeadRejLookupImpl ae G len b =
      confImplWith ae G len clen (fun _ => .real) (fun _ => false) 0 b := by
  rw [confImplWith, oracleTransmitBlk_false, oracleChallMode_real, oracleCorrALow_zero,
    oracleCorrBLow_zero]
  rfl

/-- Let `ae` be correct. Then `G_rej` for the construction `fromAEADPRG ae prg` returns `b = b'`
with the probability that `G_conf^0` with real challenges, for the chain `G_i = prg.gen`, gives
`b = b'`. -/
theorem prEvent_securityExpRej_eq_confRun [SampleableType W] [LenSampleable Cae]
    {ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae} (hae : ae.Correct)
    (prg : PRGScheme W (W × Kae)) (len : M → ℕ) (clen : ℕ → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    Pr{let x ← securityExpRej (fromAEADPRG ae prg) len Prod.fst adversary}[x = true] =
      Pr{let r ← (do
        let k ← $ᵗ W
        let b ← $ᵗ Bool
        let z ← confRun ae (fun _ => prg.gen) len clen (fun _ => .real) (fun _ => false) 0 b
          adversary k
        pure (b, z.1, z.2.2))}[r.1 = r.2.1] := by
  rw [securityExpRej, prEvent_map, fromAEADPRG, gameRun_rej_eq_lookup hae, gameRun]
  refine prEvent_bind_congr _ _ _ _ _ fun k => prEvent_bind_congr _ _ _ _ _ fun b => ?_
  rw [prEvent_map, fsaeadRejLookupImpl_eq_confImplWith ae _ len clen b, confRun, confImpl,
    ← extendState_run_proj_eq _ confAux adversary _ ConfHist.init, prEvent_map, bind_pure_comp,
    prEvent_map]
  refine prEvent_congr _ _ _ fun z => ?_
  simp only [Prod.map_fst, id_eq, beq_iff_eq]

/-! ## Stopping below `s` -/

/-- A corruption reveals a position below `s` in `G_conf^0`. -/
def LowExpo (s : ℕ) (h : ConfHist) : Prop := ∃ r, h.expo = some r ∧ r < s

omit [DecidableEq AD] [DecidableEq Cae] in
/-- `reveal` keeps `LowExpo s`. -/
theorem lowExpo_reveal {s r : ℕ} {h : ConfHist} (hb : LowExpo s h) : LowExpo s (h.reveal r) := by
  obtain ⟨t, ht, hts⟩ := hb
  exact ⟨min t r, by simp only [ConfHist.reveal, ht, Option.elim_some], by omega⟩

omit [DecidableEq AD] [DecidableEq Cae] in
/-- A reveal of a position below `s` gives `LowExpo s`. -/
theorem lowExpo_reveal_of_lt {s r : ℕ} (h : ConfHist) (hr : r < s) : LowExpo s (h.reveal r) := by
  refine ⟨h.expo.elim r (min · r), rfl, ?_⟩
  cases h.expo <;> simp only [Option.elim_none, Option.elim_some] <;> omega

omit [DecidableEq AD] [DecidableEq Cae] in
/-- The history update keeps `LowExpo s`. -/
theorem lowExpo_confAux {s : ℕ}
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (st : CState W Kae AD M Cae) (u) (st' : CState W Kae AD M Cae) {h : ConfHist}
    (hb : LowExpo s h) : LowExpo s (confAux t st u st' h) := by
  rcases t with ((((((n | q) | q) | u) | u) | q) | q)
  any_goals exact hb
  all_goals simp only [confAux]; split_ifs <;> first | exact hb | exact lowExpo_reveal hb

variable [LenSampleable Cae]

/-- From every state, `O-Corr-A` and `O-Corr-A^s` with the history give every event the same
probability away from `LowExpo s`. -/
theorem prEvent_confCorrA_and_not_lowExpo_eq (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae)
    (blk : ℕ → Bool) (b : Bool) (s : ℕ) (x : CState W Kae AD M Cae × ConfHist)
    (q : Option (SendState W) × (CState W Kae AD M Cae × ConfHist) → Prop) :
    Pr{let z ← (confImpl ae G len clen cm blk 0 b fsaeadSpec.OCorrA).run x}[
        q z ∧ ¬LowExpo s z.2.2] =
      Pr{let z ← (confImpl ae G len clen cm blk s b fsaeadSpec.OCorrA).run x}[
        q z ∧ ¬LowExpo s z.2.2] := by
  obtain ⟨st, h⟩ := x
  simp only [confImpl, confImplWith, QueryImpl.extendState_apply, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr]
  by_cases hend : st.end_ = true
  · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, ↓reduceIte,
      StateT.run_pure]
  have hbad (y : Option (SendState W) × (CState W Kae AD M Cae × ConfHist))
      (hy : LowExpo s y.2.2) :
      Pr{let z ← (pure y : ProbComp _)}[q z ∧ ¬LowExpo s z.2.2] = 0 := by
    classical
    simp only [prEvent_pure, hy, not_true_eq_false, and_false, ↓reduceIte]
  by_cases hlt : st.iA < s
  · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, hlt,
      Bool.false_eq_true, ↓reduceIte, Nat.not_lt_zero, StateT.run_set, StateT.run_pure]
    erw [hbad _ ?_, hbad _ ?_] <;>
      simpa only [confAux, hend, Bool.false_eq_true, ↓reduceIte] using lowExpo_reveal_of_lt h hlt
  · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, hlt,
      Bool.false_eq_true, ↓reduceIte, Nat.not_lt_zero]

/-- From every state, `O-Corr-B` and `O-Corr-B^s` with the history give every event the same
probability away from `LowExpo s`. -/
theorem prEvent_confCorrB_and_not_lowExpo_eq (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae)
    (blk : ℕ → Bool) (b : Bool) (s : ℕ) (x : CState W Kae AD M Cae × ConfHist)
    (q : Option (SendState W × RecvState W Kae) × (CState W Kae AD M Cae × ConfHist) → Prop) :
    Pr{let z ← (confImpl ae G len clen cm blk 0 b fsaeadSpec.OCorrB).run x}[
        q z ∧ ¬LowExpo s z.2.2] =
      Pr{let z ← (confImpl ae G len clen cm blk s b fsaeadSpec.OCorrB).run x}[
        q z ∧ ¬LowExpo s z.2.2] := by
  obtain ⟨st, h⟩ := x
  simp only [confImpl, confImplWith, QueryImpl.extendState_apply, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr]
  by_cases hend : st.end_ = true ∨ st.chall ≠ ∅
  · have hg : (st.end_ || decide (st.chall ≠ ∅)) = true := by
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using hend
    simp only [oracleCorrBLow, StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte,
      StateT.run_pure]
  have hg : (st.end_ || decide (st.chall ≠ ∅)) = false := by
    simp only [not_or, Bool.not_eq_true, not_not] at hend
    simp only [hend.1, hend.2, ne_eq, not_true_eq_false, decide_false, Bool.or_self]
  have hbad (y : Option (SendState W × RecvState W Kae) × (CState W Kae AD M Cae × ConfHist))
      (hy : LowExpo s y.2.2) :
      Pr{let z ← (pure y : ProbComp _)}[q z ∧ ¬LowExpo s z.2.2] = 0 := by
    classical
    simp only [prEvent_pure, hy, not_true_eq_false, and_false, ↓reduceIte]
  by_cases hlt : min st.iA st.vB.iB < s
  · simp only [oracleCorrBLow, StateT.run_bind, StateT.run_get, pure_bind, hg, hlt,
      Bool.false_eq_true, ↓reduceIte, Nat.not_lt_zero, StateT.run_set, StateT.run_pure]
    erw [hbad _ ?_, hbad _ ?_] <;>
      simpa only [confAux, hg, Bool.false_eq_true, ↓reduceIte] using lowExpo_reveal_of_lt h hlt
  · simp only [oracleCorrBLow, StateT.run_bind, StateT.run_get, pure_bind, hg, hlt,
      Bool.false_eq_true, ↓reduceIte, Nat.not_lt_zero]

/-- **From `G_conf^0` to `G_conf^s`.** Let `X` be an event of the run that implies that no
corruption revealed a position below `s`. Then `G_conf^0` and `G_conf^s` give `X` the same
probability: the two games differ only at a call of `O-Corr-A` or `O-Corr-B` that reveals a
position below `s`. -/
theorem prEvent_confRun_eq_low (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae)
    (blk : ℕ → Bool) (b : Bool) (s : ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W)
    (X : Bool × (CState W Kae AD M Cae × ConfHist) → Prop) (hX : ∀ z, X z → ¬LowExpo s z.2.2) :
    Pr{let z ← confRun ae G len clen cm blk 0 b adversary k}[X z] =
      Pr{let z ← confRun ae G len clen cm blk s b adversary k}[X z] := by
  have hnot (s' : ℕ) : Pr{let z ← confRun ae G len clen cm blk s' b adversary k}[X z] =
      Pr{let z ← confRun ae G len clen cm blk s' b adversary k}[X z ∧ ¬LowExpo s z.2.2] :=
    prEvent_congr _ _ _ fun z => ⟨fun h => ⟨h, hX z h⟩, And.left⟩
  rw [hnot 0, hnot s]
  refine prEvent_simulateQ_run_and_not_bad_eq (confImpl ae G len clen cm blk 0 b)
    (confImpl ae G len clen cm blk s b) (fun x : CState W Kae AD M Cae × ConfHist =>
      LowExpo s x.2) ?_ ?_ ?_ adversary _ X
  · intro t x _ q
    rcases t with ((((((n | q') | q') | u) | u) | q') | q')
    any_goals rfl
    · exact prEvent_confCorrA_and_not_lowExpo_eq ae G len clen cm blk b s x q
    · exact prEvent_confCorrB_and_not_lowExpo_eq ae G len clen cm blk b s x q
  all_goals
    intro t x hb z hz
    obtain ⟨y, -, rfl⟩ := QueryImpl.mem_support_extendState_run _ confAux t x.1 x.2 hz
    exact lowExpo_confAux t x.1 y.1 y.2 hb

end FromAEADPRG

end FSAEADScheme
