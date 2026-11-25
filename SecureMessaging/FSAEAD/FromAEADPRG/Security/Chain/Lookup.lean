/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Correctness
public import SecureMessaging.FSAEAD.Security.Reject

/-!
# FS-AEAD from AEAD and PRG — delivery by lookup

Step 2 of the proof of Theorem 5 of [ACD19] for the construction `fromAEADChain ae G`.

`O-Deliver-B^lk` (`oracleDeliverBLookup`) delivers an honest ciphertext without `Dec`. It finds
the record `(i, a, m, e)` in `trans`, moves B's state with `rcvKey` (the part of `FS-Rcv` before
decryption), and returns `(i, ⊥)` for a challenge and `(i, m)` otherwise. The reductions of the
later steps need it, because they cannot decrypt under an AEAD key that they do not hold.

Let `ae` be correct. In a state that satisfies the invariant `GameInv` of the correctness proof
with `win = false`, `O-Deliver-B^nd` and `O-Deliver-B^lk` agree
(`oracleDeliverBNoWin_run_eq_lookup`). Then:
- `gameRun_rej_eq_lookup`: `G_rej` never sets `win`, so the two oracles agree in every
  reachable state, and `G_rej` with `O-Deliver-B^lk` is `G_rej`.
- `prEvent_gameRun_mon_and_not_win_eq_lookup`, `prEvent_gameRun_mon_win_eq_lookup`: in
  `fs-aead-nd` the two oracles agree only until the first win. After a win, B can consume a
  position before A sends at it, and then `FS-Rcv` rejects A's ciphertext at that position. So
  `fs-aead-nd` and `fs-aead-nd` with `O-Deliver-B^lk` are identical until `win`.

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

/-! ## The index of `FS-Rcv` -/

/-- `FS-Rcv` outputs the index of the ciphertext `(i, e)`. -/
theorem rcvIndex_fromAEADChain (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) :
    RcvIndex (fromAEADChain ae G) Prod.fst := by
  rintro vB a ⟨i, e⟩ vB' i' m' h
  exact (rcvKey_of_rcv_eq_some ae G h).choose_spec.2.1

/-! ## The lookup oracle -/

variable [DecidableEq AD] [DecidableEq Cae]

/-- **O-Deliver-B^lk(a, e)**. `O-Deliver-B^nd` without `Dec`: B's state moves as in `FS-Rcv`, and
the oracle returns the recorded index and message.
```text
O-Deliver-B^lk(a, e):
  req (i, a, m, e) ∈ trans, with the smallest such i
  r ← rcvKey(v_B, i)
  if r ≠ ⊥: (v_B, K) ← r
  c ← (i ∈ chall)
  delete(i)
  if c: return (i, ⊥)
  return (i, m)
``` -/
def oracleDeliverBLookup (G : ℕ → W → W × Kae) :
    QueryImpl (AD × (ℕ × Cae) →ₒ Option (ℕ × Option M))
      (GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :=
  fun (a, e) => do
    let st ← get
    if st.end_ then return none
    let some (i, _, m, _) := st.findTrans a e | return none
    let vB := ((rcvKey G st.vB i).map Prod.fst).getD st.vB
    set ({ st with vB }.delete i)
    return some (i, if i ∈ st.chall then none else some m)

/-- The oracles of `fs-aead-nd` with `O-Deliver-B^lk` for `O-Deliver-B`. -/
def fsaeadMonLookupImpl (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :=
  fsaeadImplWith (fromAEADChain ae G) len b (oracleDeliverBLookup G)
    (oracleInjectB (fromAEADChain ae G))

/-- The oracles of `G_rej` with `O-Deliver-B^lk` for `O-Deliver-B`. -/
def fsaeadRejLookupImpl (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :=
  fsaeadImplWith (fromAEADChain ae G) len b (oracleDeliverBLookup G)
    (oracleInjectBRej (fromAEADChain ae G) Prod.fst false)

/-- `O-Deliver-B^lk` keeps `win` and `end`. -/
theorem oracleDeliverBLookup_flags (G : ℕ → W → W × Kae) (q : AD × (ℕ × Cae))
    (st : GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    ∀ z ∈ support ((oracleDeliverBLookup G q).run st), z.2.win = st.win ∧ z.2.end_ = st.end_ := by
  intro z hz
  obtain ⟨a, e⟩ := q
  simp only [oracleDeliverBLookup, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, rfl⟩
  rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
  · simp only [hf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, rfl⟩
  · simp only [hf, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, rfl⟩

/-! ## Agreement under the invariant -/

variable {ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae} {G : ℕ → W → W × Kae} {k : W}

/-- Let `ae` be correct, and let `st` satisfy `GameInv` with `win = false`. Then
`O-Deliver-B^nd` and `O-Deliver-B^lk` agree on `st`. -/
theorem oracleDeliverBNoWin_run_eq_lookup (hae : ae.Correct)
    {st : GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae)} (hinv : GameInv ae G k st)
    (hw : st.win = false) (q : AD × (ℕ × Cae)) :
    (oracleDeliverBNoWin (fromAEADChain ae G) q).run st = (oracleDeliverBLookup G q).run st := by
  obtain ⟨a, e⟩ := q
  simp only [oracleDeliverBNoWin, oracleDeliverBLookup, StateT.run_bind, StateT.run_get,
    pure_bind]
  split_ifs
  · rfl
  rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
  · rfl
  obtain ⟨hmem, rfl, rfl⟩ := GameState.findTrans_spec hf
  obtain ⟨-, -, he⟩ := hinv.trans_honest _ hmem
  simp only at he
  obtain ⟨vB, hr⟩ := exists_rcv_eq_some ae G hinv.vB (hinv.trans_key hw _ hmem).symm
    (hae (chainKey G k i) (i, a') m)
  rw [← he] at hr
  obtain ⟨K, hk, -, -⟩ := rcvKey_of_rcv_eq_some ae G (he ▸ hr)
  simp only [fromAEADChain, hr, hk, Option.map_some, Option.getD_some, StateT.run_bind,
    StateT.run_set, StateT.run_pure, pure_bind]

/-! ## The invariant in the games -/

/-- `O-Deliver-B^nd` keeps `GameInv`. -/
theorem gameInv_deliverBNoWin {st : GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae)}
    (hinv : GameInv ae G k st) (q : AD × (ℕ × Cae)) {z}
    (hz : z ∈ support ((oracleDeliverBNoWin (fromAEADChain ae G) q).run st)) :
    GameInv ae G k z.2 := by
  obtain ⟨a, c⟩ := q
  simp only [oracleDeliverBNoWin, StateT.run_bind, StateT.run_get, pure_bind] at hz
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
  · simp only [hf, fromAEADChain, hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hinv
  · obtain ⟨hii, -⟩ := rcv_some ae G hinv.vB hr
    subst hii
    simp only [hf, fromAEADChain, hr, StateT.run_bind, StateT.run_set, StateT.run_pure,
      pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact gameInv_rcv hinv hr st.win fun hw => ⟨hw, .inl hiA⟩

/-- `O-Inject-B^rej` keeps `GameInv`. -/
theorem gameInv_injectBRej {st : GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae)}
    (hinv : GameInv ae G k st) (mon : Bool) (q : AD × (ℕ × Cae)) {z}
    (hz : z ∈ support ((oracleInjectBRej (fromAEADChain ae G) Prod.fst mon q).run st)) :
    GameInv ae G k z.2 := by
  obtain ⟨a, ⟨j, e⟩⟩ := q
  simp only [oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with h₁ h₂ h₃
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hinv
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact gameInv_win hinv
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hinv
  rcases hr : rcv ae G st.vB a (j, e) with _ | ⟨vB, i', m'⟩
  · simp only [fromAEADChain, hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hinv
  · obtain ⟨rfl, -⟩ := rcv_some ae G hinv.vB hr
    simp only [fromAEADChain, hr, StateT.run_bind, StateT.run_set, StateT.run_pure,
      pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp only [Bool.not_eq_true', Bool.not_eq_false] at h₂
    exact gameInv_rcv hinv hr st.win fun hw => ⟨hw, .inr (hinv.comp_corrA _ h₂)⟩

omit [DecidableEq AD] [DecidableEq Cae] in
/-- Let `deliver` and `inject` keep `GameInv`. Then the oracles of the game keep it. -/
theorem gameInv_implWith
    {deliver : QueryImpl (AD × (ℕ × Cae) →ₒ Option (ℕ × Option M))
      (GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae))}
    {inject : QueryImpl (AD × (ℕ × Cae) →ₒ Option (ℕ × M))
      (GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae))}
    (hd : ∀ q st, GameInv ae G k st → ∀ z ∈ support ((deliver q).run st), GameInv ae G k z.2)
    (hi : ∀ q st, GameInv ae G k st → ∀ z ∈ support ((inject q).run st), GameInv ae G k z.2)
    (len : M → ℕ) (b : Bool) :
    ∀ t st, GameInv ae G k st →
      ∀ z ∈ support ((fsaeadImplWith (fromAEADChain ae G) len b deliver inject t).run st),
        GameInv ae G k z.2 := by
  classical
  intro t st hinv z hz
  rcases t with ((t | q) | q)
  · exact gameInv_step hinv len b (.inl (.inl t)) hz
  · exact hd q st hinv z hz
  · exact hi q st hinv z hz

/-! ## `G_rej` with lookup -/

/-- Let `ae` be correct. Then `G_rej` with `O-Deliver-B^lk` is `G_rej`: the runs from the
initial state for `k` are equal. -/
theorem simulateQ_rej_run_eq_lookup (hae : ae.Correct) (len : M → ℕ)
    (b : Bool) (k : W)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    (simulateQ (fsaeadRejImpl (fromAEADChain ae G) len Prod.fst false b) adversary).run
        (.init (fromAEADChain ae G) k) =
      (simulateQ (fsaeadRejLookupImpl ae G len b) adversary).run
        (.init (fromAEADChain ae G) k) := by
  have h := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (fsaeadRejImpl (fromAEADChain ae G) len Prod.fst false b) (fsaeadRejLookupImpl ae G len b)
    (fun st => GameInv ae G k st ∧ st.win = false) id
    (fun t st hst z hz =>
      ⟨gameInv_implWith (fun q st hinv z hz => gameInv_deliverBNoWin hinv q hz)
          (fun q st hinv z hz => gameInv_injectBRej hinv false q hz) len b t st hst.1 z hz,
        fsaeadImplWith_preservesWin _ len b false
          (fun q st hw z hz => (oracleDeliverBNoWin_win _ q st z hz).trans hw)
          (fun q st hw z hz => (oracleInjectBRej_false_win _ _ q st z hz).trans hw) t st
          hst.2 z hz⟩)
    (fun t st hst => by
      simp only [Prod.map_id, id_map, id_eq]
      rcases t with ((t | q) | q)
      · rfl
      · exact oracleDeliverBNoWin_run_eq_lookup hae hst.1 hst.2 q
      · rfl)
    adversary _ ⟨gameInv_init, rfl⟩
  simpa only [Prod.map_id, id_map, id_eq] using h

/-- Let `ae` be correct. Then `G_rej` with `O-Deliver-B^lk` has the same runs as `G_rej`. -/
theorem gameRun_rej_eq_lookup (hae : ae.Correct) (len : M → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    [SampleableType W] :
    gameRun (fromAEADChain ae G) (fsaeadRejImpl (fromAEADChain ae G) len Prod.fst false)
        adversary =
      gameRun (fromAEADChain ae G) (fsaeadRejLookupImpl ae G len) adversary := by
  unfold gameRun
  simp only [simulateQ_rej_run_eq_lookup hae]

/-! ## `fs-aead-nd` with lookup, until `win` -/

/-- `win`, or `GameInv`: the invariant of `fs-aead-nd` and of `fs-aead-nd` with
`O-Deliver-B^lk`. -/
def MonInv (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) (k : W)
    (st : GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) : Prop :=
  st.win = true ∨ GameInv ae G k st

/-- The hypotheses of the identical-until-bad lemmas for `fs-aead-nd` and `fs-aead-nd` with
`O-Deliver-B^lk`, with invariant `MonInv` and bad flag `win`. -/
theorem monLookup_untilBad (hae : ae.Correct) (len : M → ℕ) (b : Bool) :
    let impl₁ := fsaeadNoDeliverWinImpl (fromAEADChain ae G) len b
    let impl₂ := fsaeadMonLookupImpl ae G len b
    (∀ t st, MonInv ae G k st → ∀ z ∈ support ((impl₁ t).run st), MonInv ae G k z.2) ∧
    (∀ t st, MonInv ae G k st → ∀ z ∈ support ((impl₂ t).run st), MonInv ae G k z.2) ∧
    (∀ t st, MonInv ae G k st → ¬st.win = true →
      ∀ q : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Range t ×
          GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae) → Prop,
        Pr{let z ← (impl₁ t).run st}[q z ∧ ¬z.2.win = true] =
          Pr{let z ← (impl₂ t).run st}[q z ∧ ¬z.2.win = true]) ∧
    (∀ t st, MonInv ae G k st → st.win = true →
      ∀ z ∈ support ((impl₁ t).run st), z.2.win = true) ∧
    (∀ t st, MonInv ae G k st → st.win = true →
      ∀ z ∈ support ((impl₂ t).run st), z.2.win = true) := by
  classical
  intro impl₁ impl₂
  have hwin₁ : ∀ t st, st.win = true → ∀ z ∈ support ((impl₁ t).run st), z.2.win = true :=
    fsaeadImplWith_preservesWin _ len b true
      (fun q st hw z hz => (oracleDeliverBNoWin_win _ q st z hz).trans hw)
      (oracleInjectB_preservesWin _)
  have hwin₂ : ∀ t st, st.win = true → ∀ z ∈ support ((impl₂ t).run st), z.2.win = true :=
    fsaeadImplWith_preservesWin _ len b true
      (fun q st hw z hz => (oracleDeliverBLookup_flags G q st z hz).1.trans hw)
      (oracleInjectB_preservesWin _)
  have hinj : ∀ q st, GameInv ae G k st →
      ∀ z ∈ support ((oracleInjectB (fromAEADChain ae G) q).run st), GameInv ae G k z.2 :=
    fun q st hinv z hz => gameInv_step hinv len b (.inr q) hz
  have hinv₁ : ∀ t st, GameInv ae G k st →
      ∀ z ∈ support ((impl₁ t).run st), GameInv ae G k z.2 :=
    gameInv_implWith (fun q st hinv z hz => gameInv_deliverBNoWin hinv q hz) hinj len b
  refine ⟨?_, ?_, ?_, fun t st _ => hwin₁ t st, fun t st _ => hwin₂ t st⟩
  · rintro t st (hw | hinv) z hz
    · exact .inl (hwin₁ t st hw z hz)
    · exact .inr (hinv₁ t st hinv z hz)
  · rintro t st (hw | hinv) z hz
    · exact .inl (hwin₂ t st hw z hz)
    cases hw : st.win
    · rcases t with ((t | q) | q)
      · exact .inr (hinv₁ (.inl (.inl t)) st hinv z hz)
      · change z ∈ support ((oracleDeliverBLookup G q).run st) at hz
        rw [← oracleDeliverBNoWin_run_eq_lookup hae hinv hw q] at hz
        exact .inr (gameInv_deliverBNoWin hinv q hz)
      · exact .inr (hinv₁ (.inr q) st hinv z hz)
    · exact .inl (hwin₂ t st hw z hz)
  · rintro t st (hw | hinv) hnw q
    · exact absurd hw hnw
    rcases t with ((t | q') | q')
    · rfl
    · exact congrArg (fun mx => Pr{let z ← mx}[q z ∧ ¬z.2.win = true])
        (oracleDeliverBNoWin_run_eq_lookup hae hinv (by simpa only [Bool.not_eq_true] using hnw) q')
    · rfl

/-- Let `ae` be correct. Then `fs-aead-nd` and `fs-aead-nd` with `O-Deliver-B^lk` give every
event of their runs the same probability away from `win`. -/
theorem prEvent_gameRun_mon_and_not_win_eq_lookup [SampleableType W]
    (hae : ae.Correct) (len : M → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (p : Bool → Bool × GameState (SendState W) (RecvState W Kae) AD M (ℕ × Cae) → Prop) :
    Pr{let r ← (gameRun (fromAEADChain ae G)
        (fsaeadNoDeliverWinImpl (fromAEADChain ae G) len) adversary)}[p r.1 r.2 ∧
          ¬r.2.2.win = true] =
      Pr{let r ← gameRun (fromAEADChain ae G) (fsaeadMonLookupImpl ae G len) adversary}[p r.1 r.2 ∧
          ¬r.2.2.win = true] :=
  prEvent_gameRun_congr _ _ _ adversary (fun b z => p b z ∧ ¬z.2.win = true)
    (fun b z => p b z ∧ ¬z.2.win = true) fun k b => by
      obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := monLookup_untilBad (k := k) hae len b
      exact prEvent_simulateQ_run_and_not_bad_eq_of_inv _ _ (MonInv ae G k)
        (fun st => st.win = true) h₁ h₂ h₃ h₄ h₅ adversary _ (.inr gameInv_init) (p b)

/-- Let `ae` be correct. Then `fs-aead-nd` and `fs-aead-nd` with `O-Deliver-B^lk` set `win` with
the same probability. -/
theorem prEvent_gameRun_mon_win_eq_lookup [SampleableType W]
    (hae : ae.Correct) (len : M → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    Pr{let r ← (gameRun (fromAEADChain ae G)
        (fsaeadNoDeliverWinImpl (fromAEADChain ae G) len) adversary)}[r.2.2.win = true] =
      Pr{let r ← gameRun (fromAEADChain ae G) (fsaeadMonLookupImpl ae G len) adversary}[
          r.2.2.win = true] :=
  prEvent_gameRun_congr _ _ _ adversary (fun _ z => z.2.win = true)
    (fun _ z => z.2.win = true) fun k b => by
      obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := monLookup_untilBad (k := k) hae len b
      exact prEvent_simulateQ_run_bad_eq_of_inv _ _ (MonInv ae G k)
        (fun st => st.win = true) h₁ h₂ h₃ h₄ h₅ adversary _ (.inr gameInv_init)

end FromAEADPRG

end FSAEADScheme
