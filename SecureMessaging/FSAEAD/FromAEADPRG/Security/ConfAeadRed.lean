/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.AeadRed
public import SecureMessaging.FSAEAD.FromAEADPRG.Security.ConfMix

/-!
# FS-AEAD from AEAD and PRG — the AEAD reductions of the confidentiality step

The reduction `E'_p` (`confAeadRed`) is a one-time IND-CCA adversary against `ae`. It samples the
chain steps `1, …, p` and plays `G_conf^p` with uniform challenge ciphertexts at the positions
`1, …, p - 1`. A challenge at `p` goes to the encryption oracle of the AEAD game. Every other use
of the key at `p`, including a transmission at `p` and the dictionary `D[p]` of B, uses the
reduction's own key. `E'_p` never calls the decryption oracle: `G_conf^p` stops at every
corruption of A below `p`, so no injection at `p` reaches `FS-Rcv`.

`E'_p` outputs `b = b'` if no corruption revealed a position below `p`, and a fair coin otherwise.
- In the real world, the challenge at `p` is encrypted under the independent key of the AEAD game,
  so `E'_p` plays `G'_p` (`confHybKey`).
- In the ideal world, the challenge at `p` is a uniform ciphertext of length `clen(|m|)`, so `E'_p`
  plays `G_{p,p}`.

`confGap_confHybKey_sub_eq` gives the gap between the two worlds.

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Figure 1, Theorem 5.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal AEADScheme

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type}

/-- `O-Chall-A` of `E'_p`: at position `p` the ciphertext comes from the AEAD encryption oracle
(`redSend`), and at every other position from the challenge mode `cm`. -/
def redChallMode [LenSampleable Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (p : ℕ)
    (b : Bool) : QueryImpl (AD × M × M →ₒ Option (ℕ × Cae)) (RedM W Kae AD M Cae) :=
  fun (a, m₀, m₁) => StateT.mk fun st =>
    if st.end_ || st.corrA || len m₀ ≠ len m₁ then pure (none, st)
    else if st.iA + 1 = p then (redSend ae G p true a (if b then m₁ else m₀)).run st
    else (liftStep (oracleChallMode ae G len clen cm b (a, m₀, m₁))).run st

variable [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae]

/-- The oracles of `E'_p` for the chain `G`, without the history. -/
def confRedImplWith (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (p : ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (RedM W Kae AD M Cae) :=
  liftImpl (oracleUnif (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    + liftImpl (oracleTransmitBlk ae G (fun _ => false))
    + redChallMode ae G len clen cm p b
    + liftImpl (oracleCorrALow (SendState W) (RecvState W Kae) AD M (ℕ × Cae) p)
    + liftImpl (oracleCorrBLow W Kae AD M Cae p)
    + liftImpl (oracleDeliverBLookup (AD := AD) (M := M) (Cae := Cae) G)
    + liftImpl (oracleInjectBRej (fromAEADChain ae G) Prod.fst false)

/-- The oracles of `E'_p` with the history. -/
def confRedImpl (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (p : ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (StateT (CState W Kae AD M Cae × ConfHist) (OracleComp (AeadSpec AD M Cae))) :=
  (confRedImplWith ae G len clen cm p b).extendState confAux

/-- **The AEAD reduction `E'_{n+1}`.** It samples the chain steps `1, …, n + 1`, the key `k` and
the bit `b`, and plays `G_conf^{n+1}` with uniform challenge ciphertexts at the positions
`1, …, n`, with the challenge at `n + 1` from the encryption oracle. It outputs `b = b'` if no
corruption revealed a position below `n + 1`, and a fair coin otherwise. -/
def confAeadRed [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (n : ℕ) : OracleComp (AeadSpec AD M Cae) Bool := do
  let U ← liftComp (sampleTab (n + 1)) (AeadSpec AD M Cae)
  let k ← liftComp ($ᵗ W) (AeadSpec AD M Cae)
  let b ← liftComp ($ᵗ Bool) (AeadSpec AD M Cae)
  let z ← (simulateQ (confRedImpl ae (hybGen prg U) len clen (randUpTo n) (n + 1) b)
    adversary).run (.init (fromAEADChain ae (hybGen prg U)) k, .init)
  let c ← liftComp ($ᵗ Bool) (AeadSpec AD M Cae)
  pure (if ¬LowExpo (n + 1) z.2.2 then b == z.1 else c)

/-! ## The reduction in the AEAD game -/

section Run

variable (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (len : M → ℕ) (clen : ℕ → ℕ)

/-- The oracles of `E'_p` run inside the one-time IND-CCA game with bit `β` and key `K`, as one
oracle set on the joint state. -/
def confRedGameImpl (G : ℕ → W → W × Kae) (cm : ℕ → ChalMode Kae) (p : ℕ) (b β : Bool)
    (K : Kae) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (StateT ((CState W Kae AD M Cae × ConfHist) × Option ((ℕ × AD) × Cae)) ProbComp) :=
  ((aeadSecurityImpl ae len clen β K).mapStateTBase
    (confRedImpl ae G len clen cm p b)).flattenStateT

/-- The challenge mode at `p` in the AEAD world `β` with key `K`: uniform for `β = 1`, and the
key `K` for `β = 0`. -/
def aeadMode (β : Bool) (K : Kae) : ChalMode Kae := if β then .rand else .key K

omit [DecidableEq AD] [DecidableEq Cae] in
/-- `O-Chall-A^cm` depends on `cm` only at the position `i_A + 1`. -/
theorem oracleChallMode_run_congr (G : ℕ → W → W × Kae) (cm₁ cm₂ : ℕ → ChalMode Kae) (b : Bool)
    (q : AD × M × M) (st : CState W Kae AD M Cae) (h : cm₁ (st.iA + 1) = cm₂ (st.iA + 1)) :
    (oracleChallMode ae G len clen cm₁ b q).run st =
      (oracleChallMode ae G len clen cm₂ b q).run st := by
  obtain ⟨a, m₀, m₁⟩ := q
  rw [oracleChallMode_run, oracleChallMode_run, h]

/-- A challenge at `p` in the AEAD game, before any encryption, is a challenge in the mode
`aeadMode β K`. -/
theorem redChallMode_run_none (G : ℕ → W → W × Kae) (cm : ℕ → ChalMode Kae) (p : ℕ)
    (b β : Bool) (K : Kae) (q : AD × M × M) (st : CState W Kae AD M Cae)
    (hiA : st.vA.iA = st.iA) (hp : st.iA + 1 = p) :
    Prod.fst <$> (simulateQ (aeadSecurityImpl ae len clen β K)
        ((redChallMode ae G len clen cm p b q).run st)).run none =
      (oracleChallMode ae G len clen (Function.update cm p (aeadMode β K)) b q).run st := by
  obtain ⟨a, m₀, m₁⟩ := q
  rw [oracleChallMode_run]
  simp only [redChallMode, StateT.run_mk]
  by_cases hg : (st.end_ || st.corrA || decide (len m₀ ≠ len m₁)) = true
  · rw [ite_eq_left hg, ite_eq_left hg]
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  rw [ite_eq_right hg, ite_eq_right hg, ite_eq_left hp]
  subst hp
  rw [Function.update_self]
  generalize (if b = true then m₁ else m₀) = m
  have he : aeadSecurityImpl ae len clen β K (Sum.inl (Sum.inr ((st.iA + 1, a), m))) =
      oracleEncrypt ae len clen β K ((st.iA + 1, a), m) := rfl
  simp only [redSend, StateT.run_mk, ↓reduceIte, simulateQ_bind, simulateQ_spec_query, he]
  cases β
  · simp only [oracleEncrypt, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, StateT.run_bind,
      StateT.run_get, pure_bind, StateT.run_map, StateT.run_set, map_pure, simulateQ_pure,
      StateT.run_pure, aeadMode, chalSend, hiA]
  · simp only [oracleEncrypt, ↓reduceIte, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, StateT.run_map, StateT.run_set, map_pure, aeadMode, chalSend, hiA, liftM,
      StateT.run_monadLift, monadLift_self, Functor.map_map, bind_map_left, simulateQ_pure,
      StateT.run_pure]

/-- One step of `E'_p` in the AEAD game is the step of `G_conf^p` with the mode `aeadMode β K` at
`p`, if the AEAD game has encrypted nothing before A's send at `p`. -/
theorem fst_confRedStep (G : ℕ → W → W × Kae) (cm : ℕ → ChalMode Kae) (p : ℕ) (b β : Bool)
    (K : Kae) (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (st : CState W Kae AD M Cae) (c : Option ((ℕ × AD) × Cae)) (hiA : st.vA.iA = st.iA)
    (hc : st.iA + 1 = p → c = none) :
    Prod.fst <$> (simulateQ (aeadSecurityImpl ae len clen β K)
        ((confRedImplWith ae G len clen cm p b t).run st)).run c =
      (confImplWith ae G len clen (Function.update cm p (aeadMode β K)) (fun _ => false) p b
        t).run st := by
  have hlift {α : Type} (x : GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae) α) :
      Prod.fst <$> (simulateQ (aeadSecurityImpl ae len clen β K) ((liftStep x).run st)).run c =
        x.run st := by
    rw [simulateQ_liftStep_run, Functor.map_map]
    exact id_map _
  rcases t with ((((((n | q) | ⟨a, m₀, m₁⟩) | u) | u) | q) | q)
  any_goals exact hlift _
  change Prod.fst <$> (simulateQ (aeadSecurityImpl ae len clen β K)
      ((redChallMode ae G len clen cm p b (a, m₀, m₁)).run st)).run c =
    (oracleChallMode ae G len clen (Function.update cm p (aeadMode β K)) b (a, m₀, m₁)).run st
  by_cases hp : st.iA + 1 = p
  · rw [hc hp]
    exact redChallMode_run_none ae len clen G cm p b β K _ st hiA hp
  by_cases hg : (st.end_ || st.corrA || decide (len m₀ ≠ len m₁)) = true
  · rw [oracleChallMode_run, ite_eq_left hg]
    simp only [redChallMode, StateT.run_mk, hg, ↓reduceIte, simulateQ_pure, StateT.run_pure,
      map_pure]
  · have h : (redChallMode ae G len clen cm p b (a, m₀, m₁)).run st =
        (liftStep (oracleChallMode ae G len clen cm b (a, m₀, m₁))).run st := by
      simp only [redChallMode, StateT.run_mk, hg, hp, Bool.false_eq_true, ↓reduceIte]
    rw [h, hlift, oracleChallMode_run_congr ae len clen G _ _ b _ st
      (Function.update_of_ne hp _ _).symm]

/-- One step of `E'_p` in the AEAD game changes the state of the AEAD game only at a challenge at
`p`, and that challenge enters the history. -/
theorem snd_confRedStep (G : ℕ → W → W × Kae) (cm : ℕ → ChalMode Kae) (p : ℕ) (b β : Bool)
    (K : Kae) (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (st : CState W Kae AD M Cae) (h : ConfHist) (c : Option ((ℕ × AD) × Cae)) :
    ∀ y ∈ support ((simulateQ (aeadSecurityImpl ae len clen β K)
      ((confRedImplWith ae G len clen cm p b t).run st)).run c),
      y.2 = c ∨ (confAux t st y.1.1 y.1.2 h).chal p = true := by
  intro y hy
  have hlift {α : Type} (x : GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae) α)
      (y' : (α × CState W Kae AD M Cae) × Option ((ℕ × AD) × Cae))
      (hy : y' ∈ support ((simulateQ (aeadSecurityImpl ae len clen β K)
        ((liftStep x).run st)).run c)) : y'.2 = c := by
    obtain ⟨z, -, rfl⟩ := mem_support_liftStep (ae := ae) (lenM := len) (clen := clen) hy
    rfl
  rcases t with ((((((n | q) | ⟨a, m₀, m₁⟩) | u) | u) | q) | q)
  any_goals exact .inl (hlift _ y hy)
  change y ∈ support ((simulateQ (aeadSecurityImpl ae len clen β K)
    ((redChallMode ae G len clen cm p b (a, m₀, m₁)).run st)).run c) at hy
  by_cases hg : (st.end_ || st.corrA || decide (len m₀ ≠ len m₁)) = true
  · simp only [redChallMode, StateT.run_mk, hg, ↓reduceIte, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact .inl rfl
  by_cases hp : st.iA + 1 = p
  · have he : ∀ m, aeadSecurityImpl ae len clen β K (Sum.inl (Sum.inr ((p, a), m))) =
        oracleEncrypt ae len clen β K ((p, a), m) := fun _ => rfl
    simp only [redChallMode, redSend, StateT.run_mk, hg, hp, Bool.false_eq_true, ↓reduceIte,
      simulateQ_bind, simulateQ_spec_query, he, StateT.run_bind, support_bind, Set.mem_iUnion,
      exists_prop] at hy
    obtain ⟨x, hx, hy⟩ := hy
    rcases c with _ | c
    · cases β
      · simp only [oracleEncrypt, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT.run_get, pure_bind, bind_pure_comp, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hx
        subst hx
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
        subst hy
        refine .inr ?_
        simp only [confAux, Option.isSome_some, ↓reduceIte, hp, decide_true, Bool.or_true]
      · simp only [oracleEncrypt, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          bind_pure_comp, StateT.run_map, StateT.run_set, map_pure, liftM, StateT.run_monadLift,
          monadLift_self, support_map, Set.mem_image] at hx
        obtain ⟨e, -, rfl⟩ := hx
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
        subst hy
        refine .inr ?_
        simp only [confAux, Option.isSome_some, ↓reduceIte, hp, decide_true, Bool.or_true]
    · simp only [oracleEncrypt, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact .inl rfl
  · have h' : (redChallMode ae G len clen cm p b (a, m₀, m₁)).run st =
        (liftStep (oracleChallMode ae G len clen cm b (a, m₀, m₁))).run st := by
      simp only [redChallMode, StateT.run_mk, hg, hp, Bool.false_eq_true, ↓reduceIte]
    rw [h'] at hy
    exact .inl (hlift _ y hy)

/-- **`E'_p` plays `G_conf^p`.** In the AEAD world `β` with key `K`, the runs of `E'_p`, with the
state of the AEAD game dropped, are the runs of `G_conf^p` with the mode `aeadMode β K` at `p`. -/
theorem confRedGameImpl_run_map (G : ℕ → W → W × Kae) (cm : ℕ → ChalMode Kae) (p : ℕ)
    (b β : Bool) (K : Kae)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W) :
    Prod.map id Prod.fst <$> (simulateQ (confRedGameImpl ae len clen G cm p b β K) adversary).run
        ((.init (fromAEADChain ae G) k, .init), none) =
      confRun ae G len clen (Function.update cm p (aeadMode β K)) (fun _ => false) p b adversary
        k := by
  have hstep : ∀ t (x : (CState W Kae AD M Cae × ConfHist) × Option ((ℕ × AD) × Cae)),
      SeedInv G k x.1.1 → TxInv x.1 → (x.2 = none ∨ x.1.2.chal p = true) →
      Prod.map id Prod.fst <$> (confRedGameImpl ae len clen G cm p b β K t).run x =
        (confImpl ae G len clen (Function.update cm p (aeadMode β K)) (fun _ => false) p b t).run
          x.1 := by
    rintro t ⟨⟨st, h⟩, c⟩ hS hT hc
    have hc' : st.iA + 1 = p → c = none := fun hp => hc.resolve_right fun hch => by
      have := hT.chal_le p hch
      simp only at this
      omega
    rw [confRedGameImpl, confRedImpl,
      OracleComp.flattenStateT_mapStateTBase_extendState_run, confImpl, QueryImpl.extendState_apply,
      ← fst_confRedStep ae len clen G cm p b β K t st c hS.vA_iA hc']
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map_apply,
      id_eq]
  refine map_run_simulateQ_eq_of_query_map_eq_inv' _ _
    (fun x => SeedInv G k x.1.1 ∧ TxInv x.1 ∧ (x.2 = none ∨ x.1.2.chal p = true)) Prod.fst ?_
    (fun t x hx => hstep t x hx.1 hx.2.1 hx.2.2) adversary _
    ⟨⟨rfl, rfl, ⟨rfl, fun _ _ h => (nomatch h), fun _ _ => rfl⟩⟩, txInv_init _ k, .inl rfl⟩
  rintro t ⟨⟨st, h⟩, c⟩ ⟨hS, hT, hc⟩ y hy
  have hy' : Prod.map id Prod.fst y ∈ support ((confImpl ae G len clen
      (Function.update cm p (aeadMode β K)) (fun _ => false) p b t).run (st, h)) := by
    rw [← hstep t _ hS hT hc, support_map]
    exact ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzy⟩ := QueryImpl.mem_support_extendState_run _ confAux t st h hy'
  refine ⟨?_, txInv_confStep ae G len clen _ p b t (st, h) hT _ hy', ?_⟩
  · have hy1 : y.2.1.1 = z.2 := congrArg (fun w => w.2.1) hzy
    rw [hy1]
    exact seedInv_confStep ae G k len clen _ _ p b t st hS z hz
  · rw [confRedGameImpl, confRedImpl,
    OracleComp.flattenStateT_mapStateTBase_extendState_run, support_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rcases snd_confRedStep ae len clen G cm p b β K t st h c x hx with hx2 | hx2
    · simp only
      rw [hx2]
      rcases hc with hc | hc
      · exact .inl hc
      · exact .inr (chal_confAux t st x.1.1 x.1.2 hc)
    · exact .inr hx2

/-- `E'_{n+1}` inside the one-time IND-CCA game with bit `β` and key `K`: it samples the table, the
key and the bit, runs the joint oracles, and outputs `b = b'` or a fair coin. -/
theorem confAeadRed_run [SampleableType W] [SampleableType Kae] (prg : PRGScheme W (W × Kae))
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (n : ℕ)
    (β : Bool) (K : Kae) :
    (do
      let z ← (simulateQ (aeadSecurityImpl ae len clen β K)
        (confAeadRed ae prg len clen adversary n)).run none
      pure z.1 : ProbComp Bool) =
    (do
      let U ← sampleTab (n + 1)
      let k ← $ᵗ W
      let b ← $ᵗ Bool
      let y ← (simulateQ (confRedGameImpl ae len clen (hybGen prg U) (randUpTo n) (n + 1) b β K)
        adversary).run ((.init (fromAEADChain ae (hybGen prg U)) k, .init), none)
      let c ← $ᵗ Bool
      pure (if ¬LowExpo (n + 1) y.2.1.2 then b == y.1 else c)) := by
  simp only [confAeadRed, simulateQ_bind, simulateQ_aeadSecurityImpl_liftComp, simulateQ_pure,
    StateT.run_bind, liftM, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    StateT.run_pure]
  simp only [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, bind_pure_comp,
    bind_map_left]
  rfl

/-- In the AEAD world `β` with key `K`, `E'_{n+1}` gives the reduction output of `G_conf^{n+1}` with
the mode `aeadMode β K` at `n + 1`. -/
theorem confAeadRed_run_eq_coinOut [SampleableType W] [SampleableType Kae]
    (prg : PRGScheme W (W × Kae))
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (n : ℕ)
    (β : Bool) (K : Kae) :
    (do
      let z ← (simulateQ (aeadSecurityImpl ae len clen β K)
        (confAeadRed ae prg len clen adversary n)).run none
      pure z.1 : ProbComp Bool) =
    coinOut (n + 1) (do
      let U ← sampleTab (n + 1)
      let k ← $ᵗ W
      let b ← $ᵗ Bool
      let z ← confRun ae (hybGen prg U) len clen (Function.update (randUpTo n) (n + 1)
        (aeadMode β K)) (fun _ => false) (n + 1) b adversary k
      pure (b, z.1, z.2.2)) := by
  rw [confAeadRed_run]
  simp only [coinOut, bind_assoc, pure_bind]
  refine congrArg _ (funext fun U => congrArg _ (funext fun k => congrArg _ (funext fun b => ?_)))
  rw [← confRedGameImpl_run_map ae len clen (hybGen prg U) (randUpTo n) (n + 1) b β K adversary k,
    bind_map_left]
  rfl

/-- **The real world of `E'_{n+1}`** is `G'_{n+1}`: the key of the AEAD game is uniform (`hkg`),
and it encrypts the challenge at `n + 1`. -/
theorem confAeadReal [SampleableType W] [SampleableType Kae]
    (hkg : ae.keygen =ᵈ ($ᵗ Kae : ProbComp Kae)) (prg : PRGScheme W (W × Kae))
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (n : ℕ) :
    Pr{let x ← securityExpFixedBit ae len clen (confAeadRed ae prg len clen adversary n) false}[
        x = true] =
      Pr{let x ← coinOut (n + 1) (confHybKey ae prg len clen adversary (n + 1) n)}[x = true] := by
  refine EvalDistEq.prEvent_eq ?_ _
  unfold securityExpFixedBit
  refine (EvalDistEq.bind_left hkg _).trans ?_
  simp only [confAeadRed_run_eq_coinOut]
  simp only [coinOut, confHybKey, bind_assoc, pure_bind]
  rfl

/-- `Function.update (randUpTo n) (n + 1) rand` is `randUpTo (n + 1)`. -/
theorem update_randUpTo (n : ℕ) :
    Function.update (randUpTo n) (n + 1) (ChalMode.rand : ChalMode Kae) = randUpTo (n + 1) := by
  funext p
  by_cases hp : p = n + 1
  · subst hp
    simp only [Function.update_self, randUpTo, le_refl, ↓reduceIte]
  · simp only [Function.update_of_ne hp, randUpTo]
    split_ifs <;> first | rfl | omega

/-- **The ideal world of `E'_{n+1}`** is `G_{n+1,n+1}`: the challenge at `n + 1` is a uniform
ciphertext. -/
theorem confAeadIdeal [SampleableType W] [SampleableType Kae] (prg : PRGScheme W (W × Kae))
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (n : ℕ) :
    Pr{let x ← securityExpFixedBit ae len clen (confAeadRed ae prg len clen adversary n) true}[
        x = true] =
      Pr{let x ← coinOut (n + 1) (confHyb ae prg len clen adversary (n + 1) (n + 1) (n + 1))}[
        x = true] := by
  refine EvalDistEq.prEvent_eq ?_ _
  unfold securityExpFixedBit
  simp only [confAeadRed_run_eq_coinOut, aeadMode, ↓reduceIte, update_randUpTo]
  exact EvalDistEq.bind_const (spec := unifSpec) _ _

/-- **The AEAD step.** The gap between `G'_{n+1}` and `G_{n+1}` on runs where no corruption revealed
a position below `n + 1` is the advantage of `E'_{n+1}`. -/
theorem confGap_confHybKey_sub_eq [SampleableType W] [SampleableType Kae]
    (hkg : ae.keygen =ᵈ ($ᵗ Kae : ProbComp Kae)) (prg : PRGScheme W (W × Kae))
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (n : ℕ) :
    |confGap (confHybKey ae prg len clen adversary (n + 1) n) (fun h => ¬LowExpo (n + 1) h) -
        confGap (confHyb ae prg len clen adversary (n + 1) (n + 1) (n + 1))
          (fun h => ¬LowExpo (n + 1) h)| =
      distAdvantage ae len clen (confAeadRed ae prg len clen adversary n) := by
  rw [distAdvantage, confAeadReal ae len clen hkg, confAeadIdeal, prEvent_coinOut_toReal,
    prEvent_coinOut_toReal, abs_sub_comm]
  ring_nf

end Run

end FromAEADPRG


end FSAEADScheme
