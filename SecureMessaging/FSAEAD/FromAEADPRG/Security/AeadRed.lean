/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Hybrid
public import ToVCVio.OracleComp.SimSemantics.StateT.MapStateTBase
public import VCVio.OracleComp.SimSemantics.StateT.StateSeparating

/-!
# FS-AEAD from AEAD and PRG — the AEAD reductions of the authenticity step

The reduction `E_p` (`aeadRed`) is a one-time IND-CCA adversary against `ae`. It plays the hybrid
`H_p` with the key `K_p` of the AEAD game. It samples the steps `1, …, p` of the chain itself, and
keeps its own key at position `p` in the game state, but never uses it:
- A's encryption at position `p` goes to the encryption oracle;
- an injection at position `p` goes to the decryption oracle.
`E_p` outputs whether the first win is at `p`.

`O-Corr-B^⊥` reveals no state, so the key at position `p` stays hidden. `E_p` never decrypts the
challenge pair: if A's ciphertext at `p` is in transit, `O-Inject-B` rejects it before `FS-Rcv`,
and otherwise B has used index `p` and `rcvKey` rejects it. `E_p` can decrypt the challenge
ciphertext with other associated data. The AEAD game allows this, because it rejects only the
challenge pair (deviation D1 in `SecureMessaging.AEAD.Defs`).

- `aeadReal_aeadRed`: in the real world, `E_p` outputs 1 with the probability of a first win at
  `p` in `H_p`.
- `aeadIdeal_aeadRed`: in the ideal world every decryption fails, so `E_p` outputs 0.

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the
  Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
  — Figure 1, Theorem 5.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal AEADScheme

namespace AEADScheme

variable {M AD K C : Type} [LenSampleable C] [DecidableEq AD] [DecidableEq C]

/-- Let `ob` be a probabilistic computation. Then its lift runs in the one-time IND-CCA game as `ob`
and keeps the state of the game. The reductions sample their own randomness this way. -/
theorem simulateQ_aeadSecurityImpl_liftComp (ae : AEADScheme ProbComp M AD K C)
    (lenM : M → ℕ) (clen : ℕ → ℕ) (b : Bool) (k : K) {β : Type} (ob : ProbComp β) :
    simulateQ (aeadSecurityImpl ae lenM clen b k) (liftComp ob (aeadOneTimeCCASpec AD M C)) =
      (liftM ob : StateT (Option (AD × C)) ProbComp β) := by
  refine StateT.ext fun s => ?_
  rw [QueryImpl.Stateful.simulateQ_liftComp_run_of_query (aeadSecurityImpl ae lenM clen b k)
    (fun t s => ?_) ob s]
  · simp only [liftM, StateT.run_monadLift, monadLift_self, bind_pure_comp]
  · rw [liftComp_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change (simulateQ (aeadSecurityImpl ae lenM clen b k) (liftM (OracleSpec.query
      (spec := aeadOneTimeCCASpec AD M C) (.inl (.inl t))))).run s = _
    rw [simulateQ_spec_query]
    rfl

end AEADScheme

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type}

/-- The oracles of the one-time IND-CCA game for the AEAD scheme of the construction. -/
abbrev AeadSpec (AD M Cae : Type) := aeadOneTimeCCASpec (ℕ × AD) M Cae

/-- The monad of the reduction's game: the game state over the AEAD game's oracles. -/
abbrev RedM (W Kae AD M Cae : Type) :=
  StateT (CState W Kae AD M Cae) (OracleComp (AeadSpec AD M Cae))

/-- A step of the FS-AEAD game, lifted to the reduction's monad. -/
def liftStep {α : Type} (x : GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae) α) :
    RedM W Kae AD M Cae α :=
  StateT.mk fun st => liftComp (x.run st) (AeadSpec AD M Cae)

/-- An oracle of the FS-AEAD game, lifted to the reduction's monad. -/
def liftImpl {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae))) :
    QueryImpl spec (RedM W Kae AD M Cae) :=
  fun t => liftStep (impl t)

/-- A sends `(a, m)` at position `i_A + 1`, as in `O-Transmit-A` and `O-Chall-A` after their
guards. At position `p` the ciphertext comes from the AEAD encryption oracle; `⊥` from the oracle
leaves the state. -/
def redSend (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) (p : ℕ)
    (isChall : Bool) (a : AD) (m : M) : RedM W Kae AD M Cae (Option (ℕ × Cae)) :=
  StateT.mk fun st =>
    let r := send ae G st.vA a m
    if st.iA + 1 = p then do
      let e? ← liftM (OracleSpec.query (spec := AeadSpec AD M Cae) (.inl (.inr ((p, a), m))))
      match e? with
      | none => pure (none, st)
      | some e =>
        pure (some (p, e), { st with vA := r.1, iA := st.iA + 1 }.record isChall a m (p, e))
    else pure (some r.2, { st with vA := r.1, iA := st.iA + 1 }.record isChall a m r.2)

/-- `O-Transmit-A` of `E_p`. -/
def redTransmitA (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) (p : ℕ) :
    QueryImpl (AD × M →ₒ Option (ℕ × Cae)) (RedM W Kae AD M Cae) :=
  fun (a, m) => StateT.mk fun st =>
    if st.end_ then pure (none, st) else (redSend ae G p false a m).run st

/-- `O-Chall-A` of `E_p`. -/
def redChallA (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) (p : ℕ)
    (len : M → ℕ) (b : Bool) :
    QueryImpl (AD × M × M →ₒ Option (ℕ × Cae)) (RedM W Kae AD M Cae) :=
  fun (a, m₀, m₁) => StateT.mk fun st =>
    if st.end_ || st.corrA || len m₀ ≠ len m₁ then pure (none, st)
    else (redSend ae G p true a (if b then m₁ else m₀)).run st

variable [DecidableEq AD] [DecidableEq Cae]

/-- `O-Inject-B^stop` of `E_p`: B finds the key with `rcvKey`, and at position `p` the AEAD
decryption oracle decrypts. -/
def redInjectB (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) (p : ℕ) :
    QueryImpl (AD × (ℕ × Cae) →ₒ Option (ℕ × M)) (RedM W Kae AD M Cae) :=
  fun (a, c) => StateT.mk fun st =>
    if st.end_ || (st.findTrans a c).isSome then pure (none, st) else
    match rcvKey G st.vB c.1 with
    | none => pure (none, st)
    | some (vB, K) => do
      let m? ← if c.1 = p then
          liftM (OracleSpec.query (spec := AeadSpec AD M Cae) (.inr ((p, a), c.2)))
        else pure (ae.decrypt K (c.1, a) c.2)
      match m? with
      | none => pure (none, st)
      | some m' =>
        pure (some (c.1, m'),
          { st with vB, win := st.win || !st.comp c.1, end_ := !st.comp c.1 }.delete c.1)

/-- The oracles of `E_p` for the chain `G`, without the history. -/
def redImplWith (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) (p : ℕ)
    (len : M → ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (RedM W Kae AD M Cae) :=
  liftImpl (oracleUnif (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    + redTransmitA ae G p
    + redChallA ae G p len b
    + liftImpl (oracleCorrALow (SendState W) (RecvState W Kae) AD M (ℕ × Cae) 0)
    + liftImpl (oracleCorrBSilent (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    + liftImpl (oracleDeliverBLookup (AD := AD) (M := M) (Cae := Cae) G)
    + redInjectB ae G p

/-- The oracles of `E_p` with the history. -/
def redImpl (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae) (p : ℕ)
    (len : M → ℕ) (b : Bool) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (StateT (CState W Kae AD M Cae × AuthHist) (OracleComp (AeadSpec AD M Cae))) :=
  (redImplWith ae G p len b).extendState authAux

/-- **The AEAD reduction `E_p`.** It samples the steps `1, …, p` of the chain, the key `k` and the
bit `b`, runs the adversary against the oracles of `E_p`, and outputs whether the first win is at
`p`. -/
def aeadRed [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (p : ℕ) :
    OracleComp (AeadSpec AD M Cae) Bool := do
  let U ← liftComp (sampleTab p) (AeadSpec AD M Cae)
  let k ← liftComp ($ᵗ W) (AeadSpec AD M Cae)
  let b ← liftComp ($ᵗ Bool) (AeadSpec AD M Cae)
  let z ← (simulateQ (redImpl ae (hybGen prg U) p len b) adversary).run
    (.init (fromAEADChain ae (hybGen prg U)) k, .init)
  pure (winIn p p z.2.2)

/-! ## The reduction in the AEAD game -/

section Run

variable [LenSampleable Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (lenM : M → ℕ)
  (clen : ℕ → ℕ)

/-- The oracles of `E_p` run inside the one-time IND-CCA game with bit `β` and key `K`, as one
oracle set on the joint state. -/
def redGameImpl (G : ℕ → W → W × Kae) (p : ℕ) (len : M → ℕ) (b β : Bool) (K : Kae) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (StateT ((CState W Kae AD M Cae × AuthHist) × Option ((ℕ × AD) × Cae)) ProbComp) :=
  ((aeadSecurityImpl ae lenM clen β K).mapStateTBase (redImpl ae G p len b)).flattenStateT

/-- A lifted game step keeps the state of the AEAD game. -/
theorem simulateQ_liftStep_run (β : Bool) (K : Kae) {α : Type}
    (x : GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae) α) (st : CState W Kae AD M Cae)
    (c : Option ((ℕ × AD) × Cae)) :
    (simulateQ (aeadSecurityImpl ae lenM clen β K) ((liftStep x).run st)).run c =
      (fun y => (y, c)) <$> x.run st := by
  change (simulateQ (aeadSecurityImpl ae lenM clen β K)
    (liftComp (x.run st) (AeadSpec AD M Cae))).run c = _
  rw [simulateQ_aeadSecurityImpl_liftComp]
  simp only [liftM, StateT.run_monadLift, monadLift_self, bind_pure_comp]

omit [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae] in
/-- The challenge facts of `RedInv` survive a step that does not lower `i_A`, keeps every record
at `p` unless B has used `p`, and keeps the indices that B has used. -/
theorem chal_mono {p : ℕ} {st st' : CState W Kae AD M Cae} {c : Option ((ℕ × AD) × Cae)}
    (hlt : st.iA < p → c = none)
    (hchal : ∀ a' e', c = some ((p, a'), e') →
      (∃ r ∈ st.trans, r.1 = p ∧ r.2.1 = a' ∧ r.2.2.2 = (p, e')) ∨ Consumed st.vB p)
    (hiA : st.iA ≤ st'.iA)
    (htrans : ∀ r ∈ st.trans, r.1 = p → r ∈ st'.trans ∨ Consumed st'.vB p)
    (hcons : Consumed st.vB p → Consumed st'.vB p) :
    (st'.iA < p → c = none) ∧ ∀ a' e', c = some ((p, a'), e') →
      (∃ r ∈ st'.trans, r.1 = p ∧ r.2.1 = a' ∧ r.2.2.2 = (p, e')) ∨ Consumed st'.vB p := by
  refine ⟨fun h => hlt (by omega), fun a' e' hc => ?_⟩
  rcases hchal a' e' hc with ⟨r, hr, h₁, h₂, h₃⟩ | h
  · rcases htrans r hr h₁ with hr' | h
    · exact .inl ⟨r, hr', h₁, h₂, h₃⟩
    · exact .inr h
  · exact .inr (hcons h)

/-! ### The real world: `E_p` plays `H_p` -/

variable {ae lenM clen}

/-- The invariant of the joint state of `E_p` in the real world. The reduction's state is on the
chain `G₁`. Before A sends at `p` there is no challenge; after, the challenge is A's ciphertext at
`p`, which is still in transit or B has used index `p`. -/
structure RedInv (G₁ : ℕ → W → W × Kae) (k : W) (p : ℕ) (st : CState W Kae AD M Cae)
    (c : Option ((ℕ × AD) × Cae)) : Prop where
  seed : SeedInv G₁ k st
  none_of_lt : st.iA < p → c = none
  chal : ∀ a' e', c = some ((p, a'), e') →
    (∃ r ∈ st.trans, r.1 = p ∧ r.2.1 = a' ∧ r.2.2.2 = (p, e')) ∨ Consumed st.vB p
  chal_pos : ∀ x, c = some x → x.1.1 = p

/-- A's step in the real world of `E_p`: at position `p` the encryption oracle encrypts under the
AEAD key `K`, which is the key of `G₂` at `p`. -/
theorem redSend_map {G₁ G₂ : ℕ → W → W × Kae} {k : W} {p : ℕ} {K : Kae}
    (hkey : ∀ q, 1 ≤ q → q ≠ p → chainKey G₁ k q = chainKey G₂ k q) (hK : chainKey G₂ k p = K)
    {st : CState W Kae AD M Cae} {c : Option ((ℕ × AD) × Cae)} (hI : RedInv G₁ k p st c)
    (isChall : Bool) (a : AD) (m : M) :
    (fun y => (y.1.1, normSt G₂ k y.1.2)) <$>
        (simulateQ (aeadSecurityImpl ae lenM clen false K)
          ((redSend ae G₁ p isChall a m).run st)).run c =
      pure (some (send ae G₂ (normS G₂ k st.vA) a m).2,
        { normSt G₂ k st with vA := (send ae G₂ (normS G₂ k st.vA) a m).1, iA := st.iA + 1 }.record
          isChall a m (send ae G₂ (normS G₂ k st.vA) a m).2) := by
  have hw := hI.seed.vA_w
  have hi := hI.seed.vA_iA
  by_cases hp : st.iA + 1 = p
  · subst hp
    have hc : c = none := hI.none_of_lt (by omega)
    subst hc
    simp only [redSend, StateT.run_mk, ↓reduceIte, simulateQ_bind, simulateQ_spec_query]
    have he : aeadSecurityImpl ae lenM clen false K (Sum.inl (Sum.inr ((st.iA + 1, a), m))) =
        oracleEncrypt ae lenM clen false K ((st.iA + 1, a), m) := rfl
    rw [he]
    simp only [oracleEncrypt, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, StateT.run_bind,
      StateT.run_get, pure_bind, StateT.run_map, StateT.run_set, map_pure, simulateQ_pure,
      StateT.run_pure]
    have hs₂ : send ae G₂ (normS G₂ k st.vA) a m = (⟨chainState G₂ k (st.iA + 1), st.iA + 1⟩,
        (st.iA + 1, ae.encrypt K (st.iA + 1, a) m)) := by
      rw [send_eq]
      simp only [normS_w, normS_iA, hi, gen_chainState, hK]
    rw [hs₂, normSt_record]
    simp only [send_eq, hi]
    rfl
  · have h := send_normS ae G₁ G₂ k (hkey _ (Nat.succ_pos _) (by omega)) hw a m
    simp only [redSend, StateT.run_mk, hp, ↓reduceIte, simulateQ_pure, StateT.run_pure,
      map_pure, ← h, normSt_record]
    rfl

/-- B's step in the real world of `E_p`: at position `p` the decryption oracle decrypts under the
AEAD key `K`, and it never gets the challenge pair. -/
theorem redInjectB_map {G₁ G₂ : ℕ → W → W × Kae} {k : W} {p : ℕ} {K : Kae}
    (hkey : ∀ q, 1 ≤ q → q ≠ p → chainKey G₁ k q = chainKey G₂ k q) (hK : chainKey G₂ k p = K)
    {st : CState W Kae AD M Cae} {c : Option ((ℕ × AD) × Cae)} (hI : RedInv G₁ k p st c)
    (q : AD × (ℕ × Cae)) :
    (fun y => (y.1.1, normSt G₂ k y.1.2)) <$>
        (simulateQ (aeadSecurityImpl ae lenM clen false K)
          ((redInjectB ae G₁ p q).run st)).run c =
      (oracleInjectBStop (fromAEADChain ae G₂) q).run (normSt G₂ k st) := by
  obtain ⟨a, i, e⟩ := q
  have hf : (normSt G₂ k st).findTrans a (i, e) = st.findTrans a (i, e) := rfl
  have h := rcvKey_normR G₁ G₂ k hI.seed.vB i
  simp only [redInjectB, oracleInjectBStop, StateT.run_mk, StateT.run_bind, StateT.run_get,
    pure_bind, normSt_end_, hf]
  by_cases hg : (st.end_ || (st.findTrans a (i, e)).isSome) = true
  · simp only [hg, ↓reduceIte, simulateQ_pure, StateT.run_pure, map_pure]
  simp only [hg, Bool.false_eq_true, ↓reduceIte]
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hg
  simp only [fromAEADChain, rcv, normSt_vB, ← h]
  rcases hr : rcvKey G₁ st.vB i with _ | ⟨vB', K'⟩
  · simp only [simulateQ_pure, StateT.run_pure, map_pure, Option.map_none, Option.bind_eq_bind,
      Option.bind_none]
  obtain ⟨rfl, hi1, -⟩ := rcvKey_some G₁ hI.seed.vB hr
  simp only [Option.map_some, Prod.map_apply, Option.bind_eq_bind, Option.bind_some]
  by_cases hip : i = p
  · subst hip
    have hc : c ≠ some ((i, a), e) := by
      intro hc
      rcases hI.chal a e hc with ⟨r, hr', -, h₂, h₃⟩ | hcons
      · exact absurd (GameState.findTrans_isSome ⟨r, hr', h₂, h₃⟩) (by simp only [hg.2,
          Bool.false_eq_true, not_false_eq_true])
      · rw [(rcvKey_eq_none_iff G₁ st.vB i).2 hcons] at hr
        exact absurd hr (by simp only [reduceCtorEq, not_false_eq_true])
    have hd : aeadSecurityImpl ae lenM clen false K (Sum.inr ((i, a), e)) =
        oracleDecrypt ae false K ((i, a), e) := rfl
    simp only [↓reduceIte, simulateQ_bind, simulateQ_spec_query, hd, hK]
    simp only [oracleDecrypt, StateT.run_bind, StateT.run_get, pure_bind, Bool.false_or,
      beq_iff_eq, hc, ↓reduceIte]
    rcases ae.decrypt K (i, a) e with _ | m'
    · simp only [StateT.run_pure, pure_bind, simulateQ_pure, map_pure, Option.bind_none]
    · simp only [StateT.run_pure, pure_bind, simulateQ_pure, map_pure, Option.pure_def,
        Option.bind_some, StateT.run_bind, StateT.run_set]
      rfl
  · simp only [hip, ↓reduceIte, hkey i hi1 hip]
    rcases ae.decrypt (chainKey G₂ k i) (i, a) e with _ | m'
    · simp only [StateT.run_pure, simulateQ_pure, map_pure, Option.bind_none]
    · simp only [StateT.run_pure, simulateQ_pure, map_pure, Option.pure_def, Option.bind_some,
        StateT.run_bind, StateT.run_set, pure_bind]
      rfl

/-- Every step of `E_p` in the real world, with `normSt G₂ k` on the game state, is the step of
`G_auth^0` for the chain `G₂`, the chain of `H_p` with the AEAD key `K` at `p`. -/
theorem redImplWith_map {G₁ G₂ : ℕ → W → W × Kae} {k : W} {p : ℕ} {K : Kae} (len : M → ℕ)
    (b : Bool) (hseed : ∀ q, chainState G₁ k q = chainState G₂ k q)
    (hkey : ∀ q, 1 ≤ q → q ≠ p → chainKey G₁ k q = chainKey G₂ k q) (hK : chainKey G₂ k p = K)
    {st : CState W Kae AD M Cae} {c : Option ((ℕ × AD) × Cae)} (hI : RedInv G₁ k p st c)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain) :
    (fun y => (y.1.1, normSt G₂ k y.1.2)) <$>
        (simulateQ (aeadSecurityImpl ae lenM clen false K)
          ((redImplWith ae G₁ p len b t).run st)).run c =
      (authImplWith (fromAEADChain ae G₂) len b 0 (oracleDeliverBLookup G₂) t).run
        (normSt G₂ k st) := by
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | q) | q)
  · change (fun y => (y.1.1, normSt G₂ k y.1.2)) <$>
      (simulateQ (aeadSecurityImpl ae lenM clen false K) ((liftStep
      (oracleUnif _ _ AD M (ℕ × Cae) n)).run st)).run c = _
    rw [simulateQ_liftStep_run, Functor.map_map]
    exact oracleUnif_map _ _ _ n st
  · change _ = (oracleTransmitA (fromAEADChain ae G₂) (a, m)).run (normSt G₂ k st)
    simp only [redImplWith, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, redTransmitA,
      oracleTransmitA, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind, normSt_end_]
    by_cases hend : st.end_ = true
    · simp only [hend, ↓reduceIte, simulateQ_pure, StateT.run_pure, map_pure]
    · simp only [Bool.not_eq_true] at hend
      simp only [hend, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind]
      refine (redSend_map hkey hK hI _ _ _).trans ?_
      simp only [normSt_end_, hend]
      rfl
  · change _ = (oracleChallA (fromAEADChain ae G₂) len b (a, m₀, m₁)).run (normSt G₂ k st)
    simp only [redImplWith, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, redChallA,
      oracleChallA, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind, normSt_end_,
      normSt_corrA]
    by_cases hg : (st.end_ || st.corrA || decide (len m₀ ≠ len m₁)) = true
    · simp only [hg, ↓reduceIte, simulateQ_pure, StateT.run_pure, map_pure]
    · simp only [hg, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind]
      refine (redSend_map hkey hK hI _ _ _).trans ?_
      rfl
  · change (fun y => (y.1.1, normSt G₂ k y.1.2)) <$>
      (simulateQ (aeadSecurityImpl ae lenM clen false K) ((liftStep
      (oracleCorrALow _ _ AD M (ℕ × Cae) 0 u)).run st)).run c = _
    rw [simulateQ_liftStep_run, Functor.map_map]
    exact oracleCorrALow_map_normSt G₁ G₂ k 0 (fun q _ => hseed q) hI.seed
  · change (fun y => (y.1.1, normSt G₂ k y.1.2)) <$>
      (simulateQ (aeadSecurityImpl ae lenM clen false K) ((liftStep
      (oracleCorrBSilent _ _ AD M (ℕ × Cae) u)).run st)).run c = _
    rw [simulateQ_liftStep_run, Functor.map_map]
    exact oracleCorrBSilent_map_normSt G₂ k st
  · change (fun y => (y.1.1, normSt G₂ k y.1.2)) <$>
      (simulateQ (aeadSecurityImpl ae lenM clen false K) ((liftStep
      (oracleDeliverBLookup G₁ q)).run st)).run c = _
    rw [simulateQ_liftStep_run, Functor.map_map]
    exact oracleDeliverBLookup_map_normSt G₁ G₂ k hI.seed q
  · exact redInjectB_map hkey hK hI q

omit [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae] in
/-- A lookup delivery keeps the challenge facts. -/
theorem chal_deliver {G : ℕ → W → W × Kae} {k : W} {p : ℕ} {st : CState W Kae AD M Cae}
    (hon : OnChain G k st.vB) (i : ℕ) :
    let st' := { st with vB := ((rcvKey G st.vB i).map Prod.fst).getD st.vB }.delete i
    st.iA ≤ st'.iA ∧ (∀ r ∈ st.trans, r.1 = p → r ∈ st'.trans ∨ Consumed st'.vB p) ∧
      (Consumed st.vB p → Consumed st'.vB p) ∧ OnChain G k st'.vB := by
  intro st'
  obtain ⟨hon', hci, hold⟩ := consumed_rcvKey_getD hon i
  refine ⟨le_rfl, fun r hr hrp => ?_, hold p, hon'⟩
  by_cases hi : i = p
  · exact .inr (hi ▸ hci)
  · exact .inl (List.mem_filter.mpr ⟨hr, by simp only [hrp, ne_eq, decide_eq_true_eq]; omega⟩)

omit [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae] in
/-- `normR` keeps the indices that B has used. -/
theorem consumed_of_normR {G : ℕ → W → W × Kae} {k : W} {vB : RecvState W Kae} {q : ℕ}
    (h : Consumed (normR G k vB) q) : Consumed vB q :=
  ⟨Option.map_eq_none_iff.mp h.1, h.2⟩

/-- A's step in `E_p` keeps `RedInv`. If A's record at `p` is dropped because an injection used
`p`, then B has used `p` (`AuthInv`). -/
theorem redInv_redSend {G₁ G₂ : ℕ → W → W × Kae} {k : W} {p : ℕ} {K : Kae}
    {st : CState W Kae AD M Cae} {c : Option ((ℕ × AD) × Cae)} {h : AuthHist}
    (hI : RedInv G₁ k p st c) (hA : AuthInv G₂ k (normSt G₂ k st, h)) (isChall : Bool) (a : AD)
    (m : M) :
    ∀ y ∈ support ((simulateQ (aeadSecurityImpl ae lenM clen false K)
      ((redSend ae G₁ p isChall a m).run st)).run c), RedInv G₁ k p y.1.2 y.2 := by
  intro y hy
  have hrec (st₀ : CState W Kae AD M Cae) (e : ℕ × Cae) :
      ∀ r ∈ st₀.trans, r ∈ (st₀.record isChall a m e).trans := by
    intro r hr
    unfold GameState.record
    split_ifs <;> first | exact hr | exact List.mem_append_left _ hr
  by_cases hp : st.iA + 1 = p
  · subst hp
    have hc : c = none := hI.none_of_lt (by omega)
    subst hc
    have he : aeadSecurityImpl ae lenM clen false K (Sum.inl (Sum.inr ((st.iA + 1, a), m))) =
        oracleEncrypt ae lenM clen false K ((st.iA + 1, a), m) := rfl
    simp only [redSend, StateT.run_mk, ↓reduceIte, simulateQ_bind, simulateQ_spec_query, he,
      oracleEncrypt, Bool.false_eq_true, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, StateT.run_map, StateT.run_set, map_pure, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨(hI.seed.send ae a m).record _ _ _ _,
      fun h' => by rw [GameState.record_iA] at h'; simp only at h'; omega,
      fun a' e' hc => ?_, fun x hx => by rw [← Option.some.inj hx]⟩
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hc
    obtain ⟨rfl, rfl⟩ := hc
    unfold GameState.record
    split_ifs with hskip
    · refine .inr ?_
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hskip
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hA.corrA hskip.1)
      have htA : t ≤ st.iA := (hA.minCorrA t ht).2
      exact consumed_of_normR (hA.comp t ht (st.iA + 1) (by omega) hskip.2)
    all_goals exact .inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl⟩
  · simp only [redSend, StateT.run_mk, hp, ↓reduceIte, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨h₁, h₂⟩ := chal_mono hI.none_of_lt hI.chal (st' := { st with
      vA := (send ae G₁ st.vA a m).1, iA := st.iA + 1 }.record isChall a m
      (send ae G₁ st.vA a m).2) (by rw [GameState.record_iA]; simp only; omega)
      (fun r hr _ => .inl (hrec { st with vA := (send ae G₁ st.vA a m).1, iA := st.iA + 1 } _ r hr))
      (by rw [GameState.record_vB]; exact id)
    exact ⟨(hI.seed.send ae a m).record _ _ _ _, h₁, h₂, hI.chal_pos⟩

/-- B's step in `E_p` keeps `RedInv`. -/
theorem redInv_redInjectB {G₁ : ℕ → W → W × Kae} {k : W} {p : ℕ} {K : Kae}
    {st : CState W Kae AD M Cae} {c : Option ((ℕ × AD) × Cae)} (hI : RedInv G₁ k p st c)
    (q : AD × (ℕ × Cae)) :
    ∀ y ∈ support ((simulateQ (aeadSecurityImpl ae lenM clen false K)
      ((redInjectB ae G₁ p q).run st)).run c), RedInv G₁ k p y.1.2 y.2 := by
  obtain ⟨a, i, e⟩ := q
  intro y hy
  simp only [redInjectB, StateT.run_mk] at hy
  by_cases hg : (st.end_ || (st.findTrans a (i, e)).isSome) = true
  · simp only [hg, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    exact hI
  simp only [hg, Bool.false_eq_true, ↓reduceIte] at hy
  rcases hr : rcvKey G₁ st.vB i with _ | ⟨vB', K'⟩
  · simp only [hr, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact hI
  simp only [hr] at hy
  -- the new state, if B accepts
  set stN := { st with vB := vB', win := st.win || !st.comp i, end_ := !st.comp i }.delete i
    with hstN
  have hnew : RedInv G₁ k p stN c := by
    obtain ⟨hci, hold⟩ := consumed_of_rcvKey_some hI.seed.vB hr
    obtain ⟨h₁, h₂⟩ := chal_mono hI.none_of_lt hI.chal
      (st' := { st with vB := vB', win := st.win || !st.comp i, end_ := !st.comp i }.delete i)
      le_rfl (fun r hr' hrp => by
        by_cases hip : i = p
        · exact .inr (hip ▸ hci)
        · exact .inl (List.mem_filter.mpr
            ⟨hr', by simp only [hrp, ne_eq, decide_eq_true_eq]; omega⟩))
      (hold p)
    exact ⟨⟨hI.seed.vA_w, hI.seed.vA_iA, (rcvKey_some G₁ hI.seed.vB hr).2.2.1⟩, h₁, h₂,
      hI.chal_pos⟩
  by_cases hip : i = p
  · subst hip
    have hd : aeadSecurityImpl ae lenM clen false K (Sum.inr ((i, a), e)) =
        oracleDecrypt ae false K ((i, a), e) := rfl
    simp only [↓reduceIte, simulateQ_bind, simulateQ_spec_query, hd, oracleDecrypt,
      StateT.run_bind, StateT.run_get, pure_bind, support_bind, Set.mem_iUnion,
      exists_prop] at hy
    obtain ⟨⟨_ | m', c'⟩, hx, hy⟩ := hy
    all_goals
      have hx2 : c' = c := by
        split_ifs at hx <;>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx <;>
          exact hx.2
      subst hx2
      dsimp only at hy
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
    · exact hI
    · exact hnew
  · simp only [hip, ↓reduceIte, pure_bind] at hy
    rcases hdec : ae.decrypt K' (i, a) e with _ | m' <;>
      simp only [hdec, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hy <;>
      subst hy
    · exact hI
    · exact hnew

/-- The steps of a lifted game step are the game's steps, with the AEAD state unchanged. -/
theorem mem_support_liftStep {β : Bool} {K : Kae} {α : Type}
    {x : GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae) α} {st : CState W Kae AD M Cae}
    {c : Option ((ℕ × AD) × Cae)} {y : (α × CState W Kae AD M Cae) × Option ((ℕ × AD) × Cae)}
    (hy : y ∈ support ((simulateQ (aeadSecurityImpl ae lenM clen β K)
      ((liftStep x).run st)).run c)) : ∃ z ∈ support (x.run st), y = (z, c) := by
  rw [simulateQ_liftStep_run, support_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨z, hz, rfl⟩

omit [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae] in
/-- A step that changes neither A, nor B, nor `i_A`, nor `trans` keeps `RedInv`. -/
theorem RedInv.of_eq {G₁ : ℕ → W → W × Kae} {k : W} {p : ℕ} {st st' : CState W Kae AD M Cae}
    {c : Option ((ℕ × AD) × Cae)} (hI : RedInv G₁ k p st c) (hA : st'.vA = st.vA)
    (hi : st'.iA = st.iA) (ht : st'.trans = st.trans) (hB : st'.vB = st.vB) :
    RedInv G₁ k p st' c :=
  ⟨⟨hA ▸ hI.seed.vA_w, hA ▸ hi ▸ hI.seed.vA_iA, hB ▸ hI.seed.vB⟩, hi ▸ hI.none_of_lt,
    hB ▸ ht ▸ hI.chal, hI.chal_pos⟩

/-- Every step of `E_p` in the real world keeps `RedInv`. -/
theorem redInv_step {G₁ G₂ : ℕ → W → W × Kae} {k : W} {p : ℕ} {K : Kae} (len : M → ℕ) (b : Bool)
    {st : CState W Kae AD M Cae} {c : Option ((ℕ × AD) × Cae)} {h : AuthHist}
    (hI : RedInv G₁ k p st c) (hA : AuthInv G₂ k (normSt G₂ k st, h))
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain) :
    ∀ y ∈ support ((simulateQ (aeadSecurityImpl ae lenM clen false K)
      ((redImplWith ae G₁ p len b t).run st)).run c), RedInv G₁ k p y.1.2 y.2 := by
  intro y hy
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | q) | q)
  · obtain ⟨z, hz, rfl⟩ := mem_support_liftStep (x := oracleUnif _ _ AD M (ℕ × Cae) n) hy
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hz
    obtain ⟨x, rfl⟩ := hz
    exact hI
  · change y ∈ support ((simulateQ (aeadSecurityImpl ae lenM clen false K)
      ((redTransmitA ae G₁ p (a, m)).run st)).run c) at hy
    simp only [redTransmitA, StateT.run_mk] at hy
    split_ifs at hy
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hI
    · exact redInv_redSend hI hA false a m y hy
  · change y ∈ support ((simulateQ (aeadSecurityImpl ae lenM clen false K)
      ((redChallA ae G₁ p len b (a, m₀, m₁)).run st)).run c) at hy
    simp only [redChallA, StateT.run_mk] at hy
    split_ifs at hy
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hI
    all_goals exact redInv_redSend hI hA true a _ y hy
  · obtain ⟨z, hz, rfl⟩ := mem_support_liftStep (x := oracleCorrALow _ _ AD M (ℕ × Cae) 0 u) hy
    simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz <;>
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_set, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz <;>
      subst hz <;>
      exact hI.of_eq rfl rfl rfl rfl
  · obtain ⟨z, hz, rfl⟩ := mem_support_liftStep (x := oracleCorrBSilent _ _ AD M (ℕ × Cae) u) hy
    simp only [oracleCorrBSilent, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz <;>
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_set, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz <;>
      subst hz <;>
      exact hI.of_eq rfl rfl rfl rfl
  · obtain ⟨z, hz, rfl⟩ := mem_support_liftStep (x := oracleDeliverBLookup G₁ q) hy
    obtain ⟨a, e⟩ := q
    simp only [oracleDeliverBLookup, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hI
    rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
    · simp only [hf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hI
    · simp only [hf, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨h₀, h₁, h₂, h₃⟩ := chal_deliver (p := p) hI.seed.vB i (st := st)
      obtain ⟨h₄, h₅⟩ := chal_mono hI.none_of_lt hI.chal h₀ h₁ h₂
      exact ⟨⟨hI.seed.vA_w, hI.seed.vA_iA, h₃⟩, h₄, h₅, hI.chal_pos⟩
  · exact redInv_redInjectB hI q y hy

/-- **`E_p` plays `H_p`.** Let the chains `G₁` (with the reduction's own key at `p`) and `G₂`
(with the AEAD key `K` at `p`) from `k` have the same seeds, and the same keys except at `p`. Then
in the real world the runs of `E_p`, with the game state normalized to `G₂` and the AEAD state
dropped, are the runs of `G_auth^0` for `G₂`. -/
theorem redGameImpl_run_map {G₁ G₂ : ℕ → W → W × Kae} {k : W} {p : ℕ} {K : Kae} (len : M → ℕ)
    (b : Bool) (hseed : ∀ q, chainState G₁ k q = chainState G₂ k q)
    (hkey : ∀ q, 1 ≤ q → q ≠ p → chainKey G₁ k q = chainKey G₂ k q) (hK : chainKey G₂ k p = K)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :
    Prod.map id (fun s : (CState W Kae AD M Cae × AuthHist) × Option ((ℕ × AD) × Cae) =>
        (normSt G₂ k s.1.1, s.1.2)) <$>
      (simulateQ (redGameImpl ae lenM clen G₁ p len b false K) adversary).run
        ((.init (fromAEADChain ae G₁) k, .init), none) =
      authRun ae G₂ len b 0 adversary k := by
  set ψ := fun s : (CState W Kae AD M Cae × AuthHist) × Option ((ℕ × AD) × Cae) =>
    (normSt G₂ k s.1.1, s.1.2)
  have hproj : ∀ t s, RedInv G₁ k p s.1.1 s.2 →
      Prod.map id ψ <$> (redGameImpl ae lenM clen G₁ p len b false K t).run s =
        (authImplC ae G₂ len b 0 t).run (ψ s) := by
    rintro t ⟨⟨st, h⟩, c⟩ hI
    rw [redGameImpl, redImpl, OracleComp.flattenStateT_mapStateTBase_extendState_run, authImplC,
      authImpl, QueryImpl.extendState_apply,
      ← redImplWith_map (ae := ae) (lenM := lenM) (clen := clen) len b hseed hkey hK hI t]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    congr 1
    funext y
    rcases t with ((((((n | q) | q) | u) | u) | q) | q) <;> rfl
  refine map_run_simulateQ_eq_of_query_map_eq_inv' _ _
    (fun s => RedInv G₁ k p s.1.1 s.2 ∧ HistInv 0 (ψ s) ∧ AuthInv G₂ k (ψ s)) ψ ?_
    (fun t s hs => hproj t s hs.1) adversary _ ⟨⟨⟨rfl, rfl, ⟨rfl, fun _ _ h => (nomatch h),
      fun _ _ => rfl⟩⟩, fun _ => rfl, fun _ _ h => (nomatch h), fun _ h => (nomatch h)⟩,
      histInv_init 0 rfl, ⟨⟨rfl, fun _ _ h => (nomatch h), fun _ _ => rfl⟩, fun h => (nomatch h),
      fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h)⟩⟩
  rintro t ⟨⟨st, h⟩, c⟩ ⟨hI, hH, hA⟩ y hy
  have hy' : Prod.map id ψ y ∈ support ((authImplC ae G₂ len b 0 t).run (ψ ((st, h), c))) := by
    rw [← hproj t _ hI, support_map]
    exact ⟨y, hy, rfl⟩
  refine ⟨?_, authImpl_histInv _ len b 0 (oracleDeliverBLookup_flags G₂) t _ hH _ hy',
    authInv_step ae G₂ k len b 0 t _ hH hA _ hy'⟩
  rw [redGameImpl, redImpl,
    OracleComp.flattenStateT_mapStateTBase_extendState_run, support_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact redInv_step len b hI hA t x hx

/-- `E_p` inside the one-time IND-CCA game with bit `β` and key `K`: it samples the table, the key
and the bit, and runs the joint oracles. -/
theorem aeadRed_run [SampleableType W] [SampleableType Kae] (prg : PRGScheme W (W × Kae))
    (len : M → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (p : ℕ) (β : Bool) (K : Kae) :
    (do
      let z ← (simulateQ (aeadSecurityImpl ae lenM clen β K)
        (aeadRed ae prg len adversary p)).run none
      pure z.1 : ProbComp Bool) =
    (do
      let U ← sampleTab p
      let k ← $ᵗ W
      let b ← $ᵗ Bool
      (fun y => winIn p p y.2.1.2) <$>
        (simulateQ (redGameImpl ae lenM clen (hybGen prg U) p len b β K) adversary).run
          ((.init (fromAEADChain ae (hybGen prg U)) k, .init), none)) := by
  simp only [aeadRed, simulateQ_bind, simulateQ_aeadSecurityImpl_liftComp, simulateQ_pure,
    StateT.run_bind, liftM, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    StateT.run_pure]
  simp only [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, bind_pure_comp,
    Functor.map_map]
  rfl

/-- **The real world of `E_p`** is the hybrid `H_p`: `E_p` outputs 1 with the probability of a
first win at `p` in `H_p`. The key of the AEAD game is uniform (`hkg`), as the key at `p` of
`H_p`. -/
theorem aeadReal_aeadRed [SampleableType W] [SampleableType Kae]
    (hkg : ae.keygen =ᵈ ($ᵗ Kae : ProbComp Kae)) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (n : ℕ) :
    Pr{let x ← securityExpFixedBit ae lenM clen (aeadRed ae prg len adversary (n + 1)) false}[
        x = true] =
      Pr{let z ← hybExp ae prg len 0 adversary (n + 1)}[winIn (n + 1) (n + 1) z.2.2 = true] := by
  rw [← prEvent_map (hybExp ae prg len 0 adversary (n + 1))
    (fun z => winIn (n + 1) (n + 1) z.2.2) (· = true)]
  refine EvalDistEq.prEvent_eq ?_ _
  unfold securityExpFixedBit
  refine (EvalDistEq.bind_left hkg _).trans ?_
  simp only [aeadRed_run, hybExp, authExp, sampleTab, bind_assoc, pure_bind, map_bind]
  refine (EvalDistEq.bind_bind_swap (spec := unifSpec) _ _ _).trans
    (EvalDistEq.bind_congr_of_support _ fun U' _ => ?_)
  have hX (u : W × Kae) (K : Kae) (k : W) (b : Bool) :
      (fun y => winIn (n + 1) (n + 1) y.2.1.2) <$>
        (simulateQ (redGameImpl ae lenM clen (hybGen prg (Function.update U' (n + 1) (some u)))
          (n + 1) len b false K) adversary).run
          ((GameState.init (fromAEADChain ae (hybGen prg (Function.update U' (n + 1) (some u)))) k,
            AuthHist.init), none) =
      (fun z => winIn (n + 1) (n + 1) z.2.2) <$>
        authRun ae (hybGen prg (Function.update U' (n + 1) (some (u.1, K)))) len b 0
          adversary k := by
    set G₁ := hybGen prg (Function.update U' (n + 1) (some u))
    set G₂ := hybGen prg (Function.update U' (n + 1) (some (u.1, K)))
    have h₂ := chain_hybGen_of_some prg (Function.update U' (n + 1) (some (u.1, K))) k
      (q := n + 1) (by omega) (u := (u.1, K)) (Function.update_self _ _ _)
    have hseed : ∀ q, chainState G₁ k q = chainState G₂ k q :=
      chainState_update_key prg U' (n + 1) u.1 u.2 K k
    have hkey : ∀ q, 1 ≤ q → q ≠ n + 1 → chainKey G₁ k q = chainKey G₂ k q :=
      fun q _ hq => chainKey_update_key prg U' (n + 1) u.1 u.2 K k hq
    rw [← redGameImpl_run_map len b hseed hkey h₂.2 adversary, Functor.map_map]
    rfl
  simp only [hX]
  exact ToVCVio.uniformSample_prod_replace_snd fun v => do
    let k ← $ᵗ W
    let b ← $ᵗ Bool
    (fun z => winIn (n + 1) (n + 1) z.2.2) <$>
      authRun ae (hybGen prg (Function.update U' (n + 1) (some v))) len b 0 adversary k

/-- In the ideal world, `E_p` accepts no injection at `p`: every decryption fails. -/
theorem redInjectB_ideal {G : ℕ → W → W × Kae} {p : ℕ} {K : Kae} (st : CState W Kae AD M Cae)
    (c : Option ((ℕ × AD) × Cae)) (q : AD × (ℕ × Cae)) :
    ∀ x ∈ support ((simulateQ (aeadSecurityImpl ae lenM clen true K)
      ((redInjectB ae G p q).run st)).run c), ∀ i m, x.1 = (some (i, m), x.1.2) → i ≠ p := by
  obtain ⟨a, i, e⟩ := q
  intro x hx i' m' hx1
  simp only [redInjectB, StateT.run_mk] at hx
  by_cases hg : (st.end_ || (st.findTrans a (i, e)).isSome) = true
  · simp only [hg, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hx
    subst hx
    simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hx1
  simp only [hg, Bool.false_eq_true, ↓reduceIte] at hx
  rcases hr : rcvKey G st.vB i with _ | ⟨vB', K'⟩
  · simp only [hr, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hx1
  simp only [hr] at hx
  by_cases hip : i = p
  · subst hip
    have hd : aeadSecurityImpl ae lenM clen true K (Sum.inr ((i, a), e)) =
        oracleDecrypt ae true K ((i, a), e) := rfl
    simp only [↓reduceIte, simulateQ_bind, simulateQ_spec_query, hd, oracleDecrypt,
      Bool.true_or, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hx1
  · simp only [hip, ↓reduceIte, pure_bind] at hx
    rcases hdec : ae.decrypt K' (i, a) e with _ | m <;>
      simp only [hdec, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hx <;>
      subst hx
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hx1
    · simp only [Prod.mk.injEq, Option.some.injEq] at hx1
      exact hx1.1.1 ▸ hip

/-- **The ideal world of `E_p`**: no first win at `p`, so `E_p` outputs 0. -/
theorem aeadIdeal_aeadRed [SampleableType W] [SampleableType Kae] (prg : PRGScheme W (W × Kae))
    (len : M → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (p : ℕ) :
    Pr{let x ← securityExpFixedBit ae lenM clen (aeadRed ae prg len adversary p) true}[
        x = true] = 0 := by
  unfold securityExpFixedBit
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun x hx => ?_
  simp only [mem_support_bind_iff] at hx
  obtain ⟨K, -, hx⟩ := hx
  rw [← mem_support_bind_iff, aeadRed_run] at hx
  simp only [mem_support_bind_iff, support_map, Set.mem_image] at hx
  obtain ⟨U, -, k, -, b, -, y, hy, rfl⟩ := hx
  have hinv := simulateQ_run_preserves_inv_of_query
    (redGameImpl ae lenM clen (hybGen prg U) p len b true K)
    (fun s => s.1.2.firstWin ≠ some p) ?_ adversary _ (by simp only [AuthHist.init, ne_eq,
      reduceCtorEq, not_false_eq_true]) y hy
  · unfold winIn
    split
    · rename_i q hq
      have : q ≠ p := fun h => hinv (h ▸ hq)
      simp only [decide_eq_true_eq, not_and]
      omega
    · simp only [Bool.false_eq_true, not_false_eq_true]
  rintro t ⟨⟨st, h⟩, c⟩ hs z hz
  rw [redGameImpl, redImpl,
    OracleComp.flattenStateT_mapStateTBase_extendState_run, support_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rcases t with ((((((n | q) | q) | u) | u) | q) | q)
  any_goals exact hs
  · simp only [authAux]
    split_ifs
    · exact hs
    · exact hs
  · simp only [authAux]
    split_ifs
    · rcases hx1 : x.1.1 with _ | ⟨i, m⟩
      · simp only [Option.map_none, ne_eq, reduceCtorEq, not_false_eq_true]
      · simp only [Option.map_some, ne_eq, Option.some.injEq]
        exact redInjectB_ideal st c q x hx i m (by rw [← hx1]; rfl)
    · exact hs

/-- **The advantage of `E_{n+1}`** is the probability of a first win at `n + 1` in `H_{n+1}`. -/
theorem distAdvantage_aeadRed [SampleableType W] [SampleableType Kae]
    (hkg : ae.keygen =ᵈ ($ᵗ Kae : ProbComp Kae)) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (n : ℕ) :
    distAdvantage ae lenM clen (aeadRed ae prg len adversary (n + 1)) =
      (Pr{let z ← hybExp ae prg len 0 adversary (n + 1)}[
        winIn (n + 1) (n + 1) z.2.2 = true]).toReal := by
  rw [distAdvantage, aeadIdeal_aeadRed, aeadReal_aeadRed hkg, ENNReal.toReal_zero, zero_sub,
    abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]

end Run

end FromAEADPRG

end FSAEADScheme
