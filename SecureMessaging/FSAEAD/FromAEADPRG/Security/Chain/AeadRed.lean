/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.Chain.Transfer
public import VCVio.OracleComp.SimSemantics.StateT.StateSeparating

/-!
# FS-AEAD from AEAD and PRG — the monad of the AEAD reductions

An AEAD reduction plays the FS-AEAD game inside the one-time IND-CCA game of `ae`. Its monad
`RedM` is the game state over the oracles of the AEAD game (`AeadSpec`). `liftStep` and
`liftImpl` lift a step and an oracle of the FS-AEAD game to `RedM`. `redSend` is A's send at
position `i_A + 1`: at the reduction's position it calls the encryption oracle.

- `simulateQ_liftStep_run`, `mem_support_liftStep`: a lifted step keeps the state of the AEAD
  game.

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

variable [DecidableEq AD] [DecidableEq Cae]

/-! ## The reduction in the AEAD game -/

section Run

variable [LenSampleable Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (lenM : M → ℕ)
  (clen : ℕ → ℕ)

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

variable {ae lenM clen}

/-- The steps of a lifted game step are the game's steps, with the AEAD state unchanged. -/
theorem mem_support_liftStep {β : Bool} {K : Kae} {α : Type}
    {x : GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae) α} {st : CState W Kae AD M Cae}
    {c : Option ((ℕ × AD) × Cae)} {y : (α × CState W Kae AD M Cae) × Option ((ℕ × AD) × Cae)}
    (hy : y ∈ support ((simulateQ (aeadSecurityImpl ae lenM clen β K)
      ((liftStep x).run st)).run c)) : ∃ z ∈ support (x.run st), y = (z, c) := by
  rw [simulateQ_liftStep_run, support_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨z, hz, rfl⟩

end Run

end FromAEADPRG

end FSAEADScheme
