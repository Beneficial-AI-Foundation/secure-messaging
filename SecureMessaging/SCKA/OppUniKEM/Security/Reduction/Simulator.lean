/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

/-!
# The IND-CPA adversary and its fixed branches

**Setting.** `adv` is a security adversary, `q` a send budget, `e` a challenge epoch, and
`(pkStar, ctStar, kStar)` an IND-CPA challenge. A *marked* value is `some x` (known) or `none`
(unavailable); a marked protocol field is `none` (absent), `some none`, or `some (some x)`.

**Definitions.**

- `securityReduction adv q`: `e ← epochChoice q`, then `run adv e pkStar ctStar kStar`: the output
  of `adv` against the simulator `oracle e pkStar ctStar kStar`, or `false` if it terminates.
  The simulator embeds `pkStar`, `ctStar` at epoch `e` with unavailable secrets and coins, lets
  A's receive output B's recorded key, and terminates when a permitted corruption or leaking send
  reveals an unavailable value. Its challenge oracle is `challenge` (`challengeWith`).
- `fixedBranch adv e b`: `(pk, _) ← keygen; (ct, k) ← encaps pk; k' ←$ K;
  run adv e pk ct (if b then k else k')`.
- *Complete material* `m : Material leak`: the outputs and coins of the three sampling phases of
  one epoch, sampled by `sampleMaterial leak`.
- `Pinned.kem m pinKeygen pinOffline pinOnline key`: the flagged phases are *pinned*, returning
  the stored outputs of `m`; decapsulation returns `key`.

**Results.** Write `Δ(G) := Pr[G true = true] - Pr[G false = true]` for bit-indexed `G`.

- `securityReduction_signed_gap_average`: for `q > 0`,
  `Δ(IND_CPA_Exp (securityReduction adv q)) = q⁻¹ · ∑_{e=1}^{q} Δ(fixedBranch adv e)`.
- `fixedBranch_eq_material`: `fixedBranch adv e b` equals the same computation with
  `(pk, ct, k)` taken from `m ← sampleMaterial leak`.
-/

/-! ## The simulator -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C : Type}

/-- Simulator key generation: `(pkStar, unavailable)` if `selected`, else `kem.keygen` with a
known secret key. -/
-- ANCHOR: embedding_primitives
def keygen (kem : KEMScheme ProbComp K PK SK C) (selected : Bool) (pkStar : PK) :
    ProbComp (PK × Option SK) :=
  if selected then pure (pkStar, none) else Prod.map id some <$> kem.keygen

/-- Simulator offline encapsulation: the offline part of `ctStar` with an unavailable state if
`selected`, else `onoff.encapsOff` with a known state. -/
def encapsOff {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (selected : Bool) (ctStar : C) : ProbComp (Option onoff.St × onoff.C₀) :=
  if selected then pure (none, (onoff.split ctStar).1)
  else Prod.map some id <$> onoff.encapsOff

/-- Simulator online encapsulation: the online part of `ctStar` with an unavailable key for an
unavailable state, else `onoff.encapsOn st pk` with a known key. -/
def encapsOn {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (ctStar : C) (st : Option onoff.St) (pk : PK) : ProbComp (onoff.C₁ × Option K) :=
  match st with
  | none => pure ((onoff.split ctStar).2, none)
  | some st => Prod.map id some <$> onoff.encapsOn st pk
-- ANCHOR_END: embedding_primitives

/-- Marked KEM of one simulator query, built from `keygen`, `encapsOff`, and `encapsOn` with the
flags `selectedA`, `selectedB`; decapsulation returns `key`, B's recorded key for A's epoch. -/
abbrev kem (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    KEMScheme ProbComp (Option K) PK (Option SK) C where
  keygen := keygen base selectedA pkStar
  encaps pk := do
    let (st, ct0) ← encapsOff onoff selectedB ctStar
    let (ct1, key) ← encapsOn onoff ctStar st pk
    pure (onoff.split.symm (ct0, ct1), key)
  decaps _ _ := pure key

/-- Deterministic-decapsulation witness for `kem`. -/
abbrev deterministic (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (kem base onoff selectedA selectedB pkStar ctStar key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- On/off structure of `kem`, with marked offline states. -/
abbrev onOff (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (kem base onoff selectedA selectedB pkStar ctStar key).OnOffStructure where
  St := Option onoff.St
  C₀ := onoff.C₀
  C₁ := onoff.C₁
  split := onoff.split
  encapsOff := encapsOff onoff selectedB ctStar
  encapsOn := encapsOn onoff ctStar
  factor _ := rfl

/-- Leaking version of `keygen`; the coins are marked like the secret key. -/
def keygenLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (selected : Bool) (pkStar : PK) :
    ProbComp ((PK × Option SK) × Option leak.KeygenRand) :=
  if selected then pure ((pkStar, none), none)
  else (fun z => ((z.1.1, some z.1.2), some z.2)) <$> leak.keygenRleak

/-- Leaking version of `encapsOff`; the coins are marked like the state. -/
def offLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (selected : Bool) (ctStar : C) :
    ProbComp ((Option onoff.St × onoff.C₀) × Option leak.OffRand) :=
  if selected then pure ((none, (onoff.split ctStar).1), none)
  else (fun z => ((some z.1.1, z.1.2), some z.2)) <$> leak.encapsOffRleak

/-- Leaking version of `encapsOn`; the coins are marked like the key. -/
def onLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (ctStar : C) (st : Option onoff.St) (pk : PK) :
    ProbComp ((onoff.C₁ × Option K) × Option leak.OnRand) :=
  match st with
  | none => pure (((onoff.split ctStar).2, none), none)
  | some st => (fun z => ((z.1.1, some z.1.2), some z.2)) <$> leak.encapsOnRleak st pk

/-- Leakage witness for `kem` with the samplers `keygenLeak`, `offLeak`, and `onLeak`. -/
abbrev leakage (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (kem base onoff selectedA selectedB pkStar ctStar key).OnOffRandLeak
      (onOff base onoff selectedA selectedB pkStar ctStar key) where
  KeygenRand := Option leak.KeygenRand
  OffRand := Option leak.OffRand
  OnRand := Option leak.OnRand
  keygenRleak := keygenLeak leak selectedA pkStar
  encapsOffRleak := offLeak leak selectedB ctStar
  encapsOnRleak := onLeak leak ctStar
  keygen_fst := by
    cases selectedA <;>
      simp [keygenLeak, keygen, ← leak.keygen_fst, map_eq_bind_pure_comp, Prod.map]
  encapsOff_fst := by
    cases selectedB <;>
      simp [offLeak, encapsOff, ← leak.encapsOff_fst, map_eq_bind_pure_comp, Prod.map]
  encapsOn_fst st pk := by
    cases st <;> simp [onLeak, encapsOn, ← leak.encapsOn_fst, map_eq_bind_pure_comp, Prod.map]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Simulator game state: A's secret key, B's offline state, and the recorded keys are marked. -/
abbrev SimState {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (Sym : Type) :=
  SCKAScheme.GameState (StateA (Option SK) PK onoff.C₀ Sym)
    (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) (Option K) (Message Sym)

/-- Unmark a field: absent gives `some none`, known `x` gives `some (some x)`, and unavailable
gives `none` (termination). -/
-- ANCHOR: embedding_revealField
def revealField {α : Type} : Option (Option α) → Option (Option α)
  | none => some none
  | some none => none
  | some (some a) => some (some a)
-- ANCHOR_END: embedding_revealField

/-- Unmark A's state; `none` exactly when its secret key is unavailable. -/
def revealA {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (s : StateA (Option SK) PK onoff.C₀ Sym) : Option (StA onoff Sym) := do
  let dk ← revealField s.dkA
  pure { dkA := dk, ekA := s.ekA, ct0 := s.ct0, t := s.t,
         ich := s.ich, lch := s.lch, ack := s.ack }

/-- Unmark B's state; `none` exactly when its offline state is unavailable. -/
def revealB {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (s : StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) : Option (StB onoff Sym) := do
  let st ← revealField s.stCt
  pure { ekA := s.ekA, ct0 := s.ct0, ct1 := s.ct1, stCt := st, t := s.t,
         ich := s.ich, lch := s.lch, ack := s.ack }

/-- Unmark the coins of a leaking send; `none` exactly when a returned coin is unavailable. -/
-- ANCHOR: embedding_revealCoins
def revealCoins {KG OFF ON : Type} :
    SendRand (Option KG) (Option OFF) (Option ON) → Option (SendRand KG OFF ON)
  | .none => some .none
  | .keygen r => .keygen <$> r
  | .off r => .off <$> r
  | .on r => .on <$> r
  | .offOn r₀ r₁ => do pure (.offOn (← r₀) (← r₁))
-- ANCHOR_END: embedding_revealCoins

/-- Unmark an optional answer: a rejection gives `some none`, an answer `a` gives
`some <$> reveal a`. -/
def revealResponse {α β : Type} (reveal : α → Option β) : Option α → Option (Option β)
  | none => some none
  | some a => some <$> reveal a

/-- Run `op` and unmark its answer; a failed unmarking terminates the simulation. -/
def revealAfter {σ α β : Type} (reveal : α → Option β) (op : StateT σ ProbComp α) :
    OptionT (StateT σ ProbComp) β :=
  OptionT.mk (do pure (reveal (← op)))

/-- `revealAfter reveal op` from `s` returns `reveal a` with the successor state of `op`. -/
theorem revealAfter_run {σ α β : Type} (reveal : α → Option β)
    (op : StateT σ ProbComp α) (s : σ) :
    ((revealAfter reveal op).run).run s =
      (do let (a, s') ← op.run s; pure (reveal a, s')) := by
  rfl

/-- Challenge oracle on game states with key-table entries `κ`, read as keys by `toKey`. It
rejects a challenge that is not eligible (A's table is consulted before B's); otherwise it adds
`t` to `challenged` and returns a uniform key if `0 < t < e`, `kStar` if `t = e`, and `toKey` of
the recorded entry otherwise. -/
-- ANCHOR: embedding_challenge
def challengeWith [SampleableType K] {σA σB κ ρ : Type} (toKey : κ → K) (e : ℕ) (kStar : K) :
    QueryImpl (ℕ →ₒ Option K) (StateT (SCKAScheme.GameState σA σB κ ρ) ProbComp) :=
  fun t => do
    let s ← get
    if t ∈ s.exposed ∨ t ∈ s.challenged then pure none
    else
      let key := match s.keyA t with
        | some k => some k
        | none => s.keyB t
      match key with
      | none => pure none
      | some honest =>
        let k ← if 0 < t ∧ t < e then liftM ($ᵗ K : ProbComp K)
          else pure (if t = e then kStar else toKey honest)
        set { s with challenged := insert t s.challenged }
        pure (some k)

/-- Simulator challenge oracle: an unavailable recorded key is read as `kStar`. -/
def challenge [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) : QueryImpl (ℕ →ₒ Option K) (StateT (SimState onoff Sym) ProbComp) :=
  challengeWith (fun key : Option K => key.getD kStar) e kStar
-- ANCHOR_END: embedding_challenge

/-- Simulator oracles: a query from `s` uses the Opp-UniKEM oracles over `kem` with
`selectedA := (s.stA.t = e)`, `selectedB := (s.stB.t = e)`, `key := s.keyB s.stA.t`, and
`challenge e kStar`. Corruptions and leaking sends unmark after their exposure guard: a rejection
answers `none`, an unavailable value terminates the simulation. -/
-- ANCHOR: embedding_oracle
def oracle [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (e : ℕ) (pkStar : PK) (ctStar : C) (kStar : K) :
    QueryImpl (securitySpec leak Sym) (OptionT (StateT (SimState onoff Sym) ProbComp)) :=
  fun t => (get : OptionT (StateT (SimState onoff Sym) ProbComp) (SimState onoff Sym)) >>= fun s =>
    let selectedA := decide (s.stA.t = e)
    let selectedB := decide (s.stB.t = e)
    let key := s.keyB s.stA.t
    let simKem := kem base onoff selectedA selectedB pkStar ctStar key
    let simOnOff := onOff base onoff selectedA selectedB pkStar ctStar key
    let simLeak := leakage base onoff leak selectedA selectedB pkStar ctStar key
    let scka := scheme simKem simOnOff
      (deterministic base onoff selectedA selectedB pkStar ctStar key) ecEk ecCt0 ecCt1 simLeak
    match (motive := ∀ query,
        OptionT (StateT (SimState onoff Sym) ProbComp) ((securitySpec leak Sym).Range query)) t with
    | .inl (.inl (.inl (.inl (.inl t)))) =>
      liftM (SCKAScheme.sckaCorrectnessImpl scka t)
    | .inl (.inl (.inl (.inl (.inr u)))) =>
      revealAfter (revealResponse (fun (out : ℕ × Option ℕ × Message Sym ×
          SendRand (Option leak.KeygenRand) (Option leak.OffRand) (Option leak.OnRand)) => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins)))
        (SCKAScheme.oracleSendArleak vulnRleakA scka u)
    | .inl (.inl (.inl (.inr u))) =>
      revealAfter (revealResponse (fun (out : ℕ × Option ℕ × Message Sym ×
          SendRand (Option leak.KeygenRand) (Option leak.OffRand) (Option leak.OnRand)) => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins)))
        (SCKAScheme.oracleSendBrleak vulnRleakB scka u)
    | .inl (.inl (.inr t)) => liftM (challenge (Sym := Sym) onoff e kStar t)
    | .inl (.inr u) =>
      revealAfter (revealResponse (revealA (onoff := onoff) (Sym := Sym)))
        (SCKAScheme.oracleCorruptA (vulnCorrA (Sym := Sym) simKem simOnOff)
          (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) (Option K) (Message Sym) u)
    | .inr u =>
      revealAfter (revealResponse (revealB (onoff := onoff) (Sym := Sym)))
        (SCKAScheme.oracleCorruptB (vulnCorrB (Sym := Sym) simKem simOnOff)
          (StateA (Option SK) PK onoff.C₀ Sym) (Option K) (Message Sym) u)
-- ANCHOR_END: embedding_oracle

/-- Initial simulator state: both parties at epoch `1` with absent local fields; empty tables
and sets. -/
def initial {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure) :
    SimState onoff Sym :=
  SCKAScheme.initGameState
    { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
      ack := { ekRec := false, ctRec := false } }
    { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0, lch := ∅,
      ack := { ekRec := false, ctRec := false } }

/-- Output of `adv` against `oracle e pkStar ctStar kStar` from `initial`, or `false` if the
simulation terminates. -/
-- ANCHOR: embedding_run
def run [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (e : ℕ) (pkStar : PK) (ctStar : C) (kStar : K) :
    ProbComp Bool := do
  let result ← ((simulateQ (oracle base onoff ecEk ecCt0 ecCt1 leak e pkStar ctStar kStar)
    adv).run).run' (initial onoff)
  pure (result.getD false)
-- ANCHOR_END: embedding_run

/-- Uniform on `{1, …, q}` if `q > 0`; `1` if `q = 0`. -/
-- ANCHOR: embedding_epochChoice
def epochChoice (q : ℕ) : ProbComp ℕ :=
  if hq : q = 0 then pure 1
  else
    letI : NeZero q := ⟨hq⟩
    (fun i : Fin q => i.val + 1) <$> ($ᵗ (Fin q) : ProbComp (Fin q))
-- ANCHOR_END: embedding_epochChoice

/-- IND-CPA adversary from `adv` and send budget `q`: on `pk`, sample `e ← epochChoice q`; on the
challenge `(ct, k)`, return `run adv e pk ct k`. -/
-- ANCHOR: securityReduction
def securityReduction [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) : base.IND_CPA_Adversary where
  State := PK × ℕ
  preChallenge pk := do pure (pk, ← epochChoice q)
  postChallenge state ct key := run base onoff ecEk ecCt0 ecCt1 leak adv state.2 state.1 ct key
-- ANCHOR_END: securityReduction

end oppUniKemCKA.Security.Embedding

/-! ## Fixed branches and stored epoch material -/

open ToVCVio OracleSpec OracleComp KEMScheme ENNReal

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
variable (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
variable (ecEk : ErasureCodePayload PK Sym)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)

/-- The reduction at epoch `e` with IND-CPA bit `b`: `run adv e pk ct k_b` for a fresh key pair
and encapsulation `(ct, k)`, with `k_true := k` and `k_false` independent uniform. -/
def fixedBranch (adv : SecurityAdversary leak Sym) (e : ℕ) (b : Bool) : ProbComp Bool := do
  let (pk, _) ← base.keygen
  let (ct, key) ← base.encaps pk
  let randomKey ← ($ᵗ K : ProbComp K)
  run base onoff ecEk ecCt0 ecCt1 leak adv e pk ct (if b then key else randomKey)

/-- `Pr[= output | IND_CPA_Exp (securityReduction adv q) b] =
Pr[= output | e ← epochChoice q; fixedBranch adv e b]`. -/
theorem securityReduction_probOutput
    (adv : SecurityAdversary leak Sym) (q : ℕ) (b output : Bool) :
    Pr[= output | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) b] =
    Pr[= output | do
      let e ← epochChoice q
      fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b] := by
  unfold KEMScheme.IND_CPA_Exp
  rw [probOutput_probCompRuntime_evalDist_eq]
  simp only [securityReduction, fixedBranch, ProbCompRuntime.probComp,
    ProbCompRuntime.liftProbComp, ProbCompLift.id, bind_assoc, pure_bind]
  exact probOutput_bind_bind_swap base.keygen (epochChoice q) _ output

/-- For `q ≠ 0`: `Pr[IND_CPA_Exp (securityReduction adv q) b = true] =
q⁻¹ · ∑_{e = 1}^{q} Pr[fixedBranch adv e b = true]`. -/
theorem securityReduction_acceptance_average
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : q ≠ 0) (b : Bool) :
    (Pr[= true | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) b]).toReal =
    (q : ℝ)⁻¹ * ∑ i : Fin q,
      (Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv (i.val + 1) b]).toReal := by
  rw [securityReduction_probOutput]
  let : NeZero q := ⟨hq⟩
  simp only [epochChoice, hq, ↓reduceDIte, bind_map_left, probOutput_bind_eq_sum_fintype,
    probOutput_uniformSample, Fintype.card_fin, ← Finset.mul_sum]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun _ _ => probOutput_ne_top)]

/-- For `q ≠ 0`: `Δ(IND_CPA_Exp (securityReduction adv q)) =
q⁻¹ · ∑_{e = 1}^{q} Δ(fixedBranch adv e)`. -/
theorem securityReduction_signed_gap_average
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : q ≠ 0) :
    (Pr[= true | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) true]).toReal -
    (Pr[= true | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) false]).toReal =
    (q : ℝ)⁻¹ * ∑ i : Fin q,
      ((Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv
        (i.val + 1) true]).toReal -
       (Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv
        (i.val + 1) false]).toReal) := by
  rw [securityReduction_acceptance_average base onoff ecEk ecCt0 ecCt1 leak adv q hq true,
    securityReduction_acceptance_average base onoff ecEk ecCt0 ecCt1 leak adv q hq false,
    Finset.sum_sub_distrib, mul_sub]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Complete material: the outputs and coins of the three sampling phases of one epoch. -/
structure Material {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) where
  /-- Public/secret key pair and the key-generation coins. -/
  keygen : (PK × SK) × leak.KeygenRand
  /-- Offline encapsulation state/ciphertext and its coins. -/
  off : (onoff.St × onoff.C₀) × leak.OffRand
  /-- Online ciphertext/shared key and its coins. -/
  on : (onoff.C₁ × K) × leak.OnRand

/-- Sample complete material; online encapsulation runs at the sampled state and public key. -/
def sampleMaterial {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) : ProbComp (Material leak) := do
  let kg ← leak.keygenRleak
  let off ← leak.encapsOffRleak
  let on ← leak.encapsOnRleak off.1.1 kg.1.1
  pure ⟨kg, off, on⟩

/-- The ciphertext reassembled from the stored offline and online components. -/
def Material.ciphertext {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) : C :=
  onoff.split.symm (m.off.1.2, m.on.1.1)

/-- `m ← sampleMaterial leak; f pk_m ct_m k_m` equals
`(pk, _) ← keygen; (ct, k) ← encaps pk; f pk ct k`. -/
theorem sampleMaterial_bind_challenge
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) {α : Type} (f : PK → C → K → ProbComp α) :
    (do
      let material ← sampleMaterial leak
      f material.keygen.1.1 material.ciphertext material.on.1.2) =
    (do
      let (pk, _) ← base.keygen
      let (ct, key) ← base.encaps pk
      f pk ct key) := by
  rw [← leak.keygen_fst]
  simp only [sampleMaterial, bind_assoc, pure_bind, Material.ciphertext]
  apply bind_congr
  intro kg
  rw [onoff.factor, ← leak.encapsOff_fst]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro off
  rw [← leak.encapsOn_fst]
  simp only [bind_assoc, pure_bind]

/-- Each component of a possible `m ← sampleMaterial leak` is a possible output of its leaking
sampler, online encapsulation at the stored state and public key. -/
theorem sampleMaterial_support
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (hm : m ∈ support (sampleMaterial leak)) :
    m.keygen ∈ support leak.keygenRleak ∧
    m.off ∈ support leak.encapsOffRleak ∧
    m.on ∈ support (leak.encapsOnRleak m.off.1.1 m.keygen.1.1) := by
  simp only [sampleMaterial, mem_support_bind_iff, mem_support_pure_iff] at hm
  obtain ⟨kg, hkg, off, hoff, on, hon, rfl⟩ := hm
  exact ⟨hkg, hoff, hon⟩

/-- Version of `sampleMaterial_support` for the samplers without coins. -/
theorem sampleMaterial_ordinary_support
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (hm : m ∈ support (sampleMaterial leak)) :
    m.keygen.1 ∈ support base.keygen ∧
    m.off.1 ∈ support onoff.encapsOff ∧
    m.on.1 ∈ support (onoff.encapsOn m.off.1.1 m.keygen.1.1) := by
  obtain ⟨hkg, hoff, hon⟩ := sampleMaterial_support leak m hm
  refine ⟨?_, ?_, ?_⟩
  · rw [← leak.keygen_fst]
    exact (mem_support_bind_iff _ _ _).mpr ⟨_, hkg, by simp⟩
  · rw [← leak.encapsOff_fst]
    exact (mem_support_bind_iff _ _ _).mpr ⟨_, hoff, by simp⟩
  · rw [← leak.encapsOn_fst]
    exact (mem_support_bind_iff _ _ _).mpr ⟨_, hon, by simp⟩

/-- `fixedBranch adv e b` equals
`m ← sampleMaterial leak; k' ←$ K; run adv e pk_m ct_m (if b then k_m else k')`. -/
theorem fixedBranch_eq_material
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (e : ℕ) (b : Bool) :
    fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b = (do
      let material ← sampleMaterial leak
      let randomKey ← ($ᵗ K : ProbComp K)
      run base onoff ecEk ecCt0 ecCt1 leak adv e material.keygen.1.1 material.ciphertext
        (if b then material.on.1.2 else randomKey)) :=
  (sampleMaterial_bind_challenge base onoff leak (fun pk ct key => do
    let randomKey ← ($ᵗ K : ProbComp K)
    run base onoff ecEk ecCt0 ecCt1 leak adv e pk ct (if b then key else randomKey))).symm

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Pinned

variable {K PK SK C : Type}

/-- Key generation pinned to `m`: the stored pair if `selected`, else `base.keygen`. -/
def keygen {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool) : ProbComp (PK × SK) :=
  if selected then pure m.keygen.1 else base.keygen

/-- Offline encapsulation pinned to `m`: the stored output if `selected`, else
`onoff.encapsOff`. -/
def encapsOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool) :
    ProbComp (onoff.St × onoff.C₀) :=
  if selected then pure m.off.1 else onoff.encapsOff

/-- Online encapsulation pinned to `m`: the stored output if `selected`, else
`onoff.encapsOn st pk`. -/
def encapsOn {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool)
    (st : onoff.St) (pk : PK) : ProbComp (onoff.C₁ × K) :=
  if selected then pure m.on.1 else onoff.encapsOn st pk

/-- KEM whose flagged phases return the stored outputs of `m`; decapsulation returns `key`. -/
abbrev kem {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    KEMScheme ProbComp K PK SK C where
  keygen := keygen m pinKeygen
  encaps pk := do
    let (st, ct0) ← encapsOff m pinOffline
    let (ct1, k) ← encapsOn m pinOnline st pk
    pure (onoff.split.symm (ct0, ct1), k)
  decaps _ _ := pure key

/-- Deterministic-decapsulation witness for `Pinned.kem`. -/
abbrev deterministic {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (kem m pinKeygen pinOffline pinOnline key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- On/off structure of `Pinned.kem`. -/
abbrev onOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (kem m pinKeygen pinOffline pinOnline key).OnOffStructure where
  St := onoff.St
  C₀ := onoff.C₀
  C₁ := onoff.C₁
  split := onoff.split
  encapsOff := encapsOff m pinOffline
  encapsOn := encapsOn m pinOnline
  factor _ := rfl

/-- Leakage witness for `Pinned.kem`: flagged phases return the stored outputs and coins. -/
abbrev leakage {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (kem m pinKeygen pinOffline pinOnline key).OnOffRandLeak
      (onOff m pinKeygen pinOffline pinOnline key) where
  KeygenRand := leak.KeygenRand
  OffRand := leak.OffRand
  OnRand := leak.OnRand
  keygenRleak := if pinKeygen then pure m.keygen else leak.keygenRleak
  encapsOffRleak := if pinOffline then pure m.off else leak.encapsOffRleak
  encapsOnRleak st pk := if pinOnline then pure m.on else leak.encapsOnRleak st pk
  keygen_fst := by cases pinKeygen <;> simp [keygen, leak.keygen_fst]
  encapsOff_fst := by cases pinOffline <;> simp [encapsOff, leak.encapsOff_fst]
  encapsOn_fst st pk := by cases pinOnline <;> simp [encapsOn, leak.encapsOn_fst]

end oppUniKemCKA.Security.Embedding.Pinned
