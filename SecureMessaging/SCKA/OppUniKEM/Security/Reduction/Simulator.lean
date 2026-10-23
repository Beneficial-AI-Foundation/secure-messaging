/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

/-!
# The IND-CPA reduction and its fixed-epoch branches

**Setting.** Let `base` be a KEM, `adv` an SCKA adversary against Opp-UniKEM making at most `q`
send queries, `e` a challenge epoch, and `(pkStar, ctStar, kStar)` an IND-CPA challenge tuple for
`base`.

**Definitions.**

- `SimState`: the simulator's game state. When the reduction embeds `pkStar` and `ctStar` at epoch
  `e`, it does not know the corresponding secret key, offline encapsulation state, shared key, or
  random coins; `SimState` wraps those secret types in `Option` (`none` for a *hidden* challenge
  secret, `some x` for a *known* secret sampled at epochs other than `e`).

- `oracle … e pkStar ctStar kStar`: the simulated SCKA oracles on `SimState`:
  - *Sampling:* key generation at A's epoch `e` returns `pkStar` and encapsulation at B's epoch `e`
    returns `ctStar`, with hidden secret key, offline state, shared key, and coins; other epochs
    sample honestly.
  - *Receive:* upon completing an online ciphertext, A outputs B's recorded key for that epoch.
  - *Challenge (`challenge`):* an eligible challenge at epoch `t` returns a uniform key if
    `0 < t < e`, `kStar` if `t = e`, and the recorded key if `t > e`.
  - *Corruption and coin leakage:* a permitted corruption or leaking send that would reveal a
    hidden value halts the simulation.

- `run … adv e pkStar ctStar kStar`: runs `adv` against `oracle … e pkStar ctStar kStar` from the
  initial state `initial` and returns `false` if the simulation halts.

- `securityReduction … adv q`: the IND-CPA adversary against `base` constructed from `adv`. In the
  pre-challenge phase it draws `e ← epochChoice q` uniformly from `{1, …, q}` (or `1` when `q = 0`);
  in the post-challenge phase on `(ctStar, kStar)` it returns `run … adv e pkStar ctStar kStar`.

- `fixedBranch … adv e b`: the reduction with challenge epoch fixed to `e` and IND-CPA bit fixed to
  `b`: samples `(pk, _) ← base.keygen`, `(ct, k) ← base.encaps pk`, and `k' ←$ K`, then returns
  `run … adv e pk ct (if b then k else k')`.

- `Material leak` (`sampleMaterial leak`): the *complete material* of one epoch, bundling the
  outputs and coins of key generation, offline encapsulation, and online encapsulation.

- `Pinned.kem m pinKeygen pinOffline pinOnline key`: a KEM instance in which each phase whose
  boolean flag is `true` returns the pre-sampled output stored in `m`, and decapsulation returns
  `key`.

**Main results.**

- `securityReduction_signed_gap_average`: for `q ≠ 0`, the difference in acceptance probability
  between the real (`true`) and random (`false`) IND-CPA branches of `securityReduction … adv q`
  equals the average over `e ∈ {1, …, q}` of the corresponding differences for
  `fixedBranch … adv e`.

- `fixedBranch_eq_material`: `fixedBranch … adv e b` coincides with drawing
  `m ← sampleMaterial leak` and `k' ←$ K` and running `adv` on the public key, reassembled
  ciphertext, and key `(if b then m.on.1.2 else k')` extracted from `m`.
-/

/-! ## The simulator -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C : Type}

/-- Simulated key generation: returns `(pkStar, none)` (with a hidden secret key) when `selected`
is `true`, and runs `kem.keygen` with a known secret key otherwise. -/
def keygen (kem : KEMScheme ProbComp K PK SK C) (selected : Bool) (pkStar : PK) :
    ProbComp (PK × Option SK) :=
  if selected then pure (pkStar, none) else Prod.map id some <$> kem.keygen

/-- Simulated offline encapsulation: returns the offline component of `ctStar` paired with a hidden
offline state (`none`) when `selected` is `true`, and runs `onoff.encapsOff` with a known state
otherwise. -/
def encapsOff {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (selected : Bool) (ctStar : C) : ProbComp (Option onoff.St × onoff.C₀) :=
  if selected then pure (none, (onoff.split ctStar).1)
  else Prod.map some id <$> onoff.encapsOff

/-- Simulated online encapsulation: returns the online component of `ctStar` paired with a hidden
shared key (`none`) when the offline state is hidden (`none`), and runs `onoff.encapsOn st pk` with
a known shared key when `st = some st`. -/
def encapsOn {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (ctStar : C) (st : Option onoff.St) (pk : PK) : ProbComp (onoff.C₁ × Option K) :=
  match st with
  | none => pure ((onoff.split ctStar).2, none)
  | some st => Prod.map id some <$> onoff.encapsOn st pk

/-- Simulated KEM for a single oracle query, constructed from `keygen`, `encapsOff`, and `encapsOn`
under the selection flags `selectedA` and `selectedB`; decapsulation constantly returns `key`
(party B's recorded key for party A's current epoch). -/
abbrev kem (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    KEMScheme ProbComp (Option K) PK (Option SK) C where
  keygen := keygen base selectedA pkStar
  encaps pk := do
    let (st, ct0) ← encapsOff onoff selectedB ctStar
    let (ct1, key) ← encapsOn onoff ctStar st pk
    pure (onoff.split.symm (ct0, ct1), key)
  decaps _ _ := pure key

/-- Deterministic-decapsulation witness for the simulated KEM `kem`. -/
abbrev deterministic (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (kem base onoff selectedA selectedB pkStar ctStar key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- On/off structure for the simulated KEM `kem`, with `Option onoff.St` as the offline state
space. -/
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

/-- Randomness-leaking counterpart of `keygen`, in which the key-generation coins are hidden
(`none`) whenever `selected` is `true`. -/
def keygenLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (selected : Bool) (pkStar : PK) :
    ProbComp ((PK × Option SK) × Option leak.KeygenRand) :=
  if selected then pure ((pkStar, none), none)
  else (fun z => ((z.1.1, some z.1.2), some z.2)) <$> leak.keygenRleak

/-- Randomness-leaking counterpart of `encapsOff`, in which the offline encapsulation coins are
hidden (`none`) whenever `selected` is `true`. -/
def offLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (selected : Bool) (ctStar : C) :
    ProbComp ((Option onoff.St × onoff.C₀) × Option leak.OffRand) :=
  if selected then pure ((none, (onoff.split ctStar).1), none)
  else (fun z => ((some z.1.1, z.1.2), some z.2)) <$> leak.encapsOffRleak

/-- Randomness-leaking counterpart of `encapsOn`, in which the online encapsulation coins are
hidden (`none`) whenever the offline state is hidden (`none`). -/
def onLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (ctStar : C) (st : Option onoff.St) (pk : PK) :
    ProbComp ((onoff.C₁ × Option K) × Option leak.OnRand) :=
  match st with
  | none => pure (((onoff.split ctStar).2, none), none)
  | some st => (fun z => ((z.1.1, some z.1.2), some z.2)) <$> leak.encapsOnRleak st pk

/-- On/off randomness-leakage witness for the simulated KEM `kem`, defined from `keygenLeak`,
`offLeak`, and `onLeak`. -/
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

/-- Simulator game state: an SCKA `GameState` in which party A's secret key (`Option SK`), party B's
offline encapsulation state (`Option onoff.St`), and the recorded keys (`Option K`) may be hidden
(`none`). -/
abbrev SimState {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (Sym : Type) :=
  SCKAScheme.GameState (StateA (Option SK) PK onoff.C₀ Sym)
    (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) (Option K) (Message Sym)

/-- Reveal an optional field, failing (`none`) only when it is present and hidden (`some none`). -/
def revealField {α : Type} : Option (Option α) → Option (Option α)
  | none => some none
  | some none => none
  | some (some a) => some (some a)

/-- Reveal party A's state, failing if A's decapsulation key is hidden. -/
def revealA {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (s : StateA (Option SK) PK onoff.C₀ Sym) : Option (StA onoff Sym) := do
  let dk ← revealField s.dkA
  pure { dkA := dk, ekA := s.ekA, ct0 := s.ct0, t := s.t,
         ich := s.ich, lch := s.lch, ack := s.ack }

/-- Reveal party B's state, failing if B's offline state is hidden. -/
def revealB {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (s : StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) : Option (StB onoff Sym) := do
  let st ← revealField s.stCt
  pure { ekA := s.ekA, ct0 := s.ct0, ct1 := s.ct1, stCt := st, t := s.t,
         ich := s.ich, lch := s.lch, ack := s.ack }

/-- Reveal the coins of a leaking send, failing if any coin is hidden. -/
def revealCoins {KG OFF ON : Type} :
    SendRand (Option KG) (Option OFF) (Option ON) → Option (SendRand KG OFF ON)
  | .none => some .none
  | .keygen r => .keygen <$> r
  | .off r => .off <$> r
  | .on r => .on <$> r
  | .offOn r₀ r₁ => do pure (.offOn (← r₀) (← r₁))

/-- Run the guarded oracle `op`, passing a rejection (`none`) to the adversary and revealing an
accepted response `a` as `reveal a`; a failed revelation (`reveal a = none`) stops the simulation.
-/
def revealAfter {σ α β : Type} (reveal : α → Option β) (op : StateT σ ProbComp (Option α)) :
    OptionT (StateT σ ProbComp) (Option β) :=
  OptionT.mk (do
    match ← op with
    | none => pure (some none)
    | some a => pure (some <$> reveal a))

/-- Unfolding `revealAfter` on state `s`. -/
theorem revealAfter_run {σ α β : Type} (reveal : α → Option β)
    (op : StateT σ ProbComp (Option α)) (s : σ) :
    ((revealAfter reveal op).run).run s =
      (do
        let (a, s') ← op.run s
        pure (match a with | none => some none | some a => some <$> reveal a, s')) := by
  simp only [revealAfter, OptionT.run_mk, StateT.run_bind]
  congr 1
  funext z
  rcases z with ⟨_ | a, s'⟩ <;> rfl

/-- Challenge oracle on game states with key-table entries `κ`, read as keys via `toKey : κ → K`:
- rejects (`none`) if `t` is exposed, already challenged, or absent from both `s.keyA` and `s.keyB`
  (`s.keyA` is consulted first);
- otherwise inserts `t` into `s.challenged` and returns a uniform key if `0 < t < e`, `kStar` if
  `t = e`, and `toKey honest` otherwise. -/
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

/-- Simulator challenge oracle on `SimState`: instantiates `challengeWith` with a hidden recorded
key (`none`) read as `kStar`. -/
def challenge [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) : QueryImpl (ℕ →ₒ Option K) (StateT (SimState onoff Sym) ProbComp) :=
  challengeWith (fun key : Option K => key.getD kStar) e kStar

/-- Simulated security oracles for challenge epoch `e` and IND-CPA challenge
`(pkStar, ctStar, kStar)`. A query from state `s` runs Opp-UniKEM over the simulated KEM `kem`,
selecting A if `s.stA.t = e` and B if `s.stB.t = e`, with decapsulation output `s.keyB s.stA.t`.
Challenges use `challenge onoff e kStar`; corruptions and leaking sends reveal their answers with
`revealAfter` after their exposure guards. -/
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
      revealAfter (fun (out : ℕ × Option ℕ × Message Sym ×
          SendRand (Option leak.KeygenRand) (Option leak.OffRand) (Option leak.OnRand)) => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins))
        (SCKAScheme.oracleSendArleak vulnRleakA scka u)
    | .inl (.inl (.inl (.inr u))) =>
      revealAfter (fun (out : ℕ × Option ℕ × Message Sym ×
          SendRand (Option leak.KeygenRand) (Option leak.OffRand) (Option leak.OnRand)) => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins))
        (SCKAScheme.oracleSendBrleak vulnRleakB scka u)
    | .inl (.inl (.inr t)) => liftM (challenge (Sym := Sym) onoff e kStar t)
    | .inl (.inr u) =>
      revealAfter (revealA (onoff := onoff) (Sym := Sym))
        (SCKAScheme.oracleCorruptA (vulnCorrA (Sym := Sym) simKem simOnOff)
          (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) (Option K) (Message Sym) u)
    | .inr u =>
      revealAfter (revealB (onoff := onoff) (Sym := Sym))
        (SCKAScheme.oracleCorruptB (vulnCorrB (Sym := Sym) simKem simOnOff)
          (StateA (Option SK) PK onoff.C₀ Sym) (Option K) (Message Sym) u)

/-- Initial simulator state: both parties start at epoch `1` with all optional local fields set to
`none` and empty message, key, exposure, and challenge tables. -/
def initial {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure) :
    SimState onoff Sym :=
  SCKAScheme.initGameState
    { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
      ack := { ekRec := false, ctRec := false } }
    { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0, lch := ∅,
      ack := { ekRec := false, ctRec := false } }

/-- Simulated execution of `adv` for challenge epoch `e` and IND-CPA challenge
`(pkStar, ctStar, kStar)`: runs `adv` against `oracle … e pkStar ctStar kStar` from `initial onoff`
and returns `false` if the simulation halts (`none`). -/
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

/-- Challenge epoch sampler: draws an epoch uniformly from `{1, …, q}` when `q > 0`, and returns
`1` when `q = 0`. -/
def epochChoice (q : ℕ) : ProbComp ℕ :=
  if hq : q = 0 then pure 1
  else
    letI : NeZero q := ⟨hq⟩
    (fun i : Fin q => i.val + 1) <$> ($ᵗ (Fin q) : ProbComp (Fin q))

/-- The IND-CPA adversary against `base` constructed from an SCKA adversary `adv` and send budget
`q`: in the pre-challenge phase it draws a challenge epoch `e ← epochChoice q` and stores `(pk, e)`;
in the post-challenge phase on `(ct, key)` it runs `run … adv e pk ct key`. -/
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

/-- Fixed-epoch branch of the reduction at challenge epoch `e` and IND-CPA challenge bit `b`:
samples `(pk, _) ← base.keygen`, `(ct, key) ← base.encaps pk`, and an independent uniform key
`randomKey ←$ K`, then executes `run … adv e pk ct (if b then key else randomKey)`. -/
def fixedBranch (adv : SecurityAdversary leak Sym) (e : ℕ) (b : Bool) : ProbComp Bool := do
  let (pk, _) ← base.keygen
  let (ct, key) ← base.encaps pk
  let randomKey ← ($ᵗ K : ProbComp K)
  run base onoff ecEk ecCt0 ecCt1 leak adv e pk ct (if b then key else randomKey)

/-- Running `securityReduction … adv q` in the IND-CPA experiment with challenge bit `b` yields any
boolean outcome `output` with the same probability as drawing `e ← epochChoice q` and running
`fixedBranch … adv e b`. -/
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

/-- For `q ≠ 0`, the acceptance probability of `securityReduction … adv q` in the IND-CPA
experiment with bit `b` equals the average of `Pr[= true | fixedBranch … adv e b]` over
`e ∈ {1, …, q}`. -/
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

/-- For `q ≠ 0`, the difference in acceptance probability between the real (`true`) and random
(`false`) IND-CPA branches of `securityReduction … adv q` equals the average over `e ∈ {1, …, q}`
of the corresponding differences for `fixedBranch … adv e`. -/
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

/-- Complete cryptographic material of a single epoch, bundling the outputs and random coins of the
three sampling phases: key generation, offline encapsulation, and online encapsulation. -/
structure Material {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) where
  /-- Key-generation output `(pk, sk)` paired with its random coins. -/
  keygen : (PK × SK) × leak.KeygenRand
  /-- Offline encapsulation output `(st, ct0)` paired with its random coins. -/
  off : (onoff.St × onoff.C₀) × leak.OffRand
  /-- Online encapsulation output `(ct1, k)` paired with its random coins. -/
  on : (onoff.C₁ × K) × leak.OnRand

/-- Sampler for a complete epoch material `Material leak`, executing `leak.keygenRleak`,
`leak.encapsOffRleak`, and `leak.encapsOnRleak` at the sampled offline state and public key. -/
def sampleMaterial {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) : ProbComp (Material leak) := do
  let kg ← leak.keygenRleak
  let off ← leak.encapsOffRleak
  let on ← leak.encapsOnRleak off.1.1 kg.1.1
  pure ⟨kg, off, on⟩

/-- Full KEM ciphertext reassembled from the offline and online ciphertext components of `m`. -/
def Material.ciphertext {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) : C :=
  onoff.split.symm (m.off.1.2, m.on.1.1)

/-- Sampling `m ← sampleMaterial leak` and passing `(m.keygen.1.1, m.ciphertext, m.on.1.2)` to a
continuation `f` coincides with sampling `(pk, _) ← base.keygen` and `(ct, key) ← base.encaps pk`
and passing `(pk, ct, key)` to `f`. -/
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

/-- Every `m` in the support of `sampleMaterial leak` has components in the supports of
`leak.keygenRleak`, `leak.encapsOffRleak`, and `leak.encapsOnRleak m.off.1.1 m.keygen.1.1`,
respectively. -/
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

/-- Every `m` in the support of `sampleMaterial leak` has non-coin outputs in the supports of
`base.keygen`, `onoff.encapsOff`, and `onoff.encapsOn m.off.1.1 m.keygen.1.1`, respectively. -/
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

/-- `fixedBranch … adv e b` coincides with drawing `m ← sampleMaterial leak` and `randomKey ←$ K`
and executing `run … adv e m.keygen.1.1 m.ciphertext (if b then m.on.1.2 else randomKey)`. -/
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

/-- Key generation with optional pinning to `m`: returns the pre-sampled pair `m.keygen.1` when
`selected` is `true`, and runs `base.keygen` otherwise. -/
def keygen {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool) : ProbComp (PK × SK) :=
  if selected then pure m.keygen.1 else base.keygen

/-- Offline encapsulation with optional pinning to `m`: returns the pre-sampled pair `m.off.1` when
`selected` is `true`, and runs `onoff.encapsOff` otherwise. -/
def encapsOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool) :
    ProbComp (onoff.St × onoff.C₀) :=
  if selected then pure m.off.1 else onoff.encapsOff

/-- Online encapsulation with optional pinning to `m`: returns the pre-sampled pair `m.on.1` when
`selected` is `true`, and runs `onoff.encapsOn st pk` otherwise. -/
def encapsOn {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool)
    (st : onoff.St) (pk : PK) : ProbComp (onoff.C₁ × K) :=
  if selected then pure m.on.1 else onoff.encapsOn st pk

/-- KEM instance in which each sampling phase whose boolean flag (`pinKeygen`, `pinOffline`,
`pinOnline`) is `true` returns the corresponding output stored in `m`, and decapsulation constantly
returns `key`. -/
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

/-- On/off structure for `Pinned.kem`. -/
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

/-- On/off randomness-leakage witness for `Pinned.kem`, in which each pinned phase returns both the
output and the random coins stored in `m`. -/
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
