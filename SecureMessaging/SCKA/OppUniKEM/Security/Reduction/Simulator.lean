/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

/-!
# The IND-CPA reduction and its fixed-epoch branches

**Setting.** Throughout this module, we consider:

- a KEM `kem` and an SCKA adversary `adv` against Opp-UniKEM over `kem` making at most `q`
  send queries;
- a challenge epoch `e`;
- an IND-CPA challenge tuple `(pkStar, ctStar, kStar)` for `kem`, that is, a public key, a
  ciphertext, and a candidate key.

**Main results.** The IND-CPA adversary `securityReduction … adv q` draws a challenge epoch `e`
uniformly from `{1, …, q}` and runs `adv` against simulated oracles that embed `pkStar` and
`ctStar` at `e`, keeping the corresponding secrets and coins *hidden* (`SimState`, `simOracle`,
`run`); its *fixed branch* fixes `e` and the IND-CPA bit `b` (`fixedBranch … adv e b`). The *KEM
material* of an epoch records its sampling outputs and coins (`KEMMaterial leak`, `sampleMaterial`),
which the *pinned KEM* returns in its flagged phases (`Pinned.kem kemMat …`).

- For `q ≠ 0`, the real-minus-random gap of `securityReduction … adv q` is the average over
  `e ∈ {1, …, q}` of the gaps of `fixedBranch … adv e` (`securityReduction_signed_gap_average`).
- `fixedBranch … adv e b` coincides with drawing `kemMat ← sampleMaterial leak` and `k' ←$ K` and
  running `adv` on the public key, ciphertext, and key `(if b then kemMat.key else k')` of `kemMat`
  (`fixedBranch_eq_material`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

section

variable (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
  (hDet : kem.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : kem.OnOffRandLeak onoff)

/-! ## The simulator -/

/-- Simulated key generation: returns `(pkStar, none)` (with a hidden secret key) when `selected`
is `true`, and runs `kem.keygen` with a known secret key otherwise. -/
def keygen (kem : KEMScheme ProbComp K PK SK C) (selected : Bool) (pkStar : PK) :
    ProbComp (PK × Option SK) :=
  if selected then pure (pkStar, none) else Prod.map id some <$> kem.keygen

variable {kem} in
/-- Simulated offline encapsulation: returns the offline component of `ctStar` paired with a hidden
offline state (`none`) when `selected` is `true`, and runs `onoff.encapsOff` with a known state
otherwise. -/
def encapsOff
    (selected : Bool) (ctStar : C) : ProbComp (Option onoff.St × onoff.C₀) :=
  if selected then pure (none, (onoff.split ctStar).1)
  else Prod.map some id <$> onoff.encapsOff

variable {kem} in
/-- Simulated online encapsulation: returns the online component of `ctStar` paired with a hidden
shared key (`none`) when the offline state is hidden (`none`), and runs `onoff.encapsOn st pk` with
a known shared key when `st = some st`. -/
def encapsOn
    (ctStar : C) (st : Option onoff.St) (pk : PK) : ProbComp (onoff.C₁ × Option K) :=
  match st with
  | none => pure ((onoff.split ctStar).2, none)
  | some st => Prod.map id some <$> onoff.encapsOn st pk

/-- Simulated KEM for a single oracle query, constructed from `keygen`, `encapsOff`, and `encapsOn`
under the selection flags `selectedA` and `selectedB`; decapsulation constantly returns `key`
(party B's recorded key for party A's current epoch). -/
abbrev simKem
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    KEMScheme ProbComp (Option K) PK (Option SK) C where
  keygen := keygen kem selectedA pkStar
  encaps pk := do
    let (st, ct0) ← encapsOff onoff selectedB ctStar
    let (ct1, key) ← encapsOn onoff ctStar st pk
    pure (onoff.split.symm (ct0, ct1), key)
  decaps _ _ := pure key

/-- Deterministic-decapsulation witness for the simulated KEM `simKem`. -/
abbrev simDet
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (simKem kem onoff selectedA selectedB pkStar ctStar key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- On/off structure for the simulated KEM `simKem`, with `Option onoff.St` as the offline state
space. -/
abbrev simOnOff
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (simKem kem onoff selectedA selectedB pkStar ctStar key).OnOffStructure where
  St := Option onoff.St
  C₀ := onoff.C₀
  C₁ := onoff.C₁
  split := onoff.split
  encapsOff := encapsOff onoff selectedB ctStar
  encapsOn := encapsOn onoff ctStar
  factor _ := rfl

variable {kem onoff} in
/-- Randomness-leaking counterpart of `keygen`, in which the key-generation coins are hidden
(`none`) whenever `selected` is `true`. -/
def keygenLeak (selected : Bool) (pkStar : PK) :
    ProbComp ((PK × Option SK) × Option leak.KeygenRand) :=
  if selected then pure ((pkStar, none), none)
  else (fun res => ((res.1.1, some res.1.2), some res.2)) <$> leak.keygenRleak

variable {kem onoff} in
/-- Randomness-leaking counterpart of `encapsOff`, in which the offline encapsulation coins are
hidden (`none`) whenever `selected` is `true`. -/
def offLeak (selected : Bool) (ctStar : C) :
    ProbComp ((Option onoff.St × onoff.C₀) × Option leak.OffRand) :=
  if selected then pure ((none, (onoff.split ctStar).1), none)
  else (fun res => ((some res.1.1, res.1.2), some res.2)) <$> leak.encapsOffRleak

variable {kem onoff} in
/-- Randomness-leaking counterpart of `encapsOn`, in which the online encapsulation coins are
hidden (`none`) whenever the offline state is hidden (`none`). -/
def onLeak (ctStar : C) (st : Option onoff.St) (pk : PK) :
    ProbComp ((onoff.C₁ × Option K) × Option leak.OnRand) :=
  match st with
  | none => pure (((onoff.split ctStar).2, none), none)
  | some st => (fun res => ((res.1.1, some res.1.2), some res.2)) <$> leak.encapsOnRleak st pk

/-- On/off randomness-leakage witness for the simulated KEM `simKem`, defined from `keygenLeak`,
`offLeak`, and `onLeak`. -/
abbrev simLeak
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (simKem kem onoff selectedA selectedB pkStar ctStar key).OnOffRandLeak
      (simOnOff kem onoff selectedA selectedB pkStar ctStar key) where
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

variable {kem} in
/-- Simulator game state: an SCKA `GameState` in which party A's secret key (`Option SK`), party B's
offline encapsulation state (`Option onoff.St`), and the recorded keys (`Option K`) may be hidden
(`none`). -/
abbrev SimState
    (Sym : Type) :=
  SCKAScheme.GameState (StateA (Option SK) PK onoff.C₀ Sym)
    (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) (Option K) (Message Sym)

/-- Reveal an optional field, failing (`none`) only when it is present and hidden (`some none`). -/
def revealField {α : Type} : Option (Option α) → Option (Option α)
  | none => some none
  | some none => none
  | some (some a) => some (some a)

variable {kem onoff} in
/-- Reveal party A's state, failing if A's decapsulation key is hidden. -/
def revealA
    (stA : StateA (Option SK) PK onoff.C₀ Sym) : Option (StA onoff Sym) := do
  let dk ← revealField stA.dkA
  pure { dkA := dk, ekA := stA.ekA, ct0 := stA.ct0, t := stA.t,
         ich := stA.ich, lch := stA.lch, ack := stA.ack }

variable {kem onoff} in
/-- Reveal party B's state, failing if B's offline state is hidden. -/
def revealB
    (stB : StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) : Option (StB onoff Sym) := do
  let st ← revealField stB.stCt
  pure { ekA := stB.ekA, ct0 := stB.ct0, ct1 := stB.ct1, stCt := st, t := stB.t,
         ich := stB.ich, lch := stB.lch, ack := stB.ack }

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
  funext res
  rcases res with ⟨_ | a, s'⟩ <;> rfl

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

variable {kem} in
/-- Simulator challenge oracle on `SimState`: instantiates `challengeWith` with a hidden recorded
key (`none`) read as `kStar`. -/
def challenge [SampleableType K]
    (e : ℕ) (kStar : K) : QueryImpl (ℕ →ₒ Option K) (StateT (SimState onoff Sym) ProbComp) :=
  challengeWith (fun key : Option K => key.getD kStar) e kStar

/-- Simulated security oracles for challenge epoch `e` and IND-CPA challenge
`(pkStar, ctStar, kStar)`. A query from state `s` runs Opp-UniKEM over the simulated KEM `simKem`,
selecting A if `s.stA.t = e` and B if `s.stB.t = e`, with decapsulation output `s.keyB s.stA.t`.
Challenges use `challenge onoff e kStar`; corruptions and leaking sends reveal their answers with
`revealAfter` after their exposure guards. -/
def simOracle [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (e : ℕ) (pkStar : PK) (ctStar : C) (kStar : K) :
    QueryImpl (securitySpec leak Sym) (OptionT (StateT (SimState onoff Sym) ProbComp)) :=
  fun t => (get : OptionT (StateT (SimState onoff Sym) ProbComp) (SimState onoff Sym)) >>= fun s =>
    let selectedA := decide (s.stA.t = e)
    let selectedB := decide (s.stB.t = e)
    let key := s.keyB s.stA.t
    let simKem := simKem kem onoff selectedA selectedB pkStar ctStar key
    let simOnOff := simOnOff kem onoff selectedA selectedB pkStar ctStar key
    let simLeak := simLeak kem onoff leak selectedA selectedB pkStar ctStar key
    let scka := scheme simKem simOnOff
      (simDet kem onoff selectedA selectedB pkStar ctStar key) ecEk ecCt0 ecCt1 simLeak
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

variable {kem} in
/-- Initial simulator state: both parties start at epoch `1` with all optional local fields set to
`none` and empty message, key, exposure, and challenge tables. -/
def initial :
    SimState onoff Sym :=
  SCKAScheme.initGameState
    { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
      ack := { ekRec := false, ctRec := false } }
    { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0, lch := ∅,
      ack := { ekRec := false, ctRec := false } }

/-- Simulated execution of `adv` for challenge epoch `e` and IND-CPA challenge
`(pkStar, ctStar, kStar)`: runs `adv` against `simOracle … e pkStar ctStar kStar` from
`initial onoff` and returns `false` if the simulation halts (`none`). -/
def run [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (adv : SecurityAdversary leak Sym) (e : ℕ) (pkStar : PK) (ctStar : C) (kStar : K) :
    ProbComp Bool := do
  let result ← ((simulateQ (simOracle kem onoff ecEk ecCt0 ecCt1 leak e pkStar ctStar kStar)
    adv).run).run' (initial onoff)
  pure (result.getD false)

/-- Challenge epoch sampler: draws an epoch uniformly from `{1, …, q}` when `q > 0`, and returns
`1` when `q = 0`. -/
def epochChoice (q : ℕ) : ProbComp ℕ :=
  if hq : q = 0 then pure 1
  else
    letI : NeZero q := ⟨hq⟩
    (fun i : Fin q => i.val + 1) <$> ($ᵗ (Fin q) : ProbComp (Fin q))

/-- The IND-CPA adversary against `kem` constructed from an SCKA adversary `adv` and send budget
`q`: in the pre-challenge phase it draws a challenge epoch `e ← epochChoice q` and stores `(pk, e)`;
in the post-challenge phase on `(ct, key)` it runs `run … adv e pk ct key`. -/
-- ANCHOR: securityReduction
def securityReduction [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) : kem.IND_CPA_Adversary where
  State := PK × ℕ
  preChallenge pk := do pure (pk, ← epochChoice q)
  postChallenge state ct key := run kem onoff ecEk ecCt0 ecCt1 leak adv state.2 state.1 ct key
-- ANCHOR_END: securityReduction

open ToVCVio ENNReal

/-! ## Fixed branches and stored epoch material -/

section

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Fixed-epoch branch of the reduction at challenge epoch `e` and IND-CPA challenge bit `b`:
samples `(pk, _) ← kem.keygen`, `(ct, key) ← kem.encaps pk`, and an independent uniform key
`randomKey ←$ K`, then executes `run … adv e pk ct (if b then key else randomKey)`. -/
def fixedBranch (adv : SecurityAdversary leak Sym) (e : ℕ) (b : Bool) : ProbComp Bool := do
  let (pk, _) ← kem.keygen
  let (ct, key) ← kem.encaps pk
  let randomKey ← ($ᵗ K : ProbComp K)
  run kem onoff ecEk ecCt0 ecCt1 leak adv e pk ct (if b then key else randomKey)

/-- Running `securityReduction … adv q` in the IND-CPA experiment with challenge bit `b` yields any
boolean outcome `output` with the same probability as drawing `e ← epochChoice q` and running
`fixedBranch … adv e b`. -/
theorem securityReduction_probOutput
    (adv : SecurityAdversary leak Sym) (q : ℕ) (b output : Bool) :
    Pr{let x ← (kem.IND_CPA_Experiment ProbCompRuntime.probComp
      (securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) b)}[x = output] =
    Pr{let x ← (do
      let e ← epochChoice q
      fixedBranch kem onoff ecEk ecCt0 ecCt1 leak adv e b)}[x = output] := by
  unfold KEMScheme.IND_CPA_Experiment
  simp only [securityReduction, fixedBranch, ProbCompRuntime.probComp,
    ProbCompRuntime.liftProbComp, ProbCompLift.id, bind_assoc, pure_bind]
  exact (OracleComp.EvalDistEq.bind_bind_swap kem.keygen (epochChoice q) _).prEvent_eq _

/-- For `q ≠ 0`, the acceptance probability of `securityReduction … adv q` in the IND-CPA
experiment with bit `b` equals the average of `Pr{let x ← fixedBranch … adv e b}[x = true]` over
`e ∈ {1, …, q}`. -/
theorem securityReduction_acceptance_average
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : q ≠ 0) (b : Bool) :
    (Pr{let x ← (kem.IND_CPA_Experiment ProbCompRuntime.probComp
      (securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) b)}[x = true]).toReal =
    (q : ℝ)⁻¹ * ∑ i : Fin q,
      (Pr{let x ← (fixedBranch
          kem onoff ecEk ecCt0 ecCt1 leak adv (i.val + 1) b)}[x = true]).toReal := by
  rw [securityReduction_probOutput]
  let : NeZero q := ⟨hq⟩
  simp only [epochChoice, hq, ↓reduceDIte, bind_map_left, (prEvent_bind_eq_sum_fintype _),
    SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin, ← Finset.mul_sum]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun _ _ => (prEvent_ne_top _))]

/-- For `q ≠ 0`, the difference in acceptance probability between the real (`true`) and random
(`false`) IND-CPA branches of `securityReduction … adv q` equals the average over `e ∈ {1, …, q}`
of the corresponding differences for `fixedBranch … adv e`. -/
theorem securityReduction_signed_gap_average
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : q ≠ 0) :
    (Pr{let x ← (kem.IND_CPA_Experiment ProbCompRuntime.probComp
      (securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) true)}[x = true]).toReal -
    (Pr{let x ← (kem.IND_CPA_Experiment ProbCompRuntime.probComp
      (securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) false)}[x = true]).toReal =
    (q : ℝ)⁻¹ * ∑ i : Fin q,
      ((Pr{let x ← (fixedBranch kem onoff ecEk ecCt0 ecCt1 leak adv
        (i.val + 1) true)}[x = true]).toReal -
       (Pr{let x ← (fixedBranch kem onoff ecEk ecCt0 ecCt1 leak adv
        (i.val + 1) false)}[x = true]).toReal) := by
  rw [securityReduction_acceptance_average kem onoff ecEk ecCt0 ecCt1 leak adv q hq true,
    securityReduction_acceptance_average kem onoff ecEk ecCt0 ecCt1 leak adv q hq false,
    Finset.sum_sub_distrib, mul_sub]

end

section

variable {kem onoff} in
/-- KEM material of a single epoch, bundling the outputs and random coins of the three KEM
sampling phases: key generation, offline encapsulation, and online encapsulation. -/
structure KEMMaterial where
  /-- Key-generation output `(pk, sk)` paired with its random coins. -/
  keygen : (PK × SK) × leak.KeygenRand
  /-- Offline encapsulation output `(st, ct0)` paired with its random coins. -/
  off : (onoff.St × onoff.C₀) × leak.OffRand
  /-- Online encapsulation output `(ct1, k)` paired with its random coins. -/
  on : (onoff.C₁ × K) × leak.OnRand

namespace KEMMaterial

variable {kem onoff}
  {leak : kem.OnOffRandLeak onoff} (kemMat : KEMMaterial leak)

/-- The public key of `kemMat`. -/
abbrev pk : PK := kemMat.keygen.1.1

/-- The secret key of `kemMat`. -/
abbrev sk : SK := kemMat.keygen.1.2

/-- The offline encapsulation state of `kemMat`. -/
abbrev st : onoff.St := kemMat.off.1.1

/-- The offline ciphertext component of `kemMat`. -/
abbrev ct0 : onoff.C₀ := kemMat.off.1.2

/-- The online ciphertext component of `kemMat`. -/
abbrev ct1 : onoff.C₁ := kemMat.on.1.1

/-- The encapsulated key of `kemMat`. -/
abbrev key : K := kemMat.on.1.2

end KEMMaterial

variable {kem onoff} in
/-- Sampler for the KEM material `KEMMaterial leak` of one epoch, executing `leak.keygenRleak`,
`leak.encapsOffRleak`, and `leak.encapsOnRleak` at the sampled offline state and public key. -/
def sampleMaterial : ProbComp (KEMMaterial leak) := do
  let kg ← leak.keygenRleak
  let off ← leak.encapsOffRleak
  let on ← leak.encapsOnRleak off.1.1 kg.1.1
  pure ⟨kg, off, on⟩

variable {kem onoff leak} in
/-- Full KEM ciphertext reassembled from the offline and online ciphertext components of
`kemMat`. -/
def KEMMaterial.ciphertext (kemMat : KEMMaterial leak) : C :=
  onoff.split.symm (kemMat.ct0, kemMat.ct1)

/-- Sampling `kemMat ← sampleMaterial leak` and passing `(kemMat.pk, kemMat.ciphertext, kemMat.key)`
to a continuation `f` coincides with sampling `(pk, _) ← kem.keygen` and
`(ct, key) ← kem.encaps pk` and passing `(pk, ct, key)` to `f`. -/
theorem sampleMaterial_bind_challenge {α : Type} (f : PK → C → K → ProbComp α) :
    (do
      let material ← sampleMaterial leak
      f material.pk material.ciphertext material.key) =
    (do
      let (pk, _) ← kem.keygen
      let (ct, key) ← kem.encaps pk
      f pk ct key) := by
  rw [← leak.keygen_fst]
  simp only [sampleMaterial, bind_assoc, pure_bind, KEMMaterial.ciphertext]
  apply bind_congr
  intro kg
  rw [onoff.factor, ← leak.encapsOff_fst]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro off
  rw [← leak.encapsOn_fst]
  simp only [bind_assoc, pure_bind]

variable {kem onoff} in
/-- Every `kemMat` in the support of `sampleMaterial leak` has components in the supports of
`leak.keygenRleak`, `leak.encapsOffRleak`, and `leak.encapsOnRleak kemMat.st kemMat.pk`,
respectively. -/
theorem sampleMaterial_support (kemMat : KEMMaterial leak)
    (hm : kemMat ∈ support (sampleMaterial leak)) :
    kemMat.keygen ∈ support leak.keygenRleak ∧
    kemMat.off ∈ support leak.encapsOffRleak ∧
    kemMat.on ∈ support (leak.encapsOnRleak kemMat.st kemMat.pk) := by
  simp only [sampleMaterial, mem_support_bind_iff, mem_support_pure_iff] at hm
  obtain ⟨kg, hkg, off, hoff, on, hon, rfl⟩ := hm
  exact ⟨hkg, hoff, hon⟩

variable {kem onoff} in
/-- Every `kemMat` in the support of `sampleMaterial leak` has non-coin outputs in the supports of
`kem.keygen`, `onoff.encapsOff`, and `onoff.encapsOn kemMat.st kemMat.pk`, respectively. -/
theorem sampleMaterial_ordinary_support (kemMat : KEMMaterial leak)
    (hm : kemMat ∈ support (sampleMaterial leak)) :
    kemMat.keygen.1 ∈ support kem.keygen ∧
    kemMat.off.1 ∈ support onoff.encapsOff ∧
    kemMat.on.1 ∈ support (onoff.encapsOn kemMat.st kemMat.pk) := by
  obtain ⟨hkg, hoff, hon⟩ := sampleMaterial_support leak kemMat hm
  refine ⟨?_, ?_, ?_⟩
  · rw [← leak.keygen_fst]
    exact (mem_support_bind_iff _ _ _).mpr ⟨_, hkg, by simp⟩
  · rw [← leak.encapsOff_fst]
    exact (mem_support_bind_iff _ _ _).mpr ⟨_, hoff, by simp⟩
  · rw [← leak.encapsOn_fst]
    exact (mem_support_bind_iff _ _ _).mpr ⟨_, hon, by simp⟩

/-- `fixedBranch … adv e b` coincides with drawing `kemMat ← sampleMaterial leak` and
`randomKey ←$ K` and executing
`run … adv e kemMat.pk kemMat.ciphertext (if b then kemMat.key else randomKey)`. -/
theorem fixedBranch_eq_material
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (adv : SecurityAdversary leak Sym) (e : ℕ) (b : Bool) :
    fixedBranch kem onoff ecEk ecCt0 ecCt1 leak adv e b = (do
      let material ← sampleMaterial leak
      let randomKey ← ($ᵗ K : ProbComp K)
      run kem onoff ecEk ecCt0 ecCt1 leak adv e material.pk material.ciphertext
        (if b then material.key else randomKey)) :=
  (sampleMaterial_bind_challenge kem onoff leak (fun pk ct key => do
    let randomKey ← ($ᵗ K : ProbComp K)
    run kem onoff ecEk ecCt0 ecCt1 leak adv e pk ct (if b then key else randomKey))).symm

end

end

namespace Pinned

/-- Key generation with optional pinning to `kemMat`: returns the pre-sampled pair `kemMat.keygen.1`
when `selected` is `true`, and runs `kem.keygen` otherwise. -/
def keygen {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    {leak : kem.OnOffRandLeak onoff} (kemMat : KEMMaterial leak) (selected : Bool) :
    ProbComp (PK × SK) :=
  if selected then pure kemMat.keygen.1 else kem.keygen

/-- Offline encapsulation with optional pinning to `kemMat`: returns the pre-sampled pair
`kemMat.off.1` when `selected` is `true`, and runs `onoff.encapsOff` otherwise. -/
def encapsOff {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    {leak : kem.OnOffRandLeak onoff} (kemMat : KEMMaterial leak) (selected : Bool) :
    ProbComp (onoff.St × onoff.C₀) :=
  if selected then pure kemMat.off.1 else onoff.encapsOff

/-- Online encapsulation with optional pinning to `kemMat`: returns the pre-sampled pair
`kemMat.on.1` when `selected` is `true`, and runs `onoff.encapsOn st pk` otherwise. -/
def encapsOn {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    {leak : kem.OnOffRandLeak onoff} (kemMat : KEMMaterial leak) (selected : Bool)
    (st : onoff.St) (pk : PK) : ProbComp (onoff.C₁ × K) :=
  if selected then pure kemMat.on.1 else onoff.encapsOn st pk

/-- KEM instance in which each sampling phase whose boolean flag (`pinKeygen`, `pinOffline`,
`pinOnline`) is `true` returns the corresponding output stored in `kemMat`, and decapsulation
constantly returns `key`. -/
abbrev kem {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    {leak : kem.OnOffRandLeak onoff} (kemMat : KEMMaterial leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    KEMScheme ProbComp K PK SK C where
  keygen := keygen kemMat pinKeygen
  encaps pk := do
    let (st, ct0) ← encapsOff kemMat pinOffline
    let (ct1, k) ← encapsOn kemMat pinOnline st pk
    pure (onoff.split.symm (ct0, ct1), k)
  decaps _ _ := pure key

/-- Deterministic-decapsulation witness for `Pinned.kem`. -/
abbrev deterministic {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    {leak : kem.OnOffRandLeak onoff} (kemMat : KEMMaterial leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (Pinned.kem kemMat pinKeygen pinOffline pinOnline key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- On/off structure for `Pinned.kem`. -/
abbrev onOff {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    {leak : kem.OnOffRandLeak onoff} (kemMat : KEMMaterial leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (Pinned.kem kemMat pinKeygen pinOffline pinOnline key).OnOffStructure where
  St := onoff.St
  C₀ := onoff.C₀
  C₁ := onoff.C₁
  split := onoff.split
  encapsOff := encapsOff kemMat pinOffline
  encapsOn := encapsOn kemMat pinOnline
  factor _ := rfl

/-- On/off randomness-leakage witness for `Pinned.kem`, in which each pinned phase returns both the
output and the random coins stored in `kemMat`. -/
abbrev leakage {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (leak : kem.OnOffRandLeak onoff) (kemMat : KEMMaterial leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (Pinned.kem kemMat pinKeygen pinOffline pinOnline key).OnOffRandLeak
      (onOff kemMat pinKeygen pinOffline pinOnline key) where
  KeygenRand := leak.KeygenRand
  OffRand := leak.OffRand
  OnRand := leak.OnRand
  keygenRleak := if pinKeygen then pure kemMat.keygen else leak.keygenRleak
  encapsOffRleak := if pinOffline then pure kemMat.off else leak.encapsOffRleak
  encapsOnRleak st pk := if pinOnline then pure kemMat.on else leak.encapsOnRleak st pk
  keygen_fst := by cases pinKeygen <;> simp [keygen, leak.keygen_fst]
  encapsOff_fst := by cases pinOffline <;> simp [encapsOff, leak.encapsOff_fst]
  encapsOn_fst st pk := by cases pinOnline <;> simp [encapsOn, leak.encapsOn_fst]

end Pinned

end oppUniKemCKA.Security.Embedding
