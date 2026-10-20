/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic

/-!
# The IND-CPA adversary

**Setting.** Let `adv` be a security adversary against Opp-UniKEM, `q` a send budget, `e : ℕ` a
selected epoch, and `(pkStar, ctStar, kStar)` an IND-CPA challenge: a public key, a ciphertext,
and a candidate key. The simulator *marks* private values: `some x` is a known value `x` and
`none` an unavailable value. An outer `Option` records presence in the protocol state, so a field
is `none` when absent, `some none` when present but unavailable, and `some (some x)` when present
and known.

**Definitions.** The IND-CPA adversary `securityReduction adv q` samples `e ← epochChoice q` and
returns `run adv e pkStar ctStar kStar`: the output of `adv` against the simulator oracles
`oracle e pkStar ctStar kStar`, or `false` if the simulation terminates.

- In epoch `e`, A's key generation returns `pkStar` and B's encapsulation returns `ctStar`, with
  unavailable secret key, offline state, shared key, and coins; other epochs sample honestly.
- An eligible challenge at epoch `t` returns a uniform key if `0 < t < e`, `kStar` if `t = e`,
  and the recorded key otherwise.
- A permitted corruption or leaking send whose answer contains an unavailable value terminates
  the simulation.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C : Type}

/-- Simulator key generation: if `selected`, return `pkStar` with an unavailable secret key;
otherwise run `kem.keygen` and mark the secret key as known. -/
-- ANCHOR: embedding_primitives
def keygen (kem : KEMScheme ProbComp K PK SK C) (selected : Bool) (pkStar : PK) :
    ProbComp (PK × Option SK) :=
  if selected then pure (pkStar, none) else Prod.map id some <$> kem.keygen

/-- Simulator offline encapsulation: if `selected`, return the offline component of `ctStar`
with an unavailable offline state; otherwise run `onoff.encapsOff` and mark the state as known. -/
def encapsOff {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (selected : Bool) (ctStar : C) : ProbComp (Option onoff.St × onoff.C₀) :=
  if selected then pure (none, (onoff.split ctStar).1)
  else Prod.map some id <$> onoff.encapsOff

/-- Simulator online encapsulation: for an unavailable offline state, return the online
component of `ctStar` with an unavailable shared key; for a known state `st`, run
`onoff.encapsOn st pk` and mark the key as known. -/
def encapsOn {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (ctStar : C) (st : Option onoff.St) (pk : PK) : ProbComp (onoff.C₁ × Option K) :=
  match st with
  | none => pure ((onoff.split ctStar).2, none)
  | some st => Prod.map id some <$> onoff.encapsOn st pk
-- ANCHOR_END: embedding_primitives

/-- Marked KEM answering one simulator query. Key generation uses `pkStar` if `selectedA` (A is
in the selected epoch); offline encapsulation uses `ctStar` if `selectedB`, and online
encapsulation does so for an unavailable offline state. Decapsulation ignores its inputs and
returns `key`, B's recorded marked key for A's current epoch, as in the ideal game. -/
abbrev kem (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    KEMScheme ProbComp (Option K) PK (Option SK) C where
  keygen := keygen base selectedA pkStar
  encaps pk := do
    let (st, ct0) ← encapsOff onoff selectedB ctStar
    let (ct1, key) ← encapsOn onoff ctStar st pk
    pure (onoff.split.symm (ct0, ct1), key)
  decaps _ _ := pure key

/-- Deterministic-decapsulation witness for `kem`: decapsulation returns the constant `key`. -/
abbrev deterministic (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (kem base onoff selectedA selectedB pkStar ctStar key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- On/off structure of `kem`: the original ciphertext split, marked offline states, and the
algorithms `encapsOff` and `encapsOn`; the factorization holds by definition. -/
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

/-- Leaking version of `keygen`: if `selected`, return `pkStar` with unavailable secret key and
coins; otherwise run `leak.keygenRleak` and mark the secret key and coins as known. -/
def keygenLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (selected : Bool) (pkStar : PK) :
    ProbComp ((PK × Option SK) × Option leak.KeygenRand) :=
  if selected then pure ((pkStar, none), none)
  else (fun z => ((z.1.1, some z.1.2), some z.2)) <$> leak.keygenRleak

/-- Leaking version of `encapsOff`: if `selected`, return the offline component of `ctStar` with
unavailable state and coins; otherwise run `leak.encapsOffRleak` and mark the state and coins as
known. -/
def offLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (selected : Bool) (ctStar : C) :
    ProbComp ((Option onoff.St × onoff.C₀) × Option leak.OffRand) :=
  if selected then pure ((none, (onoff.split ctStar).1), none)
  else (fun z => ((some z.1.1, z.1.2), some z.2)) <$> leak.encapsOffRleak

/-- Leaking version of `encapsOn`: for an unavailable offline state, return the online component
of `ctStar` with unavailable key and coins; for a known state, run `leak.encapsOnRleak` and mark
the key and coins as known. -/
def onLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (ctStar : C) (st : Option onoff.St) (pk : PK) :
    ProbComp ((onoff.C₁ × Option K) × Option leak.OnRand) :=
  match st with
  | none => pure (((onoff.split ctStar).2, none), none)
  | some st => (fun z => ((z.1.1, some z.1.2), some z.2)) <$> leak.encapsOnRleak st pk

/-- Leakage witness for `kem` with samplers `keygenLeak`, `offLeak`, and `onLeak`: discarding
their coins gives `keygen`, `encapsOff`, and `encapsOn`, by the marginal laws of `leak`. -/
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

/-- Simulator game state: the security-game state with A's secret key, B's offline state, and
the recorded keys marked. -/
abbrev SimState {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (Sym : Type) :=
  SCKAScheme.GameState (StateA (Option SK) PK onoff.C₀ Sym)
    (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) (Option K) (Message Sym)

/-- Unmark an optional field: an absent field gives `some none`, a known value `x` gives
`some (some x)`, and a present unavailable value gives `none`, signaling termination. -/
-- ANCHOR: embedding_revealField
def revealField {α : Type} : Option (Option α) → Option (Option α)
  | none => some none
  | some none => none
  | some (some a) => some (some a)
-- ANCHOR_END: embedding_revealField

/-- Unmark A's state for a permitted corruption; the result is `none` exactly when A's secret key
is present but unavailable. -/
def revealA {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (s : StateA (Option SK) PK onoff.C₀ Sym) : Option (StA onoff Sym) := do
  let dk ← revealField s.dkA
  pure { dkA := dk, ekA := s.ekA, ct0 := s.ct0, t := s.t,
         ich := s.ich, lch := s.lch, ack := s.ack }

/-- Unmark B's state for a permitted corruption; the result is `none` exactly when B's offline
state is present but unavailable. -/
def revealB {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (s : StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) : Option (StB onoff Sym) := do
  let st ← revealField s.stCt
  pure { ekA := s.ekA, ct0 := s.ct0, ct1 := s.ct1, stCt := st, t := s.t,
         ich := s.ich, lch := s.lch, ack := s.ack }

/-- Unmark the coins returned by a leaking send: the result is `none` exactly when a returned coin
is unavailable, and `SendRand.none` gives `some SendRand.none`. -/
-- ANCHOR: embedding_revealCoins
def revealCoins {KG OFF ON : Type} :
    SendRand (Option KG) (Option OFF) (Option ON) → Option (SendRand KG OFF ON)
  | .none => some .none
  | .keygen r => .keygen <$> r
  | .off r => .off <$> r
  | .on r => .on <$> r
  | .offOn r₀ r₁ => do pure (.offOn (← r₀) (← r₁))
-- ANCHOR_END: embedding_revealCoins

/-- Apply `reveal` to an optional oracle answer: a rejection `none` gives `some none`, and an
answer `a` gives `some <$> reveal a`, which is `none` (termination) when `reveal a = none`. -/
def revealResponse {α β : Type} (reveal : α → Option β) : Option α → Option (Option β)
  | none => some none
  | some a => some <$> reveal a

/-- Run `op` and apply `reveal` to its answer in `OptionT`: the answer is `none`, which
terminates the simulation, when `reveal` fails; the successor state of `op` is kept. -/
def revealAfter {σ α β : Type} (reveal : α → Option β) (op : StateT σ ProbComp α) :
    OptionT (StateT σ ProbComp) β :=
  OptionT.mk (do pure (reveal (← op)))

/-- From state `s`, `revealAfter reveal op` runs `op` from `s` and returns `reveal a` with the
successor state of `op`. -/
theorem revealAfter_run {σ α β : Type} (reveal : α → Option β)
    (op : StateT σ ProbComp α) (s : σ) :
    ((revealAfter reveal op).run).run s =
      (do let (a, s') ← op.run s; pure (reveal a, s')) := by
  rfl

/-- Challenge oracle for selected epoch `e` and candidate key `kStar`, on game states whose key
tables have entries of type `κ`; `toKey` reads an entry as a key. A query `t` is rejected
(`none`) if `t` is exposed or challenged or no key is recorded for `t`, with A's table consulted
before B's. Otherwise it inserts `t` into `challenged` and returns a uniform key if `0 < t < e`,
`kStar` if `t = e`, and `toKey` of the recorded entry otherwise. The key tables are
unchanged. -/
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

/-- Simulator challenge oracle on marked states: a recorded key is read as its known value, or
as `kStar` if unavailable. -/
def challenge [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) : QueryImpl (ℕ →ₒ Option K) (StateT (SimState onoff Sym) ProbComp) :=
  challengeWith (fun key : Option K => key.getD kStar) e kStar
-- ANCHOR_END: embedding_challenge

/-- Simulator oracles for selected epoch `e` and IND-CPA challenge `(pkStar, ctStar, kStar)`, on
marked states. A query from state `s` is answered by the Opp-UniKEM security oracles over
`kem` with `selectedA := (s.stA.t = e)`, `selectedB := (s.stB.t = e)`, and decapsulation result
`s.keyB s.stA.t`; challenges use `challenge e kStar`. A corruption or leaking send applies its
exposure guard before unmarking its answer: a rejected query answers `none` and the simulation
continues, while a permitted answer containing an unavailable value terminates the simulation. -/
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

/-- Initial simulator state: both parties at epoch `1` with all optional local fields absent and
counters zero; empty message and key tables and empty exposure and challenge sets. -/
def initial {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure) :
    SimState onoff Sym :=
  SCKAScheme.initGameState
    { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
      ack := { ekRec := false, ctRec := false } }
    { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0, lch := ∅,
      ack := { ekRec := false, ctRec := false } }

/-- Run `adv` against `oracle e pkStar ctStar kStar` from `initial onoff`; return the output of
`adv`, or `false` if the simulation terminates. -/
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

/-- The uniform distribution on `{1, …, q}` if `q > 0`, and the epoch `1` if `q = 0`. -/
-- ANCHOR: embedding_epochChoice
def epochChoice (q : ℕ) : ProbComp ℕ :=
  if hq : q = 0 then pure 1
  else
    letI : NeZero q := ⟨hq⟩
    (fun i : Fin q => i.val + 1) <$> ($ᵗ (Fin q) : ProbComp (Fin q))
-- ANCHOR_END: embedding_epochChoice

/-- IND-CPA adversary against `base` constructed from `adv` and send budget `q`. Given `pk`, its
first stage samples `e ← epochChoice q`; given the challenge `(ct, k)`, its second stage returns
`run adv e pk ct k`. -/
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
