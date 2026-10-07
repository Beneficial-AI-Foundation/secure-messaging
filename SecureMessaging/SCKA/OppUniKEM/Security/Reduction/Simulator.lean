/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic

/-!
# The IND-CPA adversary

**Setting.** Let `adv` be a security adversary against Opp-UniKEM, `e : ℕ` a selected epoch, and
`(pkStar, ctStar, kStar)` an IND-CPA challenge: a public key, a ciphertext, and a key. The
simulation *marks* private values: `some x` is a known value `x` and `none` an unavailable value.
An outer `Option` records presence in the protocol state, so a field is `none` when erased,
`some none` when present but unavailable, and `some (some x)` when present and known.

**Definitions.**

- `keygen`, `encapsOff`, `encapsOn`, and the KEM `kem` with `onOff`, `deterministic`, `leakage`:
  in the selected epoch, key generation and encapsulation return `pkStar` and the components of
  `ctStar` with unavailable secrets, key, and coins; in other epochs they run the original
  samplers and mark their results as known. Decapsulation returns B's marked recorded key.
- `oracle e pkStar ctStar kStar`: the security oracles of Opp-UniKEM with these primitives on
  marked states (`SimState`). An eligible challenge at epoch `t` returns a uniform key if
  `0 < t < e`, `kStar` if `t = e`, and the recorded key otherwise (`challenge`). A permitted
  corruption or leaking send whose answer contains an unavailable value stops the simulation
  (`revealA`, `revealB`, `revealCoins`).
- `run adv e pkStar ctStar kStar`: runs `adv` against `oracle` from the initial state `initial`
  and returns its output, or `false` if the simulation stopped.
- `epochChoice q`: the uniform distribution on `1, …, q`, and epoch `1` if `q = 0`.
- `securityReduction adv q`: the IND-CPA adversary that keeps `pkStar`, samples
  `e ← epochChoice q`, and returns `run adv e pkStar ctStar kStar` on the challenge.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C : Type}

/-- Key generation for a simulator query. When `selected = true`, return
`pkStar` with an unavailable secret; otherwise sample an honest key pair
and mark its secret as known. -/
-- ANCHOR: embedding_primitives
def keygen (kem : KEMScheme ProbComp K PK SK C) (selected : Bool) (pkStar : PK) :
    ProbComp (PK × Option SK) :=
  if selected then pure (pkStar, none) else Prod.map id some <$> kem.keygen

/-- Offline encapsulation for a simulator query. In the selected epoch,
return the offline component of `ctStar` with unavailable offline state;
otherwise sample the original offline algorithm. -/
def encapsOff {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (selected : Bool) (ctStar : C) : ProbComp (Option onoff.St × onoff.C₀) :=
  if selected then pure (none, (onoff.split ctStar).1)
  else Prod.map some id <$> onoff.encapsOff

/-- Online encapsulation uses the original algorithm for known offline
state. Unavailable state denotes the selected epoch: return `ctStar`'s
online component and mark its honest encapsulated key as unavailable. -/
def encapsOn {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (ctStar : C) (st : Option onoff.St) (pk : PK) : ProbComp (onoff.C₁ × Option K) :=
  match st with
  | none => pure ((onoff.split ctStar).2, none)
  | some st => Prod.map id some <$> onoff.encapsOn st pk
-- ANCHOR_END: embedding_primitives

/-- KEM used for one simulator query. `selectedA` and `selectedB` identify
whether each role is in the selected epoch. `key` is B's recorded symbolic
key for A's current epoch and is used for auxiliary decapsulation. -/
abbrev kem (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    KEMScheme ProbComp (Option K) PK (Option SK) C where
  keygen := keygen base selectedA pkStar
  encaps pk := do
    let (st, ct0) ← encapsOff onoff selectedB ctStar
    let (ct1, key) ← encapsOn onoff ctStar st pk
    pure (onoff.split.symm (ct0, ct1), key)
  decaps _ _ := pure key

/-- The simulator's constant decapsulation is deterministic and returns
its supplied auxiliary key `key`, including an unavailable selected key. -/
abbrev deterministic (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (kem base onoff selectedA selectedB pkStar ctStar key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- The simulator retains the original ciphertext split and marks its
offline state as known or unavailable. Its encapsulation factors into the
simulator's offline and online algorithms by construction. -/
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

/-- Leaking key generation returns unavailable coins in the selected epoch
and the original leakage sample, with known secret and coins, otherwise. -/
def keygenLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (selected : Bool) (pkStar : PK) :
    ProbComp ((PK × Option SK) × Option leak.KeygenRand) :=
  if selected then pure ((pkStar, none), none)
  else (fun z => ((z.1.1, some z.1.2), some z.2)) <$> leak.keygenRleak

/-- Leaking offline encapsulation returns unavailable state and coins in
the selected epoch; all other epochs use the original leakage algorithm. -/
def offLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (selected : Bool) (ctStar : C) :
    ProbComp ((Option onoff.St × onoff.C₀) × Option leak.OffRand) :=
  if selected then pure ((none, (onoff.split ctStar).1), none)
  else (fun z => ((some z.1.1, z.1.2), some z.2)) <$> leak.encapsOffRleak

/-- Leaking online encapsulation returns unavailable key and coins for the
selected offline state; known states use the original leakage algorithm. -/
def onLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (ctStar : C) (st : Option onoff.St) (pk : PK) :
    ProbComp ((onoff.C₁ × Option K) × Option leak.OnRand) :=
  match st with
  | none => pure (((onoff.split ctStar).2, none), none)
  | some st => (fun z => ((z.1.1, some z.1.2), some z.2)) <$> leak.encapsOnRleak st pk

/-- Simulator leakage witnesses. Forgetting the marked coins recovers
each ordinary simulator algorithm, by the original leakage marginal laws. -/
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
    cases selectedA
    · change (do let z ← keygenLeak leak false pkStar; pure z.1) = keygen base false pkStar
      simp only [keygenLeak, keygen, Bool.false_eq_true, ↓reduceIte, bind_map_left]
      rw [← leak.keygen_fst]
      simp [map_eq_bind_pure_comp, bind_assoc, Prod.map, id]
    · simp [keygenLeak, keygen]
  encapsOff_fst := by
    cases selectedB
    · change (do let z ← offLeak leak false ctStar; pure z.1) = encapsOff onoff false ctStar
      simp only [offLeak, encapsOff, Bool.false_eq_true, ↓reduceIte, bind_map_left]
      rw [← leak.encapsOff_fst]
      simp [map_eq_bind_pure_comp, bind_assoc, Prod.map, id]
    · simp [offLeak, encapsOff]
  encapsOn_fst st pk := by
    cases st with
    | none => simp [onLeak, encapsOn]
    | some st =>
      change (do let z ← onLeak leak ctStar (some st) pk; pure z.1) =
        encapsOn onoff ctStar (some st) pk
      simp only [onLeak, encapsOn, bind_map_left]
      rw [← leak.encapsOn_fst st pk]
      simp [map_eq_bind_pure_comp, bind_assoc, Prod.map, id]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Simulator state: private keys, offline states, and honest epoch keys
are individually marked as known (`some`) or unavailable (`none`). -/
abbrev SimState {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (Sym : Type) :=
  SCKAScheme.GameState (StateA (Option SK) PK onoff.C₀ Sym)
    (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) (Option K) (Message Sym)

/-- Recover an optional secret field. An erased field returns `some none`;
a present unavailable secret returns `none`, signaling termination. -/
-- ANCHOR: embedding_revealField
def revealField {α : Type} : Option (Option α) → Option (Option α)
  | none => some none
  | some none => none
  | some (some a) => some (some a)
-- ANCHOR_END: embedding_revealField

/-- Recover A's original state for a permitted corruption, failing exactly
when its current decapsulation key is present but unavailable. -/
def revealA {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (s : StateA (Option SK) PK onoff.C₀ Sym) : Option (StA onoff Sym) := do
  let dk ← revealField s.dkA
  pure { dkA := dk, ekA := s.ekA, ct0 := s.ct0, t := s.t,
         ich := s.ich, lch := s.lch, ack := s.ack }

/-- Recover B's original state for a permitted corruption, failing exactly
when its offline encapsulation state is present but unavailable. -/
def revealB {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (s : StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) : Option (StB onoff Sym) := do
  let st ← revealField s.stCt
  pure { ekA := s.ekA, ct0 := s.ct0, ct1 := s.ct1, stCt := st, t := s.t,
         ich := s.ich, lch := s.lch, ack := s.ack }

/-- Recover the coins returned by a leaking send. Deterministic sends
return `some SendRand.none`; a sampling phase with unavailable coins
returns `none`, signaling termination. -/
-- ANCHOR: embedding_revealCoins
def revealCoins {KG OFF ON : Type} :
    SendRand (Option KG) (Option OFF) (Option ON) → Option (SendRand KG OFF ON)
  | .none => some .none
  | .keygen r => .keygen <$> r
  | .off r => .off <$> r
  | .on r => .on <$> r
  | .offOn r₀ r₁ => do pure (.offOn (← r₀) (← r₁))
-- ANCHOR_END: embedding_revealCoins

/-- Convert an optional oracle response using `reveal`. Rejection (`none`)
is returned normally; an unavailable successful response terminates. -/
def revealResponse {α β : Type} (reveal : α → Option β) : Option α → Option (Option β)
  | none => some none
  | some a => some <$> reveal a

/-- Apply a response conversion after a stateful oracle operation. A
failed conversion terminates the enclosing `OptionT` simulation. -/
def revealAfter {σ α β : Type} (reveal : α → Option β) (op : StateT σ ProbComp α) :
    OptionT (StateT σ ProbComp) β :=
  OptionT.mk (do pure (reveal (← op)))

/-- For every operation `op` and initial state `s`, response conversion
returns `reveal a` and retains the successor state sampled by `op`. -/
theorem revealAfter_run {σ α β : Type} (reveal : α → Option β)
    (op : StateT σ ProbComp α) (s : σ) :
    ((revealAfter reveal op).run).run s =
      (do let (a, s') ← op.run s; pure (reveal a, s')) := by
  rfl

/-- Challenge oracle for selected epoch `e` and supplied KEM key `kStar`.
Eligible epochs below `e` return independent uniform keys; the selected
epoch returns `kStar`; later epochs return their recorded known keys.
Exposed, repeated, and unavailable-table challenges return `none`.
Every challenge preserves both honest key tables. -/
-- ANCHOR: embedding_challenge
def challenge [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) : QueryImpl (ℕ →ₒ Option K)
      (StateT (SimState onoff Sym) ProbComp) :=
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
          else pure (if t = e then kStar else honest.getD kStar)
        set { s with challenged := insert t s.challenged }
        pure (some k)
-- ANCHOR_END: embedding_challenge

/-- Full selected-epoch oracle simulator. For each query, instantiate the
original protocol with marked KEM primitives at the roles' current epochs.
Corruption and leaking-send guards run before response conversion, so a
rejected exposure query returns its rejection response. Successful exposure requiring
an unavailable secret or coin terminates through `OptionT`. -/
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

/-- Initial simulator state: both parties start in epoch one, local
secret fields are absent, and message and key tables and exposure and
challenge sets are empty. -/
def initial {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure) :
    SimState onoff Sym :=
  SCKAScheme.initGameState
    { dkA := none, ekA := none, ct0 := none, t := 1, ich := 0, lch := ∅,
      ack := { ekRec := false, ctRec := false } }
    { ekA := none, ct0 := none, ct1 := none, stCt := none, t := 1, ich := 0, lch := ∅,
      ack := { ekRec := false, ctRec := false } }

/-- For inputs `adv`, selected epoch `e`, and challenge tuple
`(pkStar, ctStar, kStar)`, execute the simulator from `initial onoff`.
Return the adversary's output on completion and `false` on exposure
termination. Selected private material is represented by unavailable markers. -/
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

/-- Select an epoch uniformly from `{1, …, q}` when `q > 0`. For `q = 0`,
return epoch one; the zero-send security theorem treats that case separately. -/
-- ANCHOR: embedding_epochChoice
def epochChoice (q : ℕ) : ProbComp ℕ :=
  if hq : q = 0 then pure 1
  else
    letI : NeZero q := ⟨hq⟩
    (fun i : Fin q => i.val + 1) <$> ($ᵗ (Fin q) : ProbComp (Fin q))
-- ANCHOR_END: embedding_epochChoice

/-- Single IND-CPA reduction for a send budget `q`. The first stage chooses
an epoch uniformly from `1, …, q` and saves the challenge public key. The
second stage executes the selected-epoch simulator and returns its Boolean
output, including `false` on unavailable-secret exposure. -/
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
