/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Primitives

/-!
# Selected-epoch IND-CPA adversary

**Inputs.** A security adversary `A`, an epoch `e : ℕ`, and an IND-CPA tuple
`(pkStar, ctStar, kStar)`.

**Simulation.** `run` executes the full SCKA interface from the initial state.
`Primitives` embeds the supplied public key and split ciphertext at `e`
and samples other epochs honestly. A receives B's encapsulated keys.
Eligible challenges below `e` return uniform keys, at `e` return `kStar`,
and above `e` return recorded keys. All challenge responses retain the honest
symbolic key tables.

**Exposure.** Reveal functions recover known or erased material. A permitted
request for unavailable material terminates with `false`; a rejected request
returns its rejection response. A completed run returns A's output.

**Reduction.** `epochReduction` saves `pkStar` in the first IND-CPA stage
and runs the simulation in the second. `securityReduction` additionally
chooses `e` uniformly from `1, …, q` for `q > 0`, and uses one for `q = 0`.
The adjacent-hybrid correspondence remains to be proved.
-/

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
        (SCKAScheme.oracleSendArleak sendExposureA scka u)
    | .inl (.inl (.inl (.inr u))) =>
      revealAfter (revealResponse (fun (out : ℕ × Option ℕ × Message Sym ×
          SendRand (Option leak.KeygenRand) (Option leak.OffRand) (Option leak.OnRand)) => do
        let (n, epoch, msg, coins) := out
        pure (n, epoch, msg, ← revealCoins coins)))
        (SCKAScheme.oracleSendBrleak sendExposureB scka u)
    | .inl (.inl (.inr t)) => liftM (challenge (Sym := Sym) onoff e kStar t)
    | .inl (.inr u) =>
      revealAfter (revealResponse (revealA (onoff := onoff) (Sym := Sym)))
        (SCKAScheme.oracleCorruptA (vulnA (Sym := Sym) simKem simOnOff)
          (StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym) (Option K) (Message Sym) u)
    | .inr u =>
      revealAfter (revealResponse (revealB (onoff := onoff) (Sym := Sym)))
        (SCKAScheme.oracleCorruptB (vulnB (Sym := Sym) simKem simOnOff)
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

/-- IND-CPA adversary for the adjacent epoch hybrids `e − 1` and `e`.
Its first stage saves the challenge public key; its second stage runs
`adv` in the selected-epoch simulator using the supplied ciphertext/key. -/
-- ANCHOR: epochReduction
def epochReduction [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (e : ℕ) : base.IND_CPA_Adversary where
  State := PK
  preChallenge pk := pure pk
  postChallenge pk ct key := run base onoff ecEk ecCt0 ecCt1 leak adv e pk ct key
-- ANCHOR_END: epochReduction

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
