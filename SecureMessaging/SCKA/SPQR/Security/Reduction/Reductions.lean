/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Security.Reduction.HybridGame
public import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage
public import ToVCVio.OracleComp.Constructions.EpochChoice
public import SecureMessaging.SCKA.MLKEMBraid.Security.KDFGame

/-!
# The merged reductions

Let `adv` be an SCKA adversary against SPQR and `q` its send budget. A *context*
`ctx = (e, ik, d) ← sampleContext q` consists of a challenge epoch `e ← epochChoice q`, uniform
on `{1, …, q}` (`1` if `q = 0`), an initial key `ik ← sampleInitKey`, and dummies
`d ← sampleDummies`; `contextProb q G` is the acceptance probability of a game `G e d ik` over a
sampled context.

A *step* `s ← sampleStep q` adds to a context a uniform version `x ∈ {real, random}` (`false`,
`true`) and a uniform bit `prev`, which selects the epoch `s.epoch` at which the step embeds its
challenge: `e - 1` if `prev`, `e` otherwise. On a public key `pk` and a ciphertext `c`, the
*step game* `stepGame s pk c w` embeds the key `w` at `s.epoch`:

- for `prev = false`, it runs the simulated game of `e` over `hybridAuth auth e ik κ` for
  `κ ←$ P.EpochKey`, with the update of `e` keyed by `w` and the challenge key `w` in `real` and a
  uniform `k'` in `random`;
- for `prev = true`, it runs `prevGame x e d ik pk c₁ c₂ w`, with the update of `e - 1` keyed by
  `w` (`Reduction.HybridGame`).

`stepOutput` returns the output of the step game, negated in version `random`. The three
reductions are:

```text
𝓑_KEM.pre(pk):        s ← sampleStep q
𝓑_KEM.post(c, k):     stepOutput s pk c (P.kdfOK k s.epoch)
𝓑_KDF.context:        s ← sampleStep q;  (pk, _) ← KeyGen;  (c, _) ← Encaps(pk);  return s.epoch
𝓑_KDF.guess(y):       stepOutput s pk c y
𝓑_Auth.context:       ctx ← sampleContext q;  (pk, _) ← KeyGen;  (c, _) ← Encaps(pk);  return e
𝓑_Auth.guess(y, h):   simRun over withHidden auth h e on pk, c with the challenge key y
```

Each experiment averages games of the chain (`Reduction.HybridGame`) over a sampled context. The
step games whose embedded key is the derived key of the encapsulated key, the derived key of a
uniform KEM key, or a uniform epoch key are `realGame x prev`, `randGame x prev` and
`unifGame x prev`:

| step `(x, prev)`  | `realGame`    | `randGame`    | `unifGame`     |
| ----------------- | ------------- | ------------- | -------------- |
| `(real, false)`   | `realKey`     | `randKey`     | `randEpochKey` |
| `(random, false)` | `realKeyChal` | `randKeyChal` | `splitKeys`    |
| `(x, true)`       | `prevReal x`  | `prevRand x`  | `prevKdf x`    |

With `±p := p` for `x = real` and `1 - p` for `x = random` (`kemReduction_prEvent_toReal`,
`kdfReduction_prEvent_toReal`, `authReduction_prEvent_toReal`):

```text
Pr[IND-CPA experiment of 𝓑_KEM with bit b] = 4⁻¹ ∑_{x, prev} ±contextProb (G x prev),
  G := realGame for b = true, randGame for b = false
Pr[kdfContextExp P.kdfOK 𝓑_KDF derived] = 4⁻¹ ∑_{x, prev} ±contextProb (G x prev),
  G := randGame for derived = true, unifGame for derived = false
Pr[authHideExp 𝓑_Auth true] = contextProb randEpochKey
Pr[authHideExp 𝓑_Auth false] = contextProb splitKeys
```

The key-hiding game hands `𝓑_Auth` the operations of `auth` on the hidden state
`hiddenState auth e ik' κ` for its own initial key `ik'`; the authenticator map
`hiddenMap e (hiddenState auth e ik' κ)` (`Reduction.AuthMap`) relates the simulated game
over `withHidden` to the one over `hybridAuth auth e ik₀ κ`, for `ik₀ := ik'` if `e = 1` and the
initial key of the context otherwise (`prEvent_simRun_withHidden`).

**Main result** (`hybrid_gap_eq_reductions`). Let
`p_i := Pr[idealExp (hybridMode i) adv = true]`. For `q > 0`, if every gap `p_{e-1} - p_e`
satisfies the identity of `idealExp_gap_eq` (`Reduction.HybridGame`), then averaging it over the
challenge epoch gives `p_0 - p_q = q · (4 Δ_KEM + 4 Δ_KDF + Δ_Auth)`, where each `Δ` is the
difference between the experiments above of a reduction with bit `true` and with bit `false`.
-/

@[expose] public section

open OracleSpec OracleComp

namespace SPQR

open Chunked
open Braid (hiddenAuth)

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (sampleInitKey : ProbComp InitKey)

/-! ### Contexts and averaging -/

/-- A sampled context of the reductions: a challenge epoch, an initial key and dummies. -/
structure Context (P : SPQR.Parameters ProbComp) (InitKey : Type) where
  /-- The challenge epoch. -/
  e : ℕ
  /-- The initial key. -/
  ik : InitKey
  /-- The dummies. -/
  d : Dummies P

/-- Sample the context: `e ← epochChoice q`, `ik ← sampleInitKey`, `d ← sampleDummies`. -/
def sampleContext (q : ℕ) : ProbComp (Context P InitKey) := do
  let e ← ToVCVio.epochChoice q
  let ik ← sampleInitKey
  let d ← sampleDummies
  pure ⟨e, ik, d⟩

/-- The acceptance probability of a game over a sampled context. -/
noncomputable def contextProb (q : ℕ) (game : ℕ → Dummies P → InitKey → ProbComp Bool) : ℝ :=
  (Pr{let y ← (do
    let ctx ← sampleContext sampleInitKey q
    game ctx.e ctx.d ctx.ik)}[y = true]).toReal

/-- For `q ≠ 0`, `∑_{i < q} gameProb game (i + 1) = q · contextProb q game`. -/
private theorem sum_gameProb_eq (q : ℕ) (hq : q ≠ 0)
    (game : ℕ → Dummies P → InitKey → ProbComp Bool) :
    ∑ i ∈ Finset.range q, gameProb sampleInitKey game (i + 1) =
      (q : ℝ) * contextProb sampleInitKey q game := by
  have h : contextProb sampleInitKey q game =
      (q : ℝ)⁻¹ * ∑ i : Fin q, gameProb sampleInitKey game (i.val + 1) := by
    simp only [contextProb, sampleContext, bind_assoc, pure_bind]
    exact ToVCVio.toReal_prEvent_epochChoice_bind q hq _ (· = true)
  rw [h, ← Fin.sum_univ_eq_sum_range (fun i => gameProb sampleInitKey game (i + 1)) q,
    ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hq), one_mul]

/-- Negating the output: `Pr[!y | y ← g] = 1 - Pr[y | y ← g]`. -/
private theorem toReal_prEvent_not_map (g : ProbComp Bool) :
    (Pr{let y ← (! ·) <$> g}[y = true]).toReal = 1 - (Pr{let y ← g}[y = true]).toReal := by
  have h : Pr{let y ← (! ·) <$> g}[y = true] = 1 - Pr{let y ← g}[y = true] := by
    rw [prEvent_map, ← (show Pr{let _ ← g}[True] = 1 by simp),
      ← prEvent_add_prEvent_not_eq_prEvent_true g (· = true),
      ENNReal.add_sub_cancel_left (prEvent_ne_top _)]
    exact prEvent_congr g _ _ fun b => by cases b <;> simp
  rw [h, ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top, ENNReal.toReal_one]

/-! ### Steps -/

/-- A step of the merged reductions: a version `x` (`false` for `real`, `true` for `random`), the
choice `prev` of the epoch before the challenge epoch, and a context. -/
structure Step (P : SPQR.Parameters ProbComp) (InitKey : Type) where
  /-- The version: `false` for `real`, `true` for `random`. -/
  x : Bool
  /-- `true` for the epoch before the challenge epoch, `false` for the challenge epoch. -/
  prev : Bool
  /-- The context. -/
  ctx : Context P InitKey

/-- The epoch at which a step embeds its challenge: `ctx.e - 1` if `prev`, else `ctx.e`. -/
def Step.epoch (s : Step P InitKey) : ℕ := if s.prev then s.ctx.e - 1 else s.ctx.e

/-- Sample a step: `(x, prev) ←$ Bool × Bool` and `ctx ← sampleContext q`. -/
def sampleStep (q : ℕ) : ProbComp (Step P InitKey) := do
  let xp ← ($ᵗ (Bool × Bool) : ProbComp (Bool × Bool))
  let ctx ← sampleContext sampleInitKey q
  pure ⟨xp.1, xp.2, ctx⟩

/-- For `q`, the average over a sampled step of a function of the step:
`Pr[s ← sampleStep q; f s] = 4⁻¹ · ∑_{x, prev} Pr[ctx ← sampleContext q; f ⟨x, prev, ctx⟩]`. -/
theorem prEvent_sampleStep_bind_toReal (q : ℕ) (f : Step P InitKey → ProbComp Bool) :
    (Pr{let y ← (do let s ← sampleStep sampleInitKey q; f s)}[y = true]).toReal =
      4⁻¹ * ∑ x : Bool, ∑ prev : Bool, (Pr{let y ← (do
        let ctx ← sampleContext sampleInitKey q
        f ⟨x, prev, ctx⟩)}[y = true]).toReal := by
  simp only [sampleStep, bind_assoc, pure_bind]
  rw [prEvent_uniform_bind_toReal, Fintype.sum_prod_type]
  norm_num [Fintype.card_prod, Fintype.card_bool]

/-- For `x = true`, negating the output of a step game over a sampled context complements its
acceptance probability. -/
private theorem toReal_prEvent_ctx_ite_not (q : ℕ) (x : Bool)
    (g : Context P InitKey → ProbComp Bool) :
    (Pr{let y ← (do
      let ctx ← sampleContext sampleInitKey q
      if x then (! ·) <$> g ctx else g ctx)}[y = true]).toReal =
    if x then 1 - (Pr{let y ← (do
      let ctx ← sampleContext sampleInitKey q
      g ctx)}[y = true]).toReal
    else (Pr{let y ← (do
      let ctx ← sampleContext sampleInitKey q
      g ctx)}[y = true]).toReal := by
  cases x
  · simp
  · simp only [↓reduceIte]
    rw [← toReal_prEvent_not_map]
    simp only [map_bind]

/-- The average over a sampled step of the output of a step game, negated for `x = true`. -/
private theorem toReal_prEvent_sampleStep_ite_not (q : ℕ) (g : Step P InitKey → ProbComp Bool) :
    (Pr{let y ← (do
      let s ← sampleStep sampleInitKey q
      if s.x then (! ·) <$> g s else g s)}[y = true]).toReal =
    4⁻¹ * ∑ x : Bool, ∑ prev : Bool,
      if x then 1 - (Pr{let y ← (do
        let ctx ← sampleContext sampleInitKey q
        g ⟨x, prev, ctx⟩)}[y = true]).toReal
      else (Pr{let y ← (do
        let ctx ← sampleContext sampleInitKey q
        g ⟨x, prev, ctx⟩)}[y = true]).toReal := by
  rw [prEvent_sampleStep_bind_toReal]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun prev _ => ?_
  exact toReal_prEvent_ctx_ite_not sampleInitKey q x fun ctx => g ⟨x, prev, ctx⟩

/-- Dropping a sample that the rest of a game does not use, after a key generation and an
encapsulation. -/
private theorem prEvent_material_bind_unused {β : Type} (s : ProbComp β)
    (G : P.PK → P.C → P.K → ProbComp Bool) :
    Pr{let y ← (do
      let (pk, _) ← P.det.toKEM.keygen
      let (c, k) ← P.det.toKEM.encaps pk
      let _ ← s
      G pk c k)}[y = true] =
    Pr{let y ← (do
      let (pk, _) ← P.det.toKEM.keygen
      let (c, k) ← P.det.toKEM.encaps pk
      G pk c k)}[y = true] := by
  refine OracleComp.prEvent_bind_congr_of_support' _ _ fun kp _ => ?_
  obtain ⟨pk, sk⟩ := kp
  refine OracleComp.prEvent_bind_congr_of_support' _ _ fun ck _ => ?_
  obtain ⟨c, k⟩ := ck
  exact (OracleComp.EvalDistEq.bind_const _ _).prEvent_eq _

variable [DecidableEq P.EpochKey] [SampleableType P.EpochKey]
  (adv : SecurityAdversary P AuthState) (q : ℕ)

/-- The game of a step `s` on the public values `pk`, `c` of an encapsulation, with `w` the key
embedded at `s.epoch`. For `s.prev = false`: the simulated game of `e := s.ctx.e` over
`hybridAuth auth e ik κ` for a uniform `κ`, with the update of `e` keyed by `w` and the challenge
key `w` in version `real` and a uniform `k'` in version `random`. For `s.prev = true`:
`prevGame s.x` with the update of `e - 1` keyed by `w`. -/
def stepGame (s : Step P InitKey) (pk : P.PK) (c : P.C) (w : P.EpochKey) : ProbComp Bool :=
  if s.prev then
    prevGame auth sampleInitKey adv s.x s.ctx.e s.ctx.d s.ctx.ik pk (P.det.splitC c).1
      (P.det.splitC c).2 w
  else do
    let kStar ← if s.x then ($ᵗ P.EpochKey : ProbComp P.EpochKey) else pure w
    let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
    simRun (hybridAuth auth s.ctx.e s.ctx.ik κ) sampleInitKey adv s.ctx.e s.ctx.d s.ctx.ik pk
      (P.det.splitC c).1 (P.det.splitC c).2 kStar w

/-- The output of a step: that of `stepGame`, negated in version `random`. -/
def stepOutput (s : Step P InitKey) (pk : P.PK) (c : P.C) (w : P.EpochKey) : ProbComp Bool :=
  if s.x then (! ·) <$> stepGame auth sampleInitKey adv s pk c w
  else stepGame auth sampleInitKey adv s pk c w

section Kinds

variable [SampleableType P.K]

/-- The game of the step `(x, prev)` with the derived key of a fresh encapsulation. -/
def realGame (x prev : Bool) : ℕ → Dummies P → InitKey → ProbComp Bool :=
  if prev then prevReal auth sampleInitKey adv x
  else if x then realKeyChal auth sampleInitKey adv else realKey auth sampleInitKey adv

/-- The game of the step `(x, prev)` with the derived key of a uniform KEM key. -/
def randGame (x prev : Bool) : ℕ → Dummies P → InitKey → ProbComp Bool :=
  if prev then prevRand auth sampleInitKey adv x
  else if x then randKeyChal auth sampleInitKey adv else randKey auth sampleInitKey adv

/-- The game of the step `(x, prev)` with a uniform epoch key. -/
def unifGame (x prev : Bool) : ℕ → Dummies P → InitKey → ProbComp Bool :=
  if prev then prevKdf auth sampleInitKey adv x
  else if x then splitKeys auth sampleInitKey adv else randEpochKey auth sampleInitKey adv

omit [SampleableType P.K] in
/-- The step game of `⟨x, prev, ctx⟩` with the derived key of a fresh encapsulated key accepts as
often as `realGame x prev`. -/
private theorem step_real (x prev : Bool) (ctx : Context P InitKey) :
    Pr{let y ← (do
      let (pk, _) ← P.det.toKEM.keygen
      let (c, k) ← P.det.toKEM.encaps pk
      stepGame auth sampleInitKey adv ⟨x, prev, ctx⟩ pk c
        (P.kdfOK k (Step.epoch ⟨x, prev, ctx⟩)))}[y = true] =
    Pr{let y ← realGame auth sampleInitKey adv x prev ctx.e ctx.d ctx.ik}[y = true] := by
  cases x <;> cases prev <;>
    simp [realGame, stepGame, Step.epoch, realKey, realKeyChal, prevReal]

/-- The step game of `⟨x, prev, ctx⟩` with the derived key of a uniform KEM key accepts as often
as `randGame x prev`. -/
private theorem step_rand (x prev : Bool) (ctx : Context P InitKey) :
    Pr{let y ← (do
      let (pk, _) ← P.det.toKEM.keygen
      let (c, _) ← P.det.toKEM.encaps pk
      let r ← ($ᵗ P.K : ProbComp P.K)
      stepGame auth sampleInitKey adv ⟨x, prev, ctx⟩ pk c
        (P.kdfOK r (Step.epoch ⟨x, prev, ctx⟩)))}[y = true] =
    Pr{let y ← randGame auth sampleInitKey adv x prev ctx.e ctx.d ctx.ik}[y = true] := by
  cases x <;> cases prev <;>
    simp [randGame, stepGame, Step.epoch, randKey, randKeyChal, prevRand]

omit [SampleableType P.K] in
/-- The step game of `⟨x, prev, ctx⟩` with a uniform epoch key accepts as often as
`unifGame x prev`. -/
private theorem step_unif (x prev : Bool) (ctx : Context P InitKey) :
    Pr{let y ← (do
      let (pk, _) ← P.det.toKEM.keygen
      let (c, _) ← P.det.toKEM.encaps pk
      let u ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      stepGame auth sampleInitKey adv ⟨x, prev, ctx⟩ pk c u)}[y = true] =
    Pr{let y ← unifGame auth sampleInitKey adv x prev ctx.e ctx.d ctx.ik}[y = true] := by
  cases x <;> cases prev <;>
    simp [unifGame, stepGame, randEpochKey, splitKeys, prevKdf]

end Kinds

/-! ### The merged IND-CPA reduction -/

/-- The merged IND-CPA adversary against `P.det.toKEM`: on `pk`, draw a step `s ← sampleStep q`; on
the challenge `(c, k)`, return the output of the step game of `s` on `pk`, `c` with the embedded
key `P.kdfOK k s.epoch`, negated in version `random`. -/
-- ANCHOR: kemReduction
def kemReduction : P.det.toKEM.IND_CPA_Adversary where
  State := Step P InitKey × P.PK
  preChallenge pk := do
    let s ← sampleStep sampleInitKey q
    pure (s, pk)
  postChallenge st c k := stepOutput auth sampleInitKey adv st.1 st.2 c (P.kdfOK k st.1.epoch)
-- ANCHOR_END: kemReduction

section KEM

variable [SampleableType P.K]

/-- The step game of `s` with the derived key of the encapsulated key (`b = true`) or of a
uniform KEM key (`b = false`). -/
private def kemStep (b : Bool) (s : Step P InitKey) : ProbComp Bool := do
  let (pk, _) ← P.det.toKEM.keygen
  let (c, k) ← P.det.toKEM.encaps pk
  let r ← ($ᵗ P.K : ProbComp P.K)
  stepGame auth sampleInitKey adv s pk c (P.kdfOK (if b then k else r) s.epoch)

/-- The IND-CPA experiment of `kemReduction` with bit `b` draws the step first and outputs the
step game `kemStep b s`, negated for `s.x = true`. -/
private theorem kemReduction_exp_eq (b : Bool) :
    Pr{let y ← (P.det.toKEM.IND_CPA_Experiment ProbCompRuntime.probComp
      (kemReduction auth sampleInitKey adv q) b)}[y = true] =
    Pr{let y ← (do
      let s ← sampleStep sampleInitKey q
      if s.x then (! ·) <$> kemStep auth sampleInitKey adv b s
      else kemStep auth sampleInitKey adv b s)}[y = true] := by
  rw [← KEMScheme.indCPAExpProb_prEvent_true_eq]
  simp only [KEMScheme.indCPAExpProb, KEMScheme.indCPAPrefix, kemReduction, bind_assoc,
    pure_bind]
  rw [(OracleComp.EvalDistEq.bind_bind_swap P.det.toKEM.keygen (sampleStep sampleInitKey q)
    _).prEvent_eq]
  refine OracleComp.prEvent_bind_congr_of_support' _ _ fun s _ => ?_
  cases hx : s.x <;> simp [stepOutput, kemStep, hx, map_bind]

/-- The step game `kemStep b ⟨x, prev, ctx⟩` accepts as often as `realGame x prev` for `b = true`
and `randGame x prev` for `b = false`. -/
private theorem kemStep_prEvent (b x prev : Bool) (ctx : Context P InitKey) :
    Pr{let y ← kemStep auth sampleInitKey adv b ⟨x, prev, ctx⟩}[y = true] =
    Pr{let y ← (if b then realGame auth sampleInitKey adv x prev ctx.e ctx.d ctx.ik
      else randGame auth sampleInitKey adv x prev ctx.e ctx.d ctx.ik)}[y = true] := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← step_rand]
    rfl
  · simp only [↓reduceIte]
    rw [← step_real]
    exact prEvent_material_bind_unused ($ᵗ P.K) fun pk c k =>
      stepGame auth sampleInitKey adv ⟨x, prev, ctx⟩ pk c (P.kdfOK k (Step.epoch ⟨x, prev, ctx⟩))

/-- The IND-CPA experiment of `kemReduction` with bit `b` averages the step games over the four
steps, complemented in version `random`: for `G := realGame` if `b = true` and `G := randGame` if
`b = false`, `Pr[exp b] = 4⁻¹ · ∑_{x, prev} ±contextProb (G x prev)`, where `±p` is `p` for
`x = false` and `1 - p` for `x = true`. -/
theorem kemReduction_prEvent_toReal (b : Bool) :
    (Pr{let y ← (P.det.toKEM.IND_CPA_Experiment ProbCompRuntime.probComp
      (kemReduction auth sampleInitKey adv q) b)}[y = true]).toReal =
    4⁻¹ * ∑ x : Bool, ∑ prev : Bool,
      if x then 1 - contextProb sampleInitKey q (if b then realGame auth sampleInitKey adv x prev
        else randGame auth sampleInitKey adv x prev)
      else contextProb sampleInitKey q (if b then realGame auth sampleInitKey adv x prev
        else randGame auth sampleInitKey adv x prev) := by
  rw [kemReduction_exp_eq, toReal_prEvent_sampleStep_ite_not]
  have h (x prev : Bool) : (Pr{let y ← (do
      let ctx ← sampleContext sampleInitKey q
      kemStep auth sampleInitKey adv b ⟨x, prev, ctx⟩)}[y = true]).toReal =
      contextProb sampleInitKey q (if b then realGame auth sampleInitKey adv x prev
        else randGame auth sampleInitKey adv x prev) := by
    unfold contextProb
    congr 1
    refine OracleComp.prEvent_bind_congr_of_support' _ _ fun ctx _ => ?_
    rw [kemStep_prEvent]
    cases b <;> rfl
  simp only [h]

end KEM

/-! ### The merged KDF reduction -/

/-- The merged key-derivation adversary: it draws a step `s ← sampleStep q`, a key pair `(pk, _)`
and an encapsulation `(c, _)` under `pk`, and chooses the label `s.epoch`; on the epoch key `y`,
it returns the output of the step game of `s` on `pk`, `c` with the embedded key `y`, negated in
version `random`. -/
-- ANCHOR: kdfReduction
def kdfReduction : Braid.KDFContextAdversary P.EpochKey where
  State := Step P InitKey × P.PK × P.C
  context := do
    let s ← sampleStep sampleInitKey q
    let (pk, _) ← P.det.toKEM.keygen
    let (c, _) ← P.det.toKEM.encaps pk
    pure (s.epoch, (s, pk, c))
  guess st y := stepOutput auth sampleInitKey adv st.1 st.2.1 st.2.2 y
-- ANCHOR_END: kdfReduction

section KDF

variable [SampleableType P.K]

/-- The key-derivation experiment of `kdfReduction` averages the step games over the four steps,
complemented in version `random`: for `G := randGame` if `derived` and `G := unifGame` otherwise,
`Pr[kdfContextExp derived] = 4⁻¹ · ∑_{x, prev} ±contextProb (G x prev)`, where `±p` is `p` for
`x = false` and `1 - p` for `x = true`. -/
theorem kdfReduction_prEvent_toReal (derived : Bool) :
    (Pr{let y ← (Braid.kdfContextExp P.kdfOK (kdfReduction auth sampleInitKey adv q)
      derived)}[y = true]).toReal =
    4⁻¹ * ∑ x : Bool, ∑ prev : Bool,
      if x then 1 - contextProb sampleInitKey q (if derived then randGame auth sampleInitKey adv x
        prev else unifGame auth sampleInitKey adv x prev)
      else contextProb sampleInitKey q (if derived then randGame auth sampleInitKey adv x prev
        else unifGame auth sampleInitKey adv x prev) := by
  let G : Step P InitKey → ProbComp Bool := fun s => do
    let (pk, _) ← P.det.toKEM.keygen
    let (c, _) ← P.det.toKEM.encaps pk
    if derived then do
      let k ← ($ᵗ P.K : ProbComp P.K)
      stepGame auth sampleInitKey adv s pk c (P.kdfOK k s.epoch)
    else do
      let u ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      stepGame auth sampleInitKey adv s pk c u
  have hexp : Pr{let y ← (Braid.kdfContextExp P.kdfOK (kdfReduction auth sampleInitKey adv q)
      derived)}[y = true] =
      Pr{let y ← (do
        let s ← sampleStep sampleInitKey q
        if s.x then (! ·) <$> G s else G s)}[y = true] := by
    simp only [Braid.kdfContextExp, Braid.kdfExp, kdfReduction, PRGScheme.prgRealExperiment,
      PRGScheme.prgIdealExperiment, bind_assoc, pure_bind]
    refine OracleComp.prEvent_bind_congr_of_support' _ _ fun s _ => ?_
    cases derived <;> cases hx : s.x <;> simp [G, stepOutput, hx, map_bind]
  rw [hexp, toReal_prEvent_sampleStep_ite_not]
  have h (x prev : Bool) : (Pr{let y ← (do
      let ctx ← sampleContext sampleInitKey q
      G ⟨x, prev, ctx⟩)}[y = true]).toReal =
      contextProb sampleInitKey q (if derived then randGame auth sampleInitKey adv x prev
        else unifGame auth sampleInitKey adv x prev) := by
    unfold contextProb
    congr 1
    refine OracleComp.prEvent_bind_congr_of_support' _ _ fun ctx _ => ?_
    cases derived
    · simpa [G] using step_unif auth sampleInitKey adv x prev ctx
    · simpa [G] using step_rand auth sampleInitKey adv x prev ctx
  simp only [h]

end KDF

/-! ### The key-hiding reduction -/

/-- The key-hiding adversary: draw a context `ctx`, a key pair `(pk, _)` and an encapsulation
`(c, _)` under `pk`, and choose the epoch `ctx.e`; on the challenge key `y` and the operations `h`
on the hidden state, run the simulated game of `ctx.e` over `withHidden auth h ctx.e` with the
challenge key `y`. -/
-- ANCHOR: authReduction
def authReduction : Braid.AuthHideAdversary P.EpochKey AuthState P.det.PKheader
    (P.det.C₁ × P.det.C₂) P.Mac where
  State := Context P InitKey × P.PK × P.C
  context := do
    let ctx ← sampleContext sampleInitKey q
    let (pk, _) ← P.det.toKEM.keygen
    let (c, _) ← P.det.toKEM.encaps pk
    pure (ctx.e, (ctx, pk, c))
  guess st y h :=
    simRun (withHidden auth h st.1.e) sampleInitKey adv st.1.e st.1.d st.1.ik st.2.1
      (P.det.splitC st.2.2).1 (P.det.splitC st.2.2).2 y y
-- ANCHOR_END: authReduction

/-- For `0 < e` and `H := hiddenState auth e ik κ`, the simulated game over
`withHidden auth (Braid.hiddenAuth auth e ik κ u) e` from `ik₁` with the challenge key `y` accepts
as often as the simulated game over `authAt auth (e - 1) H` from `ik₂` with the challenge key `y`
and the update of `e` keyed by `u`, if `hiddenMap e H` maps the initial authenticator state of
`ik₁` to that of `ik₂`. -/
theorem prEvent_simRun_withHidden {e : ℕ} (he : 0 < e) (ik : InitKey) (κ u y : P.EpochKey)
    (d : Dummies P) (ik₁ ik₂ : InitKey) (pk : P.PK) (ct1 : P.det.C₁) (ct2 : P.det.C₂)
    (hinit : hiddenMap e (hiddenState auth e ik κ) 1 (auth.init ik₁ 1) = auth.init ik₂ 1) :
    Pr{let x ← (simRun (withHidden auth (hiddenAuth auth e ik κ u) e) sampleInitKey adv e d ik₁ pk
      ct1 ct2 y y)}[x = true] =
    Pr{let x ← (simRun (authAt auth (e - 1) (hiddenState auth e ik κ)) sampleInitKey adv e d ik₂
      pk ct1 ct2 y u)}[x = true] := by
  have hs : authMapState (hiddenMap e (hiddenState auth e ik κ))
      (initState (withHidden auth (hiddenAuth auth e ik κ u) e) ik₁) =
      initState (authAt auth (e - 1) (hiddenState auth e ik κ)) ik₂ :=
    authMapState_initState _ _ ik₁ ik₂ hinit
  unfold simRun
  rw [← hs]
  exact (prEvent_stoppedRun_authMap (simOps pk ct1 ct2 d e) sampleInitKey
    (authMap_withHidden auth he ik κ u y) e
    (fun t ht => hiddenMap_of_ne (hiddenState auth e ik κ) ht)
    (SCKAScheme.pinnedChallenge e y)
    (fun t s => pinnedChallenge_run_authMapState (π := hiddenMap e (hiddenState auth e ik κ)) e y
      t s) adv _).symm

/-- The game of the key-hiding experiment after the transport: for `0 < e`, the simulated game
over `withHidden` with the operations on `hiddenState auth e ik' κ` accepts as often as the
simulated game over `hybridAuth auth e ik₀ κ` from `ik₀ := if e = 1 then ik' else ik`. -/
private theorem prEvent_authGuess_eq {e : ℕ} (he : 0 < e) (d : Dummies P) (ik ik' : InitKey)
    (pk : P.PK) (c : P.C) (u y κ : P.EpochKey) :
    Pr{let x ← (simRun (withHidden auth (hiddenAuth auth e ik' κ u) e)
      sampleInitKey adv e d ik pk (P.det.splitC c).1 (P.det.splitC c).2 y y)}[x = true] =
    Pr{let x ← (simRun (hybridAuth auth e (if e = 1 then ik' else ik) κ) sampleInitKey adv e d
      (if e = 1 then ik' else ik) pk (P.det.splitC c).1 (P.det.splitC c).2 y u)}[x = true] := by
  by_cases he1 : e = 1
  · subst he1
    exact prEvent_simRun_withHidden auth sampleInitKey adv he ik' κ u y d ik ik' pk _ _
      (by simp [hiddenMap, hiddenState])
  · have hH : hiddenState auth e ik' κ = hiddenState auth e ik κ :=
      funext fun a => by simp [hiddenState, he1]
    simp only [he1, ↓reduceIte]
    rw [prEvent_simRun_withHidden auth sampleInitKey adv he ik' κ u y d ik ik pk _ _
      (by simp [hiddenMap, Ne.symm he1]), hH]

omit [DecidableEq P.EpochKey] in
/-- Acceptance probabilities agree under the samples of the key-hiding experiment if they agree
for all samples. -/
private theorem prEvent_authShape_congr
    (X Y : InitKey → Dummies P → P.PK → P.C → InitKey → P.EpochKey → P.EpochKey → P.EpochKey →
      ProbComp Bool)
    (h : ∀ ik d pk c ik' u u' κ, Pr{let x ← X ik d pk c ik' u u' κ}[x = true] =
      Pr{let x ← Y ik d pk c ik' u u' κ}[x = true]) :
    Pr{let x ← (do
      let ik ← sampleInitKey
      let d ← sampleDummies
      let (pk, _) ← P.det.toKEM.keygen
      let (c, _) ← P.det.toKEM.encaps pk
      let ik' ← sampleInitKey
      let u ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      let u' ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      X ik d pk c ik' u u' κ)}[x = true] =
    Pr{let x ← (do
      let ik ← sampleInitKey
      let d ← sampleDummies
      let (pk, _) ← P.det.toKEM.keygen
      let (c, _) ← P.det.toKEM.encaps pk
      let ik' ← sampleInitKey
      let u ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      let u' ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      Y ik d pk c ik' u u' κ)}[x = true] := by
  apply OracleComp.prEvent_bind_congr_of_support'; rintro ik -
  apply OracleComp.prEvent_bind_congr_of_support'; rintro d -
  apply OracleComp.prEvent_bind_congr_of_support'; rintro ⟨pk, sk⟩ -
  apply OracleComp.prEvent_bind_congr_of_support'; rintro ⟨c, k⟩ -
  apply OracleComp.prEvent_bind_congr_of_support'; rintro ik' -
  apply OracleComp.prEvent_bind_congr_of_support'; rintro u -
  apply OracleComp.prEvent_bind_congr_of_support'; rintro u' -
  apply OracleComp.prEvent_bind_congr_of_support'; rintro κ -
  exact h ik d pk c ik' u u' κ

omit [DecidableEq P.EpochKey] in
/-- A game of the key-hiding experiment that uses the initial key `ik'` drawn after the
encapsulation for `e = 1` and the initial key `ik` of the context otherwise accepts as often as
the game with the initial key of the context. -/
private theorem prEvent_initKey_select (e : ℕ)
    (F : InitKey → Dummies P → P.PK → P.C → P.EpochKey → P.EpochKey → P.EpochKey →
      ProbComp Bool) :
    Pr{let x ← (do
      let ik ← sampleInitKey
      let d ← sampleDummies
      let (pk, _) ← P.det.toKEM.keygen
      let (c, _) ← P.det.toKEM.encaps pk
      let ik' ← sampleInitKey
      let u ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      let u' ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      F (if e = 1 then ik' else ik) d pk c u u' κ)}[x = true] =
    Pr{let x ← (do
      let ik ← sampleInitKey
      let d ← sampleDummies
      let (pk, _) ← P.det.toKEM.keygen
      let (c, _) ← P.det.toKEM.encaps pk
      let u ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      let u' ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      F ik d pk c u u' κ)}[x = true] := by
  by_cases he1 : e = 1
  · simp only [he1, ↓reduceIte]
    rw [(OracleComp.EvalDistEq.bind_const _ _).prEvent_eq,
      (OracleComp.EvalDistEq.bind_bind_swap sampleInitKey sampleDummies _).prEvent_eq]
    apply OracleComp.prEvent_bind_congr_of_support'; rintro d -
    rw [(OracleComp.EvalDistEq.bind_bind_swap sampleInitKey P.det.toKEM.keygen _).prEvent_eq]
    apply OracleComp.prEvent_bind_congr_of_support'; rintro ⟨pk, sk⟩ -
    dsimp only
    rw [(OracleComp.EvalDistEq.bind_bind_swap sampleInitKey (P.det.toKEM.encaps pk)
      _).prEvent_eq]
  · simp only [he1, ↓reduceIte]
    apply OracleComp.prEvent_bind_congr_of_support'; rintro ik -
    apply OracleComp.prEvent_bind_congr_of_support'; rintro d -
    apply OracleComp.prEvent_bind_congr_of_support'; rintro ⟨pk, sk⟩ -
    apply OracleComp.prEvent_bind_congr_of_support'; rintro ⟨c, k⟩ -
    exact (OracleComp.EvalDistEq.bind_const _ _).prEvent_eq _

/-- The key-hiding experiment of `authReduction` accepts, over a sampled context, as often as
`randEpochKey` when handed the key of the hidden update (`real = true`) and as `splitKeys` when
handed an independent key. -/
theorem authReduction_prEvent_toReal (real : Bool) :
    (Pr{let y ← (Braid.authHideExp auth sampleInitKey (authReduction auth sampleInitKey adv q)
      real)}[y = true]).toReal =
    contextProb sampleInitKey q (if real then randEpochKey auth sampleInitKey adv
      else splitKeys auth sampleInitKey adv) := by
  unfold contextProb
  congr 1
  simp only [Braid.authHideExp, authReduction, sampleContext, bind_assoc, pure_bind]
  apply OracleComp.prEvent_bind_congr_of_support'; rintro e he
  have he0 := ToVCVio.pos_of_mem_support_epochChoice he
  refine (prEvent_authShape_congr sampleInitKey
    (fun ik d pk c ik' u u' κ =>
      simRun (withHidden auth (hiddenAuth auth e ik' κ u) e) sampleInitKey
        adv e d ik pk (P.det.splitC c).1 (P.det.splitC c).2 (if real then u else u')
        (if real then u else u'))
    (fun ik d pk c ik' u u' κ =>
      simRun (hybridAuth auth e (if e = 1 then ik' else ik) κ) sampleInitKey adv e d
        (if e = 1 then ik' else ik) pk (P.det.splitC c).1 (P.det.splitC c).2
        (if real then u else u') u)
    fun ik d pk c ik' u u' κ =>
      prEvent_authGuess_eq auth sampleInitKey adv he0 d ik ik' pk c u _ κ).trans ?_
  refine (prEvent_initKey_select sampleInitKey e (fun ik d pk c u u' κ =>
    simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik pk (P.det.splitC c).1
      (P.det.splitC c).2 (if real then u else u') u)).trans ?_
  cases real
  · simp only [Bool.false_eq_true, ↓reduceIte, splitKeys]
  · simp only [↓reduceIte, randEpochKey]
    apply OracleComp.prEvent_bind_congr_of_support'; rintro ik -
    apply OracleComp.prEvent_bind_congr_of_support'; rintro d -
    apply OracleComp.prEvent_bind_congr_of_support'; rintro ⟨pk, sk⟩ -
    apply OracleComp.prEvent_bind_congr_of_support'; rintro ⟨c, k⟩ -
    apply OracleComp.prEvent_bind_congr_of_support'; rintro u -
    exact (OracleComp.EvalDistEq.bind_const _ _).prEvent_eq _

/-! ### Averaging over the challenge epoch -/

section Averaging

variable [SampleableType P.K]

/-- Averaging over the challenge epoch: for `q ≠ 0`, if every `p_i - p_{i+1}` is given by
`idealExp_gap_eq`, then `p_0 - p_q = q · (4 Δ_KEM + 4 Δ_KDF + Δ_Auth)`, where
`p_i := Pr[idealExp (hybridMode i) adv = true]` and each `Δ` is the difference of the acceptance
probabilities of the experiment of a reduction with bit `true` and with bit `false`: the IND-CPA
experiment of `kemReduction`, `Braid.kdfContextExp P.kdfOK` of `kdfReduction`, and
`Braid.authHideExp auth sampleInitKey` of `authReduction`. -/
theorem hybrid_gap_eq_reductions (hq : q ≠ 0)
    (hgap : ∀ i, (Pr{let x ← (idealExp auth sampleInitKey (SCKAScheme.hybridMode i)
        adv)}[x = true]).toReal -
      (Pr{let x ← (idealExp auth sampleInitKey (SCKAScheme.hybridMode (i + 1))
          adv)}[x = true]).toReal =
      (gameProb sampleInitKey (prevReal auth sampleInitKey adv false) (i + 1) -
          gameProb sampleInitKey (prevKdf auth sampleInitKey adv false) (i + 1)) +
        (gameProb sampleInitKey (realKey auth sampleInitKey adv) (i + 1) -
          gameProb sampleInitKey (realKeyChal auth sampleInitKey adv) (i + 1)) -
        (gameProb sampleInitKey (prevReal auth sampleInitKey adv true) (i + 1) -
          gameProb sampleInitKey (prevKdf auth sampleInitKey adv true) (i + 1))) :
    (Pr{let x ← idealExp auth sampleInitKey (SCKAScheme.hybridMode 0) adv}[x = true]).toReal -
      (Pr{let x ← idealExp auth sampleInitKey (SCKAScheme.hybridMode q) adv}[x = true]).toReal =
    (q : ℝ) * (
      4 * ((Pr{let x ← (P.det.toKEM.IND_CPA_Experiment ProbCompRuntime.probComp
          (kemReduction auth sampleInitKey adv q) true)}[x = true]).toReal -
        (Pr{let x ← (P.det.toKEM.IND_CPA_Experiment ProbCompRuntime.probComp
          (kemReduction auth sampleInitKey adv q) false)}[x = true]).toReal) +
      4 * ((Pr{let x ← (Braid.kdfContextExp P.kdfOK (kdfReduction auth sampleInitKey adv q)
          true)}[x = true]).toReal -
        (Pr{let x ← (Braid.kdfContextExp P.kdfOK (kdfReduction auth sampleInitKey adv q)
          false)}[x = true]).toReal) +
      ((Pr{let x ← (Braid.authHideExp auth sampleInitKey (authReduction auth sampleInitKey adv q)
          true)}[x = true]).toReal -
        (Pr{let x ← (Braid.authHideExp auth sampleInitKey (authReduction auth sampleInitKey adv q)
          false)}[x = true]).toReal)) := by
  rw [← Finset.sum_range_sub' (fun i =>
    (Pr{let x ← idealExp auth sampleInitKey (SCKAScheme.hybridMode i) adv}[x = true]).toReal) q]
  simp only [hgap, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_gameProb_eq sampleInitKey q hq]
  rw [kemReduction_prEvent_toReal, kemReduction_prEvent_toReal, kdfReduction_prEvent_toReal,
    kdfReduction_prEvent_toReal, authReduction_prEvent_toReal, authReduction_prEvent_toReal]
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, realGame, randGame, unifGame]
  ring

end Averaging

end SPQR
