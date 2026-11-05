/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.OppBiKEM.Security.Cancellation
public import SecureMessaging.SCKA.OppBiKEM.Security.Injected
public import ToVCVio.OracleComp.QueryTracking.OneUseSampling
public import ToVCVio.EvalDist.Monad.Basic

/-!
# Opp-BiKEM — Eager sampling of the target's values

**Setting.** Fix a target epoch `t > 0` and a version `x ∈ {real, random}` (the Lean argument
`b` is `true` for `random`). The stopped hybrid `S_t^x` (`Cancellation`) draws the target's key
pair at the owner's generating send, the encapsulation at the peer's encapsulating send and, in
`random`, the uniform challenge key at the challenge of `t`. The *eager hybrid*

```text
E_t^x(pk, sk, c, k, r) := stoppedEagerExp … t b pk sk c k r adv
```

holds all three from the start: it runs `adv` against the injected oracles with injection
`⟨pk, sk, c, k⟩` (`Injected`), whose challenge of `t` answers `r` in `random` (`eagerAnswer`,
`eagerSecurityImpl`), stopped at the first exposure of `t`. The IND-CPA experiment draws the key
pair and the encapsulation, correlated, before the reduction's simulation starts; the reduction
receives `pk`, `c` and a candidate key, never `sk` (`Simulation`).

**Main result** (`prEvent_stoppedHybridExp_eq_eager`). With correct erasure codes,

```text
Pr[S_t^x = true]
  = E_{(pk, sk) ← keygen, (c, k) ← encaps pk, r ←$ K} Pr[E_t^x(pk, sk, c, k, r) = true].
```

The proof peels the three samples one at a time with the one-use sampling theorem
`optionRun_sample_once_eq_sampleEachQuery`, from the innermost draw outwards, through two
intermediate oracle families: the injected oracles with the hybrid challenge selection, and the
*keygen-injected* oracles with the injected key pair and honest encapsulation
(`keygenInjectedScheme`). Each peel supplies:

- a hit test naming the query that consumes the sample (`hitRand`, `hitEncaps`, `hitKeygen`)
  and a monotone used predicate excluding a second consumption (the challenged set,
  `usedEncaps`, `usedKeygen`);
- when the hit predicate is false, equal query computations of the sampled family for all samples
  (`…_of_not_hit…`);
- at the hit, the distribution of drawing the sample and running the sampled oracles equals that
  of the lazy oracles (`eager_hitRand_evalDist`, `injected_hitEncaps_evalDist`,
  `keygenInjected_hitKeygen_eq`): the uniform key answers the challenge, the encapsulation
  commutes with the sender's own independent key generation, and the key pair is the send's
  first effect.

The random-key and key-pair peels use `True` and `GameInv` as invariants. The encapsulation
peel uses the injected-state invariant of `Injected` through its existential closure over
supported encapsulations (`encapsInv`): at the encapsulation for the target both tables are
empty, so the witness switches to the sample (`injInv_switch_key`); elsewhere the sample is not
read. `IdealReceive` supplies the shared oracle families and state-preservation lemmas;
`Injected` supplies the facts about changing the injected encapsulation. The stopped-simulation
support lemmas (`stopOnState_run_run_eq`, `mem_support_stopOnState`,
`exists_of_mem_support_stopOnState`) come from `ToVCVio.OracleComp.SimSemantics.StateT.Stop`, and
the per-query sampling bridge `evalDistEq_sampleEachQuery_stopOnState` from
`ToVCVio.OracleComp.QueryTracking.OneUseSampling`.
-/

@[expose] public section

open OracleSpec OracleComp KEMScheme SCKAScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-! ## The intermediate oracle families -/

section Families

variable (kem : KEMScheme ProbComp K PK SK C)

/-- Key generation that returns `(pk, sk)` at the generation of the target's key pair and is
honest otherwise; `injectedKeygen` is this at the injection's pair. -/
def targetKeygen (role : Role) (t : ℕ) (pk : PK) (sk : SK) (st : State PK SK C Sym) :
    ProbComp ((PK × SK) × Unit) :=
  if sendGeneratesTarget role t st then pure ((pk, sk), ())
  else do let keys ← kem.keygen; pure (keys, ())

/-- The honest encapsulation sampler of `send`. -/
def honestEncaps : PK → ProbComp ((C × K) × Unit) :=
  fun pk => do let out ← kem.encaps pk; pure (out, ())

/-- `injectedKeygen` is `targetKeygen` at the injected pair. -/
lemma injectedKeygen_eq_targetKeygen (role : Role) (t : ℕ) (inj : TargetInjection PK SK C K)
    (st : State PK SK C Sym) :
    injectedKeygen kem role t inj st = targetKeygen kem role t inj.pk inj.sk st := rfl

/-- The ordinary send with the target's key generation replaced by `(pk, sk)` and honest
encapsulation. -/
def keygenInjectedSend (role : Role) (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym) (t : ℕ) (pk : PK) (sk : SK) (st : State PK SK C Sym) :
    ProbComp (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym)) := do
  let out ← sendWith role (targetKeygen kem role t pk sk st) (honestEncaps kem) ecEk ecCt st
  pure (out.map fun (key?, ρ, epoch, st', _) => (key?, ρ, epoch, st'))

/-- If `sendEncapsulatesTarget role t st = false`, the injected send is the keygen-injected
send. -/
lemma injectedSend_eq_keygenInjectedSend (role : Role) (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym) (t : ℕ) (inj : TargetInjection PK SK C K)
    (st : State PK SK C Sym) (henc : sendEncapsulatesTarget role t st = false) :
    injectedSend kem role ecEk ecCt t inj st =
      keygenInjectedSend kem role ecEk ecCt t inj.pk inj.sk st := by
  have henc' : injectedEncaps kem role t inj st = honestEncaps kem := by
    funext pk
    simp only [injectedEncaps, henc, Bool.false_eq_true, ↓reduceIte, honestEncaps]
  simp only [injectedSend, keygenInjectedSend, injectedKeygen_eq_targetKeygen, henc']

/-- If `sendGeneratesTarget role t st = false`, the keygen-injected send is the honest send. -/
lemma keygenInjectedSend_eq_send (role : Role) (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym) (t : ℕ) (pk : PK) (sk : SK) (st : State PK SK C Sym)
    (hgen : sendGeneratesTarget role t st = false) :
    keygenInjectedSend kem role ecEk ecCt t pk sk st = send role kem ecEk ecCt st := by
  simp only [keygenInjectedSend, targetKeygen, hgen, Bool.false_eq_true, ↓reduceIte, send]
  rfl

/-- At an encapsulation for the target, the injected encapsulation is the constant injected
value. -/
lemma injectedEncaps_eq_of_target (role : Role) (t : ℕ) (inj : TargetInjection PK SK C K)
    (st : State PK SK C Sym) (henc : sendEncapsulatesTarget role t st = true) :
    injectedEncaps kem role t inj st = fun _ => pure ((inj.ct, inj.key), ()) := by
  funext pk
  simp only [injectedEncaps, henc, ↓reduceIte]

variable [DecidableEq K] [DecidableEq Sym]
  (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)

/-- The Opp-BiKEM scheme with both ordinary sends keygen-injected at target `t`. -/
def keygenInjectedScheme (t : ℕ) (pk : PK) (sk : SK) :
    SCKAScheme ProbComp Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) :=
  { scheme kem hDet ecEk ecCt leak with
      sendA := keygenInjectedSend kem .A ecEk ecCt t pk sk
      sendB := keygenInjectedSend kem .B ecEk ecCt t pk sk }

variable [SampleableType K]

/-- The eager challenge answer for target `t`: random below `t`, the eager random key at `t`
when `b` is set, and the recorded key otherwise. -/
def eagerAnswer (t : ℕ) (b : Bool) (kRand : K) : ℕ → K → ProbComp K :=
  fun e k => if e < t then ($ᵗ K : ProbComp K) else if b && decide (e = t) then pure kRand
    else pure k

/-- The eager security oracles: the injected oracles with the challenge of the target answered
by the eagerly drawn `kRand` when `b` is set. -/
def eagerSecurityImpl (t : ℕ) (inj : TargetInjection PK SK C K) (b : Bool) (kRand : K) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
        ProbComp) :=
  SCKAScheme.securityImplOf (injectedCorrectnessImpl kem hDet ecEk ecCt leak t inj)
    (SCKAScheme.oracleChallWith (eagerAnswer t b kRand) _ _ _) (exposure .A leak)
    (exposure .B leak) (scheme kem hDet ecEk ecCt leak)

/-- The eager hybrid experiment for target `t` and bit `b` with all of the target's values drawn
in advance, stopped once `t` is exposed. -/
def stoppedEagerExp (t : ℕ) (b : Bool) (pk : PK) (sk : SK) (c : C) (kReal kRand : K)
    (adv : SecurityAdversary leak Sym) : ProbComp Bool :=
  stoppedRun (eagerSecurityImpl kem hDet ecEk ecCt leak t ⟨pk, sk, c, kReal⟩ b kRand)
    (targetExposed t) adv (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))

end Families

/-! ## Hit predicates -/

section Hits

variable {kem : KEMScheme ProbComp K PK SK C} {leak : kem.RandLeak}

/-- The query that first uses the eager random key: an eligible challenge of `t` with `b`
set. -/
def hitRand (t : ℕ) (b : Bool) :
    (securitySpec leak Sym).Domain →
      SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) → Bool
  | sckaSecuritySpec.OChall e, s =>
      b && decide (e = t) && !decide (t ∈ s.exposed ∨ t ∈ s.challenged) &&
        ((s.keyA t).isSome || (s.keyB t).isSome)
  | _, _ => false

/-- The query that first uses the target's encapsulation: an ordinary send that encapsulates
for `t`. -/
def hitEncaps (t : ℕ) :
    (securitySpec leak Sym).Domain →
      SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) → Bool
  | sckaSecuritySpec.OCorrectness sckaCorrectnessSpec.OSendA, s =>
      sendEncapsulatesTarget .A t s.stA
  | sckaSecuritySpec.OCorrectness sckaCorrectnessSpec.OSendB, s =>
      sendEncapsulatesTarget .B t s.stB
  | _, _ => false

/-- The query that first uses the target's key pair: an ordinary send that generates it. -/
def hitKeygen (t : ℕ) :
    (securitySpec leak Sym).Domain →
      SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) → Bool
  | sckaSecuritySpec.OCorrectness sckaCorrectnessSpec.OSendA, s =>
      sendGeneratesTarget .A t s.stA
  | sckaSecuritySpec.OCorrectness sckaCorrectnessSpec.OSendB, s =>
      sendGeneratesTarget .B t s.stB
  | _, _ => false

end Hits

/-! ## Query computations when the hit predicate is false -/

section HitFalse

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
  (t : ℕ)

/-- If `hitEncaps t q s = false`, the injected query computation is independent of the
injected encapsulation. -/
lemma injectedSecurityImpl_run_eq_of_not_hitEncaps (pk : PK) (sk : SK) (y y' : C × K)
    (random : ℕ → Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (q : (securitySpec leak Sym).Domain) (hq : hitEncaps (leak := leak) t q s = false) :
    (injectedSecurityImpl kem hDet ecEk ecCt leak t ⟨pk, sk, y.1, y.2⟩ random q).run s =
      (injectedSecurityImpl kem hDet ecEk ecCt leak t ⟨pk, sk, y'.1, y'.2⟩ random q).run s := by
  rw [injectedSecurityImpl_eq, injectedSecurityImpl_eq]
  refine idealRecvSecurityImpl_run_eq kem hDet ecEk ecCt leak _ _ random s q ?_ ?_
  · rintro rfl
    change injectedSend kem .A ecEk ecCt t _ s.stA = injectedSend kem .A ecEk ecCt t _ s.stA
    rw [injectedSend_eq_keygenInjectedSend kem .A ecEk ecCt t _ s.stA hq,
      injectedSend_eq_keygenInjectedSend kem .A ecEk ecCt t _ s.stA hq]
  · rintro rfl
    change injectedSend kem .B ecEk ecCt t _ s.stB = injectedSend kem .B ecEk ecCt t _ s.stB
    rw [injectedSend_eq_keygenInjectedSend kem .B ecEk ecCt t _ s.stB hq,
      injectedSend_eq_keygenInjectedSend kem .B ecEk ecCt t _ s.stB hq]

/-- If `hitEncaps t q s = false`, the injected and keygen-injected oracles give the same
query computation from `s`. -/
lemma injectedSecurityImpl_run_eq_keygenInjected_of_not_hitEncaps (pk : PK) (sk : SK)
    (y : C × K) (random : ℕ → Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (q : (securitySpec leak Sym).Domain) (hq : hitEncaps (leak := leak) t q s = false) :
    (injectedSecurityImpl kem hDet ecEk ecCt leak t ⟨pk, sk, y.1, y.2⟩ random q).run s =
      (idealRecvSecurityImpl kem hDet ecEk ecCt leak
        (keygenInjectedScheme kem hDet ecEk ecCt leak t pk sk) random q).run s := by
  rw [injectedSecurityImpl_eq]
  refine idealRecvSecurityImpl_run_eq kem hDet ecEk ecCt leak _ _ random s q ?_ ?_
  · rintro rfl
    exact injectedSend_eq_keygenInjectedSend kem .A ecEk ecCt t _ s.stA hq
  · rintro rfl
    exact injectedSend_eq_keygenInjectedSend kem .B ecEk ecCt t _ s.stB hq

/-- If `hitKeygen t q s = false`, the keygen-injected query computation is independent of the
injected key pair. -/
lemma keygenInjected_run_eq_of_not_hitKeygen (x x' : PK × SK) (random : ℕ → Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (q : (securitySpec leak Sym).Domain) (hq : hitKeygen (leak := leak) t q s = false) :
    (idealRecvSecurityImpl kem hDet ecEk ecCt leak
        (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) random q).run s =
      (idealRecvSecurityImpl kem hDet ecEk ecCt leak
        (keygenInjectedScheme kem hDet ecEk ecCt leak t x'.1 x'.2) random q).run s := by
  refine idealRecvSecurityImpl_run_eq kem hDet ecEk ecCt leak _ _ random s q ?_ ?_
  · rintro rfl
    change keygenInjectedSend kem .A ecEk ecCt t _ _ s.stA =
      keygenInjectedSend kem .A ecEk ecCt t _ _ s.stA
    rw [keygenInjectedSend_eq_send kem .A ecEk ecCt t _ _ s.stA hq,
      keygenInjectedSend_eq_send kem .A ecEk ecCt t _ _ s.stA hq]
  · rintro rfl
    change keygenInjectedSend kem .B ecEk ecCt t _ _ s.stB =
      keygenInjectedSend kem .B ecEk ecCt t _ _ s.stB
    rw [keygenInjectedSend_eq_send kem .B ecEk ecCt t _ _ s.stB hq,
      keygenInjectedSend_eq_send kem .B ecEk ecCt t _ _ s.stB hq]

/-- If `hitKeygen t q s = false`, the keygen-injected and hybrid oracles give the same query
computation from `s`. -/
lemma keygenInjected_run_eq_hybrid_of_not_hitKeygen (x : PK × SK) (random : ℕ → Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (q : (securitySpec leak Sym).Domain) (hq : hitKeygen (leak := leak) t q s = false) :
    (idealRecvSecurityImpl kem hDet ecEk ecCt leak
        (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) random q).run s =
      (hybridSecurityImpl kem hDet ecEk ecCt leak random q).run s := by
  rw [hybridSecurityImpl_eq]
  refine idealRecvSecurityImpl_run_eq kem hDet ecEk ecCt leak _ _ random s q ?_ ?_
  · rintro rfl
    exact keygenInjectedSend_eq_send kem .A ecEk ecCt t _ _ s.stA hq
  · rintro rfl
    exact keygenInjectedSend_eq_send kem .B ecEk ecCt t _ _ s.stB hq

/-- If `hitRand t b q s = false`, the eager query computation is independent of the eager
random key. -/
lemma eagerSecurityImpl_run_eq_of_not_hitRand (inj : TargetInjection PK SK C K) (b : Bool)
    (r r' : K) (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (q : (securitySpec leak Sym).Domain) (hq : hitRand (leak := leak) t b q s = false) :
    (eagerSecurityImpl kem hDet ecEk ecCt leak t inj b r q).run s =
      (eagerSecurityImpl kem hDet ecEk ecCt leak t inj b r' q).run s := by
  rcases q with (((((q | u) | u) | e) | u) | u) <;> (try rfl)
  change (SCKAScheme.oracleChallWith (eagerAnswer t b r) _ _ _ e).run s =
    (SCKAScheme.oracleChallWith (eagerAnswer t b r') _ _ _ e).run s
  refine SCKAScheme.oracleChallWith_run_eq_of_eligible_imp _ _ s e (fun hrej hkey k => ?_)
  rcases eq_or_ne e t with rfl | hne
  · have hb : b = false := by
      cases b with
      | false => rfl
      | true =>
        exfalso
        simp [hitRand, hrej] at hq
        rcases hkey with h | h <;> simp_all
    simp [eagerAnswer, hb]
  · simp [eagerAnswer, hne]

/-- If `hitRand t b q s = false`, the eager and injected oracles give the same query
computation from `s`, with the hybrid selection of threshold `t + b`. -/
lemma eagerSecurityImpl_run_eq_injected_of_not_hitRand (inj : TargetInjection PK SK C K)
    (b : Bool) (r : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (q : (securitySpec leak Sym).Domain) (hq : hitRand (leak := leak) t b q s = false) :
    (eagerSecurityImpl kem hDet ecEk ecCt leak t inj b r q).run s =
      (injectedSecurityImpl kem hDet ecEk ecCt leak t inj (hybridRandom (t + b.toNat))
        q).run s := by
  rcases q with (((((q | u) | u) | e) | u) | u) <;> (try rfl)
  change (SCKAScheme.oracleChallWith (eagerAnswer t b r) _ _ _ e).run s =
    (SCKAScheme.oracleChallOn (hybridRandom (t + b.toNat)) _ _ _ _ e).run s
  rw [SCKAScheme.oracleChallOn_run_eq_oracleChallWith]
  refine SCKAScheme.oracleChallWith_run_eq_of_eligible_imp _ _ s e (fun hrej hkey k => ?_)
  rcases eq_or_ne e t with rfl | hne
  · have hb : b = false := by
      cases b with
      | false => rfl
      | true =>
        exfalso
        simp [hitRand, hrej] at hq
        rcases hkey with h | h <;> simp_all
    simp [eagerAnswer, hybridRandom, hb]
  · cases b with
    | false => simp [eagerAnswer, hybridRandom]
    | true =>
      have hlt : e < t + 1 ↔ e < t := by omega
      simp [eagerAnswer, hybridRandom, hne, hlt]

end HitFalse

/-! ## Query computations at the hits -/

section AtHits

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
  (t : ℕ)

/-- At an eligible challenge of the target, drawing the eager random key and answering with it
is answering with a fresh random key. -/
lemma eager_hitRand_evalDist (inj : TargetInjection PK SK C K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (helig : ¬(t ∈ s.exposed ∨ t ∈ s.challenged))
    (hkey : (s.keyA t).isSome = true ∨ (s.keyB t).isSome = true) :
    (($ᵗ K : ProbComp K) >>= fun r =>
        (eagerSecurityImpl kem hDet ecEk ecCt leak t inj true r
          (sckaSecuritySpec.OChall t)).run s) =ᵈ
      (injectedSecurityImpl kem hDet ecEk ecCt leak t inj (hybridRandom (t + 1))
        (sckaSecuritySpec.OChall t)).run s := by
  refine ToVCVio.evalDistEq_of_eq ?_
  change (($ᵗ K : ProbComp K) >>= fun r =>
      (SCKAScheme.oracleChallWith (eagerAnswer t true r) _ _ _ t).run s) =
    (SCKAScheme.oracleChallOn (hybridRandom (t + 1)) _ _ _ _ t).run s
  rw [SCKAScheme.oracleChallOn_run_eq_oracleChallWith,
    SCKAScheme.oracleChallWith_bind_eq_of_eligible ($ᵗ K) (fun r => eagerAnswer t true r) id s t
      helig hkey (fun r k => by simp [eagerAnswer])]
  exact SCKAScheme.oracleChallWith_run_eq_of_eligible_imp _ _ s t
    (fun _ _ k => by simp [hybridRandom])

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] hDet leak in
/-- At a generation of the target's key pair, drawing the pair and running the keygen-injected
send is the honest send: key generation is the send's first effect. -/
lemma keygenInjectedSend_hit_eq (role : Role) (st : State PK SK C Sym)
    (hgen : sendGeneratesTarget role t st = true) :
    (kem.keygen >>= fun x => keygenInjectedSend kem role ecEk ecCt t x.1 x.2 st) =
      send role kem ecEk ecCt st := by
  have hg : sendKeygenGuard role st = true := by
    simp only [sendGeneratesTarget, Bool.and_eq_true] at hgen
    exact hgen.1
  have hc : (st.req.ek.isNone && decide (st.res.resEpoch ∈ st.ack.ctRec ∧
      st.res.resEpoch + role.offset ∈ st.ack.ctRec)) = true := hg
  simp only [keygenInjectedSend, targetKeygen, hgen, ↓reduceIte, send]
  unfold sendWith
  dsimp only
  simp only [hc, ↓reduceIte, honestEncaps, bind_assoc, pure_bind]

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] hDet leak in
/-- At an encapsulation for the target, drawing the encapsulation to the decoded peer key and
running the send with it is the send with honest encapsulation; the send's own key generation,
if any, is an independent draw. -/
lemma sendWith_hitEncaps_evalDist {RK : Type} (role : Role) (keygen : ProbComp ((PK × SK) × RK))
    (st : State PK SK C Sym) (pk : PK) (hg : sendEncapsGuard role st = true)
    (hpk : ∀ pk', st.res.ekPeer (st.res.resEpoch + if sendKeygenGuard role st then 2 else 0) =
      some pk' → pk' = pk) :
    (kem.encaps pk >>= fun y => sendWith role keygen (fun _ => pure (y, ())) ecEk ecCt st) =ᵈ
      sendWith role keygen (honestEncaps kem) ecEk ecCt st := by
  rw [sendEncapsGuard_eq_true_iff] at hg
  obtain ⟨h1, h2, h3, h4⟩ := hg
  by_cases hk : sendKeygenGuard role st = true
  · simp only [hk, ite_true] at h1 h2 h4 hpk
    obtain ⟨⟨reqEpoch, dk, ek, chunks⟩, ⟨resEpoch, ekPeer, ct, ich⟩, ack⟩ := st
    dsimp only at h1 h2 h3 h4 hpk
    subst h3
    have hc : (ek.isNone && decide (resEpoch ∈ ack.ctRec ∧ resEpoch + role.offset ∈ ack.ctRec)) =
        true := hk
    unfold sendWith
    dsimp only
    simp only [hc, ↓reduceIte]
    simp only [h1, not_true_eq_false, h2, not_false_eq_true, h4, decide_true, Option.isNone_none,
      Bool.and_self, ↓reduceIte]
    generalize hpeer : ekPeer (resEpoch + 2) = o
    cases o with
    | none =>
      dsimp only
      exact OracleComp.EvalDistEq.bind_const _ _
    | some peerEk =>
      obtain rfl := hpk peerEk hpeer
      dsimp only
      simp only [honestEncaps, bind_assoc, pure_bind]
      exact EvalDistEq.bind_bind_swap _ _ _
  · have hk' : sendKeygenGuard role st = false := Bool.eq_false_iff.mpr hk
    simp only [hk', Bool.false_eq_true, ite_false, add_zero] at h1 h2 h4 hpk
    obtain ⟨⟨reqEpoch, dk, ek, chunks⟩, ⟨resEpoch, ekPeer, ct, ich⟩, ack⟩ := st
    dsimp only at h1 h2 h3 h4 hpk
    subst h3
    have hc : (ek.isNone && decide (resEpoch ∈ ack.ctRec ∧ resEpoch + role.offset ∈ ack.ctRec)) =
        false := hk'
    unfold sendWith
    dsimp only
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    simp only [h1, not_true_eq_false, h2, not_false_eq_true, h4, decide_true, Option.isNone_none,
      Bool.and_self, ↓reduceIte]
    generalize hpeer : ekPeer resEpoch = o
    cases o with
    | none =>
      dsimp only
      exact OracleComp.EvalDistEq.bind_const _ _
    | some peerEk =>
      obtain rfl := hpk peerEk hpeer
      dsimp only
      simp only [honestEncaps, bind_assoc, pure_bind]
      try rfl

/-- At a generation of the target's key pair, drawing the pair and running the keygen-injected
oracles is running the hybrid oracles. -/
lemma keygenInjected_hitKeygen_eq (random : ℕ → Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (q : (securitySpec leak Sym).Domain) (hq : hitKeygen (leak := leak) t q s = true) :
    (kem.keygen >>= fun x => (idealRecvSecurityImpl kem hDet ecEk ecCt leak
        (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) random q).run s) =
      (hybridSecurityImpl kem hDet ecEk ecCt leak random q).run s := by
  rw [hybridSecurityImpl_eq]
  rcases q with (((((((((n | u) | u) | n) | n) | u) | u) | e) | u) | u) <;> (try cases hq)
  · simp only [idealRecvSecurityImpl_run_OSendA, SCKAScheme.oracleSendA_run_eq,
      map_eq_bind_pure_comp]
    rw [← bind_assoc]
    change (kem.keygen >>= fun x => keygenInjectedSend kem .A ecEk ecCt t x.1 x.2 s.stA) >>= _ =
      send .A kem ecEk ecCt s.stA >>= _
    rw [keygenInjectedSend_hit_eq kem ecEk ecCt t .A s.stA hq]
  · simp only [idealRecvSecurityImpl_run_OSendB, SCKAScheme.oracleSendB_run_eq,
      map_eq_bind_pure_comp]
    rw [← bind_assoc]
    change (kem.keygen >>= fun x => keygenInjectedSend kem .B ecEk ecCt t x.1 x.2 s.stB) >>= _ =
      send .B kem ecEk ecCt s.stB >>= _
    rw [keygenInjectedSend_hit_eq kem ecEk ecCt t .B s.stB hq]

/-- At an encapsulation for the target, drawing the encapsulation to the injected public key
and running the injected oracles has the distribution of the keygen-injected oracles, provided
the sender's decoded key for the target is the injected public key. -/
lemma injected_hitEncaps_evalDist (x : PK × SK) (random : ℕ → Bool)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (q : (securitySpec leak Sym).Domain) (hq : hitEncaps (leak := leak) t q s = true)
    (hpkA : sendEncapsulatesTarget .A t s.stA = true →
      ∀ pk', s.stA.res.ekPeer t = some pk' → pk' = x.1)
    (hpkB : sendEncapsulatesTarget .B t s.stB = true →
      ∀ pk', s.stB.res.ekPeer t = some pk' → pk' = x.1) :
    (kem.encaps x.1 >>= fun y =>
        (injectedSecurityImpl kem hDet ecEk ecCt leak t ⟨x.1, x.2, y.1, y.2⟩ random q).run s) =ᵈ
      (idealRecvSecurityImpl kem hDet ecEk ecCt leak
        (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) random q).run s := by
  rcases q with (((((((((n | u) | u) | n) | n) | u) | u) | e) | u) | u) <;>
    simp only [hitEncaps, Bool.false_eq_true] at hq
  · have hpkA := hpkA hq
    have hcore : (kem.encaps x.1 >>= fun y =>
        injectedSend kem .A ecEk ecCt t ⟨x.1, x.2, y.1, y.2⟩ s.stA) =ᵈ
        keygenInjectedSend kem .A ecEk ecCt t x.1 x.2 s.stA := by
      simp only [injectedSend, keygenInjectedSend, injectedKeygen_eq_targetKeygen,
        injectedEncaps_eq_of_target kem .A t _ s.stA hq]
      rw [← bind_assoc]
      refine EvalDistEq.bind_left (sendWith_hitEncaps_evalDist kem ecEk ecCt .A _ s.stA x.1
        ?_ ?_) _
      · simp only [sendEncapsulatesTarget, Bool.and_eq_true] at hq
        exact hq.1
      · simp only [sendEncapsulatesTarget, Bool.and_eq_true, decide_eq_true_eq] at hq
        rw [hq.2]
        exact hpkA
    simp only [injectedSecurityImpl_eq, idealRecvSecurityImpl_run_OSendA,
      SCKAScheme.oracleSendA_run_eq, map_eq_bind_pure_comp]
    rw [← bind_assoc]
    exact hcore.bind_left _
  · have hpkB := hpkB hq
    have hcore : (kem.encaps x.1 >>= fun y =>
        injectedSend kem .B ecEk ecCt t ⟨x.1, x.2, y.1, y.2⟩ s.stB) =ᵈ
        keygenInjectedSend kem .B ecEk ecCt t x.1 x.2 s.stB := by
      simp only [injectedSend, keygenInjectedSend, injectedKeygen_eq_targetKeygen,
        injectedEncaps_eq_of_target kem .B t _ s.stB hq]
      rw [← bind_assoc]
      refine EvalDistEq.bind_left (sendWith_hitEncaps_evalDist kem ecEk ecCt .B _ s.stB x.1
        ?_ ?_) _
      · simp only [sendEncapsulatesTarget, Bool.and_eq_true] at hq
        exact hq.1
      · simp only [sendEncapsulatesTarget, Bool.and_eq_true, decide_eq_true_eq] at hq
        rw [hq.2]
        exact hpkB
    simp only [injectedSecurityImpl_eq, idealRecvSecurityImpl_run_OSendB,
      SCKAScheme.oracleSendB_run_eq, map_eq_bind_pure_comp]
    rw [← bind_assoc]
    exact hcore.bind_left _

end AtHits

/-! ## The keygen-injected sends within the honest sends -/

section KeygenSubset

variable (kem : KEMScheme ProbComp K PK SK C)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (t : ℕ)

/-- For a supported pair, the keygen-injected send's outputs are outputs of the honest send. -/
lemma keygenInjectedSend_support_subset (role : Role) (x : PK × SK)
    (hx : x ∈ support kem.keygen) (st : State PK SK C Sym) :
    support (keygenInjectedSend kem role ecEk ecCt t x.1 x.2 st) ⊆
      support (send role kem ecEk ecCt st) := by
  unfold keygenInjectedSend send
  refine support_bind_mono _ _ _ _
    (sendWith_support_mono role _ _ _ _ ecEk ecCt st ?_ (fun _ _ => subset_rfl))
    fun _ _ => subset_rfl
  intro y hy
  unfold targetKeygen at hy
  split_ifs at hy with h
  · simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rw [mem_support_bind_iff]
    exact ⟨x, hx, by simp⟩
  · exact hy

end KeygenSubset

/-! ## Peel 1: the eager random key -/

section PeelRand

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
  (t : ℕ)

/-- Every eager security query grows the challenged set. -/
lemma eagerSecurityImpl_challenged_subset (inj : TargetInjection PK SK C K) (b : Bool) (r : K)
    (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z) (hz : z ∈ support ((eagerSecurityImpl kem hDet ecEk ecCt leak t inj b r q).run s)) :
    s.challenged ⊆ z.2.challenged := by
  refine (SCKAScheme.securityImplOf_bookkeeping _ _ _ _ _ s
    (fun q z hz => injectedCorrectnessImpl_bookkeeping kem hDet ecEk ecCt leak t inj q s z hz)
    (fun e z hz => ?_) q z hz).2.1
  rcases SCKAScheme.oracleChallWith_support _ s e z hz with ⟨h, -⟩ | ⟨-, -, h⟩
  · rw [h]; exact ⟨rfl, le_rfl⟩
  · rw [h]; exact ⟨rfl, Finset.subset_insert _ _⟩

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] in
/-- Once `t` is challenged, no query is an eligible challenge of `t`. -/
lemma hitRand_eq_false_of_challenged (b : Bool) (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hu : t ∈ s.challenged) : hitRand (leak := leak) t b q s = false := by
  rcases q with (((((q | u) | u) | e) | u) | u) <;> simp [hitRand, hu]

/-- Drawing the eager random key first and running the stopped eager oracles has the acceptance
probability of the stopped injected oracles with the hybrid selection of threshold `t + b`. -/
lemma prEvent_stopped_eager_eq_injected (inj : TargetInjection PK SK C K) (b : Bool)
    (adv : SecurityAdversary leak Sym)
    (s₀ : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    Pr{let x ← ($ᵗ K : ProbComp K) >>= fun r =>
        stoppedRun (eagerSecurityImpl kem hDet ecEk ecCt leak t inj b r) (targetExposed t) adv
          s₀}[x = true] =
      Pr{let x ← stoppedRun (injectedSecurityImpl kem hDet ecEk ecCt leak t inj
           (hybridRandom (t + b.toNat))) (targetExposed t) adv s₀}[x = true] := by
  unfold stoppedRun
  rw [map_bind, optionRun_sample_once_eq_sampleEachQuery ($ᵗ K : ProbComp K)
    (fun r => stopOnState (eagerSecurityImpl kem hDet ecEk ecCt leak t inj b r) (targetExposed t))
    (fun _ => True) (fun s => t ∈ s.challenged) (hitRand t b)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun r _ q s _ hu z hz _ => by
      obtain ⟨w, hw, rfl⟩ := (mem_support_stopOnState _ _ q s z).1 hz
      exact eagerSecurityImpl_challenged_subset kem hDet ecEk ecCt leak t inj b r q s w hw hu)
    (fun q s _ hh r _ r' _ => by
      rw [stopOnState_run_run_eq _ _ _ q s
        (eagerSecurityImpl_run_eq_of_not_hitRand kem hDet ecEk ecCt leak t inj b r r' s q hh)])
    (fun q s _ hu => hitRand_eq_false_of_challenged kem leak t b q s hu)
    (fun r _ q s _ hh z hz _ => by
      obtain ⟨w, hw, rfl⟩ := (mem_support_stopOnState _ _ q s z).1 hz
      rcases q with (((((q | u) | u) | e) | u) | u) <;>
        simp only [hitRand, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true', decide_eq_false_iff_not] at hh
      obtain ⟨⟨⟨-, rfl⟩, hrej⟩, hkey⟩ := hh
      rcases SCKAScheme.oracleChallWith_support (eagerAnswer e b r) s e w hw with
        ⟨-, h⟩ | ⟨-, -, h⟩
      · rcases h with h | ⟨hA, hB⟩
        · exact absurd h hrej
        · simp [hA, hB] at hkey
      · rw [h]
        exact Finset.mem_insert_self _ _)
    adv s₀ trivial]
  refine (prEvent_optionRun_eq_of_state_map _ _ id (fun _ => True)
    (fun _ _ _ _ _ _ => trivial) (fun q s _ => ?_) adv s₀ trivial).symm
  simp only [id, Prod.map_id, id_map]
  refine EvalDistEq.symm ?_
  refine evalDistEq_sampleEachQuery_stopOnState ($ᵗ K : ProbComp K) _ _ (targetExposed t) q s ?_
  cases hh : hitRand (leak := leak) t b q s with
  | false =>
    have heq : ∀ r, (eagerSecurityImpl kem hDet ecEk ecCt leak t inj b r q).run s =
        (injectedSecurityImpl kem hDet ecEk ecCt leak t inj (hybridRandom (t + b.toNat))
          q).run s :=
      fun r => eagerSecurityImpl_run_eq_injected_of_not_hitRand kem hDet ecEk ecCt leak t inj b
        r s q hh
    simp only [heq]
    exact OracleComp.EvalDistEq.bind_const _ _
  | true =>
    rcases q with (((((q | u) | u) | e) | u) | u) <;>
      simp only [hitRand, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true', decide_eq_false_iff_not, Bool.or_eq_true] at hh
    obtain ⟨⟨⟨rfl, rfl⟩, hrej⟩, hkey⟩ := hh
    exact eager_hitRand_evalDist kem hDet ecEk ecCt leak e inj s hrej hkey

end PeelRand

/-! ## Peels 2 and 3: the encapsulation and the key pair -/

section PeelSamples

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
  (t : ℕ)

/-- The target's encapsulation has been used: its owner's peer has encapsulated for `t`. -/
def usedEncaps (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    Prop :=
  match targetOwner t with
  | .A => targetEncapsulated t s.stB
  | .B => targetEncapsulated t s.stA

/-- The target's key pair has been used: its owner has generated it. -/
def usedKeygen (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    Prop :=
  match targetOwner t with
  | .A => targetGenerated .A t s.stA
  | .B => targetGenerated .B t s.stB

/-- The invariant across the encapsulation sample: `InjInv` for the fixed key pair and some
supported encapsulation. -/
def encapsInv (x : PK × SK)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  ∃ y, y ∈ support (kem.encaps x.1) ∧ InjInv kem ecEk ecCt t ⟨x.1, x.2, y.1, y.2⟩ s

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] hDet leak in
/-- A successful keygen-injected send is a successful `sendWith` with its samplers. -/
lemma exists_rand_of_mem_keygenInjectedSend (role : Role) (pk : PK) (sk : SK)
    (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈
      support (keygenInjectedSend kem role ecEk ecCt t pk sk st)) :
    ∃ rand : SendRand Unit Unit, some (key?, ρ, tsnd, st', rand) ∈
      support (sendWith role (targetKeygen kem role t pk sk st) (honestEncaps kem) ecEk ecCt
        st) := by
  rw [keygenInjectedSend, mem_support_bind_iff] at hout
  obtain ⟨out, hmem, hpure⟩ := hout
  cases out with
  | none => simp at hpure
  | some out =>
    rcases out with ⟨key, msg, epoch, state, rand⟩
    simp only [support_pure, Set.mem_singleton_iff, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hpure
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpure
    exact ⟨rand, hmem⟩

/-! ### Peel 2: the encapsulation -/

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] hDet in
/-- At an encapsulation for the target on an `InjInv` state, both tables are empty at the
target. -/
lemma tables_empty_of_hitEncaps (ht : 0 < t) (inj : TargetInjection PK SK C K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) (q : (securitySpec leak Sym).Domain)
    (hq : hitEncaps (leak := leak) t q s = true) : s.keyA t = none ∧ s.keyB t = none := by
  obtain ⟨-, T, hA, hB⟩ := hs.1
  have htpar := targetOwner_parity t
  rcases q with (((((((((n | u) | u) | n) | n) | u) | u) | e) | u) | u) <;>
    simp only [hitEncaps, Bool.false_eq_true] at hq
  · cases ho : targetOwner t
    · rw [ho] at htpar
      rw [sendEncapsulatesTarget_eq_false_of_parity .A t s.stA htpar hA.res_parity] at hq
      cases hq
    · rw [ho] at htpar
      exact (tables_empty_of_encapsulates hB hA ht htpar hq).symm
  · cases ho : targetOwner t
    · rw [ho] at htpar
      exact tables_empty_of_encapsulates hA hB ht htpar hq
    · rw [ho] at htpar
      rw [sendEncapsulatesTarget_eq_false_of_parity .B t s.stB htpar hB.res_parity] at hq
      cases hq

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] hDet in
/-- Once the target is encapsulated for, no query encapsulates for it. -/
lemma hitEncaps_eq_false_of_used
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hu : usedEncaps t s) (q : (securitySpec leak Sym).Domain) :
    hitEncaps (leak := leak) t q s = false := by
  obtain ⟨-, T, hA, hB⟩ := hs
  have htpar := targetOwner_parity t
  rcases q with (((((((((n | u) | u) | n) | n) | u) | u) | e) | u) | u) <;> (try rfl)
  · change sendEncapsulatesTarget .A t s.stA = false
    cases ho : targetOwner t
    · rw [ho] at htpar
      exact sendEncapsulatesTarget_eq_false_of_parity .A t s.stA htpar hA.res_parity
    · simp only [usedEncaps, ho] at hu
      exact sendEncapsulatesTarget_eq_false_of_encapsulated .A t s.stA hu
  · change sendEncapsulatesTarget .B t s.stB = false
    cases ho : targetOwner t
    · simp only [usedEncaps, ho] at hu
      exact sendEncapsulatesTarget_eq_false_of_encapsulated .B t s.stB hu
    · rw [ho] at htpar
      exact sendEncapsulatesTarget_eq_false_of_parity .B t s.stB htpar hB.res_parity

/-- Every injected query keeps the target encapsulated for. -/
lemma usedEncaps_step (inj : TargetInjection PK SK C K) (random : ℕ → Bool)
    (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hu : usedEncaps t s) :
    ∀ z ∈ support ((injectedSecurityImpl kem hDet ecEk ecCt leak t inj random q).run s),
      usedEncaps t z.2 := by
  rw [injectedSecurityImpl_eq]
  intro z hz
  cases ho : targetOwner t <;> simp only [usedEncaps, ho] at hu ⊢
  · refine idealRecvSecurityImpl_stB_step kem hDet ecEk ecCt leak _ random (targetEncapsulated t)
      (fun st key? ρ tsnd st' hout hQ => ?_)
      (fun st key? ρ tsnd st' rand hw hQ =>
        targetEncapsulated_sendWith .B t _ _ ecEk ecCt st key? ρ tsnd st' rand hw hQ)
      (fun recover st ρ key? trcv st' hr hQ =>
        targetEncapsulated_recvWith .B t recover ecEk ecCt st ρ key? trcv st' hr hQ) q s hu z hz
    obtain ⟨rand, hw⟩ :=
      exists_rand_of_mem_injectedSend kem ecEk ecCt t inj .B st key? ρ tsnd st' hout
    exact targetEncapsulated_sendWith .B t _ _ ecEk ecCt st key? ρ tsnd st' rand hw hQ
  · refine idealRecvSecurityImpl_stA_step kem hDet ecEk ecCt leak _ random (targetEncapsulated t)
      (fun st key? ρ tsnd st' hout hQ => ?_)
      (fun st key? ρ tsnd st' rand hw hQ =>
        targetEncapsulated_sendWith .A t _ _ ecEk ecCt st key? ρ tsnd st' rand hw hQ)
      (fun recover st ρ key? trcv st' hr hQ =>
        targetEncapsulated_recvWith .A t recover ecEk ecCt st ρ key? trcv st' hr hQ) q s hu z hz
    obtain ⟨rand, hw⟩ :=
      exists_rand_of_mem_injectedSend kem ecEk ecCt t inj .A st key? ρ tsnd st' hout
    exact targetEncapsulated_sendWith .A t _ _ ecEk ecCt st key? ρ tsnd st' rand hw hQ

/-- An encapsulation for the target on an `InjInv` state leaves the target encapsulated for:
the send is not rejected, and its output state records the encapsulation. -/
lemma usedEncaps_of_hit (x : PK × SK) (hx : x ∈ support kem.keygen) (y : C × K)
    (hy : y ∈ support (kem.encaps x.1)) (inj : TargetInjection PK SK C K) (random : ℕ → Bool)
    (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) (hpk : inj.pk = x.1)
    (hq : hitEncaps (leak := leak) t q s = true) :
    ∀ z ∈ support ((injectedSecurityImpl kem hDet ecEk ecCt leak t ⟨x.1, x.2, y.1, y.2⟩ random
      q).run s), usedEncaps t z.2 := by
  obtain ⟨-, T, hA, hB⟩ := hs.1
  have htpar := targetOwner_parity t
  rw [injectedSecurityImpl_eq]
  intro z hz
  rcases q with (((((((((n | u) | u) | n) | n) | u) | u) | e) | u) | u) <;>
    simp only [hitEncaps, Bool.false_eq_true] at hq
  · have hpin := ekPeer_pinned_of_hitA kem ecEk ecCt t inj s hs hq
    cases ho : targetOwner t
    · exfalso
      rw [ho] at htpar
      rw [sendEncapsulatesTarget_eq_false_of_parity .A t s.stA htpar hA.res_parity] at hq
      cases hq
    · simp only [usedEncaps, ho]
      obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendA_run_iff _ s z).1 hz
      rcases out with _ | ⟨key?, ρ, tsnd, stA'⟩
      · exfalso
        refine send_ne_none hA (injectedSend_support_subset kem .A ecEk ecCt t _ s.stA
          (fun _ => hx) (fun _ pk' hpk' => ?_) hout)
        rw [hpin pk' hpk', hpk]
        exact hy
      · obtain ⟨rand, hw⟩ :=
          exists_rand_of_mem_injectedSend kem ecEk ecCt t _ .A s.stA key? ρ tsnd stA' hout
        rcases key? with _ | ⟨tI, k⟩ <;>
          exact targetEncapsulated_of_sendWith .A t _ _ ecEk ecCt s.stA _ ρ tsnd stA' rand hw hq
  · have hpin := ekPeer_pinned_of_hitB kem ecEk ecCt t inj s hs hq
    cases ho : targetOwner t
    · simp only [usedEncaps, ho]
      obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendB_run_iff _ s z).1 hz
      rcases out with _ | ⟨key?, ρ, tsnd, stB'⟩
      · exfalso
        refine send_ne_none hB (injectedSend_support_subset kem .B ecEk ecCt t _ s.stB
          (fun _ => hx) (fun _ pk' hpk' => ?_) hout)
        rw [hpin pk' hpk', hpk]
        exact hy
      · obtain ⟨rand, hw⟩ :=
          exists_rand_of_mem_injectedSend kem ecEk ecCt t _ .B s.stB key? ρ tsnd stB' hout
        rcases key? with _ | ⟨tI, k⟩ <;>
          exact targetEncapsulated_of_sendWith .B t _ _ ecEk ecCt s.stB _ ρ tsnd stB' rand hw hq
    · exfalso
      rw [ho] at htpar
      rw [sendEncapsulatesTarget_eq_false_of_parity .B t s.stB htpar hB.res_parity] at hq
      cases hq

include hEk hCt in
/-- The encapsulation invariant is kept on continuing successors of every injected query with
a supported encapsulation: at the encapsulation for the target the witness switches to the
sample, elsewhere the sample is not read. -/
lemma encapsInv_step (ht : 0 < t) (x : PK × SK) (hx : x ∈ support kem.keygen) (y : C × K)
    (hy : y ∈ support (kem.encaps x.1)) (random : ℕ → Bool)
    (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : encapsInv kem ecEk ecCt t x s) :
    ∀ z ∈ support ((injectedSecurityImpl kem hDet ecEk ecCt leak t ⟨x.1, x.2, y.1, y.2⟩ random
      q).run s), t ∉ z.2.exposed → encapsInv kem ecEk ecCt t x z.2 := by
  intro z hz hexp
  obtain ⟨y', hy', hs'⟩ := hs
  cases hh : hitEncaps (leak := leak) t q s with
  | true =>
    obtain ⟨hA, hB⟩ := tables_empty_of_hitEncaps kem ecEk ecCt leak t ht _ s hs' q hh
    exact ⟨y, hy, injectedSecurityImpl_preservesInv_continuing kem hDet ecEk ecCt hEk hCt leak t
      _ hx hy ht random q s (injInv_switch_key hA hB hs') z hz hexp⟩
  | false =>
    rw [injectedSecurityImpl_run_eq_of_not_hitEncaps kem hDet ecEk ecCt leak t x.1 x.2 y y' random
      s q hh] at hz
    exact ⟨y', hy', injectedSecurityImpl_preservesInv_continuing kem hDet ecEk ecCt hEk hCt leak
      t _ hx hy' ht random q s hs' z hz hexp⟩

include hEk hCt in
/-- Drawing the target's encapsulation first and running the stopped injected oracles has the
acceptance probability of the stopped keygen-injected oracles, for a supported key pair. -/
lemma prEvent_stopped_injected_eq_keygenInjected (ht : 0 < t) (x : PK × SK)
    (hx : x ∈ support kem.keygen) (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr{let w ← kem.encaps x.1 >>= fun y =>
        stoppedRun (injectedSecurityImpl kem hDet ecEk ecCt leak t ⟨x.1, x.2, y.1, y.2⟩
          (hybridRandom (t + b.toNat))) (targetExposed t) adv
          (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))}[w = true] =
      Pr{let w ← stoppedRun (idealRecvSecurityImpl kem hDet ecEk ecCt leak
           (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) (hybridRandom (t + b.toNat)))
           (targetExposed t) adv
           (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))}[w = true] := by
  obtain ⟨y₀, hy₀⟩ := OracleComp.support_nonempty (kem.encaps x.1)
  have hinit : encapsInv kem ecEk ecCt t x initState := ⟨y₀, hy₀, injInv_init kem ecEk ecCt t ht _⟩
  unfold stoppedRun
  rw [map_bind, optionRun_sample_once_eq_sampleEachQuery (kem.encaps x.1)
    (fun y : C × K => stopOnState (injectedSecurityImpl kem hDet ecEk ecCt leak t
      ⟨x.1, x.2, y.1, y.2⟩ (hybridRandom (t + b.toNat))) (targetExposed t))
    (encapsInv kem ecEk ecCt t x) (usedEncaps t) (hitEncaps t)
    (fun y hy q s hs z hz hsome => by
      obtain ⟨w, hw, hexp, hzw⟩ :=
        exists_of_mem_support_stopOnState _ _ _ _ _ hz hsome
      simp only [targetExposed, decide_eq_false_iff_not] at hexp
      rw [hzw]
      exact encapsInv_step kem hDet ecEk ecCt hEk hCt leak t ht x hx y hy _ q s hs w hw hexp)
    (fun y _ q s _ hu z hz _ => by
      obtain ⟨w, hw, hzw⟩ := exists_base_of_mem_stopOnState hz
      rw [hzw]
      exact usedEncaps_step kem hDet ecEk ecCt leak t _ _ q s hu w hw)
    (fun q s _ hh (y : C × K) _ (y' : C × K) _ => by
      rw [stopOnState_run_run_eq _ _ _ q s
        (injectedSecurityImpl_run_eq_of_not_hitEncaps kem hDet ecEk ecCt leak t x.1 x.2 y y' _ s q
          hh)])
    (fun q s hs hu => by
      obtain ⟨y', -, hs'⟩ := hs
      exact hitEncaps_eq_false_of_used kem ecEk ecCt leak t s hs'.1 hu q)
    (fun y hy q s hs hh z hz _ => by
      obtain ⟨w, hw, hzw⟩ := exists_base_of_mem_stopOnState hz
      rw [hzw]
      obtain ⟨y', -, hs'⟩ := hs
      exact usedEncaps_of_hit kem hDet ecEk ecCt leak t x hx y hy _ _ q s hs' rfl hh w hw)
    adv initState hinit]
  refine (prEvent_optionRun_eq_of_state_map
    (sampleEachQuery (kem.encaps x.1) (fun y : C × K =>
      stopOnState (injectedSecurityImpl kem hDet ecEk ecCt leak t ⟨x.1, x.2, y.1, y.2⟩
        (hybridRandom (t + b.toNat))) (targetExposed t)))
    (stopOnState (idealRecvSecurityImpl kem hDet ecEk ecCt leak
      (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) (hybridRandom (t + b.toNat)))
      (targetExposed t))
    id (encapsInv kem ecEk ecCt t x)
    (fun q s hs z hz hsome => ?_) (fun q s hs => ?_) adv initState hinit).symm
  · rw [sampleEachQuery_run, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    obtain ⟨w, hw, hexp, hzw⟩ :=
      exists_of_mem_support_stopOnState _ _ _ _ _ hz hsome
    simp only [targetExposed, decide_eq_false_iff_not] at hexp
    rw [hzw]
    exact encapsInv_step kem hDet ecEk ecCt hEk hCt leak t ht x hx y hy _ q s hs w hw hexp
  · simp only [id, Prod.map_id, id_map]
    refine EvalDistEq.symm ?_
    refine evalDistEq_sampleEachQuery_stopOnState (kem.encaps x.1) _ _ (targetExposed t) q s ?_
    cases hh : hitEncaps (leak := leak) t q s with
    | false =>
      have heq : ∀ y : C × K, (injectedSecurityImpl kem hDet ecEk ecCt leak t
          ⟨x.1, x.2, y.1, y.2⟩ (hybridRandom (t + b.toNat)) q).run s =
          (idealRecvSecurityImpl kem hDet ecEk ecCt leak
            (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) (hybridRandom (t + b.toNat))
            q).run s :=
        fun y => injectedSecurityImpl_run_eq_keygenInjected_of_not_hitEncaps kem hDet ecEk ecCt
          leak t x.1 x.2 y _ s q hh
      simp only [heq]
      exact OracleComp.EvalDistEq.bind_const _ _
    | true =>
      obtain ⟨y', -, hs'⟩ := hs
      exact injected_hitEncaps_evalDist kem hDet ecEk ecCt leak t x _ s q hh
        (ekPeer_pinned_of_hitA kem ecEk ecCt t _ s hs')
        (ekPeer_pinned_of_hitB kem ecEk ecCt t _ s hs')

/-! ### Peel 3: the key pair -/

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] hDet in
/-- Once the target's key pair is generated, no query generates it. -/
lemma hitKeygen_eq_false_of_used
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hu : usedKeygen t s) (q : (securitySpec leak Sym).Domain) :
    hitKeygen (leak := leak) t q s = false := by
  obtain ⟨-, T, hA, hB⟩ := hs
  have htpar := targetOwner_parity t
  rcases q with (((((((((n | u) | u) | n) | n) | u) | u) | e) | u) | u) <;> (try rfl)
  · change sendGeneratesTarget .A t s.stA = false
    cases ho : targetOwner t
    · simp only [usedKeygen, ho] at hu
      exact sendGeneratesTarget_eq_false_of_generated .A t s.stA hu
    · rw [ho] at htpar
      exact sendGeneratesTarget_eq_false_of_parity .A t s.stA (by simpa using htpar)
        hA.res_parity
  · change sendGeneratesTarget .B t s.stB = false
    cases ho : targetOwner t
    · rw [ho] at htpar
      exact sendGeneratesTarget_eq_false_of_parity .B t s.stB (by simpa using htpar)
        hB.res_parity
    · simp only [usedKeygen, ho] at hu
      exact sendGeneratesTarget_eq_false_of_generated .B t s.stB hu

/-- Every keygen-injected query keeps the target's key pair generated. -/
lemma usedKeygen_step (x : PK × SK) (random : ℕ → Bool) (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hu : usedKeygen t s) :
    ∀ z ∈ support ((idealRecvSecurityImpl kem hDet ecEk ecCt leak
      (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) random q).run s),
      usedKeygen t z.2 := by
  intro z hz
  cases ho : targetOwner t <;> simp only [usedKeygen, ho] at hu ⊢
  · refine idealRecvSecurityImpl_stA_step kem hDet ecEk ecCt leak _ random (targetGenerated .A t)
      (fun st key? ρ tsnd st' hout hQ => ?_)
      (fun st key? ρ tsnd st' rand hw hQ =>
        targetGenerated_sendWith .A t _ _ ecEk ecCt st key? ρ tsnd st' rand hw hQ)
      (fun recover st ρ key? trcv st' hr hQ =>
        targetGenerated_recvWith .A t recover ecEk ecCt st ρ key? trcv st' hr hQ) q s hu z hz
    obtain ⟨rand, hw⟩ :=
      exists_rand_of_mem_keygenInjectedSend kem ecEk ecCt t .A x.1 x.2 st key? ρ tsnd st' hout
    exact targetGenerated_sendWith .A t _ _ ecEk ecCt st key? ρ tsnd st' rand hw hQ
  · refine idealRecvSecurityImpl_stB_step kem hDet ecEk ecCt leak _ random (targetGenerated .B t)
      (fun st key? ρ tsnd st' hout hQ => ?_)
      (fun st key? ρ tsnd st' rand hw hQ =>
        targetGenerated_sendWith .B t _ _ ecEk ecCt st key? ρ tsnd st' rand hw hQ)
      (fun recover st ρ key? trcv st' hr hQ =>
        targetGenerated_recvWith .B t recover ecEk ecCt st ρ key? trcv st' hr hQ) q s hu z hz
    obtain ⟨rand, hw⟩ :=
      exists_rand_of_mem_keygenInjectedSend kem ecEk ecCt t .B x.1 x.2 st key? ρ tsnd st' hout
    exact targetGenerated_sendWith .B t _ _ ecEk ecCt st key? ρ tsnd st' rand hw hQ

/-- A generation of the target's key pair on a `GameInv` state leaves the target generated. -/
lemma usedKeygen_of_hit (x : PK × SK) (hx : x ∈ support kem.keygen) (random : ℕ → Bool)
    (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : GameInv kem ecEk ecCt s) (hq : hitKeygen (leak := leak) t q s = true) :
    ∀ z ∈ support ((idealRecvSecurityImpl kem hDet ecEk ecCt leak
      (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) random q).run s),
      usedKeygen t z.2 := by
  obtain ⟨-, T, hA, hB⟩ := hs
  have htpar := targetOwner_parity t
  intro z hz
  rcases q with (((((((((n | u) | u) | n) | n) | u) | u) | e) | u) | u) <;>
    simp only [hitKeygen, Bool.false_eq_true] at hq
  · cases ho : targetOwner t
    · simp only [usedKeygen, ho]
      obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendA_run_iff _ s z).1 hz
      rcases out with _ | ⟨key?, ρ, tsnd, stA'⟩
      · exact absurd (keygenInjectedSend_support_subset kem ecEk ecCt t .A x hx s.stA hout)
          (send_ne_none hA)
      · obtain ⟨rand, hw⟩ := exists_rand_of_mem_keygenInjectedSend kem ecEk ecCt t .A x.1 x.2
          s.stA key? ρ tsnd stA' hout
        rcases key? with _ | ⟨tI, k⟩ <;>
          exact targetGenerated_of_sendWith .A t _ _ ecEk ecCt s.stA _ ρ tsnd stA' rand hw hq
    · exfalso
      rw [ho] at htpar
      rw [sendGeneratesTarget_eq_false_of_parity .A t s.stA (by simpa using htpar)
        hA.res_parity] at hq
      cases hq
  · cases ho : targetOwner t
    · exfalso
      rw [ho] at htpar
      rw [sendGeneratesTarget_eq_false_of_parity .B t s.stB (by simpa using htpar)
        hB.res_parity] at hq
      cases hq
    · simp only [usedKeygen, ho]
      obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendB_run_iff _ s z).1 hz
      rcases out with _ | ⟨key?, ρ, tsnd, stB'⟩
      · exact absurd (keygenInjectedSend_support_subset kem ecEk ecCt t .B x hx s.stB hout)
          (send_ne_none hB)
      · obtain ⟨rand, hw⟩ := exists_rand_of_mem_keygenInjectedSend kem ecEk ecCt t .B x.1 x.2
          s.stB key? ρ tsnd stB' hout
        rcases key? with _ | ⟨tI, k⟩ <;>
          exact targetGenerated_of_sendWith .B t _ _ ecEk ecCt s.stB _ ρ tsnd stB' rand hw hq

include hEk hCt in
/-- The stopped hybrid oracles have the acceptance probability of drawing the target's key pair
first and running the stopped keygen-injected oracles. -/
lemma prEvent_stopped_hybrid_eq_keygenInjected (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr{let x ← stoppedRun (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom (t + b.toNat)))
        (targetExposed t) adv
        (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))}[x = true] =
      Pr{let w ← kem.keygen >>= fun x =>
           stoppedRun (idealRecvSecurityImpl kem hDet ecEk ecCt leak
          (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) (hybridRandom (t + b.toNat)))
          (targetExposed t) adv
          (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))}[w = true] := by
  have hinit : GameInv kem ecEk ecCt (initState (K := K) (PK := PK) (SK := SK) (C := C)
      (Sym := Sym)) :=
    gameInv_init kem ecEk ecCt _ _ (by simp [initA, init, initialState])
      (by simp [initB, init, initialState])
  have hpres : ∀ x ∈ support kem.keygen, ∀ q s, GameInv kem ecEk ecCt s →
      ∀ z ∈ support ((idealRecvSecurityImpl kem hDet ecEk ecCt leak
        (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) (hybridRandom (t + b.toNat))
        q).run s), GameInv kem ecEk ecCt z.2 :=
    fun x hx q s hs z hz => gameInv_idealRecv_step kem hDet ecEk ecCt leak _ _ hEk hCt
      (fun st => keygenInjectedSend_support_subset kem ecEk ecCt t .A x hx st)
      (fun st => keygenInjectedSend_support_subset kem ecEk ecCt t .B x hx st) q s hs z hz
  unfold stoppedRun
  rw [map_bind, optionRun_sample_once_eq_sampleEachQuery kem.keygen
    (fun x : PK × SK => stopOnState (idealRecvSecurityImpl kem hDet ecEk ecCt leak
      (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) (hybridRandom (t + b.toNat)))
      (targetExposed t))
    (GameInv kem ecEk ecCt) (usedKeygen t) (hitKeygen t)
    (fun x hx q s hs z hz _ => by
      obtain ⟨w, hw, hzw⟩ := exists_base_of_mem_stopOnState hz
      rw [hzw]
      exact hpres x hx q s hs w hw)
    (fun x _ q s _ hu z hz _ => by
      obtain ⟨w, hw, hzw⟩ := exists_base_of_mem_stopOnState hz
      rw [hzw]
      exact usedKeygen_step kem hDet ecEk ecCt leak t x _ q s hu w hw)
    (fun q s _ hh x _ x' _ => by
      rw [stopOnState_run_run_eq _ _ _ q s
        (keygenInjected_run_eq_of_not_hitKeygen kem hDet ecEk ecCt leak t x x' _ s q hh)])
    (fun q s hs hu => hitKeygen_eq_false_of_used kem ecEk ecCt leak t s hs hu q)
    (fun x hx q s hs hh z hz _ => by
      obtain ⟨w, hw, hzw⟩ := exists_base_of_mem_stopOnState hz
      rw [hzw]
      exact usedKeygen_of_hit kem hDet ecEk ecCt leak t x hx _ q s hs hh w hw)
    adv initState hinit]
  refine prEvent_optionRun_eq_of_state_map
    (sampleEachQuery kem.keygen (fun x : PK × SK =>
      stopOnState (idealRecvSecurityImpl kem hDet ecEk ecCt leak
        (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) (hybridRandom (t + b.toNat)))
        (targetExposed t)))
    (stopOnState (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom (t + b.toNat)))
      (targetExposed t))
    id (GameInv kem ecEk ecCt)
    (fun q s hs z hz _ => ?_) (fun q s hs => ?_) adv initState hinit
  · rw [sampleEachQuery_run, mem_support_bind_iff] at hz
    obtain ⟨x, hx, hz⟩ := hz
    obtain ⟨w, hw, hzw⟩ := exists_base_of_mem_stopOnState hz
    rw [hzw]
    exact hpres x hx q s hs w hw
  · simp only [id, Prod.map_id, id_map]
    refine EvalDistEq.symm ?_
    refine evalDistEq_sampleEachQuery_stopOnState kem.keygen _ _ (targetExposed t) q s ?_
    cases hh : hitKeygen (leak := leak) t q s with
    | false =>
      have heq : ∀ x : PK × SK, (idealRecvSecurityImpl kem hDet ecEk ecCt leak
          (keygenInjectedScheme kem hDet ecEk ecCt leak t x.1 x.2) (hybridRandom (t + b.toNat))
          q).run s = (hybridSecurityImpl kem hDet ecEk ecCt leak (hybridRandom (t + b.toNat))
          q).run s :=
        fun x => keygenInjected_run_eq_hybrid_of_not_hitKeygen kem hDet ecEk ecCt leak t x _ s q hh
      simp only [heq]
      exact OracleComp.EvalDistEq.bind_const _ _
    | true =>
      rw [keygenInjected_hitKeygen_eq kem hDet ecEk ecCt leak t _ s q hh]

end PeelSamples

/-! ## Eager equals lazy on the stopped hybrids -/

section Main

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)

include hEk hCt in
/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes;
* `0 < t`.

Then the stopped hybrid with threshold `t + b` accepts with the probability of the eager hybrid
for bit `b`, averaged over the target's key pair, encapsulation and uniform challenge key:
`Pr[S_t^x = true] = E_{(pk, sk), (c, k), r} Pr[E_t^x(pk, sk, c, k, r) = true]`. -/
theorem prEvent_stoppedHybridExp_eq_eager (adv : SecurityAdversary leak Sym) (t : ℕ)
    (ht : 0 < t) (b : Bool) :
    Pr{let x ← stoppedHybridExp kem hDet ecEk ecCt leak t (t + b.toNat) adv}[x = true] =
      Pr{let w ← kem.keygen >>= fun x => kem.encaps x.1 >>= fun y => ($ᵗ K : ProbComp K) >>=
           fun r => stoppedEagerExp kem hDet ecEk ecCt leak t b x.1 x.2 y.1 y.2 r
             adv}[w = true] := by
  unfold stoppedHybridExp
  rw [prEvent_stopped_hybrid_eq_keygenInjected kem hDet ecEk ecCt hEk hCt leak t b adv,
    map_bind, map_bind]
  refine prEvent_bind_congr_of_support _ _ _ fun x hx => ?_
  rw [← prEvent_stopped_injected_eq_keygenInjected kem hDet ecEk ecCt hEk hCt leak t ht x hx b
    adv, map_bind, map_bind]
  refine prEvent_bind_congr_of_support _ _ _ fun y _ => ?_
  exact (prEvent_stopped_eager_eq_injected kem hDet ecEk ecCt leak t ⟨x.1, x.2, y.1, y.2⟩ b adv
    _).symm

end Main

end oppBiKemCKA
