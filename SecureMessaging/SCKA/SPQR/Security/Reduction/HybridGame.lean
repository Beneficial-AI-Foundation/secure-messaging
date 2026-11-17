/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Security.Reduction.Deferral
public import SecureMessaging.SCKA.SPQR.Security.Reduction.AuthMap

/-!
# The hybrid gap as a difference of simulated games

Assume that the four stream decoders of `P` are sound for their erasure codes, and fix an SCKA
adversary `adv` against SPQR, the challenge epoch `e > 0` drawn by the reductions, dummies `d`
(`Reduction.Relation`), an initial key `ik`, and a version `x ∈ {real, random}` (`false` for
`real`, `true` for `random`): a challenge at `e` returns the real (recorded) key in `real` and an
independent uniform key in `random`. All games below run `adv` from `initState auth ik`, return
`false` at the first query that exposes `e`, and otherwise return the output of `adv`.

- The *stopped hybrid* `S_e^x[A]` over an authenticator `A` runs the ideal hybrid `H_{e-1}` in
  `real` and `H_e` in `random` (`stoppedHybridExp A adv (e - 1) e ik` and
  `stoppedHybridExp A adv e e ik`, `Security.Ideal`); `S_e^x := S_e^x[auth]`.
- `A_κ := hybridAuth auth e ik κ` is `auth` with its update of `e - 1` replaced by
  `hiddenState auth e ik κ` (`Reduction.AuthMap`): the update keyed by `κ` for
  `e ≥ 2`, and for `e = 1` an update that no reachable state performs.
- The *simulated game* `simRun A e d ik pk ct1 ct2 kStar kUpd` runs the simulated instance over `A`,
  which holds only the public values `pk`, `ct1`, `ct2` of `e` and the dummies `d`
  (`simSchemeOf`, `Reduction.Relation`); the keys recorded at `e` are the dummy key
  `P.kdfOK d.k e`, the authenticator update of `e` uses `kUpd`, and challenges are answered by the
  pinned challenge `pinnedChallenge e kStar` (`SCKA.Security.Hybrids`): an eligible challenge at
  `t` returns a uniform key if `0 < t < e`, `kStar` if `t = e`, and the recorded key otherwise.
- The *games of the chain* over `A_κ` draw a fresh key pair `(pk, _) ← P.det.toKEM.keygen` and
  encapsulation `(c, k) ← P.det.toKEM.encaps pk`, the keys of the following table, and
  `κ ←$ P.EpochKey`, and run `simRun A_κ e d ik pk (splitC c).1 (splitC c).2 kStar kUpd`, for
  `kdf k := P.kdfOK k e`, `r ←$ P.K`, and `u u' k' ←$ P.EpochKey`:

  | game           | `kStar` (challenge key) | `kUpd` (authenticator update) |
  | -------------- | ----------------------- | ----------------------------- |
  | `realKey`      | `kdf k`                 | `kdf k`                       |
  | `randKey`      | `kdf r`                 | `kdf r`                       |
  | `randEpochKey` | `u`                     | `u`                           |
  | `splitKeys`    | `u'`                    | `u`                           |
  | `randKeyChal`  | `k'`                    | `kdf r`                       |
  | `realKeyChal`  | `k'`                    | `kdf k`                       |

- For `e ≥ 2`, `prevGame x e d ik pk ct1 ct2 w` runs the simulated instance of `e - 1` over `auth`
  holding `pk`, `ct1`, `ct2`, with the update of `e - 1` keyed by `w`, against the challenge
  oracle of `S_e^x`; it is `pure false` for `e = 1`. The other games of the chain, `prevReal x`,
  `prevRand x` and `prevKdf x`, run it on a fresh encapsulation `(c, k)` with
  `w := P.kdfOK k (e - 1)`, `w := P.kdfOK r (e - 1)` for `r ←$ P.K`, and `w ←$ P.EpochKey`.

**Main results.** For every `x`, `d` and `ik`:

```text
Pr[κ ←$ P.EpochKey; S_e^real[A_κ]] = Pr[realKey]
Pr[κ ←$ P.EpochKey; S_e^random[A_κ]] = Pr[realKeyChal]
Pr[S_e^x] - Pr[κ ←$ P.EpochKey; S_e^x[A_κ]] = Pr[prevReal x] - Pr[prevKdf x]
```

(`stoppedHybrid_hybridAuth_real_eq_realKey`, `stoppedHybrid_hybridAuth_random_eq_realKeyChal`,
`stoppedHybrid_sub_hybridAuth_eq`). For `e = 1`, both `prev` games are `pure false`.
-/

@[expose] public section

open OracleSpec OracleComp

namespace SPQR

open Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac) (sampleInitKey : ProbComp InitKey)
  (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
  (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
  [DecidableEq P.EpochKey] [SampleableType P.EpochKey]
  (adv : SecurityAdversary P AuthState)

/-! ### The simulated game -/

/-- The simulated game of epoch `e` with dummies `d`: `adv` run from `initState auth ik` against
the simulated instance holding `pk`, `ct1`, `ct2`, with the authenticator update of `e` keyed by
`kUpd` and challenges answered by `pinnedChallenge e kStar` (an eligible challenge at `t` returns a
uniform key if `0 < t < e`, `kStar` if `t = e`, and the recorded key otherwise), returning `false`
at the first exposure of `e`. -/
def simRun (e : ℕ) (d : Dummies P) (ik : InitKey) (pk : P.PK) (ct1 : P.det.C₁) (ct2 : P.det.C₂)
    (kStar kUpd : P.EpochKey) : ProbComp Bool :=
  stoppedRun (SCKAScheme.securityImplAt
      (simSchemeOf auth sampleInitKey e d pk ct1 ct2 (fun a => auth.update a e kUpd))
      (SCKAScheme.pinnedChallenge e kStar) (vuln P AuthState) (vuln P AuthState))
    (fun u => decide (e ∈ u.exposed)) adv (initState auth ik)

section Hybrids

variable (e : ℕ) (d : Dummies P) (ik : InitKey)

include hHdrSound hEkSound hCt1Sound hCt2Sound

/-- For a possible KEM material `kemMat`, the stopped pinned game of version `real` (mode
`adjacentMode e false`) accepts as often as the simulated game with both keys
`kemMat.epochKey e`. -/
private theorem stoppedRun_pinned_real_eq_simRun (kemMat : KEMMaterial P)
    (hm : kemMat ∈ support (sampleMaterial)) :
    Pr{let x ← (stoppedRun (pinnedImpl auth sampleInitKey e (some kemMat.kg) (some kemMat.enc)
        (SCKAScheme.adjacentMode e false)) (fun u => decide (e ∈ u.exposed)) adv
      (initState auth ik))}[x = true] =
    Pr{let x ← (simRun auth sampleInitKey adv e d ik kemMat.pk kemMat.ct1 kemMat.ct2
      (kemMat.epochKey e)
      (kemMat.epochKey e))}[x = true] := by
  unfold simRun
  rw [prEvent_stoppedRun_sim_eq_honest_pinned auth sampleInitKey hHdrSound hEkSound
    hCt1Sound hCt2Sound e d kemMat hm (kemMat.epochKey e) adv ik]
  refine prEvent_stoppedRun_eq_of_query_eq _ _ _
    (PinnedInv auth (some kemMat.kg.1) (some kemMat.enc.1) e)
    (honestImpl_preservesInv auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound e kemMat hm _ (SCKAScheme.pinnedChallenge_recordsChallenges e _))
    (fun t s hs => (SCKAScheme.securityImplAt_pinnedChallenge_eq_recorded e (kemMat.epochKey e)
      (honestSchemeOf auth sampleInitKey e kemMat) (vuln P AuthState) (vuln P AuthState)
      t s (fun k hk => hk.elim
        (fun h => PinnedInv.keys_eq auth hs true h)
        (fun h => PinnedInv.keys_eq auth hs false h))).symm)
    adv _ (pinnedInv_initState auth _ _ e ik)

/-- For `0 < e` and a possible KEM material `kemMat`, the stopped pinned game of version `random`
(mode `adjacentMode e true`) accepts as often as the simulated game with a uniform challenge key and
the update key `kemMat.epochKey e`. -/
private theorem stoppedRun_pinned_random_eq_simRun (he : 0 < e) (kemMat : KEMMaterial P)
    (hm : kemMat ∈ support (sampleMaterial)) :
    Pr{let x ← (stoppedRun (pinnedImpl auth sampleInitKey e (some kemMat.kg) (some kemMat.enc)
        (SCKAScheme.adjacentMode e true)) (fun u => decide (e ∈ u.exposed)) adv
      (initState auth ik))}[x = true] =
    Pr{let x ← (do
      let k ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      simRun auth sampleInitKey adv e d ik kemMat.pk kemMat.ct1 kemMat.ct2 k
        (kemMat.epochKey e))}[x = true] := by
  change Pr{let x ← (stoppedRun (SCKAScheme.modeImpl
    (honestSchemeOf auth sampleInitKey e kemMat)
    (vuln P AuthState) (vuln P AuthState) (SCKAScheme.adjacentMode e true))
    (fun u => decide (e ∈ u.exposed)) adv (initState auth ik))}[x = true] = _
  rw [← SCKAScheme.stoppedRun_pinnedChallenge_sample_eq e
    (honestSchemeOf auth sampleInitKey e kemMat)
    (vuln P AuthState) (vuln P AuthState) he adv (initState auth ik)]
  refine OracleComp.prEvent_bind_congr_of_support' _ _ fun k _ => ?_
  unfold simRun
  exact (prEvent_stoppedRun_sim_eq_honest_pinned auth sampleInitKey hHdrSound hEkSound
    hCt1Sound hCt2Sound e d kemMat hm k adv ik).symm

/-- The stopped hybrid `S_e^real := stoppedHybridExp adv (e - 1) e ik` accepts as often as the
simulated game over a sampled KEM material with both keys `kemMat.epochKey e`. -/
private theorem stoppedHybrid_real_eq_simRun :
    Pr{let x ← stoppedHybridExp auth sampleInitKey adv (e - 1) e ik}[x = true] =
    Pr{let x ← (do
      let kemMat ← sampleMaterial
      simRun auth sampleInitKey adv e d ik kemMat.pk kemMat.ct1 kemMat.ct2 (kemMat.epochKey e)
        (kemMat.epochKey e))}[x = true] := by
  rw [stoppedHybridExp, ← stoppedRun_material_deferred auth sampleInitKey hHdrSound
    hEkSound hCt1Sound hCt2Sound e (Or.inl rfl) _ adv ik]
  exact OracleComp.prEvent_bind_congr_of_support' _ _ fun kemMat hm =>
    stoppedRun_pinned_real_eq_simRun auth sampleInitKey hHdrSound hEkSound hCt1Sound
    hCt2Sound adv e d ik kemMat hm

/-- For `0 < e`, the stopped hybrid `S_e^random := stoppedHybridExp adv e e ik` accepts as often as
the simulated game over a sampled KEM material with a uniform challenge key and the update key
`kemMat.epochKey e`. -/
private theorem stoppedHybrid_random_eq_simRun (he : 0 < e) :
    Pr{let x ← stoppedHybridExp auth sampleInitKey adv e e ik}[x = true] =
    Pr{let x ← (do
      let kemMat ← sampleMaterial
      let k ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      simRun auth sampleInitKey adv e d ik kemMat.pk kemMat.ct1 kemMat.ct2 k
        (kemMat.epochKey e))}[x = true] := by
  rw [stoppedHybridExp, ← stoppedRun_material_deferred auth sampleInitKey hHdrSound
    hEkSound hCt1Sound hCt2Sound e (Or.inl rfl) _ adv ik]
  exact OracleComp.prEvent_bind_congr_of_support' _ _ fun kemMat hm =>
    stoppedRun_pinned_random_eq_simRun auth sampleInitKey hHdrSound hEkSound hCt1Sound
    hCt2Sound adv e d ik he kemMat hm

end Hybrids

/-! ### The authenticator with the hidden state -/

/-- The authenticator of the hybrids with the hidden state at `e`: `auth` with its update of
`e - 1` replaced by `hiddenState auth e ik κ`. For `e = 1` this replaces an update that
no reachable state performs. -/
abbrev hybridAuth (e : ℕ) (ik : InitKey) (κ : P.EpochKey) :=
  authAt auth (e - 1) (hiddenState auth e ik κ)

/-! ### The games of the chain -/

section Chain

variable (e : ℕ) (d : Dummies P) (ik : InitKey)

/-- The game with both keys the derived key `P.kdfOK k e` of a fresh encapsulation `(c, k)`. -/
def realKey : ProbComp Bool := do
  let (pk, _) ← P.det.toKEM.keygen
  let (c, k) ← P.det.toKEM.encaps pk
  let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik pk (P.det.splitC c).1
    (P.det.splitC c).2 (P.kdfOK k e) (P.kdfOK k e)

/-- The game with the challenge key a uniform `k'` and the update key the derived key `P.kdfOK k e`
of a fresh encapsulation `(c, k)`. -/
def realKeyChal : ProbComp Bool := do
  let (pk, _) ← P.det.toKEM.keygen
  let (c, k) ← P.det.toKEM.encaps pk
  let k' ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik pk (P.det.splitC c).1
    (P.det.splitC c).2 k' (P.kdfOK k e)

include hHdrSound hEkSound hCt1Sound hCt2Sound

/-- The stopped hybrid `S_e^real` over `hybridAuth auth e ik κ`, for a uniform `κ`, accepts as
often as `realKey`. -/
theorem stoppedHybrid_hybridAuth_real_eq_realKey :
    Pr{let y ← (do
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      stoppedHybridExp (hybridAuth auth e ik κ) sampleInitKey adv (e - 1) e ik)}[y = true] =
    Pr{let y ← realKey auth sampleInitKey adv e d ik}[y = true] := by
  calc _ = Pr{let y ← (do
        let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        let kemMat ← sampleMaterial
        simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik kemMat.pk kemMat.ct1
          kemMat.ct2 (kemMat.epochKey e) (kemMat.epochKey e))}[y = true] :=
        OracleComp.prEvent_bind_congr_of_support' _ _ fun κ _ =>
          stoppedHybrid_real_eq_simRun (hybridAuth auth e ik κ) sampleInitKey hHdrSound
            hEkSound hCt1Sound hCt2Sound adv e d ik
    _ = Pr{let y ← (do
        let kemMat ← sampleMaterial
        let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik kemMat.pk kemMat.ct1
          kemMat.ct2 (kemMat.epochKey e) (kemMat.epochKey e))}[y = true] :=
        (OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _
    _ = _ := by
        have h := sampleMaterial_bind_challenge (fun pk ct1 ct2 k => do
          let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
          simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik pk ct1 ct2 (P.kdfOK k e)
            (P.kdfOK k e))
        simp only at h
        simp only [KEMMaterial.epochKey]
        rw [h]
        rfl

/-- For `0 < e`, the stopped hybrid `S_e^random` over `hybridAuth auth e ik κ`, for a uniform `κ`,
accepts as often as `realKeyChal`. -/
theorem stoppedHybrid_hybridAuth_random_eq_realKeyChal (he : 0 < e) :
    Pr{let y ← (do
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      stoppedHybridExp (hybridAuth auth e ik κ) sampleInitKey adv e e ik)}[y = true] =
    Pr{let y ← realKeyChal auth sampleInitKey adv e d ik}[y = true] := by
  calc _ = Pr{let y ← (do
        let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        let kemMat ← sampleMaterial
        let k' ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik kemMat.pk kemMat.ct1
          kemMat.ct2 k' (kemMat.epochKey e))}[y = true] :=
        OracleComp.prEvent_bind_congr_of_support' _ _ fun κ _ =>
          stoppedHybrid_random_eq_simRun (hybridAuth auth e ik κ) sampleInitKey hHdrSound
            hEkSound hCt1Sound hCt2Sound adv e d ik he
    _ = Pr{let y ← (do
        let kemMat ← sampleMaterial
        let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        let k' ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik kemMat.pk kemMat.ct1
          kemMat.ct2 k' (kemMat.epochKey e))}[y = true] :=
        (OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _
    _ = Pr{let y ← (do
        let kemMat ← sampleMaterial
        let k' ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik kemMat.pk kemMat.ct1
          kemMat.ct2 k' (kemMat.epochKey e))}[y = true] :=
        OracleComp.prEvent_bind_congr_of_support' _ _ fun _ _ =>
          (OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _
    _ = _ := by
        have h := sampleMaterial_bind_challenge (fun pk ct1 ct2 k => do
          let k' ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
          let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
          simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik pk ct1 ct2 k' (P.kdfOK k e))
        simp only at h
        simp only [KEMMaterial.epochKey]
        rw [h]
        rfl

end Chain

section ChainRand

variable [SampleableType P.K] (e : ℕ) (d : Dummies P) (ik : InitKey)

/-- The game with both keys `P.kdfOK r e` for a uniform KEM key `r`. -/
def randKey : ProbComp Bool := do
  let (pk, _) ← P.det.toKEM.keygen
  let (c, _) ← P.det.toKEM.encaps pk
  let r ← ($ᵗ P.K : ProbComp P.K)
  let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik pk (P.det.splitC c).1
    (P.det.splitC c).2 (P.kdfOK r e) (P.kdfOK r e)

/-- The game with both keys a uniform epoch key `u`. -/
def randEpochKey : ProbComp Bool := do
  let (pk, _) ← P.det.toKEM.keygen
  let (c, _) ← P.det.toKEM.encaps pk
  let u ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik pk (P.det.splitC c).1
    (P.det.splitC c).2 u u

/-- The game with the challenge key a uniform `u'` and the update key an independent uniform `u`. -/
def splitKeys : ProbComp Bool := do
  let (pk, _) ← P.det.toKEM.keygen
  let (c, _) ← P.det.toKEM.encaps pk
  let u ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  let u' ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik pk (P.det.splitC c).1
    (P.det.splitC c).2 u' u

/-- The game with the challenge key a uniform `k'` and the update key `P.kdfOK r e` for a uniform
KEM key `r`. -/
def randKeyChal : ProbComp Bool := do
  let (pk, _) ← P.det.toKEM.keygen
  let (c, _) ← P.det.toKEM.encaps pk
  let r ← ($ᵗ P.K : ProbComp P.K)
  let k' ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  simRun (hybridAuth auth e ik κ) sampleInitKey adv e d ik pk (P.det.splitC c).1
    (P.det.splitC c).2 k' (P.kdfOK r e)

end ChainRand

/-! ### The epoch before the challenge -/

section Prev

/-- For `e ≥ 2`, the simulated game of `e - 1` in version `x`: `adv` run from
`initState auth ik` against the simulated instance holding `pk`, `ct1`, `ct2` at `e - 1`, with the
authenticator update of `e - 1` keyed by `k`, against the challenge oracle of `adjacentMode e x`,
returning `false` at the first exposure of `e`. For `e = 1` it is `pure false`. -/
def prevGame (x : Bool) (e : ℕ) (d : Dummies P) (ik : InitKey) (pk : P.PK) (ct1 : P.det.C₁)
    (ct2 : P.det.C₂) (k : P.EpochKey) : ProbComp Bool :=
  if e = 1 then pure false else
  stoppedRun (SCKAScheme.securityImplAt
      (simSchemeOf auth sampleInitKey (e - 1) d pk ct1 ct2 (fun a => auth.update a (e - 1) k))
      (SCKAScheme.challOf (SCKAScheme.adjacentMode e x)) (vuln P AuthState) (vuln P AuthState))
    (fun u => decide (e ∈ u.exposed)) adv (initState auth ik)

/-- `prevGame` on a fresh encapsulation `(c, k)` at `e - 1` with the derived key
`P.kdfOK k (e - 1)`. -/
def prevReal (x : Bool) (e : ℕ) (d : Dummies P) (ik : InitKey) : ProbComp Bool := do
  let (pk, _) ← P.det.toKEM.keygen
  let (c, k) ← P.det.toKEM.encaps pk
  prevGame auth sampleInitKey adv x e d ik pk (P.det.splitC c).1 (P.det.splitC c).2
    (P.kdfOK k (e - 1))

/-- `prevGame` on a fresh encapsulation at `e - 1` with `P.kdfOK r (e - 1)` for a uniform KEM key
`r`. -/
def prevRand [SampleableType P.K] (x : Bool) (e : ℕ) (d : Dummies P) (ik : InitKey) :
    ProbComp Bool := do
  let (pk, _) ← P.det.toKEM.keygen
  let (c, _) ← P.det.toKEM.encaps pk
  let r ← ($ᵗ P.K : ProbComp P.K)
  prevGame auth sampleInitKey adv x e d ik pk (P.det.splitC c).1 (P.det.splitC c).2
    (P.kdfOK r (e - 1))

/-- `prevGame` on a fresh encapsulation at `e - 1` with a uniform epoch key `κ`. -/
def prevKdf (x : Bool) (e : ℕ) (d : Dummies P) (ik : InitKey) : ProbComp Bool := do
  let (pk, _) ← P.det.toKEM.keygen
  let (c, _) ← P.det.toKEM.encaps pk
  let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
  prevGame auth sampleInitKey adv x e d ik pk (P.det.splitC c).1 (P.det.splitC c).2 κ

include hHdrSound hEkSound hCt1Sound hCt2Sound

/-- For `e ≥ 2`, the stopped hybrid of version `x` over `auth` accepts as often as
`prevReal x`: the KEM material of `e - 1` is drawn in advance and simulated. -/
theorem stoppedHybrid_eq_prevReal {e : ℕ} (he : 2 ≤ e) (x : Bool) (d : Dummies P)
    (ik : InitKey) :
    Pr{let y ← (stoppedHybridExp auth sampleInitKey adv (if x then e else e - 1) e ik)}[y = true] =
    Pr{let y ← prevReal auth sampleInitKey adv x e d ik}[y = true] := by
  have he1 : e ≠ 1 := by omega
  have hsucc : e - 1 + 1 = e := by omega
  have hmode : SCKAScheme.adjacentMode e x (e - 1) = true := by
    simp [SCKAScheme.adjacentMode_apply]; omega
  rw [stoppedHybridExp, show SCKAScheme.hybridMode (if x then e else e - 1) =
      SCKAScheme.adjacentMode e x from rfl,
    ← stoppedRun_material_deferred auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound (e - 1) (e' := e) (Or.inr hsucc.symm) _ adv ik]
  have hsim := fun (kemMat : KEMMaterial P) (hm : kemMat ∈ support sampleMaterial) =>
    prEvent_stoppedRun_sim_eq_honest_challOf auth sampleInitKey hHdrSound hEkSound
      hCt1Sound hCt2Sound (e - 1) d kemMat hm (SCKAScheme.adjacentMode e x) hmode adv ik
  simp only [hsucc] at hsim
  have hmat := sampleMaterial_bind_challenge (fun pk ct1 ct2 k =>
    prevGame auth sampleInitKey adv x e d ik pk ct1 ct2 (P.kdfOK k (e - 1)))
  simp only [prevReal]
  rw [← hmat]
  refine OracleComp.prEvent_bind_congr_of_support' _ _ fun kemMat hm => ?_
  simp only [prevGame, he1, ↓reduceIte]
  exact (hsim kemMat hm).symm

/-- For `e ≥ 2`, the stopped hybrid of version `x` over `hybridAuth auth e ik κ` accepts as often
as `prevGame x` on a sampled KEM material of `e - 1` with the update of `e - 1` keyed by `κ`. -/
private theorem stoppedHybrid_hybridAuth_eq_prevGame {e : ℕ} (he : 2 ≤ e) (x : Bool)
    (d : Dummies P) (ik : InitKey) (κ : P.EpochKey) :
    Pr{let y ← (stoppedHybridExp (hybridAuth auth e ik κ) sampleInitKey adv
      (if x then e else e - 1) e ik)}[y = true] =
    Pr{let y ← (do
      let kemMat ← sampleMaterial
      prevGame auth sampleInitKey adv x e d ik kemMat.pk kemMat.ct1 kemMat.ct2 κ)}[y = true] := by
  have he1 : e ≠ 1 := by omega
  have hsucc : e - 1 + 1 = e := by omega
  have hmode : SCKAScheme.adjacentMode e x (e - 1) = true := by
    simp [SCKAScheme.adjacentMode_apply]; omega
  have hH : hiddenState auth e ik κ = fun a => auth.update a (e - 1) κ :=
    funext fun a => by simp [hiddenState, he1]
  rw [stoppedHybridExp, show SCKAScheme.hybridMode (if x then e else e - 1) =
      SCKAScheme.adjacentMode e x from rfl,
    ← stoppedRun_material_deferred (hybridAuth auth e ik κ) sampleInitKey hHdrSound hEkSound
      hCt1Sound hCt2Sound (e - 1) (e' := e) (Or.inr hsucc.symm) _ adv ik]
  have hsim := fun (kemMat : KEMMaterial P) (hm : kemMat ∈ support sampleMaterial) =>
    prEvent_stoppedRun_sim_eq_honest_challOf (hybridAuth auth e ik κ) sampleInitKey hHdrSound
      hEkSound hCt1Sound hCt2Sound (e - 1) d kemMat hm (SCKAScheme.adjacentMode e x) hmode
      adv ik
  simp only [hsucc] at hsim
  refine OracleComp.prEvent_bind_congr_of_support' _ _ fun kemMat hm => ?_
  rw [← hsim kemMat hm]
  have hupd : (fun a => (hybridAuth auth e ik κ).update a (e - 1) (kemMat.epochKey (e - 1))) =
      hiddenState auth e ik κ := by
    funext a
    simp [hybridAuth]
  have hscheme : simSchemeOf (hybridAuth auth e ik κ) sampleInitKey (e - 1) d kemMat.pk
      kemMat.ct1 kemMat.ct2
      (fun a => (hybridAuth auth e ik κ).update a (e - 1) (kemMat.epochKey (e - 1))) =
      simSchemeOf auth sampleInitKey (e - 1) d kemMat.pk kemMat.ct1 kemMat.ct2
        (fun a => auth.update a (e - 1) κ) := by
    rw [hupd]
    funext s
    simp only [simSchemeOf, hybridAuth, authAt_authAt, hH]
  have hinit : initState (hybridAuth auth e ik κ) ik = initState auth ik := rfl
  rw [hscheme, hinit]
  simp only [prevGame, he1, ↓reduceIte]

/-- For `e ≥ 2`, the stopped hybrid of version `x` over `hybridAuth auth e ik κ`, for a uniform
`κ`, accepts as often as `prevKdf x`. -/
theorem stoppedHybrid_hybridAuth_eq_prevKdf {e : ℕ} (he : 2 ≤ e) (x : Bool) (d : Dummies P)
    (ik : InitKey) :
    Pr{let y ← (do
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      stoppedHybridExp (hybridAuth auth e ik κ) sampleInitKey adv
        (if x then e else e - 1) e ik)}[y = true] =
    Pr{let y ← prevKdf auth sampleInitKey adv x e d ik}[y = true] := by
  calc _ = Pr{let y ← (do
        let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        let kemMat ← sampleMaterial
        prevGame auth sampleInitKey adv x e d ik kemMat.pk kemMat.ct1 kemMat.ct2 κ)}[y = true] :=
        OracleComp.prEvent_bind_congr_of_support' _ _ fun κ _ =>
          stoppedHybrid_hybridAuth_eq_prevGame auth sampleInitKey hHdrSound hEkSound
            hCt1Sound hCt2Sound adv he x d ik κ
    _ = Pr{let y ← (do
        let kemMat ← sampleMaterial
        let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        prevGame auth sampleInitKey adv x e d ik kemMat.pk kemMat.ct1 kemMat.ct2 κ)}[y = true] :=
        (OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq _
    _ = _ := by
        have h := sampleMaterial_bind_challenge (fun pk ct1 ct2 (_ : P.K) => do
          let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
          prevGame auth sampleInitKey adv x e d ik pk ct1 ct2 κ)
        simp only at h
        rw [h]
        rfl

/-- For every `i`, `x`, `d` and `ik`, with `e := i + 1`, `A_κ := hybridAuth auth e ik κ`, and
`S_e^x[A]` the stopped hybrid of version `x` over an authenticator `A` (`S_e^x := S_e^x[auth]`):
`Pr[S_e^x] - Pr[κ ←$ P.EpochKey; S_e^x[A_κ]] = Pr[prevReal x] - Pr[prevKdf x]`. -/
theorem stoppedHybrid_sub_hybridAuth_eq (i : ℕ) (x : Bool) (d : Dummies P) (ik : InitKey) :
    (Pr{let y ← (stoppedHybridExp auth sampleInitKey adv (if x then i + 1 else i) (i + 1)
      ik)}[y = true]).toReal -
    (Pr{let y ← (do
      let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
      stoppedHybridExp (hybridAuth auth (i + 1) ik κ) sampleInitKey adv
        (if x then i + 1 else i) (i + 1) ik)}[y = true]).toReal =
    (Pr{let y ← prevReal auth sampleInitKey adv x (i + 1) d ik}[y = true]).toReal -
    (Pr{let y ← prevKdf auth sampleInitKey adv x (i + 1) d ik}[y = true]).toReal := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hA (κ : P.EpochKey) := prEvent_stoppedRun_idealImpl_authAt_zero auth sampleInitKey
      hHdrSound hEkSound hCt1Sound hCt2Sound (hiddenState auth 1 ik κ)
      (SCKAScheme.hybridMode (if x then 1 else 0)) (fun u => decide (1 ∈ u.exposed)) adv ik
    have hκ : Pr{let y ← (do
        let κ ← ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        stoppedHybridExp (hybridAuth auth (0 + 1) ik κ) sampleInitKey adv
          (if x then 0 + 1 else 0) (0 + 1) ik)}[y = true] =
        Pr{let y ← (stoppedHybridExp auth sampleInitKey adv (if x then 0 + 1 else 0) (0 + 1)
          ik)}[y = true] := by
      rw [← (OracleComp.EvalDistEq.bind_const ($ᵗ P.EpochKey : ProbComp P.EpochKey)
        (stoppedHybridExp auth sampleInitKey adv (if x then 0 + 1 else 0) (0 + 1)
          ik)).prEvent_eq]
      exact OracleComp.prEvent_bind_congr_of_support' _ _ fun κ _ => hA κ
    have hz : Pr{let y ← prevReal auth sampleInitKey adv x (0 + 1) d ik}[y = true] =
        Pr{let y ← prevKdf auth sampleInitKey adv x (0 + 1) d ik}[y = true] := by
      rw [(OracleComp.prEvent_eq_zero_iff _ _).2 fun y hy => ?_,
        (OracleComp.prEvent_eq_zero_iff _ _).2 fun y hy => ?_] <;>
        simp only [prevReal, prevKdf, prevGame, show 0 + 1 = 1 from rfl, ↓reduceIte,
          mem_support_bind_iff, mem_support_pure_iff] at hy <;>
        aesop
    rw [hκ, hz]
    ring
  · have he : 2 ≤ i + 1 := by omega
    have h1 := stoppedHybrid_eq_prevReal auth sampleInitKey hHdrSound hEkSound hCt1Sound
      hCt2Sound adv he x d ik
    have h2 := stoppedHybrid_hybridAuth_eq_prevKdf auth sampleInitKey hHdrSound hEkSound
      hCt1Sound hCt2Sound adv he x d ik
    simp only [Nat.add_sub_cancel] at h1 h2
    rw [h1, h2]

end Prev

end SPQR
