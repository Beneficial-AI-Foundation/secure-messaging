/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.ErasureCode.SPQRReedSolomon.Correctness
public import SecureMessaging.KEM.IncrementalKEM.FromMLKEM.Equivalence
public import SecureMessaging.SCKA.SPQR.Correctness.Relabel
public import SecureMessaging.SCKA.SPQR.Correctness.Relation
public import SecureMessaging.SCKA.SPQR.Instances

/-!
# SPQR correctness

Let:

* `Π := scheme P auth sampleInitKey` be the SPQR SCKA scheme, where `P` holds the incremental
  KEM with explicit coins, the epoch-key derivation and the four erasure-coded streams, `auth` is
  the authenticator, and `sampleInitKey` samples the initial key;
* `G(Adv) := SCKAScheme.correctnessExp Π Adv` be its correctness game for an adversary `Adv`;
* `ε := P.det.toKEM.correctnessError ProbCompRuntime.probComp` be the correctness error of the
  underlying KEM.

The game is the SCKA correctness game (Definition 3.1 and Figure 1 of [SCKA]). The adversary
chooses which party sends and which recorded message each party receives, so it may omit, delay,
reorder, duplicate or replay messages. The game keeps a correctness flag, which becomes false when a
receive refuses a recorded message or when a check on the reported epochs and the output keys fails.

## Main results

If the four stream decoders of `P` are sound for their erasure codes (`StreamDecoder.Sound`) and
`Adv` makes at most `q` send queries, then

* `correctness_error_le`: `1 - Pr[G(Adv) = true] ≤ q · ε`;
* `v1Scheme_correctness_error_le`: the same bound for `v1Scheme`, with `ε` the correctness error of
  ML-KEM-768. Its four SPQR Reed-Solomon codes are correct, so its set-based decoders are sound.

## Proof

The proof reduces SPQR correctness to the correctness of ML-KEM Braid. The Braid proof gives the
same bound for the Braid scheme (`Braid.correctness_error_le`) from an invariant `CorrectnessInv`
and a potential `failurePotential` on Braid game states. Here, `GameState.toBraid` translates each
SPQR game state into a Braid game state, and the invariant and the potential apply to the
translated state. The SPQR invariant adds `Ct1AckInv`. Then
`SCKAScheme.correctness_error_le_of_potential` gives the bound, once each query is shown to preserve
the invariant and to raise the expected potential by at most `ε` for a send and not at all
otherwise:

* if the correctness flag is already false, it stays false and the potential stays `1`;
* a query that delivers no message in `RecvDivergence` is the Braid query on the translated state
  (`sckaCorrectnessImpl_run_toBraid`), so the Braid lemmas apply;
* otherwise the query delivers a plain vector chunk to a party in `ct1Acknowledged`
  (`DeliveryDivergence.ct1Acknowledged_ek`), and it is the Braid query on the translation in which
  that record is an acknowledging vector chunk (`sckaCorrectnessImpl_run_toBraidAck`).

The relabelling in the last case keeps the invariant (`SPQR.Correctness.Relabel`) and the
potential, which does not read recorded messages.

## References

The protocol is Signal's SparsePostQuantumRatchet at revision `f2589fe`, which
implements *The ML-KEM Braid Protocol* (https://signal.org/docs/specifications/mlkembraid/),
sections 2.3 to 2.6. The correctness game follows Definition 3.1, Figure 1, and Appendix B.1 of:

- [SCKA] Auerbach, Dodis, Jost, Katsumata, Schmidt.
  *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols.*
  USENIX Security 2025, https://eprint.iacr.org/2025/2267
-/

@[expose] public section

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic
open ErasureCodePayload.Streaming

namespace SPQR

open Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)

variable [DecidableEq P.EpochKey] (sampleInitKey : ProbComp InitKey)

/-! ### Preservation and drift -/

/-- With sound stream decoders, every query of the SPQR correctness game preserves the Braid
invariant on the translated state together with `Ct1AckInv`. -/
theorem correctnessImpl_preserves_correctnessInv
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2) (ik : InitKey) :
    QueryImpl.PreservesInv (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey))
      (fun s : GameState P AuthState =>
        Braid.CorrectnessInv auth ik s.toBraid ∧ Ct1AckInv s)
    := by
  intro t s ⟨hs, hack⟩ z hz
  refine ⟨?_, sckaCorrectnessImpl_preserves_ct1AckInv auth sampleInitKey t s hack z hz⟩
  have hbraid := Braid.correctnessImpl_preserves_correctnessInv (P := P.toBraid) auth
    P.det.toRandLeak sampleInitKey hHdrSound hEkSound hCt1Sound hCt2Sound ik
  rcases hs with hsf | ⟨T, hT⟩
  · exact Or.inl (SCKAScheme.sckaCorrectnessImpl_preserves_correct_eq_false _ t s hsf z hz)
  by_cases hdiv : DeliveryDivergence s t
  · obtain ⟨party, n, core, dec, chunk, tsnd, rfl, hst, hmsg⟩ :=
      DeliveryDivergence.ct1Acknowledged_ek hT.control hT.statePair hack hdiv
    have hmem : GameState.toBraid z.2 ∈ support ((fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey)
          (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
            else SCKAScheme.sckaCorrectnessSpec.ORecvB n)).run s) := by
      rw [support_map]
      exact Set.mem_image_of_mem _ hz
    rw [sckaCorrectnessImpl_run_toBraidAck auth sampleInitKey s party n core dec chunk
      tsnd hst hmsg, support_map] at hmem
    obtain ⟨z', hz', hzz⟩ := hmem
    have hAck := hbraid _ _
      (Or.inr ⟨T, transcriptConsistent_toBraidAck auth hT party n hst hmsg⟩) z' hz'
    rw [← hzz]
    refine correctnessInv_restore auth party n hmsg ?_ hAck
    exact Braid.messagesAt_of_mem_support_recv (P := P.toBraid) auth P.det.toRandLeak
      sampleInitKey party n hz' _
  · have hmem : GameState.toBraid z.2 ∈ support ((fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey) t).run s) := by
      rw [support_map]
      exact Set.mem_image_of_mem _ hz
    rw [sckaCorrectnessImpl_run_toBraid auth sampleInitKey s t hdiv, support_map] at hmem
    obtain ⟨z', hz', hzz⟩ := hmem
    rw [← hzz]
    exact hbraid _ _ (Or.inr ⟨T, hT⟩) z' hz'

/-- With sound stream decoders, from a state whose translation satisfies the Braid correctness
invariant `CorrectnessInv` and that satisfies `Ct1AckInv`, one query of the SPQR correctness game
raises the expected failure potential of the translated state by at most the KEM correctness error
for a send query, and not at all for other queries. -/
theorem wp_failurePotential_query_le [DecidableEq P.K]
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2) (ik : InitKey)
    (t : (SCKAScheme.sckaCorrectnessSpec (Chunked.Message P.Sym)).Domain)
    (s : GameState P AuthState)
    (hs : Braid.CorrectnessInv auth ik s.toBraid) (hack : Ct1AckInv s) :
    wp ((SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey) t).run s)
        (fun z => Braid.failurePotential (GameState.toBraid z.2)) ≤
      Braid.failurePotential s.toBraid +
        if SCKAScheme.isSendQuery (Rho := Chunked.Message P.Sym) t
        then P.det.toKEM.correctnessError ProbCompRuntime.probComp else 0
    := by
  have hbraid := Braid.wp_failurePotential_query_le (P := P.toBraid) auth P.det.toRandLeak
    sampleInitKey hHdrSound hEkSound hCt1Sound hCt2Sound ik
  rcases hs with hsf | ⟨T, hT⟩
  · -- A false flag stays false, and the potential stays `1`.
    have hsf' : s.correct = false := hsf
    have h1 : Braid.failurePotential s.toBraid = 1 := by
      simp [Braid.failurePotential, GameState.toBraid, hsf']
    rw [h1]
    refine le_trans (wp_le_const_of_support _ fun z hz => ?_) le_self_add
    have hzf := SCKAScheme.sckaCorrectnessImpl_preserves_correct_eq_false _ t s hsf z hz
    simp [Braid.failurePotential, GameState.toBraid, hzf]
  by_cases hdiv : DeliveryDivergence s t
  · obtain ⟨party, n, core, dec, chunk, tsnd, rfl, hst, hmsg⟩ :=
      DeliveryDivergence.ct1Acknowledged_ek hT.control hT.statePair hack hdiv
    have hAck : Braid.CorrectnessInv auth ik (s.toBraidAck party n) :=
      Or.inr ⟨T, transcriptConsistent_toBraidAck auth hT party n hst hmsg⟩
    calc wp ((SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey)
            (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
              else SCKAScheme.sckaCorrectnessSpec.ORecvB n)).run s)
          (fun z => Braid.failurePotential (GameState.toBraid z.2))
        = wp ((fun z => GameState.toBraid z.2) <$>
            (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey)
              (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
                else SCKAScheme.sckaCorrectnessSpec.ORecvB n)).run s)
            Braid.failurePotential := by rw [wp_map]; rfl
      _ = wp ((SCKAScheme.sckaCorrectnessImpl
            (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey)
            (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
              else SCKAScheme.sckaCorrectnessSpec.ORecvB n)).run (s.toBraidAck party n))
            (fun z => Braid.failurePotential z.2) := by
          rw [sckaCorrectnessImpl_run_toBraidAck auth sampleInitKey s party n core dec
            chunk tsnd hst hmsg, wp_map]
          congr 1
          funext z
          cases party <;> rfl
      _ ≤ Braid.failurePotential (s.toBraidAck party n) +
            if SCKAScheme.isSendQuery (Rho := Braid.Message P.Sym)
              (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
                else SCKAScheme.sckaCorrectnessSpec.ORecvB n)
            then P.det.toKEM.correctnessError ProbCompRuntime.probComp else 0 :=
          hbraid _ _ hAck
      _ = _ := by cases party <;> rfl
  · calc wp ((SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey) t).run s)
          (fun z => Braid.failurePotential (GameState.toBraid z.2))
        = wp ((fun z => GameState.toBraid z.2) <$>
            (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey) t).run s)
            Braid.failurePotential := by rw [wp_map]; rfl
      _ = wp ((SCKAScheme.sckaCorrectnessImpl
            (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey) t).run
            s.toBraid) (fun z => Braid.failurePotential z.2) := by
          rw [sckaCorrectnessImpl_run_toBraid auth sampleInitKey s t hdiv, wp_map]
          rfl
      _ ≤ Braid.failurePotential s.toBraid +
            if SCKAScheme.isSendQuery (Rho := Braid.Message P.Sym) t
            then P.det.toKEM.correctnessError ProbCompRuntime.probComp else 0 :=
          hbraid t _ (Or.inr ⟨T, hT⟩)
      _ = _ := by rcases t with ((((n | u) | u) | n) | n) <;> rfl

end SPQR

/-! ### The correctness bound -/

namespace SPQR

open Chunked

/-- With sound stream decoders, every adversary making at most `q` sends across both parties causes
a false correctness flag with probability at most `q` times the KEM correctness error. -/
-- ANCHOR: SPQR_correctness_error_le
theorem correctness_error_le
    (P : SPQR.Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (sampleInitKey : ProbComp InitKey)
    (hHdrSound : P.decHdr.Sound P.ecpHdr)
    (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1)
    (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Chunked.Message P.Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    1 - Pr{let x ← SCKAScheme.correctnessExp (scheme P auth sampleInitKey) adv}[x = true] ≤
      (q : ℝ≥0∞) * P.det.toKEM.correctnessError ProbCompRuntime.probComp
-- ANCHOR_END: SPQR_correctness_error_le
    := by
  refine SCKAScheme.correctness_error_le_of_potential (scheme P auth sampleInitKey)
    (fun ik s => Braid.CorrectnessInv auth ik (GameState.toBraid s) ∧ Ct1AckInv s)
    (fun s => Braid.failurePotential (GameState.toBraid s)) _ ?_ ?_
    (correctnessImpl_preserves_correctnessInv auth sampleInitKey
      hHdrSound hEkSound hCt1Sound hCt2Sound)
    (fun ik t s hs => wp_failurePotential_query_le auth sampleInitKey
      hHdrSound hEkSound hCt1Sound hCt2Sound ik t s hs.1 hs.2) adv q hq
  · intro s hs
    simp [Braid.failurePotential, GameState.toBraid, hs]
  · intro ik _ stA hA stB hB
    simp only [scheme, mem_support_pure_iff] at hA hB
    subst hA hB
    refine ⟨⟨Or.inr ⟨_, Braid.transcriptConsistent_initGameState (P := P.toBraid) auth ik⟩,
      ?_⟩, ?_⟩
    · intro party n msg tsnd h
      cases party <;> simp [SCKAScheme.initGameState, GameState.messagesAt] at h
    · change Braid.failurePotential
        (SCKAScheme.initGameState (Braid.initA P.toBraid auth ik)
          (Braid.initB P.toBraid auth ik)) = 0
      simp [Braid.failurePotential, Braid.currentEpochFailure,
        Braid.pairFailure, SCKAScheme.initGameState, Braid.initA, Braid.initB,
        Braid.State.controlPosition, Braid.State.epoch]

open ErasureCode.SPQRReedSolomon (Chunk GF16 erasureCode_correct) in
/-- The bound of `correctness_error_le` for `v1Scheme`. The four SPQR Reed-Solomon codes are
correct, and `ε` is the correctness error of ML-KEM-768. -/
-- ANCHOR: SPQR_v1Scheme_correctness_error_le
theorem v1Scheme_correctness_error_le {InitKey AuthState EpochKey Mac : Type}
    [DecidableEq EpochKey]
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey)
    (serializeHdr : v1Incremental.PKheader × Mac → Fin 3 → Chunk GF16)
    (parseHdr : (Fin 3 → Chunk GF16) → Option (v1Incremental.PKheader × Mac))
    (parseHdr_serializeHdr : ∀ payload, parseHdr (serializeHdr payload) = some payload)
    (serializeEk : v1Incremental.PKvector → Fin 36 → Chunk GF16)
    (parseEk : (Fin 36 → Chunk GF16) → Option v1Incremental.PKvector)
    (parseEk_serializeEk : ∀ payload, parseEk (serializeEk payload) = some payload)
    (serializeCt1 : v1Incremental.C₁ → Fin 30 → Chunk GF16)
    (parseCt1 : (Fin 30 → Chunk GF16) → Option v1Incremental.C₁)
    (parseCt1_serializeCt1 : ∀ payload, parseCt1 (serializeCt1 payload) = some payload)
    (serializeCt2 : v1Incremental.C₂ × Mac → Fin 5 → Chunk GF16)
    (parseCt2 : (Fin 5 → Chunk GF16) → Option (v1Incremental.C₂ × Mac))
    (parseCt2_serializeCt2 : ∀ payload, parseCt2 (serializeCt2 payload) = some payload)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState
      v1Incremental.PKheader (v1Incremental.C₁ × v1Incremental.C₂) Mac)
    (sampleInitKey : ProbComp InitKey)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Chunked.Message (Chunk GF16)))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    1 - Pr{let x ← (SCKAScheme.correctnessExp
        (v1Scheme kdfOK serializeHdr parseHdr parseHdr_serializeHdr serializeEk parseEk
          parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1 serializeCt2 parseCt2
          parseCt2_serializeCt2 auth sampleInitKey) adv)}[x = true] ≤
      (q : ℝ≥0∞) * MLKEM.mlkem768Scheme.correctnessError ProbCompRuntime.probComp
-- ANCHOR_END: SPQR_v1Scheme_correctness_error_le
    := by
  let P₀ := v1Parameters kdfOK serializeHdr parseHdr parseHdr_serializeHdr serializeEk parseEk
    parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1 serializeCt2 parseCt2
    parseCt2_serializeCt2
  let : DecidableEq P₀.K := by
    change DecidableEq MLKEM.SharedSecret
    infer_instance
  let : DecidableEq P₀.EpochKey := by
    change DecidableEq EpochKey
    infer_instance
  let : DecidableEq P₀.Sym := by
    change DecidableEq (Chunk GF16)
    infer_instance
  have hε : v1Det.toKEM.correctnessError ProbCompRuntime.probComp =
      MLKEM.mlkem768Scheme.correctnessError ProbCompRuntime.probComp :=
    MLKEM.mlkemIncrementalDet_correctnessError _ _ _
  rw [← hε]
  exact correctness_error_le P₀ auth sampleInitKey
    (ErasureCodePayload.Streaming.setDecoder_sound _
      (erasureCode_correct 3 (by norm_num) (by norm_num)))
    (ErasureCodePayload.Streaming.setDecoder_sound _
      (erasureCode_correct 36 (by norm_num) (by norm_num)))
    (ErasureCodePayload.Streaming.setDecoder_sound _
      (erasureCode_correct 30 (by norm_num) (by norm_num)))
    (ErasureCodePayload.Streaming.setDecoder_sound _
      (erasureCode_correct 5 (by norm_num) (by norm_num))) adv q hq

end SPQR
