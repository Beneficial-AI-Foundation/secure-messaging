/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Security
import SecureMessaging.SCKA.MLKEMBraid.Construction
import SecureMessaging.SCKA.MLKEMBraid.Correctness.Oracles
import VCVio.OracleComp.QueryTracking.Iter

/-!
# Initial snapshots and an epoch-one ciphertext observation

The trace retains selected initial authenticator states, challenges Bob's first exported key,
and reconstructs the public ciphertext and its tag. It does not deliver the second ciphertext
to Alice and therefore does not invoke decapsulation. The primitive trial keeps the same joint
observations, corruption-dependent refusal and native order of sampling.
-/

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.InitialSnapshot

/-- Joint observations from the initialized schedule. Missing observations remain explicit. -/
structure View (P : Parameters ProbComp) (AuthState : Type) where
  /-- Initial authenticator state, obtained from a selected snapshot. -/
  prior : Option AuthState
  /-- Epoch-one challenge answer, including refusal. -/
  candidate : Option P.EpochKey
  /-- Publicly reconstructed first ciphertext component. -/
  ct1 : Option P.inc.C₁
  /-- Publicly reconstructed second component and ciphertext tag. -/
  ct2Tag : Option (P.inc.C₂ × P.Mac)

/-- Observe selected initial snapshots, an epoch-one challenge and the subsequent public tag.
Recorded message 1 is replayed to cover a first-ciphertext reconstruction threshold of one. -/
def trace (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (snapshots : Finset Bool) :
    OracleComp
      (SCKAScheme.sckaSecuritySpec
        (State P AuthState) (State P AuthState) P.EpochKey
        (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand))
      (View P AuthState) := do
  let spec := SCKAScheme.sckaSecuritySpec
    (State P AuthState) (State P AuthState) P.EpochKey
    (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand)
  let sendA : OracleComp spec (Option (ℕ × Option ℕ × Message P.Sym)) :=
    liftM (spec.query
      (SCKAScheme.sckaSecuritySpec.OCorrectness
        SCKAScheme.sckaCorrectnessSpec.OSendA))
  let sendB : OracleComp spec (Option (ℕ × Option ℕ × Message P.Sym)) :=
    liftM (spec.query
      (SCKAScheme.sckaSecuritySpec.OCorrectness
        SCKAScheme.sckaCorrectnessSpec.OSendB))
  let recvA : ℕ → OracleComp spec (Option (ℕ × Option ℕ)) :=
    fun n => liftM (spec.query
      (SCKAScheme.sckaSecuritySpec.OCorrectness
        (SCKAScheme.sckaCorrectnessSpec.ORecvA n)))
  let recvB : ℕ → OracleComp spec (Option (ℕ × Option ℕ)) :=
    fun n => liftM (spec.query
      (SCKAScheme.sckaSecuritySpec.OCorrectness
        (SCKAScheme.sckaCorrectnessSpec.ORecvB n)))
  let a? ← if true ∈ snapshots then
      do
        let st? ← liftM (spec.query (.inl (.inr ())))
        pure (st?.bind fun st =>
          match st with
          | .keysUnsampled _ a => some a
          | _ => none)
    else pure none
  let b? ← if false ∈ snapshots then
      do
        let st? ← liftM (spec.query (.inr ()))
        pure (st?.bind fun st =>
          match st with
          | .noHeaderReceived _ a _ => some a
          | _ => none)
    else pure none
  for i in List.range P.ecpHdr.ec.nchunk do
    let _ ← sendA
    let _ ← recvB (i + 1)
    pure ()
  let d1 ← (List.range P.ecpCt1.ec.nchunk).foldlM
    (fun (dec : DecoderState P.inc.C₁ P.Sym) i => do
      let answer ← sendB
      let _ ← recvA (i + 1)
      pure (match answer with
        | some (_, _, msg) =>
            match msg.data with
            | some chunk => dec.addChunk chunk
            | none => dec
        | none => dec))
    (DecoderState.empty P.ecpCt1)
  let _ ← recvA 1
  let candidate ← liftM (spec.query (.inl (.inl (.inr 1))))
  for i in List.range P.ecpEk.ec.nchunk do
    let _ ← sendA
    let _ ← recvB (P.ecpHdr.ec.nchunk + i + 1)
    pure ()
  let d2 ← (List.range P.ecpCt2.ec.nchunk).foldlM
    (fun (dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym) _ => do
      let answer ← sendB
      pure (match answer with
        | some (_, _, msg) =>
            match msg.data with
            | some chunk => dec.addChunk chunk
            | none => dec
        | none => dec))
    (DecoderState.empty P.ecpCt2)
  pure {
    prior := match a? with
      | some a => some a
      | none => b?
    candidate := candidate
    ct1 := d1.decodedPayload
    ct2Tag := d2.decodedPayload }

/-- Reject a complete candidate observation exactly when its ciphertext tag fails verification
under the saved initial state updated with that candidate. -/
def decision (P : Parameters ProbComp) {AuthState : Type}
    (auth : RatchetedAuthenticator (Vector UInt8 32)
      P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (v : View P AuthState) : Bool :=
  match v.prior, v.candidate, v.ct1, v.ct2Tag with
  | some a, some x, some c1, some (c2, tag) =>
      !(auth.verifyCiphertext (auth.update a 1 x) 1 (c1, c2) tag)
  | _, _, _, _ => false

/-- The native-game adversary obtained by applying the rejection test to the joint trace. -/
def adversary (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator (Vector UInt8 32)
      P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (snapshots : Finset Bool) :
    OracleComp
      (SCKAScheme.sckaSecuritySpec
        (State P AuthState) (State P AuthState) P.EpochKey
        (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand)) Bool :=
  decision P auth <$> trace P irl snapshots

/-- The correlated primitive trial, with refusal determined by the selected initial footprints.
Only an eligible random challenge draws a fresh candidate; the protocol tag always uses the
actual encapsulated key. -/
def primitiveTrial (P : Parameters ProbComp) {AuthState : Type}
    [SampleableType P.EpochKey]
    (auth : RatchetedAuthenticator (Vector UInt8 32)
      P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (snapshots : Finset Bool)
    (vulnA vulnB : SCKAScheme.VulnerableEpochs
      (State P AuthState) (SendRand irl.KeygenRand irl.Encaps1Rand))
    (b : Bool) : ProbComp (View P AuthState) := do
  let ik ← ($ᵗ (Vector UInt8 32))
  let a := auth.init ik 1
  let exposed :=
    (if true ∈ snapshots then
      vulnA.corrupt (initA P auth ik) else ∅) ∪
    (if false ∈ snapshots then
      vulnB.corrupt (initB P auth ik) else ∅)
  let (pk, _) ← P.kem.keygen
  let (es, c1, k) ← P.inc.encaps1 (P.inc.toHeader pk)
  let key := P.kdfOK k 1
  let candidate ←
    if 1 ∈ exposed then pure none
    else if b then some <$> ($ᵗ P.EpochKey)
    else pure (some key)
  let c2 := P.hEnc2.encaps2Det es
    (P.inc.toHeader pk) (P.inc.toVector pk)
  let tag := auth.macCiphertext (auth.update a 1 key) 1 (c1, c2)
  pure {
    prior := if snapshots.Nonempty then some a else none
    candidate := candidate
    ct1 := some c1
    ct2Tag := some (c2, tag) }

/-- Charge the displayed schedule by query class, independently of all oracle responses.
The public query theorem instantiates the charges for sends, all queries and leaking sends. -/
private theorem trace_bound (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym] (irl : P.kem.IncrementalRandLeak P.inc) (snapshots : Finset Bool)
    (p : (SCKAScheme.sckaSecuritySpec (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand)).Domain → Prop)
    [DecidablePred p] (sa sb ra rb ca cb ch : ℕ)
    (hsa : p (SCKAScheme.sckaSecuritySpec.OCorrectness
      SCKAScheme.sckaCorrectnessSpec.OSendA) → 0 < sa)
    (hsb : p (SCKAScheme.sckaSecuritySpec.OCorrectness
      SCKAScheme.sckaCorrectnessSpec.OSendB) → 0 < sb)
    (hra : ∀ n, p (SCKAScheme.sckaSecuritySpec.OCorrectness
      (SCKAScheme.sckaCorrectnessSpec.ORecvA n)) → 0 < ra)
    (hrb : ∀ n, p (SCKAScheme.sckaSecuritySpec.OCorrectness
      (SCKAScheme.sckaCorrectnessSpec.ORecvB n)) → 0 < rb)
    (hca : p (.inl (.inr ())) → 0 < ca)
    (hcb : p (.inr ()) → 0 < cb)
    (hch : p (.inl (.inl (.inr 1))) → 0 < ch) :
    (trace P (AuthState := AuthState) irl snapshots).IsQueryBoundP p
      ((if true ∈ snapshots then ca else 0) + (if false ∈ snapshots then cb else 0) +
        P.ecpHdr.ec.nchunk * (sa + rb) + P.ecpCt1.ec.nchunk * (sb + ra) + ra + ch +
        P.ecpEk.ec.nchunk * (sa + rb) + P.ecpCt2.ec.nchunk * sb) := by
  let spec := SCKAScheme.sckaSecuritySpec (State P AuthState) (State P AuthState)
    P.EpochKey (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand)
  have for_bound {α β : Type} (f : α → β → OracleComp spec (ForInStep β)) (n : ℕ)
      (hf : ∀ a b, (f a b).IsQueryBoundP p n) (xs : List α) (b : β) :
      (forIn xs b f).IsQueryBoundP p (xs.length * n) := by
    induction xs generalizing b with
    | nil => simp
    | cons a xs ih =>
        simpa only [List.forIn_cons, List.length_cons, Nat.succ_mul, Nat.add_comm] using
          isQueryBoundP_bind (hf a b) (fun r _ => by
            cases r with
            | done b => exact isQueryBoundP_pure p b _
            | yield b => exact ih b)
  have hsa' : (liftM (spec.query (SCKAScheme.sckaSecuritySpec.OCorrectness
      SCKAScheme.sckaCorrectnessSpec.OSendA)) : OracleComp spec _).IsQueryBoundP p sa := by
    simpa only [isQueryBoundP_query_iff] using hsa
  have hsb' : (liftM (spec.query (SCKAScheme.sckaSecuritySpec.OCorrectness
      SCKAScheme.sckaCorrectnessSpec.OSendB)) : OracleComp spec _).IsQueryBoundP p sb := by
    simpa only [isQueryBoundP_query_iff] using hsb
  have hra' (n : ℕ) : (liftM (spec.query (SCKAScheme.sckaSecuritySpec.OCorrectness
      (SCKAScheme.sckaCorrectnessSpec.ORecvA n))) : OracleComp spec _).IsQueryBoundP p ra := by
    simpa only [isQueryBoundP_query_iff] using hra n
  have hrb' (n : ℕ) : (liftM (spec.query (SCKAScheme.sckaSecuritySpec.OCorrectness
      (SCKAScheme.sckaCorrectnessSpec.ORecvB n))) : OracleComp spec _).IsQueryBoundP p rb := by
    simpa only [isQueryBoundP_query_iff] using hrb n
  have hca' : (liftM (spec.query (.inl (.inr ()))) : OracleComp spec _).IsQueryBoundP p ca := by
    simpa only [isQueryBoundP_query_iff] using hca
  have hcb' : (liftM (spec.query (.inr ())) : OracleComp spec _).IsQueryBoundP p cb := by
    simpa only [isQueryBoundP_query_iff] using hcb
  have hch' :
      (liftM (spec.query (.inl (.inl (.inr 1)))) : OracleComp spec _).IsQueryBoundP p ch := by
    simpa only [isQueryBoundP_query_iff] using hch
  unfold trace
  dsimp only
  split_ifs with ha hb hb
  all_goals simp only [pure_bind, Nat.add_assoc, Nat.zero_add, Nat.add_zero]
  all_goals first | refine isQueryBoundP_bind hca' (fun _ _ => ?_) | skip
  all_goals first | refine isQueryBoundP_bind hcb' (fun _ _ => ?_) | skip
  all_goals
    refine isQueryBoundP_bind (n := P.ecpHdr.ec.nchunk * (sa + rb)) ?_ (fun _ _ => ?_)
    · simpa only [List.length_range] using for_bound _ (sa + rb)
        (fun i _ => isQueryBoundP_bind hsa' (fun _ _ => by
          simpa only [bind_pure_comp, isQueryBoundP_map_iff] using hrb' (i + 1)))
        (List.range P.ecpHdr.ec.nchunk) PUnit.unit
    · refine isQueryBoundP_bind (n := P.ecpCt1.ec.nchunk * (sb + ra)) ?_ (fun _ _ => ?_)
      · simpa only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul] using
          OracleComp.isQueryBoundP_listFoldlM (k := fun _ => sb + ra)
            (fun _ i => isQueryBoundP_bind hsb' (fun _ _ => by
              simpa only [bind_pure_comp, isQueryBoundP_map_iff] using hra' (i + 1)))
            (DecoderState.empty P.ecpCt1) (List.range P.ecpCt1.ec.nchunk)
      · refine isQueryBoundP_bind (hra' 1) (fun _ _ => ?_)
        refine isQueryBoundP_bind hch' (fun _ _ => ?_)
        refine isQueryBoundP_bind (n := P.ecpEk.ec.nchunk * (sa + rb)) ?_ (fun _ _ => ?_)
        · simpa only [List.length_range] using for_bound _ (sa + rb)
            (fun i _ => isQueryBoundP_bind hsa' (fun _ _ => by
              simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
                hrb' (P.ecpHdr.ec.nchunk + i + 1)))
            (List.range P.ecpEk.ec.nchunk) PUnit.unit
        · simp only [bind_pure_comp, isQueryBoundP_map_iff]
          simpa only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul] using
            OracleComp.isQueryBoundP_listFoldlM (k := fun _ => sb)
              (fun _ _ => by simpa only [bind_pure_comp, isQueryBoundP_map_iff] using hsb')
              (DecoderState.empty P.ecpCt2) (List.range P.ecpCt2.ec.nchunk)

/-- Structural bounds for ordinary sends, all queries and randomness-leaking sends.
The bounds hold for arbitrary oracle responses, including refused challenges. -/
theorem adversary_queryBounds
    (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator (Vector UInt8 32)
      P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (snapshots : Finset Bool) :
    let H := P.ecpHdr.ec.nchunk
    let C := P.ecpCt1.ec.nchunk
    let E := P.ecpEk.ec.nchunk
    let T := P.ecpCt2.ec.nchunk
    let A := adversary P auth irl snapshots
    A.IsQueryBoundP
        (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true)
        (H + C + E + T) ∧
      A.IsTotalQueryBound (2 * (H + C + E) + T + 2 + snapshots.card) ∧
      A.IsQueryBoundP
        (fun t =>
          (match t with
            | SCKAScheme.sckaSecuritySpec.OSendArleak => true
            | SCKAScheme.sckaSecuritySpec.OSendBrleak => true
            | _ => false) = true) 0 := by
  dsimp only
  unfold adversary
  rw [← isQueryBoundP_true_iff]
  simp only [isQueryBoundP_map_iff]
  refine ⟨?_, ?_, ?_⟩
  · convert trace_bound P (AuthState := AuthState) irl snapshots
      (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) 1 1 0 0 0 0 0
      (by simp) (by simp) (by simp [SCKAScheme.sckaSecuritySpec.isSendQuery,
        SCKAScheme.isSendQuery])
      (by simp [SCKAScheme.sckaSecuritySpec.isSendQuery, SCKAScheme.isSendQuery])
      (by simp [SCKAScheme.sckaSecuritySpec.isSendQuery])
      (by simp [SCKAScheme.sckaSecuritySpec.isSendQuery])
      (by simp [SCKAScheme.sckaSecuritySpec.isSendQuery]) using 1
    simp
  · have hcard : snapshots.card =
        (if true ∈ snapshots then 1 else 0) + (if false ∈ snapshots then 1 else 0) := by
      fin_cases snapshots <;> decide
    convert trace_bound P (AuthState := AuthState) irl snapshots (fun _ => True) 1 1 1 1 1 1 1
      (by simp)
      (by simp)
      (by simp)
      (by simp)
      (by simp)
      (by simp)
      (by simp) using 1
    omega
  · convert trace_bound P (AuthState := AuthState) irl snapshots
      (fun t => (match t with
        | SCKAScheme.sckaSecuritySpec.OSendArleak => true
        | SCKAScheme.sckaSecuritySpec.OSendBrleak => true
        | _ => false) = true) 0 0 0 0 0 0 0
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) using 1
    all_goals first | simp | (funext t; rcases t with (((((t | u) | u) | n) | u) | u) <;> rfl)

/-- Honest consecutive decoder prefixes, used by the streaming phases of `trace_law`. -/
private theorem prefix_decoded {M Sym : Type} (ecp : ErasureCodePayload M Sym)
    (hcorrect : ecp.ec.Correct) (payload : M) (n : ℕ) (hn : n ≤ ecp.ec.N) :
    (DecoderState.mk ecp (ecp.payloadChunks payload
      ((Finset.range n).image ecp.counterIndex))).decodedPayload =
      if ecp.ec.nchunk ≤ n then some payload else none := by
  classical
  have hinj : Set.InjOn ecp.counterIndex (Finset.range n) := by
    intro i hi j hj hij
    have hi' : i < ecp.ec.N := lt_of_lt_of_le (Finset.mem_range.mp hi) hn
    have hj' : j < ecp.ec.N := lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    have := congrArg Fin.val hij
    simpa only [ErasureCodePayload.counterIndex, Nat.mod_eq_of_lt hi',
      Nat.mod_eq_of_lt hj'] using this
  have hcard : ((Finset.range n).image ecp.counterIndex).card = n := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  split_ifs with h
  · exact DecoderState.decodedPayload_payloadChunks ecp hcorrect payload _
      (by rw [hcard]; exact h)
  · exact ErasureCodePayload.decode_payloadChunks_none ecp hcorrect payload _
      (by rw [hcard]; omega)

/-- One recorded header delivery, used by the header phase of `trace_law`. -/
private theorem header_step (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym] [DecidableEq P.EpochKey]
    (auth : RatchetedAuthenticator (Vector UInt8 32) P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (hHdr : P.ecpHdr.ec.Correct)
    (s : GameState P AuthState) (a : AuthState) (pk : P.PK) (sk : P.SK) (i : ℕ)
    (hi : i < P.ecpHdr.ec.nchunk) (hcount : s.nA = i)
    (ha : s.stA = .keysSampled 1 a sk (P.inc.toVector pk)
      ⟨P.ecpHdr, (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk)), i⟩)
    (hb : s.stB = .noHeaderReceived 1 a ⟨P.ecpHdr,
      P.ecpHdr.payloadChunks (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk))
        ((Finset.range i).image P.ecpHdr.counterIndex)⟩) :
    let payload := (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk))
    let msg : Message P.Sym := ⟨1, .hdr, some (P.ecpHdr.encode payload i)⟩
    let stA := State.keysSampled 1 a sk (P.inc.toVector pk) ⟨P.ecpHdr, payload, i + 1⟩
    let stB := if P.ecpHdr.ec.nchunk ≤ i + 1 then
      State.headerReceived 1 a (P.inc.toHeader pk) (DecoderState.empty P.ecpEk)
      else State.noHeaderReceived 1 a ⟨P.ecpHdr,
        P.ecpHdr.payloadChunks payload ((Finset.range (i + 1)).image P.ecpHdr.counterIndex)⟩
    let s1 := SCKAScheme.sendAUpdate s none msg 0 stA
    (do
      let _ ← SCKAScheme.oracleSendA (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
      SCKAScheme.oracleRecvB (scheme P auth irl ($ᵗ (Vector UInt8 32))) (i + 1)).run s =
      pure (some (0, none), SCKAScheme.recvBUpdate s1 0 none 0 stB) := by
  classical
  dsimp only
  rw [StateT.run_bind, MLKEMBraid.oracleSendA_run_eq, ha]
  simp only [send, EncoderState.nextChunk, map_pure, pure_bind]
  apply MLKEMBraid.oracleRecvB_run_eq_of_ok auth irl ($ᵗ (Vector UInt8 32))
    (msg := ⟨1, .hdr, some (P.ecpHdr.encode
      (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk)) i)⟩)
    (tsnd := 0)
    (r := ⟨0, none, if P.ecpHdr.ec.nchunk ≤ i + 1 then
      State.headerReceived 1 a (P.inc.toHeader pk) (DecoderState.empty P.ecpEk)
      else State.noHeaderReceived 1 a ⟨P.ecpHdr,
        P.ecpHdr.payloadChunks (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk))
          ((Finset.range (i + 1)).image P.ecpHdr.counterIndex)⟩⟩)
  · simp [SCKAScheme.sendAUpdate, hcount]
  · have hadd := DecoderState.addChunk_payloadChunks P.ecpHdr
      (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk))
      ((Finset.range i).image P.ecpHdr.counterIndex) i
    have hrange : insert (P.ecpHdr.counterIndex i)
        ((Finset.range i).image P.ecpHdr.counterIndex) =
        (Finset.range (i + 1)).image P.ecpHdr.counterIndex := by
      rw [Finset.range_add_one, Finset.image_insert]
    rw [hrange] at hadd
    have hd := prefix_decoded P.ecpHdr hHdr
      (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk)) (i + 1)
      (by have := P.ecpHdr.ec.nchunk_le_N; omega)
    by_cases h : P.ecpHdr.ec.nchunk ≤ i + 1 <;>
      simp [SCKAScheme.sendAUpdate, hb, receive, Message.wellFormed, hadd, hd, h,
        auth.verifyHeader_correct]

/-- The deterministic header tail and its retained bookkeeping for `trace_law`. -/
private theorem header_tail (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym] [DecidableEq P.EpochKey]
    (auth : RatchetedAuthenticator (Vector UInt8 32) P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (hHdr : P.ecpHdr.ec.Correct)
    (a : AuthState) (pk : P.PK) (sk : P.SK) (len i : ℕ)
    (s : GameState P AuthState) (hbound : i + len ≤ P.ecpHdr.ec.nchunk)
    (hcount : s.nA = i)
    (ha : s.stA = .keysSampled 1 a sk (P.inc.toVector pk)
      ⟨P.ecpHdr, (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk)), i⟩)
    (hb : s.stB = if P.ecpHdr.ec.nchunk ≤ i then
      .headerReceived 1 a (P.inc.toHeader pk) (DecoderState.empty P.ecpEk)
      else .noHeaderReceived 1 a ⟨P.ecpHdr,
        P.ecpHdr.payloadChunks (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk))
          ((Finset.range i).image P.ecpHdr.counterIndex)⟩) :
    ∃ s' : GameState P AuthState,
      ((for j in List.range' i len do
        let _ ← SCKAScheme.oracleSendA (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
        let _ ← SCKAScheme.oracleRecvB (scheme P auth irl ($ᵗ (Vector UInt8 32))) (j + 1)
        pure ()) : StateT (GameState P AuthState) ProbComp PUnit).run s = pure (PUnit.unit, s') ∧
      s'.stA = .keysSampled 1 a sk (P.inc.toVector pk)
        ⟨P.ecpHdr, (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk)), i + len⟩ ∧
      s'.stB = (if P.ecpHdr.ec.nchunk ≤ i + len then
        .headerReceived 1 a (P.inc.toHeader pk) (DecoderState.empty P.ecpEk)
        else .noHeaderReceived 1 a ⟨P.ecpHdr,
          P.ecpHdr.payloadChunks (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk))
            ((Finset.range (i + len)).image P.ecpHdr.counterIndex)⟩) ∧
      s'.nA = i + len ∧ s'.nB = s.nB ∧ s'.keyA = s.keyA ∧ s'.keyB = s.keyB ∧
      s'.msgB = s.msgB ∧ s'.exposed = s.exposed ∧ s'.challenged = s.challenged := by
  classical
  induction len generalizing i s with
  | zero => exact ⟨s, by simp, by simpa using ha, by simpa using hb,
      by simpa using hcount, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ len ih =>
      have hi : i < P.ecpHdr.ec.nchunk := by omega
      have hb' : s.stB = .noHeaderReceived 1 a ⟨P.ecpHdr,
          P.ecpHdr.payloadChunks (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk))
            ((Finset.range i).image P.ecpHdr.counterIndex)⟩ := by
        simpa only [if_neg (by omega : ¬ P.ecpHdr.ec.nchunk ≤ i)] using hb
      let payload := (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk))
      let msg : Message P.Sym := ⟨1, .hdr, some (P.ecpHdr.encode payload i)⟩
      let stA := State.keysSampled 1 a sk (P.inc.toVector pk) ⟨P.ecpHdr, payload, i + 1⟩
      let stB := if P.ecpHdr.ec.nchunk ≤ i + 1 then
        State.headerReceived 1 a (P.inc.toHeader pk) (DecoderState.empty P.ecpEk)
        else State.noHeaderReceived 1 a ⟨P.ecpHdr,
          P.ecpHdr.payloadChunks payload ((Finset.range (i + 1)).image P.ecpHdr.counterIndex)⟩
      let next := SCKAScheme.recvBUpdate (SCKAScheme.sendAUpdate s none msg 0 stA) 0 none 0 stB
      have hstep : (do
          let _ ← SCKAScheme.oracleSendA (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
          SCKAScheme.oracleRecvB (scheme P auth irl ($ᵗ (Vector UInt8 32))) (i + 1)).run s =
          pure (some (0, none), next) :=
        header_step P auth irl hHdr s a pk sk i hi hcount ha hb'
      obtain ⟨s', hrun, hA, hB, hN, hNB, hKA, hKB, hMB, hX, hC⟩ :=
        ih (i + 1) next (by omega)
          (by simp [next, SCKAScheme.recvBUpdate, SCKAScheme.sendAUpdate, hcount])
          (by simp [next, SCKAScheme.recvBUpdate, SCKAScheme.sendAUpdate, stA, payload])
          (by simp [next, SCKAScheme.recvBUpdate, SCKAScheme.sendAUpdate, stB, payload])
      refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hcons :
            (for j in List.range' i (len + 1) do
              let _ ← SCKAScheme.oracleSendA (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
              let _ ← SCKAScheme.oracleRecvB (scheme P auth irl ($ᵗ (Vector UInt8 32))) (j + 1)
              pure ()) = (do
              let _ ← (do
                let _ ← SCKAScheme.oracleSendA (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
                SCKAScheme.oracleRecvB (scheme P auth irl ($ᵗ (Vector UInt8 32))) (i + 1))
              for j in List.range' (i + 1) len do
                let _ ← SCKAScheme.oracleSendA (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
                let _ ← SCKAScheme.oracleRecvB (scheme P auth irl ($ᵗ (Vector UInt8 32))) (j + 1)
                pure ()) := by simp [List.range'_succ, List.forIn_cons, bind_assoc]
        rw [hcons, StateT.run_bind, hstep, pure_bind]
        exact hrun
      · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hA
      · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hB
      · omega
      · simpa only [next, SCKAScheme.recvBUpdate, SCKAScheme.sendAUpdate] using hNB
      · simpa only [next, SCKAScheme.recvBUpdate, SCKAScheme.sendAUpdate] using hKA
      · simpa only [next, SCKAScheme.recvBUpdate, SCKAScheme.sendAUpdate] using hKB
      · simpa only [next, SCKAScheme.recvBUpdate, SCKAScheme.sendAUpdate] using hMB
      · simpa only [next, SCKAScheme.recvBUpdate, SCKAScheme.sendAUpdate] using hX
      · simpa only [next, SCKAScheme.recvBUpdate, SCKAScheme.sendAUpdate] using hC

/-- Extract native key generation at the first header send; used by `initial_header` and
ultimately `trace_law`. This is the archived `header_sample` phase, with its dependency name
made explicit. -/
private theorem header_sample_step (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym] [DecidableEq P.EpochKey]
    (auth : RatchetedAuthenticator (Vector UInt8 32) P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (s : GameState P AuthState) (a : AuthState) (ha : s.stA = .keysUnsampled 1 a) :
    ((for j in List.range P.ecpHdr.ec.nchunk do
      let _ ← SCKAScheme.oracleSendA (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
      let _ ← SCKAScheme.oracleRecvB (scheme P auth irl ($ᵗ (Vector UInt8 32))) (j + 1)
      pure ()) : StateT (GameState P AuthState) ProbComp PUnit).run s =
    (do
      let (pk, sk) ← P.kem.keygen
      ((for j in List.range P.ecpHdr.ec.nchunk do
        let _ ← SCKAScheme.oracleSendA (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
        let _ ← SCKAScheme.oracleRecvB (scheme P auth irl ($ᵗ (Vector UInt8 32))) (j + 1)
        pure ()) : StateT (GameState P AuthState) ProbComp PUnit).run
          {s with stA := (.keysSampled 1 a sk (P.inc.toVector pk)
            (EncoderState.init P.ecpHdr
              (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk))))}) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt P.ecpHdr.ec.nchunk_pos)
  simp only [hn, List.range_succ_eq_map, List.forIn_cons, bind_assoc, pure_bind,
    StateT.run_bind, StateT.run_pure, MLKEMBraid.oracleSendA_run_eq, ha,
    send_keysUnsampled_eq, map_eq_pure_bind, bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨pk, sk⟩
  simp only [send, EncoderState.nextChunk, pure_bind]
  rfl

/-- The sampled header phase with exact protocol endpoints and retained game fields.
Its future public consumer is `trace_law`. -/
private theorem initial_header (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym] [DecidableEq P.EpochKey]
    (auth : RatchetedAuthenticator (Vector UInt8 32) P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (hHdr : P.ecpHdr.ec.Correct)
    (s : GameState P AuthState) (a : AuthState) (ha : s.stA = .keysUnsampled 1 a)
    (hb : s.stB = .noHeaderReceived 1 a (DecoderState.empty P.ecpHdr)) (hn : s.nA = 0) :
    ∃ finish : P.PK × P.SK → GameState P AuthState,
      ((for j in List.range P.ecpHdr.ec.nchunk do
        let _ ← SCKAScheme.oracleSendA (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
        let _ ← SCKAScheme.oracleRecvB (scheme P auth irl ($ᵗ (Vector UInt8 32))) (j + 1)
        pure ()) : StateT (GameState P AuthState) ProbComp PUnit).run s =
        (do let kp ← P.kem.keygen; pure (PUnit.unit, finish kp)) ∧
      ∀ pk sk,
        (finish (pk, sk)).stA = .keysSampled 1 a sk (P.inc.toVector pk)
          ⟨P.ecpHdr, (P.inc.toHeader pk, auth.macHeader a 1 (P.inc.toHeader pk)),
            P.ecpHdr.ec.nchunk⟩ ∧
        (finish (pk, sk)).stB = .headerReceived 1 a (P.inc.toHeader pk)
          (DecoderState.empty P.ecpEk) ∧
        (finish (pk, sk)).nA = P.ecpHdr.ec.nchunk ∧ (finish (pk, sk)).nB = s.nB ∧
        (finish (pk, sk)).keyA = s.keyA ∧ (finish (pk, sk)).keyB = s.keyB ∧
        (finish (pk, sk)).msgB = s.msgB ∧ (finish (pk, sk)).exposed = s.exposed ∧
        (finish (pk, sk)).challenged = s.challenged := by
  classical
  let sampled (kp : P.PK × P.SK) : GameState P AuthState :=
    {s with stA := (.keysSampled 1 a kp.2 (P.inc.toVector kp.1)
      (EncoderState.init P.ecpHdr
        (P.inc.toHeader kp.1, auth.macHeader a 1 (P.inc.toHeader kp.1))))}
  have ht (kp : P.PK × P.SK) := header_tail P auth irl hHdr a kp.1 kp.2
    P.ecpHdr.ec.nchunk 0 (sampled kp) (by simp) hn rfl (by
      simpa [sampled, P.ecpHdr.ec.nchunk_pos.ne', DecoderState.empty,
        ErasureCodePayload.payloadChunks, ErasureCode.encodeChunks] using hb)
  choose finish hrun hA hB hN hNB hKA hKB hMB hX hC using ht
  refine ⟨finish, ?_, ?_⟩
  · rw [header_sample_step P auth irl s a ha]
    apply bind_congr
    rintro ⟨pk, sk⟩
    simpa only [← List.range_eq_range', Nat.zero_add] using hrun (pk, sk)
  · intro pk sk
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.zero_add] using hA (pk, sk)
    · simpa only [Nat.zero_add, le_refl, ↓reduceIte] using hB (pk, sk)
    · simpa only [Nat.zero_add] using hN (pk, sk)
    · exact hNB (pk, sk)
    · exact hKA (pk, sk)
    · exact hKB (pk, sk)
    · exact hMB (pk, sk)
    · exact hX (pk, sk)
    · exact hC (pk, sk)

/-- A later recorded first-ciphertext delivery, used by the ct1 tail of `trace_law`. -/
private theorem ct1_step (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym] [DecidableEq P.EpochKey]
    (auth : RatchetedAuthenticator (Vector UInt8 32) P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (hCt1 : P.ecpCt1.ec.Correct)
    (s : GameState P AuthState) (a0 a1 : AuthState) (sk : P.SK) (vec : P.inc.PKvector)
    (hdr : P.inc.PKheader) (es : P.inc.St) (c1 : P.inc.C₁) (i : ℕ)
    (hi : i < P.ecpCt1.ec.nchunk) (hcount : s.nB = i)
    (ha : s.stA = .headerSent 1 a0 sk
      ⟨P.ecpCt1, P.ecpCt1.payloadChunks c1 ((Finset.range i).image P.ecpCt1.counterIndex)⟩
      (EncoderState.init P.ecpEk vec))
    (hb : s.stB = .ct1Sampled 1 a1 hdr es c1 ⟨P.ecpCt1, c1, i⟩
      (DecoderState.empty P.ecpEk)) :
    let msg : Message P.Sym := ⟨1, .ct1, some (P.ecpCt1.encode c1 i)⟩
    let stB := State.ct1Sampled 1 a1 hdr es c1 ⟨P.ecpCt1, c1, i + 1⟩
      (DecoderState.empty P.ecpEk)
    let stA := if P.ecpCt1.ec.nchunk ≤ i + 1 then
      State.ct1Received 1 a0 sk c1 (EncoderState.init P.ecpEk vec)
      else State.headerSent 1 a0 sk
        ⟨P.ecpCt1, P.ecpCt1.payloadChunks c1
          ((Finset.range (i + 1)).image P.ecpCt1.counterIndex)⟩
        (EncoderState.init P.ecpEk vec)
    let s1 := SCKAScheme.sendBUpdate s none msg 0 stB
    (do
      let answer ← SCKAScheme.oracleSendB (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
      let _ ← SCKAScheme.oracleRecvA (scheme P auth irl ($ᵗ (Vector UInt8 32))) (i + 1)
      pure answer).run s =
      pure (some (0, none, msg), SCKAScheme.recvAUpdate s1 0 none 0 stA) := by
  classical
  dsimp only
  let msg : Message P.Sym := ⟨1, .ct1, some (P.ecpCt1.encode c1 i)⟩
  let stB := State.ct1Sampled 1 a1 hdr es c1 ⟨P.ecpCt1, c1, i + 1⟩
    (DecoderState.empty P.ecpEk)
  let stA := if P.ecpCt1.ec.nchunk ≤ i + 1 then
    State.ct1Received 1 a0 sk c1 (EncoderState.init P.ecpEk vec)
    else State.headerSent 1 a0 sk
      ⟨P.ecpCt1, P.ecpCt1.payloadChunks c1
        ((Finset.range (i + 1)).image P.ecpCt1.counterIndex)⟩
      (EncoderState.init P.ecpEk vec)
  let s1 := SCKAScheme.sendBUpdate s none msg 0 stB
  have hsend : (SCKAScheme.oracleSendB (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()).run s =
      pure (some (0, none, msg), s1) := by
    rw [MLKEMBraid.oracleSendB_run_eq, hb]
    simp only [send, EncoderState.nextChunk, map_pure]
    rfl
  have hm : s1.msgB (i + 1) = some (msg, 0) := by
    simp [s1, SCKAScheme.sendBUpdate, hcount]
  have hr : receive P auth s1.stA msg = .ok ⟨0, none, stA⟩ := by
    have hadd := DecoderState.addChunk_payloadChunks P.ecpCt1 c1
      ((Finset.range i).image P.ecpCt1.counterIndex) i
    have hrange : insert (P.ecpCt1.counterIndex i)
        ((Finset.range i).image P.ecpCt1.counterIndex) =
        (Finset.range (i + 1)).image P.ecpCt1.counterIndex := by
      rw [Finset.range_add_one, Finset.image_insert]
    rw [hrange] at hadd
    have hd := prefix_decoded P.ecpCt1 hCt1 c1 (i + 1)
      (by have := P.ecpCt1.ec.nchunk_le_N; omega)
    by_cases h : P.ecpCt1.ec.nchunk ≤ i + 1 <;>
      simp [s1, SCKAScheme.sendBUpdate, ha, msg, stA, receive, Message.wellFormed,
        hadd, hd, h]
  have hrecv := MLKEMBraid.oracleRecvA_run_eq_of_ok auth irl ($ᵗ (Vector UInt8 32)) hm hr
  simp only [StateT.run_bind, hsend, pure_bind, hrecv, StateT.run_pure]
  rfl

/-- PMF missing mass and honest real-trial rejection, for the future `game_law` proof. -/
private theorem trial_basics (P : Parameters ProbComp) {AuthState : Type}
    [SampleableType P.EpochKey]
    (auth : RatchetedAuthenticator (Vector UInt8 32) P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (snapshots : Finset Bool)
    (vulnA vulnB : SCKAScheme.VulnerableEpochs (State P AuthState)
      (SendRand irl.KeygenRand irl.Encaps1Rand)) :
    (∀ b : Bool, Pr[⊥ | decision P auth <$>
      primitiveTrial P auth irl snapshots vulnA vulnB b] = 0) ∧
    Pr[= true | decision P auth <$> primitiveTrial P auth irl snapshots vulnA vulnB false] = 0 := by
  constructor
  · intro b
    exact probFailure_of_liftM_PMF _
  · have hreal : ∀ v ∈ support (primitiveTrial P auth irl snapshots vulnA vulnB false),
        decision P auth v = false := by
      intro v hv
      simp only [primitiveTrial, Bool.false_eq_true, ↓reduceIte,
        mem_support_bind_iff] at hv
      obtain ⟨ik, _, ⟨pk, sk⟩, _, ⟨es, c1, k⟩, _, hv⟩ := hv
      dsimp only at hv
      split_ifs at hv with he
      all_goals
        simp only [mem_support_bind_iff, mem_support_pure_iff] at hv
        obtain ⟨candidate, hc, rfl⟩ := hv
        subst candidate
        simp [decision, auth.verifyCiphertext_correct]
    rw [probOutput_eq_zero_iff]
    simp only [support_map, Set.mem_image]
    rintro ⟨v, hv, hdec⟩
    rw [hreal v hv] at hdec
    cases hdec

/-- The first native ciphertext export and delivery, including the public decoder prefix.
The future consumer is the ct1 phase of `trace_law`. -/
private theorem ct1_head (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym] [DecidableEq P.EpochKey]
    (auth : RatchetedAuthenticator (Vector UInt8 32) P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (s : GameState P AuthState) (a : AuthState) (sk : P.SK) (vec : P.inc.PKvector)
    (hdr : P.inc.PKheader) (enc : EncoderState (P.inc.PKheader × P.Mac) P.Sym)
    (ha : s.stA = .keysSampled 1 a sk vec enc)
    (hb : s.stB = .headerReceived 1 a hdr (DecoderState.empty P.ecpEk))
    (hn : s.nB = 0) :
    (do
      let answer ← SCKAScheme.oracleSendB (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
      let _ ← SCKAScheme.oracleRecvA (scheme P auth irl ($ᵗ (Vector UInt8 32))) 1
      pure (match answer with
        | some (_, _, msg) => match msg.data with
          | some chunk => (DecoderState.empty P.ecpCt1).addChunk chunk
          | none => DecoderState.empty P.ecpCt1
        | none => DecoderState.empty P.ecpCt1)).run s =
    (do
      let (es, c1, k) ← P.inc.encaps1 hdr
      let dec := DecoderState.mk P.ecpCt1
        (P.ecpCt1.payloadChunks c1 ((Finset.range 1).image P.ecpCt1.counterIndex))
      let msg : Message P.Sym := ⟨1, .ct1, some (P.ecpCt1.encode c1 0)⟩
      let stB := State.ct1Sampled 1 (auth.update a 1 (P.kdfOK k 1)) hdr es c1
        ⟨P.ecpCt1, c1, 1⟩ (DecoderState.empty P.ecpEk)
      let stA := State.headerSent 1 a sk dec (EncoderState.init P.ecpEk vec)
      let s1 := SCKAScheme.sendBUpdate s (some (1, P.kdfOK k 1)) msg 0 stB
      pure (dec, SCKAScheme.recvAUpdate s1 0 none 0 stA)) := by
  classical
  rw [StateT.run_bind, MLKEMBraid.oracleSendB_run_eq, hb, send_headerReceived_eq]
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨es, c1, k⟩
  have hdec : (DecoderState.empty P.ecpCt1).addChunk (P.ecpCt1.encode c1 0) =
      DecoderState.mk P.ecpCt1
        (P.ecpCt1.payloadChunks c1 ((Finset.range 1).image P.ecpCt1.counterIndex)) := by
    have he : P.ecpCt1.payloadChunks c1 ∅ = ∅ := by
      simp [ErasureCodePayload.payloadChunks, ErasureCode.encodeChunks]
    change (DecoderState.mk P.ecpCt1 ∅).addChunk _ = _
    rw [← he, DecoderState.addChunk_payloadChunks]
    congr 1
  let dec := DecoderState.mk P.ecpCt1
    (P.ecpCt1.payloadChunks c1 ((Finset.range 1).image P.ecpCt1.counterIndex))
  let msg : Message P.Sym := ⟨1, .ct1, some (P.ecpCt1.encode c1 0)⟩
  let stB := State.ct1Sampled 1 (auth.update a 1 (P.kdfOK k 1)) hdr es c1
    ⟨P.ecpCt1, c1, 1⟩ (DecoderState.empty P.ecpEk)
  let stA := State.headerSent 1 a sk dec (EncoderState.init P.ecpEk vec)
  let s1 := SCKAScheme.sendBUpdate s (some (1, P.kdfOK k 1)) msg 0 stB
  have hm : s1.msgB 1 = some (msg, 0) := by
    simp [s1, SCKAScheme.sendBUpdate, hn]
  have hr : receive P auth s1.stA msg = .ok ⟨0, none, stA⟩ := by
    simp [s1, SCKAScheme.sendBUpdate, ha, msg, stA, dec, receive, Message.wellFormed, hdec]
  have hrecv := MLKEMBraid.oracleRecvA_run_eq_of_ok auth irl ($ᵗ (Vector UInt8 32)) hm hr
  change (do
    let p ← (SCKAScheme.oracleRecvA (scheme P auth irl ($ᵗ (Vector UInt8 32))) 1).run s1
    pure ((DecoderState.empty P.ecpCt1).addChunk (P.ecpCt1.encode c1 0), p.2)) =
      pure (dec, SCKAScheme.recvAUpdate s1 0 none 0 stA)
  rw [hrecv]
  simp only [pure_bind, hdec]
  rfl

/-- Joint public-decoder and native-state progress through a consecutive ct1 tail.
The shared local step is introduced from the statement itself; future consumer: `trace_law`. -/
private theorem ct1_joint_tail (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym] [DecidableEq P.EpochKey]
    (auth : RatchetedAuthenticator (Vector UInt8 32) P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (hCt1 : P.ecpCt1.ec.Correct)
    (a0 a1 : AuthState) (sk : P.SK) (vec : P.inc.PKvector)
    (hdr : P.inc.PKheader) (es : P.inc.St) (c1 : P.inc.C₁) (len i : ℕ)
    (s : GameState P AuthState) (dec : DecoderState P.inc.C₁ P.Sym)
    (hi : 0 < i) (hbound : i + len ≤ P.ecpCt1.ec.nchunk) (hcount : s.nB = i)
    (hd : dec = ⟨P.ecpCt1, P.ecpCt1.payloadChunks c1
      ((Finset.range i).image P.ecpCt1.counterIndex)⟩)
    (ha : s.stA = if P.ecpCt1.ec.nchunk ≤ i then
      .ct1Received 1 a0 sk c1 (EncoderState.init P.ecpEk vec)
      else .headerSent 1 a0 sk
        ⟨P.ecpCt1, P.ecpCt1.payloadChunks c1 ((Finset.range i).image P.ecpCt1.counterIndex)⟩
        (EncoderState.init P.ecpEk vec))
    (hb : s.stB = .ct1Sampled 1 a1 hdr es c1 ⟨P.ecpCt1, c1, i⟩
      (DecoderState.empty P.ecpEk)) :
    let cell (d : DecoderState P.inc.C₁ P.Sym) (j : ℕ) :
        StateT (GameState P AuthState) ProbComp (DecoderState P.inc.C₁ P.Sym) := do
      let answer ← SCKAScheme.oracleSendB (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
      let _ ← SCKAScheme.oracleRecvA (scheme P auth irl ($ᵗ (Vector UInt8 32))) (j + 1)
      pure (match answer with
        | some (_, _, msg) => match msg.data with | some chunk => d.addChunk chunk | none => d
        | none => d)
    ∃ s' : GameState P AuthState,
      ((List.range' i len).foldlM cell dec).run s =
        pure (⟨P.ecpCt1, P.ecpCt1.payloadChunks c1
          ((Finset.range (i + len)).image P.ecpCt1.counterIndex)⟩, s') ∧
      s'.stA = (if P.ecpCt1.ec.nchunk ≤ i + len then
        .ct1Received 1 a0 sk c1 (EncoderState.init P.ecpEk vec)
        else .headerSent 1 a0 sk
          ⟨P.ecpCt1, P.ecpCt1.payloadChunks c1
            ((Finset.range (i + len)).image P.ecpCt1.counterIndex)⟩
          (EncoderState.init P.ecpEk vec)) ∧
      s'.stB = .ct1Sampled 1 a1 hdr es c1 ⟨P.ecpCt1, c1, i + len⟩
        (DecoderState.empty P.ecpEk) ∧
      s'.nB = i + len ∧ s'.nA = s.nA ∧ s'.keyA = s.keyA ∧ s'.keyB = s.keyB ∧
      s'.msgB 1 = s.msgB 1 ∧ s'.exposed = s.exposed ∧ s'.challenged = s.challenged := by
  intro cell
  classical
  let collect (d : DecoderState P.inc.C₁ P.Sym)
      (answer : Option (ℕ × Option ℕ × Message P.Sym)) :=
    match answer with
    | some (_, _, msg) => match msg.data with | some chunk => d.addChunk chunk | none => d
    | none => d
  induction len generalizing i s dec with
  | zero => exact ⟨s, by simpa using congrArg (fun d => pure (d, s) :
      DecoderState P.inc.C₁ P.Sym → ProbComp _) hd,
      by simpa using ha, by simpa using hb, by simpa using hcount,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ len ih =>
      have hlt : i < P.ecpCt1.ec.nchunk := by omega
      have ha' : s.stA = .headerSent 1 a0 sk
          ⟨P.ecpCt1, P.ecpCt1.payloadChunks c1 ((Finset.range i).image P.ecpCt1.counterIndex)⟩
          (EncoderState.init P.ecpEk vec) := by
        simpa only [if_neg (by omega : ¬ P.ecpCt1.ec.nchunk ≤ i)] using ha
      let msg : Message P.Sym := ⟨1, .ct1, some (P.ecpCt1.encode c1 i)⟩
      let stB := State.ct1Sampled 1 a1 hdr es c1 ⟨P.ecpCt1, c1, i + 1⟩
        (DecoderState.empty P.ecpEk)
      let stA := if P.ecpCt1.ec.nchunk ≤ i + 1 then
        State.ct1Received 1 a0 sk c1 (EncoderState.init P.ecpEk vec)
        else State.headerSent 1 a0 sk
          ⟨P.ecpCt1, P.ecpCt1.payloadChunks c1
            ((Finset.range (i + 1)).image P.ecpCt1.counterIndex)⟩
          (EncoderState.init P.ecpEk vec)
      let next := SCKAScheme.recvAUpdate (SCKAScheme.sendBUpdate s none msg 0 stB) 0 none 0 stA
      let dnext := DecoderState.mk P.ecpCt1 (P.ecpCt1.payloadChunks c1
        ((Finset.range (i + 1)).image P.ecpCt1.counterIndex))
      have hs := ct1_step P auth irl hCt1 s a0 a1 sk vec hdr es c1 i hlt hcount ha' hb
      have hadd : dec.addChunk (P.ecpCt1.encode c1 i) = dnext := by
        rw [hd, DecoderState.addChunk_payloadChunks]
        congr 1
        rw [Finset.range_add_one, Finset.image_insert]
      have hcell : (cell dec i).run s = pure (dnext, next) := by
        have heq : cell dec i = collect dec <$> (do
            let answer ← SCKAScheme.oracleSendB (scheme P auth irl ($ᵗ (Vector UInt8 32))) ()
            let _ ← SCKAScheme.oracleRecvA (scheme P auth irl ($ᵗ (Vector UInt8 32))) (i + 1)
            pure answer) := by
          dsimp only [cell, collect]
          simp only [map_eq_pure_bind, bind_assoc, pure_bind]
          apply bind_congr
          intro answer
          apply bind_congr
          intro reply
          cases answer <;> rfl
        rw [heq, StateT.run_map, hs, map_pure]
        change pure (dec.addChunk (P.ecpCt1.encode c1 i), next) =
          (pure (dnext, next) : ProbComp _)
        rw [hadd]
      obtain ⟨s', hrun, hA, hB, hN, hNA, hKA, hKB, hM, hX, hC⟩ :=
        ih (i + 1) next dnext (by omega) (by omega)
          (by simp [next, SCKAScheme.recvAUpdate, SCKAScheme.sendBUpdate, hcount]) rfl
          (by simp [next, SCKAScheme.recvAUpdate, SCKAScheme.sendBUpdate, stA])
          (by simp [next, SCKAScheme.recvAUpdate, SCKAScheme.sendBUpdate, stB])
      refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.range'_succ, List.foldlM_cons, StateT.run_bind, hcell, pure_bind]
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrun
      · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hA
      · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hB
      · omega
      · simpa [next, SCKAScheme.recvAUpdate, SCKAScheme.sendBUpdate] using hNA
      · simpa [next, SCKAScheme.recvAUpdate, SCKAScheme.sendBUpdate] using hKA
      · simpa [next, SCKAScheme.recvAUpdate, SCKAScheme.sendBUpdate] using hKB
      · have hm : s'.msgB 1 = Function.update s.msgB (s.nB + 1) (some (msg, 0)) 1 := by
          simpa only [next, SCKAScheme.recvAUpdate, SCKAScheme.sendBUpdate] using hM
        rw [Function.update_of_ne (by omega : 1 ≠ s.nB + 1)] at hm
        exact hm
      · simpa [next, SCKAScheme.recvAUpdate, SCKAScheme.sendBUpdate] using hX
      · simpa [next, SCKAScheme.recvAUpdate, SCKAScheme.sendBUpdate] using hC

/-- Recorded message1 completes Alice's first ciphertext at threshold1; after a longer
completed ciphertext phase, the same replay leaves her protocol state unchanged.
The future consumer is the ct1 phase of `trace_law`. -/
private theorem ct1_replay (P : Parameters ProbComp) {AuthState : Type}
    [DecidableEq P.Sym] [DecidableEq P.EpochKey]
    (auth : RatchetedAuthenticator (Vector UInt8 32) P.EpochKey AuthState P.inc.PKheader
      (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (hCt1 : P.ecpCt1.ec.Correct)
    (s : GameState P AuthState) (a : AuthState) (sk : P.SK) (vec : P.inc.PKvector)
    (c1 : P.inc.C₁)
    (ha : s.stA = if P.ecpCt1.ec.nchunk = 1 then
      .headerSent 1 a sk
        ⟨P.ecpCt1, P.ecpCt1.payloadChunks c1
          ((Finset.range P.ecpCt1.ec.nchunk).image P.ecpCt1.counterIndex)⟩
        (EncoderState.init P.ecpEk vec)
      else .ct1Received 1 a sk c1 (EncoderState.init P.ecpEk vec))
    (hm : s.msgB 1 = some (⟨1, .ct1, some (P.ecpCt1.encode c1 0)⟩, 0)) :
    (SCKAScheme.oracleRecvA (scheme P auth irl ($ᵗ (Vector UInt8 32))) 1).run s =
      pure (some (0, none), SCKAScheme.recvAUpdate s 0 none 0
        (.ct1Received 1 a sk c1 (EncoderState.init P.ecpEk vec))) := by
  classical
  have hmem : P.ecpCt1.counterIndex 0 ∈
      (Finset.range P.ecpCt1.ec.nchunk).image P.ecpCt1.counterIndex :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr P.ecpCt1.ec.nchunk_pos, rfl⟩
  have hadd : (DecoderState.mk P.ecpCt1 (P.ecpCt1.payloadChunks c1
      ((Finset.range P.ecpCt1.ec.nchunk).image P.ecpCt1.counterIndex))).addChunk
      (P.ecpCt1.encode c1 0) =
      DecoderState.mk P.ecpCt1 (P.ecpCt1.payloadChunks c1
        ((Finset.range P.ecpCt1.ec.nchunk).image P.ecpCt1.counterIndex)) := by
    rw [DecoderState.addChunk_payloadChunks, Finset.insert_eq_of_mem hmem]
  have hd := prefix_decoded P.ecpCt1 hCt1 c1 P.ecpCt1.ec.nchunk
    P.ecpCt1.ec.nchunk_le_N
  simp only [le_refl, ↓reduceIte] at hd
  apply MLKEMBraid.oracleRecvA_run_eq_of_ok auth irl ($ᵗ (Vector UInt8 32))
    (r := ⟨0, none, .ct1Received 1 a sk c1 (EncoderState.init P.ecpEk vec)⟩) hm
  rw [ha]
  split_ifs with hc
  · simp [receive, Message.wellFormed, hadd, hd]
  · simp [receive, Message.wellFormed, State.epoch]

end MLKEMBraid.InitialSnapshot
