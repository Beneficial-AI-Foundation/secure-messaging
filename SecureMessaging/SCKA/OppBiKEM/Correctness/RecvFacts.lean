/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness.Receive
import SecureMessaging.SCKA.OppBiKEM.Correctness.SendFacts

/-!
# Opp-BiKEM — facts about a single receive

Support-level facts about `recv`, used by the main-invariant proofs: the reported sending
epoch (`recv_reports_message_sendingEpoch`), the post-state of a successful receive
(`recv_success_state_facts`), the facts behind an emitted key (`recv_emitted_key_facts`), and
how a receive changes the own public-key buffer (`recv_local_publicKey_eq_or_none`) and the
decoded peer keys (`recv_peerKeys_stable`, `recv_peerKeys_origin`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

universe u

private theorem option_all_ite {α : Type} (p : Prop) [Decidable p]
    (a b : Option α) (f : α → Bool) :
    (if p then a else b).all f = if p then a.all f else b.all f := by
  split <;> rfl

/-- Every successful receive reports the message's explicit sending epoch. -/
theorem recv_reports_message_sendingEpoch
  {m : Type → Type u} [Monad m] (role : Role)
  (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
  (hDet : kem.DeterministicDecaps) (ecEk : ErasureCodePayload PK Sym)
  (ecCt : ErasureCodePayload C Sym) (st : State PK SK C Sym) (ρ : Message Sym)
  (out : Option (ℕ × K) × ℕ × State PK SK C Sym)
  (hout : recv role kem hDet ecEk ecCt st ρ = some out) :
  out.2.1 = ρ.sendingEpoch := by
  have hepoch : (recv role kem hDet ecEk ecCt st ρ).all
      (fun x => x.2.1 == ρ.sendingEpoch) = true := by
    cases hek : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 <;>
      cases hct : (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).2
    all_goals simp only [recv, hek, hct, option_all_ite, Option.pure_def, Option.all_some,
      beq_self_eq_true, ite_self, Option.bind_eq_bind, Option.all_bind,
      Function.comp_def, Option.all_true]
  simpa only [hout, Option.all_some, beq_iff_eq] using hepoch

private theorem recv_nonstale_non_ciphertext_view
    [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (hnotstale : st.req.reqEpoch ≤ ρ.tRes)
    (hbit : ρ.bit ≠ some 1) :
    let ack : Acknowledgements :=
      { ekRec :=
          if ρ.ack.ekRec = true then
            insert (ρ.tReq + role.offset) st.ack.ekRec
          else st.ack.ekRec
        ctRec :=
          if ρ.ack.ctRec = true then insert ρ.tReq st.ack.ctRec
          else st.ack.ctRec }
    let q :=
      if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2
      else st.req.reqEpoch
    let decoded :=
      if (st.res.ekPeer (q - role.offset)).isNone = true ∧ ρ.bit = some 0 then
        insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch
      else (st.req.receivedChunks, none)
    let chunks :=
      match decoded.2 with
      | none => decoded.1
      | some _ => ∅
    let ack' : Acknowledgements :=
      match decoded.2 with
      | none => ack
      | some _ => { ack with ekRec := insert (q - role.offset) ack.ekRec }
    (recv role kem hDet ecEk ecCt st ρ).map
        (fun out =>
          (out.1, out.2.2.res.resEpoch, out.2.2.res.ich,
            out.2.2.req.reqEpoch, out.2.2.req.dk,
            out.2.2.req.receivedChunks, out.2.2.ack)) =
      some (none, st.res.resEpoch, st.res.ich, q, st.req.dk, chunks, ack') := by
  let ack : Acknowledgements :=
    { ekRec :=
        if ρ.ack.ekRec = true then
          insert (ρ.tReq + role.offset) st.ack.ekRec
        else st.ack.ekRec
      ctRec :=
        if ρ.ack.ctRec = true then insert ρ.tReq st.ack.ctRec
        else st.ack.ctRec }
  let q : ℤ :=
    if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2
    else st.req.reqEpoch
  have hstale : ¬ ρ.tRes < st.req.reqEpoch := not_lt.mpr hnotstale
  rw [recv]
  dsimp only
  by_cases hctRec : ρ.ack.ctRec = true <;>
    simp only [hctRec, Bool.false_eq_true, if_true, if_false]
  all_goals
    by_cases hekRec : ρ.ack.ekRec = true <;>
      simp only [hekRec, Bool.false_eq_true, if_true, if_false]
  all_goals simp only [hstale, if_false]
  all_goals
    by_cases hadvance : st.req.reqEpoch < ρ.tRes <;>
      simp only [hadvance, if_true, if_false]
  all_goals
    by_cases hpk :
        (st.res.ekPeer (q - role.offset)).isNone = true ∧ ρ.bit = some 0
    · simp only [q, hadvance, if_true, if_false] at hpk
      simp only [hpk]
      cases hdecode : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch) with
      | mk chunksEk peerEk? =>
          cases hpeerEk : peerEk? with
          | none =>
              simp only [true_and, if_true]
              by_cases hclearCt : st.res.resEpoch ∈ ack.ctRec <;>
                simp only [ack, hctRec, Bool.false_eq_true,
                  if_true, if_false] at hclearCt <;>
                by_cases hclearEk : st.res.resEpoch + role.offset ∈ ack.ekRec <;>
                simp only [ack, hekRec, Bool.false_eq_true,
                  if_true, if_false] at hclearEk <;>
                simp only [hclearCt, hclearEk, if_true, if_false,
                  Option.pure_def, Option.map_some]
          | some peerEk =>
              simp only [true_and, if_true]
              by_cases hclearCt : st.res.resEpoch ∈ ack.ctRec <;>
                simp only [ack, hctRec, Bool.false_eq_true,
                  if_true, if_false] at hclearCt <;>
                by_cases hclearEk :
                    st.res.resEpoch + role.offset ∈ insert (q - role.offset) ack.ekRec <;>
                simp only [ack, q, hekRec, hadvance,
                  Bool.false_eq_true, if_true, if_false] at hclearEk <;>
                simp only [hclearCt, hclearEk, if_true, if_false,
                  Option.pure_def, Option.map_some]
    · simp only [q, hadvance, if_true, if_false] at hpk
      simp only [hpk, if_false]
      simp only [hbit, and_false]
      by_cases hclearCt : st.res.resEpoch ∈ ack.ctRec <;>
        simp only [ack, hctRec, Bool.false_eq_true,
          if_true, if_false] at hclearCt <;>
        by_cases hclearEk : st.res.resEpoch + role.offset ∈ ack.ekRec <;>
        simp only [ack, hekRec, Bool.false_eq_true,
          if_true, if_false] at hclearEk <;>
        simp only [hclearCt, hclearEk, if_true, if_false,
          Option.pure_def, Option.map_some]

private theorem recv_nonstale_ciphertext_view
    [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (hnotstale : st.req.reqEpoch ≤ ρ.tRes)
    (hbit : ρ.bit = some 1) :
    let ack : Acknowledgements :=
      { ekRec :=
          if ρ.ack.ekRec = true then
            insert (ρ.tReq + role.offset) st.ack.ekRec
          else st.ack.ekRec
        ctRec :=
          if ρ.ack.ctRec = true then insert ρ.tReq st.ack.ctRec
          else st.ack.ctRec }
    let q :=
      if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2
      else st.req.reqEpoch
    let decoded :=
      if q ∉ ack.ctRec then
        insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch
      else (st.req.receivedChunks, none)
    (recv role kem hDet ecEk ecCt st ρ).map
        (fun out =>
          (out.1, out.2.2.res.resEpoch, out.2.2.res.ich,
            out.2.2.req.reqEpoch, out.2.2.req.dk,
            out.2.2.req.receivedChunks, out.2.2.ack)) =
      match decoded.2 with
      | none =>
          some (none, st.res.resEpoch, st.res.ich, q,
            st.req.dk, decoded.1, ack)
      | some ciphertext =>
          (st.req.dk.lookup q).bind fun secretKey =>
            (hDet.decapsDet secretKey ciphertext).map fun key =>
              (some (q.toNat, key), st.res.resEpoch, st.res.ich, q,
                st.req.dk.filter (fun p => p.1 != q), ∅,
                { ack with ctRec := insert q ack.ctRec }) := by
  let ack : Acknowledgements :=
    { ekRec :=
        if ρ.ack.ekRec = true then
          insert (ρ.tReq + role.offset) st.ack.ekRec
        else st.ack.ekRec
      ctRec :=
        if ρ.ack.ctRec = true then insert ρ.tReq st.ack.ctRec
        else st.ack.ctRec }
  let q : ℤ :=
    if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2
    else st.req.reqEpoch
  have hstale : ¬ ρ.tRes < st.req.reqEpoch := not_lt.mpr hnotstale
  have hnotpk :
      ¬ ((st.res.ekPeer (q - role.offset)).isNone = true ∧ ρ.bit = some 0) := by
    intro hpk
    have hselectors : some (1 : Bit) = some 0 := hbit.symm.trans hpk.2
    have h10 : (1 : Bit) ≠ 0 := by decide
    exact h10 (Option.some.inj hselectors)
  rw [recv]
  dsimp only
  by_cases hctRec : ρ.ack.ctRec = true <;>
    simp only [hctRec, Bool.false_eq_true, if_true, if_false]
  all_goals
    by_cases hekRec : ρ.ack.ekRec = true <;>
      simp only [hekRec, Bool.false_eq_true, if_true, if_false]
  all_goals simp only [hstale, if_false]
  all_goals
    by_cases hadvance : st.req.reqEpoch < ρ.tRes <;>
      simp only [hadvance, if_true, if_false]
  all_goals simp only [q, hadvance, if_true, if_false] at hnotpk
  all_goals simp only [hnotpk, if_false]
  all_goals
    by_cases hguard : q ∉ ack.ctRec
    · simp only [ack, q, hctRec, hadvance,
        Bool.false_eq_true, if_true, if_false] at hguard
      simp only [hguard, hbit, and_true]
      cases hdecode : (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch) with
      | mk chunksCt peerCt? =>
          cases hpeerCt : peerCt? with
          | none =>
              simp only [not_false_eq_true, if_true]
              by_cases hclearCt : st.res.resEpoch ∈ ack.ctRec <;>
                simp only [ack, hctRec, Bool.false_eq_true,
                  if_true, if_false] at hclearCt <;>
                by_cases hclearEk : st.res.resEpoch + role.offset ∈ ack.ekRec <;>
                simp only [ack, hekRec, Bool.false_eq_true,
                  if_true, if_false] at hclearEk <;>
                simp only [hclearCt, hclearEk, if_true, if_false,
                  Option.pure_def, Option.map_some]
          | some ciphertext =>
              cases hlookup :
                  (List.lookup (α := ℤ) (β := SK) q st.req.dk) with
              | none =>
                  simp only [q, hadvance, if_true, if_false] at hlookup
                  simp only [not_false_eq_true, if_true]
                  simp only [Option.bind_eq_bind]
                  rw [hlookup]
                  simp only [Option.bind_none, Option.map_none]
              | some secretKey =>
                  cases hdecaps : (hDet.decapsDet secretKey ciphertext) with
                  | none =>
                      simp only [q, hadvance, if_true, if_false] at hlookup
                      simp only [not_false_eq_true, if_true]
                      simp only [Option.bind_eq_bind]
                      rw [hlookup]
                      simp only [Option.bind_some]
                      rw [hdecaps]
                      simp only [Option.bind_none, Option.map_none]
                  | some key =>
                      simp only [q, hadvance, if_true, if_false] at hlookup
                      simp only [not_false_eq_true, if_true]
                      simp only [Option.bind_eq_bind]
                      rw [hlookup]
                      simp only [Option.bind_some]
                      rw [hdecaps]
                      simp only [Option.bind_some, Option.map_some]
                      by_cases hclearCt :
                          st.res.resEpoch ∈ insert q ack.ctRec <;>
                        simp only [ack, q, hctRec, hadvance,
                          Bool.false_eq_true, if_true, if_false] at hclearCt <;>
                        by_cases hclearEk :
                            st.res.resEpoch + role.offset ∈ ack.ekRec <;>
                        simp only [ack, hekRec, Bool.false_eq_true,
                          if_true, if_false] at hclearEk <;>
                        simp only [hclearCt, hclearEk, if_true, if_false,
                          Option.pure_def, Option.map_some]
    · simp only [ack, q, hctRec, hadvance,
        Bool.false_eq_true, if_true, if_false] at hguard
      simp only [hguard, false_and, if_false]
      by_cases hclearCt : st.res.resEpoch ∈ ack.ctRec <;>
        simp only [ack, hctRec, Bool.false_eq_true,
          if_true, if_false] at hclearCt <;>
        by_cases hclearEk : st.res.resEpoch + role.offset ∈ ack.ekRec <;>
        simp only [ack, hekRec, Bool.false_eq_true,
          if_true, if_false] at hclearEk <;>
        simp only [hclearCt, hclearEk, if_true, if_false,
          Option.pure_def, Option.map_some]

theorem recv_success_state_facts
    [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st')) :
    trcv = ρ.sendingEpoch ∧
    st'.res.resEpoch = st.res.resEpoch ∧
    st'.res.ich = st.res.ich ∧
    st'.req.reqEpoch =
      (if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2 else st.req.reqEpoch) ∧
    st.ack.ctRec ⊆ st'.ack.ctRec ∧
    st.ack.ekRec ⊆ st'.ack.ekRec ∧
    (ρ.ack.ctRec = true → ρ.tReq ∈ st'.ack.ctRec) ∧
    (ρ.ack.ekRec = true → ρ.tReq + role.offset ∈ st'.ack.ekRec) ∧
    (key? = none → st'.req.dk = st.req.dk) := by
  have htrcv := recv_reports_message_sendingEpoch role kem hDet ecEk ecCt st ρ
    (key?, trcv, st') hout
  change trcv = ρ.sendingEpoch at htrcv
  let ack : Acknowledgements :=
    { ekRec :=
        if ρ.ack.ekRec = true then
          insert (ρ.tReq + role.offset) st.ack.ekRec
        else st.ack.ekRec
      ctRec :=
        if ρ.ack.ctRec = true then insert ρ.tReq st.ack.ctRec
        else st.ack.ctRec }
  let q : ℤ :=
    if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2
    else st.req.reqEpoch
  have hctSubset : st.ack.ctRec ⊆ ack.ctRec := by
    intro t ht
    unfold ack
    by_cases hctRec : ρ.ack.ctRec = true
    · simp only [hctRec, if_true]
      exact Finset.mem_insert_of_mem ht
    · simp only [hctRec]
      exact ht
  have hekSubset : st.ack.ekRec ⊆ ack.ekRec := by
    intro t ht
    unfold ack
    by_cases hekRec : ρ.ack.ekRec = true
    · simp only [hekRec, if_true]
      exact Finset.mem_insert_of_mem ht
    · simp only [hekRec]
      exact ht
  have hctReported : ρ.ack.ctRec = true → ρ.tReq ∈ ack.ctRec := by
    intro hctRec
    unfold ack
    simp only [hctRec, if_true]
    exact Finset.mem_insert_self _ _
  have hekReported :
      ρ.ack.ekRec = true → ρ.tReq + role.offset ∈ ack.ekRec := by
    intro hekRec
    unfold ack
    simp only [hekRec, if_true]
    exact Finset.mem_insert_self _ _
  by_cases hstale : ρ.tRes < st.req.reqEpoch
  · have hview := congrArg
      (Option.map fun out =>
        (out.1, out.2.2.res.resEpoch, out.2.2.res.ich,
          out.2.2.req.reqEpoch, out.2.2.req.dk,
          out.2.2.req.receivedChunks, out.2.2.ack)) hout
    simp only [Option.map_some] at hview
    rw [recv] at hview
    dsimp only at hview
    by_cases hctRec : ρ.ack.ctRec = true <;>
      simp only [hctRec, Bool.false_eq_true, if_true, if_false] at hview
    all_goals
      by_cases hekRec : ρ.ack.ekRec = true <;>
        simp only [hekRec, Bool.false_eq_true, if_true, if_false] at hview
    all_goals simp only [hstale, if_true, Option.pure_def, Option.map_some] at hview
    all_goals
      have hadvance : ¬ st.req.reqEpoch < ρ.tRes :=
        not_lt.mpr (le_of_lt hstale)
      simp only [ack, hctRec, hekRec, if_true] at hctSubset hekSubset
      have htuple := Option.some.inj hview
      simp only [Prod.mk.injEq] at htuple
      rcases htuple with ⟨_, hres, hich, hreq, hdk, _, hack⟩
      refine ⟨htrcv, hres.symm, hich.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [hadvance, if_false]
        exact hreq.symm
      · intro t ht
        rw [← hack]
        exact hctSubset ht
      · intro t ht
        rw [← hack]
        exact hekSubset ht
      · intro hct
        rw [← hack]
        have hctMem := hctReported hct
        simp only [ack, hctRec, if_true] at hctMem
        exact hctMem
      · intro hek
        rw [← hack]
        have hekMem := hekReported hek
        simp only [ack, hekRec, if_true] at hekMem
        exact hekMem
      · intro _
        exact hdk.symm
  · have hnotstale : st.req.reqEpoch ≤ ρ.tRes := not_lt.mp hstale
    by_cases hbit : ρ.bit = some 1
    · let decoded :=
        if q ∉ ack.ctRec then
          insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch
        else (st.req.receivedChunks, none)
      have hview := recv_nonstale_ciphertext_view role kem hDet ecEk ecCt st ρ
        hnotstale hbit
      change (recv role kem hDet ecEk ecCt st ρ).map
          (fun out =>
            (out.1, out.2.2.res.resEpoch, out.2.2.res.ich,
              out.2.2.req.reqEpoch, out.2.2.req.dk,
              out.2.2.req.receivedChunks, out.2.2.ack)) =
        match decoded.2 with
        | none =>
            some (none, st.res.resEpoch, st.res.ich, q,
              st.req.dk, decoded.1, ack)
        | some ciphertext =>
            (st.req.dk.lookup q).bind fun secretKey =>
              (hDet.decapsDet secretKey ciphertext).map fun key =>
                (some (q.toNat, key), st.res.resEpoch, st.res.ich, q,
                  st.req.dk.filter (fun p => p.1 != q), ∅,
                  { ack with ctRec := insert q ack.ctRec }) at hview
      simp only [hout, Option.map_some] at hview
      cases hdecoded : decoded.2 with
      | none =>
          simp only [hdecoded] at hview
          have htuple := Option.some.inj hview
          simp only [Prod.mk.injEq] at htuple
          rcases htuple with ⟨_, hres, hich, hreq, hdk, _, hack⟩
          refine ⟨htrcv, hres, hich, hreq, ?_, ?_, ?_, ?_, ?_⟩
          · intro t ht
            rw [hack]
            exact hctSubset ht
          · intro t ht
            rw [hack]
            exact hekSubset ht
          · intro hct
            rw [hack]
            exact hctReported hct
          · intro hek
            rw [hack]
            exact hekReported hek
          · intro _
            exact hdk
      | some ciphertext =>
          simp only [hdecoded] at hview
          have hsuccess := hview.symm
          rw [Option.bind_eq_some_iff] at hsuccess
          obtain ⟨secretKey, _, hmap⟩ := hsuccess
          rw [Option.map_eq_some_iff] at hmap
          obtain ⟨key, _, htuple⟩ := hmap
          have htuple' := htuple.symm
          simp only [Prod.mk.injEq] at htuple'
          rcases htuple' with ⟨hkey, hres, hich, hreq, _, _, hack⟩
          refine ⟨htrcv, hres, hich, hreq, ?_, ?_, ?_, ?_, ?_⟩
          · intro t ht
            rw [hack]
            exact Finset.mem_insert_of_mem (hctSubset ht)
          · intro t ht
            rw [hack]
            exact hekSubset ht
          · intro hct
            rw [hack]
            exact Finset.mem_insert_of_mem (hctReported hct)
          · intro hek
            rw [hack]
            exact hekReported hek
          · intro hnone
            cases hnone.symm.trans hkey
    · let decoded :=
        if (st.res.ekPeer (q - role.offset)).isNone = true ∧ ρ.bit = some 0 then
          insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch
        else (st.req.receivedChunks, none)
      have hview := recv_nonstale_non_ciphertext_view role kem hDet ecEk ecCt st ρ
        hnotstale hbit
      change (recv role kem hDet ecEk ecCt st ρ).map
          (fun out =>
            (out.1, out.2.2.res.resEpoch, out.2.2.res.ich,
              out.2.2.req.reqEpoch, out.2.2.req.dk,
              out.2.2.req.receivedChunks, out.2.2.ack)) =
        some (none, st.res.resEpoch, st.res.ich, q, st.req.dk,
          match decoded.2 with
          | none => decoded.1
          | some _ => ∅,
          match decoded.2 with
          | none => ack
          | some _ => { ack with ekRec := insert (q - role.offset) ack.ekRec }) at hview
      simp only [hout, Option.map_some] at hview
      cases hdecoded : decoded.2 with
      | none =>
          simp only [hdecoded] at hview
          have htuple := Option.some.inj hview
          simp only [Prod.mk.injEq] at htuple
          rcases htuple with ⟨_, hres, hich, hreq, hdk, _, hack⟩
          refine ⟨htrcv, hres, hich, hreq, ?_, ?_, ?_, ?_, ?_⟩
          · intro t ht
            rw [hack]
            exact hctSubset ht
          · intro t ht
            rw [hack]
            exact hekSubset ht
          · intro hct
            rw [hack]
            exact hctReported hct
          · intro hek
            rw [hack]
            exact hekReported hek
          · intro _
            exact hdk
      | some peerEk =>
          simp only [hdecoded] at hview
          have htuple := Option.some.inj hview
          simp only [Prod.mk.injEq] at htuple
          rcases htuple with ⟨_, hres, hich, hreq, hdk, _, hack⟩
          refine ⟨htrcv, hres, hich, hreq, ?_, ?_, ?_, ?_, ?_⟩
          · intro t ht
            rw [hack]
            exact hctSubset ht
          · intro t ht
            rw [hack]
            exact Finset.mem_insert_of_mem (hekSubset ht)
          · intro hct
            rw [hack]
            exact hctReported hct
          · intro hek
            rw [hack]
            exact Finset.mem_insert_of_mem (hekReported hek)
          · intro _
            exact hdk

theorem recv_emitted_key_facts
    [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (tI : ℕ) (key : K) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ =
      some (some (tI, key), trcv, st')) :
    ρ.bit = some 1 ∧
    st.req.reqEpoch ≤ ρ.tRes ∧
    tI = st'.req.reqEpoch.toNat ∧
    st'.req.reqEpoch ∉ st.ack.ctRec ∧
    st'.req.reqEpoch ∈ st'.ack.ctRec ∧
    st'.req.dk = st.req.dk.filter (fun p => p.1 != st'.req.reqEpoch) ∧
    st'.req.dk.lookup st'.req.reqEpoch = none ∧
    st'.req.receivedChunks = ∅ ∧
    ∃ secretKey : SK, ∃ ciphertext : C,
      st.req.dk.lookup st'.req.reqEpoch = some secretKey ∧
      (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).2 = some ciphertext ∧
      hDet.decapsDet secretKey ciphertext = some key := by
  let ack : Acknowledgements :=
    { ekRec :=
        if ρ.ack.ekRec = true then
          insert (ρ.tReq + role.offset) st.ack.ekRec
        else st.ack.ekRec
      ctRec :=
        if ρ.ack.ctRec = true then insert ρ.tReq st.ack.ctRec
        else st.ack.ctRec }
  let q : ℤ :=
    if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2
    else st.req.reqEpoch
  have hctSubset : st.ack.ctRec ⊆ ack.ctRec := by
    intro t ht
    unfold ack
    by_cases hctRec : ρ.ack.ctRec = true
    · simp only [hctRec, if_true]
      exact Finset.mem_insert_of_mem ht
    · simp only [hctRec]
      exact ht
  by_cases hstale : ρ.tRes < st.req.reqEpoch
  · have hkeyView := congrArg (Option.map fun out => out.1) hout
    simp only [Option.map_some] at hkeyView
    rw [recv] at hkeyView
    dsimp only at hkeyView
    by_cases hctRec : ρ.ack.ctRec = true <;>
      simp only [hctRec, Bool.false_eq_true, if_true, if_false] at hkeyView
    all_goals
      by_cases hekRec : ρ.ack.ekRec = true <;>
        simp only [hekRec, Bool.false_eq_true, if_true, if_false] at hkeyView
    all_goals
      simp only [hstale, if_true, Option.pure_def, Option.map_some] at hkeyView
    all_goals
      have hnone := Option.some.inj hkeyView
      cases hnone
  · have hnotstale : st.req.reqEpoch ≤ ρ.tRes := not_lt.mp hstale
    by_cases hbit : ρ.bit = some 1
    · let decoded :=
        if q ∉ ack.ctRec then
          insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch
        else (st.req.receivedChunks, none)
      have hview := recv_nonstale_ciphertext_view role kem hDet ecEk ecCt st ρ
        hnotstale hbit
      change (recv role kem hDet ecEk ecCt st ρ).map
          (fun out =>
            (out.1, out.2.2.res.resEpoch, out.2.2.res.ich,
              out.2.2.req.reqEpoch, out.2.2.req.dk,
              out.2.2.req.receivedChunks, out.2.2.ack)) =
        match decoded.2 with
        | none =>
            some (none, st.res.resEpoch, st.res.ich, q,
              st.req.dk, decoded.1, ack)
        | some ciphertext =>
            (st.req.dk.lookup q).bind fun secretKey =>
              (hDet.decapsDet secretKey ciphertext).map fun decodedKey =>
                (some (q.toNat, decodedKey), st.res.resEpoch, st.res.ich, q,
                  st.req.dk.filter (fun p => p.1 != q), ∅,
                  { ack with ctRec := insert q ack.ctRec }) at hview
      simp only [hout, Option.map_some] at hview
      cases hdecoded : decoded.2 with
      | none =>
          simp only [hdecoded] at hview
          have htuple := Option.some.inj hview
          simp only [Prod.mk.injEq] at htuple
          cases htuple.1
      | some ciphertext =>
          simp only [hdecoded] at hview
          have hsuccess := hview.symm
          rw [Option.bind_eq_some_iff] at hsuccess
          obtain ⟨secretKey, hlookup, hmap⟩ := hsuccess
          rw [Option.map_eq_some_iff] at hmap
          obtain ⟨decodedKey, hdecaps, htuple⟩ := hmap
          have htuple' := htuple.symm
          simp only [Prod.mk.injEq] at htuple'
          rcases htuple' with ⟨hkey, _, _, hreq, hdk, hchunks, hack⟩
          have hkey' := Option.some.inj hkey
          simp only [Prod.mk.injEq] at hkey'
          rcases hkey' with ⟨htI, hdecodedKey⟩
          have hguard : q ∉ ack.ctRec := by
            intro hmem
            simp only [decoded, hmem, not_true_eq_false, if_false] at hdecoded
            cases hdecoded
          have hdecode :
              (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).2 =
                some ciphertext := by
            have hdecode := hdecoded
            simp only [decoded, hguard] at hdecode
            exact hdecode
          refine ⟨hbit, hnotstale, ?_, ?_, ?_, ?_, ?_, hchunks, ?_⟩
          · rw [hreq]
            exact htI
          · rw [hreq]
            intro hmem
            exact hguard (hctSubset hmem)
          · rw [hreq, hack]
            exact Finset.mem_insert_self _ _
          · rw [hreq]
            exact hdk
          · rw [hreq, hdk, List.lookup_eq_none_iff]
            intro p hp
            rw [List.mem_filter] at hp
            rw [bne_comm]
            exact hp.2
          · refine ⟨secretKey, ciphertext, ?_, hdecode, ?_⟩
            · rw [hreq]
              exact hlookup
            · rw [hdecodedKey]
              exact hdecaps
    · let decoded :=
        if (st.res.ekPeer (q - role.offset)).isNone = true ∧ ρ.bit = some 0 then
          insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch
        else (st.req.receivedChunks, none)
      have hview := recv_nonstale_non_ciphertext_view role kem hDet ecEk ecCt st ρ
        hnotstale hbit
      change (recv role kem hDet ecEk ecCt st ρ).map
          (fun out =>
            (out.1, out.2.2.res.resEpoch, out.2.2.res.ich,
              out.2.2.req.reqEpoch, out.2.2.req.dk,
              out.2.2.req.receivedChunks, out.2.2.ack)) =
        some (none, st.res.resEpoch, st.res.ich, q, st.req.dk,
          match decoded.2 with
          | none => decoded.1
          | some _ => ∅,
          match decoded.2 with
          | none => ack
          | some _ => { ack with ekRec := insert (q - role.offset) ack.ekRec }) at hview
      simp only [hout, Option.map_some] at hview
      have htuple := Option.some.inj hview
      simp only [Prod.mk.injEq] at htuple
      cases htuple.1

theorem recv_local_publicKey_eq_or_none
    [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st')) :
    st'.req.ek = st.req.ek ∨ st'.req.ek = none := by
  have hproj := congrArg
    (Option.map fun out : Option (ℕ × K) × ℕ × State PK SK C Sym =>
      out.2.2.req.ek) hout
  simp only [Option.map_some] at hproj
  rw [recv] at hproj
  dsimp only at hproj
  by_cases hctRec : ρ.ack.ctRec = true <;>
    simp only [hctRec, Bool.false_eq_true, if_true, if_false] at hproj
  all_goals
    by_cases hekRec : ρ.ack.ekRec = true <;>
      simp only [hekRec, Bool.false_eq_true, if_true, if_false] at hproj
  all_goals
    by_cases hstale : ρ.tRes < st.req.reqEpoch <;>
      simp only [hstale, if_true, if_false] at hproj
  all_goals try
    (simp only [Option.pure_def, Option.map_some] at hproj
     exact Or.inl (Option.some.inj hproj).symm)
  all_goals
    by_cases hadvance : st.req.reqEpoch < ρ.tRes <;>
      simp only [hadvance, if_true, if_false] at hproj
  all_goals
    by_cases hpk :
        (st.res.ekPeer
          ((if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2
            else st.req.reqEpoch) - role.offset)).isNone = true ∧
        ρ.bit = some 0
    · simp only [hadvance, if_true, if_false] at hpk
      simp only [hpk] at hproj
      simp only [true_and, if_true] at hproj
      cases hdecode : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 <;>
        simp only [hdecode] at hproj
      all_goals
        repeat' split at hproj
        try simp only [Option.pure_def, Option.map_some] at hproj
        all_goals first
          | exact Or.inl (Option.some.inj hproj).symm
          | exact Or.inr (Option.some.inj hproj).symm
    · simp only [hadvance, if_true, if_false] at hpk
      simp only [hpk, if_false] at hproj
      repeat' split at hproj
      all_goals try simp only [Option.bind_eq_bind,
        Option.bind] at hproj
      all_goals repeat' split at hproj
      all_goals try simp only [Option.pure_def, Option.map_some,
        Option.map_none] at hproj
      all_goals repeat' split at hproj
      all_goals try simp only [Option.map_some, Option.map_none] at hproj
      all_goals try cases hproj
      all_goals first
        | exact Or.inl (Option.some.inj hproj).symm
        | exact Or.inr (Option.some.inj hproj).symm

/-- A successful receive never changes an already installed peer public key. -/
theorem recv_peerKeys_stable [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st'))
    (t : ℤ) (ht : (st.res.ekPeer t).isSome = true) :
    st'.res.ekPeer t = st.res.ekPeer t := by
  -- The only `ekPeer` write is guarded by an empty slot, which `t` is not.
  have hne : ∀ q : ℤ, (st.res.ekPeer q).isNone = true → t ≠ q := by
    intro q hq htq
    subst htq
    rw [Option.isNone_iff_eq_none] at hq
    rw [hq] at ht
    cases ht
  have hproj := congrArg
    (Option.map fun out : Option (ℕ × K) × ℕ × State PK SK C Sym =>
      out.2.2.res.ekPeer t) hout
  simp only [Option.map_some] at hproj
  rw [recv] at hproj
  dsimp only at hproj
  by_cases hctRec : ρ.ack.ctRec = true <;>
    simp only [hctRec, Bool.false_eq_true, if_true, if_false] at hproj
  all_goals
    by_cases hekRec : ρ.ack.ekRec = true <;>
      simp only [hekRec, Bool.false_eq_true, if_true, if_false] at hproj
  all_goals
    by_cases hstale : ρ.tRes < st.req.reqEpoch <;>
      simp only [hstale, if_true, if_false] at hproj
  all_goals try
    (simp only [Option.pure_def, Option.map_some] at hproj
     exact (Option.some.inj hproj).symm)
  all_goals
    by_cases hadvance : st.req.reqEpoch < ρ.tRes <;>
      simp only [hadvance, if_true, if_false] at hproj
  all_goals
    by_cases hpk :
        (st.res.ekPeer
          ((if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2
            else st.req.reqEpoch) - role.offset)).isNone = true ∧
        ρ.bit = some 0
    · simp only [hadvance, if_true, if_false] at hpk
      simp only [hpk] at hproj
      simp only [true_and, if_true] at hproj
      cases hdecode : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 <;>
        simp only [hdecode] at hproj
      all_goals repeat' split at hproj
      all_goals try simp only [Option.pure_def, Option.map_some] at hproj
      all_goals first
        | exact (Option.some.inj hproj).symm
        | exact (Option.some.inj hproj).symm.trans
            (Function.update_of_ne (hne _ hpk.1) _ _)
    · simp only [hadvance, if_true, if_false] at hpk
      simp only [hpk, if_false] at hproj
      repeat' split at hproj
      all_goals try simp only [Option.bind_eq_bind,
        Option.bind] at hproj
      all_goals repeat' split at hproj
      all_goals try simp only [Option.pure_def, Option.map_some,
        Option.map_none] at hproj
      all_goals repeat' split at hproj
      all_goals try simp only [Option.map_some, Option.map_none] at hproj
      all_goals try cases hproj
      all_goals exact (Option.some.inj hproj).symm

/-- A successful receive changes the peer public key at index `t` only when `t` is the
receiver's new requester epoch shifted by its role offset, the only index `recv` writes. -/
theorem recv_peerKeys_origin [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st'))
    (t : ℤ) :
    st'.res.ekPeer t = st.res.ekPeer t ∨ t = st'.req.reqEpoch - role.offset := by
  have hproj := congrArg
    (Option.map fun out : Option (ℕ × K) × ℕ × State PK SK C Sym =>
      (out.2.2.req.reqEpoch, out.2.2.res.ekPeer t)) hout
  simp only [Option.map_some] at hproj
  rw [recv] at hproj
  dsimp only at hproj
  by_cases hctRec : ρ.ack.ctRec = true <;>
    simp only [hctRec, Bool.false_eq_true, if_true, if_false] at hproj
  all_goals
    by_cases hekRec : ρ.ack.ekRec = true <;>
      simp only [hekRec, Bool.false_eq_true, if_true, if_false] at hproj
  all_goals
    by_cases hstale : ρ.tRes < st.req.reqEpoch <;>
      simp only [hstale, if_true, if_false] at hproj
  -- Stale leaves keep both the requester epoch and `ekPeer`.
  all_goals try
    (simp only [Option.pure_def, Option.map_some] at hproj
     exact Or.inl (Prod.mk.inj (Option.some.inj hproj)).2.symm)
  all_goals
    by_cases hadvance : st.req.reqEpoch < ρ.tRes <;>
      simp only [hadvance, if_true, if_false] at hproj
  all_goals
    by_cases hpk :
        (st.res.ekPeer
          ((if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2
            else st.req.reqEpoch) - role.offset)).isNone = true ∧
        ρ.bit = some 0
    · simp only [hadvance, if_true, if_false] at hpk
      simp only [hpk] at hproj
      simp only [true_and, if_true] at hproj
      cases hdecode : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 <;>
        simp only [hdecode] at hproj
      all_goals repeat' split at hproj
      all_goals try simp only [Option.pure_def, Option.map_some] at hproj
      -- Public-key leaves: either `ekPeer` is unchanged, or the decoded key is installed
      -- at the new requester epoch shifted by the role offset.
      all_goals
        obtain ⟨hreq, hpe⟩ := Prod.mk.inj (Option.some.inj hproj)
        first
          | exact Or.inl hpe.symm
          | (rw [← hpe, ← hreq, Function.update_apply]
             split_ifs with htq
             · exact Or.inr htq
             · exact Or.inl rfl)
    · simp only [hadvance, if_true, if_false] at hpk
      simp only [hpk, if_false] at hproj
      repeat' split at hproj
      all_goals try simp only [Option.bind_eq_bind,
        Option.bind] at hproj
      all_goals repeat' split at hproj
      all_goals try simp only [Option.pure_def, Option.map_some,
        Option.map_none] at hproj
      all_goals repeat' split at hproj
      all_goals try simp only [Option.map_some, Option.map_none] at hproj
      all_goals try cases hproj
      -- Ciphertext and no-payload leaves never write `ekPeer`.
      all_goals
        obtain ⟨-, hpe⟩ := Prod.mk.inj (Option.some.inj hproj)
        exact Or.inl hpe.symm

end oppBiKemCKA
