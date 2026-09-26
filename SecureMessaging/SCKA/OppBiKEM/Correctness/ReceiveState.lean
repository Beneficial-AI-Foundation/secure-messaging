/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.Receive
import SecureMessaging.SCKA.OppBiKEM.Correctness.SendB

/-!
# Opp-BiKEM successful receive state

This file characterizes the local state and game transition at the successful-output boundary of
Opp-BiKEM receive. It does not establish honest-message origin, message availability, or the
cryptographic correctness of an emitted key.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

theorem Acknowledgements.sendingHorizon_mono
    (ack ack' : Acknowledgements)
    (hct : ack.ctRec ⊆ ack'.ctRec) :
    ack.sendingHorizon ≤ ack'.sendingHorizon := by
  unfold sendingHorizon
  apply Finset.sup_mono
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨hct ht.1, hct ht.2⟩

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
    simp only [hctRec, Bool.true_eq, Bool.false_eq_true, if_true, if_false]
  all_goals
    by_cases hekRec : ρ.ack.ekRec = true <;>
      simp only [hekRec, Bool.true_eq, Bool.false_eq_true, if_true, if_false]
  all_goals simp only [hstale, if_false]
  all_goals
    by_cases hadvance : st.req.reqEpoch < ρ.tRes <;>
      simp only [hadvance, if_true, if_false]
  all_goals
    by_cases hpk :
        (st.res.ekPeer (q - role.offset)).isNone = true ∧ ρ.bit = some 0
    · simp only [q, hadvance, if_true, if_false] at hpk
      simp only [hpk, if_true]
      cases hdecode : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch) with
      | mk chunksEk peerEk? =>
          cases hpeerEk : peerEk? with
          | none =>
              simp only [true_and, if_true]
              by_cases hclearCt : st.res.resEpoch ∈ ack.ctRec <;>
                simp only [ack, hctRec, Bool.true_eq, Bool.false_eq_true,
                  if_true, if_false] at hclearCt <;>
                by_cases hclearEk : st.res.resEpoch + role.offset ∈ ack.ekRec <;>
                simp only [ack, hekRec, Bool.true_eq, Bool.false_eq_true,
                  if_true, if_false] at hclearEk <;>
                simp only [hclearCt, hclearEk, if_true, if_false,
                  Option.pure_def, Option.map_some]
          | some peerEk =>
              simp only [true_and, if_true]
              by_cases hclearCt : st.res.resEpoch ∈ ack.ctRec <;>
                simp only [ack, hctRec, Bool.true_eq, Bool.false_eq_true,
                  if_true, if_false] at hclearCt <;>
                by_cases hclearEk :
                    st.res.resEpoch + role.offset ∈ insert (q - role.offset) ack.ekRec <;>
                simp only [ack, q, hekRec, hadvance, Bool.true_eq,
                  Bool.false_eq_true, if_true, if_false] at hclearEk <;>
                simp only [hclearCt, hclearEk, if_true, if_false,
                  Option.pure_def, Option.map_some]
    · simp only [q, hadvance, if_true, if_false] at hpk
      simp only [hpk, if_false]
      simp only [hbit, and_false]
      by_cases hclearCt : st.res.resEpoch ∈ ack.ctRec <;>
        simp only [ack, hctRec, Bool.true_eq, Bool.false_eq_true,
          if_true, if_false] at hclearCt <;>
        by_cases hclearEk : st.res.resEpoch + role.offset ∈ ack.ekRec <;>
        simp only [ack, hekRec, Bool.true_eq, Bool.false_eq_true,
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
    simp only [hctRec, Bool.true_eq, Bool.false_eq_true, if_true, if_false]
  all_goals
    by_cases hekRec : ρ.ack.ekRec = true <;>
      simp only [hekRec, Bool.true_eq, Bool.false_eq_true, if_true, if_false]
  all_goals simp only [hstale, if_false]
  all_goals
    by_cases hadvance : st.req.reqEpoch < ρ.tRes <;>
      simp only [hadvance, if_true, if_false]
  all_goals simp only [q, hadvance, if_true, if_false] at hnotpk
  all_goals simp only [hnotpk, if_false]
  all_goals
    by_cases hguard : q ∉ ack.ctRec
    · simp only [ack, q, hctRec, hekRec, hadvance, Bool.true_eq,
        Bool.false_eq_true, if_true, if_false] at hguard
      simp only [hguard, hbit, and_true, if_true]
      cases hdecode : (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch) with
      | mk chunksCt peerCt? =>
          cases hpeerCt : peerCt? with
          | none =>
              simp only [not_false_eq_true, if_true]
              by_cases hclearCt : st.res.resEpoch ∈ ack.ctRec <;>
                simp only [ack, hctRec, Bool.true_eq, Bool.false_eq_true,
                  if_true, if_false] at hclearCt <;>
                by_cases hclearEk : st.res.resEpoch + role.offset ∈ ack.ekRec <;>
                simp only [ack, hekRec, Bool.true_eq, Bool.false_eq_true,
                  if_true, if_false] at hclearEk <;>
                simp only [hclearCt, hclearEk, if_true, if_false,
                  Option.pure_def, Option.map_some]
          | some ciphertext =>
              cases hlookup :
                  (List.lookup (α := ℤ) (β := SK) q st.req.dk) with
              | none =>
                  simp only [q, hadvance, if_true, if_false] at hlookup
                  simp only [not_false_eq_true, if_true]
                  simp only [Option.bind_eq_bind, Function.comp_def,
                    Option.map_eq_map]
                  rw [hlookup]
                  simp only [Option.bind_none, Option.map_none]
              | some secretKey =>
                  cases hdecaps : (hDet.decapsDet secretKey ciphertext) with
                  | none =>
                      simp only [q, hadvance, if_true, if_false] at hlookup
                      simp only [not_false_eq_true, if_true]
                      simp only [Option.bind_eq_bind, Function.comp_def,
                        Option.map_eq_map]
                      rw [hlookup]
                      simp only [Option.bind_some]
                      rw [hdecaps]
                      simp only [Option.bind_none, Option.map_none]
                  | some key =>
                      simp only [q, hadvance, if_true, if_false] at hlookup
                      simp only [not_false_eq_true, if_true]
                      simp only [Option.bind_eq_bind, Function.comp_def,
                        Option.map_eq_map]
                      rw [hlookup]
                      simp only [Option.bind_some]
                      rw [hdecaps]
                      simp only [Option.bind_some, Option.map_some]
                      by_cases hclearCt :
                          st.res.resEpoch ∈ insert q ack.ctRec <;>
                        simp only [ack, q, hctRec, hadvance, Bool.true_eq,
                          Bool.false_eq_true, if_true, if_false] at hclearCt <;>
                        by_cases hclearEk :
                            st.res.resEpoch + role.offset ∈ ack.ekRec <;>
                        simp only [ack, hekRec, Bool.true_eq, Bool.false_eq_true,
                          if_true, if_false] at hclearEk <;>
                        simp only [hclearCt, hclearEk, if_true, if_false,
                          Option.pure_def, Option.map_some]
    · simp only [ack, q, hctRec, hekRec, hadvance, Bool.true_eq,
        Bool.false_eq_true, if_true, if_false] at hguard
      simp only [hguard, false_and, if_false]
      by_cases hclearCt : st.res.resEpoch ∈ ack.ctRec <;>
        simp only [ack, hctRec, Bool.true_eq, Bool.false_eq_true,
          if_true, if_false] at hclearCt <;>
        by_cases hclearEk : st.res.resEpoch + role.offset ∈ ack.ekRec <;>
        simp only [ack, hekRec, Bool.true_eq, Bool.false_eq_true,
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
    · simp only [hctRec, if_false]
      exact ht
  have hekSubset : st.ack.ekRec ⊆ ack.ekRec := by
    intro t ht
    unfold ack
    by_cases hekRec : ρ.ack.ekRec = true
    · simp only [hekRec, if_true]
      exact Finset.mem_insert_of_mem ht
    · simp only [hekRec, if_false]
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
      simp only [hctRec, Bool.true_eq, Bool.false_eq_true, if_true, if_false] at hview
    all_goals
      by_cases hekRec : ρ.ack.ekRec = true <;>
        simp only [hekRec, Bool.true_eq, Bool.false_eq_true, if_true, if_false] at hview
    all_goals simp only [hstale, if_true, Option.pure_def, Option.map_some] at hview
    all_goals
      have hadvance : ¬ st.req.reqEpoch < ρ.tRes :=
        not_lt.mpr (le_of_lt hstale)
      simp only [ack, hctRec, hekRec, if_true, if_false] at hctSubset hekSubset
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
        simp only [ack, hctRec, hekRec, if_true, if_false] at hctMem
        exact hctMem
      · intro hek
        rw [← hack]
        have hekMem := hekReported hek
        simp only [ack, hctRec, hekRec, if_true, if_false] at hekMem
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
    · simp only [hctRec, if_false]
      exact ht
  by_cases hstale : ρ.tRes < st.req.reqEpoch
  · have hkeyView := congrArg (Option.map fun out => out.1) hout
    simp only [Option.map_some] at hkeyView
    rw [recv] at hkeyView
    dsimp only at hkeyView
    by_cases hctRec : ρ.ack.ctRec = true <;>
      simp only [hctRec, Bool.true_eq, Bool.false_eq_true, if_true, if_false] at hkeyView
    all_goals
      by_cases hekRec : ρ.ack.ekRec = true <;>
        simp only [hekRec, Bool.true_eq, Bool.false_eq_true, if_true, if_false] at hkeyView
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
            simp only [decoded, hguard, if_true] at hdecode
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

theorem oracleRecvB_recorded_state_facts
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (s s' : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : MessageEpochsConsistent s)
    (n trcv : ℕ) (tI : Option ℕ)
    (hout : (some (trcv, tI), s') ∈ support
      ((SCKAScheme.oracleRecvB (scheme kem hDet ecEk ecCt leak) n).run s)) :
    ∃ ρ : Message Sym,
      s.msgA n = some (ρ, trcv) ∧
      ρ.sendingEpoch = trcv ∧
      s'.tcurB = max s.tcurB ρ.sendingEpoch ∧
      s'.tcurA = s.tcurA ∧
      s'.stA = s.stA ∧
      s'.stB.res.resEpoch = s.stB.res.resEpoch ∧
      s'.stB.req.reqEpoch =
        (if s.stB.req.reqEpoch < ρ.tRes then
          s.stB.req.reqEpoch + 2 else s.stB.req.reqEpoch) ∧
      s.stB.ack.ctRec ⊆ s'.stB.ack.ctRec ∧
      s.stB.ack.ekRec ⊆ s'.stB.ack.ekRec ∧
      s.stB.ack.sendingHorizon ≤ s'.stB.ack.sendingHorizon ∧
      (tI = none → s'.stB.req.dk = s.stB.req.dk) ∧
      (∀ t : ℕ, tI = some t →
        t = s'.stB.req.reqEpoch.toNat ∧
        s'.stB.req.reqEpoch ∈ s'.stB.ack.ctRec ∧
        s'.stB.req.dk.lookup s'.stB.req.reqEpoch = none ∧
        ∃ key : K, ∃ secretKey : SK, ∃ ciphertext : C,
          s'.keyB t = some key ∧
          s.stB.req.dk.lookup s'.stB.req.reqEpoch = some secretKey ∧
          (insertChunkAndDecode ecCt s.stB.req.receivedChunks ρ.ch).2 =
            some ciphertext ∧
          hDet.decapsDet secretKey ciphertext = some key) := by
  obtain ⟨ρ, hmsg, hepoch, htcurB, htcurA⟩ :=
    oracleRecvB_recorded_currentEpoch kem hDet ecEk ecCt leak s s' hs n trcv tI hout
  refine ⟨ρ, hmsg, hepoch, htcurB, htcurA, ?_⟩
  cases hrecv : recv .B kem hDet ecEk ecCt s.stB ρ with
  | none =>
      simp only [SCKAScheme.oracleRecvB, scheme, recvB, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map,
        StateT.run_set, map_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        Option.some.injEq] at hout
      cases hout.1
  | some out =>
      rcases out with ⟨key?, epoch, stB'⟩
      have hstate := recv_success_state_facts .B kem hDet ecEk ecCt s.stB ρ
        key? epoch stB' hrecv
      cases key? with
      | none =>
          simp only [SCKAScheme.oracleRecvB, scheme, recvB, bind_pure_comp,
            StateT.run_bind, StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map,
            StateT.run_set, map_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hout
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hout
          rcases hstate with ⟨_, hres, _, hreq, hct, hek, _, _, hdk⟩
          refine ⟨rfl, hres, hreq, hct, hek,
            Acknowledgements.sendingHorizon_mono _ _ hct, ?_, ?_⟩
          · intro _
            exact hdk rfl
          intro t ht
          cases ht
      | some keyOut =>
          rcases keyOut with ⟨epochI, key⟩
          have hkey := recv_emitted_key_facts .B kem hDet ecEk ecCt s.stB ρ
            epochI key epoch stB' hrecv
          simp only [SCKAScheme.oracleRecvB, scheme, recvB, bind_pure_comp,
            StateT.run_bind, StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map,
            StateT.run_set, map_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hout
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hout
          rcases hstate with ⟨_, hres, _, hreq, hct, hek, _, _, _⟩
          rcases hkey with ⟨_, _, htI, _, hin, _, hlookup, _, secretKey, ciphertext,
            hold, hdecode, hdecaps⟩
          refine ⟨rfl, hres, hreq, hct, hek,
            Acknowledgements.sendingHorizon_mono _ _ hct, ?_, ?_⟩
          · intro htI
            cases htI
          · intro t ht
            simp only [Option.some.injEq] at ht
            subst t
            refine ⟨htI, hin, hlookup, key, secretKey, ciphertext, ?_, hold, hdecode,
              hdecaps⟩
            exact Function.update_self ..

end oppBiKemCKA
