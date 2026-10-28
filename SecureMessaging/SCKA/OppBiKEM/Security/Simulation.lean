/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Eager

/-!
# Opp-BiKEM — The eager hybrid is the reduction's simulation

For a fixed draw of the target's key pair `(pk, sk)`, encapsulation `(c, kReal)` and random key
`kRand`, the eager hybrid `stoppedEagerExp` of bit `b` and the reduction's run on the KEM
challenge `(pk, c, k_b)`, with `k_b = kRand` if `b` is set and `kReal` otherwise, are the
injected oracles up to what the game state holds at the target epoch: the eager hybrid stores
the honest secret `sk` and records `kReal`, answering the challenge of `t` with `k_b` through
`eagerAnswer`; the reduction stores a placeholder secret and records `k_b`, answering from the
table. The state map `targetStateMap t dummy k_b` replaces the stored secret at `t` by `dummy`
and the table entries at `t` by `k_b`.

The main result `probOutput_stoppedEagerExp_eq_reductionRun` transports acceptance through the
state map with `probOutput_optionRun_eq_of_state_map_some`, whose per-query obligation compares
the answer and the mapped successor on continuing answers only. Every oracle commutes with the
map on an `InjInv` state with `t` unexposed:

* ordinary sends: the injected sends from the two injections are related by `sendWith_mapSecret`,
  a commutation of `sendWith` with the secret map for samplers that differ exactly as the map
  prescribes at the target sites;
* ideal receives: `recvWith` commutes with the map, since the ideal recovery ignores the secret
  and copies the mapped table value;
* challenges: both sides answer randomly below `t`, from the (equal) tables above `t`, and `k_b`
  at `t`, where the eager side reads the pinned entry `kReal`;
* corruptions and leaking sends: honest on both sides; a query that touches the target's secret
  or randomness stops with equal mass, every other query commutes with the map.

The placeholder secret is never read, since the receives are ideal, and the secret map is
discarded by every function of the state that the oracles compute (`vuln`, `rleakEpochs`, the
send guards).
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-! ## The state map -/

section StateMap

/-- Replace the secret of a retained key-pair entry at epoch `t` by `d`. -/
def secretMap (t : ℕ) (d : SK) (p : ℤ × SK) : ℤ × SK :=
  if p.1 = (t : ℤ) then (p.1, d) else p

@[simp] lemma secretMap_fst (t : ℕ) (d : SK) (p : ℤ × SK) : (secretMap t d p).1 = p.1 := by
  unfold secretMap; split_ifs <;> rfl

lemma secretMap_mk (t : ℕ) (d : SK) (e : ℤ) (sk : SK) :
    secretMap t d (e, sk) = (e, if e = (t : ℤ) then d else sk) := by
  unfold secretMap; split_ifs <;> rfl

@[simp] lemma secretMap_secretMap (t : ℕ) (d : SK) (p : ℤ × SK) :
    secretMap t d (secretMap t d p) = secretMap t d p := by
  unfold secretMap; split_ifs <;> simp_all

/-- Replace the retained secret at epoch `t` by `d`; every other field is unchanged. -/
def mapSecret (t : ℕ) (d : SK) (st : State PK SK C Sym) : State PK SK C Sym :=
  { st with req := { st.req with dk := st.req.dk.map (secretMap t d) } }

@[simp] lemma mapSecret_res (t : ℕ) (d : SK) (st : State PK SK C Sym) :
    (mapSecret t d st).res = st.res := rfl

@[simp] lemma mapSecret_ack (t : ℕ) (d : SK) (st : State PK SK C Sym) :
    (mapSecret t d st).ack = st.ack := rfl

@[simp] lemma mapSecret_reqEpoch (t : ℕ) (d : SK) (st : State PK SK C Sym) :
    (mapSecret t d st).req.reqEpoch = st.req.reqEpoch := rfl

@[simp] lemma mapSecret_ek (t : ℕ) (d : SK) (st : State PK SK C Sym) :
    (mapSecret t d st).req.ek = st.req.ek := rfl

@[simp] lemma mapSecret_receivedChunks (t : ℕ) (d : SK) (st : State PK SK C Sym) :
    (mapSecret t d st).req.receivedChunks = st.req.receivedChunks := rfl

@[simp] lemma mapSecret_dk (t : ℕ) (d : SK) (st : State PK SK C Sym) :
    (mapSecret t d st).req.dk = st.req.dk.map (secretMap t d) := rfl

lemma mapSecret_mapSecret (t : ℕ) (d : SK) (st : State PK SK C Sym) :
    mapSecret t d (mapSecret t d st) = mapSecret t d st := by
  simp [mapSecret, List.map_map, Function.comp_def]

@[simp] lemma sendKeygenGuard_mapSecret (role : Role) (t : ℕ) (d : SK)
    (st : State PK SK C Sym) : sendKeygenGuard role (mapSecret t d st) = sendKeygenGuard role st :=
  rfl

@[simp] lemma sendEncapsGuard_mapSecret (role : Role) (t : ℕ) (d : SK)
    (st : State PK SK C Sym) : sendEncapsGuard role (mapSecret t d st) = sendEncapsGuard role st :=
  rfl

@[simp] lemma sendGeneratesTarget_mapSecret (role : Role) (t t' : ℕ) (d : SK)
    (st : State PK SK C Sym) :
    sendGeneratesTarget role t' (mapSecret t d st) = sendGeneratesTarget role t' st := rfl

@[simp] lemma sendEncapsulatesTarget_mapSecret (role : Role) (t t' : ℕ) (d : SK)
    (st : State PK SK C Sym) :
    sendEncapsulatesTarget role t' (mapSecret t d st) = sendEncapsulatesTarget role t' st := rfl

@[simp] lemma rleakEpochs_mapSecret {RK RE : Type} (role : Role) (t : ℕ) (d : SK)
    (st : State PK SK C Sym) (rand : SendRand RK RE) :
    rleakEpochs role (mapSecret t d st) rand = rleakEpochs role st rand := rfl

@[simp] lemma vuln_mapSecret (t : ℕ) (d : SK) (st : State PK SK C Sym) :
    vuln (mapSecret t d st) = vuln st := by
  simp [vuln, List.map_map, Function.comp_def]

/-- Without a retained secret at `t`, the secret map is the identity. -/
lemma mapSecret_eq_self (t : ℕ) (d : SK) (st : State PK SK C Sym)
    (h : ∀ sk, ((t : ℤ), sk) ∉ st.req.dk) : mapSecret t d st = st := by
  unfold mapSecret
  have : st.req.dk.map (secretMap t d) = st.req.dk := by
    refine (List.map_congr_left fun p hp => ?_).trans (List.map_id _)
    unfold secretMap
    split_ifs with hp'
    · exact absurd (hp' ▸ hp) (h p.2)
    · rfl
  rw [this]

/-- Without the target among the vulnerable epochs, the secret map is the identity. -/
lemma mapSecret_eq_self_of_not_mem_vuln (t : ℕ) (ht : 0 < t) (d : SK) (st : State PK SK C Sym)
    (h : t ∉ vuln st) : mapSecret t d st = st :=
  mapSecret_eq_self t d st fun sk hsk => h ((mem_vuln_iff st t).2 ⟨ht, sk, hsk⟩)

/-- Looking up an epoch in the mapped secrets looks it up in the originals and maps the result
at `t`. -/
lemma lookup_map_secretMap (t : ℕ) (d : SK) (q : ℤ) (l : List (ℤ × SK)) :
    (l.map (secretMap t d)).lookup q =
      (l.lookup q).map fun sk => if q = (t : ℤ) then d else sk := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨e, sk⟩
    simp only [List.map_cons, secretMap_mk, List.lookup_cons]
    by_cases hq : q = e
    · subst hq; simp
    · have hne : (q == e) = false := beq_eq_false_iff_ne.mpr hq
      simp [hne, ih]

/-- Filtering by epoch commutes with the secret map. -/
lemma filter_map_secretMap (t : ℕ) (d : SK) (e : ℤ) (l : List (ℤ × SK)) :
    (l.map (secretMap t d)).filter (fun p => p.1 != e) =
      (l.filter (fun p => p.1 != e)).map (secretMap t d) := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun p _ => by simp [Function.comp]

/-- Replace the table entry at `t` by `k` where present. -/
def mapTable (t : ℕ) (k : K) (tbl : ℕ → Option K) : ℕ → Option K :=
  fun e => if e = t then (tbl e).map fun _ => k else tbl e

lemma mapTable_of_ne (t : ℕ) (k : K) (tbl : ℕ → Option K) (e : ℕ) (he : e ≠ t) :
    mapTable t k tbl e = tbl e := by
  simp [mapTable, he]

@[simp] lemma mapTable_self (t : ℕ) (k : K) (tbl : ℕ → Option K) :
    mapTable t k tbl t = (tbl t).map fun _ => k := by
  simp [mapTable]

@[simp] lemma mapTable_isSome (t : ℕ) (k : K) (tbl : ℕ → Option K) (e : ℕ) :
    (mapTable t k tbl e).isSome = (tbl e).isSome := by
  unfold mapTable; split_ifs <;> simp

@[simp] lemma mapTable_isNone (t : ℕ) (k : K) (tbl : ℕ → Option K) (e : ℕ) :
    (mapTable t k tbl e).isNone = (tbl e).isNone := by
  unfold mapTable; split_ifs <;> simp

@[simp] lemma knownPrefix_mapTable (t : ℕ) (k : K) (tbl : ℕ → Option K) (n : ℕ) :
    SCKAScheme.knownPrefix (mapTable t k tbl) n = SCKAScheme.knownPrefix tbl n := by
  simp [SCKAScheme.knownPrefix]

/-- The value an emitted or recorded key takes under the table map. -/
def mapKeyVal (t : ℕ) (k : K) (e : ℕ) (key : K) : K := if e = t then k else key

/-- The table map on an emitted key: the key at `t` becomes `k`. -/
def mapKey (t : ℕ) (k : K) : Option (ℕ × K) → Option (ℕ × K) :=
  Option.map fun p => (p.1, mapKeyVal t k p.1 p.2)

@[simp] lemma mapKey_none (t : ℕ) (k : K) : mapKey t k (none : Option (ℕ × K)) = none := rfl

@[simp] lemma mapKey_some (t : ℕ) (k : K) (e : ℕ) (key : K) :
    mapKey t k (some (e, key)) = some (e, mapKeyVal t k e key) := rfl

@[simp] lemma mapKey_map_fst (t : ℕ) (k : K) (key? : Option (ℕ × K)) :
    (mapKey t k key?).map Prod.fst = key?.map Prod.fst := by
  rcases key? with _ | ⟨e, key⟩ <;> rfl

/-- Updating a table commutes with the table map. -/
lemma mapTable_update (t : ℕ) (k : K) (tbl : ℕ → Option K) (e : ℕ) (key : K) :
    mapTable t k (Function.update tbl e (some key)) =
      Function.update (mapTable t k tbl) e (some (mapKeyVal t k e key)) := by
  funext x
  simp only [mapTable, Function.update_apply, mapKeyVal]
  by_cases hx : x = e <;> by_cases hx' : x = t <;> subst_vars <;> simp_all

/-- The state map from the eager hybrid to the reduction's simulation: the retained secret at
`t` becomes `d` in both parties' states and the table entries at `t` become `k`. -/
def targetStateMap (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) :=
  { s with stA := mapSecret t d s.stA, stB := mapSecret t d s.stB,
           keyA := mapTable t k s.keyA, keyB := mapTable t k s.keyB }

@[simp] lemma targetStateMap_stA (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).stA = mapSecret t d s.stA := rfl

@[simp] lemma targetStateMap_stB (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).stB = mapSecret t d s.stB := rfl

@[simp] lemma targetStateMap_keyA (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).keyA = mapTable t k s.keyA := rfl

@[simp] lemma targetStateMap_keyB (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).keyB = mapTable t k s.keyB := rfl

@[simp] lemma targetStateMap_msgA (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).msgA = s.msgA := rfl

@[simp] lemma targetStateMap_msgB (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).msgB = s.msgB := rfl

@[simp] lemma targetStateMap_correct (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).correct = s.correct := rfl

@[simp] lemma targetStateMap_tcurA (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).tcurA = s.tcurA := rfl

@[simp] lemma targetStateMap_tcurB (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).tcurB = s.tcurB := rfl

@[simp] lemma targetStateMap_nA (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).nA = s.nA := rfl

@[simp] lemma targetStateMap_nB (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).nB = s.nB := rfl

@[simp] lemma targetStateMap_exposed (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).exposed = s.exposed := rfl

@[simp] lemma targetStateMap_challenged (t : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    (targetStateMap t d k s).challenged = s.challenged := rfl

@[simp] lemma targetExposed_targetStateMap (t t' : ℕ) (d : SK) (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    targetExposed t' (targetStateMap t d k s) = targetExposed t' s := rfl

/-- The initial state is fixed by the state map: no secret and no key is stored. -/
lemma targetStateMap_init (t : ℕ) (d : SK) (k : K) :
    targetStateMap t d k (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) =
      initState := by
  have h : mapTable t k (fun _ => none : ℕ → Option K) = fun _ => none := by
    funext e; simp [mapTable]
  simp [targetStateMap, initState, SCKAScheme.initGameState, mapSecret, initialState, h]

end StateMap

/-! ## Commutation of one send and one receive with the state map -/

section Commute

/-- For a positive `t`, an integer has `toNat` equal to `t` exactly when it equals `t`. -/
lemma toNat_eq_iff_of_pos {m : ℤ} {t : ℕ} (ht : 0 < t) : m.toNat = t ↔ m = (t : ℤ) :=
  ⟨eq_of_toNat_eq_of_pos ht, fun h => by rw [h, Int.toNat_natCast]⟩

/-- The state map on a send output: the emitted key at `t` becomes `k` and the retained secret
at `t` becomes `d`. -/
def mapSendOut {RK RE : Type} (t : ℕ) (d : SK) (k : K)
    (out : Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym × SendRand RK RE) :
    Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym × SendRand RK RE :=
  (mapKey t k out.1, out.2.1, out.2.2.1, mapSecret t d out.2.2.2.1, out.2.2.2.2)

/-- `sendWith` commutes with the state map, for samplers that differ exactly as the map
prescribes: the secret generated at key epoch `t` is `d` on the mapped side, and the key
encapsulated at responder epoch `t` is `k`. The sampler hypotheses are needed only when the
corresponding guard holds. -/
lemma sendWith_mapSecret {RK RE : Type} (role : Role) (t : ℕ) (ht : 0 < t) (d : SK) (k : K)
    (keygen keygen' : ProbComp ((PK × SK) × RK)) (encaps encaps' : PK → ProbComp ((C × K) × RE))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (st : State PK SK C Sym)
    (hk : sendKeygenGuard role st = true → keygen' =
      (fun x => ((x.1.1, if st.res.resEpoch + 2 + role.offset = (t : ℤ) then d else x.1.2), x.2))
        <$> keygen)
    (he : sendEncapsGuard role st = true → encaps' = fun pk =>
      (fun y => ((y.1.1, if st.res.resEpoch + (if sendKeygenGuard role st then 2 else 0) = (t : ℤ)
        then k else y.1.2), y.2)) <$> encaps pk) :
    sendWith role keygen' encaps' ecEk ecCt (mapSecret t d st) =
      Option.map (mapSendOut t d k) <$> sendWith role keygen encaps ecEk ecCt st := by
  obtain ⟨⟨reqEpoch, dk, ek, chunks⟩, ⟨resEpoch, ekPeer, ct, ich⟩, ack⟩ := st
  simp only [sendKeygenGuard, sendEncapsGuard] at hk he
  by_cases hg : (ek.isNone && decide (resEpoch ∈ ack.ctRec ∧ resEpoch + role.offset ∈ ack.ctRec))
      = true
  · rw [hk hg]
    clear hk
    simp only [hg, if_true] at he
    unfold sendWith
    dsimp only [mapSecret]
    simp only [hg, ↓reduceIte, bind_map_left, map_bind]
    refine bind_congr fun x => ?_
    generalize hsk : (if resEpoch + 2 + role.offset = (t : ℤ) then d else x.1.2) = sk'
    by_cases hEnc : (decide (resEpoch + 2 + role.offset ∈ ack.ekRec) &&
        decide (resEpoch + 2 ∉ ack.ctRec) && ct.isNone && decide (resEpoch + 2 ∈ ack.ekRec)) = true
    · rw [he hEnc]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hEnc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hEnc
      simp only [h1, h2, h3, h4, not_true_eq_false, not_false_eq_true, decide_true, Bool.and_self,
        ↓reduceIte]
      generalize ekPeer (resEpoch + 2) = o
      cases o with
      | none => simp
      | some peerEk =>
        simp only [bind_map_left, map_bind]
        refine bind_congr fun y => ?_
        simp [mapSendOut, secretMap_mk, filter_map_secretMap, mapSecret, mapKeyVal,
          toNat_eq_iff_of_pos ht, hsk]
    · clear he
      split_ifs with h1 h2 h3
      all_goals first
        | (simp [mapSendOut, secretMap_mk, filter_map_secretMap, mapSecret, hsk]; done)
        | (exfalso; exact hEnc (by simp_all))
  · have hg' := Bool.eq_false_iff.mpr hg
    clear hk
    simp only [hg', Bool.false_eq_true, if_false, add_zero] at he
    unfold sendWith
    dsimp only [mapSecret]
    simp only [hg', Bool.false_eq_true, ↓reduceIte]
    by_cases hEnc : (decide (resEpoch + role.offset ∈ ack.ekRec) &&
        decide (resEpoch ∉ ack.ctRec) && ct.isNone && decide (resEpoch ∈ ack.ekRec)) = true
    · rw [he hEnc]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hEnc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hEnc
      simp only [h1, h2, h3, h4, not_true_eq_false, not_false_eq_true, decide_true, Bool.and_self,
        ↓reduceIte]
      generalize ekPeer resEpoch = o
      cases o with
      | none => simp
      | some peerEk =>
        simp only [bind_map_left, map_bind]
        refine bind_congr fun y => ?_
        simp [mapSendOut, mapSecret, mapKeyVal, toNat_eq_iff_of_pos ht]
    · clear he
      split_ifs with h1 h2 h3
      all_goals first
        | (simp [mapSendOut, mapSecret]; done)
        | ((cases ek <;> simp [mapSendOut, mapSecret]); done)
        | (exfalso; exact hEnc (by simp_all))

/-- The randomness of a send does not depend on the stored secrets: projecting a `sendWith`
output to its randomness gives the same computation from `st` and from the mapped state. -/
lemma sendWith_rand_mapSecret {RK RE : Type} (role : Role) (t : ℕ) (ht : 0 < t) (d : SK) (k : K)
    (keygen : ProbComp ((PK × SK) × RK)) (encaps : PK → ProbComp ((C × K) × RE))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    (Option.map fun o : Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym × SendRand RK RE =>
        o.2.2.2.2) <$> sendWith role keygen encaps ecEk ecCt (mapSecret t d st) =
      (Option.map fun o : Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym × SendRand RK RE =>
        o.2.2.2.2) <$> sendWith role keygen encaps ecEk ecCt st := by
  have h1 := sendWith_mapSecret role t ht d k keygen _ encaps _ ecEk ecCt st (fun _ => rfl)
    (fun _ => rfl)
  have h2 : sendWith role
      ((fun x => ((x.1.1, if st.res.resEpoch + 2 + role.offset = (t : ℤ) then d else x.1.2), x.2))
        <$> keygen)
      (fun pk => (fun y => ((y.1.1, if st.res.resEpoch +
        (if sendKeygenGuard role st then 2 else 0) = (t : ℤ) then k else y.1.2), y.2)) <$>
          encaps pk)
      ecEk ecCt (mapSecret t d (mapSecret t d st)) =
      Option.map (mapSendOut t d k) <$> sendWith role keygen encaps ecEk ecCt (mapSecret t d st) :=
    sendWith_mapSecret role t ht d k keygen _ encaps _ ecEk ecCt (mapSecret t d st)
      (fun _ => rfl) (fun _ => rfl)
  rw [mapSecret_mapSecret] at h2
  have h3 : ∀ X : ProbComp (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
      SendRand RK RE)),
      (Option.map fun o : Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
          SendRand RK RE => o.2.2.2.2) <$> (Option.map (mapSendOut t d k) <$> X) =
        (Option.map fun o : Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
          SendRand RK RE => o.2.2.2.2) <$> X := by
    intro X
    rw [Functor.map_map]
    congr 1
    funext o
    rcases o with _ | o
    · rfl
    · rfl
  calc _ = (Option.map fun o : Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
          SendRand RK RE => o.2.2.2.2) <$> (Option.map (mapSendOut t d k) <$>
          sendWith role keygen encaps ecEk ecCt (mapSecret t d st)) := (h3 _).symm
    _ = _ := by rw [← h2, h1, h3]

/-- The state map on a receive output: the emitted key at `t` becomes `k` and the retained
secret at `t` becomes `d`. -/
def mapRecvOut (t : ℕ) (d : SK) (k : K) (out : Option (ℕ × K) × ℕ × State PK SK C Sym) :
    Option (ℕ × K) × ℕ × State PK SK C Sym :=
  (mapKey t k out.1, out.2.1, mapSecret t d out.2.2)

/-- The ideal receive commutes with the state map: the ideal recovery ignores the retained
secret and copies the table value, which the map replaces at `t`. -/
lemma recvWith_idealRecover_mapSecret [DecidableEq Sym] (role : Role) (t : ℕ) (d : SK) (k : K)
    (tbl : ℕ → Option K) (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    recvWith role (idealRecover (mapTable t k tbl)) ecEk ecCt (mapSecret t d st) ρ =
      (recvWith role (idealRecover tbl) ecEk ecCt st ρ).map (mapRecvOut t d k) := by
  have hfin : ∀ q e dk ch ack, recvFinish role (mapSecret t d st) q e (dk.map (secretMap t d)) ch
      ack = mapSecret t d (recvFinish role st q e dk ch ack) := by
    intro q e dk ch ack
    rfl
  have hreq : recvReq (mapSecret t d st) ρ = recvReq st ρ := rfl
  unfold recvWith
  simp only [mapSecret_ack, mapSecret_reqEpoch, mapSecret_res, mapSecret_receivedChunks,
    mapSecret_dk, hreq, filter_map_secretMap, hfin]
  split_ifs with h1 h2 h3
  · rfl
  · rcases hdec : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 with _ | pk <;>
      dsimp only <;> rfl
  · rcases hdec : (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).2 with _ | c
    · dsimp only
      rfl
    · simp only [lookup_map_secretMap]
      rcases st.req.dk.lookup (recvReq st ρ) with _ | sk
      · rfl
      · simp only [Option.map_some, idealRecover, mapTable]
        rcases tbl (recvReq st ρ).toNat with _ | k'
        · simp
        · by_cases hq : (recvReq st ρ).toNat = t <;> simp [hq, mapRecvOut, mapKey, mapKeyVal]
  · rfl

end Commute

/-! ## The eager oracles preserve the invariant on continuing successors -/

section Preservation

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
  (t : ℕ) (inj : TargetInjection PK SK C K)
  (hpk : (inj.pk, inj.sk) ∈ support kem.keygen)
  (hct : (inj.ct, inj.key) ∈ support (kem.encaps inj.pk)) (ht : 0 < t)

include hEk hCt hpk hct ht in
/-- Every eager security query from an `InjInv` state keeps `InjInv` on the successors that
leave the target unexposed: the eager challenge only touches bookkeeping, and the other oracles
are the injected ones. -/
theorem eagerSecurityImpl_preservesInv_continuing (b : Bool) (kRand : K)
    (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) :
    ∀ z ∈ support ((eagerSecurityImpl kem hDet ecEk ecCt leak t inj b kRand q).run s),
      t ∉ z.2.exposed → InjInv kem ecEk ecCt t inj z.2 := by
  intro z hz hexp
  rcases q with (((((q | u) | u) | e) | u) | u)
  · rcases q with (((n | u) | u) | n) | n
    · exact SCKAScheme.oracleUnif_preservesInv (InjInv kem ecEk ecCt t inj) n s hs z hz
    · cases u
      exact injInv_sendA_step kem hDet ecEk ecCt leak t inj hpk hct ht s hs z hz
    · cases u
      exact injInv_sendB_step kem hDet ecEk ecCt leak t inj hpk hct ht s hs z hz
    · exact injInv_recvA_step kem hDet ecEk ecCt hEk hCt leak t inj ht n s hs z hz
    · exact injInv_recvB_step kem hDet ecEk ecCt hEk hCt leak t inj ht n s hs z hz
  · cases u
    exact injInv_sendArleak_step kem hDet ecEk ecCt leak t inj ht s hs z hz hexp
  · cases u
    exact injInv_sendBrleak_step kem hDet ecEk ecCt leak t inj ht s hs z hz hexp
  · rcases SCKAScheme.oracleChallWith_support _ s e z hz with ⟨rfl, -⟩ | ⟨-, -, h⟩
    · exact hs
    · rw [h]
      exact hs
  · cases u
    rcases SCKAScheme.oracleCorruptA_support _ s z hz with rfl | ⟨-, rfl⟩ <;> exact hs
  · cases u
    rcases SCKAScheme.oracleCorruptB_support _ s z hz with rfl | ⟨-, rfl⟩ <;> exact hs

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] hDet leak in
/-- On an `InjInv` state both tables are empty or the injected key at `t`. -/
lemma injInv_tables_pinned
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) :
    (s.keyA t = none ∨ s.keyA t = some inj.key) ∧
      (s.keyB t = none ∨ s.keyB t = some inj.key) := by
  cases ho : targetOwner t
  · obtain ⟨-, h⟩ := (injInv_A ho).1 hs
    exact ⟨h.table_own, h.table_peer⟩
  · obtain ⟨-, h⟩ := (injInv_B ho).1 hs
    exact ⟨h.table_peer, h.table_own⟩

end Preservation

/-! ## The oracles commute with the state map -/

section Steps

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
  (t : ℕ) (ht : 0 < t) (pk : PK) (sk dummy : SK) (c : C) (kReal kRand : K) (b : Bool)

omit [DecidableEq K] [SampleableType K] in
/-- The table map reads as a map of the entry. -/
lemma mapTable_eq_map (k : K) (tbl : ℕ → Option K) (e : ℕ) :
    mapTable t k tbl e = (tbl e).map (mapKeyVal t k e) := by
  unfold mapTable mapKeyVal
  split_ifs <;> simp

omit [DecidableEq K] [DecidableEq Sym] hDet leak in
/-- The eager answer on a pinned state is the hybrid answer at the mapped key: random below `t`,
the mapped entry `k_b` at `t`, the entry above `t`. -/
lemma eagerAnswer_eq_mapped
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t ⟨pk, sk, c, kReal⟩ s) (e : ℕ) (k : K)
    (hk : s.keyA e = some k ∨ (s.keyA e = none ∧ s.keyB e = some k)) :
    eagerAnswer t b kRand e k = if hybridRandom t e then ($ᵗ K : ProbComp K)
      else pure (mapKeyVal t (if b then kRand else kReal) e k) := by
  unfold eagerAnswer hybridRandom mapKeyVal
  by_cases hlt : e < t
  · simp [hlt]
  by_cases het : e = t
  · subst het
    cases b
    · have hpin := injInv_tables_pinned kem ecEk ecCt e ⟨pk, sk, c, kReal⟩ s hs
      have hkey : k = kReal := by
        rcases hk with hA | ⟨-, hB⟩
        · rcases hpin.1 with h | h <;> simp_all
        · rcases hpin.2 with h | h <;> simp_all
      simp [hkey]
    · simp
  · simp [hlt, het]

omit [DecidableEq K] [DecidableEq Sym] hDet leak in
/-- The challenge oracles commute with the state map. -/
lemma chall_step
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t ⟨pk, sk, c, kReal⟩ s) (e : ℕ) :
    (SCKAScheme.oracleChallOn (hybridRandom t) (StA PK SK C Sym) (StB PK SK C Sym) K
        (Message Sym) e).run (targetStateMap t dummy (if b then kRand else kReal) s) =
      Prod.map id (targetStateMap t dummy (if b then kRand else kReal)) <$>
        (SCKAScheme.oracleChallWith (eagerAnswer t b kRand) (StA PK SK C Sym) (StB PK SK C Sym)
          (Message Sym) e).run s := by
  rw [SCKAScheme.oracleChallOn_run_eq_oracleChallWith]
  set kb := if b then kRand else kReal with hkb
  have hA : (targetStateMap t dummy kb s).keyA e = (s.keyA e).map (mapKeyVal t kb e) :=
    mapTable_eq_map t kb s.keyA e
  have hB : (targetStateMap t dummy kb s).keyB e = (s.keyB e).map (mapKeyVal t kb e) :=
    mapTable_eq_map t kb s.keyB e
  by_cases hrej : e ∈ s.exposed ∨ e ∈ s.challenged
  · rw [SCKAScheme.oracleChallWith_rejected _ s e hrej,
      SCKAScheme.oracleChallWith_rejected _ _ e (by simpa using hrej)]
    simp
  have hrej' : ¬(e ∈ (targetStateMap t dummy kb s).exposed ∨
      e ∈ (targetStateMap t dummy kb s).challenged) := by simpa using hrej
  rcases hkA : s.keyA e with _ | k
  · rcases hkB : s.keyB e with _ | k
    · rw [SCKAScheme.oracleChallWith_unavailable _ s e hkA hkB,
        SCKAScheme.oracleChallWith_unavailable _ _ e (by simp [hA, hkA]) (by simp [hB, hkB])]
      simp
    · rw [SCKAScheme.oracleChallWith_eligible _ s e hrej k (Or.inr ⟨hkA, hkB⟩),
        SCKAScheme.oracleChallWith_eligible _ _ e hrej' (mapKeyVal t kb e k)
          (Or.inr ⟨by simp [hA, hkA], by simp [hB, hkB]⟩),
        eagerAnswer_eq_mapped kem ecEk ecCt t pk sk c kReal kRand b s hs e k (Or.inr ⟨hkA, hkB⟩)]
      simp only [map_bind, map_pure]
      rfl
  · rw [SCKAScheme.oracleChallWith_eligible _ s e hrej k (Or.inl hkA),
      SCKAScheme.oracleChallWith_eligible _ _ e hrej' (mapKeyVal t kb e k)
        (Or.inl (by simp [hA, hkA])),
      eagerAnswer_eq_mapped kem ecEk ecCt t pk sk c kReal kRand b s hs e k (Or.inl hkA)]
    simp only [map_bind, map_pure]
    rfl

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] hDet leak in
/-- The uniform-sampling oracle commutes with the state map. -/
lemma unif_step (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) (n : ℕ) :
    (SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) n).run
        (targetStateMap t dummy k s) =
      Prod.map id (targetStateMap t dummy k) <$>
        (SCKAScheme.oracleUnif (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) n).run s := by
  rw [SCKAScheme.oracleUnif_run_eq, SCKAScheme.oracleUnif_run_eq, Functor.map_map]
  rfl

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] hDet in
include ht in
/-- A's corruption commutes with the state map on the stopped answers: a corruption that
reveals the target's secret stops on both sides, and otherwise the secret map is the identity
on A's state. -/
lemma corruptA_step (k : K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : t ∉ s.exposed) :
    𝒟[(fun z => z.1.map fun a => (a, z.2)) <$>
        ((stopOnState (SCKAScheme.oracleCorruptA (exposure .A leak).corrupt (StB PK SK C Sym) K
          (Message Sym)) (targetExposed t) ()).run).run (targetStateMap t dummy k s)] =
      𝒟[(fun z => z.1.map fun a => (a, targetStateMap t dummy k z.2)) <$>
        ((stopOnState (SCKAScheme.oracleCorruptA (exposure .A leak).corrupt (StB PK SK C Sym) K
          (Message Sym)) (targetExposed t) ()).run).run s] := by
  have hrun : ∀ u, ((stopOnState (SCKAScheme.oracleCorruptA (exposure .A leak).corrupt
      (StB PK SK C Sym) K (Message Sym)) (targetExposed t) ()).run).run u = (do
        let z ← (SCKAScheme.oracleCorruptA (exposure .A leak).corrupt (StB PK SK C Sym) K
          (Message Sym) ()).run u
        pure (if targetExposed t z.2 then none else some z.1, z.2)) := fun u => rfl
  rw [hrun, hrun, SCKAScheme.oracleCorruptA_run, SCKAScheme.oracleCorruptA_run]
  simp only [exposure_corrupt, targetStateMap_stA, vuln_mapSecret, targetStateMap_challenged,
    targetStateMap_exposed]
  by_cases hconf : vuln s.stA ∩ s.challenged ≠ ∅
  · simp [hconf, targetExposed, hs]
  · by_cases hv : t ∈ vuln s.stA
    · simp [hconf, targetExposed, hv]
    · rw [mapSecret_eq_self_of_not_mem_vuln t ht dummy s.stA hv]
      simp [hconf, targetExposed, hv, hs, targetStateMap,
        mapSecret_eq_self_of_not_mem_vuln t ht dummy s.stA hv]

end Steps

/-! ## The game-state updates of a send commute with the state map -/

section Updates

variable [DecidableEq K] (t : ℕ) (d : SK) (k : K)

omit [DecidableEq K] in
/-- `knownPrefix` reads only which entries are present, which the table map keeps. -/
lemma knownPrefix_update_mapTable (tbl : ℕ → Option K) (e : ℕ) (v v' : K) (n : ℕ) :
    SCKAScheme.knownPrefix (Function.update (mapTable t k tbl) e (some v)) n =
      SCKAScheme.knownPrefix (Function.update tbl e (some v')) n := by
  simp only [SCKAScheme.knownPrefix]
  congr 1
  funext x
  by_cases hx : x = e <;> simp [hx]

/-- The key-consistency assertion of a table update holds after the table map whenever it held
before. -/
lemma consistent_mapTable (tbl : ℕ → Option K) (e : ℕ) (key : K)
    (h : ((tbl e).isNone || tbl e == some key) = true) :
    ((tbl e).isNone || mapTable t k tbl e == some (mapKeyVal t k e key)) = true := by
  rw [mapTable_eq_map]
  rcases hv : tbl e with _ | v
  · simp
  · simp only [hv, Option.isNone_some, Bool.false_or, beq_iff_eq, Option.some.injEq] at h
    simp [h]

/-- A's send update commutes with the state map, provided the correctness flag holds after the
update: every assertion then holds, and the mapped assertions follow. -/
lemma sendAUpdate_map (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K
      (Message Sym)) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (stA' : State PK SK C Sym)
    (hcorr : (SCKAScheme.sendAUpdate s key? ρ tsnd stA').correct = true) :
    SCKAScheme.sendAUpdate (targetStateMap t d k s) (mapKey t k key?) ρ tsnd
        (mapSecret t d stA') =
      targetStateMap t d k (SCKAScheme.sendAUpdate s key? ρ tsnd stA') := by
  rcases key? with _ | ⟨tI, key⟩
  · simp [SCKAScheme.sendAUpdate, targetStateMap]
    try rfl
  · simp only [SCKAScheme.sendAUpdate, mapKey_some, targetStateMap]
    have hcorr' := hcorr
    simp only [SCKAScheme.sendAUpdate, Bool.and_eq_true] at hcorr'
    obtain ⟨⟨⟨⟨hc, hmono⟩, huniq⟩, hcons⟩, hknown⟩ := hcorr'
    congr 1
    · exact (mapTable_update t k s.keyA tI key).symm
    · simp only [mapTable_isNone]
      rw [hc, hmono, huniq, hcons, hknown, consistent_mapTable t k s.keyB tI key hcons,
        knownPrefix_update_mapTable t k s.keyA tI _ key, hknown]
      simp [of_decide_eq_true hmono]

/-- B's send update commutes with the state map, under the same correctness proviso. -/
lemma sendBUpdate_map (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K
      (Message Sym)) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (stB' : State PK SK C Sym)
    (hcorr : (SCKAScheme.sendBUpdate s key? ρ tsnd stB').correct = true) :
    SCKAScheme.sendBUpdate (targetStateMap t d k s) (mapKey t k key?) ρ tsnd
        (mapSecret t d stB') =
      targetStateMap t d k (SCKAScheme.sendBUpdate s key? ρ tsnd stB') := by
  rcases key? with _ | ⟨tI, key⟩
  · simp [SCKAScheme.sendBUpdate, targetStateMap]
    try rfl
  · simp only [SCKAScheme.sendBUpdate, mapKey_some, targetStateMap]
    have hcorr' := hcorr
    simp only [SCKAScheme.sendBUpdate, Bool.and_eq_true] at hcorr'
    obtain ⟨⟨⟨⟨hc, hmono⟩, huniq⟩, hcons⟩, hknown⟩ := hcorr'
    congr 1
    · exact (mapTable_update t k s.keyB tI key).symm
    · simp only [mapTable_isNone]
      rw [hc, hmono, huniq, hcons, hknown, consistent_mapTable t k s.keyA tI key hcons,
        knownPrefix_update_mapTable t k s.keyB tI _ key, hknown]
      simp [of_decide_eq_true hmono]

/-- A's receive update commutes with the state map, under the same correctness proviso. -/
lemma recvAUpdate_map (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K
      (Message Sym)) (tsnd : ℕ) (key? : Option (ℕ × K)) (trcv : ℕ)
    (stA' : State PK SK C Sym)
    (hcorr : (SCKAScheme.recvAUpdate s tsnd key? trcv stA').correct = true) :
    SCKAScheme.recvAUpdate (targetStateMap t d k s) tsnd (mapKey t k key?) trcv
        (mapSecret t d stA') =
      targetStateMap t d k (SCKAScheme.recvAUpdate s tsnd key? trcv stA') := by
  rcases key? with _ | ⟨tI, key⟩
  · simp [SCKAScheme.recvAUpdate, targetStateMap]
    try rfl
  · simp only [SCKAScheme.recvAUpdate, mapKey_some, targetStateMap]
    have hcorr' := hcorr
    simp only [SCKAScheme.recvAUpdate, Bool.and_eq_true] at hcorr'
    obtain ⟨⟨⟨⟨hc, hmatch⟩, huniq⟩, hcons⟩, hknown⟩ := hcorr'
    congr 1
    · exact (mapTable_update t k s.keyA tI key).symm
    · simp only [mapTable_isNone]
      rw [hc, hmatch, huniq, hcons, hknown, consistent_mapTable t k s.keyB tI key hcons,
        knownPrefix_update_mapTable t k s.keyA tI _ key, hknown]

/-- B's receive update commutes with the state map, under the same correctness proviso. -/
lemma recvBUpdate_map (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K
      (Message Sym)) (tsnd : ℕ) (key? : Option (ℕ × K)) (trcv : ℕ)
    (stB' : State PK SK C Sym)
    (hcorr : (SCKAScheme.recvBUpdate s tsnd key? trcv stB').correct = true) :
    SCKAScheme.recvBUpdate (targetStateMap t d k s) tsnd (mapKey t k key?) trcv
        (mapSecret t d stB') =
      targetStateMap t d k (SCKAScheme.recvBUpdate s tsnd key? trcv stB') := by
  rcases key? with _ | ⟨tI, key⟩
  · simp [SCKAScheme.recvBUpdate, targetStateMap]
    try rfl
  · simp only [SCKAScheme.recvBUpdate, mapKey_some, targetStateMap]
    have hcorr' := hcorr
    simp only [SCKAScheme.recvBUpdate, Bool.and_eq_true] at hcorr'
    obtain ⟨⟨⟨⟨hc, hmatch⟩, huniq⟩, hcons⟩, hknown⟩ := hcorr'
    congr 1
    · exact (mapTable_update t k s.keyB tI key).symm
    · simp only [mapTable_isNone]
      rw [hc, hmatch, huniq, hcons, hknown, consistent_mapTable t k s.keyA tI key hcons,
        knownPrefix_update_mapTable t k s.keyB tI _ key, hknown]

end Updates

/-! ## Sends, receives and corruptions commute with the state map -/

section OracleSteps

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
  (t : ℕ) (ht : 0 < t) (pk : PK) (sk : SK) (c : C) (kReal : K) (d : SK) (k : K)

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] hDet leak in
include ht in
/-- The injected send with the mapped injection from the mapped state is the injected send with
the original injection, mapped: the two injections differ exactly as the map prescribes at the
target sites. -/
lemma injectedSend_mapSecret (role : Role) (st : State PK SK C Sym) :
    injectedSend kem role ecEk ecCt t ⟨pk, d, c, k⟩ (mapSecret t d st) =
      (Option.map fun o : Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym =>
        (mapKey t k o.1, o.2.1, o.2.2.1, mapSecret t d o.2.2.2)) <$>
        injectedSend kem role ecEk ecCt t ⟨pk, sk, c, kReal⟩ st := by
  have hk : sendKeygenGuard role st = true →
      injectedKeygen kem role t ⟨pk, d, c, k⟩ (mapSecret t d st) =
        (fun x => ((x.1.1, if st.res.resEpoch + 2 + role.offset = (t : ℤ) then d else x.1.2),
          x.2)) <$> injectedKeygen kem role t ⟨pk, sk, c, kReal⟩ st := by
    intro hg
    have hgen : sendGeneratesTarget role t st =
        decide (st.res.resEpoch + 2 + role.offset = (t : ℤ)) := by
      simp [sendGeneratesTarget, hg]
    simp only [injectedKeygen, sendGeneratesTarget_mapSecret, hgen]
    by_cases hc : st.res.resEpoch + 2 + role.offset = (t : ℤ) <;> simp [hc]
  have he : sendEncapsGuard role st = true →
      injectedEncaps kem role t ⟨pk, d, c, k⟩ (mapSecret t d st) = fun pk' =>
        (fun y => ((y.1.1, if st.res.resEpoch + (if sendKeygenGuard role st then 2 else 0) =
          (t : ℤ) then k else y.1.2), y.2)) <$>
          injectedEncaps kem role t ⟨pk, sk, c, kReal⟩ st pk' := by
    intro hg
    funext pk'
    have henc : sendEncapsulatesTarget role t st =
        decide (st.res.resEpoch + (if sendKeygenGuard role st then 2 else 0) = (t : ℤ)) := by
      simp [sendEncapsulatesTarget, hg]
    simp only [injectedEncaps, sendEncapsulatesTarget_mapSecret, henc]
    by_cases hc : st.res.resEpoch + (if sendKeygenGuard role st then 2 else 0) = (t : ℤ) <;>
      simp [hc]
  unfold injectedSend
  rw [sendWith_mapSecret role t ht d k _ _ _ _ ecEk ecCt st hk he]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr fun out => ?_
  rcases out with _ | ⟨key?, ρ, tsnd, st', rand⟩ <;> rfl

omit [SampleableType K] in
include ht in
/-- A's ordinary send commutes with the state map on `InjInv` states with supported injected
values. -/
lemma sendA_step (hx : (pk, sk) ∈ support kem.keygen)
    (hy : (c, kReal) ∈ support (kem.encaps pk))
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t ⟨pk, sk, c, kReal⟩ s) :
    𝒟[(SCKAScheme.oracleSendA (injectedScheme kem hDet ecEk ecCt leak t ⟨pk, d, c, k⟩) ()).run
        (targetStateMap t d k s)] =
      𝒟[Prod.map id (targetStateMap t d k) <$>
        (SCKAScheme.oracleSendA (injectedScheme kem hDet ecEk ecCt leak t ⟨pk, sk, c, kReal⟩)
          ()).run s] := by
  rw [SCKAScheme.oracleSendA_run_eq, SCKAScheme.oracleSendA_run_eq]
  simp only [injectedScheme, targetStateMap_stA]
  rw [injectedSend_mapSecret kem ecEk ecCt t ht pk sk c kReal d k .A s.stA, Functor.map_map]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  apply evalDist_bind_congr
  intro out hout
  rcases out with _ | ⟨key?, ρ, tsnd, stA'⟩
  · rfl
  · have hcorr : (SCKAScheme.sendAUpdate s key? ρ tsnd stA').correct = true :=
      (injInv_sendA_step kem hDet ecEk ecCt leak t ⟨pk, sk, c, kReal⟩ hx hy ht s hs
        (some (tsnd, key?.map Prod.fst, ρ), SCKAScheme.sendAUpdate s key? ρ tsnd stA')
        ((SCKAScheme.mem_support_oracleSendA_run_iff _ s _).2 ⟨_, hout, rfl⟩)).1.1
    simp only [Function.comp_apply, Option.map_some, mapKey_map_fst, Prod.map, id]
    rw [sendAUpdate_map t d k s key? ρ tsnd stA' hcorr]

omit [SampleableType K] in
include ht in
/-- B's ordinary send commutes with the state map on `InjInv` states with supported injected
values. -/
lemma sendB_step (hx : (pk, sk) ∈ support kem.keygen)
    (hy : (c, kReal) ∈ support (kem.encaps pk))
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t ⟨pk, sk, c, kReal⟩ s) :
    𝒟[(SCKAScheme.oracleSendB (injectedScheme kem hDet ecEk ecCt leak t ⟨pk, d, c, k⟩) ()).run
        (targetStateMap t d k s)] =
      𝒟[Prod.map id (targetStateMap t d k) <$>
        (SCKAScheme.oracleSendB (injectedScheme kem hDet ecEk ecCt leak t ⟨pk, sk, c, kReal⟩)
          ()).run s] := by
  rw [SCKAScheme.oracleSendB_run_eq, SCKAScheme.oracleSendB_run_eq]
  simp only [injectedScheme, targetStateMap_stB]
  rw [injectedSend_mapSecret kem ecEk ecCt t ht pk sk c kReal d k .B s.stB, Functor.map_map]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  apply evalDist_bind_congr
  intro out hout
  rcases out with _ | ⟨key?, ρ, tsnd, stB'⟩
  · rfl
  · have hcorr : (SCKAScheme.sendBUpdate s key? ρ tsnd stB').correct = true :=
      (injInv_sendB_step kem hDet ecEk ecCt leak t ⟨pk, sk, c, kReal⟩ hx hy ht s hs
        (some (tsnd, key?.map Prod.fst, ρ), SCKAScheme.sendBUpdate s key? ρ tsnd stB')
        ((SCKAScheme.mem_support_oracleSendB_run_iff _ s _).2 ⟨_, hout, rfl⟩)).1.1
    simp only [Function.comp_apply, Option.map_some, mapKey_map_fst, Prod.map, id]
    rw [sendBUpdate_map t d k s key? ρ tsnd stB' hcorr]

omit [SampleableType K] in
include hEk hCt ht in
/-- A's ideal receive commutes with the state map on `InjInv` states. -/
lemma recvA_step
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t ⟨pk, sk, c, kReal⟩ s) (n : ℕ) :
    𝒟[(oracleRecvAIdeal kem hDet ecEk ecCt leak n).run (targetStateMap t d k s)] =
      𝒟[Prod.map id (targetStateMap t d k) <$>
        (oracleRecvAIdeal kem hDet ecEk ecCt leak n).run s] := by
  have hrun : ∀ u, (oracleRecvAIdeal kem hDet ecEk ecCt leak n).run u =
      (SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
        (recvWith .A (idealRecover u.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n).run u :=
    fun u => rfl
  rw [hrun, hrun]
  have hmsg' : (targetStateMap t d k s).msgB n = s.msgB n := rfl
  rcases hmsg : s.msgB n with _ | ⟨ρ, tsnd⟩
  · rw [SCKAScheme.oracleRecvA_run_eq_of_none _ _ hmsg,
      SCKAScheme.oracleRecvA_run_eq_of_none _ _ (hmsg' ▸ hmsg)]
    simp
  · have hrecv : (schemeWithRecv kem hDet ecEk ecCt leak
        (recvWith .A (idealRecover (targetStateMap t d k s).keyB) ecEk ecCt)
        (recvB kem hDet ecEk ecCt)).recvA (targetStateMap t d k s).stA ρ =
        (recvWith .A (idealRecover s.keyB) ecEk ecCt s.stA ρ).map (mapRecvOut t d k) :=
      recvWith_idealRecover_mapSecret .A t d k s.keyB ecEk ecCt s.stA ρ
    rcases hr : recvWith .A (idealRecover s.keyB) ecEk ecCt s.stA ρ with _ | ⟨keyOpt, trcv, stA'⟩
    · rw [SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ hmsg hr,
        SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ (hmsg' ▸ hmsg) (by rw [hrecv, hr]; rfl)]
      simp only [map_pure, Prod.map, id]
      rfl
    · rw [SCKAScheme.oracleRecvA_run_eq_of_accept _ _ hmsg hr,
        SCKAScheme.oracleRecvA_run_eq_of_accept _ _ (hmsg' ▸ hmsg) (by rw [hrecv, hr]; rfl)]
      have hcorr : (SCKAScheme.recvAUpdate s tsnd keyOpt trcv stA').correct = true :=
        (injInv_recvA_step kem hDet ecEk ecCt hEk hCt leak t ⟨pk, sk, c, kReal⟩ ht n s hs
          (some (trcv, keyOpt.map Prod.fst), SCKAScheme.recvAUpdate s tsnd keyOpt trcv stA')
          ((SCKAScheme.mem_support_oracleRecvA_run_iff _ s n _).2
            (Or.inr (Or.inr ⟨ρ, tsnd, keyOpt, trcv, stA', hmsg, hr, rfl⟩)))).1.1
      simp only [map_pure, mapKey_map_fst, Prod.map, id]
      rw [recvAUpdate_map t d k s tsnd keyOpt trcv stA' hcorr]

omit [SampleableType K] in
include hEk hCt ht in
/-- B's ideal receive commutes with the state map on `InjInv` states. -/
lemma recvB_step
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t ⟨pk, sk, c, kReal⟩ s) (n : ℕ) :
    𝒟[(oracleRecvBIdeal kem hDet ecEk ecCt leak n).run (targetStateMap t d k s)] =
      𝒟[Prod.map id (targetStateMap t d k) <$>
        (oracleRecvBIdeal kem hDet ecEk ecCt leak n).run s] := by
  have hrun : ∀ u, (oracleRecvBIdeal kem hDet ecEk ecCt leak n).run u =
      (SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
        (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover u.keyA) ecEk ecCt)) n).run u :=
    fun u => rfl
  rw [hrun, hrun]
  have hmsg' : (targetStateMap t d k s).msgA n = s.msgA n := rfl
  rcases hmsg : s.msgA n with _ | ⟨ρ, tsnd⟩
  · rw [SCKAScheme.oracleRecvB_run_eq_of_none _ _ hmsg,
      SCKAScheme.oracleRecvB_run_eq_of_none _ _ (hmsg' ▸ hmsg)]
    simp
  · have hrecv : (schemeWithRecv kem hDet ecEk ecCt leak (recvA kem hDet ecEk ecCt)
        (recvWith .B (idealRecover (targetStateMap t d k s).keyA) ecEk ecCt)).recvB
          (targetStateMap t d k s).stB ρ =
        (recvWith .B (idealRecover s.keyA) ecEk ecCt s.stB ρ).map (mapRecvOut t d k) :=
      recvWith_idealRecover_mapSecret .B t d k s.keyA ecEk ecCt s.stB ρ
    rcases hr : recvWith .B (idealRecover s.keyA) ecEk ecCt s.stB ρ with _ | ⟨keyOpt, trcv, stB'⟩
    · rw [SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ hmsg hr,
        SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ (hmsg' ▸ hmsg) (by rw [hrecv, hr]; rfl)]
      simp only [map_pure, Prod.map, id]
      rfl
    · rw [SCKAScheme.oracleRecvB_run_eq_of_accept _ _ hmsg hr,
        SCKAScheme.oracleRecvB_run_eq_of_accept _ _ (hmsg' ▸ hmsg) (by rw [hrecv, hr]; rfl)]
      have hcorr : (SCKAScheme.recvBUpdate s tsnd keyOpt trcv stB').correct = true :=
        (injInv_recvB_step kem hDet ecEk ecCt hEk hCt leak t ⟨pk, sk, c, kReal⟩ ht n s hs
          (some (trcv, keyOpt.map Prod.fst), SCKAScheme.recvBUpdate s tsnd keyOpt trcv stB')
          ((SCKAScheme.mem_support_oracleRecvB_run_iff _ s n _).2
            (Or.inr (Or.inr ⟨ρ, tsnd, keyOpt, trcv, stB', hmsg, hr, rfl⟩)))).1.1
      simp only [map_pure, mapKey_map_fst, Prod.map, id]
      rw [recvBUpdate_map t d k s tsnd keyOpt trcv stB' hcorr]

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] hDet in
include ht in
/-- B's corruption commutes with the state map on the stopped answers. -/
lemma corruptB_step
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : t ∉ s.exposed) :
    𝒟[(fun z => z.1.map fun a => (a, z.2)) <$>
        ((stopOnState (SCKAScheme.oracleCorruptB (exposure .B leak).corrupt (StA PK SK C Sym) K
          (Message Sym)) (targetExposed t) ()).run).run (targetStateMap t d k s)] =
      𝒟[(fun z => z.1.map fun a => (a, targetStateMap t d k z.2)) <$>
        ((stopOnState (SCKAScheme.oracleCorruptB (exposure .B leak).corrupt (StA PK SK C Sym) K
          (Message Sym)) (targetExposed t) ()).run).run s] := by
  have hrun : ∀ u, ((stopOnState (SCKAScheme.oracleCorruptB (exposure .B leak).corrupt
      (StA PK SK C Sym) K (Message Sym)) (targetExposed t) ()).run).run u = (do
        let z ← (SCKAScheme.oracleCorruptB (exposure .B leak).corrupt (StA PK SK C Sym) K
          (Message Sym) ()).run u
        pure (if targetExposed t z.2 then none else some z.1, z.2)) := fun u => rfl
  rw [hrun, hrun, SCKAScheme.oracleCorruptB_run, SCKAScheme.oracleCorruptB_run]
  simp only [exposure_corrupt, targetStateMap_stB, vuln_mapSecret, targetStateMap_challenged,
    targetStateMap_exposed]
  by_cases hconf : vuln s.stB ∩ s.challenged ≠ ∅
  · simp [hconf, targetExposed, hs]
  · by_cases hv : t ∈ vuln s.stB
    · simp [hconf, targetExposed, hv]
    · rw [mapSecret_eq_self_of_not_mem_vuln t ht d s.stB hv]
      simp [hconf, targetExposed, hv, hs, targetStateMap,
        mapSecret_eq_self_of_not_mem_vuln t ht d s.stB hv]


omit [SampleableType K] in
include ht in
/-- A leaking send by A that generates or encapsulates for the target: on the stopped answers,
every accepted outcome stops and every rejected one keeps the state, so the answer distribution
is a function of the randomness alone. -/
lemma sendArleak_touch_evalDist
    (u : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (F : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) →
      SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hexp : t ∉ u.exposed)
    (htouch : sendGeneratesTarget .A t u.stA = true ∨ sendEncapsulatesTarget .A t u.stA = true) :
    𝒟[(fun z => z.1.map fun a => (a, F z.2)) <$>
        ((stopOnState (SCKAScheme.oracleSendArleak (exposure .A leak).rleak
          (scheme kem hDet ecEk ecCt leak)) (targetExposed t) ()).run).run u] =
      𝒟[(Option.map fun o : Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
          SendRand leak.KeygenRand leak.EncapsRand => o.2.2.2.2) <$>
        sendWith .A leak.keygenRleak leak.encapsRleak ecEk ecCt u.stA >>= fun r? =>
        pure (match r? with
          | none => some (none, F u)
          | some rand => if rleakEpochs .A u.stA rand ∩ u.challenged ≠ ∅ then some (none, F u)
              else none)] := by
  have hrun : ((stopOnState (SCKAScheme.oracleSendArleak (exposure .A leak).rleak
      (scheme kem hDet ecEk ecCt leak)) (targetExposed t) ()).run).run u = (do
        let z ← (SCKAScheme.oracleSendArleak (exposure .A leak).rleak
          (scheme kem hDet ecEk ecCt leak) ()).run u
        pure (if targetExposed t z.2 then none else some z.1, z.2)) := rfl
  rw [hrun, SCKAScheme.oracleSendArleak_run_eq]
  have hsend : (scheme kem hDet ecEk ecCt leak).sendArleak u.stA =
      sendWith .A leak.keygenRleak leak.encapsRleak ecEk ecCt u.stA := rfl
  rw [hsend]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp, exposure_rleak]
  apply evalDist_bind_congr
  intro out hout
  rcases out with _ | ⟨key?, ρ, tsnd, stA', rand⟩
  · simp [targetExposed, hexp]
  · have hmem : t ∈ rleakEpochs .A u.stA rand :=
      mem_rleakEpochs_of_target .A _ _ ecEk ecCt u.stA key? ρ tsnd stA' rand hout t ht htouch
    by_cases hconf : rleakEpochs .A u.stA rand ∩ u.challenged ≠ ∅
    · simp [hconf, targetExposed, hexp]
    · simp [hconf, targetExposed, hmem]

omit [SampleableType K] in
include ht in
/-- The version of `sendArleak_touch_evalDist` for B. -/
lemma sendBrleak_touch_evalDist
    (u : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (F : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) →
      SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hexp : t ∉ u.exposed)
    (htouch : sendGeneratesTarget .B t u.stB = true ∨ sendEncapsulatesTarget .B t u.stB = true) :
    𝒟[(fun z => z.1.map fun a => (a, F z.2)) <$>
        ((stopOnState (SCKAScheme.oracleSendBrleak (exposure .B leak).rleak
          (scheme kem hDet ecEk ecCt leak)) (targetExposed t) ()).run).run u] =
      𝒟[(Option.map fun o : Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
          SendRand leak.KeygenRand leak.EncapsRand => o.2.2.2.2) <$>
        sendWith .B leak.keygenRleak leak.encapsRleak ecEk ecCt u.stB >>= fun r? =>
        pure (match r? with
          | none => some (none, F u)
          | some rand => if rleakEpochs .B u.stB rand ∩ u.challenged ≠ ∅ then some (none, F u)
              else none)] := by
  have hrun : ((stopOnState (SCKAScheme.oracleSendBrleak (exposure .B leak).rleak
      (scheme kem hDet ecEk ecCt leak)) (targetExposed t) ()).run).run u = (do
        let z ← (SCKAScheme.oracleSendBrleak (exposure .B leak).rleak
          (scheme kem hDet ecEk ecCt leak) ()).run u
        pure (if targetExposed t z.2 then none else some z.1, z.2)) := rfl
  rw [hrun, SCKAScheme.oracleSendBrleak_run_eq]
  have hsend : (scheme kem hDet ecEk ecCt leak).sendBrleak u.stB =
      sendWith .B leak.keygenRleak leak.encapsRleak ecEk ecCt u.stB := rfl
  rw [hsend]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp, exposure_rleak]
  apply evalDist_bind_congr
  intro out hout
  rcases out with _ | ⟨key?, ρ, tsnd, stB', rand⟩
  · simp [targetExposed, hexp]
  · have hmem : t ∈ rleakEpochs .B u.stB rand :=
      mem_rleakEpochs_of_target .B _ _ ecEk ecCt u.stB key? ρ tsnd stB' rand hout t ht htouch
    by_cases hconf : rleakEpochs .B u.stB rand ∩ u.challenged ≠ ∅
    · simp [hconf, targetExposed, hexp]
    · simp [hconf, targetExposed, hmem]

omit [SampleableType K] in
include ht in
/-- A's leaking send commutes with the state map on the stopped answers: a send touching the
target stops or is rejected on both sides with equal mass, and any other send commutes with
the map outright. -/
lemma sendArleak_step
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t ⟨pk, sk, c, kReal⟩ s) (hexp : t ∉ s.exposed) :
    𝒟[(fun z => z.1.map fun a => (a, z.2)) <$>
        ((stopOnState (SCKAScheme.oracleSendArleak (exposure .A leak).rleak
          (scheme kem hDet ecEk ecCt leak)) (targetExposed t) ()).run).run
          (targetStateMap t d k s)] =
      𝒟[(fun z => z.1.map fun a => (a, targetStateMap t d k z.2)) <$>
        ((stopOnState (SCKAScheme.oracleSendArleak (exposure .A leak).rleak
          (scheme kem hDet ecEk ecCt leak)) (targetExposed t) ()).run).run s] := by
  by_cases htouch : sendGeneratesTarget .A t s.stA = true ∨
      sendEncapsulatesTarget .A t s.stA = true
  · have h1 := sendArleak_touch_evalDist kem hDet ecEk ecCt leak t ht (targetStateMap t d k s) id
      hexp htouch
    have h2 := sendArleak_touch_evalDist kem hDet ecEk ecCt leak t ht s (targetStateMap t d k)
      hexp htouch
    simp only [id_eq, targetStateMap_stA, targetStateMap_challenged, rleakEpochs_mapSecret] at h1
    rw [h1, h2, sendWith_rand_mapSecret .A t ht d k]
    rfl
  · refine evalDist_stopped_map_of_base _ _ (targetStateMap t d k) (targetExposed t)
      (targetExposed t) (fun _ => rfl) () s ?_
    have hgen : sendGeneratesTarget .A t s.stA = false := by
      cases h : sendGeneratesTarget .A t s.stA
      · rfl
      · exact absurd (Or.inl h) htouch
    have henc : sendEncapsulatesTarget .A t s.stA = false := by
      cases h : sendEncapsulatesTarget .A t s.stA
      · rfl
      · exact absurd (Or.inr h) htouch
    have hk : sendKeygenGuard .A s.stA = true → leak.keygenRleak =
        (fun x => ((x.1.1, if s.stA.res.resEpoch + 2 + Role.A.offset = (t : ℤ) then d else x.1.2),
          x.2)) <$> leak.keygenRleak := by
      intro hg
      have hc : ¬s.stA.res.resEpoch + 2 + Role.A.offset = (t : ℤ) := fun hc => by
        simp [sendGeneratesTarget, hg, hc] at hgen
      simp [hc]
    have he : sendEncapsGuard .A s.stA = true → leak.encapsRleak = fun pk' =>
        (fun y => ((y.1.1, if s.stA.res.resEpoch +
          (if sendKeygenGuard .A s.stA then 2 else 0) = (t : ℤ) then k else y.1.2), y.2)) <$>
          leak.encapsRleak pk' := by
      intro hg
      have hc : ¬s.stA.res.resEpoch + (if sendKeygenGuard .A s.stA then 2 else 0) = (t : ℤ) :=
        fun hc => by simp [sendEncapsulatesTarget, hg, hc] at henc
      funext pk'
      simp [hc]
    rw [SCKAScheme.oracleSendArleak_run_eq, SCKAScheme.oracleSendArleak_run_eq]
    have hsend : ∀ u : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym),
        (scheme kem hDet ecEk ecCt leak).sendArleak u.stA =
          sendWith .A leak.keygenRleak leak.encapsRleak ecEk ecCt u.stA := fun _ => rfl
    rw [hsend, hsend, targetStateMap_stA,
      sendWith_mapSecret .A t ht d k _ _ _ _ ecEk ecCt s.stA hk he, Functor.map_map]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp, exposure_rleak]
    apply evalDist_bind_congr
    intro out hout
    rcases out with _ | ⟨key?, ρ, tsnd, stA', rand⟩
    · rfl
    · simp only [Function.comp_apply, Option.map_some, mapSendOut, mapKey_map_fst,
        rleakEpochs_mapSecret, targetStateMap_challenged, targetStateMap_exposed]
      by_cases hconf : rleakEpochs .A s.stA rand ∩ s.challenged ≠ ∅
      · simp [hconf]
      · have hcorr : (SCKAScheme.sendAUpdate s key? ρ tsnd stA').correct = true :=
          (SCKAScheme.oracleSendArleak_preservesInv_at _ (exposure .A leak).rleak
            (sendWith_rleak_forget kem .A ecEk ecCt leak) (GameInv kem ecEk ecCt)
            (fun _ _ h => h) s hs.1 (gameInv_sendA_step kem hDet ecEk ecCt leak s hs.1)
            (some (tsnd, key?.map Prod.fst, ρ, rand),
              { SCKAScheme.sendAUpdate s key? ρ tsnd stA' with
                  exposed := s.exposed ∪ rleakEpochs .A s.stA rand })
            (by rw [SCKAScheme.oracleSendArleak_run_eq, support_map]
                exact ⟨_, hout, by simp [hconf, exposure_rleak]⟩)).1
        simp only [hconf, ↓reduceIte, Prod.map, id]
        rw [sendAUpdate_map t d k s key? ρ tsnd stA' hcorr]
        rfl

omit [SampleableType K] in
include ht in
/-- B's leaking send commutes with the state map on the stopped answers. -/
lemma sendBrleak_step
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t ⟨pk, sk, c, kReal⟩ s) (hexp : t ∉ s.exposed) :
    𝒟[(fun z => z.1.map fun a => (a, z.2)) <$>
        ((stopOnState (SCKAScheme.oracleSendBrleak (exposure .B leak).rleak
          (scheme kem hDet ecEk ecCt leak)) (targetExposed t) ()).run).run
          (targetStateMap t d k s)] =
      𝒟[(fun z => z.1.map fun a => (a, targetStateMap t d k z.2)) <$>
        ((stopOnState (SCKAScheme.oracleSendBrleak (exposure .B leak).rleak
          (scheme kem hDet ecEk ecCt leak)) (targetExposed t) ()).run).run s] := by
  by_cases htouch : sendGeneratesTarget .B t s.stB = true ∨
      sendEncapsulatesTarget .B t s.stB = true
  · have h1 := sendBrleak_touch_evalDist kem hDet ecEk ecCt leak t ht (targetStateMap t d k s) id
      hexp htouch
    have h2 := sendBrleak_touch_evalDist kem hDet ecEk ecCt leak t ht s (targetStateMap t d k)
      hexp htouch
    simp only [id_eq, targetStateMap_stB, targetStateMap_challenged, rleakEpochs_mapSecret] at h1
    rw [h1, h2, sendWith_rand_mapSecret .B t ht d k]
    rfl
  · refine evalDist_stopped_map_of_base _ _ (targetStateMap t d k) (targetExposed t)
      (targetExposed t) (fun _ => rfl) () s ?_
    have hgen : sendGeneratesTarget .B t s.stB = false := by
      cases h : sendGeneratesTarget .B t s.stB
      · rfl
      · exact absurd (Or.inl h) htouch
    have henc : sendEncapsulatesTarget .B t s.stB = false := by
      cases h : sendEncapsulatesTarget .B t s.stB
      · rfl
      · exact absurd (Or.inr h) htouch
    have hk : sendKeygenGuard .B s.stB = true → leak.keygenRleak =
        (fun x => ((x.1.1, if s.stB.res.resEpoch + 2 + Role.B.offset = (t : ℤ) then d else x.1.2),
          x.2)) <$> leak.keygenRleak := by
      intro hg
      have hc : ¬s.stB.res.resEpoch + 2 + Role.B.offset = (t : ℤ) := fun hc => by
        simp [sendGeneratesTarget, hg, hc] at hgen
      simp [hc]
    have he : sendEncapsGuard .B s.stB = true → leak.encapsRleak = fun pk' =>
        (fun y => ((y.1.1, if s.stB.res.resEpoch +
          (if sendKeygenGuard .B s.stB then 2 else 0) = (t : ℤ) then k else y.1.2), y.2)) <$>
          leak.encapsRleak pk' := by
      intro hg
      have hc : ¬s.stB.res.resEpoch + (if sendKeygenGuard .B s.stB then 2 else 0) = (t : ℤ) :=
        fun hc => by simp [sendEncapsulatesTarget, hg, hc] at henc
      funext pk'
      simp [hc]
    rw [SCKAScheme.oracleSendBrleak_run_eq, SCKAScheme.oracleSendBrleak_run_eq]
    have hsend : ∀ u : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym),
        (scheme kem hDet ecEk ecCt leak).sendBrleak u.stB =
          sendWith .B leak.keygenRleak leak.encapsRleak ecEk ecCt u.stB := fun _ => rfl
    rw [hsend, hsend, targetStateMap_stB,
      sendWith_mapSecret .B t ht d k _ _ _ _ ecEk ecCt s.stB hk he, Functor.map_map]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp, exposure_rleak]
    apply evalDist_bind_congr
    intro out hout
    rcases out with _ | ⟨key?, ρ, tsnd, stB', rand⟩
    · rfl
    · simp only [Function.comp_apply, Option.map_some, mapSendOut, mapKey_map_fst,
        rleakEpochs_mapSecret, targetStateMap_challenged, targetStateMap_exposed]
      by_cases hconf : rleakEpochs .B s.stB rand ∩ s.challenged ≠ ∅
      · simp [hconf]
      · have hcorr : (SCKAScheme.sendBUpdate s key? ρ tsnd stB').correct = true :=
          (SCKAScheme.oracleSendBrleak_preservesInv_at _ (exposure .B leak).rleak
            (sendWith_rleak_forget kem .B ecEk ecCt leak) (GameInv kem ecEk ecCt)
            (fun _ _ h => h) s hs.1 (gameInv_sendB_step kem hDet ecEk ecCt leak s hs.1)
            (some (tsnd, key?.map Prod.fst, ρ, rand),
              { SCKAScheme.sendBUpdate s key? ρ tsnd stB' with
                  exposed := s.exposed ∪ rleakEpochs .B s.stB rand })
            (by rw [SCKAScheme.oracleSendBrleak_run_eq, support_map]
                exact ⟨_, hout, by simp [hconf, exposure_rleak]⟩)).1
        simp only [hconf, ↓reduceIte, Prod.map, id]
        rw [sendBUpdate_map t d k s key? ρ tsnd stB' hcorr]
        rfl

end OracleSteps

/-! ## The simulation theorem -/

section Main

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
  (t : ℕ) (ht : 0 < t) (pk : PK) (sk dummy : SK) (c : C) (kReal kRand : K) (b : Bool)

include hEk hCt ht in
/-- Every stopped query of the reduction's oracles from the mapped state agrees, on the answers
and the mapped successors, with the stopped eager query from an `InjInv` state with the target
unexposed. -/
lemma targetStateMap_step (hx : (pk, sk) ∈ support kem.keygen)
    (hy : (c, kReal) ∈ support (kem.encaps pk)) (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t ⟨pk, sk, c, kReal⟩ s ∧ t ∉ s.exposed) :
    𝒟[(fun z => z.1.map fun a => (a, z.2)) <$>
        ((stopOnState (injectedSecurityImpl kem hDet ecEk ecCt leak t
          ⟨pk, dummy, c, if b then kRand else kReal⟩ (hybridRandom t)) (targetExposed t) q).run).run
          (targetStateMap t dummy (if b then kRand else kReal) s)] =
      𝒟[(fun z => z.1.map fun a => (a, targetStateMap t dummy (if b then kRand else kReal) z.2)) <$>
        ((stopOnState (eagerSecurityImpl kem hDet ecEk ecCt leak t ⟨pk, sk, c, kReal⟩ b kRand)
          (targetExposed t) q).run).run s] := by
  rcases q with (((((q | u) | u) | e) | u) | u)
  · rcases q with (((n | u) | u) | n) | n
    · exact evalDist_stopped_map_of_base _ _ _ _ _ (fun _ => rfl) _ s
        (congrArg (fun x => 𝒟[x]) (unif_step t dummy (if b then kRand else kReal) s n))
    · cases u
      exact evalDist_stopped_map_of_base _ _ _ _ _ (fun _ => rfl) _ s
        (sendA_step kem hDet ecEk ecCt leak t ht pk sk c kReal dummy _ hx hy s hs.1)
    · cases u
      exact evalDist_stopped_map_of_base _ _ _ _ _ (fun _ => rfl) _ s
        (sendB_step kem hDet ecEk ecCt leak t ht pk sk c kReal dummy _ hx hy s hs.1)
    · exact evalDist_stopped_map_of_base _ _ _ _ _ (fun _ => rfl) _ s
        (recvA_step kem hDet ecEk ecCt hEk hCt leak t ht pk sk c kReal dummy _ s hs.1 n)
    · exact evalDist_stopped_map_of_base _ _ _ _ _ (fun _ => rfl) _ s
        (recvB_step kem hDet ecEk ecCt hEk hCt leak t ht pk sk c kReal dummy _ s hs.1 n)
  · cases u
    exact sendArleak_step kem hDet ecEk ecCt leak t ht pk sk c kReal dummy _ s hs.1 hs.2
  · cases u
    exact sendBrleak_step kem hDet ecEk ecCt leak t ht pk sk c kReal dummy _ s hs.1 hs.2
  · exact evalDist_stopped_map_of_base _ _ _ _ _ (fun _ => rfl) _ s
      (congrArg (fun x => 𝒟[x]) (chall_step kem ecEk ecCt t pk sk dummy c kReal kRand b s hs.1 e))
  · cases u
    exact corruptA_step kem leak t ht dummy _ s hs.2
  · cases u
    exact corruptB_step kem leak t ht dummy _ s hs.2

include hEk hCt ht in
/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes;
* `0 < t`;
* `(pk, sk)` is a possible key pair and `(c, kReal)` a possible encapsulation to `pk`.

Then the eager hybrid of bit `b` with these values accepts with the probability of the
reduction's simulation on the KEM challenge `(pk, c, k_b)`, for every placeholder secret
`dummy`, where `k_b` is `kRand` if `b` is set and `kReal` otherwise. -/
theorem probOutput_stoppedEagerExp_eq_reductionRun (adv : SecurityAdversary leak Sym)
    (hx : (pk, sk) ∈ support kem.keygen) (hy : (c, kReal) ∈ support (kem.encaps pk)) :
    Pr[= true | stoppedEagerExp kem hDet ecEk ecCt leak t b pk sk c kReal kRand adv] =
      Pr[= true | stoppedRun (injectedSecurityImpl kem hDet ecEk ecCt leak t
        ⟨pk, dummy, c, if b then kRand else kReal⟩ (hybridRandom t)) (targetExposed t) adv
        (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym))] := by
  unfold stoppedEagerExp stoppedRun
  have hinit := targetStateMap_init (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym) t dummy
    (if b then kRand else kReal)
  conv_rhs => rw [← hinit]
  refine (probOutput_optionRun_eq_of_state_map_some _ _
    (targetStateMap t dummy (if b then kRand else kReal))
    (fun s => InjInv kem ecEk ecCt t ⟨pk, sk, c, kReal⟩ s ∧ t ∉ s.exposed) ?_ ?_ adv _
    ⟨injInv_init kem ecEk ecCt t ht _, by simp [initState, SCKAScheme.initGameState]⟩).symm
  · intro q s hs z hz hsome
    obtain ⟨w, hw, hzw, hexp⟩ := exists_base_of_stopped (t := t) hz hsome
    rw [hzw]
    exact ⟨eagerSecurityImpl_preservesInv_continuing kem hDet ecEk ecCt hEk hCt leak t _ hx hy ht
      b kRand q s hs.1 w hw hexp, hexp⟩
  · intro q s hs
    exact targetStateMap_step kem hDet ecEk ecCt hEk hCt leak t ht pk sk dummy c kReal kRand b hx
      hy q s hs

end Main

end oppBiKemCKA
