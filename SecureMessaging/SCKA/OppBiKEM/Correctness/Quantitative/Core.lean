/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.KEM.CorrectnessError
import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant

/-!
# Opp-BiKEM — KEM failure event and failure potential

For the quantitative correctness bound the game is run with a Boolean flag recording whether a
KEM instance has completed inconsistently. Both the flag's trigger and the potential that pays
for it are read off the game state alone.

* `kemFailureAt st peer peerKey`: the requester `st` retains a secret key for the peer's current
  responder epoch, the peer retains a ciphertext for it and has recorded a key, and
  decapsulation disagrees with that key. `kemFailure s` checks both parties.
* `pendingTerm st peer peerKey (e, sk)`: the conditional correctness error
  `keypairFailure pk sk` of a retained secret key whose epoch the peer has not encapsulated
  to yet, with `pk` the peer's decoded copy or the requester's own retained copy.
  `pendingPotential` sums it over the retained keys, and `failurePotential s` over both parties.
  On invariant states a party retains at most one key (`PartyInv.dk_shape`).
* `trackedScore (s, b)`: `1` once the flag is set, `failurePotential s` otherwise.

`decaps_of_noFailure` is the bridge to the receive step of the main invariant: when the flag is
clear, decapsulating the current epoch returns the transcript key.
-/

open OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

section Failure

variable {kem : KEMScheme ProbComp K PK SK C} (hDet : kem.DeterministicDecaps)

/-- The requester `st` holds a secret key for the peer's current responder epoch, the peer
retains the ciphertext of that epoch and has recorded its key, and decapsulation disagrees. -/
def kemFailureAt [DecidableEq K] (st peer : State PK SK C Sym) (peerKey : ℕ → Option K) : Bool :=
  match st.req.dk.lookup peer.res.resEpoch, peer.res.ct, peerKey peer.res.resEpoch.toNat with
  | some sk, some c, some k => decide (hDet.decapsDet sk c ≠ some k)
  | _, _, _ => false

/-- A KEM instance of either party has completed inconsistently. -/
def kemFailure [DecidableEq K]
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Bool :=
  kemFailureAt hDet s.stA s.stB s.keyB || kemFailureAt hDet s.stB s.stA s.keyA

theorem kemFailure_eq_false_iff [DecidableEq K]
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    kemFailure hDet s = false ↔
      kemFailureAt hDet s.stA s.stB s.keyB = false ∧
        kemFailureAt hDet s.stB s.stA s.keyA = false := by
  simp [kemFailure]

/-- `kemFailureAt` is false unless all three components are present. -/
theorem kemFailureAt_eq_false_of [DecidableEq K] {st peer : State PK SK C Sym}
    {peerKey : ℕ → Option K}
    (h : st.req.dk.lookup peer.res.resEpoch = none ∨ peer.res.ct = none ∨
      peerKey peer.res.resEpoch.toNat = none) :
    kemFailureAt hDet st peer peerKey = false := by
  unfold kemFailureAt
  rcases h with h | h | h <;> rw [h] <;> (try split) <;> simp_all

/-- When all three components are present, `kemFailureAt` decides disagreement. -/
theorem kemFailureAt_eq_decide [DecidableEq K] {st peer : State PK SK C Sym}
    {peerKey : ℕ → Option K} {sk : SK} {c : C} {k : K}
    (hsk : st.req.dk.lookup peer.res.resEpoch = some sk) (hc : peer.res.ct = some c)
    (hk : peerKey peer.res.resEpoch.toNat = some k) :
    kemFailureAt hDet st peer peerKey = decide (hDet.decapsDet sk c ≠ some k) := by
  unfold kemFailureAt
  rw [hsk, hc, hk]

/-- `kemFailureAt` depends only on the three components it reads. -/
theorem kemFailureAt_congr [DecidableEq K] {st st' peer peer' : State PK SK C Sym}
    {peerKey peerKey' : ℕ → Option K}
    (hres : peer'.res.resEpoch = peer.res.resEpoch)
    (hdk : st'.req.dk.lookup peer.res.resEpoch = st.req.dk.lookup peer.res.resEpoch)
    (hct : peer'.res.ct = peer.res.ct)
    (hkey : peerKey' peer.res.resEpoch.toNat = peerKey peer.res.resEpoch.toNat) :
    kemFailureAt hDet st' peer' peerKey' = kemFailureAt hDet st peer peerKey := by
  unfold kemFailureAt
  rw [hres, hdk, hct, hkey]

/-- Conditional correctness error of one retained secret key `(e, sk)`: `φ(pk, sk)` if the peer
has not encapsulated to `e` yet and a public key for `e` is available, `0` otherwise. -/
noncomputable def pendingTerm [DecidableEq K] (st peer : State PK SK C Sym)
    (peerKey : ℕ → Option K) (p : ℤ × SK) : ℝ≥0∞ :=
  if peerKey p.1.toNat = none then
    match peer.res.ekPeer p.1, st.req.ek with
    | some pk, _ => keypairFailure kem hDet pk p.2
    | none, some pk => keypairFailure kem hDet pk p.2
    | none, none => 0
  else 0

/-- The requester's pending failure potential: the sum of `pendingTerm` over its retained
secret keys. -/
noncomputable def pendingPotential [DecidableEq K] (st peer : State PK SK C Sym)
    (peerKey : ℕ → Option K) : ℝ≥0∞ :=
  (st.req.dk.map (pendingTerm hDet st peer peerKey)).sum

/-- The failure potential of a game state: both parties' pending potentials. -/
noncomputable def failurePotential [DecidableEq K]
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : ℝ≥0∞ :=
  pendingPotential hDet s.stA s.stB s.keyB + pendingPotential hDet s.stB s.stA s.keyA

/-- `1` once the failure flag is set, the failure potential otherwise. -/
noncomputable def trackedScore [DecidableEq K]
    (p : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) × Bool) :
    ℝ≥0∞ :=
  if p.2 then 1 else failurePotential hDet p.1

theorem trackedScore_true [DecidableEq K]
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    trackedScore hDet (s, true) = 1 := by
  simp [trackedScore]

theorem trackedScore_false [DecidableEq K]
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) :
    trackedScore hDet (s, false) = failurePotential hDet s := by
  simp [trackedScore]

theorem one_le_trackedScore_of_flag [DecidableEq K]
    (p : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym) × Bool)
    (h : p.2 = true) : 1 ≤ trackedScore hDet p := by
  simp [trackedScore, h]

theorem pendingTerm_of_key_some [DecidableEq K] {st peer : State PK SK C Sym}
    {peerKey : ℕ → Option K} {p : ℤ × SK} (h : peerKey p.1.toNat ≠ none) :
    pendingTerm hDet st peer peerKey p = 0 := by
  simp [pendingTerm, h]

theorem pendingTerm_of_ekPeer [DecidableEq K] {st peer : State PK SK C Sym}
    {peerKey : ℕ → Option K} {p : ℤ × SK} (hnone : peerKey p.1.toNat = none) {pk : PK}
    (hpk : peer.res.ekPeer p.1 = some pk) :
    pendingTerm hDet st peer peerKey p = keypairFailure kem hDet pk p.2 := by
  simp [pendingTerm, hnone, hpk]

theorem pendingTerm_of_ek [DecidableEq K] {st peer : State PK SK C Sym}
    {peerKey : ℕ → Option K} {p : ℤ × SK} (hnone : peerKey p.1.toNat = none)
    (hpeer : peer.res.ekPeer p.1 = none) {pk : PK} (hpk : st.req.ek = some pk) :
    pendingTerm hDet st peer peerKey p = keypairFailure kem hDet pk p.2 := by
  simp [pendingTerm, hnone, hpeer, hpk]

/-- `pendingTerm` depends only on the key table at the entry's epoch, the peer key there and the
own public key. -/
theorem pendingTerm_congr [DecidableEq K] {st st' peer peer' : State PK SK C Sym}
    {peerKey peerKey' : ℕ → Option K} (p : ℤ × SK)
    (hkey : peerKey' p.1.toNat = peerKey p.1.toNat)
    (hpeer : peer'.res.ekPeer p.1 = peer.res.ekPeer p.1) (hek : st'.req.ek = st.req.ek) :
    pendingTerm hDet st' peer' peerKey' p = pendingTerm hDet st peer peerKey p := by
  unfold pendingTerm
  rw [hkey, hpeer, hek]

/-- When the peer holds a decoded key for the entry's epoch, the own retained key is irrelevant. -/
theorem pendingTerm_congr_of_ekPeer [DecidableEq K] {st st' peer peer' : State PK SK C Sym}
    {peerKey peerKey' : ℕ → Option K} (p : ℤ × SK)
    (hkey : peerKey' p.1.toNat = peerKey p.1.toNat) {pk : PK}
    (hpeer : peer.res.ekPeer p.1 = some pk) (hpeer' : peer'.res.ekPeer p.1 = some pk) :
    pendingTerm hDet st' peer' peerKey' p = pendingTerm hDet st peer peerKey p := by
  unfold pendingTerm
  rw [hkey, hpeer, hpeer']

theorem pendingPotential_nil [DecidableEq K] {st peer : State PK SK C Sym}
    {peerKey : ℕ → Option K} (h : st.req.dk = []) :
    pendingPotential hDet st peer peerKey = 0 := by
  simp [pendingPotential, h]

theorem pendingPotential_singleton [DecidableEq K] {st peer : State PK SK C Sym}
    {peerKey : ℕ → Option K} {p : ℤ × SK} (h : st.req.dk = [p]) :
    pendingPotential hDet st peer peerKey = pendingTerm hDet st peer peerKey p := by
  simp [pendingPotential, h]

theorem pendingPotential_le_one [DecidableEq K] {st peer : State PK SK C Sym}
    {peerKey : ℕ → Option K}
    (hshape : st.req.dk = [] ∨ ∃ sk, st.req.dk = [(st.res.resEpoch + 1, sk)] ∨
      st.req.dk = [(st.res.resEpoch - 1, sk)]) :
    pendingPotential hDet st peer peerKey ≤ 1 := by
  rcases hshape with h | ⟨sk, h | h⟩
  · rw [pendingPotential_nil hDet h]; exact zero_le_one
  all_goals
    rw [pendingPotential_singleton hDet h]
    unfold pendingTerm
    split_ifs
    · split <;> first | exact keypairFailure_le_one kem hDet _ _ | exact zero_le_one
    · exact zero_le_one

end Failure

/-! ### Structural facts on invariant states -/

section Invariant

variable {kem : KEMScheme ProbComp K PK SK C} {hDet : kem.DeterministicDecaps}
  {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
  {T : Transcript kem} {role : Role} {st peer : State PK SK C Sym}
  {ownMsgs peerMsgs : ℕ → Option (Message Sym × ℕ)} {ownKey peerKey : ℕ → Option K}
  {tcur tcur' : ℕ}
  (h : PartyInv role ecEk ecCt T st peer ownMsgs ownKey peerKey tcur)
  (h' : PartyInv role.peer ecEk ecCt T peer st peerMsgs peerKey ownKey tcur')

include h h'

/-- The peer's key table at a retained key's epoch is the transcript key: populated exactly
once the peer has encapsulated. -/
theorem peerKey_eq_key_of_dk (e : ℤ) (sk : SK) (hmem : (e, sk) ∈ st.req.dk) :
    peerKey e.toNat = (T e).key := by
  obtain ⟨hp, hpos, -, -, -⟩ := h.dk_T e sk hmem
  have hp' : e % 2 = role.peer.resParity := by simpa using hp
  exact h'.key_res e hpos hp'

/-- A retained secret key whose epoch the peer has not encapsulated to has an available public
key: the peer's decoded copy or the own retained one, both the transcript's. -/
theorem pendingKey_available (e : ℤ) (sk : SK) (hmem : (e, sk) ∈ st.req.dk) :
    ∃ pk, (T e).keypair = some (pk, sk) ∧
      (peer.res.ekPeer e = some pk ∨ (peer.res.ekPeer e = none ∧ st.req.ek = some pk)) := by
  obtain ⟨hp, hpos, -, -, pk, hkp⟩ := h.dk_T e sk hmem
  refine ⟨pk, hkp, ?_⟩
  -- the retained key sits at the current key epoch
  have he : e = st.res.resEpoch + role.offset := by
    rcases h.dk_shape with hnil | ⟨sk', hone⟩
    · rw [hnil] at hmem; cases hmem
    · rw [hone] at hmem
      simp only [List.mem_singleton, Prod.mk.injEq] at hmem
      exact hmem.1
  cases hpeer : peer.res.ekPeer e with
  | some pk' =>
      left
      obtain ⟨sk', hkp'⟩ := h'.ekPeer_T e pk' hpeer
      rw [hkp] at hkp'
      simp only [Option.some.injEq, Prod.mk.injEq] at hkp'
      rw [hkp'.1]
  | none =>
      right
      refine ⟨rfl, ?_⟩
      cases hek : st.req.ek with
      | some pk' =>
          obtain ⟨sk', hkp'⟩ := h.ek_T pk' hek
          rw [← he, hkp] at hkp'
          simp only [Option.some.injEq, Prod.mk.injEq] at hkp'
          rw [hkp'.1]
      | none =>
          exfalso
          rcases h.ek_acked hek with hnone | hack
          · rw [← he, hkp] at hnone; cases hnone
          · rw [← he] at hack
            have hp' : e % 2 = role.reqParity := hp
            have := h.ekRec_req e hack hp'
            rw [hpeer] at this; cases this

/-- The pending term of a retained key is the conditional error of the transcript's key pair,
or `0` once the peer has encapsulated. -/
theorem pendingTerm_eq [DecidableEq K] (e : ℤ) (sk : SK) (hmem : (e, sk) ∈ st.req.dk) :
    ∃ pk, (T e).keypair = some (pk, sk) ∧
      pendingTerm hDet st peer peerKey (e, sk) =
        if (T e).enc = none then keypairFailure kem hDet pk sk else 0 := by
  obtain ⟨pk, hkp, hav⟩ := pendingKey_available h h' e sk hmem
  refine ⟨pk, hkp, ?_⟩
  have hkey := peerKey_eq_key_of_dk h h' e sk hmem
  by_cases henc : (T e).enc = none
  · have hnone : peerKey e.toNat = none := by rw [hkey, EpochTranscript.key, henc]; rfl
    rw [if_pos henc]
    rcases hav with hpk | ⟨hpeer, hek⟩
    · exact pendingTerm_of_ekPeer hDet hnone hpk
    · exact pendingTerm_of_ek hDet hnone hpeer hek
  · rw [if_neg henc]
    apply pendingTerm_of_key_some
    rw [hkey, EpochTranscript.key]
    obtain ⟨⟨c, k⟩, hck⟩ := Option.ne_none_iff_exists'.mp henc
    rw [hck]; simp

/-- When the flag is clear, decapsulating the current, not yet acknowledged epoch `q` returns
the transcript key: the three components `kemFailureAt` reads are exactly the transcript's. -/
theorem decaps_of_noFailure [DecidableEq K]
    (hfail : kemFailureAt hDet st peer peerKey = false) (q : ℤ)
    (hq : q ∉ st.ack.ctRec) (hqpar : q % 2 = role.reqParity) :
    ∀ pk sk c k, (T q).keypair = some (pk, sk) → (T q).enc = some (c, k) →
      hDet.decapsDet sk c = some k := by
  intro pk sk c k hkp henc
  have hqpos : 0 < q := h.keypair_pos q hqpar (by rw [hkp]; rfl)
  have hqparS : q % 2 = role.peer.resParity := by simpa using hqpar
  -- the peer's responder epoch is `q`: it cannot have advanced past an unacknowledged epoch
  have hres : peer.res.resEpoch = q := by
    have hle : q ≤ peer.res.resEpoch := by
      by_contra hlt
      rw [not_le] at hlt
      have := h'.enc_future q hqparS hlt
      rw [henc] at this; cases this
    rcases lt_or_eq_of_le hle with hlt | heq
    · exfalso
      have hmem := h'.ctRec_res_closed q hqpos hqparS hlt
      exact hq (h'.ctRec_res_peer q hmem hqparS)
    · exact heq.symm
  -- the peer retains the ciphertext and has recorded the key
  have hct : peer.res.ct = some c := by
    rcases h'.enc_current c k (by rw [hres]; exact henc) with hc | hin
    · exact hc
    · exfalso
      rw [hres] at hin
      exact hq (h'.ctRec_res_peer q hin hqparS)
  have hkey : peerKey peer.res.resEpoch.toNat = some k := by
    rw [hres, h'.key_res q hqpos hqparS, EpochTranscript.key, henc]; rfl
  -- the requester retains the secret key
  have hmem : (q, sk) ∈ st.req.dk := h.T_dk q pk sk hkp hqpar hq
  have hlk : st.req.dk.lookup peer.res.resEpoch = some sk := by
    rw [hres]
    cases hl : st.req.dk.lookup q with
    | none =>
        exfalso
        have := List.lookup_eq_none_iff.mp hl (q, sk) hmem
        simp at this
    | some sk' =>
        have hmem' : (q, sk') ∈ st.req.dk := by
          obtain ⟨before, after, hlist, -⟩ := List.lookup_eq_some_iff.mp hl
          simp only [hlist, List.mem_append, List.mem_cons, true_or, or_true]
        obtain ⟨-, -, -, -, pk', hkp'⟩ := h.dk_T q sk' hmem'
        rw [hkp] at hkp'
        simp only [Option.some.injEq, Prod.mk.injEq] at hkp'
        rw [hkp'.2]
  rw [kemFailureAt_eq_decide hDet hlk hct hkey] at hfail
  simpa using hfail

/-- On an invariant state the failure potential of a party is at most one. -/
theorem pendingPotential_le_one_of_inv [DecidableEq K] :
    pendingPotential hDet st peer peerKey ≤ 1 := by
  apply pendingPotential_le_one
  rcases h.dk_shape with hnil | ⟨sk, hone⟩
  · exact Or.inl hnil
  · right
    refine ⟨sk, ?_⟩
    cases role <;> simp only [Role.offset] at hone <;> [exact Or.inl hone; exact Or.inr hone]

end Invariant

end oppBiKemCKA
