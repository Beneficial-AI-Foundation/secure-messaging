/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.FromAEADPRG.Security.ConfMix
public import SecureMessaging.FSAEAD.Security.Mask

/-!
# FS-AEAD from AEAD and PRG — the end term of the confidentiality step

The telescope of the confidentiality step leaves the terms `confGap(G_v, m = v)`, where `m` is the
smallest position that a corruption reveals, capped at `L`. This file shows that they vanish for
`v < L` (`confGap_confHyb_expo_eq_zero`), and that the term for `v = L` is at most half the
probability of a challenge above `L` (`abs_confGap_confHyb_expo_le`).

- Every challenge comes before the first corruption of A, and B received it before a corruption of
  B. So every challenge position is at most every revealed position (`EndInv`). On runs with
  `m = v < L`, every challenge is at a position `≤ v`.
- `G_v` and `G_v^♯` (`confHybAll`, every challenge ciphertext uniform) are identical until a
  challenge above `v`.
- In `G_v^♯` the bit `b` changes only the messages of the challenge records in `trans`, and no
  oracle reads them: `O-Deliver-B^lk` answers `(i, ⊥)` for a challenge at `i`. Replacing these
  messages by a fixed `d` (`maskSt` in `SecureMessaging.FSAEAD.Security.Mask`) turns the runs for
  `b = 0` and `b = 1` into the same runs (`map_confRun_rand_eq`). So `b` is independent of
  `(b', history)`, and the gap is zero.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal OracleComp.ProgramLogic.Relational

namespace FSAEADScheme

namespace FromAEADPRG

variable {W Kae Cae AD M : Type}

/-! ## Challenges come before the revealed positions -/

/-- The invariant of `G_conf^s` without blocked positions for the end term.
- The challenges in transit and the records in `trans` are at positions that A has sent.
- Only a corrupted A has compromised indices, and a compromised index is above every challenge.
- A reveal happens only after a corruption of A or at the end, and every challenge is at a
  position at most every revealed position.
- A challenge is in transit, or B passed its position. -/
structure EndInv (x : CState W Kae AD M Cae × ConfHist) : Prop where
  chall_le : ∀ i ∈ x.1.chall, i ≤ x.1.iA
  trans_le : ∀ r ∈ x.1.trans, r.1 ≤ x.1.iA
  comp_corrA : ∀ i, x.1.comp i = true → x.1.corrA = true
  expo : x.2.expo.isSome = true → x.1.corrA = true ∨ x.1.end_ = true
  chal_expo : ∀ p r, x.2.chal p = true → x.2.expo = some r → p ≤ r
  chal_iB : ∀ p, x.2.chal p = true → p ∈ x.1.chall ∨ p ≤ x.1.vB.iB
  comp_chal : ∀ i p, x.1.comp i = true → x.2.chal p = true → p < i

/-- Let `EndInv` hold, and let B move to a state `vB'` with `i_B ≤ i_B'` and `i ≤ i_B'`. Then
`EndInv` holds after B's update and `delete(i)`. -/
theorem EndInv.delete_vB {st : CState W Kae AD M Cae} {h : ConfHist} (hE : EndInv (st, h))
    {vB' : RecvState W Kae} {i : ℕ} (hiB : st.vB.iB ≤ vB'.iB) (hi : i ≤ vB'.iB) :
    EndInv ({ st with vB := vB' }.delete i, h) := by
  refine ⟨fun j hj => hE.chall_le j (Finset.mem_of_mem_erase hj),
    fun r hr => hE.trans_le r (List.mem_filter.mp hr).1, fun j hj => ?_, hE.expo, hE.chal_expo,
    fun p hp => ?_, fun j p hj hp => ?_⟩
  · simp only [GameState.delete, Bool.and_eq_true, bne_iff_ne, ne_eq] at hj
    exact hE.comp_corrA j hj.2
  · simp only [GameState.delete]
    rcases hE.chal_iB p hp with h' | h'
    · by_cases hpi : p = i
      · exact .inr (hpi ▸ hi)
      · exact .inl (Finset.mem_erase.mpr ⟨hpi, h'⟩)
    · exact .inr (h'.trans hiB)
  · simp only [GameState.delete, Bool.and_eq_true, bne_iff_ne, ne_eq] at hj
    exact hE.comp_chal j p hj.2 hp

/-- The initial state satisfies `EndInv`. -/
theorem endInv_init (fs : FSAEADScheme W (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (k : W) : EndInv ((GameState.init fs k : CState W Kae AD M Cae), ConfHist.init) :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h), fun h => (nomatch h),
    fun _ _ h => (nomatch h), fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

/-- `reveal` keeps `chal_expo` if every challenge is at most the revealed position. -/
theorem chal_expo_reveal {h : ConfHist} {r₀ : ℕ}
    (hce : ∀ p r, h.chal p = true → h.expo = some r → p ≤ r)
    (hr₀ : ∀ p, h.chal p = true → p ≤ r₀) :
    ∀ p r, (h.reveal r₀).chal p = true → (h.reveal r₀).expo = some r → p ≤ r := by
  intro p r hp hr
  simp only [ConfHist.reveal, Option.some.injEq] at hp hr
  subst hr
  rcases he : h.expo with _ | r'
  · simp only [Option.elim_none]
    exact hr₀ p hp
  · simp only [Option.elim_some, le_min_iff]
    exact ⟨hce p r' hp he, hr₀ p hp⟩

variable [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae]

/-- Every step of `G_conf^s` without blocked positions keeps `EndInv`. -/
theorem endInv_confStep (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (k : W) (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (s : ℕ) (b : Bool)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (x : CState W Kae AD M Cae × ConfHist) (hS : SeedInv G k x.1) (hT : TxInv x)
    (hE : EndInv x) :
    ∀ z ∈ support ((confImpl ae G len clen cm (fun _ => false) s b t).run x), EndInv z.2 := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := QueryImpl.mem_support_extendState_run _ confAux t x.1 x.2 hz
  obtain ⟨st, h⟩ := x
  have hchal_le : ∀ p, h.chal p = true → p ≤ st.iA := hT.chal_le
  have hcl : ∀ i ∈ st.chall, i ≤ st.iA := hE.chall_le
  have htl : ∀ r ∈ st.trans, r.1 ≤ st.iA := hE.trans_le
  have hcc : ∀ i, st.comp i = true → st.corrA = true := hE.comp_corrA
  have hex : h.expo.isSome = true → st.corrA = true ∨ st.end_ = true := hE.expo
  have hce : ∀ p r, h.chal p = true → h.expo = some r → p ≤ r := hE.chal_expo
  have hci : ∀ p, h.chal p = true → p ∈ st.chall ∨ p ≤ st.vB.iB := hE.chal_iB
  have hcp : ∀ i p, st.comp i = true → h.chal p = true → p < i := hE.comp_chal
  have hSB : OnChain G k st.vB := hS.vB
  rcases t with ((((((n | ⟨a, m⟩) | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, e⟩) | ⟨a, e⟩)
  · change y ∈ support ((oracleUnif _ _ _ _ _ n).run st) at hy
    rw [oracleUnif, ToVCVio.support_unifLiftStateT_run] at hy
    obtain ⟨x, rfl⟩ := hy
    exact hE
  · change y ∈ support ((oracleTransmitBlk ae G (fun _ => false) (a, m)).run st) at hy
    simp only [oracleTransmitBlk, StateT.run_bind, StateT.run_get, pure_bind,
      Bool.or_false] at hy
    split_ifs at hy with hend
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [confAux, hend, ↓reduceIte] using hE
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    simp only [Bool.not_eq_true] at hend
    have hh : confAux (fsaeadSpec.OTransmitA (a, m)) st (some (send ae G st.vA a m).2)
        ({ st with vA := (send ae G st.vA a m).1, iA := st.iA + 1 }.record false a m
          (send ae G st.vA a m).2) h =
        { h with tx := fun p => h.tx p || decide (p = st.iA + 1) } := by
      simp only [confAux, hend, Bool.false_eq_true, ↓reduceIte]
    rw [hh]
    refine ⟨fun i hi => ?_, fun r hr => ?_, fun i hi => ?_, fun h' => ?_, hce,
      fun p hp => ?_, fun i p hi hp => hcp i p (by simpa only [GameState.record_comp] using hi) hp⟩
    · rcases GameState.mem_chall_of_mem_record hi with hi | hi
      · have := hcl i hi
        simp only [GameState.record_iA]
        omega
      · simp only [GameState.record_iA, hi, le_refl]
    · simp only [GameState.record_iA]
      rcases GameState.mem_record_trans hr with hr | rfl
      · have := htl r hr
        omega
      · exact le_rfl
    · simp only [GameState.record_comp, GameState.record_corrA] at hi ⊢
      exact hcc i hi
    · simpa only [GameState.record_corrA, GameState.record_end_] using hex h'
    · simp only [GameState.record_vB]
      rcases hci p hp with h' | h'
      · exact .inl (GameState.mem_record_chall h')
      · exact .inr h'
  · change y ∈ support ((oracleChallMode ae G len clen cm b (a, m₀, m₁)).run st) at hy
    rcases mem_support_oracleChallMode ae G len clen cm b a m₀ m₁ st hy with
      rfl | ⟨hend, hcorr, -, r, -, rfl⟩
    · simpa only [confAux, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using hE
    have hexpo : h.expo = none := by
      cases he : h.expo
      · rfl
      · rcases hex (by simp only [he, Option.isSome_some]) with h' | h'
        · rw [hcorr] at h'
          exact absurd h' Bool.false_ne_true
        · rw [hend] at h'
          exact absurd h' Bool.false_ne_true
    simp only [confAux, Option.isSome_some, ↓reduceIte]
    refine ⟨fun i hi => ?_, fun r' hr => ?_, fun i hi => ?_, fun h' => ?_, fun p r' _ hr => ?_,
      fun p hp => ?_, fun i p hi _ => ?_⟩
    · rcases GameState.mem_chall_of_mem_record hi with hi | hi
      · have := hcl i hi
        simp only [GameState.record_iA]
        omega
      · simp only [GameState.record_iA, hi, le_refl]
    · simp only [GameState.record_iA]
      rcases GameState.mem_record_trans hr with hr | rfl
      · have := htl r' hr
        omega
      · exact le_rfl
    · simp only [GameState.record_comp, GameState.record_corrA] at hi ⊢
      exact hcc i hi
    · simp only [hexpo, Option.isSome_none, Bool.false_eq_true] at h'
    · simp only [hexpo, reduceCtorEq] at hr
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hp
      simp only [GameState.record_vB]
      rcases hp with hp | rfl
      · rcases hci p hp with h' | h'
        · exact .inl (GameState.mem_record_chall h')
        · exact .inr h'
      · exact .inl (GameState.iA_mem_record_chall (st := { st with vA := r.1, iA := st.iA + 1 })
          hcorr a _ _)
    · simp only [GameState.record_comp] at hi
      have := hcc i hi
      rw [hcorr] at this
      exact absurd this Bool.false_ne_true
  · change y ∈ support ((oracleCorrALow _ _ _ _ _ s ()).run st) at hy
    by_cases hend : st.end_ = true
    · simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, ↓reduceIte,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [confAux, hend, ↓reduceIte] using hE
    have hrev : ∀ c : CState W Kae AD M Cae, c.corrA = true → c.iA = st.iA →
        c.chall = st.chall → c.trans = st.trans → c.vB = st.vB →
        (∀ i, c.comp i = true → ∀ p, h.chal p = true → p < i) →
        EndInv (c, h.reveal st.iA) := fun c hc hi hch htr hvB hcomp =>
      ⟨fun i hi' => hi ▸ hcl i (hch ▸ hi'), fun r hr => hi ▸ htl r (htr ▸ hr),
        fun _ _ => hc, fun _ => .inl hc,
        chal_expo_reveal hce hchal_le,
        fun p hp => by rw [hch, hvB]; exact hci p hp, fun i p hi' hp => hcomp i hi' p hp⟩
    have hcomp : ∀ i, (if st.corrA = true then st.comp else fun i => decide (st.iA < i)) i =
        true → ∀ p, h.chal p = true → p < i := by
      intro i hi p hp
      cases hc : st.corrA
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hi
        have := hchal_le p hp
        omega
      · simp only [hc, ↓reduceIte] at hi
        exact hcp i p hi hp
    by_cases hlt : st.iA < s <;>
      (simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, hend, hlt,
         Bool.false_eq_true, ↓reduceIte, StateT.run_set, StateT.run_pure, support_pure,
         Set.mem_singleton_iff] at hy
       subst hy
       simp only [confAux, hend, Bool.false_eq_true, ↓reduceIte]
       exact hrev _ rfl rfl rfl rfl rfl hcomp)
  · change y ∈ support ((oracleCorrBLow W Kae AD M Cae s ()).run st) at hy
    by_cases hg : (st.end_ || decide (st.chall ≠ ∅)) = true
    · simp only [oracleCorrBLow, StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      simpa only [confAux, hg, ↓reduceIte] using hE
    have hg' := hg
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, not_not] at hg'
    have hfin : EndInv ({ st with end_ := true }, h.reveal (min st.iA st.vB.iB)) :=
      ⟨hcl, htl, hcc, fun _ => .inr rfl,
        chal_expo_reveal hce fun p hp => by
          have h₁ := hchal_le p hp
          rcases hci p hp with h₂ | h₂
          · rw [hg'.2] at h₂
            exact absurd h₂ (Finset.notMem_empty p)
          · exact le_min h₁ h₂,
        hci, hcp⟩
    simp only [oracleCorrBLow, StateT.run_bind, StateT.run_get, pure_bind, hg,
      Bool.false_eq_true, ↓reduceIte, StateT.run_set] at hy
    split_ifs at hy <;>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy <;>
      subst hy <;>
      simpa only [confAux, hg, Bool.false_eq_true, ↓reduceIte] using hfin
  · change y ∈ support ((oracleDeliverBLookup G (a, e)).run st) at hy
    simp only [oracleDeliverBLookup, StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hE
    rcases hf : st.findTrans a e with _ | ⟨i, a', m, e'⟩
    · simp only [hf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hE
    simp only [hf, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    change EndInv ({ st with vB := ((rcvKey G st.vB i).map Prod.fst).getD st.vB }.delete i, h)
    rcases hr : rcvKey G st.vB i with _ | ⟨vB', K⟩
    · exact hE.delete_vB le_rfl ((rcvKey_eq_none_iff G st.vB i).1 hr).2
    · obtain ⟨-, -, -, hiB, -⟩ := rcvKey_some G hSB hr
      exact hE.delete_vB (by simp only [Option.map_some, Option.getD_some]; omega)
        (by simp only [Option.map_some, Option.getD_some]; omega)
  · change y ∈ support ((oracleInjectBRej (fromAEADChain ae G) Prod.fst false (a, e)).run st)
      at hy
    simp only [oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte] at hy
    split_ifs at hy with h₁ h₂
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hE
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hE
    obtain ⟨i, e⟩ := e
    rcases hr : rcv ae G st.vB a (i, e) with _ | ⟨vB', i', m'⟩
    · simp only [fromAEADChain, hr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hE
    simp only [fromAEADChain, hr, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨hii, -, -, -, hiB, -⟩ := rcv_some ae G hSB hr
    subst i'
    exact hE.delete_vB (by omega) (by omega)

/-! ## The oracles under masking -/

section Mask

variable (d : M)

/-- The oracles of `G_conf^s` other than `O-Chall-A` commute with masking: no oracle reads the
message of a challenge record. -/
theorem confImplWith_maskSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (clen : ℕ → ℕ) (cm : ℕ → ChalMode Kae) (s : ℕ) (b : Bool)
    (t : (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae)).Domain)
    (ht : ∀ q, t ≠ fsaeadSpec.OChallA q) (st : CState W Kae AD M Cae)
    (hchall : ∀ i ∈ st.chall, i ≤ st.iA) :
    (confImplWith ae G len clen cm (fun _ => false) s b t).run (maskSt d st) =
      Prod.map id (maskSt d) <$> (confImplWith ae G len clen cm (fun _ => false) s b t).run st := by
  rcases t with ((((((n | ⟨a, m⟩) | q) | u) | u) | ⟨a, e⟩) | ⟨a, e⟩)
  · exact (oracleUnif_map _ _ (maskSt d) n st).symm
  · change (oracleTransmitBlk ae G (fun _ => false) (a, m)).run (maskSt d st) =
      Prod.map id (maskSt d) <$> (oracleTransmitBlk ae G (fun _ => false) (a, m)).run st
    simp only [oracleTransmitBlk, StateT.run_bind, StateT.run_get, pure_bind, maskSt_end_,
      maskSt_iA, maskSt_vA, Bool.or_false]
    split_ifs
    · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
        Prod.map_apply, id_eq]
      rw [maskSt_record_false d _ a m _ fun h => by have := hchall _ h; simp only at this; omega]
      rfl
  · exact absurd rfl (ht q)
  · change (oracleCorrALow _ _ _ _ _ s ()).run (maskSt d st) =
      Prod.map id (maskSt d) <$> (oracleCorrALow _ _ _ _ _ s ()).run st
    simp only [oracleCorrALow, StateT.run_bind, StateT.run_get, pure_bind, maskSt_end_,
      maskSt_iA, maskSt_corrA, maskSt_vA]
    split_ifs <;>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
        Prod.map_apply, id_eq] <;> rfl
  · change (oracleCorrBLow W Kae AD M Cae s ()).run (maskSt d st) =
      Prod.map id (maskSt d) <$> (oracleCorrBLow W Kae AD M Cae s ()).run st
    simp only [oracleCorrBLow, StateT.run_bind, StateT.run_get, pure_bind, maskSt_end_,
      maskSt_iA, maskSt_chall, maskSt_vA, maskSt_vB]
    split_ifs <;>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
        Prod.map_apply, id_eq] <;> rfl
  · change (oracleDeliverBLookup G (a, e)).run (maskSt d st) =
      Prod.map id (maskSt d) <$> (oracleDeliverBLookup G (a, e)).run st
    simp only [oracleDeliverBLookup, StateT.run_bind, StateT.run_get, pure_bind, maskSt_end_,
      findTrans_maskSt, maskSt_vB, maskSt_chall]
    split_ifs
    · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
    rcases st.findTrans a e with _ | ⟨i, a', m, e'⟩
    · simp only [Option.map_none, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
    · simp only [Option.map_some, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        map_pure, Prod.map_apply, id_eq]
      unfold maskRec
      split_ifs <;>
      · rw [maskSt_delete]
        rfl
  · change (oracleInjectBRej (fromAEADChain ae G) Prod.fst false (a, e)).run (maskSt d st) =
      Prod.map id (maskSt d) <$>
        (oracleInjectBRej (fromAEADChain ae G) Prod.fst false (a, e)).run st
    simp only [oracleInjectBRej, StateT.run_bind, StateT.run_get, pure_bind, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, maskSt_end_, findTrans_maskSt, Option.isSome_map,
      maskSt_comp, maskSt_vB]
    split_ifs
    · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
    · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
    rcases (fromAEADChain ae G).rcv st.vB a e with _ | ⟨vB', i', m'⟩
    · simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
        Prod.map_apply, id_eq]
      rw [maskSt_delete]
      rfl

omit [DecidableEq AD] [DecidableEq Cae] in
/-- With uniform challenge ciphertexts, `O-Chall-A` for the bit `b` and for the bit `0` give the
same masked steps. -/
theorem oracleChallMode_rand_maskSt (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (b : Bool) (q : AD × M × M)
    (st : CState W Kae AD M Cae) (htrans : ∀ r ∈ st.trans, r.1 ≤ st.iA) :
    Prod.map id (maskSt d) <$> (oracleChallMode ae G len clen (fun _ => .rand) b q).run st =
      Prod.map id (maskSt d) <$>
        (oracleChallMode ae G len clen (fun _ => .rand) false q).run (maskSt d st) := by
  obtain ⟨a, m₀, m₁⟩ := q
  rw [oracleChallMode_run, oracleChallMode_run]
  simp only [maskSt_end_, maskSt_corrA, maskSt_iA, maskSt_vA, Bool.false_eq_true, ↓reduceIte]
  by_cases hg : (st.end_ || st.corrA || decide (len m₀ ≠ len m₁)) = true
  · rw [ite_eq_left hg, ite_eq_left hg]
    simp only [map_pure, Prod.map_apply, id_eq, maskSt_maskSt]
  rw [ite_eq_right hg, ite_eq_right hg]
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, not_not] at hg
  have hlen : len (if b = true then m₁ else m₀) = len m₀ := by
    cases b
    · rfl
    · exact hg.2.symm
  simp only [chalSend, hlen, send_eq, Functor.map_map]
  congr 1
  funext e
  simp only [Prod.map_apply, id_eq, Prod.mk.injEq, true_and]
  exact maskSt_record_true d _ a _ _ _ hg.1.2 fun r hr => by
    have := htrans r hr
    simp only
    omega

end Mask

/-! ## The bit is independent of the run in `G_v^♯` -/

/-- The masked game with uniform challenge ciphertexts: the steps of `G_conf^s` for the bit `0`,
followed by masking. -/
def maskImpl (d : M) (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (clen : ℕ → ℕ) (s : ℕ) :
    QueryImpl (fsaeadSpec (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
      (GameM (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) :=
  fun t => StateT.mk fun st => Prod.map id (maskSt d) <$>
    (confImplWith ae G len clen (fun _ => .rand) (fun _ => false) s false t).run st

/-- With uniform challenge ciphertexts, the masked runs of `G_conf^s` do not depend on the bit. -/
theorem map_confRun_rand_maskSt (d : M) (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (G : ℕ → W → W × Kae) (len : M → ℕ) (clen : ℕ → ℕ) (s : ℕ) (b : Bool)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W) :
    Prod.map id (Prod.map (maskSt d) id) <$>
        confRun ae G len clen (fun _ => .rand) (fun _ => false) s b adversary k =
      (simulateQ ((maskImpl d ae G len clen s).extendState confAux) adversary).run
        (.init (fromAEADChain ae G) k, .init) := by
  have hinit : Prod.map (maskSt d) id
      ((GameState.init (fromAEADChain ae G) k : CState W Kae AD M Cae), ConfHist.init) =
      (GameState.init (fromAEADChain ae G) k, ConfHist.init) := rfl
  rw [confRun]
  conv_rhs => rw [← hinit]
  refine map_run_simulateQ_eq_of_query_map_eq_inv' _ _
    (fun x => SeedInv G k x.1 ∧ TxInv x ∧ EndInv x) (Prod.map (maskSt d) id) ?_ ?_ adversary _
    ⟨⟨rfl, rfl, ⟨rfl, fun _ _ h => (nomatch h), fun _ _ => rfl⟩⟩, txInv_init _ k,
      endInv_init _ k⟩
  · intro t x hx y hy
    obtain ⟨z, hz, rfl⟩ := QueryImpl.mem_support_extendState_run _ confAux t x.1 x.2 hy
    exact ⟨seedInv_confStep ae G k len clen _ _ s b t x.1 hx.1 z hz,
      txInv_confStep ae G len clen _ s b t x hx.2.1 _ hy,
      endInv_confStep ae G k len clen _ s b t x hx.1 hx.2.1 hx.2.2 _ hy⟩
  · intro t x hx
    obtain ⟨st, h⟩ := x
    refine QueryImpl.extendState_run_map_eq _ _ confAux confAux (maskSt d) t st h ?_
      fun u s' => ?_
    · change Prod.map id (maskSt d) <$>
          (confImplWith ae G len clen (fun _ => .rand) (fun _ => false) s b t).run st =
        Prod.map id (maskSt d) <$>
          (confImplWith ae G len clen (fun _ => .rand) (fun _ => false) s false t).run
            (maskSt d st)
      by_cases ht : ∃ q, t = fsaeadSpec.OChallA q
      · obtain ⟨q, rfl⟩ := ht
        exact oracleChallMode_rand_maskSt d ae G len clen b q st hx.2.2.trans_le
      · push Not at ht
        rw [confImplWith_maskSt d ae G len clen _ s false t ht st hx.2.2.chall_le,
          Functor.map_map]
        simp only [Prod.map_map, Function.comp_def, maskSt_maskSt]
        rcases t with ((((((n | q) | ⟨a, m₀, m₁⟩) | u) | u) | q) | q)
        all_goals first | rfl | exact absurd rfl (ht (a, m₀, m₁))
    · rcases t with ((((((n | q) | q) | u) | u) | q) | q) <;> rfl

/-- With uniform challenge ciphertexts, the guess and the history of `G_conf^s` do not depend on the
bit. -/
theorem map_confRun_rand_eq (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (G : ℕ → W → W × Kae)
    (len : M → ℕ) (clen : ℕ → ℕ) (s : ℕ) (b : Bool)
    (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)) (k : W) :
    (fun z => (z.1, z.2.2)) <$>
        confRun ae G len clen (fun _ => .rand) (fun _ => false) s b adversary k =
      (fun z => (z.1, z.2.2)) <$>
        confRun ae G len clen (fun _ => .rand) (fun _ => false) s false adversary k := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨d⟩⟩
  · have hch : oracleChallMode ae G len clen (fun _ => .rand) b =
        oracleChallMode ae G len clen (fun _ => .rand) false := funext fun q => isEmptyElim q.2.1
    simp only [confRun, confImpl, confImplWith, hch]
  · have h (b : Bool) : (fun z => (z.1, z.2.2)) <$>
        confRun ae G len clen (fun _ => .rand) (fun _ => false) s b adversary k =
        (fun z => (z.1, z.2.2)) <$> (simulateQ ((maskImpl d ae G len clen s).extendState confAux)
          adversary).run (.init (fromAEADChain ae G) k, .init) := by
      rw [← map_confRun_rand_maskSt d ae G len clen s b adversary k, Functor.map_map]
      rfl
    rw [h, h]

/-- **The hybrid `G_v^♯`.** `G_v^s` with uniform ciphertexts for every challenge. -/
def confHybAll [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (s v : ℕ) : ProbComp (Bool × Bool × ConfHist) := do
  let U ← sampleTab v
  let k ← $ᵗ W
  let b ← $ᵗ Bool
  let z ← confRun ae (hybGen prg U) len clen (fun _ => .rand) (fun _ => false) s b adversary k
  pure (b, z.1, z.2.2)

/-- **The bit is hidden in `G_v^♯`.** For every event `E` of the history, `G_v^♯` has gap zero:
`Pr[b = b' ∧ E] = Pr[E] / 2`. -/
theorem confGap_confHybAll_eq_zero [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (s v : ℕ) (E : ConfHist → Prop) :
    confGap (confHybAll ae prg len clen adversary s v) E = 0 := by
  set mx := confHybAll ae prg len clen adversary s v
  have hsym : Pr{let r ← mx}[r.1 = r.2.1 ∧ E r.2.2] = Pr{let r ← mx}[¬r.1 = r.2.1 ∧ E r.2.2] := by
    refine prEvent_bind_congr _ _ _ _ _ fun U => prEvent_bind_congr _ _ _ _ _ fun k => ?_
    have hR (b : Bool) : (do
        let z ← confRun ae (hybGen prg U) len clen (fun _ => .rand) (fun _ => false) s b
          adversary k
        pure (b, z.1, z.2.2) : ProbComp (Bool × Bool × ConfHist)) =
        (fun w => (b, w)) <$> ((fun z => (z.1, z.2.2)) <$>
          confRun ae (hybGen prg U) len clen (fun _ => .rand) (fun _ => false) s false adversary
            k) := by
      rw [← map_confRun_rand_eq ae _ len clen s b adversary k, Functor.map_map, bind_pure_comp]
    have hcoin (P : Bool × Bool × ConfHist → Prop) (Y : ProbComp (Bool × ConfHist)) :
        Pr{let r ← (do let b ← ($ᵗ Bool : ProbComp Bool); (fun w => (b, w)) <$> Y)}[P r] =
          2⁻¹ * Pr{let w ← Y}[P (true, w)] + 2⁻¹ * Pr{let w ← Y}[P (false, w)] := by
      rw [prEvent_bind_eq_lintegral_of_discrete, MeasureTheory.lintegral_fintype,
        Fintype.sum_bool]
      simp only [SampleableType.evalDist_uniformSample_singleton, Fintype.card_bool, prEvent_map,
        Nat.cast_ofNat]
      ring
    simp only [hR]
    rw [hcoin, hcoin, add_comm]
    congr 2 <;> refine prEvent_congr _ _ _ fun w => ?_ <;> rcases w with ⟨b', h⟩ <;> cases b' <;>
      simp only [Bool.true_eq_false, Bool.false_eq_true, false_and, true_and,
        not_false_eq_true, not_true_eq_false]
  have hsum : Pr{let r ← mx}[E r.2.2] =
      Pr{let r ← mx}[r.1 = r.2.1 ∧ E r.2.2] + Pr{let r ← mx}[¬r.1 = r.2.1 ∧ E r.2.2] := by
    rw [prEvent_eq_prEvent_and_add_prEvent_and_not mx _ fun r => r.1 = r.2.1]
    congr 1 <;> exact prEvent_congr mx _ _ fun r => and_comm
  rw [confGap, hsum, ← hsym, ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)]
  ring

/-- A challenge at a position above `v`. -/
def ChalAbove (v : ℕ) (h : ConfHist) : Prop := ∃ p, v < p ∧ h.chal p = true

/-- `G_v` and `G_v^♯` give every event the same probability on runs without a challenge above
`v`. -/
theorem prEvent_confHyb_and_not_above_eq [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (s v : ℕ) (X : Bool × Bool × ConfHist → Prop) :
    Pr{let r ← confHyb ae prg len clen adversary s v v}[X r ∧ ¬ChalAbove v r.2.2] =
      Pr{let r ← confHybAll ae prg len clen adversary s v}[X r ∧ ¬ChalAbove v r.2.2] := by
  refine prEvent_bind_congr _ _ _ _ _ fun U => prEvent_bind_congr _ _ _ _ _ fun k =>
    prEvent_bind_congr _ _ _ _ _ fun b => ?_
  simp only [bind_pure_comp, prEvent_map]
  have hmono (cm : ℕ → ChalMode Kae) (t) (x : CState W Kae AD M Cae × ConfHist)
      (hb : ChalAbove v x.2) :
      ∀ z ∈ support ((confImpl ae (hybGen prg U) len clen cm (fun _ => false) s b t).run x),
        ChalAbove v z.2.2 := fun z hz => by
    obtain ⟨y, -, rfl⟩ := QueryImpl.mem_support_extendState_run _ confAux t x.1 x.2 hz
    obtain ⟨p, hp, hc⟩ := hb
    exact ⟨p, hp, chal_confAux t x.1 y.1 y.2 hc⟩
  exact prEvent_simulateQ_run_and_not_bad_eq _ _
    (fun x : CState W Kae AD M Cae × ConfHist => ChalAbove v x.2)
    (fun t x _ q => prEvent_confImpl_and_not_chal_eq ae _ len clen _ _ _ s b (v < ·)
      (fun p hp => by simp only [randUpTo, not_lt.mp hp, ↓reduceIte]) t x q)
    (hmono _) (hmono _) adversary _ _

/-- In `G_v`, every challenge position is at most every revealed position. -/
theorem chal_le_of_expo [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (s v u : ℕ) :
    ∀ r ∈ support (confHyb ae prg len clen adversary s v u), ∀ p q, r.2.2.chal p = true →
      r.2.2.expo = some q → p ≤ q := by
  intro r hr
  simp only [confHyb, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨U, -, k, -, b, -, z, hz, rfl⟩ := hr
  have hI := simulateQ_run_preserves_inv_of_query _
    (fun x => SeedInv (hybGen prg U) k x.1 ∧ TxInv x ∧ EndInv x)
    (fun t x hx y hy => by
      obtain ⟨w, hw, rfl⟩ := QueryImpl.mem_support_extendState_run _ confAux t x.1 x.2 hy
      exact ⟨seedInv_confStep ae _ k len clen _ _ s b t x.1 hx.1 w hw,
        txInv_confStep ae _ len clen _ s b t x hx.2.1 _ hy,
        endInv_confStep ae _ k len clen _ s b t x hx.1 hx.2.1 hx.2.2 _ hy⟩)
    adversary (GameState.init (fromAEADChain ae (hybGen prg U)) k, ConfHist.init)
    ⟨⟨rfl, rfl, ⟨rfl, fun _ _ h => (nomatch h), fun _ _ => rfl⟩⟩, txInv_init _ k,
      endInv_init _ k⟩ z hz
  exact hI.2.2.chal_expo

/-! ## The end term -/

omit [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae] in
/-- The gap splits along an event `F` of the history. -/
theorem confGap_split (mx : ProbComp (Bool × Bool × ConfHist)) (E F : ConfHist → Prop) :
    confGap mx E = confGap mx (fun h => E h ∧ F h) + confGap mx (fun h => E h ∧ ¬F h) := by
  have h₁ := prEvent_eq_prEvent_and_add_prEvent_and_not mx (fun r => r.1 = r.2.1 ∧ E r.2.2)
    fun r => F r.2.2
  have h₂ := prEvent_eq_prEvent_and_add_prEvent_and_not mx (fun r => E r.2.2) fun r => F r.2.2
  simp only [and_assoc] at h₁
  rw [confGap, confGap, confGap, h₁, h₂, ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _),
    ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)]
  ring

omit [DecidableEq AD] [DecidableEq Cae] [LenSampleable Cae] in
/-- The gap of an event is at most half its probability. -/
theorem abs_confGap_le (mx : ProbComp (Bool × Bool × ConfHist)) (E : ConfHist → Prop) :
    |confGap mx E| ≤ (Pr{let r ← mx}[E r.2.2]).toReal / 2 := by
  have h₀ : 0 ≤ (Pr{let r ← mx}[r.1 = r.2.1 ∧ E r.2.2]).toReal := ENNReal.toReal_nonneg
  have h₁ : (Pr{let r ← mx}[r.1 = r.2.1 ∧ E r.2.2]).toReal ≤ (Pr{let r ← mx}[E r.2.2]).toReal :=
    ENNReal.toReal_mono (prEvent_ne_top _) (prEvent_mono _ _ _ fun r h => h.2)
  rw [confGap, abs_le]
  constructor <;> linarith

/-- The exposure index `m`: the smallest position that a corruption revealed, capped at `L`. -/
def expoIdx (L : ℕ) (h : ConfHist) : ℕ := min L (h.expo.getD L)

/-- `G_v` has gap zero on runs without a challenge above `v`. -/
theorem confGap_confHyb_not_above_eq_zero [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (s v : ℕ) (E : ConfHist → Prop) :
    confGap (confHyb ae prg len clen adversary s v v) (fun h => E h ∧ ¬ChalAbove v h) = 0 := by
  have h (mx : ProbComp (Bool × Bool × ConfHist)) (X : Bool × Bool × ConfHist → Prop) :
      Pr{let r ← mx}[X r ∧ E r.2.2 ∧ ¬ChalAbove v r.2.2] =
        Pr{let r ← mx}[(X r ∧ E r.2.2) ∧ ¬ChalAbove v r.2.2] :=
    prEvent_congr mx _ _ fun r => and_assoc.symm
  have h' (mx : ProbComp (Bool × Bool × ConfHist)) :
      Pr{let r ← mx}[E r.2.2 ∧ ¬ChalAbove v r.2.2] =
        Pr{let r ← mx}[(True ∧ E r.2.2) ∧ ¬ChalAbove v r.2.2] :=
    prEvent_congr mx _ _ fun r => by simp only [true_and]
  rw [← confGap_confHybAll_eq_zero ae prg len clen adversary s v (fun h => E h ∧ ¬ChalAbove v h),
    confGap, confGap, h, h, h', h',
    prEvent_confHyb_and_not_above_eq ae prg len clen adversary s v fun r => r.1 = r.2.1 ∧ E r.2.2,
    prEvent_confHyb_and_not_above_eq ae prg len clen adversary s v fun r => True ∧ E r.2.2]

/-- **The end term below `L`.** For `v < L`, `G_v` has gap zero on runs with `m = v`: such a run
reveals position `v`, so every challenge is at a position `≤ v`. -/
theorem confGap_confHyb_expo_eq_zero [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    {L v : ℕ} (hv : v < L) :
    confGap (confHyb ae prg len clen adversary 0 v v) (fun h => expoIdx L h = v) = 0 := by
  rw [confGap_split _ _ fun h => ¬ChalAbove v h, confGap_confHyb_not_above_eq_zero, zero_add]
  have h0 : Pr{let r ← confHyb ae prg len clen adversary 0 v v}[
      expoIdx L r.2.2 = v ∧ ¬¬ChalAbove v r.2.2] = 0 := by
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun r hr ⟨he, ha⟩ => ?_
    obtain ⟨p, hp, hc⟩ := not_not.mp ha
    have hexpo : r.2.2.expo = some v := by
      unfold expoIdx at he
      rcases hx : r.2.2.expo with _ | q
      · simp only [hx, Option.getD_none, min_self] at he
        omega
      · simp only [hx, Option.getD_some] at he
        rw [Option.some.injEq]
        omega
    have := chal_le_of_expo ae prg len clen adversary 0 v v r hr p v hc hexpo
    omega
  have h0' : Pr{let r ← confHyb ae prg len clen adversary 0 v v}[
      r.1 = r.2.1 ∧ expoIdx L r.2.2 = v ∧ ¬¬ChalAbove v r.2.2] = 0 :=
    le_antisymm ((prEvent_mono _ _ _ fun r h => h.2).trans (le_of_eq h0)) zero_le
  rw [confGap, h0, h0', ENNReal.toReal_zero]
  ring

/-- **The end term at `L`.** `G_L` has gap at most half the probability of a challenge above `L` on
runs with `m = L`. -/
theorem abs_confGap_confHyb_expo_le [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) (adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae))
    (L : ℕ) :
    |confGap (confHyb ae prg len clen adversary 0 L L) (fun h => expoIdx L h = L)| ≤
      (Pr{let r ← confHyb ae prg len clen adversary 0 L L}[ChalAbove L r.2.2]).toReal / 2 := by
  rw [confGap_split _ _ fun h => ¬ChalAbove L h, confGap_confHyb_not_above_eq_zero, zero_add]
  refine (abs_confGap_le _ _).trans ?_
  gcongr
  · exact prEvent_ne_top _
  · exact prEvent_mono _ _ _ fun r h => not_not.mp h.2

/-! ## No challenge above the number of sends -/

/-- Let the adversary make at most `q ≤ L` calls of `O-Transmit-A` and `O-Chall-A`. Then no
hybrid has a challenge above `L`. -/
theorem prEvent_confHyb_chalAbove_eq_zero [SampleableType W] [SampleableType Kae]
    (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) (len : M → ℕ)
    (clen : ℕ → ℕ) {adversary : FSAEADAdversary (SendState W) (RecvState W Kae) AD M (ℕ × Cae)}
    {q L : ℕ} (hq : SendQueryBound adversary q) (hqL : q ≤ L) (s v u : ℕ) :
    Pr{let r ← confHyb ae prg len clen adversary s v u}[ChalAbove L r.2.2] = 0 := by
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun r hr ⟨p, hLp, hp⟩ => ?_
  simp only [confHyb, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨U, -, k, -, b, -, z, hz, rfl⟩ := hr
  have hT := simulateQ_run_preserves_inv_of_query _ TxInv
    (fun t x hx y hy => txInv_confStep ae _ len clen _ s b t x hx y hy)
    adversary _ (txInv_init _ k) z hz
  have hstep (t) (x : CState W Kae AD M Cae × ConfHist) :
      ∀ y ∈ support ((confImpl ae (hybGen prg U) len clen (randUpTo u) (fun _ => false) s b
        t).run x), y.2.1.iA = x.1.iA ∨ (fsaeadSpec.isSendQuery t = true ∧ y.2.1.iA = x.1.iA + 1) :=
    fun y hy => by
      obtain ⟨w, hw, rfl⟩ := QueryImpl.mem_support_extendState_run _ confAux t x.1 x.2 hy
      exact iA_confStep ae _ len clen _ _ s b t x.1 w hw
  have hi := IsQueryBoundP.cost_le_of_mem_support_run_simulateQ
    (fun x : CState W Kae AD M Cae × ConfHist => x.1.iA)
    (fun t _ x y hy => by rcases hstep t x y hy with h | h <;> omega)
    (fun t ht x y hy => (hstep t x y hy).elim le_of_eq fun h => absurd h.1 ht) hq _ z hz
  have := hT.chal_le p hp
  simp only [GameState.init, zero_add] at hi
  omega

end FromAEADPRG






end FSAEADScheme
