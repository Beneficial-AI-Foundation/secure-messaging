/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.FSAEAD.Security.Reject

/-!
# FS-AEAD security — masking the challenge messages

`maskSt d` replaces the message of every record in `trans` whose index is a challenge in transit
by the fixed message `d`. The oracles of the confidentiality game never read these messages:
`findTrans` matches the associated data and the ciphertext, and `O-Deliver-B^lk` answers `(i, ⊥)`
for a challenge at `i`. The
confidentiality step uses masking to show that, with uniform challenge ciphertexts, the bit `b`
is independent of the guess and the history.

`maskSt` commutes with `findTrans` (`findTrans_maskSt`), `delete` (`maskSt_delete`) and `record`
(`maskSt_record_false`, `maskSt_record_true`).
-/

@[expose] public section

namespace FSAEADScheme

variable {StS StR AD M C : Type} (d : M)

/-- The record with the message `d` if its index is a challenge in transit. -/
def maskRec (c : Finset ℕ) (r : ℕ × AD × M × C) : ℕ × AD × M × C :=
  if r.1 ∈ c then (r.1, r.2.1, d, r.2.2.2) else r

/-- The game state with the message `d` in every challenge record in transit. -/
@[simps]
def maskSt (st : GameState StS StR AD M C) : GameState StS StR AD M C :=
  { st with trans := st.trans.map (maskRec d st.chall) }

/-- Masking twice is masking once. -/
theorem maskRec_maskRec (c : Finset ℕ) (r : ℕ × AD × M × C) :
    maskRec d c (maskRec d c r) = maskRec d c r := by
  unfold maskRec
  by_cases h : r.1 ∈ c <;> simp only [h, ↓reduceIte]

/-- Masking twice is masking once. -/
theorem maskSt_maskSt (st : GameState StS StR AD M C) : maskSt d (maskSt d st) = maskSt d st := by
  simp only [maskSt, List.map_map, Function.comp_def, maskRec_maskRec]

/-- Masking twice is masking once. -/
theorem maskSt_comp_maskSt :
    (maskSt d ∘ maskSt d : GameState StS StR AD M C → GameState StS StR AD M C) = maskSt d :=
  funext (maskSt_maskSt d)

/-- Masking keeps the index, the associated data and the ciphertext of a record. -/
theorem findTrans_maskSt [DecidableEq AD] [DecidableEq C] (st : GameState StS StR AD M C)
    (a : AD) (e : C) :
    (maskSt d st).findTrans a e = (st.findTrans a e).map (maskRec d st.chall) := by
  simp only [GameState.findTrans, maskSt, List.find?_map]
  congr 2
  funext r
  simp only [Function.comp_apply]
  unfold maskRec
  split_ifs <;> rfl

/-- `delete` commutes with masking. -/
theorem maskSt_delete (st : GameState StS StR AD M C) (i : ℕ) :
    maskSt d (st.delete i) = (maskSt d st).delete i := by
  have hf : ((fun x => decide (x.1 ≠ i)) ∘ maskRec d st.chall) =
      fun x : ℕ × AD × M × C => decide (x.1 ≠ i) := by
    funext r
    simp only [Function.comp_apply]
    unfold maskRec
    split_ifs <;> rfl
  simp only [maskSt, GameState.delete, List.filter_map, hf, GameState.mk.injEq, and_true,
    true_and]
  refine List.map_congr_left fun r hr => ?_
  simp only [List.mem_filter, decide_eq_true_eq] at hr
  unfold maskRec
  simp only [Finset.mem_erase, ne_eq, hr.2, not_false_eq_true, true_and]

/-- `record` of a normal message at an index that is not a challenge commutes with masking. -/
theorem maskSt_record_false (st : GameState StS StR AD M C) (a : AD) (m : M) (e : C)
    (h : st.iA ∉ st.chall) :
    maskSt d (st.record false a m e) = (maskSt d st).record false a m e := by
  unfold GameState.record
  simp only [maskSt_corrA, maskSt_comp, maskSt_iA]
  by_cases hc : (st.corrA && !st.comp st.iA) = true
  · simp only [hc, ↓reduceIte]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, maskSt, List.map_append, List.map_cons,
      List.map_nil, maskRec, h]

/-- Before a corruption of A, the masked `record` of a challenge does not depend on its message
or on the masking of the earlier records. -/
theorem maskSt_record_true (st : GameState StS StR AD M C) (a : AD) (m m' : M) (e : C)
    (hc : st.corrA = false) (h : ∀ r ∈ st.trans, r.1 ≠ st.iA) :
    maskSt d (st.record true a m e) = maskSt d ((maskSt d st).record true a m' e) := by
  unfold GameState.record
  simp only [maskSt_corrA, maskSt_comp, maskSt_iA, hc, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]
  simp only [maskSt, List.map_append, List.map_cons, List.map_nil, List.map_map,
    GameState.mk.injEq, true_and, and_true]
  congr 1
  · refine List.map_congr_left fun r hr => ?_
    have hr' := h r hr
    by_cases hm : r.1 ∈ st.chall <;>
      simp only [Function.comp_apply, maskRec, Finset.mem_insert, hr', hm, false_or, ↓reduceIte]
  · unfold maskRec
    simp only [Finset.mem_insert_self, ↓reduceIte]

end FSAEADScheme
