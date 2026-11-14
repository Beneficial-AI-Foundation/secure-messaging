/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Invariant.Receive
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import ToVCVio.OracleComp.SimSemantics.StateT.IdenticalUntilBadInvariant
public import ToVCVio.OracleComp.SimSemantics.StateT.QueryImplAdd

/-!
# The trace invariant and the real trace game

This module compares three games for a scheduled authenticator `S` and a challenge bit `b`: the
SCKA security game `fixed S irl A b` of `scheme P S irl` under E⁺; the real trace game, which is
`run` with the empty table, the real rules, the challenge modes `Modes.fixedBit b` and the real
receive; and the repaired trace game, the same run with the repaired receive.

In the repaired game, the trace invariant `TraceInv` states that the game state agrees with the
records, whether or not the bad flag is set. In the real game, when the bad flag is false, it
states two facts: the game state agrees with the records, and decapsulating every recorded
encapsulation with its recorded key pair gives the epoch key derived from the recorded KEM key.
When the bad flag is set in the real game, `TraceInv` states neither fact. In both games, whether
or not the bad flag is set, it also states that the exposed and challenged epochs are disjoint.

`Parameters` contains the four stream decoders but no proof that they are sound. Several results
below take their soundness as four hypotheses: `hHdrSound : P.decHdr.Sound P.ecpHdr`,
`hEkSound : P.decEk.Sound P.ecpEk`, `hCt1Sound : P.decCt1.Sound P.ecpCt1` and
`hCt2Sound : P.decCt2.Sound P.ecpCt2`. They state that the header, encapsulation-key, `ct₁` and
`ct₂` decoders are sound for their erasure codes: a decoder that received only chunks of a payload
`p`, at least one, decodes to `none` or to `some p` (`StreamDecoder.Sound`). A decoder that is not
sound may output a payload other than the one sent, and the correctness error of the KEM does not
cover that case.

In both trace games, the uniform-randomness, send, challenge and corruption oracles keep
`TraceInv` with no hypothesis on the stream decoders. Under the four soundness hypotheses, a
receive keeps `TraceInv` in the repaired game (`traceReceive_preservesInv`) and in the real game
(`traceReceive_real_preservesInv`). Hence, under these hypotheses, every query of the real trace
game keeps `TraceInv` of the real game (`traceImpl_real_preservesInv`).

Under the four soundness hypotheses, at a state that satisfies `TraceInv` of the real game and has
the bad flag false, the real and the repaired trace games answer every query in the same way
(`traceImpl_real_eq_repaired`). No query clears the bad flag (`traceImpl_bad_mono`). Forgetting
the records and the bad flag of the real trace game gives the security game (`run_erase`); this
needs no hypothesis on the stream decoders.

Both games first draw a uniform initial key `ik`. The trace game records the initial
authenticator value `S.F 1 S.initRoot ik`; the security game starts both parties from it. The
comparison is proved for each initial key and then averaged over the draw. Under the four
soundness hypotheses, `fixed_repaired_gap_le` bounds the distance between the security game and
the repaired game by the probability that the real trace game sets the bad flag.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal
open ErasureCodePayload.Streaming

namespace MLKEMBraid.Auth

open Braid

variable {P : Parameters ProbComp} {Root MacKey : Type}

/-- The modes of the security game with the challenge bit `b`: every epoch key and authenticator
value is chosen the real way, and an eligible challenge is answered with the recorded key if
`b = false` and with a uniform key if `b = true`. -/
def Modes.fixedBit (b : Bool) : Modes :=
  { Modes.real with chal := fun _ => if b then .uniform else .real }

/-- The invariant of a trace game for the scheduled authenticator `S`, the table `tbl`, the modes
`modes` and the initial key `ik`. In the repaired game (`repair = true`), it states that the game
state agrees with the records (`RepairInv`), whether or not the bad flag is set. In the real game
(`repair = false`), when the bad flag is false, it states two facts: the game state agrees with
the records, and decapsulating every recorded encapsulation with its recorded key pair gives the
epoch key derived from the recorded KEM key (`Braid.NoAuth.DecapsGood`). When the bad flag is set
in the real game, it states neither fact. In both games, whether or not the bad flag is set, it
also states that the exposed and challenged epochs are disjoint. -/
def TraceInv [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    (S : ScheduledAuthenticator P Root MacKey) (tbl : Installed P irl (Root × MacKey))
    (modes : Modes) (ik : P.EpochKey) (repair : Bool) (s : TraceState P (Root × MacKey)) : Prop :=
  ((repair = true ∨ s.bad = false) →
    RepairInv S tbl modes ik s.transcript s.game ∧
      (repair = false → NoAuth.DecapsGood (EpochRecord.toTranscript ∘ s.transcript))) ∧
  s.game.exposed ∩ s.game.challenged = ∅

/-- One query step from `s` to `z` keeps `TraceInv` if it keeps the bad flag set, keeps the
agreement with the records and the decapsulation property before the bad event, and keeps the
exposed and challenged epochs disjoint. -/
theorem TraceInv.step [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {tbl : Installed P irl (Root × MacKey)}
    {modes : Modes} {ik : P.EpochKey} {repair : Bool} {s z : TraceState P (Root × MacKey)}
    (hs : TraceInv S tbl modes ik repair s) (hbad : s.bad = true → z.bad = true)
    (hstep : RepairInv S tbl modes ik s.transcript s.game →
      (repair = false → NoAuth.DecapsGood (EpochRecord.toTranscript ∘ s.transcript)) →
      RepairInv S tbl modes ik z.transcript z.game ∧
        (NoAuth.DecapsGood (EpochRecord.toTranscript ∘ s.transcript) → z.bad = false →
          NoAuth.DecapsGood (EpochRecord.toTranscript ∘ z.transcript)))
    (hdisj : z.game.exposed ∩ z.game.challenged = ∅) :
    TraceInv S tbl modes ik repair z := by
  refine ⟨fun hz => ?_, hdisj⟩
  have hs' : repair = true ∨ s.bad = false := by
    rcases hz with h | h
    · exact Or.inl h
    · right
      cases hb : s.bad
      · rfl
      · have := hbad hb
        rw [h] at this
        cases this
  obtain ⟨hR, hG⟩ := hs.1 hs'
  obtain ⟨hR', hG'⟩ := hstep hR hG
  refine ⟨hR', fun hrep => hG' (hG hrep) ?_⟩
  rcases hz with h | h
  · rw [h] at hrep
    cases hrep
  · exact h

/-- Let `a0` be the initial authenticator value, and let the table install no other initial value.
Then the initial trace state satisfies `TraceInv` for every initial key `ik`, in either game. -/
theorem traceInv_init [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    (S : ScheduledAuthenticator P Root MacKey) (tbl : Installed P irl (Root × MacKey))
    (modes : Modes) (ik : P.EpochKey) (repair : Bool) (a0 : Root × MacKey)
    (h0 : ∀ p, tbl.pair 0 = some p → a0 = p) :
    TraceInv S tbl modes ik repair (initTrace P a0) := by
  have hc := Braid.transcriptConsistent_initGameState
    (P := P) (recorded S (initTrace P a0).transcript) ik
  refine ⟨fun _ => ⟨⟨hc.correct, hc.control, hc.statePair, rfl, rfl, ?_, ?_, hc.localA, hc.localB,
    hc.messages, ?_, by simp [initTrace], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro e pk sk h
    simp [initTrace] at h
  · intro e es ct1 k h
    simp [initTrace] at h
  · intro party e
    cases party <;> simp [initTrace, SCKAScheme.initGameState]
  · intro e
    simp [initTrace]
  · intro e he
    simp [initTrace, Nat.pos_iff_ne_zero.mp he]
  · intro e x h
    simp [initTrace] at h
  · intro e es ct1 k h
    simp [initTrace] at h
  · intro e p _ h
    simp [initTrace] at h
  · intro e x _ h
    simp [initTrace] at h
  · intro p hp
    simp [initTrace, h0 p hp]
  · intro _ e pk sk es ct1 k _ h
    simp [initTrace, EpochRecord.toTranscript] at h
  · simp [initTrace, SCKAScheme.initGameState]

/-- The uniform-randomness oracle keeps `TraceInv`. -/
theorem traceUnif_preservesInv [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    (S : ScheduledAuthenticator P Root MacKey) (tbl : Installed P irl (Root × MacKey))
    (modes : Modes) (ik : P.EpochKey) (repair : Bool) :
    QueryImpl.PreservesInv (traceUnif P (Root × MacKey)) (TraceInv S tbl modes ik repair) := by
  intro t s hs z hz
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame
    (c := SCKAScheme.oracleUnif (State P (Root × MacKey)) (State P (Root × MacKey)) P.EpochKey
      (Message P.Sym) t) hz
  have hw' : w.2 = s.game :=
    SCKAScheme.oracleUnif_preservesInv (fun g => g = s.game) t s.game rfl w hw
  change TraceInv S tbl modes ik repair { s with game := w.2 }
  rw [hw']
  exact hs

/-- A corruption of A (`party = true`) or of B (`party = false`) keeps `TraceInv`: a refused
corruption changes nothing, and an accepted one adds exposed epochs that are not challenged. -/
theorem traceCorrupt_preservesInv [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    (S : ScheduledAuthenticator P Root MacKey) (tbl : Installed P irl (Root × MacKey))
    (modes : Modes) (ik : P.EpochKey) (repair party : Bool) :
    QueryImpl.PreservesInv
      (if party then traceCorruptA (AS := Root × MacKey) (MacKey := MacKey) irl some
        else traceCorruptB (AS := Root × MacKey) (MacKey := MacKey) irl some)
      (TraceInv S tbl modes ik repair) := by
  intro t s hs z hz
  have core : ∀ (g : GameState P (Root × MacKey)) (V : Finset ℕ),
      (g = s.game ∨
        (V ∩ s.game.challenged = ∅ ∧ g = { s.game with exposed := s.game.exposed ∪ V })) →
      TraceInv S tbl modes ik repair { s with game := g } := by
    rintro g V (hg | ⟨hV, hg⟩)
    · rw [hg]
      exact hs
    · rw [hg]
      refine TraceInv.step hs (fun hb => hb) (fun hR _ => ⟨hR.setFlags _ _, fun hg _ => hg⟩) ?_
      change (s.game.exposed ∪ V) ∩ s.game.challenged = ∅
      rw [Finset.union_inter_distrib_right, Finset.union_eq_empty]
      exact ⟨hs.2, hV⟩
  cases party
  · rw [ite_eq_right Bool.false_ne_true, (traceCorrupt_eq_oracleCorrupt irl).2] at hz
    obtain ⟨w, hw, rfl⟩ := mem_support_liftGame hz
    cases t
    exact core _ _ (mem_support_oracleCorruptB hw)
  · rw [ite_eq_left rfl, (traceCorrupt_eq_oracleCorrupt irl).1] at hz
    obtain ⟨w, hw, rfl⟩ := mem_support_liftGame hz
    cases t
    exact core _ _ (mem_support_oracleCorruptA hw)

/-- A challenge keeps `TraceInv`, whatever table `tbl'` and modes `modes'` answer it: it only adds
an unexposed epoch to the challenged epochs. -/
theorem traceChallenge_preservesInv [DecidableEq P.Mac] [SampleableType P.K]
    [SampleableType P.EpochKey] {irl : P.kem.IncrementalRandLeak P.inc}
    (S : ScheduledAuthenticator P Root MacKey) (tbl : Installed P irl (Root × MacKey))
    (modes : Modes) (ik : P.EpochKey) (repair : Bool)
    (tbl' : Installed P irl (Root × MacKey)) (modes' : Modes) :
    QueryImpl.PreservesInv (traceChallenge tbl' modes') (TraceInv S tbl modes ik repair) := by
  intro e s hs z hz
  rcases mem_support_traceChallenge hz with hz | ⟨hex, hz⟩
  · rw [hz]
    exact hs
  · rw [hz]
    refine TraceInv.step hs (fun hb => hb) (fun hR _ => ⟨hR.setFlags _ _, fun hg _ => hg⟩) ?_
    change s.game.exposed ∩ insert e s.game.challenged = ∅
    rw [Finset.inter_insert_of_notMem hex]
    exact hs.2

/-- Every outcome of an ordinary send is an outcome of the trace send without leakage, with the
coins removed from the answer. -/
theorem mem_support_tracePlain {AS : Type} [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    {party : Bool} {t : Unit} {s : TraceState P AS}
    {z : Option (ℕ × Option ℕ × Message P.Sym) × TraceState P AS}
    (hz : z ∈ support ((tracePlain view irl tbl rules party t).run s)) :
    ∃ w ∈ support ((traceSend view irl tbl rules party false).run s),
      z = (w.1.map fun x => (x.1, x.2.1, x.2.2.1), w.2) := by
  change z ∈ support (((fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
    traceSend view irl tbl rules party false).run s) at hz
  rw [StateT.run_map, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

/-- A trace send of the installed game with the table `tbl` and the modes `modes` keeps
`TraceInv`. -/
theorem traceSend_traceInv [DecidableEq P.Mac] [DecidableEq P.EpochKey] [SampleableType P.K]
    [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    {irl : P.kem.IncrementalRandLeak P.inc} {S : ScheduledAuthenticator P Root MacKey}
    {tbl : Installed P irl (Root × MacKey)} {modes : Modes} {ik : P.EpochKey}
    (party leaking repair : Bool) (s : TraceState P (Root × MacKey))
    (hs : TraceInv S tbl modes ik repair s)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P (Root × MacKey)}
    (hz : z ∈ support ((traceSend S.toRatcheted irl tbl (installedRules S tbl modes) party
      leaking).run s)) :
    TraceInv S tbl modes ik repair z.2 :=
  TraceInv.step hs (fun hb => traceSend_bad _ irl _ _ hb hz)
    (fun hR _ => traceSend_preserves party leaking s hR hz)
    (traceSend_disjoint _ irl _ _ hs.2 hz)

/-- Let the four stream decoders be sound. Then a receive of the repaired game keeps `TraceInv`, for
every table and every choice of modes. -/
theorem traceReceive_preservesInv [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    [SampleableType P.EpochKey] {irl : P.kem.IncrementalRandLeak P.inc}
    (S : ScheduledAuthenticator P Root MacKey) (tbl : Installed P irl (Root × MacKey))
    (modes : Modes) (ik : P.EpochKey)
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2) (party : Bool) :
    QueryImpl.PreservesInv (traceReceive S.toRatcheted irl true party)
      (TraceInv S tbl modes ik true) := by
  intro n s hs z hz
  have hz' := hz
  rw [traceReceive_run] at hz'
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame hz'
  refine TraceInv.step hs (fun hb => hb) (fun hR _ => ?_) ?_
  · obtain ⟨h1, h2, -⟩ :=
      traceReceive_outcome hHdrSound hEkSound hCt1Sound hCt2Sound party n s hR _ hz
    exact ⟨h1, fun hg _ => h2 ▸ hg⟩
  · change w.2.exposed ∩ w.2.challenged = ∅
    cases party
    · rw [ite_eq_right Bool.false_ne_true] at hw
      obtain ⟨h1, h2, -, -⟩ := SCKAScheme.oracleRecvB_flags _ hw
      rw [h1, h2]
      exact hs.2
    · rw [ite_eq_left rfl] at hw
      obtain ⟨h1, h2, -, -⟩ := SCKAScheme.oracleRecvA_flags _ hw
      rw [h1, h2]
      exact hs.2

/-- Let the four stream decoders be sound. Then a receive of the real game keeps `TraceInv` of the
real game: before the bad event it is the repaired receive (`traceReceive_real_eq`), and it
changes neither the records nor the bad flag. -/
theorem traceReceive_real_preservesInv [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    [SampleableType P.EpochKey] (S : ScheduledAuthenticator P Root MacKey)
    (irl : P.kem.IncrementalRandLeak P.inc) (ik : P.EpochKey)
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2) (party : Bool) :
    QueryImpl.PreservesInv (traceReceive S.toRatcheted irl false party)
      (TraceInv S (Installed.empty (irl := irl)) Modes.real ik false) := by
  intro n s hs z hz
  have hz' := hz
  rw [traceReceive_run] at hz'
  obtain ⟨w, hw, rfl⟩ := mem_support_liftGame hz'
  refine TraceInv.step hs (fun hb => hb) (fun hR hG => ?_) ?_
  · rw [traceReceive_real_eq hHdrSound hEkSound hCt1Sound hCt2Sound party n s hR (hG rfl)] at hz
    obtain ⟨h1, h2, -⟩ :=
      traceReceive_outcome hHdrSound hEkSound hCt1Sound hCt2Sound party n s hR _ hz
    exact ⟨h1, fun hg _ => h2 ▸ hg⟩
  · change w.2.exposed ∩ w.2.challenged = ∅
    cases party
    · rw [ite_eq_right Bool.false_ne_true] at hw
      obtain ⟨h1, h2, -, -⟩ := SCKAScheme.oracleRecvB_flags _ hw
      rw [h1, h2]
      exact hs.2
    · rw [ite_eq_left rfl] at hw
      obtain ⟨h1, h2, -, -⟩ := SCKAScheme.oracleRecvA_flags _ hw
      rw [h1, h2]
      exact hs.2

/-- Let the four stream decoders be sound. Then every query of the real trace game keeps `TraceInv`
of the real game, for every choice of challenge modes. -/
theorem traceImpl_real_preservesInv [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (ik : P.EpochKey)
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2) (modes : Modes) :
    QueryImpl.PreservesInv
      (traceImpl S.toRatcheted some irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) modes false)
      (TraceInv S (Installed.empty (irl := irl)) Modes.real ik false) := by
  have hplain : ∀ party, QueryImpl.PreservesInv
      (tracePlain S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) party)
      (TraceInv S (Installed.empty (irl := irl)) Modes.real ik false) := by
    intro party t s hs z hz
    obtain ⟨w, hw, rfl⟩ := mem_support_tracePlain _ irl _ _ hz
    exact traceSend_traceInv party false false s hs hw
  have hleak : ∀ party, QueryImpl.PreservesInv
      (traceLeak S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) party)
      (TraceInv S (Installed.empty (irl := irl)) Modes.real ik false) :=
    fun party _ s hs _ hz => traceSend_traceInv party true false s hs hz
  exact (((((((((traceUnif_preservesInv S Installed.empty Modes.real ik false).add
    (hplain true)).add (hplain false)).add
    (traceReceive_real_preservesInv S irl ik hHdrSound hEkSound hCt1Sound hCt2Sound true)).add
    (traceReceive_real_preservesInv S irl ik hHdrSound hEkSound hCt1Sound hCt2Sound false)).add
    (hleak true)).add (hleak false)).add
    (traceChallenge_preservesInv S Installed.empty Modes.real ik false Installed.empty modes)).add
    (traceCorrupt_preservesInv S Installed.empty Modes.real ik false true)).add
    (traceCorrupt_preservesInv S Installed.empty Modes.real ik false false)

/-- Let the four stream decoders be sound. At a state that satisfies `TraceInv` of the real game and
has the bad flag false, the real and the repaired trace games answer every query in the same way. -/
theorem traceImpl_real_eq_repaired [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (ik : P.EpochKey)
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2) (modes : Modes) :
    ∀ t s, (TraceInv S (Installed.empty (irl := irl)) Modes.real ik false s ∧ s.bad = false) →
      (traceImpl S.toRatcheted some irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) modes false t).run s =
        (traceImpl S.toRatcheted some irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) modes true t).run s := by
  have hR : ∀ (party : Bool) n (s : TraceState P (Root × MacKey)),
      (TraceInv S (Installed.empty (irl := irl)) Modes.real ik false s ∧ s.bad = false) →
      (traceReceive S.toRatcheted irl false party n).run s =
        (traceReceive S.toRatcheted irl true party n).run s := fun party n s hs =>
    traceReceive_real_eq hHdrSound hEkSound hCt1Sound hCt2Sound party n s
      (hs.1.1 (Or.inr hs.2)).1 ((hs.1.1 (Or.inr hs.2)).2 rfl)
  exact queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _
    (queryEq_add _ (queryEq_add _ (queryEq_add _ (queryEq_add _ (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)) (fun _ _ _ => rfl)) (hR true)) (hR false)) (fun _ _ _ => rfl))
      (fun _ _ _ => rfl)) (fun _ _ _ => rfl)) (fun _ _ _ => rfl)) (fun _ _ _ => rfl)

/-- No query of a trace game clears the bad flag. -/
theorem traceImpl_bad_mono {AS : Type} [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.EpochKey]
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (obs : State P AS → Option (State P (Root × MacKey)))
    (irl : P.kem.IncrementalRandLeak P.inc) (tbl : Installed P irl AS) (rules : UpdateRules P AS)
    (modes : Modes) (repair : Bool) :
    QueryImpl.PreservesInv (traceImpl view obs irl tbl rules modes repair)
      (fun s => s.bad = true) := by
  have hlift : ∀ {ι : Type} {spec : OracleSpec ι}
      (c : QueryImpl spec (StateT (GameState P AS) ProbComp)),
      QueryImpl.PreservesInv (fun t => liftGame (c t))
        (fun s : TraceState P AS => s.bad = true) := by
    intro ι spec c t s hs z hz
    obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
    exact hs
  have hplain : ∀ party, QueryImpl.PreservesInv (tracePlain view irl tbl rules party)
      (fun s : TraceState P AS => s.bad = true) := by
    intro party t s hs z hz
    obtain ⟨w, hw, rfl⟩ := mem_support_tracePlain view irl tbl rules hz
    exact traceSend_bad view irl tbl rules hs hw
  have hrecv : ∀ party, QueryImpl.PreservesInv (traceReceive view irl repair party)
      (fun s : TraceState P AS => s.bad = true) := by
    intro party n s hs z hz
    rw [traceReceive_run] at hz
    obtain ⟨w, -, rfl⟩ := mem_support_liftGame hz
    exact hs
  have hleak : ∀ party, QueryImpl.PreservesInv (traceLeak view irl tbl rules party)
      (fun s : TraceState P AS => s.bad = true) :=
    fun party _ s hs _ hz => traceSend_bad view irl tbl rules hs hz
  have hcorrupt : ∀ party : Bool, QueryImpl.PreservesInv
      (if party then traceCorruptA (AS := AS) (MacKey := MacKey) irl obs
        else traceCorruptB (AS := AS) (MacKey := MacKey) irl obs)
      (fun s : TraceState P AS => s.bad = true) := by
    intro party t s hs z hz
    cases party
    · rw [ite_eq_right Bool.false_ne_true] at hz
      change z ∈ support (traceCorruptB irl obs t s) at hz
      simp only [traceCorruptB] at hz
      split_ifs at hz <;> rw [mem_support_pure_iff] at hz <;> rw [hz] <;> exact hs
    · rw [ite_eq_left rfl] at hz
      change z ∈ support (traceCorruptA irl obs t s) at hz
      simp only [traceCorruptA] at hz
      split_ifs at hz <;> rw [mem_support_pure_iff] at hz <;> rw [hz] <;> exact hs
  exact (((((((((hlift _).add (hplain true)).add (hplain false)).add (hrecv true)).add
    (hrecv false)).add (hleak true)).add (hleak false)).add
    (fun e s hs z hz => by
      rcases mem_support_traceChallenge hz with hz | ⟨-, hz⟩ <;> rw [hz] <;> exact hs)).add
    (hcorrupt true)).add (hcorrupt false)

/-- Forgetting the records and the bad flag of a send of the real trace game gives the leaking send
of the scheme. -/
theorem sampledSend_erase [DecidableEq P.Mac] [DecidableEq P.EpochKey] [SampleableType P.K]
    [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (s : TraceState P (Root × MacKey)) (party : Bool) :
    Prod.fst <$> sampledSend S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) s party =
      Braid.sendRleak P irl S.toRatcheted (s.game.stateAt party) := by
  cases hst : s.game.stateAt party <;>
    simp [sampledSend, hst, installedRules, Installed.empty, Modes.real, Braid.sendRleak,
      ScheduledAuthenticator.toRatcheted]

/-- Projecting an ordinary send of the real trace game to the game state gives the send oracle of
the scheme. -/
theorem tracePlain_map [DecidableEq P.Mac] [DecidableEq P.EpochKey] [SampleableType P.K]
    [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (party : Bool) (t : Unit) (s : TraceState P (Root × MacKey)) :
    Prod.map id TraceState.game <$> (tracePlain S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) party t).run s =
      (Braid.oracleSend S.toRatcheted irl ($ᵗ P.EpochKey) party t).run s.game := by
  rw [Braid.oracleSend_run_eq S.toRatcheted irl ($ᵗ P.EpochKey) s.game party,
    Braid.send_eq_map_sendRleak P irl, ← sampledSend_erase S irl s party]
  change Prod.map id TraceState.game <$> ((fun out => out.map fun x => (x.1, x.2.1, x.2.2.1)) <$>
    traceSend S.toRatcheted irl Installed.empty
      (installedRules S (Installed.empty (irl := irl)) Modes.real) party false).run s = _
  rw [StateT.run_map]
  change Prod.map id TraceState.game <$> ((fun p => _) <$>
    traceSend S.toRatcheted irl Installed.empty
      (installedRules S (Installed.empty (irl := irl)) Modes.real) party false s) = _
  simp only [traceSend, Functor.map_map]
  refine congrArg (fun f => f <$> sampledSend S.toRatcheted irl Installed.empty
    (installedRules S (Installed.empty (irl := irl)) Modes.real) s party) (funext fun w => ?_)
  have h1 := (sendUpdate_flags s.game party w.1.1).1
  simp only [ne_eq, decide_not, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.map_some,
    Prod.map_apply, id_eq, Prod.mk.injEq, true_and]
  rw [← h1]

/-- Projecting a leaking send of the real trace game to the game state gives the leaking send
oracle of the security game under E⁺, of A for `party = true` and of B for `party = false`. -/
theorem traceLeak_map [DecidableEq P.Mac] [DecidableEq P.EpochKey] [SampleableType P.K]
    [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (party : Bool) (t : Unit) (s : TraceState P (Root × MacKey)) :
    Prod.map id TraceState.game <$> (traceLeak S.toRatcheted irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) party t).run s =
      (if party then
        SCKAScheme.oracleSendArleak (successorExposure P irl Root MacKey).rleak (scheme P S irl) t
      else
        SCKAScheme.oracleSendBrleak (successorExposure P irl Root MacKey).rleak (scheme P S irl)
          t).run s.game := by
  cases t
  have hrun : (if party then
        SCKAScheme.oracleSendArleak (successorExposure P irl Root MacKey).rleak (scheme P S irl) ()
      else
        SCKAScheme.oracleSendBrleak (successorExposure P irl Root MacKey).rleak (scheme P S irl)
          ()).run s.game =
      (fun w : SendResult P (Root × MacKey) × SendRand irl.KeygenRand irl.Encaps1Rand =>
        if (successorExposure P irl Root MacKey).rleak (s.game.stateAt party) w.2 ∩
            s.game.challenged ≠ ∅ then (none, s.game)
        else (some (w.1.sendingEpoch, w.1.outputKey.map Prod.fst, w.1.msg, w.2),
          { sendUpdate s.game party w.1 with exposed := s.game.exposed ∪
            (successorExposure P irl Root MacKey).rleak (s.game.stateAt party) w.2 })) <$>
        Braid.sendRleak P irl S.toRatcheted (s.game.stateAt party) := by
    cases party
    · rw [ite_eq_right Bool.false_ne_true, SCKAScheme.oracleSendBrleak_run_eq]
      simp only [scheme, Braid.scheme, map_eq_bind_pure_comp, bind_assoc, pure_bind]
      exact bind_congr fun w => rfl
    · rw [ite_eq_left rfl, SCKAScheme.oracleSendArleak_run_eq]
      simp only [scheme, Braid.scheme, map_eq_bind_pure_comp, bind_assoc, pure_bind]
      exact bind_congr fun w => rfl
  rw [hrun, ← sampledSend_erase S irl s party]
  change Prod.map id TraceState.game <$> traceSend S.toRatcheted irl Installed.empty
    (installedRules S (Installed.empty (irl := irl)) Modes.real) party true s = _
  simp only [traceSend, Functor.map_map]
  refine congrArg (fun f => f <$> sampledSend S.toRatcheted irl Installed.empty
    (installedRules S (Installed.empty (irl := irl)) Modes.real) s party) (funext fun w => ?_)
  have hE : (exposureAt P irl (Root × MacKey)).rleak (s.game.stateAt party) w.1.2 =
      (successorExposure P irl Root MacKey).rleak (s.game.stateAt party) w.1.2 := rfl
  by_cases hc : (successorExposure P irl Root MacKey).rleak (s.game.stateAt party) w.1.2 ∩
      s.game.challenged = ∅
  · simp [hE, hc]
  · simp [hE, hc]

/-- Projecting the challenge of the real trace game with the modes `Modes.fixedBit b` to the game
state gives the challenge oracle of the security game with the bit `b`. -/
theorem traceChallenge_map [SampleableType P.K] [SampleableType P.EpochKey]
    (irl : P.kem.IncrementalRandLeak P.inc) (b : Bool) (e : ℕ)
    (s : TraceState P (Root × MacKey)) :
    Prod.map id TraceState.game <$>
        (traceChallenge (Installed.empty (irl := irl)) (Modes.fixedBit b) e).run s =
      (SCKAScheme.oracleChall b (State P (Root × MacKey)) (State P (Root × MacKey)) P.EpochKey
        (Message P.Sym) e).run s.game := by
  change Prod.map id TraceState.game <$>
    traceChallenge (Installed.empty (irl := irl)) (Modes.fixedBit b) e s = _
  simp only [traceChallenge, SCKAScheme.oracleChall, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hex : e ∈ s.game.exposed ∨ e ∈ s.game.challenged
  · rw [ite_eq_left hex, ite_eq_left hex]
    simp [StateT.run_pure]
  · rw [ite_eq_right hex, ite_eq_right hex]
    cases hA : s.game.keyA e with
    | some k =>
        have hk : lookupKey s.game e = some k := by simp [lookupKey, hA]
        rw [hk]
        cases b <;> simp [Braid.NoAuth.challengeValue, Installed.empty, Modes.fixedBit,
          StateT.run_bind, StateT.run_set, StateT.run_monadLift]
    | none =>
        cases hB : s.game.keyB e with
        | none =>
            have hk : lookupKey s.game e = none := by simp [lookupKey, hA, hB]
            rw [hk]
            simp [StateT.run_pure]
        | some k =>
            have hk : lookupKey s.game e = some k := by simp [lookupKey, hA, hB]
            rw [hk]
            cases b <;> simp [Braid.NoAuth.challengeValue, Installed.empty, Modes.fixedBit,
              StateT.run_bind, StateT.run_set, StateT.run_monadLift]

/-- Projecting each query of the real trace game with the modes `Modes.fixedBit b` to the game state
gives the same query of the security game with the bit `b` under E⁺. -/
theorem traceImpl_real_map [DecidableEq P.Mac] [DecidableEq P.EpochKey] [SampleableType P.K]
    [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (b : Bool) :
    ∀ t s, Prod.map id TraceState.game <$>
        (traceImpl S.toRatcheted some irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false
          t).run s =
      (SCKAScheme.sckaSecurityImpl b (successorExposure P irl Root MacKey)
        (successorExposure P irl Root MacKey) (scheme P S irl) t).run (TraceState.game s) :=
  queryMap_add _ (queryMap_add _ (queryMap_add _ (queryMap_add _ (queryMap_add _
    (queryMap_add _ (queryMap_add _ (queryMap_add _ (queryMap_add _
      (fun _ s => map_game_liftGame _ s)
      (fun t s => tracePlain_map S irl true t s))
      (fun t s => tracePlain_map S irl false t s))
      (fun n s => by rw [traceReceive_run, map_game_liftGame, ite_eq_left rfl]; rfl))
      (fun n s => by
        rw [traceReceive_run, map_game_liftGame, ite_eq_right Bool.false_ne_true]
        rfl))
      (fun t s => traceLeak_map S irl true t s))
      (fun t s => traceLeak_map S irl false t s))
      (fun e s => traceChallenge_map irl b e s))
      (fun _ s => by
        rw [(traceCorrupt_eq_oracleCorrupt irl).1]
        exact map_game_liftGame _ s))
      (fun _ s => by
        rw [(traceCorrupt_eq_oracleCorrupt irl).2]
        exact map_game_liftGame _ s)

/-- Projecting the real trace run with the bit `b` to its game state gives the security game of
`scheme P S irl` with the bit `b` under E⁺, run from the initial states of the same uniform initial
key. The two computations are equal. The stream decoders need not be sound. -/
theorem run_erase [DecidableEq P.Mac] [DecidableEq P.EpochKey] [SampleableType P.K]
    [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P S irl) (b : Bool) :
    Prod.map id TraceState.game <$>
        run S.toRatcheted some S irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false A =
      (do
        let ik ← $ᵗ P.EpochKey
        (simulateQ (SCKAScheme.sckaSecurityImpl b (successorExposure P irl Root MacKey)
          (successorExposure P irl Root MacKey) (scheme P S irl)) A).run
          (SCKAScheme.initGameState (Braid.initA P S.toRatcheted ik)
            (Braid.initB P S.toRatcheted ik))) := by
  have hinit : (installedRules S (Installed.empty (irl := irl)) Modes.real).initPair =
      (fun ik => S.F 1 S.initRoot ik) <$> ($ᵗ P.EpochKey) := rfl
  simp only [run, hinit, map_bind, bind_map_left]
  exact bind_congr fun ik => OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ TraceState.game
    (traceImpl_real_map S irl b) A _

/-- Let the four stream decoders be sound. Then the distance `boolDist` between the output
distributions of the security game `fixed S irl A b` and of the repaired trace game with the bit
`b` is at most the probability that the real trace game with the bit `b` sets the bad flag. -/
theorem fixed_repaired_gap_le [DecidableEq P.Mac] [DecidableEq P.EpochKey] [SampleableType P.K]
    [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (A : Adversary P S irl) (b : Bool) :
    (𝒟[fixed S irl A b].boolDist
        𝒟[Prod.fst <$> run S.toRatcheted some S irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) true
          A]).toReal ≤
      (Pr{let z ← run S.toRatcheted some S irl Installed.empty
            (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false
            A}[z.2.bad = true]).toReal := by
  have hinit : (installedRules S (Installed.empty (irl := irl)) Modes.real).initPair =
      (fun ik => S.F 1 S.initRoot ik) <$> ($ᵗ P.EpochKey) := rfl
  have hrun : ∀ repair, run S.toRatcheted some S irl Installed.empty
      (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) repair A =
      ($ᵗ P.EpochKey) >>= fun ik => (simulateQ (traceImpl S.toRatcheted some irl Installed.empty
        (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) repair)
        A).run (initTrace P (S.F 1 S.initRoot ik)) := by
    intro repair
    simp only [run, hinit, bind_map_left]
  have hfixed : fixed S irl A b = Prod.fst <$> run S.toRatcheted some S irl Installed.empty
      (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false A := by
    have hK : (scheme P S irl).initKeyGen = $ᵗ P.EpochKey := rfl
    have hA : ∀ ik, (scheme P S irl).initA ik = pure (Braid.initA P S.toRatcheted ik) :=
      fun _ => rfl
    have hB : ∀ ik, (scheme P S irl).initB ik = pure (Braid.initB P S.toRatcheted ik) :=
      fun _ => rfl
    have h := congrArg (fun m => Prod.fst <$> m) (run_erase S irl A b)
    simp only [Functor.map_map, map_bind] at h
    simp only [fixed, SCKAScheme.securityExpFixedBit, hK, hA, hB, pure_bind, bind_pure_comp]
    exact h.symm
  rw [ToVCVio.toReal_boolDist_evalDist, hfixed, hrun true, hrun false]
  simp only [prEvent_map]
  have hbounds : ∀ ik : P.EpochKey,
      (Pr{let z ← (simulateQ (traceImpl S.toRatcheted some irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false)
          A).run (initTrace P (S.F 1 S.initRoot ik))}[z.1 = true] ≤
        Pr{let z ← (simulateQ (traceImpl S.toRatcheted some irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) true)
          A).run (initTrace P (S.F 1 S.initRoot ik))}[z.1 = true] +
        Pr{let z ← (simulateQ (traceImpl S.toRatcheted some irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false)
          A).run (initTrace P (S.F 1 S.initRoot ik))}[z.2.bad = true]) ∧
      (Pr{let z ← (simulateQ (traceImpl S.toRatcheted some irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) true)
          A).run (initTrace P (S.F 1 S.initRoot ik))}[z.1 = true] ≤
        Pr{let z ← (simulateQ (traceImpl S.toRatcheted some irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false)
          A).run (initTrace P (S.F 1 S.initRoot ik))}[z.1 = true] +
        Pr{let z ← (simulateQ (traceImpl S.toRatcheted some irl Installed.empty
          (installedRules S (Installed.empty (irl := irl)) Modes.real) (Modes.fixedBit b) false)
          A).run (initTrace P (S.F 1 S.initRoot ik))}[z.2.bad = true]) := fun ik =>
    prEvent_simulateQ_run_bounds_of_inv _ _ (TraceInv S Installed.empty Modes.real ik false)
      (fun s => s.bad = true)
      (traceImpl_real_preservesInv S irl ik hHdrSound hEkSound hCt1Sound hCt2Sound _)
      (traceImpl_bad_mono (Root := Root) (MacKey := MacKey) _ _ _ _ _ _ _)
      (fun t s hs hb => traceImpl_real_eq_repaired S irl ik hHdrSound hEkSound hCt1Sound
        hCt2Sound _ t s ⟨hs, by simpa using hb⟩)
      A (fun x => x = true) _
      (traceInv_init S Installed.empty Modes.real ik false _ fun _ h => by cases h)
  have key : ∀ L R : P.EpochKey → ProbComp (Bool × TraceState P (Root × MacKey)),
      (∀ ik, Pr{let z ← L ik}[z.1 = true] ≤
        Pr{let z ← R ik}[z.1 = true] + Pr{let z ← L ik}[z.2.bad = true]) →
      (∀ ik, Pr{let z ← R ik}[z.1 = true] ≤
        Pr{let z ← L ik}[z.1 = true] + Pr{let z ← L ik}[z.2.bad = true]) →
      |(Pr{let z ← ($ᵗ P.EpochKey >>= L)}[z.1 = true]).toReal -
          (Pr{let z ← ($ᵗ P.EpochKey >>= R)}[z.1 = true]).toReal| ≤
        (Pr{let z ← ($ᵗ P.EpochKey >>= L)}[z.2.bad = true]).toReal := by
    intro L R h1 h2
    have hl := prEvent_bind_le_add_bad_of_disagree' (D := fun _ => False) (ε := 0)
      (mx := $ᵗ P.EpochKey) (my := L) (oc := R) (ob := L)
      (q := fun z : Bool × TraceState P (Root × MacKey) => z.1 = true)
      (r := fun z : Bool × TraceState P (Root × MacKey) => z.2.bad = true)
      (fun _ _ h => h.elim) (fun ik _ _ => by simpa using h1 ik)
    have hr := prEvent_bind_le_add_bad_of_disagree' (D := fun _ => False) (ε := 0)
      (mx := $ᵗ P.EpochKey) (my := R) (oc := L) (ob := L)
      (q := fun z : Bool × TraceState P (Root × MacKey) => z.1 = true)
      (r := fun z : Bool × TraceState P (Root × MacKey) => z.2.bad = true)
      (fun _ _ h => h.elim) (fun ik _ _ => by simpa using h2 ik)
    simp only [add_zero] at hl hr
    have hl' := ENNReal.toReal_mono (by simp) hl
    have hr' := ENNReal.toReal_mono (by simp) hr
    rw [ENNReal.toReal_add (by simp) (by simp)] at hl' hr'
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  exact key _ _ (fun ik => (hbounds ik).1) (fun ik => (hbounds ik).2)

end MLKEMBraid.Auth
