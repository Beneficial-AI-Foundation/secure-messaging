import SecureMessaging.SCKA.MLKEMBraid.Correctness.KnownPrefix

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

def State.controlPosition
    {P : Parameters ProbComp} {AuthState : Type} :
    State P AuthState → Bool × ℕ
  | .keysUnsampled .. => (true, 0)
  | .keysSampled .. => (true, 1)
  | .headerSent .. => (true, 2)
  | .ct1Received .. => (true, 3)
  | .ekSentCt1Received .. => (true, 4)
  | .noHeaderReceived .. => (false, 0)
  | .headerReceived .. => (false, 1)
  | .ct1Sampled .. => (false, 2)
  | .ekReceivedCt1Sampled .. => (false, 3)
  | .ct1Acknowledged .. => (false, 3)
  | .ct2Sampled .. => (false, 4)

def ControlInv
    {P : Parameters ProbComp} {AuthState : Type}
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym)) : Prop :=
  EpochKnowledgeInv s ∧ RecordedReportInv s ∧
    s.tcurA ≤ s.stA.epoch - 1 ∧
    s.tcurB ≤ s.stB.epoch - 1 ∧
    ∀ party : Bool,
      let st := if party then s.stA else s.stB
      let peer := if party then s.stB else s.stA
      let messages := if party then s.msgA else s.msgB
      st.controlPosition.1 = decide (st.epoch % 2 = if party then 1 else 0) ∧
      (peer.epoch = st.epoch + 1 → st.controlPosition = (false, 4)) ∧
      ∀ n msg tsnd, messages n = some (msg, tsnd) →
        msg.wellFormed = true ∧ msg.epoch ≤ st.epoch ∧
        match msg.type with
        | .none => True
        | .hdr =>
            party = decide (msg.epoch % 2 = 1) ∧
              (msg.epoch = st.epoch → 1 ≤ st.controlPosition.2)
        | .ek =>
            party = decide (msg.epoch % 2 = 1) ∧
              (msg.epoch = st.epoch → 2 ≤ st.controlPosition.2)
        | .ekCt1Ack =>
            party = decide (msg.epoch % 2 = 1) ∧
              (msg.epoch = st.epoch → 3 ≤ st.controlPosition.2)
        | .ct1 =>
            party ≠ decide (msg.epoch % 2 = 1) ∧
              (msg.epoch = st.epoch → 2 ≤ st.controlPosition.2)
        | .ct2 =>
            party ≠ decide (msg.epoch % 2 = 1) ∧
              (msg.epoch = st.epoch → 4 ≤ st.controlPosition.2)
        | .ct1Ack => False

private def MessageControl
    {P : Parameters ProbComp} {AuthState : Type}
    (party : Bool) (st : State P AuthState)
    (msg : Message P.Sym) : Prop :=
  msg.wellFormed = true ∧ msg.epoch ≤ st.epoch ∧
    match msg.type with
    | .none => True
    | .hdr =>
        party = decide (msg.epoch % 2 = 1) ∧
          (msg.epoch = st.epoch → 1 ≤ st.controlPosition.2)
    | .ek =>
        party = decide (msg.epoch % 2 = 1) ∧
          (msg.epoch = st.epoch → 2 ≤ st.controlPosition.2)
    | .ekCt1Ack =>
        party = decide (msg.epoch % 2 = 1) ∧
          (msg.epoch = st.epoch → 3 ≤ st.controlPosition.2)
    | .ct1 =>
        party ≠ decide (msg.epoch % 2 = 1) ∧
          (msg.epoch = st.epoch → 2 ≤ st.controlPosition.2)
    | .ct2 =>
        party ≠ decide (msg.epoch % 2 = 1) ∧
          (msg.epoch = st.epoch → 4 ≤ st.controlPosition.2)
    | .ct1Ack => False

private def ReceiveControlStep
    {P : Parameters ProbComp} {AuthState : Type}
    (st : State P AuthState) (msg : Message P.Sym)
    (st' : State P AuthState) : Prop :=
  (st'.epoch = st.epoch ∧
    st'.controlPosition.1 = st.controlPosition.1 ∧
    st.controlPosition.2 ≤ st'.controlPosition.2) ∨
  (st'.epoch = st.epoch + 1 ∧
    st.controlPosition = (true, 4) ∧
    st'.controlPosition = (false, 0) ∧
    msg.type = .ct2 ∧ msg.epoch = st.epoch) ∨
  (st'.epoch = st.epoch + 1 ∧
    st.controlPosition = (false, 4) ∧
    st'.controlPosition = (true, 0) ∧
    msg.epoch = st.epoch + 1)

private theorem send_control
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (party : Bool) (st : State P AuthState)
    (hrole : st.controlPosition.1 =
      decide (st.epoch % 2 = if party then 1 else 0))
    (r : SendResult P AuthState)
    (hr : r ∈ support (send P auth st)) :
    r.state.epoch = st.epoch ∧
      r.state.controlPosition.1 = st.controlPosition.1 ∧
      st.controlPosition.2 ≤ r.state.controlPosition.2 ∧
      MessageControl party r.state r.msg := by
  have hparity := Nat.mod_two_eq_zero_or_one st.epoch
  cases st
  case keysUnsampled =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨⟨pk, sk⟩, _, hr⟩ := hr
    simp only [mem_support_pure_iff] at hr
    subst r
    simp only [MessageControl, State.controlPosition, State.epoch,
      Message.wellFormed, Option.isSome, true_and] at hrole hparity ⊢
    rcases hparity with heven | hodd <;>
      cases party <;> simp_all
  case headerReceived =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨⟨encapsState, ct1, key⟩, _, hr⟩ := hr
    simp only [mem_support_pure_iff] at hr
    subst r
    simp only [MessageControl, State.controlPosition, State.epoch,
      Message.wellFormed, Option.isSome, true_and] at hrole hparity ⊢
    rcases hparity with heven | hodd <;>
      cases party <;> simp_all
  all_goals
    simp only [send, mem_support_pure_iff] at hr
    subst r
    simp only [MessageControl, State.controlPosition, State.epoch,
      Message.wellFormed, Option.isSome, Option.isNone, true_and] at hrole hparity ⊢
    rcases hparity with heven | hodd <;>
      cases party <;> simp_all

private theorem receive_control_generator
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym)
    (hgenerator : st.controlPosition.1 = true)
    (r : RecvResult P AuthState)
    (hr : receive P auth st msg = .ok r) :
    ReceiveControlStep st msg r.state := by
  cases st <;>
    simp [State.controlPosition] at hgenerator
  all_goals
    simp only [receive] at hr
    repeat' split at hr
    all_goals cases hr
    all_goals simp_all [ReceiveControlStep, State.epoch, State.controlPosition]

private theorem receive_control_encapsulator
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym)
    (hencapsulator : st.controlPosition.1 = false)
    (r : RecvResult P AuthState)
    (hr : receive P auth st msg = .ok r) :
    ReceiveControlStep st msg r.state := by
  cases st <;>
    simp [State.controlPosition] at hencapsulator
  all_goals
    simp only [receive] at hr
    repeat' split at hr
    all_goals cases hr
    all_goals simp_all [ReceiveControlStep, State.epoch, State.controlPosition]

end MLKEMBraid
