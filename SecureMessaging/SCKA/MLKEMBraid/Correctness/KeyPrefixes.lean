import SecureMessaging.SCKA.MLKEMBraid.Construction

open OracleSpec OracleComp

universe u

namespace MLKEMBraid

def State.completedEpoch
    {m : Type → Type u} [Monad m]
    {P : Parameters m} {AuthState : Type} :
    State P AuthState → ℕ
  | .ct1Sampled e .. => e
  | .ekReceivedCt1Sampled e .. => e
  | .ct1Acknowledged e .. => e
  | .ct2Sampled e .. => e
  | st => st.epoch - 1

theorem send_completedEpoch_of_mem_support
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState)
    (hpos : 0 < st.epoch)
    (r : SendResult P AuthState)
    (hr : r ∈ support (send P auth st)) :
    0 < r.state.epoch ∧
      (match r.outputKey with
       | none => r.state.completedEpoch = st.completedEpoch
       | some (tI, _) =>
           tI = st.completedEpoch + 1 ∧
             r.state.completedEpoch = tI) := by
  cases st
  case keysUnsampled =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨pk, sk⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    simpa [State.epoch, State.completedEpoch] using hpos
  case headerReceived =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨encapsState, ct1, k⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    simp only [State.epoch] at hpos
    simp only [State.epoch, State.completedEpoch, and_true]
    omega
  all_goals
    simp only [send, mem_support_pure_iff] at hr
    subst r
    simpa [State.epoch, State.completedEpoch] using hpos

theorem receive_completedEpoch_of_eq_ok
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState)
    (hpos : 0 < st.epoch)
    (msg : Message P.Sym)
    (r : RecvResult P AuthState)
    (hr : receive P auth st msg = .ok r) :
    0 < r.state.epoch ∧
      (match r.outputKey with
       | none => r.state.completedEpoch = st.completedEpoch
       | some (tI, _) =>
           tI = st.completedEpoch + 1 ∧
             r.state.completedEpoch = tI) := by
  cases hst : st <;>
    simp only [hst, State.epoch] at hpos hr ⊢ <;>
    simp only [receive] at hr
  all_goals
    repeat' split at hr
  all_goals cases hr
  all_goals simp only [State.epoch, State.completedEpoch, and_true]
  all_goals repeat' apply And.intro
  all_goals omega

end MLKEMBraid
