import SecureMessaging.SCKA.MLKEMBraid.Correctness.KeyPrefixes
import SecureMessaging.SCKA.MLKEMBraid.Correctness.MessageReports

open OracleSpec OracleComp

namespace MLKEMBraid

/-- A supported send preserves the negotiation epoch, records it in the message,
and sends `Ct2` only after completing that epoch. -/
theorem send_epoch_fields_of_mem_support
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState)
    (r : SendResult P AuthState)
    (hr : r ∈ support (send P auth st)) :
    r.state.epoch = st.epoch ∧
      r.msg.epoch = st.epoch ∧
      (r.msg.type = .ct2 → r.msg.epoch ≤ st.completedEpoch) := by
  cases st
  case keysUnsampled =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨pk, sk⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    simp [State.epoch]
  case headerReceived =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨encapsState, ct1, k⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    simp [State.epoch]
  all_goals
    simp only [send, mem_support_pure_iff] at hr
    subst r
    simp [State.epoch, State.completedEpoch]

/-- A successful receive preserves the peer-relative negotiation-epoch bound. -/
theorem receive_epoch_le_of_eq_ok
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym)
    (r : RecvResult P AuthState) (c : ℕ)
    (hst : st.epoch ≤ c + 1)
    (hmsg : msg.epoch ≤ c + 1)
    (hct2 : msg.type = .ct2 → msg.epoch ≤ c)
    (hr : receive P auth st msg = .ok r) :
    r.state.epoch ≤ c + 1 := by
  cases hstate : st <;>
    simp only [hstate, State.epoch] at hst hr ⊢ <;>
    simp only [receive] at hr
  all_goals
    repeat' split at hr
  all_goals cases hr
  all_goals simp_all only
  all_goals first | omega | have := hct2 trivial; omega

end MLKEMBraid
