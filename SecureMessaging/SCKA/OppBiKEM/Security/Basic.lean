/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Defs

/-!
# Opp-BiKEM — Security interface

**Main result.** The SCKA security interface of Opp-BiKEM admits Boolean adversaries `adv`
(`securitySpec`, `SecurityAdversary`, `Defs`), whose *send budget* `q` bounds the ordinary and
leaking sends on every oracle-response path (`SecuritySendQueryBound adv q`, `Defs`).

- A leaking send without its coins is the ordinary send, for either role and every local state
  (`sendWith_rleak_forget`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- For either role and every local state, dropping the returned coins from the leaking-send
engine gives the ordinary send computation, including effects preceding a failed send. -/
theorem sendWith_rleak_forget
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (kem : KEMScheme m K PK SK C)
    (role : Role)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (st : State PK SK C Sym) :
    (do
      let out ←
        sendWith role leak.keygenRleak leak.encapsRleak ecEk ecCt st
      pure (out.map fun (key, msg, epoch, state, _) =>
        (key, msg, epoch, state))) =
      send role kem ecEk ecCt st := by
  simp only [send, sendWith, ← leak.keygen_fst, ← leak.encaps_fst, bind_assoc, pure_bind]
  split
  · simp only [bind_assoc]
    refine bind_congr fun _ => ?_
    split_ifs <;> (try split) <;> simp
  · split_ifs <;> (try split) <;> simp

end oppBiKemCKA
