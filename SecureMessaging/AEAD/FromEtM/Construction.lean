/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.Defs
import SecureMessaging.SymEnc.Defs
import VCVio.CryptoFoundations.PRF

/-!
# Encrypt-then-MAC (EtM) Construction

Constructs an `AEADScheme` from a deterministic symmetric encryption scheme
(`DetSEAlg`) and a pseudorandom function (`PRFScheme`) using the
Encrypt-then-MAC paradigm.

## Paper References

- [NRS14] Namprempre, Rogaway, Shrimpton.
  *Reconsidering Generic Composition.*
  EUROCRYPT 2014.
  — Figure 2, scheme A5 (= A2.100_111): outer-tag EtM with
  `IV = F^iv_L(N)`, `C = E_K(IV, M)`, `T = F^tag_L(N, A, C)`.

## Deviations from NRS14 A5

1. **No nonce `N`**: one-time key provides freshness (ACD19 setting).
2. **No IV derivation from PRF**: deterministic cipher, IV absorbed into key.
3. **Independent keys** `(K_e, K_m)` instead of shared PRF key `L`.
4. **MAC input is `(AD, C)`** not `(N, A, C)` (nonce dropped).
5. **`decrypt` returns `Option M`** matching ACD19's AEAD syntax (not
   `M ∪ {⊥}` as in NRS14).
-/

namespace EtM

open OracleSpec OracleComp

variable {K_e K_m M AD C_e T : Type}
  [DecidableEq AD] [DecidableEq C_e] [DecidableEq T]

/-- Encrypt-then-MAC composition: build an `AEADScheme` from a deterministic
symmetric cipher `se` and a PRF `prf`.

NRS14 Figure 2, scheme A5 (outer-tag EtM), adapted: one-time, no nonce.

- `encrypt(ke, km, ad, m)`: `c := se.encrypt ke m; t := prf.eval km (ad, c); return (c, t)`
- `decrypt(ke, km, ad, (c, t))`: if `t == prf.eval km (ad, c)` then `se.decrypt ke c` else `none`
- `keygen`: independent `ke ← se.keygen; km ← prf.keygen` -/
-- ANCHOR: etmAEAD
def etmAEAD (se : DetSEAlg K_e M C_e)
    (prf : PRFScheme K_m (AD × C_e) T) :
    AEADScheme ProbComp M AD (K_e × K_m) (C_e × T) where
  keygen := do
    let ke ← se.keygen
    let km ← prf.keygen
    return (ke, km)
  encrypt := fun (ke, km) ad m =>
    let c := se.encrypt ke m
    let t := prf.eval km (ad, c)
    (c, t)
  decrypt := fun (ke, km) ad (c, t) =>
    if t == prf.eval km (ad, c)
    then se.decrypt ke c
    else none
-- ANCHOR_END: etmAEAD

end EtM
