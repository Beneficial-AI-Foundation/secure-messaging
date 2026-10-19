/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction
import SecureMessaging.SCKA.MLKEMBraid.Security.Bounds
import SecureMessaging.SCKA.MLKEMBraid.Security.Concrete
import SecureMessaging.SCKA.MLKEMBraid.Security.Bounded

/-!
# No-authentication security of ML-KEM Braid

The generic reduction bound and its unrestricted-payload ML-KEM specialization retain their
public interfaces through this import. The latter keeps abstract payload codecs as caller
parameters: finite-symbol fixed-block codecs cannot universally roundtrip unrestricted
ByteArray payloads. A bounded payload domain is a distinct additive specialization.

The adapter preserves the supplied concrete primitive's vector-before-seed hash convention;
the Braid PDF writes seed-before-vector. No hash-order equality or game hop is asserted.
Theorems quantify over supplied ring and primitive functions; opaque external hashes do not
establish SHA-3/SHAKE semantics. C/FFI, implemented NTT loops, entropy/capped-sampler failure,
constant time and physical erasure remain outside the correspondence proved here. Numerical
FIPS bounds still require NTTRingLaws and CoefficientFailureBound. Abstract algebraic codecs
do not establish runtime SPQR layout or complexity. No primitive/KDF hardness, efficient/QPT
adversary class, authenticated security or messaging-composition result is added.
-/
