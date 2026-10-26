/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction
import SecureMessaging.SCKA.MLKEMBraid.Security.Bounds
import SecureMessaging.SCKA.MLKEMBraid.Security.Concrete
import SecureMessaging.SCKA.MLKEMBraid.Security.Bounded
import SecureMessaging.SCKA.MLKEMBraid.Security.Native
import SecureMessaging.SCKA.MLKEMBraid.Security.InitialSnapshot

/-!
# No-authentication security of ML-KEM Braid

The canonical native endpoints are `NoAuth.security_le_native`,
`mlkemBraidScheme_noAuth_security_le_native` and `mlkemBraidBounded_noAuth_security_le_native`.
They transport the accepted explicit-policy bounds with unchanged premises and loss. The
explicit-policy endpoints and the historical delta experiment through `deltaExposure` remain
available; the old root APIs now take native policies, with no relocated old-name wrappers.

The unrestricted-payload specialization keeps abstract payload codecs as caller parameters:
finite-symbol fixed-block codecs cannot universally roundtrip unrestricted ByteArray payloads.
A bounded payload domain is a distinct additive specialization.

`InitialSnapshot` defines an initialized snapshot/challenge/ciphertext observation and its
correlated primitive trial. Its structural query bounds include selected corruptions and the
challenge even when an oracle refuses a response.

The adapter preserves the supplied concrete primitive's vector-before-seed hash convention;
the Braid PDF writes seed-before-vector. No hash-order equality or game hop is asserted.
Theorems quantify over supplied ring and primitive functions; opaque external hashes do not
establish SHA-3/SHAKE semantics. C/FFI, implemented NTT loops, entropy/capped-sampler failure,
constant time and physical erasure remain outside the correspondence proved here. Numerical
FIPS bounds still require NTTRingLaws and CoefficientFailureBound. Abstract algebraic codecs
do not establish runtime SPQR layout or complexity. No primitive/KDF hardness, efficient/QPT
adversary class, authenticated security or messaging-composition result is added.
-/
