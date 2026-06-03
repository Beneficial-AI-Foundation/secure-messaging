import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.CryptoNotation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Ratcheting Key Encapsulation Mechanism" =>

An RKEM provides key encapsulation with ratcheting: each operation
advances the state, providing forward secrecy and post-compromise security
(Section 5.1, {Informal.citet TR25}[]).

:::group "rkem"
Ratcheting Key Encapsulation Mechanism (RKEM).
:::

# Scheme Definition (issues \#43, \#47)

:::definition "rkem_scheme" (parent := "rkem")
_RKEM scheme_ (\#47, Section 5.1, {Informal.citet TR25}[]).
Syntax for an RKEM: $`(\Gen, \Encaps, \Decaps)` with
ratcheting state evolution. Security notions include forward secrecy (FS)
and ratchet simulatability (RS).
:::

# RKEM-from-DDH, non-FS version (issues \#48, \#66–68)

:::definition "rkem_from_ddh_nonfs_spec" (parent := "rkem")
_RKEM-from-DDH (non-FS)_ (\#66). Construction of an RKEM from the DDH assumption
without forward secrecy.
{uses "rkem_scheme"}[] is the target interface.
:::

:::theorem "rkem_from_ddh_nonfs_correctness" (parent := "rkem")
_Correctness of RKEM-from-DDH (non-FS)_ (\#67).
{uses "rkem_from_ddh_nonfs_spec"}[] satisfies RKEM correctness.
:::

:::theorem "rkem_from_ddh_nonfs_ratchet_sim" (parent := "rkem")
_Ratchet simulatability of RKEM-from-DDH (non-FS)_ (\#68).
{uses "rkem_from_ddh_nonfs_spec"}[] satisfies ratchet simulatability.
:::

# RKEM-from-DDH, FS version (issues \#69–73)

:::definition "rkem_from_ddh_fs_spec" (parent := "rkem")
_RKEM-from-DDH (FS)_ (\#70). Construction of an RKEM from the DDH assumption
with forward secrecy.
{uses "rkem_scheme"}[] is the target interface.
:::

:::theorem "rkem_from_ddh_fs_correctness" (parent := "rkem")
_Correctness of RKEM-from-DDH (FS)_ (\#71).
{uses "rkem_from_ddh_fs_spec"}[] satisfies RKEM correctness.
:::

:::theorem "rkem_from_ddh_fs_forward_security" (parent := "rkem")
_Forward security of RKEM-from-DDH (FS)_ (\#72).
{uses "rkem_from_ddh_fs_spec"}[] satisfies RKEM forward secrecy.
:::

:::theorem "rkem_from_ddh_fs_ratchet_sim" (parent := "rkem")
_Ratchet simulatability of RKEM-from-DDH (FS)_ (\#73).
{uses "rkem_from_ddh_fs_spec"}[] satisfies ratchet simulatability.
:::

# RKEM-from-KEM (issues \#74–78)

:::definition "rkem_from_kem_spec" (parent := "rkem")
_RKEM-from-KEM_ (\#75). Generic construction of an RKEM from a standard KEM.
{uses "rkem_scheme"}[] is the target interface.
:::

:::theorem "rkem_from_kem_correctness" (parent := "rkem")
_Correctness of RKEM-from-KEM_ (\#76).
{uses "rkem_from_kem_spec"}[] satisfies RKEM correctness.
:::

:::theorem "rkem_from_kem_forward_security" (parent := "rkem")
_Forward security of RKEM-from-KEM_ (\#77).
{uses "rkem_from_kem_spec"}[] satisfies RKEM forward secrecy.
:::

:::theorem "rkem_from_kem_ratchet_sim" (parent := "rkem")
_Ratchet simulatability of RKEM-from-KEM_ (\#78).
{uses "rkem_from_kem_spec"}[] satisfies ratchet simulatability.
:::

# Katana-RKEM-from-Lattices, plain (issues \#79, \#81–84)

:::definition "katana_plain_spec" (parent := "rkem")
_Plain Katana-RKEM-from-Lattices_ (\#81). The basic lattice-based RKEM
construction (Section 6, {Informal.citet TR25}[]).
{uses "rkem_scheme"}[] is the target interface.
:::

:::theorem "katana_plain_correctness" (parent := "rkem")
_Correctness of plain Katana-RKEM_ (\#82).
{uses "katana_plain_spec"}[] satisfies RKEM correctness.
:::

:::theorem "katana_plain_forward_security" (parent := "rkem")
_Forward security of plain Katana-RKEM_ (\#83).
{uses "katana_plain_spec"}[] satisfies RKEM forward secrecy.
:::

:::theorem "katana_plain_ratchet_sim" (parent := "rkem")
_Ratchet simulatability of plain Katana-RKEM_ (\#84).
{uses "katana_plain_spec"}[] satisfies ratchet simulatability.
:::

# Katana-RKEM-from-Lattices, optimised (issues \#80, \#85–88)

:::definition "katana_optimised_spec" (parent := "rkem")
_Optimised Katana-RKEM-from-Lattices_ (\#85). The bandwidth-optimised
lattice-based RKEM construction (Section 6, {Informal.citet TR25}[]).
{uses "rkem_scheme"}[] is the target interface.
:::

:::theorem "katana_optimised_correctness" (parent := "rkem")
_Correctness of optimised Katana-RKEM_ (\#86).
{uses "katana_optimised_spec"}[] satisfies RKEM correctness.
:::

:::theorem "katana_optimised_forward_security" (parent := "rkem")
_Forward secrecy of optimised Katana-RKEM_ (\#87).
{uses "katana_optimised_spec"}[] satisfies RKEM forward secrecy.
:::

:::theorem "katana_optimised_ratchet_sim" (parent := "rkem")
_Ratchet simulatability of optimised Katana-RKEM_ (\#88).
{uses "katana_optimised_spec"}[] satisfies ratchet simulatability.
:::
