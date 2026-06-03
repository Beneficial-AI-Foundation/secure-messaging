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
_RKEM scheme_ (\#47, Definition 5.1, {Informal.citet TR25}[]).
Syntax for an RKEM: $`(\Gen, \Encaps, \Decaps)` with
ratcheting state evolution.
:::

:::definition "rkem_correctness" (parent := "rkem")
_RKEM correctness_ (Definition 5.2, {Informal.citet TR25}[]).
An RKEM is correct when, for every valid sequence of encapsulate/decapsulate
operations, the decapsulated key matches the encapsulated key.
{uses "rkem_scheme"}[] defines the scheme under test.
:::

:::definition "rkem_security_fs" (parent := "rkem")
_RKEM forward secrecy_ (Definition 5.3, {Informal.citet TR25}[]).
The RKEM forward-secrecy game requires that past encapsulated keys
remain indistinguishable from random even after the current state is
compromised.
{uses "rkem_scheme"}[] defines the scheme under attack.
:::

:::definition "rkem_security_rs" (parent := "rkem")
_RKEM ratchet simulatability_ (Definition 5.4, {Informal.citet TR25}[]).
Ratchet simulatability requires that the adversary cannot distinguish
real ratchet states from simulated ones, ensuring that state exposure
does not reveal information about past keys.
{uses "rkem_scheme"}[] defines the scheme under attack.
:::

# RKEM-from-DDH, non-FS version (issues \#48, \#66–68)

:::definition "rkem_from_ddh_nonfs_spec" (parent := "rkem")
_RKEM-from-DDH (non-FS)_ (\#66, Section 5.2, {Informal.citet TR25}[]).
Construction of an RKEM from the DDH assumption without forward secrecy.
{uses "rkem_scheme"}[] is the target interface.
:::

:::theorem "rkem_from_ddh_nonfs_correctness" (parent := "rkem")
_Correctness of RKEM-from-DDH (non-FS)_ (\#67).
{uses "rkem_from_ddh_nonfs_spec"}[] satisfies {uses "rkem_correctness"}[].
:::

:::theorem "rkem_from_ddh_nonfs_ratchet_sim" (parent := "rkem")
_Ratchet simulatability of RKEM-from-DDH (non-FS)_ (\#68).
{uses "rkem_from_ddh_nonfs_spec"}[] satisfies {uses "rkem_security_rs"}[].
:::

# RKEM-from-DDH, FS version (issues \#69–73)

:::definition "rkem_from_ddh_fs_spec" (parent := "rkem")
_RKEM-from-DDH (FS)_ (\#70, Section 5.3, {Informal.citet TR25}[]).
Construction of an RKEM from the DDH assumption with forward secrecy.
{uses "rkem_scheme"}[] is the target interface.
:::

:::theorem "rkem_from_ddh_fs_correctness" (parent := "rkem")
_Correctness of RKEM-from-DDH (FS)_ (\#71).
{uses "rkem_from_ddh_fs_spec"}[] satisfies {uses "rkem_correctness"}[].
:::

:::theorem "rkem_from_ddh_fs_forward_security" (parent := "rkem")
_Forward security of RKEM-from-DDH (FS)_ (\#72).
{uses "rkem_from_ddh_fs_spec"}[] satisfies {uses "rkem_security_fs"}[].
:::

:::theorem "rkem_from_ddh_fs_ratchet_sim" (parent := "rkem")
_Ratchet simulatability of RKEM-from-DDH (FS)_ (\#73).
{uses "rkem_from_ddh_fs_spec"}[] satisfies {uses "rkem_security_rs"}[].
:::

# RKEM-from-KEM (issues \#74–78)

:::definition "rkem_from_kem_spec" (parent := "rkem")
_RKEM-from-KEM_ (\#75, Section 5.4, {Informal.citet TR25}[]).
Generic construction of an RKEM from a standard KEM.
{uses "rkem_scheme"}[] is the target interface.
:::

:::theorem "rkem_from_kem_correctness" (parent := "rkem")
_Correctness of RKEM-from-KEM_ (\#76).
{uses "rkem_from_kem_spec"}[] satisfies {uses "rkem_correctness"}[].
:::

:::theorem "rkem_from_kem_forward_security" (parent := "rkem")
_Forward security of RKEM-from-KEM_ (\#77).
{uses "rkem_from_kem_spec"}[] satisfies {uses "rkem_security_fs"}[].
:::

:::theorem "rkem_from_kem_ratchet_sim" (parent := "rkem")
_Ratchet simulatability of RKEM-from-KEM_ (\#78).
{uses "rkem_from_kem_spec"}[] satisfies {uses "rkem_security_rs"}[].
:::

# Katana-RKEM-from-Lattices, plain (issues \#79, \#81–84)

:::definition "katana_plain_spec" (parent := "rkem")
_Plain Katana-RKEM-from-Lattices_ (\#81). The basic lattice-based RKEM
construction (Section 6, {Informal.citet TR25}[]).
{uses "rkem_scheme"}[] is the target interface.
:::

:::theorem "katana_plain_correctness" (parent := "rkem")
_Correctness of plain Katana-RKEM_ (\#82).
{uses "katana_plain_spec"}[] satisfies {uses "rkem_correctness"}[].
:::

:::theorem "katana_plain_forward_security" (parent := "rkem")
_Forward security of plain Katana-RKEM_ (\#83).
{uses "katana_plain_spec"}[] satisfies {uses "rkem_security_fs"}[].
:::

:::theorem "katana_plain_ratchet_sim" (parent := "rkem")
_Ratchet simulatability of plain Katana-RKEM_ (\#84).
{uses "katana_plain_spec"}[] satisfies {uses "rkem_security_rs"}[].
:::

# Katana-RKEM-from-Lattices, optimised (issues \#80, \#85–88)

:::definition "katana_optimised_spec" (parent := "rkem")
_Optimised Katana-RKEM-from-Lattices_ (\#85). The bandwidth-optimised
lattice-based RKEM construction (Section 6, {Informal.citet TR25}[]).
{uses "rkem_scheme"}[] is the target interface.
:::

:::theorem "katana_optimised_correctness" (parent := "rkem")
_Correctness of optimised Katana-RKEM_ (\#86).
{uses "katana_optimised_spec"}[] satisfies {uses "rkem_correctness"}[].
:::

:::theorem "katana_optimised_forward_security" (parent := "rkem")
_Forward secrecy of optimised Katana-RKEM_ (\#87).
{uses "katana_optimised_spec"}[] satisfies {uses "rkem_security_fs"}[].
:::

:::theorem "katana_optimised_ratchet_sim" (parent := "rkem")
_Ratchet simulatability of optimised Katana-RKEM_ (\#88).
{uses "katana_optimised_spec"}[] satisfies {uses "rkem_security_rs"}[].
:::
