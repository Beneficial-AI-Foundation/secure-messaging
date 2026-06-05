import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.CryptoNotation

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Ratcheting KEM" =>

*References:*

- {Informal.citet TR25}[]

:::group "rkem"
Ratcheting Key Encapsulation Mechanism (RKEM).
:::

# Definitions

:::definition "rkem_scheme" (parent := "rkem")
_RKEM scheme_ (issue \#47).
:::

:::definition "rkem_ratchet_sim" (parent := "rkem")
_RKEM scheme — ratchet simulatability_ (issue \#47).
{uses "rkem_scheme"}[].
:::

:::definition "rkem_forward_security" (parent := "rkem")
_RKEM scheme — forward security_ (issue \#47).
{uses "rkem_scheme"}[].
:::

:::definition "rkem_correctness" (parent := "rkem")
_RKEM scheme — correctness_ (issue \#47).
{uses "rkem_scheme"}[].
:::

# Constructions

## RKEM-from-DDH (non-FS)

:::group "rkem_rkem_from_ddh_non_fs"
RKEM-from-DDH (non-FS).
:::

:::definition "rkem_from_ddh_nonfs_spec" (parent := "rkem_rkem_from_ddh_non_fs")
_RKEM-from-DDH construction (non-FS version)_ (issue \#66).
{uses "rkem_scheme"}[].
:::

:::theorem "rkem_from_ddh_nonfs_correctness" (parent := "rkem_rkem_from_ddh_non_fs")
_RKEM-from-DDH construction (non-FS version) — correctness_ (issue \#67).
{uses "rkem_from_ddh_nonfs_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_correctness"}[].
:::

:::theorem "rkem_from_ddh_nonfs_ratchet_sim" (parent := "rkem_rkem_from_ddh_non_fs")
_RKEM-from-DDH construction (non-FS version) — ratchet simulatability_ (issue \#68).
{uses "rkem_from_ddh_nonfs_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_ratchet_sim"}[].
:::

## RKEM-from-DDH (FS)

:::group "rkem_rkem_from_ddh_fs"
RKEM-from-DDH (FS).
:::

:::definition "rkem_from_ddh_fs_spec" (parent := "rkem_rkem_from_ddh_fs")
_RKEM-from-DDH construction (FS version)_ (issue \#70).
{uses "rkem_scheme"}[].
:::

:::theorem "rkem_from_ddh_fs_correctness" (parent := "rkem_rkem_from_ddh_fs")
_RKEM-from-DDH construction (FS version) — correctness_ (issue \#71).
{uses "rkem_from_ddh_fs_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_correctness"}[].
:::

:::theorem "rkem_from_ddh_fs_forward_security" (parent := "rkem_rkem_from_ddh_fs")
_RKEM-from-DDH construction (FS version) — forward security_ (issue \#72).
{uses "rkem_from_ddh_fs_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_forward_security"}[].
:::

:::theorem "rkem_from_ddh_fs_ratchet_sim" (parent := "rkem_rkem_from_ddh_fs")
_RKEM-from-DDH construction (FS version) — ratchet simulatability_ (issue \#73).
{uses "rkem_from_ddh_fs_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_ratchet_sim"}[].
:::

## RKEM-from-KEM

:::group "rkem_rkem_from_kem"
RKEM-from-KEM.
:::

:::definition "rkem_from_kem_spec" (parent := "rkem_rkem_from_kem")
_RKEM-from-KEM construction_ (issue \#75).
{uses "rkem_scheme"}[].
:::

:::theorem "rkem_from_kem_correctness" (parent := "rkem_rkem_from_kem")
_RKEM-from-KEM construction — correctness_ (issue \#76).
{uses "rkem_from_kem_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_correctness"}[].
:::

:::theorem "rkem_from_kem_forward_security" (parent := "rkem_rkem_from_kem")
_RKEM-from-KEM construction — forward security_ (issue \#77).
{uses "rkem_from_kem_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_forward_security"}[].
:::

:::theorem "rkem_from_kem_ratchet_sim" (parent := "rkem_rkem_from_kem")
_RKEM-from-KEM construction — ratchet simulatability_ (issue \#78).
{uses "rkem_from_kem_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_ratchet_sim"}[].
:::

## Katana RKEM (plain)

:::group "rkem_katana_rkem_plain"
Katana RKEM (plain).
:::

:::definition "plain_katana_rkem_spec" (parent := "rkem_katana_rkem_plain")
_plain Katana-RKEM-from-Lattices construction_ (issue \#81).
{uses "rkem_scheme"}[].
:::

:::theorem "plain_katana_rkem_correctness" (parent := "rkem_katana_rkem_plain")
_plain Katana-RKEM-from-Lattices construction — correctness_ (issue \#82).
{uses "plain_katana_rkem_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_correctness"}[].
:::

:::theorem "plain_katana_rkem_forward_security" (parent := "rkem_katana_rkem_plain")
_plain Katana-RKEM-from-Lattices construction — forward security_ (issue \#83).
{uses "plain_katana_rkem_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_forward_security"}[].
:::

:::theorem "plain_katana_rkem_ratchet_sim" (parent := "rkem_katana_rkem_plain")
_plain Katana-RKEM-from-Lattices construction — ratchet simulatability_ (issue \#84).
{uses "plain_katana_rkem_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_ratchet_sim"}[].
:::

## Katana RKEM (optimised)

:::group "rkem_katana_rkem_optimised"
Katana RKEM (optimised).
:::

:::definition "optimised_katana_rkem_spec" (parent := "rkem_katana_rkem_optimised")
_optimised Katana-RKEM-from-Lattices construction_ (issue \#85).
{uses "rkem_scheme"}[].
:::

:::theorem "optimised_katana_rkem_correctness" (parent := "rkem_katana_rkem_optimised")
_optimised Katana-RKEM-from-Lattices construction — correctness_ (issue \#86).
{uses "optimised_katana_rkem_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_correctness"}[].
:::

:::theorem "optimised_katana_rkem_forward_security" (parent := "rkem_katana_rkem_optimised")
_optimised Katana-RKEM-from-Lattices construction — forward security_ (issue \#87).
{uses "optimised_katana_rkem_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_forward_security"}[].
:::

:::theorem "optimised_katana_rkem_ratchet_sim" (parent := "rkem_katana_rkem_optimised")
_optimised Katana-RKEM-from-Lattices construction — ratchet simulatability_ (issue \#88).
{uses "optimised_katana_rkem_spec"}[].
{uses "rkem_scheme"}[].
{uses "rkem_ratchet_sim"}[].
:::

