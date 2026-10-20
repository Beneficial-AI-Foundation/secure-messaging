import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography

open Verso.Genre Manual
open Informal

set_option doc.verso true

#doc (Manual) "Errata" =>

During formalization, we found the following issues in {Informal.citet SCKA25}[].
The protocol pages contain the full explanations, execution traces, and corrections.
The numbering preserves the original errata list.

1. Under the paper's strict failure convention, Opp-BiKEM can abort a send while
   waiting for the peer's encapsulation key. See {bpref "opp_bikem_cka_spec"}[] and its
   {ref "opp-bikem-errata"}[errata box] for the trace, modeling convention, and proposed paper correction.
   The same issue occurs in {bpref "opp_rkem_cka_spec"}[Opp-RKEM].
2. Opp-BiKEM sends and records public-key acknowledgements at the wrong indices,
   preventing the first key exchange from completing. See the {ref "opp-bikem-errata"}[Opp-BiKEM errata box]
   for the correction table and execution trace.
3. Opp-BiKEM uses A's responder counter in Send-B and overwrites A's own ciphertext
   in Rec-A. See the {ref "opp-bikem-errata"}[Opp-BiKEM errata box] for the corrected variables.
4. Opp-UniKEM records acknowledgements in the wrong epoch, which can prevent later
   key exchanges. See {bpref "opp_unikem_cka_spec"}[] for the failure trace and epoch guard.
5. Opp-UniKEM Rec-B returns the receiver's epoch instead of the message's sending
   epoch. See {bpref "opp_unikem_cka_spec"}[] for the delayed-delivery example and correction.
