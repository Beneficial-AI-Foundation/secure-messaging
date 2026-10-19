#!/usr/bin/env python3
"""Generate ../dylean-simpleauth-workshop.html with code excerpts pulled from the sources.

Every excerpt is read from disk by line range and checked against an expected first line,
so the tutorial cannot silently drift from the compiled files.

Library excerpts are read from the pinned dependency checkouts, so build both projects first:
    (cd dylean-examples && lake build) && (cd leandy-examples && lake build)
    python3 tools/generate_dylean_tutorial.py
"""
import html
import re
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent  # symbolicTools/
OUT = ROOT / "dylean-simpleauth-workshop.html"

DY_REV = "d58f33b8d2d8dee121072afa9094bdb5bdf44ef6"
LDY_REV = "e0705986c5dea547848bf80c10b5c4f88ae6868c"
DY_TREE = f"https://github.com/BobDyLean/dylean/tree/{DY_REV}/"
# "dylean:<path>" and "leandy:<path>" denote files of the libraries: read from the
# dependency checkout, linked to GitHub at the pinned commit.
LIBS = {
    "dylean": ("dylean-examples/.lake/packages/dylean/", f"https://github.com/BobDyLean/dylean/blob/{DY_REV}/", "DYLean"),
    "leandy": ("leandy-examples/.lake/packages/leandy/", f"https://github.com/SecPriv/leandy/blob/{LDY_REV}/", "LeanDY"),
}


def _resolve(rel):
    """Return (source path, href, display name) for an excerpt location."""
    lib, sep, path = rel.partition(":")
    if sep and lib in LIBS:
        src, url, name = LIBS[lib]
        return ROOT / src / path, url + path, f"{name} · {path}"
    for prefix in ("dylean-examples/", "leandy-examples/"):
        if rel.startswith(prefix):
            return ROOT / rel, rel, rel[len(prefix):]
    return ROOT / rel, rel, rel

report = []


def fig(rel, a, b, expect, label="Repository excerpt"):
    src, href, display = _resolve(rel)
    lines = src.read_text().split("\n")
    chunk = lines[a - 1:b]
    if not chunk[0].strip().startswith(expect):
        sys.exit(f"excerpt mismatch in {rel}:{a}: expected {expect!r}, got {chunk[0]!r}")
    code = textwrap.dedent("\n".join(chunk)).rstrip("\n")
    report.append(f"{rel}:{a}-{b}  first={chunk[0].strip()[:50]!r}  last={chunk[-1].strip()[:50]!r}")
    if href.startswith("https://"):
        href += f"#L{a}" if a == b else f"#L{a}-L{b}"
    return (
        f'<figure><figcaption>{label} · <a href="{href}">{display}:{a}–{b}</a></figcaption>'
        f"<pre><code>{html.escape(code)}</code></pre></figure>\n"
    )


def fig_find(rel, start_pattern, n_lines, label="LeanDY example excerpt"):
    """Excerpt located by its first line's content rather than by line number."""
    lines = _resolve(rel)[0].read_text().split("\n")
    for i, line in enumerate(lines):
        if line.strip().startswith(start_pattern):
            return fig(rel, i + 1, i + n_lines, start_pattern, label)
    sys.exit(f"pattern {start_pattern!r} not found in {rel}")


def block(code, label):
    code = textwrap.dedent(code).strip("\n")
    return f"<figure><figcaption>{label}</figcaption><pre><code>{html.escape(code)}</code></pre></figure>\n"


def task(text):
    return f'<aside class="task"><strong>For your own protocol</strong><p>{text}</p></aside>\n'


def note(text):
    return f'<aside class="note">{text}</aside>\n'


SA = "dylean-examples/DYLeanExamples/SimpleAuth/"
SPEC = SA + "Specification.lean"
PROOF = SA + "Proof.lean"
SYM = SA + "SymEnc.lean"
INST = SA + "Instance.lean"
THM = SA + "SecurityTheorems.lean"
SAN = SA + "SanityChecks.lean"
LDY = "leandy-examples/LeanDYExamples/SimpleAuth.lean"

CSS = """
:root { --bg:#f5f6f9; --ink:#17213a; --muted:#5c6680; --accent:#24539a; --line:#d8deea; --soft:#e6ebf4; --code:#16213a; --codeink:#e8eefb; --head:#18294a; }
* { box-sizing:border-box; } html { scroll-behavior:smooth; }
body { margin:0; background:var(--bg); color:var(--ink); font:16px/1.7 system-ui,sans-serif; }
header { padding:62px max(24px,calc((100vw - 1200px)/2)); background:var(--head); color:white; }
header p { max-width:780px; color:#d7e0f2; } .kicker { font-size:12px; letter-spacing:.15em; text-transform:uppercase; }
h1 { font:700 clamp(36px,5vw,62px)/1.1 Georgia,serif; margin:12px 0; max-width:930px; }
.layout { max-width:1250px; margin:auto; padding:35px 24px 80px; display:grid; grid-template-columns:235px minmax(0,1fr); gap:38px; }
nav { position:sticky; top:20px; align-self:start; max-height:94vh; overflow:auto; font-size:13px; }
nav a { display:block; padding:6px 8px; text-decoration:none; border-left:2px solid var(--line); }
a { color:var(--accent); text-underline-offset:3px; } section { margin-bottom:62px; scroll-margin-top:25px; min-width:0; }
h2 { font:700 30px/1.25 Georgia,serif; border-top:3px solid var(--accent); padding-top:20px; }
h3 { font:700 19px/1.3 Georgia,serif; margin:28px 0 6px; }
p { margin:14px 0; } .lead { font-size:20px; } code { font: .88em/1.6 ui-monospace,Consolas,monospace; overflow-wrap:anywhere; }
p code,li code,td code,summary code { background:var(--soft); padding:2px 4px; border-radius:3px; }
figure { margin:22px 0; } figcaption { font-size:12px; background:#e1e7f1; padding:9px 13px; border-radius:8px 8px 0 0; }
pre { margin:0 0 20px; padding:18px; background:var(--code); color:var(--codeink); overflow:auto; border-radius:0 0 8px 8px; line-height:1.6; }
pre code { white-space:pre; overflow-wrap:normal; } table { border-collapse:collapse; width:100%; background:white; margin:20px 0; font-size:14px; }
th,td { text-align:left; padding:12px; border:1px solid var(--line); vertical-align:top; } th { background:var(--soft); }
.tablewrap { overflow-x:auto; }
aside { padding:16px 20px; margin:22px 0; border-left:4px solid var(--accent); background:#e9eef7; }
aside p { margin:7px 0 0; } .note { border-color:#b37c24; background:#faf0d9; }
.verified { border-color:#2f7d4f; background:#e5f3ea; }
.pair { display:grid; grid-template-columns:1fr 1fr; gap:16px; } .pair figure { margin:12px 0; min-width:0; }
details { margin:15px 0; padding:14px 18px; background:white; border:1px solid var(--line); border-radius:8px; }
summary { cursor:pointer; font-weight:700; } .check { display:block; padding:10px 12px; background:white; border-bottom:1px solid var(--line); }
.check input { margin-right:10px; accent-color:var(--accent); } li { margin-bottom:7px; }
@media(max-width:850px) { .layout { display:block; padding:24px 16px; } nav { position:static; max-height:none; margin-bottom:35px; } header { padding:36px 22px; } .pair { grid-template-columns:1fr; } }
@media print { nav { display:none; } .layout { display:block; } header { background:white; color:black; padding:20px; } header p { color:black; } pre { white-space:pre-wrap; } pre code { white-space:pre-wrap; } details { display:block; } }
"""

NAV = [
    ("start", "0. Begin with a precise goal"),
    ("setup", "1. Set up the project and the reading map"),
    ("bytes", "2. Choose your primitives, and add the missing one"),
    ("data", "3. Define messages, states, events and their formats"),
    ("code", "4. Write each protocol step as a program"),
    ("reach", "5. Decide what the attacker can do"),
    ("sanity", "6. Check honest execution before interpreting security"),
    ("labels", "7. Assign labels and usages"),
    ("crypto", "8. Define what valid ciphertexts mean"),
    ("state", "9. Define state invariants, including compromise"),
    ("events", "10. Turn your security goal into event invariants"),
    ("contract", "11. Understand the proof contract before using tactics"),
    ("proof-start", "12. Prove key setup and the first message"),
    ("proof-respond", "13. Prove the responder: establishing the encryption invariant"),
    ("proof-finish", "14. Prove the final step: decryption and monotonization"),
    ("theorem", "15. Close the world and extract the theorem"),
    ("probe", "16. Probe the property with an attack trace"),
    ("map", "17. LeanDY ↔ DYLean, concept by concept"),
    ("beyond", "18. Extend beyond what SimpleAuth demonstrates"),
    ("checklist", "19. Your protocol-author checklist"),
    ("references", "Source map and verification notes"),
]

S = {}

# ---------------------------------------------------------------- 0
LDYLIB = "leandy:Leandy/Lib/Crypto.lean"
S["start"] = (
    """<p class="lead">Your job is the same as in LeanDY: define what executions mean, choose an invariant strong enough to express your goal, and prove that every protocol step preserves it. What changes is <em>where</em> each of these lives. In DYLean, executions are the programs you write, run by an attacker who chooses their arguments.</p>
<p>The message flow is the one from the LeanDY SimpleAuth example, plus an explicit key-setup step. DYLean has no global names, so the pre-shared key has to come from somewhere:</p>
<div class="tablewrap"><table><tr><th>Step</th><th>DYLean function</th><th>Action</th><th>Output</th></tr>
<tr><td>Setup</td><td><code>SharedKey.generate A B</code></td><td>Generate a fresh key SK(A,B); store one copy for A and one for B</td><td>two key states</td></tr>
<tr><td>Initiator A</td><td><code>Initiator.start A B</code></td><td>Generate Na; log <code>Start A B Na</code>; remember the run</td><td>A → B: (A, B, Na)</td></tr>
<tr><td>Responder B</td><td><code>Responder.respond A B</code></td><td>Check identities; encrypt a response</td><td>B → A: Enc((Na, A), SK(A,B))</td></tr>
<tr><td>Initiator A</td><td><code>Initiator.finish A</code></td><td>Decrypt; check against the saved run</td><td>logs <code>Done A B Na</code></td></tr></table></div>
<p>As in LeanDY, everything is symbolic: Na is a symbolic random value, and encryption builds an idealized term. The example states its security property twice, and proves each version on its own. The first version is LeanDY's statement word for word:</p>
"""
    + '<div class="pair">'
    + fig_find(LDY, "abbrev authentication", 8)
    + fig(THM, 46, 65, "public")
    + "</div>\n"
    + """<p>Read it literally. For every trace the attacker can produce (<code>tr.Reachable reachability</code>), if <code>Done a b na</code> is in the trace, then so is <code>Start a b na</code>. The two proofs have the same shape:</p>
<ul><li>LeanDY's <code>valid_trace_mem</code> and DYLean's <code>EventLogged_imp_EventInv</code> both retrieve the invariant that the <code>done</code> event had to satisfy when it was logged.</li>
<li>That invariant contains the matching start event, and <code>grind</code> finishes.</li>
<li>The DYLean proof has one extra first step, <code>apply_Reachable_implies_Invariant</code>. It is there because of the one difference that remains: <strong>which traces</strong> the theorem talks about. LeanDY assumes <code>Crypto.valid_trace Γ tr</code>, a trace that already satisfies the invariant. DYLean quantifies over <em>reachable</em> traces: those produced by the protocol functions and the network, with arguments chosen by the attacker. The step from “reachable” to “satisfies the invariant” is a library theorem (section 15). In LeanDY it was left to the user.</li></ul>
<p>The second version adds the order: <code>Start</code> was logged in the part of the trace <em>before</em> <code>Done</code>.</p>
"""
    + fig(THM, 73, 103, "/--")
    + """<h3>Why two versions</h3>
<p>Each framework hands you the event's invariant on a different trace, and each theorem states what naturally comes out:</p>
"""
    + fig_find(LDYLIB, "lemma valid_trace_mem", 1, "LeanDY library excerpt")
    + fig("dylean:DY/Actions/ProtocolEvent.lean", 161, 172, "public", "DYLean library excerpt")
    + """<ul><li><strong>LeanDY.</strong> <code>valid_trace_mem</code> returns the event's validity on the <em>whole</em> trace <code>tr</code>. Its proof lifts the validity there by monotonicity, starting from the moment the event was logged. At that step the position is forgotten, so “start is somewhere in <code>tr</code>” is what you get.</li>
<li><strong>DYLean.</strong> <code>EventLoggedAt_imp_EventInv</code> returns the invariant on <code>tr.prefix i</code>, the trace just before the event was logged. The order is still there, so “Start is in the prefix” is what you get. DYLean's own examples state their properties this way, e.g. SignedDH's <code>client_auth</code>.</li></ul>
<p>Both frameworks check every event against the history before it, so LeanDY's invariant contains the order information too: LeanDY's theorem simply doesn't state it. The ordered version is strictly stronger. It rules out a <code>Start</code> that appears only after <code>Done</code>, which the membership version allows on paper. The membership version would follow from it in a few lines, but here it is proved directly, as in LeanDY.</p>
<p><strong>Both are the same modest correspondence property.</strong> Neither says that B ran, that B produced the ciphertext, that a completion is unique, or that the protocol ever completes. As in LeanDY, there is no responder event from which such a statement could be built.</p>
"""
    + note(
        "Two facts in this port were <em>checked by compilation</em>, not just by reading the source. (1) The session-state invariant alone supplies the matching <code>Start</code>: a diagnostic variant of <code>Initiator.finish</code> that never receives or decrypts anything still passes its proof (section 14). (2) If B's key copy is compromised, the attacker can make A log <code>Done</code> although <code>Responder.respond</code> is never called, and that trace is proven reachable (section 16). Both theorems still hold in both cases."
    )
    + task(
        "Write your target property first. Decide whether you want local start-before-finish, peer participation, agreement on data, injective authentication or secrecy, and under which compromise conditions. In DYLean the compromise exceptions appear explicitly in the theorem statement (see SignedDH's <code>client_auth</code>), so decide which compromises your theorem tolerates."
    )
)

# ---------------------------------------------------------------- 1
S["setup"] = (
    """<p>This folder holds two independent Lake projects, one per framework, each with its own toolchain and its framework as a pinned git dependency:</p>
<div class="tablewrap"><table><tr><th>Project</th><th>Toolchain</th><th>Depends on</th><th>Modules</th></tr>
<tr><td><code>dylean-examples/</code></td><td><code>leanprover/lean4:v4.33.0</code></td><td>DYLean <code>d58f33b</code> (no further dependencies; the Comparse parsing library is part of DYLean)</td><td><code>DYLeanExamples.SimpleAuth.*</code></td></tr>
<tr><td><code>leandy-examples/</code></td><td><code>leanprover/lean4:v4.24.0-rc1</code></td><td>LeanDY <code>e0705986</code>, and through it Mathlib</td><td><code>LeanDYExamples.SimpleAuth</code>, <code>LeanDYExamples.SimpleAuthDemo</code></td></tr></table></div>
<p>Both are separate from the SecureMessaging project at the repository root, which uses Lean v4.33.1 and VCVio. The root <code>lakefile.toml</code> does not mention them, so the root build and CI do not compile them. Module names carry a prefix because both frameworks ship example libraries of their own. LeanDY's even contains an older <code>Protocols.SimpleAuth</code>.</p>
<pre><code>cd symbolicTools/dylean-examples
lake build                     # the DYLean library and the SimpleAuth port

cd symbolicTools/leandy-examples
lake exe cache get             # download prebuilt Mathlib (once)
lake build
lake env lean --run LeanDYExamples/SimpleAuthDemo.lean   # LeanDY's executable debug run</code></pre>
<p>Every DYLean example has the same six-part layout, so learning it once pays off for <a href=\"""" + DY_TREE + """Examples/SignedDH">SignedDH</a>, <a href=\"""" + DY_TREE + """Examples/Ratchet">Ratchet</a> and the others in the DYLean repository:</p>
<div class="tablewrap"><table><tr><th>File</th><th>What you write there</th><th>LeanDY counterpart</th></tr>
<tr><td><a href="dylean-examples/DYLeanExamples/SimpleAuth/SymEnc.lean">SymEnc.lean</a></td><td>A new primitive: symmetric encryption (only needed because DYLean lacks it)</td><td>Built into <code>BytesEq</code> (<code>symenc</code>, <code>symdec</code>, normalizer γ)</td></tr>
<tr><td><a href="dylean-examples/DYLeanExamples/SimpleAuth/Specification.lean">Specification.lean</a></td><td>Primitive selection, messages, states, events, wire formats, protocol code, reachability</td><td><code>Nonce</code>, <code>State</code>, <code>Event</code>, <code>derive_parsable</code>, the three exchanges</td></tr>
<tr><td><a href="dylean-examples/DYLeanExamples/SimpleAuth/SanityChecks.lean">SanityChecks.lean</a></td><td>Executable runs and reachability proofs of honest and attack traces</td><td><a href="leandy-examples/LeanDYExamples/SimpleAuthDemo.lean">SimpleAuthDemo.lean</a></td></tr>
<tr><td><a href="dylean-examples/DYLeanExamples/SimpleAuth/Proof.lean">Proof.lean</a></td><td>Labels, usages, crypto predicate, state and event invariants, one Hoare triple per step</td><td><code>Γ</code>, <code>CryptoPreds</code>, <code>HasValid</code>, <code>event_preds</code>, <code>valid_exchange</code> proofs</td></tr>
<tr><td><a href="dylean-examples/DYLeanExamples/SimpleAuth/Instance.lean">Instance.lean</a></td><td>The concrete bytes, trace and invariant, assembled with <code>#combine</code></td><td>None: fixed by the library</td></tr>
<tr><td><a href="dylean-examples/DYLeanExamples/SimpleAuth/SecurityTheorems.lean">SecurityTheorems.lean</a></td><td>The security theorems: LeanDY's statement word for word, and an ordered version</td><td><code>authentication</code>, <code>protocol_authentication</code></td></tr></table></div>
<div class="tablewrap"><table><tr><th>You write</th><th>The library provides</th></tr>
<tr><td>Which equational theories you use (and new ones if needed)</td><td>“À la carte” symbolic bytes; each theory brings its constructors, attacker rules and invariants</td></tr>
<tr><td>Messages, states, events and their Comparse formats</td><td>Parsing and serialization with <code>parse (serialize x) = some x</code></td></tr>
<tr><td>Protocol steps as <code>Traceful</code> programs, and the list of functions the attacker may call</td><td>The trace monad, actions (random, network, events, states, compromise), the reachability relation</td></tr>
<tr><td>Labels, usages, crypto predicates, state and event invariants</td><td>The trace invariant built from them, and the proof that the attacker only learns publishable bytes</td></tr>
<tr><td>One Hoare triple per protocol step (mostly with the <code>step</code> tactic)</td><td>Hoare triples for every action, the <code>step</code> tactic, induction over reachable traces</td></tr></table></div>
"""
    + '<aside class="verified"><strong>Verified for this tutorial</strong><p>On 16 October 2026 both projects in this folder were built from a clean state: the DYLean project with Lean 4.33.0, library included, and the LeanDY project with Lean 4.24.0-rc1, the LeanDY library included, on prebuilt Mathlib. Neither produced errors, warnings or <code>sorry</code>. Every code block captioned as an excerpt was extracted by line range, by <code>tools/generate_dylean_tutorial.py</code>, when this page was generated: from this folder, or from the pinned library checkouts. Other blocks are labelled for what they are.</p></aside>\n'
    + task(
        "Start a new protocol by copying the six-file skeleton of the closest example. Most of <code>HasExecBytes</code>, <code>HasExecTrace</code>, <code>HasProofTrace</code>, <code>HasBytesInvariants</code>, <code>HasTraceInvariant</code> and <code>Instance.lean</code> is boilerplate (the upstream code says so), but each list must match exactly the components you use."
    )
)

# ---------------------------------------------------------------- 2
S["bytes"] = (
    """<p>LeanDY gives every protocol the same symbolic algebra <code>𝐵 α η</code>: a quotient of raw terms by a normalizer, with a distinguished <code>fail</code> value. DYLean builds <code>Bytes</code> à la carte. Each equational theory contributes one or more constructors, a length function, attacker rules and invariants. A protocol states which theories it needs:</p>
"""
    + fig(SPEC, 61, 76, "class HasExecBytes")
    + """<p>Each <code>BytesFunctor.Has X.SubF</code> means “bytes can be built with the constructors of theory X”. Each <code>AttackerKnowledge.Has</code> means “the attacker can use X's operations”. SimpleAuth needs random values (nonces and keys), literals and concatenation (Comparse serializes messages with them), and symmetric encryption.</p>
<h3>The missing primitive</h3>
<p>DYLean's standard library (<code>DY/EquationalTheory/</code>) has concatenation, literals, hashing, signatures, Diffie-Hellman and two KDFs, but no symmetric encryption. The port therefore adds it in the example folder, the same way <code>Examples/SignedDHKEM/KEM.lean</code> adds a KEM. The library itself is untouched.</p>
"""
    + fig(SYM, 35, 37, "class CanSymEnc")
    + fig(SYM, 106, 144, "/--")
    + """<p><code>symEnc</code> builds the term <code>Enc { key, msg }</code>. <code>symDec</code> is the destructor: it looks inside a ciphertext (<code>view?</code>) and returns the plaintext only if the key matches. The equation <code>symDec k (symEnc k m) = some m</code> and its converse are proved directly, by <code>grind</code>.</p>
<p>There is no <code>fail</code> byte: decryption returns <code>Err Bytes</code> (an <code>Option</code>), and failure is handled by the program, not stored in a term. This is why the LeanDY obligations of the form <code>na ≠ fail</code> have no counterpart here.</p>
<h3>Attacker capabilities come with the primitive</h3>
"""
    + fig(SYM, 158, 175, "def symEnc.attackerKnowledge")
    + """<p>In LeanDY the attacker's deduction rules are one fixed relation. In DYLean each theory contributes rules: here, “encrypt anything you know with any key you know” and “decrypt anything you know with any key you know”. Base knowledge (what the attacker reads from the trace) comes from the trace entries: network messages are known, random values are not.</p>
<details><summary>What else a new primitive must provide</summary><p><code>SymEnc.lean</code> mirrors <code>DY/EquationalTheory/Sign.lean</code> section by section: (1) constructors and destructor, (2) attacker rules, (3) the bytes invariant of ciphertexts (section 8), (4) Hoare triples so that the <code>step</code> tactic can execute <code>symEnc</code> and <code>symDec</code> (section 11), and (5) <code>SubAttackerKnowledgeTheorem</code> instances proving that each attacker rule turns publishable inputs into publishable outputs. Obligation (5) is what makes a primitive's invariant sound against the attacker: an invariant that is too generous to the attacker fails here.</p><p>Encryption is deterministic (no encryption randomness), like LeanDY's <code>symenc</code>. The ciphertext length is the plaintext length plus 16 bytes, but nothing in SimpleAuth depends on it.</p></details>
"""
    + task(
        "Look in <code>DY/EquationalTheory/</code> and in the examples before writing a primitive. If you must write one, copy the closest theory: <code>Hash.lean</code> for a single constructor without a destructor, <code>Sign.lean</code> or this <code>SymEnc.lean</code> for a keyed primitive with a destructor. Expect most of your effort to go into the invariant and the attacker-knowledge theorem, not the constructors."
    )
)

# ---------------------------------------------------------------- 3
S["data"] = (
    fig(SPEC, 100, 144, "/-- First message")
    + """<p>Each message, plaintext and state is an ordinary Lean structure; each event is a constructor of one inductive type.</p>
<div class="tablewrap"><table><tr><th>DYLean</th><th>LeanDY</th><th>Difference</th></tr>
<tr><td><code>InitMessage {a, b, na}</code></td><td><code>[!(); a, b, na]</code></td><td>Named fields instead of nested tuples and projection paths</td></tr>
<tr><td><code>ResponsePayload {na, a}</code></td><td><code>[!(); na, a']</code> / parsed as a pair</td><td>One structure is shared by the encrypting and the decrypting side</td></tr>
<tr><td><code>SharedKeyState {initiator, responder, key}</code></td><td>none: <code>sk a b</code> is computed from the names</td><td>Keys are values that must be stored and loaded</td></tr>
<tr><td><code>InitiatorState {b, na}</code></td><td><code>State.Init a b na</code></td><td>The owner <code>a</code> is implicit: every local state is tagged with its participant. There is no <code>Null</code> state.</td></tr>
<tr><td><code>SimpleAuthEvent.Start / Done</code></td><td><code>Event.start / done</code>: a string tag plus symbolic content</td><td>Typed constructors instead of string tags</td></tr></table></div>
<h3>Wire formats</h3>
"""
    + fig(SPEC, 162, 176, "instance: ParseableSerializeable InitMessage")
    + """<p>Comparse formats are built from combinators. <code>.slowString</code> and <code>.slowBytes</code> are length-prefixed, so another field can follow them. <code>.string</code> and <code>.bytes</code> consume the rest of the input and can only come last. The library proves <code>parse (serialize x) = some x</code> and that serialization is injective for every such format.</p>
<p>The <code>IsWellFormed_eq</code> lemma is the one thing you prove per format. A predicate (invariant, publishability, attacker knowledge, …) holds on the serialized message exactly when it holds on its <code>Bytes</code> fields. Participant names are serialized as literals, which are always public, so they drop out. The <code>grind_pattern</code> lines let automation use the lemma.</p>
"""
    + note(
        "The LeanDY workshop found, by inspection, a field-order mismatch between what LeanDY's responder encrypted (nonce, identity) and what <code>initiator_check</code> expected (identity, nonce). The LeanDY example in this folder contains the fix (commit <code>dd9753c</code>, LeanDY pull request #2: it now compares <code>(sna, expectedPrincipal)</code>). In this port both sides serialize and parse the <em>same</em> structure <code>ResponsePayload</code>, so they agree on field order by construction. They could still disagree if you accidentally used two different structures. The executable sanity check in section 6 would then fail."
    )
    + task(
        "Give each message, plaintext and state its own structure, even when it has a single field. Put length-prefixed formats first and at most one extensible format last. Copy the <code>IsWellFormed_eq</code> lemma and its two <code>grind_pattern</code> lines for each format. The proofs depend on them."
    )
)

# ---------------------------------------------------------------- 4
S["code"] = (
    fig(SPEC, 262, 286, "/--")
    + fig(SPEC, 288, 318, "/--")
    + """<p>A DYLean protocol step is a program in the <code>Traceful</code> monad. Its definition is a function from the current trace to an optional result and a longer trace (<code>Traceful a := ExecTrace → Option a × {trOut // trIn ≤ trOut}</code>). The trace only ever grows: it is append-only. The actions used here are:</p>
<ul><li><code>Random.genRand n</code> appends a random-generation entry and returns a fresh symbolic value. Freshness is by construction: the value is identified by its position in the trace. LeanDY's initiator instead received its nonce <code>n</code> as an argument and did not guarantee freshness.</li>
<li><code>ProtocolEvent.logEvent ev</code> appends an event.</li>
<li><code>PersistentLocalState.storeLocalState p st</code> appends a state owned by <code>p</code> and returns its <em>handle</em> (its position). <code>getLocalState p h</code> reads the state at handle <code>h</code> and fails unless it belongs to <code>p</code>.</li>
<li><code>Network.sendMessage m</code> appends a message and returns its handle. <code>receiveMessage h</code> reads the message at handle <code>h</code>.</li>
<li><code>parse</code> (from <code>Err</code>, lifted into <code>Traceful</code>) and <code>guard c</code> fail the step when parsing fails or <code>c</code> is false.</li></ul>
<p>Compare with LeanDY, where an exchange is a pure function <code>(time, input, state) ↦ Atom {message, state, events, post_events}</code> and the generic <code>transition</code> performs receive, load, log, store and send in a fixed order. In DYLean you write that order yourself. The constraint is the same as LeanDY's “events before state”: <code>Initiator.start</code> logs <code>Start</code> <em>before</em> storing the state, because the state's invariant mentions that event (section 9).</p>
<p>The handles play the role of LeanDY's <code>ChoiceFn</code>. Whoever calls <code>Responder.respond a b keyHandle msgHandle</code> chooses which message and which key state it reads. The caller is the attacker (section 5), so it can deliver any message to any session.</p>
<details><summary>Failure is an abort, not a default value</summary><p>In LeanDY a failed check returns the default <code>Atom</code>: the transition still sends <code>fail</code> and stores the <code>Null</code> state. In DYLean a failed <code>guard</code>, <code>parse</code> or <code>symDec</code> stops the program. Entries appended before the failure stay in the trace and nothing after it happens. There is no <code>Null</code> state and no <code>fail</code> message.</p></details>
"""
    + task(
        "Write each role as straight-line code: load states and keys, receive and parse, check with <code>guard</code>, compute, log the events that later states or messages will need, store, send. Return the handles that the next step will need. Keep secrets in states and do not pass them as function arguments: arguments are chosen by the attacker."
    )
)

# ---------------------------------------------------------------- 5
S["reach"] = (
    fig(SPEC, 365, 397, "/-")
    + fig("dylean:DY/Trace/Reachability.lean", 77, 85, "inductive Trace.Reachable", "DYLean library excerpt")
    + """<p>A trace is <em>reachable</em> if it is obtained from the empty trace by repeatedly calling one of the combined functions, with any input. <code>#combine into ReachabilityConfig</code> builds <code>reachability</code> from the list. <code>Network</code> contributes one capability with a precondition: send any bytes the attacker can derive. So the attacker</p>
<ul><li>schedules every protocol function with arguments of its choice (participant names, handles), any number of times, in any order;</li>
<li>injects any message it can derive from what it has seen;</li>
<li>compromises any stored state: <code>PersistentLocalState.compromise</code> logs a compromise event and then publishes the serialized state on the network.</li></ul>
<p>Anything not in the list never happens. The attacker cannot log protocol events, cannot write into a participant's state, and cannot generate random values (it uses literals instead). It can call <code>SharedKey.generate A B</code> several times, so a pair may have several keys. In LeanDY, <code>Sk a b</code> is a single name.</p>
<p>This is the part that the LeanDY workshop listed as missing from LeanDY's SimpleAuth (“the SimpleAuth file itself does not supply a complete runnable network scheduler or an end-to-end reachable-trace theorem”). In DYLean it is part of every protocol specification.</p>
"""
    + task(
        "List every function the attacker may trigger, including state compromise and any key-compromise functions. Leaving a function out weakens the attacker, so your theorem looks stronger than it really is. Give secrets to participants through states created by a setup function that is itself in the list."
    )
)

# ---------------------------------------------------------------- 6
S["sanity"] = (
    """<p>A theorem of the form “if <code>Done</code> then <code>Start</code>” is vacuously true if <code>Done</code> can never be logged. DYLean specifications are executable, so you can test them before proving anything. This is what each example's <code>SanityChecks.lean</code> does.</p>
"""
    + fig(SAN, 38, 54, "/-")
    + """<p><code>#guard</code> runs the program at compile time on the empty trace. Symbolic bytes are concrete data with decidable equality, so every <code>guard</code>, <code>parse</code> and decryption is actually evaluated. The honest run returns <code>some ()</code>: all checks pass and the field orders agree. The next theorem proves that this trace is reachable and contains <code>Start</code> at position 4 and <code>Done</code> at position 8 with the same nonce:</p>
"""
    + fig(SAN, 88, 121, "/--")
    + """<p>Reachability is proved call by call with <code>PreservesReachabilityFrom_bind</code>; see <code>honestRun_PreservesReachability</code> in the same file. The event facts are checked by evaluation (<code>native_decide</code>). That adds a compiler-trust axiom, and <code>#print axioms</code> lists it.</p>
<h3>A rejected forgery</h3>
"""
    + fig(SAN, 123, 144, "/-")
    + """<p>Without the shared key, an attacker who encrypts the expected plaintext under a key it made up is rejected: A's decryption fails and the run returns <code>none</code>. This is one test, not a proof of responder authentication. Section 16 shows what happens once the key leaks.</p>
"""
    + note(
        "The LeanDY workshop could not run Lean, so its honest-run concern was an inspection finding. LeanDY now has <code>SimpleAuthDemo.lean</code>, an executable debug run. In DYLean, such checks sit next to the proofs in every example, and the attack scenarios come with reachability proofs, so they are proven to be traces the theorem talks about."
    )
    + task(
        "Before writing invariants, add an honest run that reaches your final event, prove it reachable, and add a few runs that must fail (wrong key, wrong nonce, wrong identity). If an honest run fails, fix the specification first: proofs about a broken specification are proofs about the wrong protocol."
    )
)

# ---------------------------------------------------------------- 7
S["labels"] = (
    fig(PROOF, 55, 79, "/--")
    + fig("dylean:DY/Label/Basic.lean", 38, 43, "@[expose]", "DYLean library excerpt")
    + fig("dylean:DY/Bytes/Invariants.lean", 508, 524, "@[expose, grind]", "DYLean library excerpt")
    + """<p>A DYLean <code>Label</code> is a monotone predicate <code>isCorrupt</code> on traces: once corrupt, always corrupt. <code>Label.pub</code> is always corrupt and <code>Label.secret</code> never is. <code>l1.canFlow l2</code> means “whenever <code>l2</code> becomes corrupt, so does <code>l1</code>”, i.e. data labelled <code>l1</code> may be given to whoever can read <code>l2</code>. Bytes are <code>Publishable</code> when they satisfy their invariant and their label can flow to <code>pub</code>, that is, when their label is already corrupt.</p>
<p>Labels are not looked up in a global environment. Each random value receives its label and usage when it is generated, as a <em>ghost</em> argument of <code>genRand</code>'s specification. These ghost values exist only in the proof trace, never at runtime:</p>
"""
    + fig("dylean:DY/Actions/Random.lean", 217, 237, "public", "DYLean library excerpt")
    + """<ul><li>The nonce Na is generated with label <code>Label.pub</code>, matching LeanDY's <code>𝓟ub</code> for <code>Nonce.Nat</code>.</li>
<li>SK(A,B) is generated with <code>sharedKeyLabel A B key</code>: it becomes corrupt as soon as A's or B's copy of that key is compromised. Like <code>Sk a b</code>, it is indexed by an ordered pair.</li>
<li>Its usage <code>sharedKeyUsage</code> (type <code>"SymKey"</code>) says what the key is for. The encryption invariant checks the usage (section 8). <code>HasUsage</code> is deliberately weak once the key is corrupt: at that point the attacker can use it for anything.</li></ul>
"""
    + '<div class="pair">'
    + fig_find(LDY, "def Γ", 5)
    + fig(PROOF, 63, 67, "def sharedKeyLabel")
    + "</div>\n"
    + note(
        "LeanDY's SimpleAuth labels <code>Sk</code> as <code>𝓢ec</code> forever and has no compromise. The literal translation is <code>Label.secret</code>, but a compromisable state may only hold data that its compromise label can know (section 9), and a secret-forever key cannot satisfy that. To mirror LeanDY exactly you would use <code>Label.secret</code> together with non-compromisable states (<code>PersistentLocalState.State</code> instead of <code>CompromisableState</code>). The port follows DYLean's convention instead: everything stored can be compromised. The authentication theorem is unaffected either way, since it never uses the key."
    )
    + task(
        "For every secret, decide at generation time who may learn it and under which corruption, and encode that as its label. Choose distinct usages for distinct purposes, so that a key generated for one purpose cannot satisfy another purpose's predicate."
    )
)

# ---------------------------------------------------------------- 8
S["crypto"] = (
    fig(SYM, 260, 303, "/--")
    + """<p>This is the invariant every ciphertext in a valid trace satisfies, in the style of DY*'s AEAD invariant. The ciphertext's label is <code>pub</code>: publishing it is fine, provided its invariant holds. The invariant says the ciphertext was produced either</p>
<ul><li><strong>honestly</strong>: the key has a usage of type <code>"SymKey"</code>, the protocol's predicate holds for that usage, and the plaintext is no more secret than the key, so publishing the ciphertext cannot leak the plaintext; or</li>
<li><strong>by the attacker</strong>: both the key and the plaintext are public.</li></ul>
<p>The protocol-specific part is the predicate:</p>
"""
    + fig(PROOF, 81, 106, "/--")
    + '<div class="pair">'
    + fig_find(LDY, "instance instCrypt", 2)
    + fig(PROOF, 89, 97, "instance SimpleAuthSymEncPred")
    + "</div>\n"
    + """<p>LeanDY requires the plaintext of an honest ciphertext to be a pair. The port requires it to parse as a <code>ResponsePayload</code>, and the key usage to be SimpleAuth's. As in LeanDY, the predicate says nothing about who encrypted or when. This is why decrypting it cannot tell A anything about B.</p>
<div class="tablewrap"><table><tr><th>Question</th><th>LeanDY</th><th>DYLean</th></tr>
<tr><td>Does decryption compute?</td><td>Constructors, normalizer γ, key matching</td><td><code>symDec</code>: <code>view?</code> plus key equality</td></tr>
<tr><td>May the ciphertext be public?</td><td>Label typing, <code>is_public</code></td><td>The label is <code>pub</code>, so it is publishable exactly when its invariant holds</td></tr>
<tr><td>Does it satisfy the protocol's crypto invariant?</td><td><code>valid_bytes</code> with <code>CryptoPreds</code></td><td><code>Enc.invariants</code> with <code>SymEncPred</code></td></tr></table></div>
<p>The proof-side counterpart is the elimination rule. Successful decryption with a key of known usage yields an invariant plaintext, no more secret than the key, and either the predicate or a corrupt key:</p>
"""
    + fig(SYM, 367, 391, "/--")
    + """<p>An authentication proof would use the left disjunct. Neither SimpleAuth theorem needs it.</p>
"""
    + task(
        "Put into the predicate the provenance your theorem needs, for example “an event <code>Respond a b na</code> has been logged”, and keep the attacker alternative (key public) intact. Prove that the predicate is monotone (<code>SymEncPredProof</code>). Here this is trivial because the predicate does not mention the trace."
    )
)

# ---------------------------------------------------------------- 9
S["state"] = (
    fig(PROOF, 134, 172, "/--")
    + """<p>A state invariant <code>invariant me st tr</code> says what holds of state <code>st</code> owned by <code>me</code>. Storing a state requires it, loading a state provides it. <code>invariant_later</code> is monotonicity: the invariant survives trace extension. It is LeanDY's <code>valid_monotone</code>. Both are about one fixed state value as the trace grows.</p>
<p><strong>The initiator's state</strong> carries exactly LeanDY's <code>HasValid</code> content: the nonce is valid and public, and <code>Start me b na</code> has been logged. This is the fact the final step will need.</p>
<p><strong>The key state</strong> carries the key's label and usage, so that whoever loads it can encrypt or decrypt with known guarantees. It also records that the owner is the initiator or the responder. That conjunct is needed for the extra obligation that compromisable states bring:</p>
<ul><li><code>invariant_implies_KnowableBy</code>: everything in the state must be knowable by the state's compromise label, which becomes corrupt when that particular state is compromised. For a key copy owned by <code>me</code>, compromising it makes <code>sharedKeyLabel initiator responder key</code> corrupt, which requires <code>me</code> to be one of the two parties.</li>
<li>For <code>InitiatorState</code> it holds trivially: the nonce is public.</li></ul>
<details><summary>What InitiatorState does not say</summary><p>As in LeanDY, it does not mention the key, does not record that the nonce was fresh (although it is), and does not assert any responder participation. Nothing prevents <code>Initiator.finish</code> from being called twice with the same state handle, so <code>Done</code> can be logged twice for one <code>Start</code>. The theorem does not claim injectivity.</p></details>
"""
    + task(
        "For every state, record the evidence a later step needs: labels and usages of stored keys, past events, relations between fields. For compromisable states, check that everything stored is knowable by the state's compromise label. If a value must stay secret even when the state leaks, it does not belong in a compromisable state."
    )
)

# ---------------------------------------------------------------- 10
S["events"] = (
    fig(PROOF, 174, 187, "/--")
    + fig("dylean:DY/Actions/ProtocolEvent.lean", 210, 219, "theorem logEvent.spec", "DYLean library excerpt")
    + """<p>An event invariant is evaluated on the trace <em>just before</em> the event is logged. That is the precondition of <code>logEvent</code>, and afterwards the event is known to be in the trace. <code>Start</code> can be logged at any time. <code>Done a b na</code> requires an earlier <code>Start a b na</code>, which is exactly LeanDY's <code>event_preds</code> for <code>"done"</code>.</p>
<p>Two small differences are worth noticing. LeanDY's <code>event_preds</code> matches on a string tag and ends with a wildcard <code>| _ => true</code>, so a newly added tag is unconstrained by default. DYLean's match is exhaustive over a typed event, so adding a constructor forces you to write its invariant. And because there is no <code>fail</code>, there is no <code>na ≠ fail</code> conjunct.</p>
"""
    + note(
        "For responder authentication, add a responder event and connect the protected response to it through the encryption predicate. Renaming events or strengthening the theorem statement cannot supply evidence that is absent from the invariant. Section 18 sketches the change."
    )
)

# ---------------------------------------------------------------- 11
S["contract"] = (
    fig("dylean:DY/Trace/Manipulation.lean", 33, 52, "instance [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]: WP Traceful", "DYLean library excerpt")
    + """<p>Proofs work on a <em>proof trace</em>: the execution trace plus ghost information, such as the label and usage of each random value. <code>erase</code> turns it back into an execution trace. The trace invariant is the conjunction of per-entry invariants:</p>
<ul><li>every network message is <code>Publishable</code> (see the excerpt below);</li>
<li>every stored state satisfies its state invariant;</li>
<li>every event satisfies its event invariant on the prefix before it;</li>
<li>random entries record their ghost label and usage. Bytes invariants such as the ciphertext invariant are checked wherever bytes appear: in messages, states and events.</li></ul>
"""
    + fig("dylean:DY/Actions/Network.lean", 100, 105, "instance", "DYLean library excerpt")
    + """<p><code>hoareTriple f pre post</code> says: from any proof trace that satisfies the invariant and <code>pre</code>, running <code>f</code> on its erasure gives an execution trace that is the erasure of a longer proof trace that satisfies the invariant and <code>post</code>. Every SimpleAuth step is proved with <code>pre</code> and <code>post</code> both <code>True</code>: the content is “the invariant is preserved”. That is LeanDY's <code>valid_exchange</code>.</p>
<p>In LeanDY the obligations are grouped by output field (<code>valid_public_bytes</code>, <code>valid_state</code>, <code>valid_events</code>, <code>valid_post_events</code>, <code>valid_restrictions</code>). In DYLean they arise one per instruction, in program order, as the preconditions of the library's Hoare triples:</p>
<div class="tablewrap"><table><tr><th>Instruction</th><th>You prove (precondition)</th><th>You get (postcondition)</th></tr>
<tr><td><code>genRand n</code> with ghost ⟨label, usage⟩</td><td>nothing</td><td>result is invariant, has that label and that usage</td></tr>
<tr><td><code>logEvent ev</code></td><td>the event invariant of <code>ev</code></td><td><code>ev</code> is logged</td></tr>
<tr><td><code>storeLocalState p st</code></td><td>the state invariant of <code>(p, st)</code></td><td>nothing</td></tr>
<tr><td><code>getLocalState p h</code></td><td>nothing</td><td>the state invariant of the loaded state</td></tr>
<tr><td><code>sendMessage m</code></td><td><code>m.Publishable</code></td><td>nothing</td></tr>
<tr><td><code>receiveMessage h</code></td><td>nothing</td><td>the message is <code>Publishable</code> (it may come from the attacker)</td></tr>
<tr><td><code>parse b</code></td><td>nothing</td><td><code>FormatRel b x</code>, i.e. <code>b = serialize x</code></td></tr>
<tr><td><code>guard c</code></td><td>nothing</td><td><code>c</code></td></tr>
<tr><td><code>symEnc k m</code> with ghost usage</td><td>key/plaintext invariants, key usage, honest case or attacker case (section 8)</td><td>the ciphertext is <code>Publishable</code></td></tr>
<tr><td><code>symDec k c</code> with ghost usage</td><td><code>c</code> is invariant and <code>k</code> has the usage</td><td>plaintext is invariant, no more secret than <code>k</code>, predicate or corrupt key</td></tr></table></div>
<h3>The <code>step</code> tactic</h3>
<p><code>step</code> symbolically executes the next instruction. It finds the instruction's Hoare triple by typeclass search, tries to discharge the precondition with <code>grind</code>, introduces the postcondition, and moves on. <code>step by tac</code> uses your tactic for the precondition. <code>step with ⟨ g ⟩</code> supplies a ghost argument (a label and usage for <code>genRand</code>, a key usage for <code>symEnc</code>/<code>symDec</code>).</p>
<p>After each instruction the trace is longer. <code>step</code> <em>monotonizes</em> the context: it transports every hypothesis about the old trace to the new one, using lemmas tagged <code>grind_later</code>. When it cannot, it stops with “cannot monotonize”. Section 14 shows a case where that happens.</p>
"""
    + task(
        "Before running the tactic, write down for each instruction of your step what its precondition needs, and where that fact comes from (an earlier postcondition, a loaded state invariant, a parsed message). If a stored state needs an event, log the event first. If a message needs a property, establish it before <code>sendMessage</code>."
    )
)

# ---------------------------------------------------------------- 12
S["proof-start"] = (
    fig(PROOF, 242, 283, "@[instance]")
    + """<p><strong>Key setup.</strong> The ghost argument of <code>genRand</code> fixes the key's label and usage. Storing each copy requires <code>SharedKeyStateInv</code>. After unfolding, <code>grind</code> sees that the owner is one of the two parties and that label and usage are the ones just generated.</p>
<p><strong>First message.</strong> The nonce gets <code>Label.pub</code>. Logging <code>Start</code> needs nothing: its invariant is <code>True</code>. Storing the state needs a publishable nonce, which comes from the <code>genRand</code> postcondition, and <code>Start a b na</code> logged, which comes from the <code>logEvent</code> postcondition, transported by monotonization. Sending needs the serialized message to be publishable. By <code>InitMessage.IsWellFormed_eq</code> that is the nonce's publishability, which <code>grind</code> finds without help.</p>
<p>Compare with LeanDY's <code>valid_initiator</code>, which chooses witnesses for <code>event_preds</code> and calls <code>prove_is_public</code>. The same facts appear here in program order instead of grouped by output field.</p>
<p>The <code>@[instance]</code> attribute makes each proven triple available to <code>step</code>, which is how the attacker scenarios and other protocols can reuse it.</p>
"""
    + task(
        "Proof scripts in DYLean usually have one <code>step</code> per instruction, plus a <code>by</code> block where a precondition needs unfolding (typically <code>simp only [PersistentLocalState.LocalStateInv.invariant]</code> then <code>grind</code>). If a <code>step</code> fails, read the precondition it printed. It tells you which instruction's contract you have not met."
    )
)

# ---------------------------------------------------------------- 13
S["proof-respond"] = (
    fig(PROOF, 285, 314, "@[instance]")
    + """<p>The interesting step is the encryption. Receiving gives a publishable message, parsing relates it to <code>msg</code>, and loading the key gives <code>SharedKeyStateInv</code>. The precondition of <code>symEnc</code> is then discharged in its honest case:</p>
<ul><li>the key has usage <code>sharedKeyUsage</code>, whose type is <code>"SymKey"</code> (from the key state);</li>
<li>the plaintext parses as a <code>ResponsePayload</code> (<code>parse (serialize x) = some x</code>), so <code>SimpleAuthSymEncPred</code> holds;</li>
<li>the plaintext is no more secret than the key, because it is public and <code>pub</code> flows to every label (<code>canFlowTrans</code>).</li></ul>
<p>The one manual line, <code>have: (serialize …).Publishable tr</code>, gives <code>grind</code> the publishability of the serialized plaintext. SignedDH's responder has the same line with the comment “TODO how to infer this automatically?”. Afterwards, sending is automatic: <code>symEnc</code>'s postcondition already says the ciphertext is publishable.</p>
<p>LeanDY's <code>valid_responder</code> is one <code>aesop_type_system</code> call, backed by the helper lemma <code>enc_pub</code> registered in the protocol rule set. Neither framework makes this obligation disappear. It is the place where the response is shown to be a legitimate ciphertext.</p>
"""
    + task(
        "When <code>grind</code> fails on a precondition, add the missing intermediate fact as a <code>have</code>. Common ones are the publishability of a serialized value, the unfolded invariant of a loaded state, and a label-flow step through <code>canFlowTrans</code>."
    )
)

# ---------------------------------------------------------------- 14
S["proof-finish"] = (
    fig(PROOF, 316, 345, "@[instance]")
    + """<p>The final step loads the session state (the <code>split</code> opens the pattern match <code>let ({ b, na }: InitiatorState) ← …</code>), loads the key, receives, decrypts, parses, checks and logs <code>Done</code>.</p>
<h3>A monotonization pitfall, and its fix</h3>
<p>Without the <code>simp only [PersistentLocalState.LocalStateInv.invariant] at *</code> line, the proof fails at the decryption step with:</p>
<pre><code>cannot monotonize (plaintext✝.label tr).canFlow (keySt✝.key.label tr) tr.erase.</code></pre>
<p><code>symDec</code>'s postcondition mentions <code>keySt.key.label tr</code>. To transport that fact to a longer trace, <code>step</code> needs <code>keySt.key.Invariant tr</code>, because labels are stable only for invariant bytes. That fact exists, but it is buried inside the folded hypothesis <code>LocalStateInv.invariant a keySt tr</code>. Unfolding the state invariants exposes it as its own hypothesis, and from then on monotonization works.</p>
<h3>Where <code>Done</code>'s obligation comes from</h3>
<p>The last <code>step</code> has to prove <code>Done</code>'s invariant, <code>Start a b na</code> logged. That fact comes from the <em>session state</em>, not from the decrypted message. This is exactly LeanDY's <code>valid_initiator_check</code>. To make the point concrete, this variant was compiled against the example:</p>
"""
    + block(
        """
        -- Diagnostic: an initiator that logs Done without receiving or decrypting anything.
        def Initiator.finishNoCheck [HasExecTrace] (a: Participant) (stHandle: Nat): Traceful Unit := do
          let ({ b, na }: InitiatorState) ← PersistentLocalState.getLocalState a stHandle
          ProtocolEvent.logEvent (SimpleAuthEvent.Done a b na)

        theorem Initiator.finishNoCheck.spec (a: Participant) (stHandle: Nat):
          HoareTriple (Initiator.finishNoCheck a stHandle) (fun _ => True) (fun _ _ => True)
        := by
          apply HoareTriple.mk
          unfold Initiator.finishNoCheck
          step
          split
          simp only [PersistentLocalState.LocalStateInv.invariant] at *
          step
          grind
        """,
        "Diagnostic experiment · compiled separately against DYLeanExamples.SimpleAuth.Proof (exit code 0); not part of the example",
    )
    + """<p>It passes. Adding this function to <code>reachability</code> would therefore break neither security theorem, which confirms that they do not depend on the ciphertext. The LeanDY workshop proposed the same experiment as a thought experiment.</p>
"""
    + task(
        "Audit your theorem by asking: would it still hold if I removed the check that I believe authenticates the peer? In DYLean you can answer by compiling a variant like the one above. If it still holds, either the check is redundant for this goal or the goal is weaker than intended."
    )
)

# ---------------------------------------------------------------- 15
S["theorem"] = (
    fig(PROOF, 357, 383, "/-")
    + """<p>Each <code>ReachableImpliesInvariant</code> instance packages one step's Hoare triple for the reachability configuration. <code>#combine into ReachabilityTheorem</code> assembles them, together with the library's instance for <code>Network</code> (the attacker sending what it knows). The library then proves, by induction on <code>Trace.Reachable</code>, that every reachable execution trace is the erasure of a proof trace satisfying the invariant.</p>
<p>The <code>Network</code> case is where the attacker-knowledge theorem is used: every byte string the attacker can derive is publishable. That theorem is assembled in <code>Instance.lean</code> from each theory's <code>SubAttackerKnowledgeTheorem</code>, including the two proved in <code>SymEnc.lean</code>. <code>Instance.lean</code> builds the concrete bytes, trace entries and invariants from exactly the components listed in the <code>Has…</code> classes:</p>
"""
    + fig(INST, 57, 82, "#combine +toplevel into BytesInvariants")
    + fig("dylean:DY/Trace/ReachabilityTheorem.lean", 54, 70, "public", "DYLean library excerpt")
    + fig("dylean:DY/Actions/ProtocolEvent.lean", 182, 192, "public", "DYLean library excerpt")
    + """<p>With these library lemmas, each security proof (section 0) is five tactic lines. <code>apply_Reachable_implies_Invariant</code> turns the statement about reachable traces into one about proof traces satisfying the invariant. <code>EventLogged_imp_EventInv</code> (for <code>initiator_auth_literal</code>) retrieves the invariant of the <code>Done</code> event on <em>some</em> earlier prefix of the trace. <code>EventLoggedAt_imp_EventInv</code> (section 0, for <code>initiator_auth</code>) retrieves it on the prefix before a given position. <code>simp</code> unfolds that invariant, and <code>grind</code> moves the <code>Start</code> event from the prefix to where the statement needs it. <code>#print axioms</code> shows only <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code> for both theorems.</p>
<p>The short final proof has the same reason as in LeanDY: the local proofs already arranged for the needed evidence to be in the invariant. What DYLean adds is the end-to-end statement. The LeanDY workshop's checklist for connecting local proofs to executions (initial configurations, every honest step, attacker injection and corruption, induction) is done here by the reachability configuration and the library.</p>
"""
)

# ---------------------------------------------------------------- 16
S["probe"] = (
    fig(SAN, 146, 177, "/-")
    + fig(SAN, 247, 265, "/--")
    + """<p>The attacker compromises B's copy of the key, reads it from the network, waits for A's first message and answers it itself. A decrypts, the checks pass, and A logs <code>Done</code>. <code>Responder.respond</code> is never called. The trace is proven reachable, so both theorems apply to it, and both hold: <code>Start</code> was logged at position 6, before <code>Done</code> at position 10.</p>
<p>Two lessons follow. First, the theorem constrains only A's own history. Second, a responder-authentication theorem in DYLean would have to say “B responded <em>or</em> SK(A,B) was compromised”. The attack shows the second disjunct cannot be dropped. With an uncompromised key, section 6's forged response is rejected, but only a theorem can say that <em>every</em> such attempt fails.</p>
"""
    + task(
        "Write at least one attack scenario per compromise disjunct of your theorem and prove it reachable. If you cannot build a scenario for a disjunct, it may be unnecessary. If a scenario violates the conclusion without using any disjunct, you have found an attack, or a bug in your specification."
    )
)

# ---------------------------------------------------------------- 17
S["map"] = """<p>A side-by-side summary of the two SimpleAuth developments.</p>
<div class="tablewrap"><table><tr><th>Concept</th><th>LeanDY SimpleAuth</th><th>DYLean SimpleAuth</th></tr>
<tr><td>Symbolic bytes</td><td>Fixed <code>BytesEq α η</code>: quotient by the normalizer γ, with a <code>fail</code> value</td><td>À-la-carte <code>Bytes</code> from chosen theories; no <code>fail</code>; destructors return <code>Option</code></td></tr>
<tr><td>Atomic names</td><td><code>Nonce</code>: <code>Nat n</code>, <code>Sk a b</code></td><td>Random values from <code>genRand</code> (fresh trace entries); literals for constants</td></tr>
<tr><td>Algorithm parameter</td><td><code>α = Unit</code></td><td>None in this example</td></tr>
<tr><td>Participants</td><td><code>ℙ</code>, embedded as <code>.princ</code> bytes</td><td><code>Participant = String</code>, serialized as literals</td></tr>
<tr><td>Symmetric encryption</td><td>Built in (<code>symenc</code>, <code>symdec</code>)</td><td>Added in <code>Examples/SimpleAuth/SymEnc.lean</code></td></tr>
<tr><td>Shared key</td><td><code>sk a b</code>, computed from names</td><td><code>SharedKey.generate</code>, stored in two states, loaded by handle</td></tr>
<tr><td>Labels</td><td><code>Γ</code> via <code>from_singles</code>: <code>𝓢ec</code> / <code>𝓟ub</code></td><td>Monotone <code>isCorrupt</code> predicates attached at generation: <code>sharedKeyLabel</code>, <code>Label.pub</code></td></tr>
<tr><td>Key usage</td><td>Key kind in the term (<code>key () .SymEnc</code>)</td><td><code>Usage</code> attached at generation, checked with <code>HasUsage</code></td></tr>
<tr><td>Crypto predicate</td><td><code>CryptoPreds.u_sym_enc_pred</code> (plaintext is a pair)</td><td><code>SymEncPred</code> instance (plaintext parses as <code>ResponsePayload</code>)</td></tr>
<tr><td>Events</td><td>String tag plus content; <code>event_preds</code> with a wildcard</td><td>Typed inductive; exhaustive <code>EventInv</code></td></tr>
<tr><td>States</td><td><code>State.Init / Null</code>, <code>derive_parsable</code>, <code>HasValid</code></td><td>One structure per state, Comparse format, <code>LocalStateInv</code> (+ <code>KnowableBy</code> when compromisable)</td></tr>
<tr><td>Protocol step</td><td>Pure <code>exchange</code> returning an <code>Atom</code></td><td><code>Traceful</code> program</td></tr>
<tr><td>Scheduling</td><td><code>transition</code> + <code>ChoiceFn</code></td><td>Reachability configuration; handles chosen by the attacker</td></tr>
<tr><td>Failure</td><td>Default <code>Atom</code> (sends <code>fail</code>, stores <code>Null</code>)</td><td>The step aborts</td></tr>
<tr><td>Compromise</td><td>Not modelled</td><td>State compromise in the reachability configuration</td></tr>
<tr><td>Step proofs</td><td><code>valid_exchange</code> via <code>intro_valid_exchange'</code>, aesop</td><td><code>HoareTriple</code> via <code>step</code>, grind</td></tr>
<tr><td>Executions to invariant</td><td><code>transition_valid</code>; the induction is left to the user</td><td><code>Trace.Reachable_implies_Invariant</code> (library)</td></tr>
<tr><td>Attacker</td><td>Fixed <code>AttackerKnows</code> rules</td><td>Per-theory rules plus base knowledge from trace entries; soundness theorem per theory</td></tr>
<tr><td>Final theorem</td><td><code>valid_trace → done ∈ tr → start ∈ tr</code></td><td><code>Reachable → Done logged → Start logged</code> (<code>initiator_auth_literal</code>), and the ordered <code>Reachable → Done at t → Start before t</code> (<code>initiator_auth</code>)</td></tr>
<tr><td>Executable checks</td><td><code>SimpleAuthDemo.lean</code> (DebugM)</td><td><code>SanityChecks.lean</code>: <code>#guard</code> runs and reachability proofs</td></tr></table></div>
"""

# ---------------------------------------------------------------- 18
S["beyond"] = (
    """<div class="tablewrap"><table><tr><th>Goal</th><th>In this port</th><th>What to add</th></tr>
<tr><td>Responder participation</td><td>Absent; section 16 shows why it needs a compromise clause</td><td>A responder event, a provenance predicate, a stronger <code>Done</code> invariant and theorem (sketch below)</td></tr>
<tr><td>Key secrecy</td><td>Encoded in <code>sharedKeyLabel</code>, but not stated as a theorem</td><td>“If the attacker knows a key stored as SK(A,B), a copy was compromised”, proved like SignedDH's <code>client_secrecy</code></td></tr>
<tr><td>Injectivity / replay</td><td><code>Done</code> can be logged twice for one <code>Start</code></td><td>Consume the session state, or state and prove uniqueness explicitly</td></tr>
<tr><td>Long-term asymmetric keys</td><td>Not used</td><td><code>DY/Actions/LongTermKeys.lean</code>, as in SignedDH</td></tr>
<tr><td>XOR reasoning</td><td>Not available: no XOR theory in <code>DY/EquationalTheory/</code></td><td>A new equational theory. LeanDY has XOR built in.</td></tr>
<tr><td>Time / liveness</td><td>Only “before” in the theorem; no progress claim</td><td>Separate assumptions and proofs</td></tr></table></div>
<p>More DYLean examples, in the DYLean repository: <a href=\"""" + DY_TREE + """Examples/SignedDH">SignedDH</a> (signatures, PKI, compromise clauses), <a href=\"""" + DY_TREE + """Examples/SignedDHKEM">SignedDHKEM</a> (locally defined primitives), <a href=\"""" + DY_TREE + """Examples/Ratchet">Ratchet</a>, <a href=\"""" + DY_TREE + """Examples/MerkleTree">MerkleTree</a>, <a href=\"""" + DY_TREE + """Examples/ACME">ACME</a> (including an attack). The LeanDY counterpart of this page is the separate LeanDY SimpleAuth workshop.</p>
<details><summary>Exercise: strengthen the example to show responder participation</summary>
<ol><li>Add an event <code>Respond (a b: Participant) (na: Bytes)</code>, log it in <code>Responder.respond</code> before encrypting, with invariant <code>True</code>.</li>
<li>Let the key usage carry the pair, e.g. <code>sharedKeyUsage a b</code> with <code>data := some (serialize …)</code>, and generate each key with the usage for its pair.</li>
<li>Strengthen <code>SimpleAuthSymEncPred</code>: the usage is <code>sharedKeyUsage i r</code>, the plaintext parses as a payload <code>p</code> with <code>p.a = i</code>, and <code>Respond i r p.na</code> has been logged. The responder establishes this right after logging <code>Respond</code>.</li>
<li>In <code>Initiator.finish</code>, <code>symDec</code>'s postcondition now gives “<code>Respond a b na</code> logged, or the key is corrupt”. Make that part of <code>Done</code>'s invariant (the corrupt case becomes “some copy of SK(a,b) was compromised”).</li>
<li>State the theorem: <code>Done a b na</code> at <code>t</code> implies <code>Respond a b na</code> or a compromise of SK(a,b) before <code>t</code>. Check it against section 16's attack: that trace must fall in the second disjunct.</li></ol>
<p>This is a design sketch. It has not been implemented or compiled as part of this example.</p></details>
<details><summary>Exercise: distinguish three claims about the same nonce</summary><p><code>na.Invariant tr</code> is a symbolic well-formedness fact (here: Na is a genuine random value of the trace). <code>na.Publishable tr</code> concerns confidentiality. “Na was generated at position i” is a trace fact that neither of them records. None of them implies that a session completes at most once.</p></details>
"""
)

# ---------------------------------------------------------------- 19
CHECKS = [
    "Write the exact final security proposition, including its compromise disjuncts.",
    "Select the equational theories; write any missing primitive with its invariant and attacker-knowledge theorem.",
    "Define one structure per message, plaintext and state, with Comparse formats and <code>IsWellFormed_eq</code> lemmas.",
    "Define the events as a typed inductive.",
    "Write each step as a <code>Traceful</code> program; log events before storing states that mention them.",
    "List every attacker-callable function (including setup and compromise) in the reachability configuration.",
    "Run an honest execution with <code>#guard</code>, prove it reachable, and add runs that must fail.",
    "Choose labels and usages for every random value; pass them as ghost arguments.",
    "Write the crypto predicates; prove they are monotone.",
    "Write state invariants; for compromisable states prove <code>invariant_implies_KnowableBy</code>.",
    "Write event invariants strong enough to carry your property.",
    "Prove one Hoare triple per step with <code>step</code>; package them with <code>ReachableImpliesInvariant</code>.",
    "Assemble <code>Instance.lean</code> from exactly the components listed in the <code>Has…</code> classes.",
    "Prove the theorem with <code>apply_Reachable_implies_Invariant</code> and check <code>#print axioms</code>.",
    "Build attack scenarios for each compromise disjunct, and audit the theorem by removing the checks you rely on.",
]
S["checklist"] = (
    "<p>Use these as concrete development milestones. Tick boxes are a reading aid and are not saved.</p>\n"
    + "".join(f'<label class="check"><input type="checkbox"> {c}</label>' for c in CHECKS)
    + "\n"
)

# ---------------------------------------------------------------- refs
S["references"] = (
    """<ul><li><a href="dylean-examples/DYLeanExamples/SimpleAuth/">dylean-examples/DYLeanExamples/SimpleAuth/</a>: the port (<code>SymEnc</code>, <code>Specification</code>, <code>Proof</code>, <code>Instance</code>, <code>SecurityTheorems</code>, <code>SanityChecks</code>), imported by <a href="dylean-examples/DYLeanExamples.lean">DYLeanExamples.lean</a>.</li>
<li>DYLean library at commit <code>d58f33b8d2d8</code> (4 September 2026), with toolchain <code>leanprover/lean4:v4.33.0</code>. Most relevant: <a href=\"""" + LIBS["dylean"][1] + """DY/EquationalTheory/Sign.lean">Sign.lean</a> (template for SymEnc), <a href=\"""" + LIBS["dylean"][1] + """DY/Bytes/Invariants.lean">Bytes/Invariants.lean</a>, <a href=\"""" + LIBS["dylean"][1] + """DY/Label/Labels.lean">Label/Labels.lean</a>, <a href=\"""" + DY_TREE + """DY/Actions">Actions/</a>, <a href=\"""" + LIBS["dylean"][1] + """DY/Trace/Manipulation.lean">Trace/Manipulation.lean</a>, <a href=\"""" + LIBS["dylean"][1] + """DY/Trace/ReachabilityTheorem.lean">Trace/ReachabilityTheorem.lean</a>, and <a href=\"""" + DY_TREE + """Examples/SignedDH">Examples/SignedDH/</a> (the structural template).</li>
<li>LeanDY: <a href="leandy-examples/LeanDYExamples/SimpleAuth.lean">leandy-examples/LeanDYExamples/SimpleAuth.lean</a> (LeanDY's SimpleAuth with the tuple-order fix of commit <code>dd9753c</code> and added annotations) and <a href="leandy-examples/LeanDYExamples/SimpleAuthDemo.lean">SimpleAuthDemo.lean</a>, on the LeanDY library at commit <code>e0705986</code>.</li>
<li>Papers: <em>Bob DyLean: A Framework for the Symbolic Analysis of Cryptographic Protocols in Lean</em> (<a href="https://eprint.iacr.org/2026/1493">eprint 2026/1493</a>), and Jeanteur, Veronese, Solitro and Maffei, <em>LeanDY: Type-Based and Trace-Based Symbolic Protocol Verification in Lean</em>. This page cites the papers only by title: section references were not checked.</li></ul>
<p><strong>What was verified.</strong> Both projects compile from a clean state without errors, warnings or <code>sorry</code>. <code>initiator_auth_literal</code> and <code>initiator_auth</code> are proved independently of each other, and each depends only on <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>. <code>honestRun_properties</code> and <code>compromisedKeyAttacker_properties</code> additionally depend on one <code>native_decide</code> axiom each. The three <code>#guard</code> runs pass, and the diagnostic variant in section 14 compiles. The design sketch in section 18 has not been implemented.</p>
<p>The HTML is self-contained, has no external scripts or stylesheets, and can be edited as ordinary HTML, or regenerated with <code>tools/generate_dylean_tutorial.py</code>. Links to files of this folder are relative. Links into the DYLean and LeanDY libraries point to GitHub at the pinned commits.</p>
"""
)

# ---------------------------------------------------------------- assemble
body = []
for sid, title in NAV:
    body.append(f'<section id="{sid}">\n<h2>{html.escape(title)}</h2>\n{S[sid]}</section>\n')

nav = "\n".join(f'<a href="#{sid}">{html.escape(title)}</a>' for sid, title in NAV)

page = f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>DYLean SimpleAuth workshop</title>
<style>
{CSS}
</style>
</head>
<body>
<header>
<div class="kicker">DYLean · a source-guided workshop</div>
<h1>Build your protocol and its proofs</h1>
<p>Learn the framework through SimpleAuth, ported from LeanDY: choose your primitives, write the protocol as programs, design labels and invariants, prove each step, and connect the proofs to every trace the attacker can produce.</p>
<p>Companion to the LeanDY SimpleAuth workshop · DYLean d58f33b and LeanDY e0705986 · 16 October 2026</p>
</header>
<div class="layout">
<nav aria-label="Tutorial chapters">
{nav}
</nav>
<main>
{''.join(body)}</main>
</div>
</body>
</html>
"""

OUT.write_text(page)
print("\n".join(report))
print(f"wrote {OUT} ({len(page)} bytes)")
