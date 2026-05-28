/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual

/-!
# Free Monad Diagram

Verso block for the editable HTML diagram used in the VCV-io oracle chapter.
-/

open Verso Genre Manual Doc Elab
open Verso.Doc
open Lean

private def htxt (s : String) : Verso.Output.Html :=
  Verso.Output.Html.text true s

private def hnode (name : String) (attrs : Array (String × String))
    (children : Array Verso.Output.Html) : Verso.Output.Html :=
  Verso.Output.Html.tag name attrs (.seq children)

private def divc (className : String) (children : Array Verso.Output.Html) :
    Verso.Output.Html :=
  hnode "div" #[("class", className)] children

private def spanc (className : String) (children : Array Verso.Output.Html) :
    Verso.Output.Html :=
  hnode "span" #[("class", className)] children

private def codec (s : String) : Verso.Output.Html :=
  hnode "code" #[] #[htxt s]

private def node (kind title body : String) : Verso.Output.Html :=
  divc ("sm-fm-node sm-fm-" ++ kind) #[
    spanc "sm-fm-node-title" #[codec title],
    spanc "sm-fm-node-body" #[htxt body]
  ]

private def branch (label title body : String) : Verso.Output.Html :=
  divc "sm-fm-branch" #[
    spanc "sm-fm-edge-label" #[codec label],
    node "subtree" title body
  ]

private def smallTree (root leftLabel leftLeaf rightLabel rightLeaf : String) :
    Verso.Output.Html :=
  divc "sm-fm-small-tree" #[
    divc "sm-fm-tree-root" #[node "query" root "query node"],
    divc "sm-fm-tree-branches" #[
      branch leftLabel leftLeaf "leaf / subtree",
      branch rightLabel rightLeaf "leaf / subtree"
    ]
  ]

private def freeMonadDiagramHtml : Verso.Output.Html :=
  hnode "figure" #[
    ("class", "sm-fm-diagram"),
    ("aria-label", "Diagram of roll, bind, simulateQ, and evalDist for a free monad")
  ] #[
    hnode "figcaption" #[("class", "sm-fm-caption")] #[
      htxt "Free monad trees: roll, grafting, and interpretation"
    ],

    divc "sm-fm-panel sm-fm-roll-panel" #[
      divc "sm-fm-panel-title" #[htxt "1. roll exposes one query node"],
      divc "sm-fm-roll-grid" #[
        divc "sm-fm-roll-tree" #[
          divc "sm-fm-roll-root" #[node "query" "q : Q" "one primitive query"],
          divc "sm-fm-branches sm-fm-three-branches" #[
            branch "r0" "k r0" "continuation tree",
            branch "r1" "k r1" "continuation tree",
            branch "r2" "k r2" "continuation tree"
          ]
        ],
        divc "sm-fm-note" #[
          divc "sm-fm-note-line" #[
            codec "roll q k : T X"
          ],
          divc "sm-fm-note-line" #[
            codec "k : R q -> T X"
          ],
          hnode "p" #[] #[
            htxt "The continuation ",
            codec "k",
            htxt " is a function. For every possible response ",
            codec "r",
            htxt ", the value ",
            codec "k r",
            htxt " is the rest of the computation as another tree."
          ]
        ]
      ]
    ],

    divc "sm-fm-panel sm-fm-bind-panel" #[
      divc "sm-fm-panel-title" #[htxt "2. bind grafts trees onto returned leaves"],
      divc "sm-fm-bind-grid" #[
        divc "sm-fm-bind-side" #[
          divc "sm-fm-side-title" #[codec "t : T X"],
          smallTree "q1" "a" "pure x" "b" "pure y"
        ],
        divc "sm-fm-bind-arrow" #[
          codec "t >>= f",
          spanc "sm-fm-arrow-line" #[htxt "->"]
        ],
        divc "sm-fm-bind-side" #[
          divc "sm-fm-side-title" #[codec "t >>= f : T Y"],
          smallTree "q1" "a" "f x" "b" "f y"
        ]
      ],
      divc "sm-fm-note sm-fm-wide-note" #[
        hnode "p" #[] #[
          htxt "The old query nodes stay in place. Each leaf ",
          codec "pure x",
          htxt " is replaced by the whole tree ",
          codec "f x",
          htxt ". That replacement is the grafting."
        ]
      ]
    ],

    divc "sm-fm-panel sm-fm-sim-panel" #[
      divc "sm-fm-panel-title" #[htxt "3. simulateQ interprets syntax; probability is optional"],
      divc "sm-fm-flow" #[
        node "semantic" "impl" "(q : Q) -> m (R q)",
        divc "sm-fm-flow-arrow" #[htxt "free-monad universal property"],
        node "semantic" "simulateQ impl" "Free(P) X -> m X",
        divc "sm-fm-flow-arrow" #[htxt "if m has HasEvalSPMF"],
        node "semantic" "evalDist" "m X -> SPMF X"
      ],
      divc "sm-fm-note sm-fm-wide-note" #[
        hnode "p" #[] #[
          codec "simulateQ",
          htxt " does not by itself mean probability. It returns ",
          codec "m X",
          htxt ". If ",
          codec "m = SPMF",
          htxt ", or if ",
          codec "m",
          htxt " has an ",
          codec "evalDist",
          htxt " map into ",
          codec "SPMF",
          htxt ", then the interpreted computation has probabilistic semantics."
        ]
      ]
    ]
  ]

block_extension Block.freeMonadDiagram where
  data := Json.null
  traverse _id _data _contents := do
    pure none
  toTeX :=
    some <| fun _goI _goB _id _data _contents => do
      pure <| Verso.Output.TeX.raw
        ("\\paragraph{Free monad tree diagram.} In HTML output, this block " ++
          "shows the editable diagram for roll, bind-as-grafting, simulateQ, " ++
          "and evalDist.\n")
  toHtml :=
    some <| fun _goI _goB _id _data _contents => do
      pure freeMonadDiagramHtml

@[directive]
def freeMonadDiagram : DirectiveExpanderOf Unit
  | (), _contents => do
    ``(Block.other Block.freeMonadDiagram #[])
