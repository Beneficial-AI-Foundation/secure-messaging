# Editable Diagrams In Verso

Prefer keeping diagrams as editable documentation source, not as disposable
rendered image artifacts.

## Recommended Pattern

For diagrams that need both web and TeX/PDF output, define a Verso block
extension in Lean:

```lean
block_extension Block.someDiagram where
  toHtml := some <| ... -- emit real HTML/SVG DOM
  toTeX  := some <| ... -- emit raw TikZ or other TeX
```

This gives one source-controlled diagram definition with output-specific
renderers:

- HTML output can emit normal HTML nodes or inline SVG elements directly into
  the page. This is not an embedded image file.
- TeX output can emit real TikZ, so generated PDF/TeX docs keep native TeX
  diagrams.

Browsers do not natively render TikZ. Any "TikZ in HTML" approach eventually
does one of these:

- compiles TikZ to SVG/PDF/PNG before serving the page,
- runs client-side TikZ rendering code that creates SVG/HTML in the page,
- or provides a separate HTML/SVG renderer for the web output.

The third option fits Verso well: write an editable Verso block, implement
`toHtml` for browser output, and implement `toTeX` for print output.

## Current Example

The free-monad/oracle diagram is implemented as a Verso-native HTML block in:

```text
docs/SecureMessagingDocs/FreeMonadDiagram.lean
```

It is inserted into the oracle chapter with:

```text
:::freeMonadDiagram
:::
```

The HTML styling lives in:

```text
docs/Main.lean
```

At the moment, the block's HTML renderer emits editable HTML structure styled
by CSS. Its TeX renderer is intentionally minimal and can be extended later to
emit matching TikZ when TeX/PDF output becomes important.

## Rule Of Thumb

Use an embedded image only when the source really is an image. For mathematical
or protocol diagrams that we expect to edit, prefer a Verso block with explicit
HTML and TeX renderers.
