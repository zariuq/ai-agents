/-!
# DocText Policy

Canonical ownership for repository prose generation:

- All README/document AST + GF-English generation modules must live under
  `Mettapedia/DocText/`.
- `Mettapedia/Languages/GF/Examples/*Readme*` may exist only as compatibility shims
  importing `Mettapedia.DocText.*`.
- Natural-language claims should be generated compositionally via GF helpers.
- Ordinary declarative prose must be emitted from GF claim renderers (`render*Claim`).
- In README trees, typed technical blocks (`apiItems`, `syntaxItems`, `pathItems`,
  `codeBlock`) are allowed for non-claim content.
- Generic `.bulletItem` / `.bulletList` should not be used for prose-bearing content.

This file is normative guidance for AI agent work in this repository.
-/

namespace Mettapedia.DocText.Policy

/-- Canonical root for README/document AST + generation code. -/
def canonicalRoot : String := "Mettapedia/DocText/"

/-- Allowed non-claim technical block classes in compositional README trees. -/
def allowedTechnicalBlocks : List String :=
  [ "code_block"
  , "path_items"
  , "api_items"
  , "syntax_items"
  ]

/-- Non-canonical legacy path retained only for shims. -/
def legacyShimRoot : String := "Mettapedia/Languages/GF/Examples/"

#eval s!"DocText canonical root: {canonicalRoot}"

end Mettapedia.DocText.Policy
