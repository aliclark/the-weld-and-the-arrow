import WeldAndArrow.Exposition.Basic

namespace WAA.Exposition

def indexBody : String := r#"
## Contents

0. **Contents** — this table of contents, listing the generated documents in reading order, with each entry inventorying what its document carries; generated, like the rest of the exposition surface, from `WeldAndArrow/Exposition/*` by `lake exe exposition_gen`.
1. **Theory** — the motivations and the rules: the floor, the act-grammar, the grade and its determination, the domain joint and orthogonality, the karma circuit and its three registers, the weld's two faces, the separate/fuse rule; the input-side assumption list at [Assumptions.md](Assumptions.md); one act run whole through the grid; [Glossary.md](Glossary.md).
2. **Theorems** — what falls out of the rules directly (backsliding, memory and prudence, dukkha, the transposition, the error-taxonomy) and the derivations that meet existing discourses (MMK 17, the three killings and AN 6.63, sudden and gradual, other-power, pariṇāmanā, transcription, the Ten Bulls, Five Ranks, and stage-schemes); with the instructive absences in both.
3. **The Identification and Placements** — the karma identification, the offices-spine that earns the name, the sower/reaper split, the contemporary placements, the pole-typing corollary, the taxonomy's internal mis-feeds, and the disclaimers, enumerated.
4. **Formalization** — a plain-English reading of the checked Lean surface: the reading conventions (the `Waa` system-POV marking, the directed-convention namespace layers as ontological ordering, rfl-transparency notes), the preorder and pole-class preliminaries, the signature and its convention layers, the layer-by-layer readings of `Consequences`, `Doctrines`, `Identification`, and `Meta` with the numbered pins, the śūnyatā wrappers and reflexivity witness, the invariance discipline and its sibling countermodels, the verdict ledger, and the axiom audit; with what remains prose-bound flagged throughout.
5. **Assumptions** — the input side, enumerated: what the Signature asserts, what it deliberately declines, and its stand-ins; with checked anchors and the axiom audit.
6. **Glossary** — the generated glossary table from `Meta/Glossary.lean`: each term with its provenance kind (a Theory, Theorems, or Identification coinage; canonical; or Lean convention), a newcomer-facing gloss, checked Lean anchors, and backward-only see-also references; term uniqueness, reference ordering, table length, and anchor resolvability are Lean-checked, while gloss accuracy and canonical caveats remain prose obligations carried by the Disclaimers.
"#

def indexDoc : Doc :=
  { id := "index"
    title := "Contents"
    output := "Exposition/index.md"
    source := "WeldAndArrow/Exposition/Index.lean"
    summary := "Contents page for the generated exposition."
    blocks := [.raw indexBody] }

end WAA.Exposition
