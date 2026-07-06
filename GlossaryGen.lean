import WeldAndArrow.Meta.Glossary

namespace WAA

def markdownEscape (s : String) : String :=
  (((s.replace "\\" "\\\\").replace "|" "\\|").replace "\n" " ").replace "\r" " "

def joinComma (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: rest => rest.foldl (fun acc item => acc ++ ", " ++ item) x

def renderAnchors (anchors : List Lean.Name) : String :=
  match anchors with
  | [] => "—"
  | names => joinComma (names.map (fun name => "`" ++ name.toString ++ "`"))

def renderSeeAlso (refs : List String) : String :=
  match refs with
  | [] => "—"
  | names => joinComma (names.map (fun name => "`" ++ markdownEscape name ++ "`"))

def renderGlossaryRow (entry : GlossaryEntry) : String :=
  "| " ++ markdownEscape entry.term ++
  " | " ++ markdownEscape entry.kind.label ++
  " | " ++ markdownEscape entry.gloss ++
  " | " ++ renderAnchors entry.anchors ++
  " | " ++ renderSeeAlso entry.seeAlso ++
  " |"

def glossaryHeader : String :=
  "# Glossary\n\n" ++
  "Generated from `WeldAndArrow/Meta/Glossary.lean` by `lake exe glossary_gen`. " ++
  "Gloss accuracy remains prose; Lean checks term uniqueness, backward `seeAlso` references, and anchor resolvability. " ++
  "Canonical Buddhist terms are glossed for newcomers; expert caveats live in the Disclaimers.\n\n" ++
  "| Term | Kind | Definition | Checked anchors | See also |\n" ++
  "| --- | --- | --- | --- | --- |"

def renderGlossary : String :=
  glossaryHeader ++ "\n" ++
    String.intercalate "\n" (glossary.map renderGlossaryRow) ++ "\n"

end WAA

def main : IO Unit := do
  IO.print WAA.renderGlossary
