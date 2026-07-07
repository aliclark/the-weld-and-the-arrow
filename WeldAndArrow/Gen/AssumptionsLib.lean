import WeldAndArrow.Exposition.Basic
import WeldAndArrow.Meta.AssumptionLedger

namespace WAA

namespace AssumptionsGen

def renderAnchor (anchor : AssumptionAnchor) : String :=
  "`" ++ anchor.name.toString ++ "` (" ++ anchor.status.label ++ ")"

def renderAnchorList (anchors : List AssumptionAnchor) : String :=
  match anchors with
  | [] => "None."
  | names => Exposition.joinComma (names.map renderAnchor)

def anchorsForLayer (layer : AnchorLayer) (entry : AssumptionEntry) :
    List AssumptionAnchor :=
  entry.anchors.filter (fun anchor => anchor.layer == layer)

def renderEntry (entry : AssumptionEntry) : String :=
  let signatureAnchors := anchorsForLayer .signature entry
  let downstreamAnchors := anchorsForLayer .downstream entry
  let note :=
    match entry.note with
    | none => ""
    | some text => "\n\n> Note: " ++ text
  let downstream :=
    match downstreamAnchors with
    | [] => ""
    | anchors =>
        "\n\n**Downstream elaboration:** " ++ renderAnchorList anchors
  "### " ++ entry.«section».key ++ "." ++ toString entry.number ++ " " ++
    Exposition.markdownEscape entry.title ++ "\n\n" ++
    entry.statement ++ "\n\n" ++
    "**Checked anchors (Signature):** " ++ renderAnchorList signatureAnchors ++
    downstream ++ note

def renderSection (sec : AssumptionSection) : String :=
  "## " ++ sec.key ++ ". " ++ sec.label ++ "\n\n" ++
    String.intercalate "\n\n"
      ((assumptionSectionEntries sec).map renderEntry)

def renderAxiomAuditEntry (name : Lean.Name) : String :=
  "- `" ++ name.toString ++ "` -- pinned by `#guard_msgs` in " ++
    "`WeldAndArrow/Signature/Assumptions.lean` to depend on no axioms."

def renderAxiomAudit : String :=
  "## Axiom audit\n\n" ++
    String.intercalate "\n" (assumptionAxiomAudit.map renderAxiomAuditEntry)

def renderAssumptions : String :=
  "<!-- GENERATED from WeldAndArrow/Meta/AssumptionLedger.lean by " ++
    "`lake exe assumptions_gen` - do not edit -->\n\n" ++
    "# Assumptions\n\n" ++
    "Generated from `WeldAndArrow/Meta/AssumptionLedger.lean` by " ++
    "`lake exe assumptions_gen`. `WeldAndArrow/Signature/Assumptions.lean` " ++
    "holds the compile-checked anchor pins; statement prose is canonical here.\n\n" ++
    String.intercalate "\n\n"
      [ renderSection .asserted,
        renderSection .declined,
        renderSection .convenience,
        renderAxiomAudit ] ++ "\n"

end AssumptionsGen

def renderAssumptions : String :=
  AssumptionsGen.renderAssumptions

end WAA
