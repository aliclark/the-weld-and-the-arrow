import WeldAndArrow.Exposition.Registry

namespace WAA.Exposition

def outputFileName (output : String) : String :=
  output.replace "Exposition/" ""

def renderIndexEntry (n : Nat) (ref : DocRef) : String :=
  s!"{n}. **[{ref.title}]({outputFileName ref.output})** — {ref.summary}."

def renderIndexEntries : Nat -> List DocRef -> List String
  | _, [] => []
  | n, ref :: refs => renderIndexEntry n ref :: renderIndexEntries (n + 1) refs

def indexBody : String :=
  "## Contents\n\n" ++ String.intercalate "\n" (renderIndexEntries 0 registry)

def indexDoc : Doc :=
  { id := indexRef.id
    title := indexRef.title
    output := indexRef.output
    source := "WeldAndArrow/Exposition/Registry.lean"
    summary := indexRef.summary
    blocks := [.raw indexBody] }

end WAA.Exposition
