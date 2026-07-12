import WeldAndArrow.Exposition.Gen.ExpositionLib

namespace WAA.Exposition.Gen.FullExpositionGeneration

def outputRoot : String := ".lake/exposition-full"

def copyStaticDocs : IO Unit := do
  IO.FS.createDirAll (outputRoot ++ "/Exposition")
  for ref in WAA.Exposition.registry do
    match ref.provenance with
    | .source =>
        let content <- IO.FS.readFile ref.output
        IO.FS.writeFile (WAA.Exposition.outputPath outputRoot ref.output) content
    | .generated _ => pure ()

def checkNonempty (ref : WAA.Exposition.DocRef) : IO Unit := do
  let path := WAA.Exposition.outputPath outputRoot ref.output
  let content <- IO.FS.readFile path
  if content.isEmpty then
    throw (IO.userError s!"exposition file is empty: {path}")

def run : IO Unit := do
  copyStaticDocs
  WAA.Exposition.writeDocs outputRoot
  for ref in WAA.Exposition.registry do
    checkNonempty ref

end WAA.Exposition.Gen.FullExpositionGeneration

def main : IO Unit := do
  WAA.Exposition.Gen.FullExpositionGeneration.run
