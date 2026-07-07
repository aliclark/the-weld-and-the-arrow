import WeldAndArrow.Exposition.Docs

namespace WAA.Exposition

structure Options where
  check : Bool := false
  outputRoot : String := ""

def outputPath (outputRoot path : String) : String :=
  if outputRoot == "" then path else outputRoot ++ "/" ++ path

def renderedDocs (outputRoot : String := "") : List (String × String) :=
  allDocs.map (fun doc => (outputPath outputRoot doc.output, renderDoc doc))

def ensureOutputDirs (outputRoot : String) : IO Unit := do
  IO.FS.createDirAll (outputPath outputRoot "Exposition")

def writeDocs (outputRoot : String := "") : IO Unit := do
  ensureOutputDirs outputRoot
  for (path, content) in renderedDocs outputRoot do
    IO.FS.writeFile path content

def checkDocs (outputRoot : String := "") : IO Unit := do
  let mut mismatches : Array String := #[]
  for (path, expected) in renderedDocs outputRoot do
    let current <- IO.FS.readFile path
    if current != expected then
      mismatches := mismatches.push path
  unless mismatches.isEmpty do
    let details := mismatches.foldl (fun acc path => acc ++ "\n" ++ path) ""
    throw (IO.userError s!"exposition output drift:{details}")

def parseArgs : List String -> Except String Options
  | [] => .ok {}
  | "--check" :: rest => do
      let opts <- parseArgs rest
      pure { opts with check := true }
  | "--output-dir" :: dir :: rest => do
      let opts <- parseArgs rest
      pure { opts with outputRoot := dir }
  | arg :: _ => .error s!"unknown argument: {arg}"

end WAA.Exposition
