import WeldAndArrow.Gen.ExpositionLib

def main (args : List String) : IO Unit := do
  match WAA.Exposition.parseArgs args with
  | .error msg => throw (IO.userError msg)
  | .ok opts =>
      if opts.check then
        WAA.Exposition.checkDocs opts.outputRoot
      else
        WAA.Exposition.writeDocs opts.outputRoot
