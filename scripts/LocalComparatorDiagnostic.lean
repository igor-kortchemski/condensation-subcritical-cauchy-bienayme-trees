module

import Lake.Check.Compare
import Lake.Check.Axioms
import Lean.Data.Json

/-!
# Local diagnostic of the official Comparator comparison

This reuses Lake's own `Lake.Check.compareAt` and `Lake.Check.checkAxioms` on two NDJSON exports
produced by `leanexport`. It is NOT `lake comparator`: it runs outside the Linux sandbox and does
not rebuild or replay anything. Its output is a local diagnostic, never an official result.
Usage: `lake env lean --run scripts/LocalComparatorDiagnostic.lean CONFIG CHALLENGE SOLUTION`.
-/

open Lean in
public def primitiveTargets : Array Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq,
  ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight,
  ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce, ``Nat, ``String, ``Char, ``optParam,
  ``autoParam, ``semiOutParam, ``outParam]

open Lean in
public def main (args : List String) : IO UInt32 := do
  let [cfgPath, challengePath, solutionPath] := args
    | IO.eprintln "usage: CONFIG CHALLENGE.ndjson SOLUTION.ndjson"; return 2
  let cfgText ← IO.FS.readFile cfgPath
  let cfg ← IO.ofExcept (Json.parse cfgText)
  let strs (k : String) : Array Name :=
    match cfg.getObjValAs? (Array String) k with
    | .ok a => a.map String.toName
    | .error _ => #[]
  let theoremNames := strs "theorem_names"
  let definitionNames := strs "definition_names"
  let legalAxioms := strs "permitted_axioms"
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  match Lake.Check.compareAt challenge solution (theoremNames ++ legalAxioms) definitionNames primitiveTargets with
  | .error e => IO.println s!"COMPARE FAILED: {e}"; return 1
  | .ok _ => IO.println "compare: statements and reachable constants match"
  match Lake.Check.checkAxioms solution theoremNames definitionNames legalAxioms with
  | .error e => IO.println s!"AXIOMS FAILED: {e}"; return 1
  | .ok _ => IO.println "axioms: only permitted axioms"
  return 0
