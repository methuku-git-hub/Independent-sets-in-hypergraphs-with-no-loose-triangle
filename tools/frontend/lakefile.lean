import Lake
import Lean.Elab.Frontend
open Lake DSL Lean
package frontend

@[«script»] unsafe def check : ScriptFn := fun args => do
  -- Initialize the ordinary Lean elaborator. No theorem is added by this host.
  -- Kernel checking remains enabled (trustLevel = 0).
  Lean.enableInitializersExecution
  if let some dir := (args[3]? : Option String) then IO.Process.setCurrentDir (System.FilePath.mk dir)
  let some path := (args[0]? : Option String) | throw <| IO.userError "expected source path"
  let input ← IO.FS.readFile (System.FilePath.mk path)
  let mod := (args[1]?.getD "Check").toName
  let out := args[2]?.filter (· != "") |>.map System.FilePath.mk
  let errorKinds := if mod == `Challenge then #[] else #[`hasSorry]
  let env? ← Lean.Elab.runFrontend input {} path mod (trustLevel := 0) (oleanFileName? := out)
    (errorOnKinds := errorKinds)
  return if env?.isSome then 0 else 1
