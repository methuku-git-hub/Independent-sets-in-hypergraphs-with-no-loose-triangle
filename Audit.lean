module
import all KMV.Basic
import all KMV.Statements
import all KMV.Expansion
import all KMV.Compression
import all KMV.Codegrees
import all KMV.Triangles
import all KMV.Coloring
import all KMV.Auxiliary
import all KMV.FiniteLaw
import all KMV.Entropy
import all KMV.SamplingProcess
import all KMV.SamplingIndependent
import all KMV.SamplingProducts
import all KMV.SamplingCap
import all KMV.SamplingEntropy
import all KMV.SamplingMarginals
import all KMV.Sampling
import all KMV.Packing
import all KMV.DensityStructure
import all KMV.DensityStars
import all KMV.DensityCounting
import all KMV.Density
import all KMV.Deletion
import all KMV.Trimming
import all KMV.AuxiliaryDegrees
import all KMV.ColoringSubset
import all KMV.TriangleCleaning
import all KMV.TriangleClassification
import all KMV.ConfigurationCounting
import all KMV.PairConfigurations
import all KMV.ConfigurationLoss
import all KMV.TriangleCover
import all KMV.IntersectionCounting
import all KMV.RandomDegrees
import all KMV.ConfigurationMonotone
import all KMV.Cleaning
import all KMV.TotalLoss
import all KMV.FiniteCleaning
import all KMV.GraphRestriction
import all KMV.RestrictedSampling
import all KMV.Reduction
import all KMV.SamplingCleaning
import all KMV.Scales
import all KMV.LossEnvelope
import all KMV.Parameters
import all KMV.SamplingParameters
import all KMV.ColorParameters
import all KMV.AssemblyBounds
import all KMV.ReducedAssembly
import all KMV.Main
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/- Audit code reads checked declarations; it does not construct proof terms. -/
run_cmd do
  let env ← getEnv
  let permitted := #[`propext, `Classical.choice, `Quot.sound]
  let mut nodes : Array Json := #[]
  let mut audited : Array Json := #[]
  for (name, ci) in env.constants.toList do
    let text := name.toString
    if text.startsWith "KMV." || text.startsWith "_private.KMV." then
      let deps := ci.type.getUsedConstants ++
        (ci.value? (allowOpaque := true) |>.map Expr.getUsedConstants |>.getD #[])
      nodes := nodes.push <| Json.mkObj [
        ("name", toJson text),
        ("direct_dependencies", toJson (deps.map Name.toString))]
      if let .thmInfo _ := ci then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless permitted.contains ax do
            throwError "Forbidden axiom in {name}: {ax}"
        audited := audited.push <| Json.mkObj [
          ("theorem", toJson text), ("axioms", toJson (axioms.map Name.toString))]
  let mainAxioms ← Lean.collectAxioms `KMV.main_result
  for ax in mainAxioms do
    unless permitted.contains ax do
      throwError "Forbidden axiom in main theorem: {ax}"
  let mut pending : Array Name := #[`KMV.main_result]
  let mut visited : Std.HashSet Name := {}
  let mut closure : Array Json := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless visited.contains name do
      visited := visited.insert name
      let some ci := env.find? name | throwError "Missing dependency: {name}"
      let deps := ci.type.getUsedConstants ++
        (ci.value? (allowOpaque := true) |>.map Expr.getUsedConstants |>.getD #[])
      closure := closure.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("direct_dependencies", toJson (deps.map Name.toString))]
      pending := pending ++ deps
  let result := Json.mkObj [
    ("scope", toJson "Full conditional main theorem and project declarations"),
    ("main_theorem_verified", toJson true),
    ("main_theorem", toJson "KMV.main_result"),
    ("main_axioms", toJson (mainAxioms.map Name.toString)),
    ("main_dependency_closure", toJson closure),
    ("axiom_audit", toJson audited),
    ("project_declaration_graph", toJson nodes)]
  liftIO <| IO.FS.createDirAll "evidence"
  liftIO <| IO.FS.writeFile "evidence/declaration-audit.json" (result.pretty ++ "\n")
  logInfo m!"Audited {audited.size} project theorems; only permitted axioms occur."
