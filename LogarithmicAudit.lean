import Erdos143.LogarithmicProof
import Lean

open Lean Elab Command

/-- Inspect only project constants: imported libraries cannot refer to this project. -/
partial def logarithmicProjectDependencies (env : Environment)
    (pending : List Name) (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: ns =>
    if seen.contains n || !(`Erdos143).isPrefixOf n then
      logarithmicProjectDependencies env ns seen
    else
      match env.find? n with
      | none => logarithmicProjectDependencies env ns (seen.insert n)
      | some info => logarithmicProjectDependencies env
          (info.getUsedConstantsAsSet.toList ++ ns) (seen.insert n)

run_cmd do
  let env ← getEnv
  let root := `Erdos143.Logarithmic.periodicPrimitiveSelection_logarithmic_proved
  let dependencies := logarithmicProjectDependencies env [root]
  let oldComparisons := [
    `Erdos143.complex_euler_factor_lower,
    `Erdos143.complex_inverse_euler_factor_upper,
    `Erdos143.complex_finite_euler_product_upper,
    `Erdos143.complex_euler_product_upper,
    `Erdos143.generating_norm_sq_le_LSeries,
    `Erdos143.generatingValue_norm_sq_le_LSeries,
    `Erdos143.generatingValue_norm_le_two_rpow_LSeries,
    `Erdos143.nonprincipal_generatingValue_bounded,
    `Erdos143.positive_euler_factor_lower,
    `Erdos143.positive_finite_euler_product_lower,
    `Erdos143.positive_euler_product_lower,
    `Erdos143.principal_generatingValue_lower,
    `Erdos143.principal_generating_local_lower,
    `Erdos143.global_generating_local_upper,
    `Erdos143.principal_abel_lower_bound,
    `Erdos143.periodicPrimitiveSelection_proved]
  for n in oldComparisons do
    if dependencies.contains n then
      throwError "The logarithmic proof still depends on the original analytic comparison: {n}"
  for n in [
    `Erdos143.generatingValue_logarithmic_identity,
    `Erdos143.prime_logarithmic_remainder_summable_and_norm_le] do
    unless dependencies.contains n do
      throwError "The logarithmic proof is missing its intended analytic input: {n}"
  logInfo m!"Logarithmic dependency audit passed: {dependencies.size} project constants; the logarithmic identity and uniform remainder are used, and the original Euler comparisons are absent."

#print axioms Erdos143.generatingValue_logarithmic_identity
#print axioms Erdos143.prime_logarithmic_remainder_summable_and_norm_le
#print axioms Erdos143.Logarithmic.remainderBound_proved
#print axioms Erdos143.Logarithmic.periodicPrimitiveSelection_logarithmic_proved
#check Erdos143.Logarithmic.periodicPrimitiveSelection_logarithmic_proved
