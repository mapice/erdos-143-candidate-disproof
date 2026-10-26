#!/usr/bin/env python3
"""Generate a collective proof-term axiom audit of every project theorem.

Lean's built-in ``#print axioms`` starts a fresh traversal for each root.  Here
the same ``Lean.CollectAxioms.collect`` traversal shares its visited set across
all roots.  Its result is the exact union of their axioms, not an individual
axiom list for each root.
"""
import pathlib
import re
import sys
root = pathlib.Path(__file__).resolve().parent.parent
names = []
for path in sorted((root / "Erdos143").glob("*.lean")):
    source = path.read_text()
    scopes = []
    for line in source.splitlines():
        namespace = re.match(r"^namespace\s+([\w.]+)\s*$", line)
        section = re.match(r"^(?:noncomputable\s+)?section(?:\s+[\w.]+)?\s*$", line)
        end = re.match(r"^end(?:\s+[\w.]+)?\s*$", line)
        declaration = re.match(r"^(?:@\[[^\n]*\]\s*)?(?:lemma|theorem)\s+([\w'.]+)", line)
        if namespace:
            scopes.append(namespace.group(1))
        elif section:
            scopes.append(None)
        elif end:
            if not scopes:
                raise SystemExit(f"Unmatched scope end in {path.name}")
            scopes.pop()
        elif declaration:
            prefix = ".".join(scope for scope in scopes if scope)
            names.append((prefix + "." if prefix else "") + declaration.group(1))
if len(names) != len(set(names)):
    raise SystemExit("Duplicate proved declaration names")
text = """import Erdos143
import Lean

open Lean Elab Command

set_option maxRecDepth 100000

/-- All source-discovered project lemmas and theorems, audited together below. -/
def axiomAuditRoots : Array Name := #[
-- BEGIN AXIOM AUDIT ROOTS
"""
text += ",\n".join("  `" + name for name in names)
text += """
-- END AXIOM AUDIT ROOTS
]

/- Use Lean's own proof-term traversal with one visited set for all roots.
The resulting axiom set is the exact union for the entire list of roots. -/
run_cmd do
  let env ← getEnv
  let mut rootsSeen : NameSet := {}
  for root in axiomAuditRoots do
    if rootsSeen.contains root then
      throwError "Duplicate audit root {root}"
    rootsSeen := rootsSeen.insert root
    match env.checked.get.find? root with
    | some (.thmInfo _) => pure ()
    | some _ => throwError "Audit root is not a checked theorem: {root}"
    | none => throwError "Missing checked audit root {root}"
  let work : CollectAxioms.M Unit := axiomAuditRoots.forM CollectAxioms.collect
  let (_, state) := (work.run env).run {}
  let axioms := state.axioms.qsort Name.lt
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for ax in axioms do
    unless allowed.contains ax do
      throwError "Unexpected collective axiom {ax}"
  for root in axiomAuditRoots do
    logInfo m!"AXIOM_AUDIT_ROOT {root}"
  for ax in axioms do
    logInfo m!"AXIOM_AUDIT_AXIOM {ax}"
  logInfo m!"AXIOM_AUDIT_SUMMARY roots={axiomAuditRoots.size} visited={state.visited.size} axioms={axioms.size}"
  logInfo "AXIOM_AUDIT_PASSED"

#print Erdos143.MainConclusion
#print Erdos143.StrongConclusion
#check Erdos143.mainConclusion_proved
#check Erdos143.strongConclusion_proved
#check Erdos143.realConclusion_proved
#check Erdos143.Logarithmic.periodicPrimitiveSelection_logarithmic_proved
"""
if "--check" in sys.argv:
    if (root / "AxiomAudit.lean").read_text() != text:
        raise SystemExit("AxiomAudit.lean is stale; run python3 scripts/generate_audit.py")
    print(f"Audit matches all {len(names)} proved declarations")
else:
    (root / "AxiomAudit.lean").write_text(text)
    print(f"Audit generated for {len(names)} proved declarations")
