#!/usr/bin/env python3
import pathlib
import re
import sys
root = pathlib.Path(__file__).resolve().parent.parent
log = pathlib.Path(sys.argv[1]).read_text()
expected_names = set(re.findall(r'^#print axioms (Erdos143\.[^\s]+)', (root / 'AxiomAudit.lean').read_text(), re.M))
expected = len(expected_names)
reports = re.findall(r"^'Erdos143\.[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log, re.M)
if len(reports) != expected:
    raise SystemExit(f'Incomplete axiom audit: {len(reports)} of {expected} reports')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
used = set()
for report in reports:
    used.update(x.strip() for x in report.split(',') if x.strip())
if not used <= allowed:
    raise SystemExit(f'Unexpected axioms: {sorted(used - allowed)}')
if 'sorryAx' in log or re.search(r'\berror:', log):
    raise SystemExit('Axiom audit contains an error or sorryAx')
print(f'{expected} proved declarations audited; only standard foundations: {", ".join(sorted(used))}')
required = {'Erdos143.mainConclusion_proved', 'Erdos143.strongConclusion_proved', 'Erdos143.realConclusion_proved'}
reported = set(re.findall(r"^'(Erdos143\.[^']+)' (?:depends on axioms:|does not depend on any axioms)", log, re.M))
if reported != expected_names:
    raise SystemExit(f'Audit declaration mismatch: missing {sorted(expected_names - reported)}, unexpected {sorted(reported - expected_names)}')
if not required <= reported:
    raise SystemExit(f'Missing closed main-theorem audit: {sorted(required - reported)}')
print('Closed MainConclusion, StrongConclusion, and real-domain conclusion audited successfully')
