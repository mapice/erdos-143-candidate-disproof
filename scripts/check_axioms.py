#!/usr/bin/env python3
"""Check exact root coverage and the collective axiom union emitted by Lean."""
import pathlib
import re
import sys
root = pathlib.Path(__file__).resolve().parent.parent
log = pathlib.Path(sys.argv[1]).read_text()
audit_source = (root / 'AxiomAudit.lean').read_text()
roots_block = re.search(r'-- BEGIN AXIOM AUDIT ROOTS\n(.*?)\n-- END AXIOM AUDIT ROOTS', audit_source, re.S)
if roots_block is None:
    raise SystemExit('Missing generated audit root list')
expected_list = re.findall(r'^  `(Erdos143\.[^\s,]+),?$', roots_block.group(1), re.M)
expected_names = set(expected_list)
if not expected_list or len(expected_list) != len(expected_names):
    raise SystemExit('Empty or duplicate generated audit roots')
expected = len(expected_list)
reported_list = re.findall(r'^AXIOM_AUDIT_ROOT (Erdos143\.[^\s]+)$', log, re.M)
reported = set(reported_list)
if len(reported_list) != expected or len(reported) != len(reported_list):
    raise SystemExit(f'Incomplete or duplicate root coverage: {len(reported_list)} of {expected} reports')
if reported != expected_names:
    raise SystemExit(f'Audit declaration mismatch: missing {sorted(expected_names - reported)}, unexpected {sorted(reported - expected_names)}')
summaries = re.findall(r'^AXIOM_AUDIT_SUMMARY roots=(\d+) visited=(\d+) axioms=(\d+)$', log, re.M)
if len(summaries) != 1 or int(summaries[0][0]) != expected or int(summaries[0][1]) < expected:
    raise SystemExit('Missing or inconsistent collective audit summary')
if len(re.findall(r'^AXIOM_AUDIT_PASSED$', log, re.M)) != 1:
    raise SystemExit('Missing or duplicate collective audit success marker')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
axiom_list = re.findall(r'^AXIOM_AUDIT_AXIOM ([^\s]+)$', log, re.M)
used = set(axiom_list)
if len(axiom_list) != len(used):
    raise SystemExit('Duplicate collective axiom report')
if int(summaries[0][2]) != len(axiom_list):
    raise SystemExit('Incomplete collective axiom union')
if not used <= allowed:
    raise SystemExit(f'Unexpected axioms: {sorted(used - allowed)}')
if 'sorryAx' in log or re.search(r'\berror:', log):
    raise SystemExit('Axiom audit contains an error or sorryAx')
print(f'{expected} proved declarations collectively audited; exact union contains only standard foundations: {", ".join(sorted(used))}')
required = {'Erdos143.mainConclusion_proved', 'Erdos143.strongConclusion_proved', 'Erdos143.realConclusion_proved', 'Erdos143.Logarithmic.periodicPrimitiveSelection_logarithmic_proved'}
if not required <= reported:
    raise SystemExit(f'Missing closed main-theorem audit: {sorted(required - reported)}')
print('Closed MainConclusion, StrongConclusion, real-domain conclusion, and logarithmic selection audited successfully')
