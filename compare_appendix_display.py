#!/usr/bin/env python3
"""Strict, narrowly scoped comparison of one historical set display field."""
import argparse
import ast
import copy
import datetime
import hashlib
import json
from pathlib import Path

FIELD = 'A digit bijection instances / B range'
REQUIRED = {'t<=8', 'L<=3'}
OMIT = ('date', 'inputs_sha256')

def strict_object(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError('Duplicate JSON object key: ' + key)
        out[key] = value
    return out

def read(path):
    data = path.read_bytes()
    return json.loads(data, object_pairs_hook=strict_object), {
        'path': str(path), 'bytes': len(data),
        'sha256': hashlib.sha256(data).hexdigest()}

def normalize(obj):
    value = obj['comparison']['recurrence'][FIELD][1]
    if type(value) is not str or len(value) > 256:
        raise ValueError('The designated value must be a short set-display string')
    parsed = ast.literal_eval(value)
    if type(parsed) is not set or len(parsed) != 2 or any(type(x) is not str for x in parsed) or parsed != REQUIRED:
        raise ValueError('The designated value is not exactly the required two-string set')
    result = copy.deepcopy(obj)
    omitted = {key: result.pop(key) for key in OMIT}
    normal = sorted(parsed)
    result['comparison']['recurrence'][FIELD][1] = normal
    return result, {'original': value, 'normalized': normal, 'omitted_top_level': omitted}

def compare(actual, expected):
    a, ar = normalize(actual)
    e, er = normalize(expected)
    # Comparing canonical JSON also distinguishes integers, floats and booleans.
    aa = json.dumps(a, sort_keys=True, ensure_ascii=False, separators=(',', ':'))
    ee = json.dumps(e, sort_keys=True, ensure_ascii=False, separators=(',', ':'))
    return aa == ee, ar, er, hashlib.sha256(aa.encode()).hexdigest(), hashlib.sha256(ee.encode()).hexdigest()

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--actual', type=Path, required=True)
parser.add_argument('--expected', type=Path, required=True)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
if args.out.exists():
    raise SystemExit('Refusing to replace an existing supplemental result')
actual, ah = read(args.actual)
expected, eh = read(args.expected)
ok, av, ev, an, en = compare(actual, expected)
negative = copy.deepcopy(actual)
negative['comparison']['recurrence'][FIELD][1] = "{'t<=9', 'L<=3'}"
try:
    changed_element_rejected = not compare(negative, expected)[0]
    changed_element_reason = 'Strict full comparison mismatch'
except (ValueError, SyntaxError) as error:
    changed_element_rejected = True
    changed_element_reason = str(error)
negative_other = copy.deepcopy(actual)
old_other = negative_other['comparison']['recurrence']['floor example equal']
assert type(old_other) is bool
negative_other['comparison']['recurrence']['floor example equal'] = not old_other
other_field_rejected = not compare(negative_other, expected)[0]
result = {
    'status': 'PASS' if ok and changed_element_rejected and other_field_rejected else 'FAIL',
    'scope': 'Public replay: exact two-string set display normalized; all other retained fields strictly compared',
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'inputs': {'actual': ah, 'expected': eh},
    'exact_normalized_field': '$.comparison.recurrence.' + FIELD + '[1]',
    'required_set_elements': sorted(REQUIRED),
    'actual': av, 'expected': ev,
    'all_other_retained_fields_strictly_equal': ok,
    'canonical_actual_sha256': an, 'canonical_expected_sha256': en,
    'negative_tests': [
        {'change': "Designated display field becomes {'t<=9', 'L<=3'}",
         'rejected': changed_element_rejected, 'reason': changed_element_reason},
        {'change': 'Flip comparison.recurrence.floor example equal',
         'rejected': other_field_rejected}],
}
args.out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({key: result[key] for key in ['status', 'scope', 'all_other_retained_fields_strictly_equal', 'negative_tests']}, indent=2))
raise SystemExit(0 if result['status'] == 'PASS' else 1)
