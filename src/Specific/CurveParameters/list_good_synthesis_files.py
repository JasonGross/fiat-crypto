#!/usr/bin/env python
from __future__ import print_function
import os, sys, re, math, json
from fractions import Fraction

CUR_PATH = os.path.dirname(os.path.realpath(__file__))

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

with open(os.path.join(CUR_PATH, 'remake_curves.sh'), 'r') as f:
    contents = f.read()

DIRS = re.findall(r'\${MAKE}.* ([^ ]*) \.\./([^\s]*)\s*$', contents, flags=re.MULTILINE)

SPECIAL_SOLINAS = [(k, v) for k, v in DIRS if k.split('_')[0] in ('x25519', 'x2555', 'x2448')]
SPECIAL_MONTGOMERY = [(k, v) for k, v in DIRS if k.split('_')[0] in ('nistp256', )]
SOLINAS = [(k, v) for k, v in DIRS if 'solinas' in k]
MONTGOMERY = [(k, v) for k, v in DIRS if 'montgomery' in k]

def get_json(jsonfile):
    with open(os.path.join(CUR_PATH, jsonfile), 'r') as f:
        return json.load(f)

def make_folders(curves):
    return [os.path.join('src/Specific', v[1]) for v in curves]

def parse_arith(expr):
    expr = expr.replace(' ', '').replace('^', '**')
    if all(ch in '0123456789+-*^()' for ch in set(expr)):
        return eval(expr, {'__builtins__':None})
    elif '+' in expr:
        ret = 0
        for term in expr.replace('-', '+-').split('+'):
            if term == '': continue
            ret += parse_arith(term)
        return ret
    elif '.' in expr and expr.replace('.', '').isdigit():
        return float(expr)
    elif '*' in expr:
        ret = 1
        for term in expr.split('*'):
            if term == '': continue
            ret *= parse_arith(term)
        return ret
    elif '/' in expr:
        return Fraction(expr)
    else:
        raw_input('Unhandled arith: %s' % expr)
        assert(False)


def filter_curves(curves):
    ret = []
    for jsonfile, folder in curves:
        contents = get_json(jsonfile)
        modulus_str, sz_str, base_str = contents['modulus'].strip(), contents['sz'].strip(), contents['base'].strip()
        modulus, sz, base = parse_arith(modulus_str), parse_arith(sz_str), parse_arith(base_str)
        if modulus > 2**(base * sz):
            eprint('ERROR: (%s) modulus > 2^(base * sz); %s > 2^(%s * %s)'
                   % (jsonfile, modulus_str, base_str, sz_str))
        elif 2**(base * sz) >= 2 * modulus and 'freeze' in contents['operations']:
            eprint('ERROR in Freeze: (%s) 2 * modulus <= 2^(base * sz); 2 * (%s) <= 2^(%s * %s)'
                   % (jsonfile, modulus_str, base_str, sz_str))
        else:
            ret.append((jsonfile, folder, contents))
    ret = sorted(ret, key=(lambda v: int(v[2]['sz'])))
    return ret

CURVES = make_folders(SPECIAL_SOLINAS + SPECIAL_MONTGOMERY +
                      filter_curves(SOLINAS + MONTGOMERY))

def get_display(folders):
    return [os.path.join(folder, display[:-len('.v')] + '.log')
            for folder in folders
            for display in os.listdir(folder)
            if display.endswith('Display.v')]

if sys.argv[1] == 'synthesis':
    print(' '.join(os.path.join(p, 'Synthesis.vo') for p in CURVES))
elif sys.argv[1] == 'display':
    print(' '.join(get_display(CURVES)))
else:
    sys.exit(1)
