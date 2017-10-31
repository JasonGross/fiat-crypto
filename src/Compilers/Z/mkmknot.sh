#!/bin/bash

set -x

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
GITDIR="$( cd "$DIR" && git rev-parse --show-toplevel)"
cd "$GITDIR"

while true; do
NUMS="$((grep '^\s*[0-9]\+,$' src/Compilers/Z/HexNotationConstants.v;
 find . -name "*.log" | xargs cat | grep -o 'Const [0-9]\+') | grep -o '[0-9]\+' | sort -h | uniq | sed s'/^\(.*\)$/    \1,/g')"

cat > src/Compilers/Z/mknot.py.new <<_EOF
#!/usr/bin/env python
from __future__ import with_statement
import math

systematic_nums \\
    = (list(range(128)) +
       [2**i + j for i in range(256) for j in (1, 0, -1)])
nums = tuple(sorted(set(systematic_nums + [
_EOF
echo "$NUMS" >> src/Compilers/Z/mknot.py.new
cat >> src/Compilers/Z/mknot.py.new <<_EOF
])))

def log2_up(i):
    return int(math.ceil(math.log(i, 2)))

def word(i, width=None):
    assert(i >= 0)
    if width is None:
        if i == 0: return word(i, width=1)
        return word(i, width=2**log2_up(log2_up(i + 1)))
    return 'WO~' + '~'.join(bin(i)[2:].rjust(width, '0'))

word_formats = tuple(sorted([(n, hex(n), bin(n), word(n)) for n in nums]))

def header():
    return (r"""Require Import Coq.ZArith.ZArith.
Require Export Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Export Bedrock.Word.
Require Export Crypto.Util.Notations.

Notation Const x := (Op (OpConst x) TT).
(""" + r"""* python:
<<
""" +
            open(__file__).read() +
            r""">>
 *""" + r""")""")


def hex_nots():
    return ('\\n'.join('''Notation "'%s'" (* %d (%s) *)\\n  := (Const %s%%Z).\\nNotation "'%s'" (* %d (%s) *)\\n  := (Const %s).''' % (h, d, h, d, h, d, h, w)
                      for d, h, b, w in word_formats))
def bin_nots():
    return ('\\n'.join('''Notation "'%s'" (* %d (%s) *)\\n  := (Const %s).''' % (b, d, h, w)
                      for d, h, b, w in word_formats))

with open('HexNotationConstants.v', 'w') as f:
    f.write(header() + '\\n' + hex_nots() + '\\n')

with open('BinaryNotationConstants.v', 'w') as f:
    f.write(header() + '\\n' + bin_nots() + '\\n')
_EOF

git status | grep -o 'src/.*Display.log' | xargs git add || true
git commit -m "Add more display logs (only under 1h)" || true
git status | grep -o 'src/.*\.[ch]' | xargs git add || true
git commit -m "Add generated c files" || true
(cd ./src/Compilers/Z && (cmp --silent ./mknot.py ./mknot.py.new || (cat ./mknot.py.new > ./mknot.py; ./mknot.py)))
git add ./src/Compilers/Z/HexNotationConstants.v ./src/Compilers/Z/BinaryNotationConstants.v && git commit -m "Add more constant notations" || true
git remote update && git push origin curves-from-json-with-primes:curves-from-json-with-primes
TARGETS="$(git grep --name-only Const | grep 'Display.log')"
pushd ../fiat-crypto-stage
git remote update
git reset --hard
git submodule update
git checkout master -f
git reset --hard
git submodule update
git pull upstream master:master -f
git reset --hard
git submodule update
DIFF="$(git diff origin/curves-from-json-with-primes | grep diff | grep 'Display.log' | grep -o 'src/Specific/[^ ]*Display.log' | sort | uniq)"
DIFF2="$(git diff origin/curves-from-json-with-primes | grep diff | grep '\.[ch]' | grep -o 'src/Specific/[^ ]*\.[ch]' | grep 'src/Specific/solinas\|src/Specific/montgomery' | sort | uniq)"
git checkout origin/curves-from-json-with-primes src/Compilers/Z/HexNotationConstants.v src/Compilers/Z/BinaryNotationConstants.v
git add src/Compilers/Z/HexNotationConstants.v src/Compilers/Z/BinaryNotationConstants.v && git commit -m "Add more constant notations"
for i in $DIFF $DIFF2; do
    git checkout origin/curves-from-json-with-primes src/Compilers/Z/HexNotationConstants.v $i
    git add src/Compilers/Z/HexNotationConstants.v $i
done
git commit -m "Update display logs and c files"
git push upstream master:master
popd
make COQBIN="$HOME/.local64/coq/coq-8.7.0/bin/" STDTIME='/home/jgross/Documents/repos/timeout/time-5m-timeout-coq -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"' TIMED=1 update-_CoqProject $TARGETS -kj6 TIMED=1 2>&1 | tee -a time-of-build9.log
make COQBIN="$HOME/.local64/coq/coq-8.7.0/bin/" STDTIME='/home/jgross/Documents/repos/timeout/time-1s-timeout-coq -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"' TIMED=1 update-_CoqProject c -kj18 TIMED=1 2>&1 | tee -a time-of-build9.log
sleep 1h
done
