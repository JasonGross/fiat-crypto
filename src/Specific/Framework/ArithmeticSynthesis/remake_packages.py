#!/usr/bin/env python
from __future__ import with_statement
import re, os
import io

PACKAGE_NAMES = [('../CurveParameters.v', [])]
CP_LIST = ['../CurveParametersPackage.v']
CP_BASE_LIST = ['../CurveParametersPackage.v', 'BasePackage.v']
CP_BASE_DEFAULTS_LIST = ['../CurveParametersPackage.v', 'BasePackage.v', 'DefaultsPackage.v']
NORMAL_PACKAGE_NAMES = [('Base.v', (CP_LIST, None)),
                        ('Defaults.v', (CP_BASE_LIST, None)),
                        ('Freeze.v', (CP_BASE_LIST, None)),
                        ('Ladderstep.v', (CP_BASE_DEFAULTS_LIST, None)),
                        ('Karatsuba.v', (CP_BASE_DEFAULTS_LIST, 'goldilocks')),
                        ('Montgomery.v', (CP_BASE_DEFAULTS_LIST, 'montgomery'))]
ALL_FILE_NAMES = PACKAGE_NAMES + NORMAL_PACKAGE_NAMES # PACKAGE_CP_NAMES + WITH_CURVE_BASE_NAMES + ['../ReificationTypes.v']
CONFIGS = ('goldilocks', 'montgomery')

EXCLUDES = ('constr:((wt_divides_chain, wt_divides_chains))', )

contents = {}
lines = {}
fns = {}

PY_FILE_NAME = os.path.basename(__file__)

def init_contents(lines=lines, contents=contents):
    for fname, _ in ALL_FILE_NAMES:
        with open(fname, 'r') as f:
            contents[fname] = f.read()
    lines.update(dict((k, v.split('\n')) for k, v in contents.items()))

def init_fns(lines=lines, fns=fns):
    header = 'Ltac pose_'
    for fname, _ in ALL_FILE_NAMES:
        stripped_lines = [i.strip() for i in lines[fname]]
        fns[fname] = [(name, args.strip())
                      for line in stripped_lines
                      if line.startswith(header)
                      for name, args in re.findall('Ltac pose_([^ ]*' + ') ([A-Za-z0-9_\' ]*' + ')', line.strip())]

def get_file_root(folder=os.path.dirname(__file__), filename='Makefile'):
    dir_path = os.path.realpath(folder)
    while not os.path.isfile(os.path.join(dir_path, filename)) and dir_path != '/':
        dir_path = os.path.realpath(os.path.join(dir_path, '..'))
    if not os.path.isfile(os.path.join(dir_path, filename)):
        print('ERROR: Could not find Makefile in the root of %s' % folder)
        raise Exception
    return dir_path

def modname_of_file_name(fname):
    assert(fname[-2:] == '.v')
    return 'Crypto.' + os.path.normpath(os.path.relpath(os.path.realpath(fname), os.path.join(root, 'src'))).replace(os.sep, '.')[:-2]

def split_args(name, args_str, indent=''):
    args = [arg.strip() for arg in args_str.split(' ')]
    pass_args = [arg for arg in args if arg.startswith('P_')]
    extract_args = [arg for arg in args if arg not in pass_args and arg != name]
    if name not in args:
        print('Error: %s not in %s' % (name, repr(args)))
        assert(name in args)
    assert(len(pass_args) + len(extract_args) + 1 == len(args))
    pass_args_str = ' '.join(pass_args)
    if pass_args_str != '': pass_args_str += ' '
    extract_args_str = ''
    nl_indent = ('\n%(indent)s  ' % locals())
    if len(extract_args) > 0:
        extract_args_str = nl_indent + nl_indent.join('let %s := Tag.get pkg TAG.%s in' % (arg, arg) for arg in extract_args)
    return args, pass_args, extract_args, pass_args_str, extract_args_str

def make_add_from_pose(name, args_str, indent='', only_if=None):
    args, pass_args, extract_args, pass_args_str, extract_args_str = split_args(name, args_str, indent=indent)
    ret = r'''%(indent)sLtac add_%(name)s pkg %(pass_args_str)s:=''' % locals()
    body = r'''%(extract_args_str)s
%(indent)s  let %(name)s := fresh "%(name)s" in
%(indent)s  ''' % locals()
    body += r'''let %(name)s := pose_%(name)s %(args_str)s in
%(indent)s  Tag.update pkg TAG.%(name)s %(name)s''' % locals()
    if only_if is None:
        ret += body + '.\n'
    else:
        body = body.strip('\n ').replace('\n', '\n                 ')
        ret += r'''
%(indent)s  if_%(only_if)s
%(indent)s    ltac:(fun _ => %(body)s)
%(indent)s    ltac:(fun _ => pkg)
%(indent)s    ().''' % locals()
    return ret

def make_add_all(fname, indent=''):
    modname, ext = os.path.splitext(os.path.basename(fname))
    all_items = [(name, split_args(name, args_str, indent=indent)) for name, args_str in fns[fname]]
    all_pass_args = []
    for name, (args, pass_args, extract_args, pass_args_str, extract_args_str) in all_items:
        for arg in pass_args:
            if arg not in all_pass_args: all_pass_args.append(arg)
    all_pass_args_str = ' '.join(all_pass_args)
    if all_pass_args_str != '': all_pass_args_str += ' '
    ret = r'''%(indent)sLtac add_%(modname)s_package pkg %(all_pass_args_str)s:=''' % locals()
    nl_indent = ('\n%(indent)s  ' % locals())
    ret += nl_indent + nl_indent.join('let pkg := add_%s pkg %sin' % (name, pass_args_str)
                                      for name, (args, pass_args, extract_args, pass_args_str, extract_args_str) in all_items)
    ret += nl_indent + 'pkg.\n'
    return ret

def make_if(name, indent=''):
    ret = r'''%(indent)sLtac if_%(name)s pkg tac_true tac_false arg :=
%(indent)s  let %(name)s := Tag.get pkg TAG.%(name)s in
%(indent)s  let %(name)s := (eval vm_compute in (%(name)s : bool)) in
%(indent)s  lazymatch %(name)s with
%(indent)s  | true => tac_true arg
%(indent)s  | false => tac_false arg
%(indent)s  end.
''' % locals()
    return ret

def write_if_changed(fname, value):
    if os.path.isfile(fname):
        with open(fname, 'r') as f:
            old_value = f.read()
        if old_value == value: return
    value = unicode(value)
    print('Writing %s...' % fname)
    with io.open(fname, 'w', newline='\n') as f:
        f.write(value)

def do_replace(fname, headers, new_contents):
    lines = contents[fname].split('\n')
    ret = []
    for line in lines:
        if any(header in line for header in headers):
            ret.append(new_contents)
            break
        else:
            ret.append(line)
    ret = unicode('\n'.join(ret))
    write_if_changed(fname, ret)

def get_existing_tags(fname, deps):
    return set(name for dep in deps for name, args in fns[dep.replace('Package.v', '.v')])

def make_package(fname, deps, extra_modname_prefix='', prefix=None, add_package=True):
    py_file_name = PY_FILE_NAME
    existing_tags = get_existing_tags(fname, deps)
    full_mod = modname_of_file_name(fname)
    modname, ext = os.path.splitext(os.path.basename(fname))
    ret = (r'''(* This file is autogenerated from %(modname)s.v by %(py_file_name)s *)
Require Export %(full_mod)s.
Require Import Crypto.Specific.Framework.Packages.
Require Import Crypto.Util.TagList.
''' % locals())
    if prefix is not None:
        ret += prefix
    new_names = [name for name, args in fns[fname] if name not in existing_tags]
    if add_package and len(new_names) > 0:
        ret += (r'''

Module Make%(extra_modname_prefix)s%(modname)sPackage (PKG : PrePackage).
  Module Import Make%(extra_modname_prefix)s%(modname)sPackageInternal := MakePackageBase PKG.
''' % locals())
        for name in new_names:
            ret += ("\n  Ltac get_%s _ := get TAG.%s." % (name, name))
            ret += ("\n  Notation %s := (ltac:(let v := get_%s () in exact v)) (only parsing)." % (name, name))
        ret += ('\nEnd Make%(extra_modname_prefix)s%(modname)sPackage.\n' % locals())
    return ret

def make_tags(fname, deps):
    existing_tags = get_existing_tags(fname, deps)
    new_tags = [name for name, args in fns[fname] if name not in existing_tags]
    if len(new_tags) == 0: return ''
    names = ' | '.join(new_tags)
    return r'''Module TAG.
  Inductive tags := %s.
End TAG.
''' % names

def write_package(fname, pkg):
    pkg_name = fname[:-2] + 'Package.v'
    write_if_changed(pkg_name, pkg)
    
def update_CurveParameters(fname='../CurveParameters.v'):
    endline = contents[fname].strip().split('\n')[-1]
    assert(endline.startswith('End '))
    header = '(* Everything below this line autogenerated by %s *)' % PY_FILE_NAME
    assert(header in contents[fname])
    ret = '  %s' % header
    for name, args in fns[fname]:
        ret += '\n' + make_add_from_pose(name, args, indent='  ')
    ret += '\n' + make_add_all(fname, indent='  ')
    ret += endline
    prefix = ''
    for name in CONFIGS:
        prefix += '\n' + make_if(name, indent='')
    pkg = make_package(fname, [], prefix=prefix)
    do_replace(fname, (header,), ret)
    write_package(fname, pkg)

def make_normal_package(fname, deps, only_if=None):
    prefix = ''
    for dep in deps:
        prefix += 'Require Import %s.\n' % modname_of_file_name(dep)
    prefix += '\n' + make_tags(fname, deps)
    for name, args in fns[fname]:
        prefix += '\n' + make_add_from_pose(name, args, indent='', only_if=only_if)
    prefix += '\n' + make_add_all(fname, indent='')
    return make_package(fname, deps, prefix=prefix)

def update_normal_package(fname, deps, only_if=None):
    pkg = make_normal_package(fname, deps, only_if=only_if)
    write_package(fname, pkg)

root = get_file_root()
init_contents()
init_fns()
update_CurveParameters()
for fname, (deps, only_if) in NORMAL_PACKAGE_NAMES:
    update_normal_package(fname, deps, only_if=only_if)

##PACKAGE_CP_NAMES = ['Base.v']
##WITH_CURVE_BASE_NAMES = ['Freeze.v', 'Karatsuba.v', 'Defaults.v', 'Ladderstep.v']
##ALL_FILE_NAMES = PACKAGE_NAMES + PACKAGE_CP_NAMES + WITH_CURVE_BASE_NAMES + ['../ReificationTypes.v']
##CONFIGS = ('goldilocks', 'montgomery')
##           
##contents = {}
##for fname in ALL_FILE_NAMES:
##    with open(fname, 'r') as f:
##        contents[fname] = f.read()
##
##lines = dict((k, v.split('\n')) for k, v in contents.items())
##
##EXCLUDES = ('constr:((wt_divides_chain, wt_divides_chains))', )
##
##fns = {}
##header = 'Ltac pose_'
##for fname in ALL_FILE_NAMES:
##    stripped_lines = [i.strip() for i in lines[fname]]
##    fns[fname] = [(name, args.strip())
##                  for line in stripped_lines
##                  if line.startswith(header)
##                  for name, args in re.findall('Ltac pose_([^ ]*' + ') ([A-Za-z0-9_\' ]*' + ')', line.strip())]
##
##def get_file_root(folder=os.path.dirname(__file__), filename='Makefile'):
##    dir_path = os.path.realpath(folder)
##    while not os.path.isfile(os.path.join(dir_path, filename)) and dir_path != '/':
##        dir_path = os.path.realpath(os.path.join(dir_path, '..'))
##    if not os.path.isfile(os.path.join(dir_path, filename)):
##        print('ERROR: Could not find Makefile in the root of %s' % folder)
##        raise Exception
##    return dir_path
##
##root = get_file_root()
##
##def modname_of_file_name(fname):
##    assert(fname[-2:] == '.v')
##    return 'Crypto.' + os.path.normpath(os.path.relpath(os.path.realpath(fname), os.path.join(root, 'src'))).replace(os.sep, '.')[:-2]
##
##PY_FILE_NAME = os.path.basename(__file__)
##
##def make_package(fname, extra_modname_prefix='', prefix=None, add_package=True):
##    py_file_name = PY_FILE_NAME
##    full_mod = modname_of_file_name(fname)
##    modname, ext = os.path.splitext(os.path.basename(fname))
##    ret = (r'''(* This file is autogenerated from %(modname)s.v by %(py_file_name)s *)
##Require Export %(full_mod)s.
##''' % locals())
##    if prefix is not None:
##        ret += prefix
##    if add_package:
##        ret += (r'''
##Module Type %(extra_modname_prefix)s%(modname)sPrePackage.
##  Parameter %(extra_modname_prefix)s%(modname)s_package' : { T : _ & T }.
##  Parameter %(extra_modname_prefix)s%(modname)s_package : projT1 %(extra_modname_prefix)s%(modname)s_package'.
##End %(extra_modname_prefix)s%(modname)sPrePackage.
##
##Module Make%(extra_modname_prefix)s%(modname)sTest (PKG : %(extra_modname_prefix)s%(modname)sPrePackage).
##  Ltac get_Make%(extra_modname_prefix)s%(modname)sTest_package _ := eval hnf in PKG.%(extra_modname_prefix)s%(modname)s_package.
##  Ltac %(modname)s_reduce_proj x :=
##    eval cbv beta iota zeta in x.
##''' % locals())
##        terms = ', '.join(name for name, args in fns[fname])
##        for name, args in fns[fname]:
##            ret += ("\n  Ltac get_%s _ := let pkg := get_Make%s%sTest_package () in %s_reduce_proj (let '(%s) := pkg in %s)." % (name, extra_modname_prefix, modname, modname, terms, name))
##            ret += ("\n  Notation %s := (ltac:(let v := get_%s () in exact v)) (only parsing)." % (name, name))
##        ret += ('\nEnd Make%(extra_modname_prefix)s%(modname)sTest.\n' % locals())
##    return ret
##
##def do_replace(fname, headers, new_contents):
##    lines = contents[fname].split('\n')
##    ret = []
##    for line in lines:
##        if any(header in line for header in headers):
##            ret.append(new_contents)
##            break
##        else:
##            ret.append(line)
##    ret = unicode('\n'.join(ret))
##    if ret == contents[fname]: return
##    #raw_input((ret, ret == contents[fname]))
##    print('Writing %s...' % fname)
##    with io.open(fname, 'w', newline='\n') as f:
##        f.write(unicode(ret))
##
##def write_package(fname, pkg):
##    pkg_name = fname[:-2] + 'Package.v'
##    if os.path.isfile(pkg_name):
##        with open(pkg_name, 'r') as f:
##            existing_pkg = f.read()
##        if pkg == existing_pkg: return
##    pkg = unicode(pkg)
##    #raw_input(pkg)
##    print('Writing %s...' % pkg_name)
##    with io.open(pkg_name, 'w', newline='\n') as f:
##        f.write(pkg)
##
##for fname in PACKAGE_NAMES:
##    assert(fname == '../CurveParameters.v')
##    modname, ext = os.path.splitext(os.path.basename(fname))
##    close_modname = 'Fill' + modname
##    full_mod = modname_of_file_name(fname)
##    header = '(* Everything below this line autogenerated by %s *)' % PY_FILE_NAME
##    tactic = 'Ltac get_%s_package _ :=' % modname
##    get_make_val = '  %s\n  %s\n    %s' % (header, tactic, '\n    '.join('let %s := fresh "%s" in' % (name, name) for name, args in fns[fname]))
##    get_make_val += ('\n    ' + '\n    '.join('let %s := pose_%s %s in' % (name, name, args) for name, args in fns[fname]))
##    get_make_val += ('\n    constr:((%s)).' % ', '.join(name for name, args in fns[fname]))
##    get_make_val += (r'''
##
##  Ltac make_%(modname)s_package _ :=
##    lazymatch goal with
##    | [ |- { T : _ & T } ] => eexists
##    | [ |- _ ] => idtac
##    end;
##    let pkg := get_%(modname)s_package () in
##    exact pkg.
##
##  Ltac choose %(modname)s_pkg tac :=
##    lazymatch (eval hnf in %(modname)s_pkg) with
##''' % locals())
##    get_make_val += '    | (%s)\n' % ', '.join('?%s' % name for name, args in fns[fname])
##    get_make_val += '      => '
##    
##    get_make_val += '\n         '.join('let %s := (eval compute in (%s : bool)) in' % (i, i) for i in CONFIGS)
##    get_make_val += (r'''
##         tac %s
##    end.
##End %s.
##''' % (' '.join(CONFIGS), close_modname))
##    pkg = make_package(fname)
##    print(fname)
##    pkg = unicode(pkg)
##    do_replace(fname, (header, tactic), get_make_val)
##    write_package(fname, pkg)
##
##for fname in PACKAGE_CP_NAMES:
##    modname, ext = os.path.splitext(os.path.basename(fname))
##    full_mod = modname_of_file_name(fname)
##    full_cp_mod = modname_of_file_name('../CurveParameters.v')
##    cp_names = tuple(name for name, args in fns['../CurveParameters.v'])
##    #raw_input(cp_names)
##    prefix = (r'''
##Ltac get_ArithmeticSynthesis%(modname)s_package CurveParameters_pkg :=
##  lazymatch (eval hnf in CurveParameters_pkg) with
##''' % locals())
##    prefix += '  | (%s)\n' % ', '.join('?%s' % i for i in cp_names)
##    prefix += ('    => %s'
##               % '\n       '.join('let %s := fresh "%s" in' % (name, name) for name, args in fns[fname]))
##    prefix += ('\n       ' + '\n       '.join('let %s := pose_%s %s in' % (name, name, args) for name, args in fns[fname]))
##    prefix += ('\n       constr:((%s))' % ', '.join(name for name, args in fns[fname]))
##    prefix += ('\n  end.\n')
##    prefix += (r'''
##Ltac make_ArithmeticSynthesis%(modname)s_package CurveParameters_pkg :=
##  lazymatch goal with
##  | [ |- { T : _ & T } ] => eexists
##  | [ |- _ ] => idtac
##  end;
##  let pkg := get_ArithmeticSynthesis%(modname)s_package CurveParameters_pkg in
##  exact pkg.
##''' % locals())
##    pkg = make_package(fname, extra_modname_prefix='ArithmeticSynthesis', prefix=prefix)
##    print(fname)
##    pkg = unicode(pkg)
##    write_package(fname, pkg)
##
##    
##full_cp_mod = modname_of_file_name('../CurveParameters.v')
##full_base_mod = modname_of_file_name('Base.v')
##cp_names = tuple(name for name, args in fns['../CurveParameters.v'])
##base_names = tuple(name for name, args in fns['Base.v'])
##
##for fname in WITH_CURVE_BASE_NAMES:
##    modname, ext = os.path.splitext(os.path.basename(fname))
##    full_mod = modname_of_file_name(fname)
##    #raw_input(cp_names)
##    prefix = (r'''
##
##Local Ltac combine_pkgs CurveParameters_pkg ArithmeticSynthesisBase_pkg :=
##  let CurveParameters_pkg := (eval hnf in CurveParameters_pkg) in
##  let ArithmeticSynthesisBase_pkg := (eval hnf in ArithmeticSynthesisBase_pkg) in
##  constr:((CurveParameters_pkg, ArithmeticSynthesisBase_pkg)).
##''' % locals())
##    for name, args in fns[fname]:
##        if name[-1] != "'": raw_input(name)
##        args = args.split(' ')
##        prefix += ((r'''
##Ltac pose_%s CurveParameters_pkg ArithmeticSynthesisBase_pkg %s :=
##  let pkg := combine_pkgs CurveParameters_pkg ArithmeticSynthesisBase_pkg in
##  lazymatch pkg with
##  | ((%s), (%s))
##'''
##                 % (name[:-1],
##                    ' '.join(arg for arg in args if arg.startswith('P_') or arg.endswith('_sig') or arg == name[:-1]),
##                    ', '.join('?%s' % i for i in cp_names),
##                    ', '.join('?%s' % i for i in base_names))).replace('  :=', ' :='))
##        prefix += (r'''    => pose_%s %s
##  end.
##''' % (name, ' '.join(args)))
##    pkg = make_package(fname, extra_modname_prefix='ArithmeticSynthesis', prefix=prefix, add_package=False)
##    print(fname)
##    pkg = unicode(pkg)
##    write_package(fname, pkg)
##
##def fix_reif_types():
##    orig = contents['../ReificationTypes.v']
##    new_val = (r'''  let pkg := combine_pkgs CurveParameters_pkg ArithmeticSynthesisBase_pkg in
##  lazymatch pkg with
##  | ((%s), (%s))'''
##               % (', '.join('?%s' % i for i in cp_names),
##                  ', '.join('?%s' % i for i in base_names)))
##    find = re.compile(r'''  let pkg := combine_pkgs CurveParameters_pkg ArithmeticSynthesisBase_pkg in
##  lazymatch pkg with
##  .*''', flags=re.MULTILINE)
##    assert(len(find.findall(orig)) == 1)
##    ret = unicode(find.sub(new_val, orig))
##    print('../ReificationTypes.v')
##    if ret != orig:
##        with io.open('../ReificationTypes.v', 'w', newline='\n') as f:
##            f.write(ret)
##
##fix_reif_types()    
####
####    ret = r'''Require Import %s.
####
####Local Ltac combine_pkgs CurveParameters_pkg ArithmeticSynthesisBase_pkg :=
####  let CurveParameters_pkg := (eval hnf in CurveParameters_pkg) in
####  let ArithmeticSynthesisBase_pkg := (eval hnf in ArithmeticSynthesisBase_pkg) in
####  constr:((CurveParameters_pkg, ArithmeticSynthesisBase_pkg)).
####
####Ltac get_ArithmeticSynthesisBase_package CurveParameters_pkg :=
####  lazymatch (eval hnf in CurveParameters_pkg) with
####  | (%s)''' % ', '.join('?%s' % i for i in cp_names))
####
####    with open(fname[:-2] + 'Package.v', 'w') as f:
####
####print(r'''Ltac get_ArithmeticSynthesisBase_package CurveParameters_pkg :=
####  lazymatch (eval hnf in CurveParameters_pkg) with
####  | (%s)''' % ', '.join('?%s' % i for i in cp_names))
####print('    => %s'
####    % '\n       '.join('let %s := fresh "%s" in' % (name, name) for name, args in fns))
####print('       ' + '\n       '.join('let %s := pose_%s %s in' % (name, name, args) for name, args in fns))
####print('       constr:((%s))' % ', '.join(name for name, args in fns))
####print('  end.')
####print(r'''
####Ltac make_ArithmeticSynthesisBase_package CurveParameters_pkg :=
####  lazymatch goal with
####  | [ |- { T : _ & T } ] => eexists
####  | [ |- _ ] => idtac
####  end;
####  let pkg := get_ArithmeticSynthesisBase_package CurveParameters_pkg in
####  exact pkg.
####
####Module Type ArithmeticSynthesisBasePrePackage.
####  Parameter ArithmeticSynthesisBase_package' : { T : _ & T }.
####  Parameter ArithmeticSynthesisBase_package : projT1 ArithmeticSynthesisBase_package'.
####End ArithmeticSynthesisBasePrePackage.
####
####Module MakeArithmeticSynthesisBaseTest (PKG : ArithmeticSynthesisBasePrePackage).
####  Ltac get_MakeArithmeticSynthesisBaseTest_package _ := eval hnf in PKG.ArithmeticSynthesisBase_package.
####  Ltac AS_reduce_proj x :=
####    eval cbv beta iota zeta in x.
####''')
####terms = ', '.join(name for name, args in fns)
####for name, args in fns:
####    print("  Ltac get_%s _ := let pkg := get_MakeArithmeticSynthesisBaseTest_package () in AS_reduce_proj (let '(%s) := pkg in %s)." % (name, terms, name))
####    print("  Notation %s := (ltac:(let v := get_%s () in exact v)) (only parsing)." % (name, name))
####print('End MakeArithmeticSynthesisBaseTest.')
