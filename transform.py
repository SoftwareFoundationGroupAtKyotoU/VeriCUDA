#!/usr/bin/python

import re
import sys

key_to_func = {
    'requires':       'declare_precondition',
    'ensures':        'declare_postcondition',
    'ghost':          'declare_logic_param',
    'loop invariant': 'declare_invariant',
    'assert':         'assert',
}

inv = 'loop invariant'
keys = '|'.join(key_to_func.keys())

def template():
    res = ''
    f = open('template.cu', 'r')
    for line in f:
        res += line
    f.close()
    return res

def add_assn(assn, i, j):
    if i in assn:
        assn[i] = assn[i] + ', "' + j.strip() + '"'
    else:
        assn[i] = '"' + j.strip() + '"'

def transform_assn(s):
    l1 = re.split(keys, s)
    l2 = re.findall(keys, s)
    assn = {}
    for i, j in zip(l2, l1[1:]):
        j = j.strip().strip(';')
        j = j.replace('\\forall', 'forall').replace('\\exists', 'exists')
        add_assn(assn, i, j)
    res = ''
    for i, j in assn.items():
        if i != inv:
            res += key_to_func[i] + '(' + j + ');\n'
    return res, assn[inv] if inv in assn else None

def attach_inv(s, invariant):
    if not invariant:
        return s
    idx = s.find('{')
    if idx == -1:
        raise Exception('loop not found')
    return s[:idx] + '{\n' + key_to_func[inv] + '(' + invariant + ');' + s[idx+1:]

def main():
    s = sys.stdin.read()
    s = s.replace('\n', '__endl__')

    s = s.replace('__global__', '__attribute__((global))')
    s = s.replace('__shared__', '__attribute__((shared))')
    l1 = re.split('/\*@.*?\*/|//@.*?__endl__', s)
    l2 = re.findall('/\*@.*?\*/|//@.*?__endl__', s)

    res = template() + l1[0]
    for i, j in zip(l2, l1[1:]):
        i = i.replace('__endl__', '\n').strip().strip('*/').strip()
        i, inv = transform_assn(i)
        res += i + attach_inv(j, inv)
    res = res.replace('__endl__', '\n')
    print res

main()
