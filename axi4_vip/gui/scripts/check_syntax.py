#!/usr/bin/env python3
"""Check Python syntax of vip_environment_generator.py"""

import os
import sys

script_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(script_dir, "..", "src")
generator_file = os.path.join(src_dir, "vip_environment_generator.py")

try:
    with open(generator_file, 'r') as f:
        code = f.read()
    compile(code, generator_file, 'exec')
    print('✅ Python syntax: OK - No errors found')
    print(f'   File: {generator_file}')
    print(f'   Size: {len(code)} bytes')
    print(f'   Lines: {code.count(chr(10))} lines')
    sys.exit(0)
except SyntaxError as e:
    print(f'❌ Syntax error at line {e.lineno}: {e.msg}')
    if e.text:
        print(f'   Problem text: {repr(e.text)[:100]}')
    print(f'   File: {generator_file}')
    sys.exit(1)