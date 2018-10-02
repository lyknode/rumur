#!/usr/bin/env python3

import json, os, platform, re, shutil, subprocess, sys, tempfile, unittest

RUMUR_BIN = os.path.abspath(os.environ.get('RUMUR', 'rumur/rumur'))
RUMUR_AST_DUMP_BIN = os.path.abspath(os.environ.get('RUMUR_AST_DUMP',
  'ast-dump/rumur-ast-dump'))
CC = os.environ.get('CC', subprocess.check_output(['which', 'cc'],
  universal_newlines=True).strip())

try:
  VALGRIND = subprocess.check_output(['which', 'valgrind'],
    universal_newlines=True).strip()
except subprocess.CalledProcessError:
  VALGRIND = None

def valgrind_wrap(args: [str]) -> [str]:
  assert VALGRIND is not None
  return [VALGRIND, '--leak-check=full', '--show-leak-kinds=all',
    '--error-exitcode=42'] + args

X86_64 = platform.machine() == 'x86_64'

def run(args):
  p = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  stdout, stderr = p.communicate()
  return p.returncode, stdout.decode('utf-8', 'replace'), stderr.decode('utf-8', 'replace')

class TemporaryDirectory(object):

  def __init__(self):
    self.tmp = None

  def __enter__(self):
    self.tmp = tempfile.mkdtemp()
    return self.tmp

  def __exit__(self, *_):
    if self.tmp is not None:
      shutil.rmtree(self.tmp)

class Tests(unittest.TestCase):
  pass

def parse_test_options(model: str):
  option = {}

  # Check for special lines at the start of the current model overriding the
  # defaults.
  with open(model, 'rt') as f:
    for line in f:
      m = re.match(r'\s*--\s*(?P<key>[a-zA-Z_]\w*)\s*:(?P<value>.*)$', line)
      if m is None:
        break
      key = m.group('key')
      value = m.group('value').strip()
      option[key] = eval(value)

  return option

def test_template(self, model: str, optimised: bool, debug: bool,
    valgrind: bool):

  # Default options to use for this test.
  option = {
    'rumur_flags':[], # Flags to pass to rumur when generating the checker.
    'rumur_exit_code':0, # Expected exit status of rumur.
    'c_flags':None, # Flags to pass to cc when compiling.
    'ld_flags':None, # Flags to pass to cc last.
    'c_exit_code':0, # Expected exit status of cc.
    'checker_exit_code':0, # Expected exit status of the checker.
  }

  option.update(parse_test_options(model))

  with TemporaryDirectory() as tmp:

    model_c = os.path.join(tmp, 'model.c')
    rumur_flags = ['--output', model_c, model]
    if debug:
      rumur_flags.append('--debug')
    args = [RUMUR_BIN] + rumur_flags + option['rumur_flags']
    if valgrind:
      args = valgrind_wrap(args)
    ret, stdout, stderr = run(args)
    if valgrind:
      if ret == 42:
        sys.stdout.write(stdout)
        sys.stderr.write(stderr)
      self.assertNotEqual(ret, 42)
      return
    if ret != option['rumur_exit_code']:
      sys.stdout.write(stdout)
      sys.stderr.write(stderr)
    self.assertEqual(ret, option['rumur_exit_code'])

    # If model generation was supposed to fail, we're done.
    if option['rumur_exit_code'] != 0:
      return

    if option['c_flags'] is None:
      cflags = ['-std=c11']
      if X86_64:
        cflags.append('-mcx16')
      if optimised:
        cflags.extend(['-O3', '-fwhole-program'])
    else:
      cflags = option['c_flags']

    if option['ld_flags'] is None:
      ldflags = ['-lpthread']
    else:
      ldflags = []

    model_bin = os.path.join(tmp, 'model.bin')
    args = [CC] + cflags + ['-o', model_bin, model_c] + ldflags
    ret, stdout, stderr = run(args)
    if ret != option['c_exit_code']:
      sys.stdout.write(stdout)
      sys.stderr.write(stderr)
    self.assertEqual(ret, option['c_exit_code'])

    # If compilation was supposed to fail, we're done.
    if option['c_exit_code'] != 0:
      return

    ret, stdout, stderr = run([model_bin])
    if ret != option['checker_exit_code']:
      sys.stdout.write(stdout)
      sys.stderr.write(stderr)
    self.assertEqual(ret, option['checker_exit_code'])

def test_ast_dumper_template(self, model: str, valgrind: bool):

  with TemporaryDirectory() as tmp:

    model_xml = os.path.join(tmp, 'model.xml')
    ad_flags = ['--output', model_xml, model]
    args = [RUMUR_AST_DUMP_BIN] + ad_flags
    if valgrind:
      args = valgrind_wrap(args)
    ret, stdout, stderr = run(args)
    if valgrind:
      if ret == 42:
        sys.stdout.write(stdout)
        sys.stderr.write(stderr)
      self.assertNotEqual(ret, 42)
      # Remainder of the test is unnecessary, because we will already test this
      # in the version of this test when valgrind=False.
      return
    if ret != 0:
      sys.stdout.write(stdout)
      sys.stderr.write(stderr)
    self.assertEqual(ret, 0)

    # See if we have xmllint
    ret, _, _ = run(['which', 'xmllint'])
    if ret != 0:
      self.skipTest('xmllint not available for validation')

    # Validate the XML
    ret, stdout, stderr = run(['xmllint', '--noout', model_xml])
    if ret != 0:
      with open(model_xml, 'rt') as f:
        sys.stderr.write('Failed to validate:\n{}\n'.format(f.read()))
      sys.stdout.write(stdout)
      sys.stderr.write(stderr)
    self.assertEqual(ret, 0)

def test_cmurphi_example_template(self, model: str, outcome: bool):

  with TemporaryDirectory() as tmp:

    model_c = os.path.join(tmp, 'model.c')
    ret, stdout, stderr = run([RUMUR_BIN, '--output', model_c, model])
    if ret != 0:
      sys.stdout.write(stdout)
      sys.stderr.write(stderr)
    self.assertEqual(ret, 0)

    cflags = ['-std=c11', '-O3', '-fwhole-program']
    if X86_64:
      cflags.append('-mcx16')
    model_bin = os.path.join(tmp, 'model.bin')
    ret, stdout, stderr = run([CC] + cflags + ['-o', model_bin, model_c,
      '-lpthread'])
    if ret != 0:
      sys.stdout.write(stdout)
      sys.stderr.write(stderr)
    self.assertEqual(ret, 0)

    ret, stdout, stderr = run([model_bin])
    if (ret == 0) != outcome:
      sys.stdout.write(stdout)
      sys.stderr.write(stderr)
    self.assertEqual(ret == 0, outcome)

def test_ast_dumper_cmurphi_example_template(self, model: str):

  with TemporaryDirectory() as tmp:

    model_xml = os.path.join(tmp, 'model.xml')
    ad_flags = ['--output', model_xml, model]
    args = [RUMUR_AST_DUMP_BIN] + ad_flags
    ret, stdout, stderr = run(args)
    if ret != 0:
      sys.stdout.write(stdout)
      sys.stderr.write(stderr)
    self.assertEqual(ret, 0)

    # See if we have xmllint
    ret, _, _ = run(['which', 'xmllint'])
    if ret != 0:
      self.skipTest('xmllint not available for validation')

    # Validate the XML
    ret, stdout, stderr = run(['xmllint', '--noout', model_xml])
    if ret != 0:
      with open(model_xml, 'rt') as f:
        sys.stderr.write('Failed to validate:\n{}\n'.format(f.read()))
      sys.stdout.write(stdout)
      sys.stderr.write(stderr)
    self.assertEqual(ret, 0)

def main(argv):

  if not os.path.isfile(RUMUR_BIN):
    sys.stderr.write('{} not found\n'.format(RUMUR_BIN))
    return -1

  # Find test cases in subdirectories.

  root = os.path.dirname(os.path.abspath(__file__))
  for m in (os.path.join(root, m) for m in os.listdir(root)):

    if not os.path.isfile(m) or os.path.splitext(m)[1] != '.m':
      continue

    m_name = os.path.basename(m)

    for optimised in (False, True):
      for debug in (False, True):
        for valgrind in (False, True):

          if valgrind and VALGRIND is None:
            # Valgrind unavailable
            continue

          test_name = re.sub(r'[^\w]', '_', 'test_{}{}{}{}'.format(
            'debug_' if debug else '',
            'optimised_' if optimised else 'unoptimised_',
            'valgrind_' if valgrind else '', m_name))

          if hasattr(Tests, test_name):
            raise Exception('{} collides with an existing test name'.format(m))

          setattr(Tests, test_name,
            lambda self, model=m, o=optimised, d=debug, v=valgrind:
              test_template(self, model, o, d, v))

    for valgrind in (False, True):

      if valgrind and VALGRIND is None:
        # Valgrind unavailable.
        continue

      # Now we want to add an AST dumper test, but skip this if the input model is
      # expected to fail.
      option = { 'rumur_exit_code':0 }
      option.update(parse_test_options(m))
      if not valgrind and option['rumur_exit_code'] != 0:
        continue

      test_name = re.sub(r'[^\w]', '_', 'test_ast_dumper_{}{}'.format(
        'valgrind_' if valgrind else '', m_name))

      if hasattr(Tests, test_name):
        raise Exception('{} collides with an existing test name'.format(m))

      setattr(Tests, test_name,
        lambda self, model=m, v=valgrind: test_ast_dumper_template(self, model, v))

  # If the user has told us where a copy of the CMurphi source is, test some of
  # the example models distributed with CMurphi.
  CMURPHI_DIR = os.environ.get('CMURPHI_DIR')
  if CMURPHI_DIR is not None:

    models = (
      # (Model path,           expected to pass?)
      ('ex/mux/2_peterson.m',  True),
      ('ex/mux/dek.m',         True),
      ('ex/mux/mcslock1.m',    True),
      ('ex/mux/mcslock2.m',    True),
      ('ex/others/arbiter.m',  False),
      ('ex/others/dp4.m',      True),
      ('ex/others/dpnew.m',    True),
      ('ex/sym/mcslock1.m',    True),
      ('ex/sym/mcslock2.m',    True),
      ('ex/tmp/scalarset.m',   True),
      ('ex/toy/down.m',        False),
      ('ex/toy/lin.m',         False),
      ('ex/toy/pingpong.m',    True),
      ('ex/toy/sets.m',        False),
      ('ex/toy/sort5.m',       False),
    )

    for path, outcome in models:
      fullpath = os.path.abspath(os.path.join(CMURPHI_DIR, path))

      test_name = re.sub(r'[^\w]', '_', 'test_cmurphi_example_{}'.format(path))

      if hasattr(Tests, test_name):
        raise Exception('{} collides with an existing test name'.format(path))

      setattr(Tests, test_name,
        lambda self, model=fullpath, outcome=outcome:
          test_cmurphi_example_template(self, model, outcome))

      test_name = re.sub(r'[^\w]', '_', 'test_ast_dumper_cmurphi_example_{}'
        .format(path))

      if hasattr(Tests, test_name):
        raise Exception('{} collides with an existing test name'.format(path))

      setattr(Tests, test_name,
        lambda self, model=fullpath:
          test_ast_dumper_cmurphi_example_template(self, model))

  unittest.main()

if __name__ == '__main__':
  sys.exit(main(sys.argv))
