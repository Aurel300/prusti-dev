#!/usr/bin/env python3

import sys
if sys.version_info[0] < 3:
    print('You need to run this script with Python 3.')
    sys.exit(1)

import os
import platform
import subprocess
import glob
import time 
import signal

BENCHMARK_RUNS = 10
CLOSURE_TESTS_BASEDIR = "prusti-tests/tests/verify/pass/closures/"
CLOSURE_TESTS_PASS = [
  "basic.rs",
  "call-desc.rs",
  "ghost_pred.rs",
  "invariant.rs",
  "outer.rs",
  "thesis-1.rs",
  "types.rs",
  "views.rs",

  "closure-examples/all.rs",
  "closure-examples/any.rs",
  "closure-examples/blameassgn.rs",
  "closure-examples/counter.rs",
  "closure-examples/delegation.rs",
  "closure-examples/map_vec.rs",
  "closure-examples/option_map.rs",
  "closure-examples/repeat_with_n.rs",
  "closure-examples/result_uoe.rs",
]
CLOSURE_TESTS_FAIL = [
  "closure-examples/any_err.rs",
  "closure-examples/blameassgn_err.rs",
  "closure-examples/counter_err.rs",
  "closure-examples/option_map_err.rs",
]

def default_linux_java_loc():
    if os.path.exists('/usr/lib/jvm/default-java'):
        return '/usr/lib/jvm/default-java'
    elif os.path.exists('/usr/lib/jvm/default'):
        return '/usr/lib/jvm/default'
    report("Could not determine default java location.")

def get_var_or(name, default):
    """If environment variable `name` set, return its value or `default`."""
    if name in os.environ:
        return os.environ[name]
    else:
        return default

def get_linux_env():
    """Get environment variables for Linux."""
    java_home = get_var_or('JAVA_HOME', default_linux_java_loc())
    variables = [
        ('JAVA_HOME', java_home),
        ('RUST_TEST_THREADS', '1'),
    ]
    if os.path.exists(java_home):
        ld_library_path = None
        for root, _, files in os.walk(java_home):
            if 'libjvm.so' in files:
                ld_library_path = root
                break
        if ld_library_path is None:
            report("could not find libjvm.so in {}", java_home)
        else:
            variables.append(('LD_LIBRARY_PATH', ld_library_path))
    viper_home = get_var_or('VIPER_HOME', os.path.abspath('viper_tools/backends'))
    if os.path.exists(viper_home):
        variables.append(('VIPER_HOME', viper_home))
    z3_exe = os.path.abspath(os.path.join(viper_home, '../z3/bin/z3'))
    if os.path.exists(z3_exe):
        variables.append(('Z3_EXE', z3_exe))
    return variables

def set_env_variables(env, variables):
    for name, value in variables:
        if name not in env:
            env[name] = value
        elif name in ("PATH", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"):
            env[name] += ":" + value

def get_env():
    env = os.environ.copy()
    set_env_variables(env, get_linux_env())
    env["PRUSTI_USE_MORE_COMPLETE_EXHALE"] = "false"
    return env

def measure_prusti_time(input_path, env):
    prusti_rustc_exe = os.path.join(os.path.dirname(os.path.realpath(sys.argv[0])), "target", "debug", "prusti-rustc")
    start_time = time.perf_counter()
    code = subprocess.run(
        [prusti_rustc_exe, "--edition=2018", input_path],
        env=env,
        stderr=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL
    ).returncode
    end_time = time.perf_counter()
    elapsed = end_time - start_time
    return (code, elapsed)

env = get_env()
print(env)

print("")
print("starting benchmark...")
print(str(BENCHMARK_RUNS) + " runs per case")
print(str(len(CLOSURE_TESTS_PASS)) + " positive cases")
print(str(len(CLOSURE_TESTS_FAIL)) + " negative cases")
print("")
sys.stdout.flush()

for test in CLOSURE_TESTS_PASS:
    i = 0
    while i < BENCHMARK_RUNS:
        (code, elapsed) = measure_prusti_time(CLOSURE_TESTS_BASEDIR + test, env)
        if code != 0:
            print("FLAKY: {}".format(test))
            sys.stdout.flush()
            continue
        i += 1
        print("{},{}".format(test, elapsed))
        sys.stdout.flush()

for test in CLOSURE_TESTS_FAIL:
    i = 0
    while i < BENCHMARK_RUNS:
        (code, elapsed) = measure_prusti_time(CLOSURE_TESTS_BASEDIR + test, env)
        if code != 1:
            print("FLAKY: {}".format(test))
            sys.stdout.flush()
            continue
        i += 1
        print("{},{}".format(test, elapsed))
        sys.stdout.flush()
