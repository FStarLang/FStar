import re
import subprocess
from enum import Enum
from tabulate import tabulate

tests_path = '..' # '../FStar/examples/tactics'
fstar_path = '../../bin/fstar.exe' # relative to tests_path

# all_modules = [('Poly', 'CanonCommSemiring', ['lemma_poly_multiply_lemma', 'lemma_poly_multiply_canon', 'lemma_poly_reduce']),
#                ('CanonCommMonoid', 'CanonCommMonoid', ['lem0', 'lem1', 'sep_logic'])]

class Config(Enum):
    interp = 1
    native = 2
    smt = 3

all_modules = \
    [('bench/Poly1', Config.smt, 'CanonCommSemiring', ['lemma_poly_multiply_smt']),
     ('bench/Poly2', Config.smt, 'CanonCommSemiring', ['lemma_poly_multiply_smt_manual']),
     ('bench/Poly3', Config.interp, 'CanonCommSemiring', ['lemma_poly_multiply_canon']),
     ('bench/Poly4', Config.native, 'CanonCommSemiring', ['lemma_poly_multiply_canon_native'])
    ]

time_regex = re.compile(r'Checked let (?P<lemma>[a-zA-Z0-9\._]+).* in (?P<time>\d+) milliseconds\n')
error_regex = re.compile(r'(Error \d+)')

def run_fstar(module, options):
    result = subprocess.run([fstar_path, *options, module+'.fst'], cwd=tests_path, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode != 0:
        print('STDOUT ' + result.stdout.decode('utf-8'))
        print('STDERR ' + result.stderr.decode('utf-8'))
    return result

def gen_native_plugin(module_name):
    options = ['--codegen', 'Plugin', '--extract', module_name]
    return run_fstar(module_name, options)

def format_table(module_name, times, seed, config, errors, tablefmt, include_headers):
    if include_headers:
        headers = ['Module', 'Lemma', 'Config', 'Seed', 'Result', 'Time (ms)']
    else:
        headers = []
    if errors:
        result = 'Failed'
    else:
        result = 'Success'
    rows = [(module_name, t[0], config.name, seed, result, t[1]) for t in times]
    if rows:
        return tabulate(rows, headers, tablefmt=tablefmt)
    else:
        return ''

def concat_tables(tables):
    if len(tables) == 1:
        return tables[0]
    else:
        table = '\n'.join(tables[0].split('\n')[:-1] + ['\n'])
        for t in tables[1:-1]:
            table += '\n'.join(t.split('\n')[4:-1] + ['\n'])
        table += '\n'.join(tables[-1].split('\n')[4:] + ['\n'])
        return table


def run_tests ():
    tables = []

    # this will delete the contents of tactic_benchmarks.txt
    # open('tactic_benchmarks.txt', 'w').close()

    for seed in range(0,101):
        for test in all_modules:
            module_name, config, tac_module_name, lemmas = test

            print('Checking ' + module_name + ' with tactics from ' + tac_module_name + ' in ' + config.name + ' (z3seed ' + str(seed) + ')')

            if (config in [Config.interp, Config.smt]):
                # Running interpreted tactic
                results = run_fstar(module_name, ['--z3seed', str(seed)])

            elif (config is Config.native):
                # Running native tactics
                # gen_native_plugin(tac_module_name)
                results = run_fstar(module_name, ['--z3seed', str(seed), '--load', tac_module_name])

            times = re.findall(time_regex, results.stdout.decode('utf-8'))
            times = list(filter((lambda x: x[0] in lemmas), times))
            errors = re.findall(error_regex, results.stderr.decode('utf-8'))

            table_plain = format_table(module_name, times, seed, config, errors, 'jira', False)
            # table_latex = format_table(module_name, times, seed, config, errors, 'latex', True)
            if table_plain:
                with open('tactic_benchmarks.txt', 'a') as f:
                    f.write(table_plain + '\n')
                # tables += [table_latex]

    # with open('tactics_benchmarks.tex', 'w') as f:
    #     f.write(concat_tables(tables))


run_tests ()
