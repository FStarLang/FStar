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
    smt_1 = 3
    smt_2 = 4
    smt_3 = 5
    interp2 = 6

all_modules = \
    [('Poly1', Config.smt_1, 'CanonCommSemiring', ['lemma_poly_multiply']),
     ('Poly1', Config.smt_2, 'CanonCommSemiring', ['lemma_poly_multiply']),
     ('Poly1', Config.smt_3, 'CanonCommSemiring', ['lemma_poly_multiply']),
     ('Poly2', Config.interp, 'CanonCommSemiring', ['lemma_poly_multiply']),
     ('Poly2', Config.native, 'CanonCommSemiring', ['lemma_poly_multiply']),
     ('Poly2', Config.interp2, 'CanonCommSemiring', ['lemma_poly_multiply']),
    ]

time_regex = re.compile(r'Checked let (?P<lemma>[a-zA-Z0-9\._]+).* in (?P<time>\d+) milliseconds\n')
smt_time_regex = re.compile(r'in (?P<time>\d+) milliseconds with fuel')
tactic_time_regex = re.compile(r'FStar.Tactics.Effect.TAC Prims.unit ran in (?P<time>\d+) ms') # this is overly specific for the general case
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

def format_table(module_name, checking_time, smt_time, tactic_time, seed, config, errors, tablefmt, include_headers):
    if include_headers:
        headers = ['Module', 'Lemma', 'Config', 'z3seed', 'Result', 'Time (ms)', 'SMT (ms)', 'Tactics (ms)']
    else:
        headers = []
    if errors:
        result = 'Failed'
    else:
        result = 'Success'
    # rows = [(module_name, t[0], config.name, seed, result, t[1]) for t in times]
    rows = [(module_name, checking_time[0], config.name, seed, result, checking_time[1], smt_time, tactic_time)]
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
    open('tactic_benchmarks.txt', 'w').close()

    for seed in range(0,150,1):
        for test in all_modules:
            module_name, config, tac_module_name, lemmas = test

            print('Checking ' + module_name + ' with tactics from ' + tac_module_name + ' in ' + config.name + ' (z3seed ' + str(seed) + ')')


            if (config in [Config.smt_1, Config.smt_2, Config.smt_3]):
                # Running SMT only
                results = run_fstar(module_name, ['--z3seed', str(seed), '--z3rlimit_factor', config.name[-1:]])

            elif (config is Config.interp):
                # Running interpreted tactic
                results = run_fstar(module_name, ['--z3seed', str(seed)])

            elif (config is Config.interp2):
                # Running native tactics
                # gen_native_plugin(tac_module_name)
                results = run_fstar(module_name, ['--z3seed', str(seed), '--load', tac_module_name, '--no_plugins'])

            elif (config is Config.native):
                # Running native tactics
                # gen_native_plugin(tac_module_name)
                results = run_fstar(module_name, ['--z3seed', str(seed), '--load', tac_module_name])

            results_stdout = results.stdout.decode('utf-8')
            checking_times = re.findall(time_regex, results_stdout)
            checking_times = list(filter((lambda x: x[0] in lemmas), checking_times))

            assert (len(checking_times) == 1)
            checking_time = checking_times[0]

            errors = re.findall(error_regex, results.stderr.decode('utf-8'))

            smt_times = re.findall(smt_time_regex, results_stdout)
            smt_time = sum(map(int, smt_times))

            tactic_times = re.findall(tactic_time_regex, results_stdout)
            tactic_time = sum(map(int, tactic_times))

            table_plain = format_table(module_name, checking_time, smt_time, tactic_time, seed, config, errors, 'jira', False)
            # table_latex = format_table(module_name, times, seed, config, errors, 'latex', True)
            if table_plain:
                with open('tactic_benchmarks.txt', 'a') as f:
                    f.write(table_plain + '\n')
                # tables += [table_latex]

    # with open('tactics_benchmarks.tex', 'w') as f:
    #     f.write(concat_tables(tables))


run_tests ()
