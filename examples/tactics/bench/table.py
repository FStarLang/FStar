import numpy as np
from itertools import chain
from tabulate import tabulate


def process_times(times, i):
    times = np.array(list(map((lambda x: int(x[i])), times)))
    return [float(int(np.mean(times)))/1000, float(int(np.std(times)))/1000] # ms -> s, 2 decimals

def process_by_config(data, config):
    data = list(filter((lambda x: x[2] == config), data))

    successful = list(filter((lambda x: x[4] == 'Success'), data))
    success_rate = float(len(successful)) / len(data)

    l = list(chain.from_iterable(map((lambda x: process_times(successful, x)), [5,6,7])))
    return ([round(success_rate, 2)] + l)

def format_table(rows):
    headers = ['Config', '% Success', 'Total (avg)', 'Total (std)', 'SMT (avg)', 'SMT (std)', 'Tactics (avg)', 'Tactics (std)']
    return tabulate(rows, headers, tablefmt='latex')

def column_from_array(arr, i):
    return list(map(float,chain.from_iterable(arr[:, [i]])))

def main():
    data = []
    with open('tactic_benchmarks6.txt', 'r') as f:
        for line in f:
            data.append(line.replace(' ', '').split('|')[1:-1])

    rows = []
    for config in ['smt_1', 'smt_2', 'smt_3', 'interp', 'native']:
        rows += [[config] + process_by_config(data, config)]

    with open('poly_table.tex', 'w') as f:
        f.write(format_table(rows))


main()
