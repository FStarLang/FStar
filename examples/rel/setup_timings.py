#!/usr/bin/env python
f = open('timings.csv')
lines = f.readlines()
lines = [ l.split(',') for l in lines ]
headers = lines[0]
lines = lines[1:]
table = { l[1] : [0,0,0] for l in lines }
for l in lines:
    entry = table[l[1]]
    entry[0] = entry[0] + int(l[2])
    entry[1] = entry[1] + int(l[3])
    entry[2] = entry[2] + int(l[4])

total = [0,0,0]
for e in table:
    total[0] = total[0] + table[e][0]
    total[1] = total[1] + table[e][1]
    total[2] = total[2] + table[e][2]

latex = """
\\begin{tabular}{|l|l|l|l|l|}
\\hline
"""
sep = '&'
latex = latex + sep.join(headers) + '\\\\\\hline\n'
for e in table:
    latex = latex + sep.join(e.split(';') + [str(x) for x in table[e]]) + '\\\\\n'
latex = latex + '\\hline ' + sep.join(['Total', ''] + [str(x) for x in total]) + '\\\\\\hline\n'
latex = latex + '\\end{tabular}'

h = open('timings.tex','w')
h.write(latex)
h.close()
