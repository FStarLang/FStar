# (C) Microsoft Research, CM Wintersteiger, 2017

import sys
import getopt
import re

def process_file(infile, outfile, stat, n):
    # "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s"
    # (.\FStar.UInt.fst(11,11-11,14))	Query-stats (FStar.UInt.pow2_values, 1)	succeeded (with hint) in 467 milliseconds with fuel 2 and ifuel 1 and rlimit 2723280 statistics={added-eqs=2 binary-propagations=3629 conflicts=1 datatype-accessor-ax=3 max-memory=8.96 memory=8.96 mk-bool-var=7332 mk-clause=54 num-allocs=25468507 num-checks=1 propagations=3632 rlimit-count=378055 time=0.00}

    rx=re.compile("^\((?P<range>.*)\)\tQuery-stats \((?P<name>.*),[ ]*(?P<index>.*)\)\t(?P<tag>[a-zA-Z]+)(?P<usedhints>.*) in (?P<time>\d+) milliseconds with fuel (?P<fuel>\d+) and ifuel (?P<ifuel>\d+) and rlimit (?P<rlimit>\d+) statistics=\{(?P<z3stats>.*)\}$")
    z3rx=re.compile("([^ =]+)=([^ =]+)")

    queries = dict()

    with (open(infile, "r") if infile != "" else sys.stdin) as f:
        for line in f:
            mr=rx.match(line)
            if mr is not None:
                stats = mr.groupdict() # range, name, index, usedhints, time, fuel, ifuel, rlimit, z3stats
                for k, v in z3rx.findall(stats["z3stats"]):
                    stats[k] = v
                queries[stats["name"] + "-" + stats["index"]] = stats
            elif line.find("Query-stats") != -1:
                print("Warning: unmatched query-stats line: %s" % line)

    oq = sorted(queries.items(), key=lambda item: item[1][stat], reverse=True)
    result = []
    for i in range(1, n):
        result.append(oq.pop(0))

    with (open(outfile, "w") if outfile != "" else sys.stdout) as f:
        for item in result:
            f.write(item[0] + ", " + item[1]["range"]+ ", "+ item[1][stat] + "\n")

SHORTOPTS="hf:o:s:n:"
LONGOPTS=["help", "infile=", "outfile=", "stat=", "--top="]

def show_help():
    print("Usage: query-stats <options>")
    print("\nOptions:")
    print("  -h, --help  \t\t\tdisplay this message")
    print("  -f x, --infile=x\t\tprocess file <x> (instead of stdin)")
    print("  -o x, --outfile=x\t\twrite output to file <x> (instead of stdout)")
    print("  -s x, --stat=x\t\trank entries by <x> (instead of time)")
    print("  -t n, --top=n\t\t\tshow the <n> highest ranked queries (default 10)")

def main(argv):
    infile=""
    outfile=""
    stat="time"
    n = "10"

    try:
        opts, args = getopt.getopt(argv, SHORTOPTS, LONGOPTS)
    except getopt.error, msg:
        show_help()
        return 1
    for o, a in opts:
        if o in ("-h", "--help"):
            show_help()
            return 1
        elif o in ("-f", "--infile"):
            infile = a
        elif o in ("-o", "--outfile"):
            outfile = a
        elif o in ("-s", "--stat"):
            stat = a
        elif o in ("-n", "--top"):
            n = a
        else:
            print("Unknown option `%s'" % opt)
            return 2

    process_file(infile, outfile, stat, int(n))
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
    # sys.exit(main( [ "-f", "FStar.UInt.fst.stats", "--stat=rlimit-count", "-n", "12" ] ))
    # sys.exit(main( [ "-f", "FStar.UInt.fst.stats", "--outfile=summary.html", "--stat=time", "-n", "12" ] ))
    
