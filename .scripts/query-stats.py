#!/usr/bin/env python 

# (C) Microsoft Research, CM Wintersteiger, 2017

import sys
import getopt
import re

ec = entry_count = "#"
fstar_output_columns = [ "fstar_tag", "fstar_usedhints", "fstar_time", "fstar_fuel", "fstar_ifuel", "fstar_rlimit" ]
column_separator = ","

SHORTOPTS="harcgf:o:s:t:n:"
LONGOPTS=["help", "infile=", "outfile=", "stat=", "top=", "collate", "append", "reverse", "global"]

def show_help():
    print("Usage: query-stats <options>")
    print("\nOptions:")
    print("  -h, --help  \t\t\tdisplay this message")
    print("  -f x, --infile=x\t\tprocess file <x> (instead of stdin)")
    print("  -o x, --outfile=x\t\twrite output to file <x> (instead of stdout)")
    print("  -s x, --stat=x\t\trank entries by <x> (instead of time)")
    print("  -n n, -t n, --top=n\t\tshow the <n> highest ranked queries (default 10)")
    print("  -a, --append\t\t\tappend to output (instead of overwriting it)")
    print("  -r, --reverse\t\t\treverse sort order")
    print("  -c, --collate\t\t\tcollate queries of the same name (instead of adding ticks)")
    print("  -g, --global\t\t\tadd global statistics table")


def cfmt_tag(value):
    return value.replace("succeeded", "+").replace("failed", "-").replace(" ", "")


def cfmt_usedhint(value):
    return value.replace("(with hint)", "+").replace(" ", "")


def cfmt(column, value):
    if column == "fstar_tag":
        return cfmt_tag(value)
    elif column == "fstar_usedhints":
        return cfmt_usedhint(value)
    else:
        return value


def merge_values(s1, s2):
    if len(s2) == 0:
        pass
    elif len(s1) == 0:
        s1 = s2
    else:
        for k, v in s1.items():
            if k in s2:
                v2 = s2[k]
                try:                        
                    i1 = int(v)
                    i2 = int(v2)
                    s1[k] = i1 + i2
                except:
                    try:
                        f1 = float(v)
                        f2 = float(v2)
                        s1[k] = f1 + f2
                    except:                        
                        str1 = str(v)
                        str2 = str(v2)
                        if (str1 == "" and str2 == ""):
                            s1[k] = ""
                        elif str1 == "":
                            s1[k] = str2
                        elif str2 == "":
                            s1[k] = str1
                        else: 
                            s1[k] = str1 + " " + str2
        for k, v in s2.items():
            if not k in s1:
                s1[k] = v
    return s1

def get_value(stats, column):
    return "" if column not in stats else stats[column]

def get_float_value(stats, column):
    return [(0.0 if t == "" else float(t)) for t in [get_value(stats, column)]][0]

def get_int_value(stats, column):
    return [(0 if t == "" else int(t)) for t in [get_value(stats, column)]][0]

def get_string_value(stats, column):
    return str(get_value(stats, column))


def write_header(f, order_column, fstar_output_columns, columns):
    f.write("\"ID (Name, Index)\"" + column_separator)
    f.write("\"Location\"" + column_separator)
    f.write("\"" + ec + "\"" + column_separator)
    f.write("\"" + order_column + "\"")
    for c in sorted(fstar_output_columns):
        f.write(column_separator + "\"" + c + "\"")
    for c in sorted(columns):        
        if (c not in { ec }):
            f.write(column_separator + "\"" + c + "\"")
    f.write("\n")


def write_footer(f):
    f.write("\n")


def write_query_row(f, item, order_column, fstar_columns, columns):
    key  = "\"" + item[0] + "\""
    stats = item[1]
    rng = "\"" + get_value(stats, "fstar_range").split(" ")[0] + "\""
    n = stats[ec]
    order_value = str(cfmt(order_column, get_value(stats, order_column)))

    f.write(key + column_separator)
    f.write(rng + column_separator)
    f.write(str(n) + column_separator)
    f.write(cfmt(order_column, str(order_value)))

    for c in sorted(fstar_output_columns):
        # c != order_column:
            f.write(column_separator + str(cfmt(c, get_value(stats, c))))
        
    for c in sorted(columns):
        # if c not in { ec, order_column }:
        if c not in { ec }:
            f.write(column_separator + str(cfmt(c, get_value(stats, c))))

    f.write("\n")


def add_query(stats, k, v):
    try:
        stats[k] = int(v)
    except:
        try:
            stats[k] = float(v)
        except:
            try:
                stats[k] = str(v)
            except:
                assert(False) # unreachable


def process_file(infile, outfile, stat, n, collate = False, append = False, reverse = False, global_stats = False):
    # "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s"
    # (.\FStar.UInt.fst(11,11-11,14))	Query-stats (FStar.UInt.pow2_values, 1)	succeeded (with hint) in 467 milliseconds with fuel 2 and ifuel 1 and rlimit 2723280 statistics={added-eqs=2 binary-propagations=3629 conflicts=1 datatype-accessor-ax=3 max-memory=8.96 memory=8.96 mk-bool-var=7332 mk-clause=54 num-allocs=25468507 num-checks=1 propagations=3632 rlimit-count=378055 time=0.00}
    # From CI:
    # 2017-05-10T12:50:45.6397264Z (.\FStar.Int.fst(8,11-8,14))       Query-stats (FStar.Int.pow2_values, 1)  succeeded (with hint) in 34 milliseconds with fuel 2 and ifuel 1 and rlimit 2723280

    rx=re.compile("^([ 0-9-TZ:.]+)?\((?P<fstar_range>.*)\)[ \t]+Query-stats \((?P<fstar_name>.*),[ ]*(?P<fstar_index>.*)\)[ \t]+(?P<fstar_tag>[a-zA-Z]+)(?P<fstar_usedhints>.*) in (?P<fstar_time>[0-9+\.+-]+) milliseconds with fuel (?P<fstar_fuel>\d+) and ifuel (?P<fstar_ifuel>\d+) and rlimit (?P<fstar_rlimit>\d+)[ \t\r]*(statistics=\{(?P<fstar_z3stats>.*)\})?[ \t\r]*$")
    z3rx=re.compile("([^ =]+)=([^ =]+)")

    queries = {}
    columns = set()
    columns.add(ec)

    with (open(infile, "r") if infile != "" else sys.stdin) as f:
        for line in f:
            mr=rx.match(line)
            if mr is not None:
                stats = {}
                for k, v in mr.groupdict().items():
                    add_query(stats, k, v)
                if ("fstar_usedhints" not in stats) or (stats["fstar_usedhints"] == ""):
                    stats["fstar_usedhints"] = "-"
                if "fstar_z3stats" in stats:
                    z3stats_str = get_value(stats, "fstar_z3stats")
                    del stats["fstar_z3stats"]
                    for k, v in z3rx.findall(z3stats_str):
                        add_query(stats, k, v)
                        columns.add(k)
                stats[ec] = 1
                id = str(get_value(stats, "fstar_name")) + ", " + str(get_value(stats, "fstar_index"))
                if not collate:
                    while id in queries:
                        id = id + "'"
                if id not in queries:
                    queries[id] = {}
                queries[id] = merge_values(queries[id], stats)
            elif line.find("Query-stats") != -1:
                print("Warning: unmatched query-stats line: %s" % line)    

    oq = sorted(queries.items(), key=lambda row: row[1][stat] if stat in row[1] else 0, reverse=not reverse)
    result = []
    for i in range(0, min(len(oq), n)):
        result.append(oq.pop(0))

    with (open(outfile, "w" if append == False else "a") if outfile != "" else sys.stdout) as f:
        write_header(f, stat, fstar_output_columns, columns)
        for item in result:
            write_query_row(f, item, stat, fstar_output_columns, columns)
        write_footer(f)
        if global_stats:
            process_global_stats(f, queries)


def process_global_stats(f, queries):
    f.write("\"Name\",\"Value\",\"Unit\"\n")
    time = 0.0
    fstar_time = 0
    max_time = 0.0
    max_fstar_time = 0
    sum_rlimit_count = 0
    max_rlimit_count = 0
    sum_fstar_rlimit = 0
    max_fstar_rlimit = 0
    max_max_memory = 0.0
    succeeded_without_hint = 0
    succeeded_with_hint = 0
    failed_without_hint = 0
    failed_with_hint = 0
    sum_num_checks = 0

    for k, v in queries.items():
        kv_time = get_float_value(v, "time")
        kv_fstar_time = get_int_value(v, "fstar_time")
        kv_rlimit_count = get_int_value(v, "rlimit-count")
        kv_fstar_rlimit = get_int_value(v, "fstar_rlimit")
        kv_max_memory = get_float_value(v, "max-memory")
        kv_num_checks = get_int_value(v, "num-checks")

        time += kv_time
        fstar_time += kv_fstar_time
        max_time = max(max_time, kv_time)
        max_fstar_time = max(max_fstar_time, kv_fstar_time)
        sum_rlimit_count += kv_rlimit_count
        max_rlimit_count = max(max_rlimit_count, kv_rlimit_count)
        sum_fstar_rlimit += kv_fstar_rlimit
        max_fstar_rlimit = max(max_fstar_rlimit, kv_fstar_rlimit)
        max_max_memory = max(max_max_memory, kv_max_memory)
        sum_num_checks += kv_num_checks

        tags = list(cfmt_tag(get_string_value(v, "fstar_tag")))
        usedhints = list(cfmt_usedhint(get_string_value(v, "fstar_usedhints")))
        assert(len(tags) == len(usedhints))
        for i in range(0, len(tags)):
            t = tags[i]
            u = usedhints[i]
            if t == "+" and u == "+":
                succeeded_with_hint += 1
            elif t == "+" and u == "-":
                succeeded_without_hint += 1
            elif t == "-" and u == "+":
                failed_with_hint += 1
            else:
                assert(t == "-" and u == "-")
                failed_without_hint += 1
            
    f.write("\"# Queries\",%s,%s\n" % (len(queries), "\"\""))
    f.write("\"# succeeded\",%s,%s\n" % ((succeeded_with_hint + succeeded_without_hint), "\"\""))
    f.write("\"# succeeded (with hint)\",%d,%s\n" % (succeeded_with_hint, "\"\""))
    f.write("\"# succeeded (without hint)\",%d,%s\n" % (succeeded_without_hint, "\"\""))
    f.write("\"# failed\",%d,%s\n" % ((failed_with_hint + failed_without_hint), "\"\""))
    f.write("\"# failed (with hint)\",%d,%s\n" % (failed_with_hint, "\"\""))
    f.write("\"# failed (without hint)\",%d,%s\n" % (failed_without_hint, "\"\""))
    f.write("\"Sum(num-checks)\",%s,%s\n" % (sum_num_checks, "\"\""))
    f.write("\"Sum(time)\",%s,%s\n" % (time, "\"sec\""))
    f.write("\"Sum(fstar_time)\",%s,%s\n" % (fstar_time, "\"msec\""))
    f.write("\"Max(time)\",%s,%s\n" % (max_time, "\"sec\""))
    f.write("\"Max(fstar_time)\",%s,%s\n" % (max_fstar_time, "\"msec\""))
    f.write("\"Sum(rlimit-count)\",%s,%s\n" % (sum_rlimit_count, "\"\""))
    f.write("\"Max(rlimit-count)\",%s,%s\n" % (max_rlimit_count, "\"\""))
    f.write("\"Sum(rlimit)\",%s,%s\n" % (sum_fstar_rlimit, "\"\""))
    f.write("\"Max(rlimit)\",%s,%s\n" % (max_fstar_rlimit, "\"\""))

    
    rlimit_cnst = float(544656)
    rlimit_budget_used = float("inf") if (max_rlimit_count == 0.0) else 100.0 * (float(sum_rlimit_count)/(float(max_rlimit_count)*rlimit_cnst))
    f.write("\"rlimit budget used\",%s,%s\n" % (rlimit_budget_used, "\"%\""))

    time_per_rlimit = float("inf") if (sum_fstar_rlimit == 0) else float(time)/float(sum_fstar_rlimit)
    rlimit_per_sec = float("inf") if (time == 0.0) else float(sum_fstar_rlimit)/float(time)
    f.write("\"time/rlimit\",%s,%s\n" % (time_per_rlimit, "\"sec\""))
    f.write("\"rlimit/sec\",%s,%s\n" % (rlimit_per_sec, "\"\""))

    f.write("\"Max(memory)\",%s,%s\n" % (max_max_memory, "\"MB\""))

    f.write("\n")


def main(argv):
    infile = ""
    outfile = ""
    stat = "time"
    n = "10"
    collate = False
    append = False
    reverse = False
    global_stats = False

    try:
        opts, args = getopt.getopt(argv, SHORTOPTS, LONGOPTS)
    except getopt.error as err:
        print("Error: " + str(err))
        print("")
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
        elif o in ("-a", "--append"):
            append = True
        elif o in ("-s", "--stat"):
            stat = a
        elif o in ("-t", "-n","--top"):
            n = a
        elif o in ("-r", "--reverse"):
            reverse = True
        elif o in ("-c", "--collate"):
            collate = True
        elif o in ("-g", "--global"):
            global_stats = True
        else:
            print("Unknown option `%s'" % o)
            return 2
    
    process_file(infile, outfile, stat, int(n), collate, append, reverse, global_stats)
    return 0


# python query-stats.py -c -f demo.log --outfile=summary.csv --stat=fstar_time -n 10
# python query-stats.py -c -f demo.log --outfile=summary.csv --stat=rlimit-count -n 10 -a
# python query-stats.py -c -f demo.log --outfile=summary.csv --stat=num-checks -n 10 -a -g


if __name__ == "__main__":    
    argv = sys.argv[1:]
    sys.exit(main(argv))
