#!/usr/bin/env python 

# (C) Microsoft Research, CM Wintersteiger, 2017

import os
import sys
import getopt
import re

ec = entry_count = "#"
fstar_output_columns = [ "fstar_tag", "fstar_usedhints", "fstar_time", "fstar_fuel", "fstar_ifuel", "fstar_rlimit" ]
column_separator = ","

SHORTOPTS="harcgf:o:s:t:n:F:"
LONGOPTS=["help", "infile=", "outfile=", "stat=", "top=", "collate", "append", "reverse", "global", "filter=", "format=" ]

def show_help():
    print("Usage: query-stats <options>")
    print("\nOptions:")
    print("  -h, --help  \t\t\tdisplay this message")
    print("  -f x, --infile=x\t\tprocess file <x> (instead of stdin)")
    print("  -o x, --outfile=x\t\twrite output to file <x> (instead of stdout)")
    print("  -s x, --stat=x\t\trank entries by <x> (instead of time; use 'ALPHA' for alphabetical)")
    print("  -n n, -t n, --top=n\t\tshow the <n> highest ranked queries (default 10, 'all' and '*' mean unlimited)")
    print("  -a, --append\t\t\tappend to output (instead of overwriting it)")
    print("  -r, --reverse\t\t\treverse sort order")
    print("  -c, --collate\t\t\tcollate queries of the same name (instead of adding ticks)")
    print("  -g, --global\t\t\tadd global statistics table")
    print("  -F, --format\t\t\toutput format (csv|html; default csv)")
    print("      --filter=s=v\t\t\tfilter queries; only include queries for which variable s is equal to v.")


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
                            s1[k] = "\"" + str1.strip("\"") + " " + str2.strip("\"") + "\""
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
    return str(get_value(stats, column)).strip("\"")

def write_header(f, order_column, fstar_output_columns, columns, output_format):
    if output_format == "csv":
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
    elif output_format == "html":
        f.write("<html><title>Query-stats</title><body>\n")
        f.write("<table width=100% border=1>\n")
        f.write("<caption><h1>Query Statistics</h1></caption>\n")
        f.write("<tr>")
        f.write("<th>ID (Name, Index)</th>")
        f.write("<th>Location</th>")
        f.write("<th>" + ec + "</th>")
        f.write("<th>" + order_column + "</th>")
        for c in sorted(fstar_output_columns):
            f.write("<th>" + c + "</th>")
        for c in sorted(columns):        
            if (c not in { ec }):
                f.write("<th>" + c + "</th>")
        f.write("</tr>\n")

def write_footer(f, output_format):
    if output_format == "csv":
        pass
    elif output_format == "html":
        f.write("</table>")

def write_eof(f, output_format):
    if output_format == "csv":
        f.write("\n")
    elif output_format == "html":
        f.write("</body></html>")

def write_query_row(f, item, order_column, fstar_columns, columns, output_format):
    if output_format == "csv":
        key  = "\"" + item[0] + "\""
        stats = item[1]
        rng = "\"" + get_value(stats, "fstar_range").strip("\"").split(" ")[0] + "\""
        n = stats[ec]
        order_value = str(cfmt(order_column, get_value(stats, order_column)))

        f.write(key + column_separator)
        f.write(rng + column_separator)
        f.write(str(n) + column_separator)
        f.write(cfmt(order_column, str(order_value)))

        for c in sorted(fstar_output_columns):
            f.write(column_separator + str(cfmt(c, get_value(stats, c))))
        
        for c in sorted(columns):
            if c not in { ec }:
                f.write(column_separator + str(cfmt(c, get_value(stats, c))))

        f.write("\n")
    elif output_format == "html":
        key  = item[0]
        stats = item[1]
        rng = get_value(stats, "fstar_range").strip("\"").split(" ")[0]
        n = stats[ec]
        order_value = str(cfmt(order_column, get_value(stats, order_column)))

        f.write("<tr>")
        f.write("<td>%s</td>" % key)
        f.write("<td>%s</td>" % rng)
        f.write("<td>%s</td>" % str(n))
        f.write("<td>%s</td>" % cfmt(order_column, str(order_value)))

        for c in sorted(fstar_output_columns):
            f.write("<td>%s</td>" % str(cfmt(c, get_value(stats, c))))
        
        for c in sorted(columns):
            if c not in { ec }:
                f.write("<td>%s</td>" % str(cfmt(c, get_value(stats, c))))

        f.write("</tr>\n")


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


def is_filtered(stats, filters):
    for s, fltrv in filters:
        if s in stats:
            statsv = cfmt(s, stats[s])
            if not statsv == fltrv:
                return False
    return True


def process_file(infile, outfile, stat, n, collate = False, append = False, reverse = False, global_stats = False, filters = None, output_format = "csv"):
    # "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s"
    # (.\FStar.UInt.fst(11,11-11,14))	Query-stats (FStar.UInt.pow2_values, 1)	succeeded (with hint) in 467 milliseconds with fuel 2 and ifuel 1 and rlimit 2723280 statistics={added-eqs=2 binary-propagations=3629 conflicts=1 datatype-accessor-ax=3 max-memory=8.96 memory=8.96 mk-bool-var=7332 mk-clause=54 num-allocs=25468507 num-checks=1 propagations=3632 rlimit-count=378055 time=0.00}
    # From CI:
    # 2017-05-10T12:50:45.6397264Z (.\FStar.Int.fst(8,11-8,14))       Query-stats (FStar.Int.pow2_values, 1)  succeeded (with hint) in 34 milliseconds with fuel 2 and ifuel 1 and rlimit 2723280
    # F* also reports:
    # 2017-06-29T14:00:36.8084892Z STDERR: Verified module: Hacl.Spec.Bignum.Fsquare (576007 milliseconds)
    # [STDOUT](aead/Crypto.AEAD.Encrypt.fst(196,2-205,53))    Query-stats ...

    rx=re.compile("^([ 0-9-TZ:.]+|\[STDOUT\])?\((?P<fstar_range>.*)\)[ \t]+Query-stats \((?P<fstar_name>.*),[ ]*(?P<fstar_index>.*)\)[ \t]+(?P<fstar_tag>[a-zA-Z]+)[ \t]*(\{reason-unknown=[^ \t]+[ \t]+[^ \t]+[ \t]+\(*(?P<fstar_reason_unknown>[^\)]*)\)*\})?[ \t]*(?P<fstar_usedhints>.*) in (?P<fstar_time>[0-9+\.+-]+) milliseconds with fuel (?P<fstar_fuel>\d+) and ifuel (?P<fstar_ifuel>\d+) and rlimit (?P<fstar_rlimit>\d+)[ \t\r]*(statistics=\{(?P<fstar_z3stats>.*)\})?[ \t\r]*$")
    z3rx=re.compile("([^ =]+)=([^ =\"]+|\".*\")")
    modrx=re.compile("^([ 0-9-TZ:.]+( STDERR:)? )?Verified module: (?P<module>[^ ]+) \((?P<module_time>[0-9]*) milliseconds\)[ \t\r]*$")

    queries = {}
    modules = {}
    columns = set()
    seen_vars = set()
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
                if "fstar_reason_unknown" in stats.keys():
                    columns.add("reason-unknown")
                    add_query(stats, "reason-unknown", stats["fstar_reason_unknown"])
                stats[ec] = 1
                id = "(%s, %d)" % (get_value(stats, "fstar_name"), get_value(stats, "fstar_index"))
                if not collate:
                    while id in queries:
                        id = id + "'"
                if id not in queries:
                    queries[id] = {}
                queries[id] = merge_values(queries[id], stats)
                seen_vars = seen_vars.union(stats.keys())
            elif line.find("Query-stats") != -1:
                print("Warning: unmatched query-stats line: %s" % line)
            modrm=modrx.match(line)
            if modrm is not None:
                k = modrm.groupdict()["module"]
                v = modrm.groupdict()["module_time"]
                modules[k] = int(v);        

    if filters is not None:
        for s, v in filters:
            if s not in seen_vars:
                print("Warning: unknown variable '%s'." % s)
        queries = { k:v for k,v in queries.iteritems() if is_filtered(v, filters) }

    if stat == "ALPHA":
        oq = sorted(queries.items(), key=lambda row: row[0], reverse=reverse)
    else:
        oq = sorted(queries.items(), key=lambda row: row[1][stat] if stat in row[1] else 0, reverse=not reverse)

    result = []
    if n < 0: n = len(oq)
    for i in range(0, min(len(oq), n)):
        result.append(oq.pop(0))

    with (open(outfile, "w" if append == False else "a") if outfile != "" else sys.stdout) as f:
        if len(result) > 0: write_header(f, stat, fstar_output_columns, columns, output_format)
        for item in result:
            write_query_row(f, item, stat, fstar_output_columns, columns, output_format)
        write_footer(f, output_format)
        if global_stats:
            process_global_stats(f, queries, modules, collate, output_format)
        write_eof(f, output_format)


def process_global_stats(f, queries, modules, collate, output_format):
    if output_format == "csv":
        f.write("\n\"Name\",\"Value\",\"Unit\"\n")
    elif output_format == "html":
        f.write("<br/></table>\n")
        f.write("<table border=1>\n")
        f.write("<caption><h1>Global Statistics</h1></caption>\n")
        f.write("<tr><th>Name</th><th>Value</th><th>Unit</th><th><Item/th></tr>\n")

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
    sum_failed = 0
    sum_failed_with_hint = 0
    sum_failed_without_hint = 0

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
            if not collate:
                # (this don't make sense with query collation)
                if t == "-":
                    sum_failed += kv_time
                    if u == "+":
                        sum_failed_with_hint += kv_time
                    elif u == "-":
                        sum_failed_without_hint += kv_time
           
    def write_fmt(format, name, value, unit=None, item=None):
        if output_format == "csv": 
            f.write("\"%s\",%s,\"%s\",\"%s\"\n" % (name, value, "" if unit is None else unit, "" if item is None else item))
        elif output_format == "html": 
            f.write("<tr><td>%s</td><td>%s</td><td>%s</td><td>%s</td></tr>\n" % 
                        (name, value, "" if unit is None else unit, "" if item is None else item))

    write_fmt(output_format, "# Queries", len(queries))
    write_fmt(output_format, "# succeeded", succeeded_with_hint + succeeded_without_hint)
    write_fmt(output_format, "# succeeded (with hint)", succeeded_with_hint)
    write_fmt(output_format, "# succeeded (without hint)", succeeded_without_hint)
    write_fmt(output_format, "# failed", (failed_with_hint + failed_without_hint))
    write_fmt(output_format, "# failed (with hint)", failed_with_hint)
    write_fmt(output_format, "# failed (without hint)", failed_without_hint)
    write_fmt(output_format, "Sum(num-checks)", sum_num_checks)
    write_fmt(output_format, "Sum(time)", time, "sec")
    write_fmt(output_format, "Sum(fstar_time)", fstar_time, "msec")
    write_fmt(output_format, "Max(time)", max_time, "sec")
    write_fmt(output_format, "Max(fstar_time)", max_fstar_time, "msec")
    write_fmt(output_format, "Sum(rlimit-count)", sum_rlimit_count)
    write_fmt(output_format, "Max(rlimit-count)", max_rlimit_count)
    write_fmt(output_format, "Sum(rlimit)", sum_fstar_rlimit)
    write_fmt(output_format, "Max(rlimit)", max_fstar_rlimit)

    if not collate:
        write_fmt(output_format, "Sum(time failed)", sum_failed, "sec")
        write_fmt(output_format, "Sum(time failed with hint)", sum_failed_with_hint, "sec")
        write_fmt(output_format, "Sum(time failed without hint)", sum_failed_without_hint, "sec")
    
    rlimit_cnst = float(544656)
    rlimit_budget_used = float("inf") if (max_rlimit_count == 0.0) else 100.0 * (float(sum_rlimit_count)/(float(max_rlimit_count)*rlimit_cnst))
    write_fmt(output_format, "rlimit budget used", rlimit_budget_used, "%")

    time_per_rlimit = float("inf") if (sum_fstar_rlimit == 0) else float(time)/float(sum_fstar_rlimit)
    rlimit_per_sec = float("inf") if (time == 0.0) else float(sum_fstar_rlimit)/float(time)
    write_fmt(output_format, "time/rlimit", time_per_rlimit, "sec")
    write_fmt(output_format, "rlimit/sec", rlimit_per_sec, "")
        
    write_fmt(output_format, "Max(memory)", max_max_memory, "MB")
        
    write_fmt(output_format, "# Modules", len(modules), "")
    if len(modules) > 0:
        min_mod = min(modules.keys(), key=(lambda key: modules[key]))
        max_mod = max(modules.keys(), key=(lambda key: modules[key]))
        write_fmt(output_format, "# Sum(time modules)", sum(modules.values()), "msec")
        write_fmt(output_format, "# Min(time modules)", min(modules.values()), "msec", min_mod)
        write_fmt(output_format, "# Max(time modules)", max(modules.values()), "msec", max_mod)
 
    if output_format == "csv":
        f.write("\n")
    elif output_format == "html":
        f.write("</table>")

def main(argv):
    infile = ""
    outfile = ""
    stat = "time"
    n = 10
    collate = False
    append = False
    reverse = False
    global_stats = False
    filters = None
    output_format = "csv"

    try:
        opts, args = getopt.getopt(argv, SHORTOPTS, LONGOPTS)
    except getopt.error as err:
        print("Error: %s\n" % str(err))
        show_help()
        return 1

    for o, a in opts:
        if o in ("-h", "--help"):
            show_help()
            return 1
        elif o in ("-f", "--infile"):
            if not os.path.exists(a):
                print("Error: file '%s' does not exists." % a)
                return 2
            else:
                infile = a
        elif o in ("-o", "--outfile"):
            outfile = a
        elif o in ("-a", "--append"):
            append = True
        elif o in ("-s", "--stat"):
            stat = a
        elif o in ("-t", "-n", "--top"):
            if a == "all" or a == "*":
                v = sys.version_info
                if v[0] >= 3:
                    n = sys.maxsize
                else:
                    n = sys.maxint
            else:
                n = int(a)
                if n < 0:
                    print("Error: -n/-t/--top must be >= 0.")
                    return 1
        elif o in ("-r", "--reverse"):
            reverse = True
        elif o in ("-c", "--collate"):
            collate = True
        elif o in ("-g", "--global"):
            global_stats = True
        elif o in ("--filter"):
            if a.count("=") != 1:
                print("Error: filter not in s=v format.")
                return 2
            s, v = a.split("=")
            f = [ s, v ]
            if filters is None:
                filters = [ ]
            filters += [ f ]
        elif o in ("-F", "--format"):
            if a != "csv" and a != "html":
                print("Error: unsupported output format '%s'" % a)
            output_format = a
        else:
            print("Unknown option `%s'" % o)
            return 2
    
    process_file(infile, outfile, stat, int(n), collate, append, reverse, global_stats, filters, output_format)
    return 0


# python query-stats.py -c -f demo.log --outfile=summary.csv --stat=fstar_time -n 10
# python query-stats.py -c -f demo.log --outfile=summary.csv --stat=rlimit-count -n 10 -a
# python query-stats.py -c -f demo.log --outfile=summary.csv --stat=num-checks -n 10 -a -g


if __name__ == "__main__":    
    argv = sys.argv[1:]
    sys.exit(main(argv))
