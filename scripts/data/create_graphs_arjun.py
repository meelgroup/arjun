#!/usr/bin/python3

import argparse
import base64
import itertools
import os
import sqlite3
import re

BLUE  = "\033[94m"
GREEN = "\033[92m"
RED   = "\033[91m"
RESET = "\033[0m"

DB = "data.sqlite3"
TABLE = "arjun"
TIMEOUT = 1800  # seconds used for PAR2 / scatter timeout
TMP_DIR = "tmp"

# ---- Configuration: which dirs to include (prefix match) ----
only_dirs = [
    # "out-synth-1068169-0",
    "out-synth-1286344-",
    # "out-synth-1296625-",
]
# -------------------------------------------------------------


def get_versions():
    con = sqlite3.connect(DB)
    cur = con.cursor()
    res = cur.execute(f"""
        SELECT arjun_sha1 FROM {TABLE}
        WHERE arjun_sha1 IS NOT NULL AND arjun_sha1 != ''
        GROUP BY arjun_sha1""")
    vers = [row[0] for row in res]
    con.close()
    return vers


def get_matching_dirs(only_dirs_list):
    """Return all dirnames from DB that start with any prefix in only_dirs_list.
    Returns all dirnames if only_dirs_list is empty."""
    con = sqlite3.connect(DB)
    cur = con.cursor()
    res = cur.execute(f"SELECT DISTINCT dirname FROM {TABLE} ORDER BY dirname")
    all_dirs = [row[0] for row in res]
    con.close()
    if not only_dirs_list:
        return all_dirs
    return [d for d in all_dirs if any(d.startswith(p) for p in only_dirs_list)]


def _dir_call_label(call: str) -> str:
    """Strip binary name and CNF filename from a raw timeout_call string."""
    call = re.sub(r'^\./arjun\S*\s+', '', call)
    call = re.sub(r'\s+\S+\.(?:qdimacs\.cnf|cnf)\S*\s*$', '', call)
    return call.strip()


def get_dirs(ver: str):
    ret = []
    con = sqlite3.connect(DB)
    cur = con.cursor()
    res = cur.execute(
        f"SELECT dirname, MIN(timeout_call) FROM {TABLE}"
        f" WHERE arjun_sha1=? GROUP BY dirname",
        (ver,))
    for row in res:
        call = _dir_call_label(row[1] or "")
        ret.append([row[0], call])
    con.close()
    return ret


def gnuplot_name_cleanup(name: str) -> str:
    name = re.sub(r'"', '', name)
    name = re.sub(r'_', '=', name)
    return name


def convert_to_cdf(fname, fname2):
    with open(fname, "r") as f:
        times = sorted(float(line.split()[0]) for line in f if line.strip())
    with open(fname2, "w") as f2:
        for i, t in enumerate(times):
            f2.write(f"{i+1} \t{t}\n")
    return len(times)


def build_csv_data(versions, matched_dirs, only_calls, not_calls, not_versions,
                   fname_like, verbose=False):
    fname2_s = []
    table_todo = []
    matched_dirs_set = set(matched_dirs)

    for ver in versions:
        for dir, call in get_dirs(ver):
            bad = False
            for nc in not_calls:
                if nc in call:
                    bad = True
            for nv in not_versions:
                if nv in ver:
                    bad = True
            if only_calls:
                if not any(oc in call for oc in only_calls):
                    bad = True
            if dir not in matched_dirs_set:
                bad = True
            if bad:
                if verbose:
                    print(f"  Skipping dir={dir} ver={ver}")
                continue
            if verbose:
                print(f"  Processing dir={dir} ver={ver} call={call!r}")

            fname = os.path.join(TMP_DIR, "run-" + dir + ".csv")
            con = sqlite3.connect(DB)
            cur = con.cursor()
            res = cur.execute(
                f"SELECT arjun_time FROM {TABLE}"
                f" WHERE dirname=? AND arjun_sha1=? AND arjun_time IS NOT NULL{fname_like}",
                (dir, ver))
            with open(fname, "w") as f:
                for row in res:
                    f.write(f"{row[0]}\n")
            con.close()

            fname2 = fname + ".gnuplotdata"
            num_solved = convert_to_cdf(fname, fname2)
            fname2_s.append([fname2, call, ver[:10], num_solved, dir])
            table_todo.append([dir, ver])

    return fname2_s, table_todo


# ---- Table helpers ----

def _print_table(headers, str_rows):
    if not str_rows:
        return
    widths = [max(len(h), max((len(r[i]) for r in str_rows), default=0))
              for i, h in enumerate(headers)]
    sep = "+-" + "-+-".join("-" * w for w in widths) + "-+"
    fmt = "| " + " | ".join(f"{{:<{w}}}" for w in widths) + " |"
    print(sep)
    print(fmt.format(*headers))
    print(sep)
    for row in str_rows:
        print(fmt.format(*row))
    print(sep)


def _sqlite_run(query, title=None):
    if title:
        print(f"\n{BLUE}{title}{RESET}")
    query_file = os.path.join(TMP_DIR, "_tmp_query.sqlite")
    with open(query_file, "w") as f:
        f.write(".mode table\n")
        f.write(query + "\n")
    os.system(f"sqlite3 {DB} < {query_file}")
    os.unlink(query_file)


def print_summary_tables(table_todo, fname_like, full=False):
    if not table_todo:
        return
    dirs = ",".join("'" + d + "'" for d, _ in table_todo)
    vers = ",".join("'" + v + "'" for _, v in table_todo)

    # Strip CNF filename and leading binary name from call
    call_expr = "TRIM(REPLACE(REPLACE(MIN(timeout_call), ' '||MIN(fname), ''), './arjun ', ''))"

    compact_cols = [
        ("replace(dirname,'out-synth-','out-')",                         "dirname"),
        (call_expr,                                                       "call"),
        ("sum(arjun_time is not null)",                                  "solved"),
        (f"CAST(ROUND(sum(coalesce(arjun_time,{TIMEOUT}))/COUNT(*),0) AS INTEGER)", "PAR2"),
        ("CAST(ROUND(avg(timeout_mem),0) AS INTEGER)",                   "av memMB"),
        ("sum(mem_out)",                                                 "mem_out"),
        ("sum(signal == 11)",                                            "sigSEGV"),
        ("sum(signal == 6)",                                             "sigABRT"),
        ("sum(signal == 14)",                                            "sigALRM"),
        ("CAST(avg(input_vars) AS INTEGER)",                             "av-inp"),
        ("CAST(avg(start_to_define_vars) AS INTEGER)",                   "av-to-def"),
        ("CAST(ROUND(avg(puura_time), 2) AS REAL)",                      "av-puura-T"),
        ("CAST(avg(puura_defined) AS INTEGER)",                          "av-puura-def"),
        ("sum(fname is not null)",                                       "nfiles"),
    ]
    full_only_cols = [
        ("CAST(ROUND(avg(extend_time), 2) AS REAL)",                     "av-ext-T"),
        ("CAST(avg(extend_defined) AS INTEGER)",                         "av-ext-def"),
        ("CAST(ROUND(avg(backward_time), 2) AS REAL)",                   "av-backw-T"),
        ("CAST(avg(backward_defined) AS INTEGER)",                       "av-backw-def"),
        ("CAST(ROUND(avg(manthan_training_time),2) AS REAL)",            "av-mant-tr-T"),
        ("CAST(ROUND(avg(manthan_repair_time),2) AS REAL)",              "av-mant-rep-T"),
        ("CAST(ROUND(avg(manthan_time), 2) AS REAL)",                    "av-manth-T"),
        ("CAST(ROUND(avg(repairs),0) AS INTEGER)",                       "av-repairs"),
        ("CAST(avg(manthan_defined) AS INTEGER)",                        "av-manthan-def"),
    ]

    cols = compact_cols + (full_only_cols if full else [])
    select_clause = ",\n        ".join(f"{expr} as '{alias}'" for expr, alias in cols)

    for only_counted in [False, True]:
        title = ("Data based on ONLY SOLVED benchmarks"
                 if only_counted else "Data including UNSOLVED benchmarks")
        counted_req = " AND arjun_time IS NOT NULL" if only_counted else ""
        _sqlite_run(
            f"select\n        {select_clause}\n"
            f"        from {TABLE}"
            f" where dirname IN ({dirs}) and arjun_sha1 IN ({vers})"
            f"{fname_like}{counted_req} group by dirname order by solved asc",
            title=title)


def _median_sq(col, dir, ver, fname_like):
    base = f"dirname='{dir}' AND arjun_sha1='{ver}' AND {col} IS NOT NULL{fname_like}"
    return (f"(SELECT {col} FROM {TABLE} WHERE {base}"
            f" ORDER BY {col} LIMIT 1"
            f" OFFSET (SELECT COUNT({col}) FROM {TABLE} WHERE {base}) / 2)")


def _avg_sq(col, dir, ver, fname_like):
    base = f"dirname='{dir}' AND arjun_sha1='{ver}' AND {col} IS NOT NULL{fname_like}"
    return f"(SELECT CAST(ROUND(AVG({col}),0) AS INTEGER) FROM {TABLE} WHERE {base})"


def print_median_tables(table_todo, fname_like):
    if not table_todo:
        return
    plain_cols = ["repairs", "timeout_mem", "arjun_time", "manthan_time"]
    union_parts = []
    for i, (dir, ver) in enumerate(table_todo):
        alias_suffix = " as dirname" if i == 0 else ""
        ver_alias    = " as ver"     if i == 0 else ""
        parts = [f"replace('{dir}','out-synth-','out-'){alias_suffix}",
                 f"'{ver[:10]}'{ver_alias}"]
        for col in plain_cols:
            parts.append(f"{_median_sq(col, dir, ver, fname_like)} as med_{col}")
        union_parts.append("SELECT " + ", ".join(parts))
    _sqlite_run("\nUNION ALL\n".join(union_parts), title="Median values per directory")


def print_instance_stats_table(table_todo, fname_like):
    if not table_todo:
        return
    metrics = [
        ("input_vars",           "inp_vars"),
        ("start_to_define_vars", "to_define"),
        ("puura_defined",        "puura_def"),
        ("extend_defined",       "ext_def"),
        ("backward_defined",     "back_def"),
        ("manthan_defined",      "mant_def"),
    ]
    union_parts = []
    for i, (dir, ver) in enumerate(table_todo):
        alias_suffix = " as dirname" if i == 0 else ""
        parts = [f"replace('{dir}','out-synth-','out-'){alias_suffix}"]
        for col, alias in metrics:
            parts.append(f"{_median_sq(col, dir, ver, fname_like)} as med_{alias}")
            parts.append(f"{_avg_sq(col, dir, ver, fname_like)} as avg_{alias}")
        count_sq = (f"(SELECT COUNT(*) FROM {TABLE}"
                    f" WHERE dirname='{dir}' AND arjun_sha1='{ver}'{fname_like})")
        parts.append(f"{count_sq} as n_inst")
        union_parts.append("SELECT " + ", ".join(parts))
    _sqlite_run("\nUNION ALL\n".join(union_parts),
                title="Instance stats: variable counts and synthesis phase results (median/avg)")


def print_signal_warnings(table_todo, fname_like):
    dirs = ",".join("'" + d + "'" for d, _ in table_todo)
    vers = ",".join("'" + v + "'" for _, v in table_todo)
    con = sqlite3.connect(DB)
    cur = con.cursor()
    cur.execute(
        f"SELECT COUNT(*) FROM {TABLE}"
        f" WHERE dirname IN ({dirs}) AND arjun_sha1 IN ({vers})"
        f" AND signal=6 AND (mem_out IS NULL OR mem_out=0){fname_like}")
    count = cur.fetchone()[0]
    if count > 0:
        print(f"\n{RED}WARNING: {count} instance(s) with sigABRT (signal=6){RESET}")
        cur.execute(
            f"SELECT dirname, fname, timeout_mem FROM {TABLE}"
            f" WHERE dirname IN ({dirs}) AND arjun_sha1 IN ({vers})"
            f" AND signal=6 AND (mem_out IS NULL OR mem_out=0){fname_like}"
            f" ORDER BY dirname, fname")
        rows = cur.fetchall()
        str_rows = [(d, f, f"{m:.1f}" if m is not None else "N/A") for d, f, m in rows]
        _print_table(["dirname", "fname", "memMB"], str_rows)
    con.close()


# ---- Plot helpers ----

def _png_dimensions(png_file):
    try:
        with open(png_file, "rb") as fh:
            fh.seek(16)
            w = int.from_bytes(fh.read(4), "big")
            h = int.from_bytes(fh.read(4), "big")
        return w, h
    except Exception:
        return 800, 600


def _display_png(png_file):
    if os.path.exists(png_file):
        with open(png_file, "rb") as fh:
            img_b64 = base64.b64encode(fh.read()).decode()
        w, h = _png_dimensions(png_file)
        print(f"\033]1337;File=inline=1;width={w}px;height={h}px:{img_b64}\a")


def _gnuplot_run(gp_file, pdf_file, png_file, console_title):
    for path in [pdf_file, png_file]:
        if os.path.exists(path):
            os.unlink(path)
    os.system(f"gnuplot {gp_file}")
    print(f"\n{BLUE}{console_title}{RESET}")
    print(f"  PDF: {pdf_file}  PNG: {png_file}")
    _display_png(png_file)


def _safe(s):
    return re.sub(r'[^a-zA-Z0-9_-]', '_', s)


def _gp_str(s):
    return s.replace('"', '\\"')


# ---- CDF plot ----

def generate_cdf(fname2_s):
    gnuplotfn = os.path.join(TMP_DIR, "cdf.gnuplot")
    pdf_file  = os.path.join(TMP_DIR, "cdf.pdf")
    png_file  = os.path.join(TMP_DIR, "cdf.png")

    def plot_lines():
        lines = []
        for fn, call, _, _, dir in fname2_s:
            label = gnuplot_name_cleanup(dir)
            if call:
                label += "-" + gnuplot_name_cleanup(call)
            lines.append(f'"{fn}" u 2:1 with linespoints title "{label}"')
        return ",\\\n".join(lines)

    with open(gnuplotfn, "w") as f:
        for term, out in [
            ('pdfcairo size 20cm,15cm background "#d0d0d0"', pdf_file),
            ('pngcairo size 800,600 background "#d0d0d0"',   png_file),
        ]:
            f.write(f'set terminal {term}\n')
            f.write(f'set output "{out}"\n')
            f.write('set title "Arjun synthesis CDF: instances solved vs. time"\n')
            f.write('set key top left\n')
            f.write('set logscale x\n')
            f.write('unset logscale y\n')
            f.write(f'set xrange [0.001:{TIMEOUT}]\n')
            f.write('set yrange [0:]\n')
            f.write('set ylabel "Instances synthesised"\n')
            f.write('set xlabel "Time (s)"\n')
            f.write('set grid\n')
            f.write('plot \\\n')
            f.write(plot_lines())
            f.write('\n\n')

    _gnuplot_run(gnuplotfn, pdf_file, png_file,
                 "CDF: instances synthesised vs. time")


# ---- Scatter plots ----

def scatter_plot_time_pairs(matched_dirs, fname_like, verbose=False):
    """For every pair of matched dirs, plot arjun_time scatter (NULL -> TIMEOUT)."""
    pairs = list(itertools.combinations(matched_dirs, 2))
    if not pairs:
        return

    # Build short label per dir
    dir_label = {}
    con = sqlite3.connect(DB)
    cur = con.cursor()
    for d in matched_dirs:
        cur.execute(f"SELECT MIN(timeout_call) FROM {TABLE} WHERE dirname=?", (d,))
        row = cur.fetchone()
        dir_label[d] = _dir_call_label(row[0] or "") if row and row[0] else d

    for dir1, dir2 in pairs:
        cur.execute(
            f"SELECT a.fname,"
            f" COALESCE(a.arjun_time, {TIMEOUT}),"
            f" COALESCE(b.arjun_time, {TIMEOUT})"
            f" FROM {TABLE} a JOIN {TABLE} b ON a.fname = b.fname"
            f" WHERE a.dirname = '{dir1}' AND b.dirname = '{dir2}'"
            f"{fname_like}")
        rows = cur.fetchall()

        if not rows:
            if verbose:
                print(f"  scatter: no common fnames for {dir1} vs {dir2}")
            continue

        safe1 = _safe(dir1)
        safe2 = _safe(dir2)
        dat_file = os.path.join(TMP_DIR, f"scatter_{safe1}_vs_{safe2}.dat")
        pdf_file = os.path.join(TMP_DIR, f"scatter_{safe1}_vs_{safe2}.pdf")
        png_file = os.path.join(TMP_DIR, f"scatter_{safe1}_vs_{safe2}.png")
        gp_file  = os.path.join(TMP_DIR, f"scatter_{safe1}_vs_{safe2}.gnuplot")

        with open(dat_file, "w") as f:
            f.write(f"# col1={dir1}  col2={dir2}\n")
            for _, t1, t2 in rows:
                f.write(f"{t1}\t{t2}\n")

        lbl1 = _gp_str(f"{dir1} [{dir_label[dir1]}]")
        lbl2 = _gp_str(f"{dir2} [{dir_label[dir2]}]")
        title = _gp_str(f"Arjun synth time: {dir1} vs {dir2}")

        with open(gp_file, "w") as f:
            for term, out in [
                (f'pdfcairo size 15cm,15cm background "#d0d0d0"', pdf_file),
                (f'pngcairo size 600,600 background "#d0d0d0"',   png_file),
            ]:
                f.write(f'set terminal {term}\n')
                f.write(f'set output "{out}"\n')
                f.write(f'set title "{title}"\n')
                f.write(f'set xlabel "{lbl1} time (s)"\n')
                f.write(f'set ylabel "{lbl2} time (s)"\n')
                f.write( 'set logscale xy\n')
                f.write(f'set xrange [0.001:{TIMEOUT * 1.1}]\n')
                f.write(f'set yrange [0.001:{TIMEOUT * 1.1}]\n')
                f.write( 'set grid\n')
                f.write( 'set key off\n')
                f.write(f'set arrow 1 from 0.001,0.001 to {TIMEOUT},{TIMEOUT}'
                        f' nohead lc rgb "gray50" lw 1\n')
                f.write(f'plot "{dat_file}" using 1:2 with points pt 7 ps 0.5'
                        f' lc rgb "blue" notitle\n')
                f.write( 'unset arrow 1\n\n')

        _gnuplot_run(gp_file, pdf_file, png_file,
                     f"Scatter: {dir1} vs {dir2} (n={len(rows)})")

    con.close()


def main():
    parser = argparse.ArgumentParser(
        description="Generate CDF/scatter plots and tables for arjun synthesis data")
    parser.add_argument("--verbose", "-v", action="store_true",
                        help="Print progress information")
    parser.add_argument("--full", action="store_true",
                        help="Print full summary table (default: compact)")
    parser.add_argument("--fname", nargs="+", metavar="PATTERN", default=[],
                        help="Filter by fname pattern(s), e.g. --fname '%%amba%%'")
    args = parser.parse_args()

    os.makedirs(TMP_DIR, exist_ok=True)

    if args.fname:
        clauses = " or ".join(f"fname like '{p}'" for p in args.fname)
        fname_like = f" AND ({clauses}) "
    else:
        fname_like = ""

    versions = get_versions()
    matched_dirs = get_matching_dirs(only_dirs)
    if args.verbose:
        print(f"Found {len(versions)} version(s) in database")
        print(f"Matched {len(matched_dirs)} dir(s): {matched_dirs}")

    not_calls    = []
    only_calls   = []
    not_versions = []

    fname2_s, table_todo = build_csv_data(
        versions, matched_dirs, only_calls, not_calls, not_versions,
        fname_like, verbose=args.verbose)

    if not table_todo:
        print(f"{RED}No matching data found.{RESET}")
        return

    print_signal_warnings(table_todo, fname_like)
    print_summary_tables(table_todo, fname_like, full=args.full)
    print_median_tables(table_todo, fname_like)
    print_instance_stats_table(table_todo, fname_like)

    if fname2_s:
        generate_cdf(fname2_s)
    else:
        print(f"{RED}No CDF data (no solved instances?){RESET}")

    scatter_plot_time_pairs(matched_dirs, fname_like, verbose=args.verbose)


if __name__ == "__main__":
    main()
