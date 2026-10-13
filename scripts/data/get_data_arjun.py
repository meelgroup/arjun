#!/usr/bin/python3

import os
import glob
import re
import sqlite3
import argparse


def strip_ansi(text):
    ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')
    return ansi_escape.sub('', text)


# any "start <label> [get-var-types]"; the raw label is stored as the stage
STAGE_RE = re.compile(r'^c o start (\w+) \[get-var-types\]')


def find_arjun_time(fname):
    mem_out = 0
    solved = False
    # last_stage: last stage entered; last_stage_done: last stage completed.
    last_stage = None
    last_stage_done = None
    arjun_sha1 = None
    sbva_sha1 = None
    cms_sha1 = None

    input_vars = None
    start_to_define_vars = None
    orig_total_vars = None

    puura_time = None
    puura_defined = None

    extend_time = None
    extend_defined = None

    backward_time = None
    backward_defined = None

    cegr_repair_time = None
    cegr_time = None
    repairs = None
    repairs_per_sec = None
    cegr_defined = None
    # cegr may run several strategies in sequence; each resets its rep
    # counter. We accumulate across strategies into `repairs`, using
    # `current_strategy_rep` to hold the in-flight count until the strategy
    # finishes ("Reached max repairs" or "[cegr] Done.") or the run dies.
    current_strategy_rep = 0

    arjun_time = None

    # parsing these:
    # c o [puura] Done. final vars: 1868 final cls: 5184 defined: 1642 still to-define: 1654 T: 0.77
    # c o [extend] Done. extend_synth  defined: 834 still to-define: 820 T: 0.38
    # c o [backward] Done. backward_round_synth finished  TR: 158 UN: 0 FA: 662 defined: 662 still to-define: 158 T: 0.73
    # c o [cegr] Done.  sampl T: 3.72 train T: 44.99 repair T: 0.71 repairs: 75 repair failed: 0 defined: 158 still to-define: 0 T: 51.05

    with open(fname, "r") as f:
        for line in f:
            line = strip_ansi(line.strip())

            # std::bad_alloc throws from C++ new; picosat prints its own
            # "out of memory" message before aborting. Both are OOM.
            if "bad_alloc" in line or "out of memory" in line:
                mem_out = 1
            elif line.startswith("c o [arjun] All done."):
                solved = True

            m = STAGE_RE.match(line)
            if m and m.group(1) != "do_synthesis":
                stage = m.group(1)
                # a new stage starting means the previous one finished
                if last_stage is not None and stage != last_stage:
                    last_stage_done = last_stage
                last_stage = stage

            # c o Arjun SHA1: 8bc2e1402ab782c8ab62aa4d5ffe40eb317691a1
            if arjun_sha1 is None and "c o Arjun SHA1:" in line:
                match = re.search(r'Arjun SHA1:\s*(\w+)', line)
                if match:
                    arjun_sha1 = match.group(1)

            # c o SBVA SHA1: a4d115e1217c40a95bb06bd642aca40d2cee465e
            if sbva_sha1 is None and "c o SBVA SHA1:" in line:
                match = re.search(r'SBVA SHA1:\s*(\w+)', line)
                if match:
                    sbva_sha1 = match.group(1)

            # c o CMS SHA1: 236c4df4ce86ad3869158f96e0bd0e2ee1bd2ee3
            if cms_sha1 is None and "c o CMS SHA1:" in line:
                match = re.search(r'CMS SHA1:\s*(\w+)', line)
                if match:
                    cms_sha1 = match.group(1)

            if "start do_synthesis" in line:
                if input_vars is None and "[get-var-types] Num input vars:" in line:
                    match = re.search(r'Num input vars:\s*(\d+)', line)
                    if match:
                        input_vars = int(match.group(1))

                if start_to_define_vars is None and "[get-var-types] Num to-define vars:" in line:
                    match = re.search(r'Num to-define vars:\s*(\d+)', line)
                    if match:
                        start_to_define_vars = int(match.group(1))

                if orig_total_vars is None and "[get-var-types] Total vars in ORIG CNF:" in line:
                    match = re.search(r'Total vars in ORIG CNF:\s*(\d+)', line)
                    if match:
                        orig_total_vars = int(match.group(1))

            # c o [puura] Done. final vars: 1868 final cls: 5184 defined: 1642 still to-define: 1654 T: 0.77
            if puura_time is None and "c o [puura] Done." in line:
                match = re.search(r'defined:\s*(\d+)', line)
                if match:
                    puura_defined = int(match.group(1))
                match = re.search(r'T:\s*([\d.]+)', line)
                if match:
                    puura_time = float(match.group(1))

            # c o [extend] Done. extend_synth  defined: 834 still to-define: 820 T: 0.38
            if extend_time is None and "c o [extend] Done." in line:
                match = re.search(r'defined:\s*(\d+)', line)
                if match:
                    extend_defined = int(match.group(1))
                match = re.search(r'T:\s*([\d.]+)', line)
                if match:
                    extend_time = float(match.group(1))

            # c o [backward] Done. backward_round_synth finished  TR: 158 UN: 0 FA: 662 defined: 662 still to-define: 158 T: 0.73
            if backward_time is None and "c o [backward] Done." in line:
                match = re.search(r'defined:\s*(\d+)', line)
                if match:
                    backward_defined = int(match.group(1))
                match = re.search(r'T:\s*([\d.]+)', line)
                if match:
                    backward_time = float(match.group(1))

            # c o [cegr] rep:   1319   loops:   1319   avg rep/loop:  1.0   ...   T:    1.83   rep/s: 718.8093
            # Progress line. Tail may carry "Reached max repairs" (strategy
            if "c o [cegr] rep:" in line:
                if repairs is None:
                    repairs = 0
                match = re.search(r'T:\s*([\d.]+)', line)
                if match:
                    cegr_time = float(match.group(1))
                match = re.search(r'rep:\s*(\d+)', line)
                if match:
                    current_strategy_rep = int(match.group(1))
                match = re.search(r'rep/s:\s*([\d.]+)', line)
                if match:
                    repairs_per_sec = float(match.group(1))
                if "Reached max repairs" in line:
                    repairs += current_strategy_rep
                    current_strategy_rep = 0

            # c o [cegr] Done.  sampl T: 3.72 train T: 44.99 repair T: 0.71 repairs: 75 repair failed: 0 defined: 158 still to-define: 0 T: 51.05
            if "c o [cegr] " in line and "DONE" in line:
                if repairs is None:
                    repairs = 0
                match = re.search(r'T:\s*([\d.]+)', line)
                if match:
                    cegr_time = float(match.group(1))
                match = re.search(r'rep:\s*(\d+)', line)
                if match:
                    current_strategy_rep = int(match.group(1))
                match = re.search(r'rep/s:\s*([\d.]+)', line)
                if match:
                    repairs_per_sec = float(match.group(1))

            # c o [arjun] All done. T: 53.52
            if arjun_time is None and "c o [arjun] All done." in line:
                match = re.search(r'T:\s*([\d.]+)', line)
                if match:
                    arjun_time = float(match.group(1))

    # Run died mid-strategy (no "Reached max repairs" or Done. terminator):
    # credit the last progress reading to the accumulated total.
    if repairs is not None:
        repairs += current_strategy_rep

    # solved => the final stage entered also completed
    if solved:
        last_stage_done = last_stage

    return {
        "arjun_sha1": arjun_sha1,
        "sbva_sha1": sbva_sha1,
        "cms_sha1": cms_sha1,
        "input_vars": input_vars,
        "start_to_define_vars": start_to_define_vars,
        "orig_total_vars": orig_total_vars,
        "puura_time": puura_time,
        "puura_defined": puura_defined,
        "extend_time": extend_time,
        "extend_defined": extend_defined,
        "backward_time": backward_time,
        "backward_defined": backward_defined,
        "cegr_repair_time": cegr_repair_time,
        "cegr_time": cegr_time,
        "repairs": repairs,
        "repairs_per_sec": repairs_per_sec,
        "cegr_defined": cegr_defined,
        "arjun_time": arjun_time,
        "last_stage": last_stage,
        "last_stage_done": last_stage_done,
        "mem_out": mem_out,
        "solved": solved,
    }


def find_cadet_time(fname):
    # CADET .out_cadet files are nearly empty. Presence of a bare "SAT" line
    # is the only signal that the synthesis instance was solved; "UNSAT",
    # empty output, and crashes all count as not solved.
    solved = False
    with open(fname, "r") as f:
        for line in f:
            if strip_ansi(line.strip()) == "SAT":
                solved = True
                break
    return {
        "solved": solved,
        "mem_out": 0,
    }


MEM_OUT_RE = re.compile(
    r"bad_alloc|out of memory|OutOfMemoryException|memory allocation of"
    r"|realloc failed|memory manager can't handle the load"
    r"|while reallocating clause space")


def has_mem_out(fname):
    with open(fname, "r", errors="replace") as f:
        return any(MEM_OUT_RE.search(line) for line in f)


def tool_of(cmd):
    name = os.path.basename(cmd.split()[0])
    return "arjun" if name.startswith("arjun") else name


def clean_cmd(cmd):
    cmd = re.sub(r'^\./', '', cmd)
    cmd = re.sub(r'^arjun\S*', 'arjun', cmd)
    cmd = re.sub(r' --verb \S+', '', cmd)
    return re.sub(r' %[io]', '', cmd).strip()


# One 2QBF run (creator_2qbf.sh) is a preprocessor and a solver, each with its
# own log and time file; .out_res has the commands and the RESULT line.
def finalize_2qbf(entry):
    parts = entry.pop("_2qbf")
    if "out_res" not in parts:
        return
    with open(parts["out_res"], "r") as f:
        lines = f.read().splitlines()
    pre = lines[0][len("pre: "):]
    solver = lines[1][len("solver: "):]
    res = [l for l in lines if l.startswith("RESULT")]
    if not res:
        return
    res = dict(x.split("=") for x in res[0].split()[1:])
    has_pre = pre != "none"

    names = []
    if has_pre:
        names.append("arjun-pre" if tool_of(pre) == "arjun" else tool_of(pre))
    names.append("arjun-2qbf" if tool_of(solver) == "arjun" else tool_of(solver))
    entry["solver"] = "+".join(names)
    entry["timeout_call"] = " + ".join(clean_cmd(c) for c in ([pre] if has_pre else []) + [solver])

    tos = [timeout_parse(parts[k]) for k in ("timeout_pre", "timeout_solve") if k in parts]
    entry["timeout_call_full"] = " ; ".join(t["timeout_call_full"] for t in tos)
    entry["timeout_mem"] = max((t["timeout_mem"] for t in tos), default=None)
    entry["page_faults"] = sum(t["page_faults"] or 0 for t in tos)
    entry["signal"] = tos[-1]["signal"] if tos else 0

    total = int(res["total_ms"]) / 1000
    entry["verdict"] = res["verdict"] if res["verdict"] != "UNKNOWN" else None
    entry["res_by"] = res["by"]
    entry["pre_time"] = int(res["pre_ms"]) / 1000 if has_pre else None
    entry["timeout_t_nonnull"] = total
    entry["timeout_t"] = total if entry["verdict"] else None

    arjun_log = "out_pre" if has_pre and tool_of(pre) == "arjun" else \
        "out_solve" if tool_of(solver) == "arjun" else None
    if arjun_log in parts:
        data = find_arjun_time(parts[arjun_log])
        entry.update({k: v for k, v in data.items() if k not in ("solved", "mem_out")})
    entry["mem_out"] = int(any(has_mem_out(parts[k]) for k in ("out_pre", "out_solve") if k in parts))


def timeout_parse(fname):
    t = None
    signal = None
    mem = None
    call_full = None
    page_faults = None

    with open(fname, "r") as f:
        for line in f:
            line = line.strip()
            if "Command terminated by signal" in line:
                signal = int(line.split()[4])
            if "Minor (reclaiming a frame) page faults:" in line:
                page_faults = int(line.split()[6])
            if "User time (seconds)" in line:
                t = float(line.split()[3])
            if "Maximum resident set size (kbytes)" in line:
                mem = float(line.split()[5]) / 1000  # convert to MB
            if "Command being timed" in line:
                # Line format: \tCommand being timed: "..."
                match = re.search(r'Command being timed: "(.+)"', line)
                if match:
                    call_full = match.group(1)

    assert call_full is not None, f"call_full not found in {fname}"
    assert mem is not None, f"mem not found in {fname}"
    assert t is not None, f"t not found in {fname}"

    if "./arjun" in call_full or "arjun_" in call_full:
        solver = "arjun"
    elif "/cadet" in call_full or "cadet_" in call_full:
        solver = "cadet"
    else:
        solver = None

    # Normalize the call for comparison purposes
    call = re.sub(r'arjun[^ ]* ', 'arjun ', call_full)
    call = re.sub(r'^\./doalarm -t real \d+ ', '', call)
    call = re.sub(r'^\./', '', call)
    call = re.sub(r'--verb \S+ ', '', call)
    call = call.strip()

    # User time as reported, kept regardless of signal (unlike timeout_t).
    timeout_t_nonnull = t

    # If the job was killed by signal, the recorded user time is not a valid solve time
    if signal is not None:
        t = None
    if signal is None:
        signal = 0

    return {
        "timeout_t": t,
        "timeout_t_nonnull": timeout_t_nonnull,
        "timeout_mem": mem,
        "timeout_call_full": call_full,
        "timeout_call": call,
        "solver": solver,
        "page_faults": page_faults,
        "signal": signal,
    }


def read_file(fname, files, existing=None):
    if ".csv" in fname:
        return

    parts = fname.split("/")
    if len(parts) < 2:
        print(f"Skipping unexpected path format: {fname}")
        return

    dirname = parts[0]
    if "competitors" in dirname:
        return

    # Strip the .out_<solver> / .timeout_<solver> suffix to get the benchmark
    # filename. Arjun outputs are *.cnf.gz.{out,timeout}_arjun and CADET
    # outputs are *.qdimacs.gz.{out,timeout}_cadet, so we can't rely on a
    # fixed extension being present.
    m = re.match(r'(.+)\.(out|timeout)_\w+$', parts[1])
    if not m:
        return
    basename = m.group(1)
    base = dirname + "/" + basename

    # Incremental: already in the DB from a previous run — skip before doing
    # the expensive file-content parse.
    if existing is not None and (dirname, basename) in existing:
        return

    if base not in files:
        files[base] = {}
    files[base]["dirname"] = dirname
    files[base]["fname"] = basename

    kind = parts[1][len(basename) + 1:]
    if kind in ("out_res", "out_pre", "out_solve", "timeout_pre", "timeout_solve"):
        files[base].setdefault("_2qbf", {})[kind] = fname
        return

    if ".timeout_" in fname:
        data = timeout_parse(fname)
        files[base].update(data)
        return

    if fname.endswith(".out_arjun"):
        files[base]["solver"] = "arjun"
        data = find_arjun_time(fname)
        # If arjun didn't solve it, don't record wall-clock time as a valid solve time
        if not data["solved"]:
            files[base]["timeout_t"] = None
        files[base].update({k: v for k, v in data.items() if k != "solved"})
        return

    if fname.endswith(".out_cadet"):
        files[base]["solver"] = "cadet"
        data = find_cadet_time(fname)
        if not data["solved"]:
            files[base]["timeout_t"] = None
        files[base].update({k: v for k, v in data.items() if k != "solved"})
        return


COLUMNS = [
    ("solver",                  "TEXT"),
    ("dirname",                 "TEXT"),
    ("fname",                   "TEXT"),
    ("timeout_t",               "REAL"),
    ("timeout_t_nonnull",       "REAL"),
    ("timeout_mem",             "REAL"),
    ("timeout_call_full",       "TEXT"),
    ("timeout_call",            "TEXT"),
    ("page_faults",             "INTEGER"),
    ("signal",                  "INTEGER"),
    ("arjun_sha1",              "TEXT"),
    ("sbva_sha1",               "TEXT"),
    ("cms_sha1",                "TEXT"),
    ("input_vars",              "INTEGER"),
    ("start_to_define_vars",    "INTEGER"),
    ("orig_total_vars",         "INTEGER"),
    ("puura_time",              "REAL"),
    ("puura_defined",           "INTEGER"),
    ("extend_time",             "REAL"),
    ("extend_defined",          "INTEGER"),
    ("backward_time",           "REAL"),
    ("backward_defined",        "INTEGER"),
    # ("cmsgen_sampling_time",    "REAL"),
    # ("cegr_sampling_time",   "REAL"),
    ("cegr_repair_time",        "REAL"),
    ("cegr_time",               "REAL"),
    ("repairs",                 "INTEGER"),
    # ("repairs_failed",          "INTEGER"),
    ("repairs_per_sec",         "REAL"),
    ("cegr_defined",            "INTEGER"),
    ("arjun_time",              "REAL"),
    ("last_stage",              "TEXT"),
    ("last_stage_done",         "TEXT"),
    ("mem_out",                 "INTEGER"),
    # 2QBF runs only: TRUE/FALSE, who ended the run (pre, solver, pre_failed,
    # no_time_left) and the preprocessor's wall-clock time
    ("verdict",                 "TEXT"),
    ("res_by",                  "TEXT"),
    ("pre_time",                "REAL"),
]


def open_db(db_path, recreate):
    # recreate: drop any existing DB so only the files given on this run end
    # up in it. Otherwise we open (or create) the DB and append, skipping
    # benchmark entries already present.
    if recreate and os.path.exists(db_path):
        os.remove(db_path)
    conn = sqlite3.connect(db_path)
    col_defs = ", ".join(f"{name} {typ}" for name, typ in COLUMNS)
    conn.execute(f"CREATE TABLE IF NOT EXISTS arjun ({col_defs})")
    have = {row[1] for row in conn.execute("PRAGMA table_info(arjun)")}
    for name, typ in COLUMNS:
        if name not in have:
            conn.execute(f"ALTER TABLE arjun ADD COLUMN {name} {typ}")
    conn.commit()
    return conn


def get_existing_keys(conn):
    # (dirname, fname) pairs already parsed into the DB.
    return set(conn.execute("SELECT dirname, fname FROM arjun"))


def insert_rows(conn, files):
    col_names = [name for name, _ in COLUMNS]
    placeholders = ", ".join("?" for _ in COLUMNS)
    sql = f"INSERT INTO arjun ({', '.join(col_names)}) VALUES ({placeholders})"
    for _, f in files.items():
        if "solver" not in f:
            print(f"WARNING: solver not found for entry, skipping: {f}")
            continue
        row = [f.get(col) for col in col_names]
        conn.execute(sql, row)
    conn.commit()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Parse arjun output files into SQLite database")
    parser.add_argument("--files", default="out-synth-*/*cnf*",
                        help="Glob pattern for files to parse (e.g. 'out-synth-1286344-3/*')")
    parser.add_argument("--recreate", action="store_true",
                        help="Empty the database first and parse only the given files "
                             "(default: accumulate, skipping already-parsed entries)")
    args = parser.parse_args()

    file_list = glob.glob(args.files)
    if not file_list:
        print(f"No files matched pattern: {args.files}")
        exit(1)
    print(f"Found {len(file_list)} files matching '{args.files}'")

    db_path = "data.sqlite3"
    conn = open_db(db_path, args.recreate)
    existing = get_existing_keys(conn)
    if existing:
        print(f"Database already has {len(existing)} benchmark entries")

    files = {}
    for f in file_list:
        read_file(f, files, existing)
    for entry in files.values():
        if "_2qbf" in entry:
            finalize_2qbf(entry)

    print(f"Parsed {len(files)} new benchmark entries")

    insert_rows(conn, files)
    conn.close()

    print(f"Database written to {db_path}")
