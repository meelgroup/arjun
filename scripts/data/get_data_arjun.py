#!/usr/bin/python3

import os
import glob
import re
import sqlite3
import argparse


def strip_ansi(text):
    ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')
    return ansi_escape.sub('', text)


def find_arjun_time(fname):
    mem_out = 0
    solved = False
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

    manthan_sampling_time = None
    manthan_training_time = None
    manthan_repair_time = None
    manthan_time = None
    repairs = None
    repairs_failed = None
    repairs_per_sec = None
    manthan_defined = None
    # Manthan may run several strategies in sequence; each resets its rep
    # counter. We accumulate across strategies into `repairs`, using
    # `current_strategy_rep` to hold the in-flight count until the strategy
    # finishes ("Reached max repairs" or "[manthan] Done.") or the run dies.
    current_strategy_rep = 0

    arjun_time = None

    # parsing these:
    # c o [puura] Done. final vars: 1868 final cls: 5184 defined: 1642 still to define: 1654 T: 0.77
    # c o [extend] Done. extend_synth  defined: 834 still to define: 820 T: 0.38
    # c o [backward] Done. backward_round_synth finished  TR: 158 UN: 0 FA: 662 defined: 662 still to define: 158 T: 0.73
    # c o [manthan] Done.  sampl T: 3.72 train T: 44.99 repair T: 0.71 repairs: 75 repair failed: 0 defined: 158 still to define: 0 T: 51.05

    with open(fname, "r") as f:
        for line in f:
            line = strip_ansi(line.strip())

            if "bad_alloc" in line:
                mem_out = 1
            elif line.startswith("c o [arjun] All done."):
                solved = True

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

            # c o [puura] Done. final vars: 1868 final cls: 5184 defined: 1642 still to define: 1654 T: 0.77
            if puura_time is None and "c o [puura] Done." in line:
                match = re.search(r'defined:\s*(\d+)', line)
                if match:
                    puura_defined = int(match.group(1))
                match = re.search(r'T:\s*([\d.]+)', line)
                if match:
                    puura_time = float(match.group(1))

            # c o [extend] Done. extend_synth  defined: 834 still to define: 820 T: 0.38
            if extend_time is None and "c o [extend] Done." in line:
                match = re.search(r'defined:\s*(\d+)', line)
                if match:
                    extend_defined = int(match.group(1))
                match = re.search(r'T:\s*([\d.]+)', line)
                if match:
                    extend_time = float(match.group(1))

            # c o [backward] Done. backward_round_synth finished  TR: 158 UN: 0 FA: 662 defined: 662 still to define: 158 T: 0.73
            if backward_time is None and "c o [backward] Done." in line:
                match = re.search(r'defined:\s*(\d+)', line)
                if match:
                    backward_defined = int(match.group(1))
                match = re.search(r'T:\s*([\d.]+)', line)
                if match:
                    backward_time = float(match.group(1))

            # c o [manthan] rep:   1319   loops:   1319   avg rep/loop:  1.0   ...   T:    1.83   rep/s: 718.8093
            # Progress line. Tail may carry "Reached max repairs" (strategy
            # gave up — commit its rep count) or "DONE" (a [manthan] Done.
            # line will follow, which supplies the final repairs count).
            if "c o [manthan] rep:" in line:
                if repairs is None:
                    repairs = 0
                match = re.search(r'T:\s*([\d.]+)', line)
                if match:
                    manthan_time = float(match.group(1))
                match = re.search(r'rep:\s*(\d+)', line)
                if match:
                    current_strategy_rep = int(match.group(1))
                match = re.search(r'rep/s:\s*([\d.]+)', line)
                if match:
                    repairs_per_sec = float(match.group(1))
                if "Reached max repairs" in line:
                    repairs += current_strategy_rep
                    current_strategy_rep = 0

            # c o [manthan] Done.  sampl T: 3.72 train T: 44.99 repair T: 0.71 repairs: 75 repair failed: 0 defined: 158 still to define: 0 T: 51.05
            if "c o [manthan] Done." in line:
                if repairs is None:
                    repairs = 0
                match = re.search(r'sampl T:\s*([\d.]+)', line)
                if match:
                    manthan_sampling_time = float(match.group(1))
                match = re.search(r'train T:\s*([\d.]+)', line)
                if match:
                    manthan_training_time = float(match.group(1))
                match = re.search(r'repair T:\s*([\d.]+)', line)
                if match:
                    manthan_repair_time = float(match.group(1))
                match = re.search(r'repairs:\s*(\d+)', line)
                if match:
                    repairs += int(match.group(1))
                current_strategy_rep = 0
                match = re.search(r'repair failed:\s*(\d+)', line)
                if match:
                    repairs_failed = int(match.group(1))
                match = re.search(r'defined:\s*(\d+)', line)
                if match:
                    manthan_defined = int(match.group(1))
                # Get the last T: value (total time for manthan)
                matches = re.findall(r'T:\s*([\d.]+)', line)
                if matches:
                    manthan_time = float(matches[-1])

            # c o [arjun] All done. T: 53.52
            if arjun_time is None and "c o [arjun] All done." in line:
                match = re.search(r'T:\s*([\d.]+)', line)
                if match:
                    arjun_time = float(match.group(1))

    # Run died mid-strategy (no "Reached max repairs" or Done. terminator):
    # credit the last progress reading to the accumulated total.
    if repairs is not None:
        repairs += current_strategy_rep

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
        "manthan_sampling_time": manthan_sampling_time,
        "manthan_training_time": manthan_training_time,
        "manthan_repair_time": manthan_repair_time,
        "manthan_time": manthan_time,
        "repairs": repairs,
        "repairs_failed": repairs_failed,
        "repairs_per_sec": repairs_per_sec,
        "manthan_defined": manthan_defined,
        "arjun_time": arjun_time,
        "mem_out": mem_out,
        "solved": solved,
    }


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

    solver = "arjun" if "./arjun" in call_full or "arjun_" in call_full else None

    # Normalize the call for comparison purposes
    call = re.sub(r'arjun[^ ]* ', 'arjun ', call_full)
    call = re.sub(r'^\./doalarm -t real \d+ ', '', call)
    call = re.sub(r'^\./', '', call)
    call = re.sub(r'--verb \S+ ', '', call)
    call = call.strip()

    # If the job was killed by signal, the recorded user time is not a valid solve time
    if signal is not None:
        t = None
    if signal is None:
        signal = 0

    return {
        "timeout_t": t,
        "timeout_mem": mem,
        "timeout_call_full": call_full,
        "timeout_call": call,
        "solver": solver,
        "page_faults": page_faults,
        "signal": signal,
    }


def read_file(fname, files):
    if ".csv" in fname:
        return

    parts = fname.split("/")
    if len(parts) < 2:
        print(f"Skipping unexpected path format: {fname}")
        return

    dirname = parts[0]
    if "competitors" in dirname:
        return

    # Extract base CNF name (everything up to and including .cnf)
    basename = parts[1].split(".cnf")[0] + ".cnf"
    base = dirname + "/" + basename

    if base not in files:
        files[base] = {}
    files[base]["dirname"] = dirname
    files[base]["fname"] = basename

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


COLUMNS = [
    ("solver",                  "TEXT"),
    ("dirname",                 "TEXT"),
    ("fname",                   "TEXT"),
    ("timeout_t",               "REAL"),
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
    ("manthan_sampling_time",   "REAL"),
    ("manthan_training_time",   "REAL"),
    ("manthan_repair_time",     "REAL"),
    ("manthan_time",            "REAL"),
    ("repairs",                 "INTEGER"),
    ("repairs_failed",          "INTEGER"),
    ("repairs_per_sec",         "REAL"),
    ("manthan_defined",         "INTEGER"),
    ("arjun_time",              "REAL"),
    ("mem_out",                 "INTEGER"),
]


def create_db(db_path):
    if os.path.exists(db_path):
        os.remove(db_path)
    conn = sqlite3.connect(db_path)
    col_defs = ", ".join(f"{name} {typ}" for name, typ in COLUMNS)
    conn.execute(f"CREATE TABLE arjun ({col_defs})")
    conn.commit()
    return conn


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
    args = parser.parse_args()

    file_list = glob.glob(args.files)
    if not file_list:
        print(f"No files matched pattern: {args.files}")
        exit(1)
    print(f"Found {len(file_list)} files matching '{args.files}'")

    files = {}
    for f in file_list:
        read_file(f, files)

    print(f"Parsed {len(files)} benchmark entries")

    db_path = "data.sqlite3"
    conn = create_db(db_path)
    insert_rows(conn, files)
    conn.close()

    print(f"Database written to {db_path}")
