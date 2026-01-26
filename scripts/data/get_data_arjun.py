#!/usr/bin/python3

import os
import glob
import re

def strip_ansi(text):
    ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')
    return ansi_escape.sub('', text)


def find_arjun_time(fname):
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
    rapairs_failed = None
    manthan_defined = None

    arjun_time = None

    # parsing these:
    # c o [puura] Done. final vars: 1868 final cls: 5184 defined: 1642 still to define: 1654 T: 0.77
    # c o [extend] Done. unsat_define  defined: 834 still to define: 820 T: 0.38
    # c o [backward] Done. backward_round_synth finished  TR: 158 UN: 0 FA: 662 defined: 662 still to define: 158 T: 0.73
    # c o [manthan] Done.  sampl T: 3.72 train T: 44.99 repair T: 0.71 repairs: 75 repair failed: 0 defined: 158 still to define: 0 T: 51.05

    with open(fname, "r") as f:
        for line in f:
            line = strip_ansi(line.strip())
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

            # c o [extend] Done. unsat_define  defined: 834 still to define: 820 T: 0.38
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

            # c o [manthan] Done.  sampl T: 3.72 train T: 44.99 repair T: 0.71 repairs: 75 repair failed: 0 defined: 158 still to define: 0 T: 51.05
            if manthan_time is None and "c o [manthan] Done." in line:
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
                repairs = int(match.group(1))
              match = re.search(r'repair failed:\s*(\d+)', line)
              if match:
                rapairs_failed = int(match.group(1))
              match = re.search(r'defined:\s*(\d+)', line)
              if match:
                manthan_defined = int(match.group(1))
              # Get the last T: value (total time)
              matches = re.findall(r'T:\s*([\d.]+)', line)
              if matches:
                manthan_time = float(matches[-1])

            # c o [arjun] All done. T: 53.52
            if arjun_time is None and "c o [arjun] All done." in line:
              match = re.search(r'T:\s*([\d.]+)', line)
              if match:
                arjun_time = float(match.group(1))

    return (arjun_sha1, sbva_sha1, cms_sha1,
            input_vars, start_to_define_vars, orig_total_vars,
            puura_time, puura_defined,
            extend_time, extend_defined,
            backward_time, backward_defined,
            manthan_sampling_time, manthan_training_time, manthan_repair_time,
            manthan_time, repairs, rapairs_failed, manthan_defined,
            arjun_time)


def timeout_parse(fname):
    t = None
    signal = None
    mem = None
    call = None
    solver = None
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
                mem = float(line.split()[5])/(1000) # get it in MB
            if "Command being timed" in line:
                call= " ".join(line.split()[3:])
                if "mc2022" in call:
                    call = call.split("mc2022_")[0]
                elif "mc2023" in call:
                    call = call.split("mc2023_")[0]
                else:
                  call = " ".join(call.split()[:-1])

                call = call.replace(" -t real", "")
                if "doalarm 3600" in call:
                  call = call.split("doalarm 3600")[1]

                if "./arjun" in call: solver = "arjun"

                call = call.replace("././arjun ", "")
                call = call.strip()

    if signal is not None:
      t = None
    if signal is None:
      signal = ""
    return [t, mem, call, solver, page_faults, signal]


def add(name, f):
    if name not in f or f[name] is None:
        return ","
    else:
        return "%s," % (f[name])


def fill_row(f):
    toprint = ""
    toprint += "%s," % f["solver"]
    toprint += f["dirname"] + ","
    toprint += f["fname"] + ","

    # check solver parsed
    if "solver" not in f:
        print("oops, solver not found, that's wrong")
        print(f)
        exit(-1)

    #timeout_t, timeout_mem, timeout_call
    toprint += add("timeout_t", f)
    toprint += add("timeout_mem", f)
    toprint += add("timeout_call", f)
    toprint += add("page_faults", f)
    toprint += add("signal", f)

    # arjun data
    toprint += add("arjun_sha1", f)
    toprint += add("sbva_sha1", f)
    toprint += add("cms_sha1", f)
    toprint += add("input_vars", f)
    toprint += add("start_to_define_vars", f)
    toprint += add("orig_total_vars", f)
    toprint += add("puura_time", f)
    toprint += add("puura_defined", f)
    toprint += add("extend_time", f)
    toprint += add("extend_defined", f)
    toprint += add("backward_time", f)
    toprint += add("backward_defined", f)
    toprint += add("manthan_sampling_time", f)
    toprint += add("manthan_training_time", f)
    toprint += add("manthan_repair_time", f)
    toprint += add("manthan_time", f)
    toprint += add("repairs", f)
    toprint += add("repairs_failed", f)
    toprint += add("manthan_defined", f)
    toprint += add("arjun_time", f)
    toprint = toprint[:-1]  # remove last ,

    return toprint

def read_file(fname):
    if ".csv" in fname:
        return
    print("parsing file: ", fname)

    dirname = fname.split("/")[0]
    if "competitors" in dirname:
        return

    full_fname = fname.split("/")[1].split(".cnf")[0] + ".cnf"
    base = dirname+"/"+full_fname
    if base not in files:
        files[base] = {}
    files[base]["dirname"] = dirname
    files[base]["fname"] = full_fname
    # print("Dealing with dir: %s fname: %s" % (dirname, full_fname))

    if ".timeout_" in fname:
        timeout_t, timeout_mem, timeout_call, timeout_solver, page_faults, signal = timeout_parse(fname)
        files[base]["timeout_t"] = timeout_t
        files[base]["timeout_mem"] = timeout_mem
        files[base]["timeout_call"] = timeout_call
        files[base]["page_faults"] = page_faults
        files[base]["signal"] = signal
        if "solver" not in files[base] or files[base]["solver"] is None:
          files[base]["solver"] = timeout_solver
        return

    if  fname.endswith(".out_synth"):
        files[base]["solver"] = "arjun"
        (arjun_sha1, sbva_sha1, cms_sha1,
         input_vars, start_to_define_vars, orig_total_vars,
         puura_time, puura_defined,
         extend_time, extend_defined,
         backward_time, backward_defined,
         manthan_sampling_time, manthan_training_time, manthan_repair_time,
         manthan_time, repairs, rapairs_failed, manthan_defined,
         arjun_time) = find_arjun_time(fname)
        files[base]["arjun_sha1"] = arjun_sha1
        files[base]["sbva_sha1"] = sbva_sha1
        files[base]["cms_sha1"] = cms_sha1
        files[base]["input_vars"] = input_vars
        files[base]["start_to_define_vars"] = start_to_define_vars
        files[base]["orig_total_vars"] = orig_total_vars
        files[base]["puura_time"] = puura_time
        files[base]["puura_defined"] = puura_defined
        files[base]["extend_time"] = extend_time
        files[base]["extend_defined"] = extend_defined
        files[base]["backward_time"] = backward_time
        files[base]["backward_defined"] = backward_defined
        files[base]["manthan_sampling_time"] = manthan_sampling_time
        files[base]["manthan_training_time"] = manthan_training_time
        files[base]["manthan_repair_time"] = manthan_repair_time
        files[base]["manthan_time"] = manthan_time
        files[base]["repairs"] = repairs
        files[base]["repairs_failed"] = rapairs_failed
        files[base]["manthan_defined"] = manthan_defined
        files[base]["arjun_time"] = arjun_time
        return


if __name__ == "__main__":
    file_list = glob.glob("out-arjun-*/*cnf*")
    file_list.extend(glob.glob("out-others-*/*cnf*"))
    files = {}
    for f in file_list:
        read_file(f)

    with open("mydata.csv", "w") as out:
        cols = "solver,dirname,fname,timeout_t,timeout_mem,timeout_call,page_faults,signal,arjun_sha1,sbva_sha1,cms_sha1,input_vars,start_to_define_vars,orig_total_vars,puura_time,puura_defined,extend_time,extend_defined,backward_time,backward_defined,manthan_sampling_time,manthan_training_time,manthan_repair_time,manthan_time,repairs,repairs_failed,manthan_defined,arjun_time"
        out.write(cols+"\n")
        for _, f in files.items():
            toprint = fill_row(f)
            out.write(toprint+"\n")

    os.system("sqlite3 mydb.sql < arjun.sql")
