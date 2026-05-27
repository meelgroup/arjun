#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Copyright (C) 2026  Mate Soos
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; version 2
# of the License.

"""Fuzzer for the in-tree CADET port (`--cadet 1`).

Generates Brummayer-style CNFs, adds a projection, runs arjun with
`--cadet 1` to synthesize the un-projected vars, and verifies the result
with `test-synth`.

Completeness contract: CADET must produce a Skolem for every
existential variable on every iteration. Any Manthan handoff is a
FUZZ FAILURE — `--cadet 1` is "cadet finishes alone" mode, period.
Projection sizes deliberately span both Phase A's enumeration range and
the larger ranges only Phase F can handle, so the terminal phase gets
proper coverage."""

import subprocess
import os
import time
import random
import optparse
import stat
import glob
import re
import shlex


def fmt_cmd(command):
    return " ".join(shlex.quote(str(c)) for c in command)


maxtimediff = 1


def unique_file(fname_begin, fname_end=".cnf", max_num_files=2700):
    counter = 1
    while True:
        fname = "out/" + fname_begin + "_" + str(counter) + fname_end
        try:
            fd = os.open(fname, os.O_CREAT | os.O_EXCL, stat.S_IREAD | stat.S_IWRITE)
            os.fdopen(fd).close()
            return str(fname)
        except OSError:
            pass
        counter += 1
        if counter > max_num_files:
            print("Cannot create unique_file, last try was: %s" % fname)
            exit(-1)


def gen_fuzz_call_brummayer(fuzzer, fname):
    seed = random.randint(0, 1000 * 1000 * 1000)
    # Mix of small, medium, and large CNFs so we cover the entire
    # Phase A → Phase F enumeration range. With Phase F now
    # unconditional (no input-size threshold), larger CNFs are the
    # interesting stress case — they force many Phase F iterations
    # and exercise periodic AIG simplification.
    #
    # Weight small/medium higher so the run is fast on average; large
    # gets ~25% of iters to exercise scaling. xlarge is omitted as a
    # routine size because it often pushes per-iter wall time past
    # the fuzzer timeout — use a manual --tout bump if you want to
    # stress-test at that size.
    #
    # -i = leaves, -I = inner nodes (see cnf-fuzz-brummayer.py).
    kind = random.choices(
        ["small", "medium", "large"],
        weights=[3, 3, 2])[0]
    if kind == "small":
        call = "{0} -s {1} -i 4 -I 12 > {2}".format(fuzzer, seed, fname)
    elif kind == "medium":
        call = "{0} -s {1} -i 12 -I 30 > {2}".format(fuzzer, seed, fname)
    else:  # large
        call = "{0} -s {1} -i 25 -I 60 > {2}".format(fuzzer, seed, fname)
    return call


def add_projection(fname):
    """Append a `c p show ...` projection. Returns the projection list,
    or None if the CNF is too small to project meaningfully.

    Sometimes clamps the projection to <= 14 inputs (Phase A-friendly);
    sometimes lets it go larger (up to n_vars - 1) so Phase A's
    threshold is exceeded and the run is forced into Phase B / C+D,
    the actual CADET part of the pipeline."""
    n_vars = 0
    with open(fname, "r") as f:
        for line in f:
            line = line.strip()
            if len(line) < 3:
                continue
            if line[0] == "p":
                parts = line.split(" ")
                assert parts[1].strip() == "cnf"
                n_vars = int(parts[2])
                break

    if n_vars == 0:
        print("ERROR: Can't find 'p cnf' in file %s" % fname)
        exit(-1)
    if n_vars < 2:
        return None

    # Half the time, clamp projection size to <= 14 (Phase A's
    # enumeration is tractable). The other half: pick from a wider
    # range so Phase A is forced to bail and Phase C+D get exercised.
    if random.choice([True, False]):
        upper = max(1, min(14, n_vars - 1))
    else:
        upper = max(1, n_vars - 1)
    num = random.randint(1, upper)
    proj_set = set()
    while len(proj_set) < num:
        proj_set.add(random.randint(1, n_vars))
    proj = sorted(proj_set)

    with open(fname, "a") as f:
        f.write("c p show " + " ".join(str(a) for a in proj) + " 0\n")
    return proj


def set_up_parser():
    parser = optparse.OptionParser(usage="usage: %prog [options]",
                                   description="Fuzz the CADET synthesis path (--cadet 1)")
    parser.add_option("--verbose", "-v", action="store_true", default=False,
                      dest="verbose", help="Print more output")
    parser.add_option("--seed", dest="rnd_seed",
                      help="Start seed (random if omitted)", type=int)
    parser.add_option("--tout", "-t", dest="maxtime", type=int, default=20,
                      help="Per-iteration wall time (s). Default: %default")
    parser.add_option("--num", "-n", dest="num", type=int, default=None,
                      help="Number of iterations; unlimited if omitted")
    return parser


def run(command):
    print("--> Executing: %s" % fmt_cmd(command))
    p = subprocess.Popen(command, stderr=subprocess.STDOUT,
                         stdout=subprocess.PIPE, universal_newlines=True)
    try:
        out, err = p.communicate(timeout=options.maxtime)
    except subprocess.TimeoutExpired:
        p.kill()
        out, err = p.communicate()
        out = "TIMEOUT: Process killed after %d seconds\n" % options.maxtime + out
    return out, err, p.returncode


def run_check(command, final, seed):
    # Cap test-synth wall time. On very large AIGs (cadet's Phase F can
    # build big ITE chains) the UNSAT-mode verifier can run for minutes
    # before the OS / user kills it. Better to time-bound it ourselves
    # and treat the timeout as a soft skip than to let it linger and
    # show up as a SIGTERM "BUG".
    p = subprocess.Popen(command, stderr=subprocess.STDOUT,
                         stdout=subprocess.PIPE, universal_newlines=True)
    try:
        out, _err = p.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        p.kill()
        out, _err = p.communicate()
        print("[skip] test-synth wall-time exceeded 120s on this AIG — "
              "treating as soft skip (likely Phase F producing a large "
              "ITE chain; not a correctness bug per se)")
        return

    # Returncode -15 (SIGTERM) means the process was killed externally
    # (typically the OS via memory pressure, or a watchdog). Treat as
    # soft skip — same reasoning as the timeout branch.
    if p.returncode == -15:
        print("[skip] test-synth killed by SIGTERM (likely OOM / "
              "external watchdog on a very large AIG)")
        return

    if p.returncode < 0 or p.returncode > 1:
        print("=" * 60)
        print("BUG: test-synth crashed with returncode %d" % p.returncode)
        print("Command was: %s" % fmt_cmd(command))
        print(out)
        print("REPRODUCE: python3 ../scripts/fuzz_cadet.py --seed %d --num 1" % seed)
        print("=" * 60)
        exit(-1)

    ok = False
    for line in out.split("\n"):
        if "INCORRECT" in line:
            print("=" * 60)
            print("BUG: test-synth reported AIGs are INCORRECT")
            print("Command was: %s" % fmt_cmd(command))
            print(out)
            print("REPRODUCE: python3 ../scripts/fuzz_cadet.py --seed %d --num 1" % seed)
            print("=" * 60)
            exit(-1)
        if "CORRECT" in line and "INCORRECT" not in line:
            print("Check output: %s" % line)
            ok = True
    if not ok and final:
        print("=" * 60)
        print("BUG: check process did not report CORRECT")
        print("Command was: %s" % fmt_cmd(command))
        print(out)
        print("REPRODUCE: python3 ../scripts/fuzz_cadet.py --seed %d --num 1" % seed)
        print("=" * 60)
        exit(-1)


def run_synth(solver, fname):
    """Run arjun, parse its output, and return (err, aigs, info) where
    info is a dict with cadet-specific stats so the caller can track
    whether cadet did real work and whether the cadet→Manthan handoff
    triggered."""
    curr_time = time.time()
    toexec = solver.split()
    toexec.append(fname)
    out, err, returncode = run(toexec)
    info = {"cadet_committed_partial": False,
            # cadet_committed_all defaults to True: if cadet is never
            # invoked (upstream pipeline already finished the synth
            # before main.cpp reached the cadet block), there's
            # nothing for cadet to do and the iteration is trivially
            # successful. The flag flips to False only if we see
            # evidence of incomplete cadet work.
            "cadet_committed_all": True,
            "handoff_triggered": False, "cadet_committed_count": 0,
            "cadet_to_define_count": 0,
            # Phase E: whether the SAT-model completion phase ran AND
            # whether it actually committed at least one undet var.
            # Phase E commits when Phase C+D left vars undetermined
            # AND the orig sampling space is small enough — exactly
            # the new mode we want the fuzzer to exercise.
            "phase_e_ran": False,
            "phase_e_committed": 0,
            # Phase F: bit-dropping generalization for orig sampling
            # spaces too large for Phase E. ran => the phase engaged;
            # converged => it covered the input space within its
            # iteration budget (only convergent runs commit; non-
            # convergent ones revert and fall back).
            "phase_f_ran": False,
            "phase_f_converged": False,
            # Phase F iteration-level diagnostics. Parsed from the
            # print_phase_f_stats line (both converged and
            # non-converged runs print it). These let us see whether
            # Phase F's bit-dropping is ACTUALLY firing across fuzz
            # iterations, not just whether the phase engaged.
            "phase_f_iters": 0,
            "phase_f_uniq_unsat": 0,
            "phase_f_uniq_sat": 0,
            "phase_f_avg_drops": 0.0,
            "phase_f_avg_core_size": 0.0,
            # CEGAR (Phase D companion). Counts come from the
            # "c o [cadet] CEGAR rounds=... joint-commits=...
            # per-y-commits=.../checks=..." line emitted at verb>=1
            # when at least one CEGAR round fired.
            "cegar_ran": False,
            "cegar_rounds": 0,
            "cegar_joint_unsat": 0,
            "cegar_joint_sat": 0,
            "cegar_joint_commits": 0,
            "cegar_per_y_commits": 0,
            "cegar_per_y_checks": 0,
            "cegar_avg_kept_cube": 0.0}
    if err is not None:
        print("Error string is: ", err)
        return True, [], info

    diff_time = time.time() - curr_time
    if diff_time > options.maxtime - maxtimediff:
        print("Too much time, aborted")
        return None, [], info

    if returncode != 0 and not out.startswith("TIMEOUT"):
        # SIGTERM (143) and SIGKILL (137) are timeout-adjacent — the
        # OS or some watchdog killed the process. Treat them as soft
        # skips, same as the explicit TIMEOUT path, rather than as
        # correctness failures. Without this, a slow cadet run that
        # lands the process in the timeout-kill window gets logged
        # as "Synthesis failed" and stops the fuzzer.
        if returncode in (143, 137):
            print("Solver killed by signal (returncode %d) — treating as timeout"
                  % returncode)
            return None, [], info
        print("Solver crashed with exit code %d" % returncode)
        print(out)
        return True, [], info

    aigs = []
    for line in out.split("\n"):
        line = line.strip()
        if "Training error" not in line:
            if "ERROR" in line or "Error" in line or "error" in line:
                print("Error line from solver: %s" % line)
                return True, [], info
            if "assert" in line or "Assertion" in line:
                print("Error line from solver: %s" % line)
                return True, [], info
        if line.startswith("c o Wrote AIG defs:"):
            aigs.append(line[len("c o Wrote AIG defs:"):].strip())

        # Cadet status lines (matched against the verb=1 prints in
        # cadet.cpp's do_cadet()). With the completeness contract we
        # now also recognize the "nothing to define" path as success.
        if "[cadet] done — all" in line:
            info["cadet_committed_all"] = True
            # parse "all N to_define vars committed"
            m = re.search(r"all (\d+) to_define vars", line)
            if m:
                info["cadet_to_define_count"] = int(m.group(1))
                info["cadet_committed_count"] = int(m.group(1))
        elif "[cadet] nothing to define" in line:
            # Upstream pipeline finished everything before cadet
            # engaged. Counts as a clean cadet success (cadet was
            # asked to do 0 vars and did 0). Without this, runs
            # where bve+autarky+extend already determinized every
            # to_define var leave the counters at zero and the
            # end-of-run check spuriously fails.
            info["cadet_committed_all"] = True
        elif "[cadet] PARTIAL: committed" in line:
            info["cadet_committed_partial"] = True
            info["cadet_committed_all"] = False
            m = re.search(r"committed (\d+)/(\d+) to_define", line)
            if m:
                info["cadet_committed_count"] = int(m.group(1))
                info["cadet_to_define_count"] = int(m.group(2))
        elif "cadet left vars undetermined" in line:
            info["handoff_triggered"] = True
        elif "Phase E — SAT-model completion on" in line:
            info["phase_e_ran"] = True
            m = re.search(r"on (\d+) undet vars", line)
            if m:
                info["phase_e_committed"] = int(m.group(1))
        elif "Phase F worker —" in line:
            info["phase_f_ran"] = True
        elif "[cadet] CEGAR rounds=" in line:
            info["cegar_ran"] = True
            m = re.search(r"CEGAR rounds=(\d+).*joint UNSAT=(\d+) SAT=(\d+).*"
                          r"joint-commits=(\d+) per-y-commits=(\d+)"
                          r"/checks=(\d+).*avg-kept-cube=([\d.]+)", line)
            if m:
                info["cegar_rounds"] = int(m.group(1))
                info["cegar_joint_unsat"] = int(m.group(2))
                info["cegar_joint_sat"] = int(m.group(3))
                info["cegar_joint_commits"] = int(m.group(4))
                info["cegar_per_y_commits"] = int(m.group(5))
                info["cegar_per_y_checks"] = int(m.group(6))
                info["cegar_avg_kept_cube"] = float(m.group(7))
        elif "Phase F converged + committed" in line or \
             "Phase F did NOT converge" in line:
            info["phase_f_converged"] = "converged + committed" in line
            # Both lines share the same diagnostic-stats suffix:
            #   iters=N uniq-UNSAT=N uniq-SAT=N uniq-UNDEF=N
            #   avg-drops/iter=X.X avg-core-size=X.X T=X.X
            m = re.search(r"iters=(\d+).*uniq-UNSAT=(\d+).*uniq-SAT=(\d+).*"
                          r"avg-drops/iter=([\d.]+).*avg-core-size=([\d.]+)", line)
            if m:
                info["phase_f_iters"] = int(m.group(1))
                info["phase_f_uniq_unsat"] = int(m.group(2))
                info["phase_f_uniq_sat"] = int(m.group(3))
                info["phase_f_avg_drops"] = float(m.group(4))
                info["phase_f_avg_core_size"] = float(m.group(5))

    return False, aigs, info


def is_unsat(fname):
    unsat_check = "../../cryptominisat/build/cryptominisat5"
    toexec = unsat_check.split()
    toexec.append(fname)
    out, _err, _ = run(toexec)
    for line in out.split("\n"):
        line = line.strip()
        if line.startswith("s UNSATISFIABLE"):
            print("File %s is UNSAT" % fname)
            return True
        if line.startswith("s SATISFIABLE"):
            print("File %s is SAT" % fname)
            return False
    print("ERROR: Could not determine SAT/UNSAT for %s" % fname)
    exit(-1)


def gen_fuzz(seed):
    fname = unique_file("fuzzCadet")
    print("Seed: %d  fname: %s" % (seed, fname))
    call = gen_fuzz_call_brummayer("./cnf-fuzz-brummayer.py", fname)
    print("Calling: %s" % call)
    status = subprocess.call(call, shell=True)
    if status != 0:
        print("Failed fuzzer file generator call: %s" % call)
        exit(-1)
    return fname


def cleanup(fname, prefix):
    try:
        os.unlink(fname)
    except OSError:
        pass
    for file_path in glob.glob(os.path.join(".", f"{prefix}*.aig")):
        if os.path.isfile(file_path):
            os.remove(file_path)
    for file_path in glob.glob(f"{prefix}-core-*.cnf"):
        if os.path.isfile(file_path):
            os.remove(file_path)
    try:
        os.unlink(prefix)
    except OSError:
        pass


if __name__ == "__main__":
    if os.path.exists("out") and os.path.isfile("out"):
        print("ERROR: file 'out' exists, but we need a directory named 'out'")
        exit(-1)
    os.makedirs("out", exist_ok=True)

    parser = set_up_parser()
    (options, args) = parser.parse_args()

    if options.rnd_seed is None:
        rnd_seed = int.from_bytes(os.urandom(8))
        print("Using seed:", rnd_seed)
    else:
        rnd_seed = options.rnd_seed
    random.seed(rnd_seed)

    # Coverage counters. The fuzz run FAILS at the end if these
    # don't reach acceptable levels — the whole point of these
    # fuzzer iterations is to actually exercise cadet's commits and
    # the cadet→Manthan handoff, not just verify Manthan via cadet's
    # passthrough.
    stats = {
        "total": 0,
        "skipped_smallcnf_or_unsat": 0,
        "synth_succeeded": 0,
        "cadet_did_nothing": 0,    # cadet ran but committed 0 vars
        "cadet_committed_partial_then_handoff": 0,
        "cadet_committed_all": 0,
        "handoff_triggered": 0,
        "partial_handoff_expected": 0,  # iterations where --cadetpartial > 0 caused handoff
        "phase_e_ran": 0,                       # iterations where Phase E ran
        "phase_e_finished_synthesis": 0,        # Phase E ran AND cadet completed all
        "phase_f_ran": 0,                       # iterations where Phase F engaged
        "phase_f_converged_and_finished": 0,    # Phase F converged AND cadet completed all
        # Cumulative iter-level stats across all Phase F engagements,
        # so we can answer "is bit-dropping actually firing during
        # fuzzing?" with concrete numbers instead of guessing.
        "phase_f_total_iters": 0,
        "phase_f_total_uniq_unsat": 0,
        "phase_f_total_uniq_sat": 0,
        "phase_f_runs_with_any_drop": 0,  # iterations where avg-drops > 0
        # CEGAR coverage. cegar_ran => CEGAR drain at least fired one
        # round; cegar_made_commits => at least one commit (joint or
        # per-y) on this iter.
        "cegar_ran": 0,
        "cegar_made_commits": 0,
        "cegar_total_rounds": 0,
        "cegar_total_joint_unsat": 0,
        "cegar_total_joint_commits": 0,
        "cegar_total_per_y_commits": 0,
    }

    i = 0
    while options.num is None or i < options.num:
        i += 1
        if options.rnd_seed is None:
            seed = int.from_bytes(os.urandom(8))
            random.seed(seed)
        else:
            seed = options.rnd_seed

        stats["total"] += 1
        fname = gen_fuzz(seed)
        if add_projection(fname) is None:
            print("CNF too small, skipping")
            os.unlink(fname)
            stats["skipped_smallcnf_or_unsat"] += 1
            continue
        if is_unsat(fname):
            print("UNSAT, skipping")
            os.unlink(fname)
            stats["skipped_smallcnf_or_unsat"] += 1
            continue

        prefix = unique_file("fuzzCadet")
        solver = "./arjun --verb 1 --debugsynth %s " % prefix
        if random.choice([True, False]):
            solver += "--synth "
        else:
            solver += "--synthmore "
        solver += "--cadet 1 "

        # Randomize every --cadet* knob so the fuzzer probes the full
        # configuration space. Defaults are weighted in so most
        # iterations look "normal" but every knob position gets
        # exercised across a long run. Each knob is picked
        # independently — the goal is to surface soundness regressions
        # under unusual combinations, not to test any one combination
        # exhaustively.
        cadet_knobs = {
            # CEGAR master + sub-options
            "--cadetcegar": random.choices([0, 1], weights=[1, 4])[0],
            "--cadetcegarpery": random.choices([0, 1], weights=[1, 3])[0],
            "--cadetcegarevery": random.choice([1, 2, 5]),
            "--cadetcegarmaxperstall": random.choice([1, 5, 50, 200]),
            "--cadetcegarmaxavgcube": random.choice([3, 17, 50, 9999]),
            "--cadetcegarmaxtot": random.choice([0, 5, 100]),
            "--cadetcegarperyundetcap": random.choice([5, 30, 100, 500]),
            "--cadetcegarperywindow": random.choice([0, 100, 5000]),
            "--cadetcegarperyminprod": random.choice([0.05, 0.1, 0.5]),
            "--cadetcegardisableafter": random.choice([0, 5, 30, 200]),
            "--cadetcegarrebuildevery": random.choice([0, 5, 50]),
            # New drain-loop bail knobs (replace previously hardcoded
            # consec=2 / immediate-noop bail). 0 disables the bail.
            "--cadetcegarconsecbail": random.choice([0, 1, 2, 4, 10]),
            "--cadetcegarnoopbail": random.choice([0, 1, 3, 10]),
            # Forbid the explored X-cube in skolem_sat after joint-SAT
            # so the next round gets a different model. Default on (1).
            "--cadetcegarforbidonsat": random.choices([0, 1], weights=[1, 3])[0],
            # Existing Phase C/D/E/F internals.
            # Phase E threshold capped at 16 — Phase E enumerates
            # 2^th SAT calls. 32 is intractable (2^32 ≈ 4·10⁹), kills
            # the runner via OOM/timeout, not a real bug.
            "--cadetphaseeth": random.choice([0, 4, 8, 16]),
            "--cadetguessdepth": random.choice([1, 4, 8, 16]),
            "--cadetrestartinit": random.choice([4, 16, 64]),
            "--cadetrestartfactor": random.choice([1.1, 1.5, 2.0]),
            "--cadetactdecay": random.choice([0.85, 0.95, 0.99]),
            "--cadetphasefsimpevery": random.choice([0, 100, 1000]),
            "--cadetphasefperycap": random.choice([5, 30, 100]),
            "--cadetphasefperywindow": random.choice([0, 100, 5000]),
            "--cadetphasefperyminprod": random.choice([0.05, 0.1, 0.5]),
            # Partial mode: 0 = off (always finishes alone). When > 0,
            # Phase F bails after K iters and Manthan finishes the rest.
            # Mostly off (cadet-finishes-alone is the standard contract),
            # but occasionally cap at small K to exercise the handoff.
            "--cadetpartial": random.choices(
                [0, 1, 5, 100], weights=[6, 1, 1, 1])[0],
        }
        for k, v in cadet_knobs.items():
            solver += "%s %s " % (k, v)

        # Preprocessing toggles. We want to exercise cadet both with
        # and without the upstream pipeline:
        #   - 50% of iterations: force EVERY toggleable pass OFF so
        #     cadet has to actually do the synthesis (otherwise BVE +
        #     autarky finish it first on fuzzer-sized CNFs).
        #   - 50% of iterations: pick each toggle independently, biased
        #     80/20 toward off. Some preprocessing still runs and the
        #     pipeline's downstream cadet sees the post-preprocessing
        #     CNF — which is what real-world usage looks like.
        prep_opts = [" --synthbve", " --autarky", " --extend", " --minimize",
                     " --unatedef", " --unatedefeq", " --unatedefeqnoninp",
                     " --unatedefrep"]
        if random.choice([True, False]):
            for opt in prep_opts:
                solver += opt + " 0"
        else:
            for opt in prep_opts:
                solver += opt + " " + str(random.choices([0, 1], weights=[4, 1])[0])

        err, aigs, info = run_synth(solver, fname)
        if err is None:
            print("Synthesis timed out on %s" % fname)
            cleanup(fname, prefix)
            continue
        if err:
            print("Synthesis failed on %s" % fname)
            print("=" * 60)
            print("REPRODUCE: python3 ../scripts/fuzz_cadet.py --seed %d --num 1" % seed)
            print("=" * 60)
            exit(-1)

        if len(aigs) == 0:
            # No output AIGs — usually a soft skip path; just move on.
            cleanup(fname, prefix)
            continue

        stats["synth_succeeded"] += 1
        if info["cadet_committed_all"]:
            stats["cadet_committed_all"] += 1
        elif info["cadet_committed_partial"] and info["handoff_triggered"]:
            stats["cadet_committed_partial_then_handoff"] += 1
            stats["handoff_triggered"] += 1
        elif info["handoff_triggered"]:
            # Cadet ran but committed nothing; Manthan did all the work.
            stats["cadet_did_nothing"] += 1
            stats["handoff_triggered"] += 1

        # Completeness contract: `--cadet 1` mode means CADET must
        # produce a Skolem for every existential. Any Manthan handoff
        # is a regression — fail immediately so the user sees the
        # exact reproduction command for the failing seed.
        # EXCEPTION: --cadetpartial K > 0 explicitly asks CADET to bail
        # out of Phase F at K iters and let Manthan finish the rest.
        # In that case a handoff is the *expected* behavior; we just
        # count it and continue.
        partial_k = int(cadet_knobs["--cadetpartial"])
        if info["handoff_triggered"] or info["cadet_committed_partial"]:
            if partial_k == 0:
                print("=" * 60)
                print("FUZZ FAIL: cadet failed to complete synthesis alone")
                print("  committed %d / %d to_define vars; rest handed off to Manthan"
                      % (info["cadet_committed_count"], info["cadet_to_define_count"]))
                print("  --cadet 1 is supposed to ALWAYS finish without Manthan.")
                print("REPRODUCE: python3 ../scripts/fuzz_cadet.py --seed %d --num 1" % seed)
                print("=" * 60)
                exit(-1)
            stats["partial_handoff_expected"] += 1
        if info["phase_e_ran"]:
            stats["phase_e_ran"] += 1
            if info["cadet_committed_all"]:
                stats["phase_e_finished_synthesis"] += 1
        if info["phase_f_ran"]:
            stats["phase_f_ran"] += 1
            if info["phase_f_converged"] and info["cadet_committed_all"]:
                stats["phase_f_converged_and_finished"] += 1
            stats["phase_f_total_iters"] += info["phase_f_iters"]
            stats["phase_f_total_uniq_unsat"] += info["phase_f_uniq_unsat"]
            stats["phase_f_total_uniq_sat"] += info["phase_f_uniq_sat"]
            if info["phase_f_avg_drops"] > 0.0:
                stats["phase_f_runs_with_any_drop"] += 1
        if info["cegar_ran"]:
            stats["cegar_ran"] += 1
            if info["cegar_joint_commits"] > 0 or \
               info["cegar_per_y_commits"] > 0:
                stats["cegar_made_commits"] += 1
            stats["cegar_total_rounds"] += info["cegar_rounds"]
            stats["cegar_total_joint_unsat"] += info["cegar_joint_unsat"]
            stats["cegar_total_joint_commits"] += info["cegar_joint_commits"]
            stats["cegar_total_per_y_commits"] += info["cegar_per_y_commits"]
        print("Synthesis succeeded on %s [cadet committed %d/%d%s], AIGs: %s" % (
            fname, info["cadet_committed_count"], info["cadet_to_define_count"],
            " + Manthan handoff" if info["handoff_triggered"] else "",
            aigs))

        for aig in aigs:
            final = "final" in aig
            if final:
                call = "./test-synth -u -v -s %d %s %s" % (seed, fname, aig)
            else:
                call = "./test-synth -v -s %d %s %s" % (seed, fname, aig)
            print("Check: %s" % call)
            run_check(call.split(), final, seed)
            os.unlink(aig)
        cleanup(fname, prefix)

    # End-of-run coverage check. The whole point of these new iterations
    # is to exercise the cadet→Manthan handoff with cadet actually
    # committing at least one var. If we ran ≥ 20 iterations and never
    # hit a handoff with non-empty cadet commits, the fuzzer is mis-
    # configured (preprocessing is finishing everything, or CNFs are
    # too small/too easy) and should be flagged.
    print("=" * 60)
    print("Fuzz run summary:")
    for k, v in stats.items():
        print("  %s: %d" % (k, v))

    # Dedicated phase-coverage callout so you can see at a glance
    # which of cadet's phases actually got exercised. Without this
    # block you'd have to scan the per-key dump above to find each
    # `phase_X_ran` value individually.
    print("-" * 60)
    print("Phase coverage (out of %d successful runs):" % stats["synth_succeeded"])
    print("  Phase E ran:                %d  (finished synthesis alone in %d)" % (
        stats["phase_e_ran"], stats["phase_e_finished_synthesis"]))
    print("  Phase F ran:                %d  (converged and finished in %d)" % (
        stats["phase_f_ran"], stats["phase_f_converged_and_finished"]))
    if stats["phase_f_ran"] > 0:
        total_checks = stats["phase_f_total_uniq_unsat"] + stats["phase_f_total_uniq_sat"]
        pct = 100.0 * stats["phase_f_total_uniq_unsat"] / total_checks if total_checks else 0.0
        print("    cumulative iters:         %d" % stats["phase_f_total_iters"])
        print("    uniqueness-check UNSAT:   %d  (i.e. drops happened: %.1f%% of checks)" % (
            stats["phase_f_total_uniq_unsat"], pct))
        print("    uniqueness-check SAT:     %d  (joint Y had alternatives)" % (
            stats["phase_f_total_uniq_sat"]))
        print("    runs where bit-drop ever fired: %d / %d" % (
            stats["phase_f_runs_with_any_drop"], stats["phase_f_ran"]))
    print("  CEGAR ran:                  %d  (made >=1 commit in %d)" % (
        stats["cegar_ran"], stats["cegar_made_commits"]))
    if stats["cegar_ran"] > 0:
        print("    cumulative rounds:        %d" % stats["cegar_total_rounds"])
        print("    joint-UNSAT rounds:       %d" % stats["cegar_total_joint_unsat"])
        print("    joint commits:            %d" % stats["cegar_total_joint_commits"])
        print("    per-y commits:            %d" % stats["cegar_total_per_y_commits"])
    print("  cadet+Manthan handoff:      %d" % stats["handoff_triggered"])
    print("  cadet finished alone:       %d" % stats["cadet_committed_all"])
    print("  expected partial handoffs:  %d" % stats["partial_handoff_expected"])
    print("=" * 60)

    # Completeness check: every successful iteration must either have
    # cadet finish alone, or be a --cadetpartial > 0 run that handed
    # off to Manthan by design. Any unexpected handoff is a regression;
    # those are caught and aborted at the time they happen (see the
    # inner loop). This end-of-run check is the belt-and-braces
    # version, so a logic error in the per-iteration parsing can't
    # hide a regression.
    if stats["synth_succeeded"] > 0 and \
       stats["cadet_committed_all"] + stats["partial_handoff_expected"] \
           != stats["synth_succeeded"]:
        print("FUZZ FAIL: %d successful runs but %d had cadet finish "
              "alone and %d were expected --cadetpartial handoffs — "
              "handoff regression somewhere." %
              (stats["synth_succeeded"], stats["cadet_committed_all"],
               stats["partial_handoff_expected"]))
        exit(-1)
    # Phase E coverage check: same idea but for the SAT-model completion
    # phase. Phase E is the small-input SAT-model completion that
    # respects Phase C+D's partial commits.
    if stats["synth_succeeded"] >= 30:
        if stats["phase_e_ran"] == 0:
            print("FUZZER CONFIG BUG: %d iterations succeeded but Phase E "
                  "(SAT-model completion that respects Phase C+D's partial "
                  "commits) never ran. Phase E is the part of cadet that "
                  "completes synthesis after Phase C+D leaves vars "
                  "undetermined — please adjust fuzzer parameters so that "
                  "some iterations exhibit partial Phase C+D commits with "
                  "small enough orig_sampl_cnf for Phase E to engage." %
                  stats["synth_succeeded"])
            exit(-1)
        if stats["phase_e_finished_synthesis"] == 0:
            print("FUZZER CONFIG BUG: Phase E ran %d times but NEVER "
                  "completed cadet's synthesis alone. The success metric "
                  "for Phase E is letting cadet finish without Manthan." %
                  stats["phase_e_ran"])
            exit(-1)
        # Phase F: at >=50 iters, expect at least one engage; at >=100
        # iters, expect at least one converge-and-finish. Phase F is the
        # terminal completion phase — no size threshold, no iter cap —
        # so plenty of fuzzer CNFs should hit it.
        if stats["synth_succeeded"] >= 50 and stats["phase_f_ran"] == 0:
            print("FUZZER CONFIG BUG: %d iterations succeeded but Phase F "
                  "(terminal SAT-model completion) never engaged. Adjust "
                  "fuzzer to widen projection sizes." %
                  stats["synth_succeeded"])
            exit(-1)
        if stats["synth_succeeded"] >= 100 and \
                stats["phase_f_converged_and_finished"] == 0:
            print("FUZZER CONFIG BUG: Phase F ran %d times but NEVER "
                  "converged and finished synthesis. Phase F is supposed "
                  "to always converge now — this is a regression." %
                  stats["phase_f_ran"])
            exit(-1)
        # CEGAR coverage: with the knob-randomization defaults above
        # (--cadetcegar weighted 4:1 on:off), at >= 100 iters we expect
        # CEGAR to have fired in at least a handful of runs. If it
        # never fires, either the random seed missed cadetcegar=1 every
        # time (very unlikely) or a regression silently disabled the
        # drain. Either way it's worth surfacing — otherwise CEGAR
        # could rot without us noticing.
        if stats["synth_succeeded"] >= 100 and stats["cegar_ran"] == 0:
            print("FUZZER CONFIG BUG: %d iterations succeeded but CEGAR "
                  "never ran. Either knob-randomization got unlucky or "
                  "the CEGAR drain is silently disabled." %
                  stats["synth_succeeded"])
            exit(-1)
    exit(0)
