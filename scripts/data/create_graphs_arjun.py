#!/usr/bin/python3

import os
import sqlite3
import re
import subprocess


def convert_to_cactus(fname, fname2):
    # print("fname:" , fname)
    f2 = open(fname2, "w")
    f = open(fname, "r")
    text = f.read()
    mylines = text.splitlines()
    i = 0
    time = []
    for line in mylines:
      time.append(float(line.split()[0]))
      i += 1

    lastnum = -1
    for a in range(0, 3600, 1):
      num = 0
      for t in time:
        #print "t: %f a: %d" %(t, a)
        if (t < a) :
          num += 1

      if (lastnum != num):
          f2.write("%d \t%d\n" %(num, a))
      lastnum = num
    f.close()
    f2.close()
    return len(mylines)


def get_versions():
    vers = []
    con = sqlite3.connect("mydb.sqlite")
    cur = con.cursor()
    res = cur.execute("""
                      SELECT arjun_sha1
                      FROM data
                      where arjun_sha1 is not NULL and arjun_sha1 != '' group by arjun_sha1""")
    for a in res:
        vers.append(a[0])

    con.close()
    return vers


def get_dirs(ver : str):
    ret = []
    con = sqlite3.connect("mydb.sqlite")
    cur = con.cursor()
    res = cur.execute("SELECT dirname, timeout_call FROM data where arjun_sha1='"+ver+"' group by dirname")
    for a in res:
        call = a[1]
        call = re.sub("././arjun", "", call)
        call = re.sub(" mc2022.*cnf.*", "", call)
        ret.append([a[0], call])

    con.close()
    return ret


def gnuplot_name_cleanup(name: str) -> str:
    # remove all non-alphanumeric characters except for underscores and dashes
    name = re.sub(r'\"', '', name)
    # replace multiple underscores or dashes with a single one
    name = re.sub(r'_', '=', name)
    return name


def generate_todos():
    fname_like = ""
    # fname_like = " and (fname like '%track1%' or fname like '%track2%') "


    not_calls = []
    # not_calls = ["ExactMC"]
    # not_versions = ["sharpsat", "gpmc", "6368237b"]
    # only_calls = ["--ignore 1 --arjun 1 --maxcache 3500 --vivif 1 --decide 2 --sbva 1000"]
    # not_versions = ["arjun"]
    # not_calls = ["forcebranch", "target"] # "cachetime"
    # exactm: out-arjun-6318929.pbs101-5/
    # exactmc2: out-arjun-6328707.pbs101-7
    # sharpsat: out-arjun-6318929.pbs101-7

    only_dirs = [
        # "out-synth-984148" # bug in sibFPE for oracle, autarkies
        # "out-synth-984881-0/", # fix bug in sibFPE, autarkies
        # "out-synth-1017598-5/", # too many fixes to name
        "out-synth-1017598-1/", # too many fixes to name
        # "out-synth-1017598-", # too many fixes to name
        # "out-synth-1043577-", # no_silent, BVA, Kuldeep ideas, 3+4 strategy etc
        "out-synth-1043577-", #strategy 0, multiplier
        # "out-synth-1043577-13", strategy 1
        # "out-synth-1043577-14"  strategy 2,
        # "out-synth-1043577-15"  strategy 3,
        # "out-synth-1043577-16"  strategy 4,
        # "out-synth-1044613-", # bva synth off, on-the-fly order

    ]
    # only_dirs = ["out-synth-6828273"]
    # not_calls = ["--minimize 0 ", "--bve 0"]
    # not_calls = ["--satsolver 0"]
    not_versions = []
    # only_dirs = []
    # only_calls = ["--synth"]
    only_calls = []
    # not_calls = ["restart"]
    not_calls = []
    only_versions = get_versions()
    fname2_s = []
    table_todo = []


    for ver in only_versions :
        dirs_call = get_dirs(ver)
        for dir,call in dirs_call:
            bad = False
            for not_call in not_calls:
              if not_call in call:
                bad = True
            for not_version in not_versions:
              if not_version in ver:
                bad = True
            if len(only_calls) != 0:
              inside = False
              for only_call in only_calls:
                if only_call in call:
                  inside = True
              if not inside: bad = True

            if len(only_dirs) != 0:
              inside = False
              for only_dir in only_dirs:
                if only_dir in (dir+"/"):
                  inside = True
              if not inside: bad = True

            if bad:
              continue

            fname = "run-"+dir+".csv"
            with open("gencsv.sql", "w") as f:
                f.write(".headers off\n")
                f.write(".mode csv\n");
                f.write(".output "+fname+"\n")
                f.write("select arjun_time from data where dirname='"+dir+"' and arjun_sha1='"+ver+"'\n and arjun_time is not NULL "+fname_like)
            os.system("sqlite3 mydb.sqlite < gencsv.sql")
            os.unlink("gencsv.sql")

            fname2 = fname + ".gnuplotdata"
            num_solved = convert_to_cactus(fname, fname2)
            fname2_s.append([fname2, call, ver[:10], num_solved, dir])
            table_todo.append([dir, ver])

    return (fname2_s, table_todo, fname_like)


fname2_s, table_todo, fname_like = generate_todos()

# summary table
for only_counted in [False, True]:
  counted_req = ""
  if only_counted:
    print("::: --------- Data based on ONLY benchmarks that are FINISHED ------- :::")
    counted_req = " and arjun_time is not NULL "
  else:
    print("::: --------- Data based on ALSO NOT FINISHED benchmarks ------- :::")
  with open("gen_table.sql", "w") as f:
    f.write(".mode table\n")
    # f.write(".mode colum\n")
    # f.write(".headers off\n")
    dirs = ""
    vers = ""
    for dir,ver in table_todo:
      dirs += "'" + dir + "',"
      vers += "'" + ver + "',"
    dirs = dirs[:-1]
    vers = vers[:-1]
    extra = ""
    f.write("select \
        replace(dirname,'out-arjun-mc','') as dirname,\
        timeout_call as call,\
        sum(mem_out) as 'mem out', \
        sum(signal == 11) as 'sigSEGV', \
        sum(signal == 6) as 'sigABRT', \
        sum(signal == 14) as 'sigALRM', \
        sum(signal == 8) as 'sigFPE', \
        CAST(ROUND(avg(timeout_mem), 0) AS INTEGER) as 'av memKB',\
        sum(arjun_time is not null) as 'solved',\
        CAST(ROUND(sum(coalesce(arjun_time, 3600))/COUNT(*),0) AS INTEGER) as 'PAR2',\
        CAST(avg(input_vars) AS INTEGER) as 'av-inp',\
        CAST(avg(start_to_define_vars) AS INTEGER) as 'av-to-def',\
        CAST(avg(orig_total_vars) AS INTEGER) as 'av-vars',\
        CAST(ROUND(avg(puura_time), 2) AS REAL) as 'av-puura-T',\
        CAST(avg(puura_defined) AS INTEGER) as 'av-puura-def',\
        CAST(ROUND(avg(extend_time), 2) AS REAL) as 'av-extend-T',\
        CAST(avg(extend_defined) AS INTEGER) as 'av-extend-def',\
        CAST(ROUND(avg(backward_time), 2) AS REAL) as 'av-backw-T',\
        CAST(avg(backward_defined) AS INTEGER) as 'av-backw-def',\
        CAST(ROUND(avg(manthan_training_time), 2) AS REAL) as 'av-mant-tr-T',\
        CAST(ROUND(avg(manthan_repair_time), 2) AS REAL) as 'av-mant-rep-T',\
        CAST(ROUND(avg(manthan_time), 2) AS REAL) as 'av-manth-T',\
        CAST(ROUND(avg(repairs),0) AS INTEGER) as 'av-repairs',\
        CAST(avg(manthan_defined) AS INTEGER) as 'av-manthan-def',\
        sum(fname is not null) as 'nfiles'\
        from data where dirname IN ("+dirs+") and arjun_sha1 IN ("+vers+") "+fname_like+" "+counted_req+"group by dirname order by solved asc")
# CAST(ROUND(avg(manthan_sampling_time), 2) AS REAL) as 'avg-mant-samp-T',\
# CAST(avg(repairs_failed) AS INTEGER) as 'avg-repairs-fail',\
# CAST(avg(repairs) AS INTEGER) as 'avg-repairs',\
  command = "sqlite3 mydb.sqlite < gen_table.sql"
  p = subprocess.Popen(command, stderr=subprocess.STDOUT,stdout=subprocess.PIPE, shell=True)
  output, _ = p.communicate()
  for line in output.decode().splitlines():
      print(line)
  os.unlink("gen_table.sql")

# median table
if True:
  for dir,ver in table_todo:
    with open("gen_table.sql", "w") as f:
      f.write(".mode table\n")
      f.write("select '"+dir+"'")
      for col in "repairs", "timeout_mem":
        f.write(", (SELECT "+col+" as 'median_"+col+"'\
        FROM data\
        where dirname IN ('"+dir+"') and "+col+" is not null"+fname_like+"\
        ORDER BY "+col+"\
        LIMIT 1\
        OFFSET (SELECT COUNT("+col+") FROM data\
          where dirname IN ('"+dir+"') \
          and "+col+" is not null) / 2) as median_"+col+" \
      ")

      # median for data where the value is > 0, to avoid having the median be 0
      # for col in "gates_extended", "padoa_extended":
      #   f.write(", (SELECT "+col+" as 'median_"+col+"_NOZERO'\
      #   FROM data\
      #   where dirname IN ('"+dir+"') and arjun_sha1 IN ('"+ver+"') and "+col+" is not null "+fname_like+"\
      #               and "+col+">0\
      #   ORDER BY "+col+"\
      #   LIMIT 1\
      #   OFFSET (SELECT COUNT("+col+") FROM data\
      #     where dirname IN ('"+dir+"') and arjun_sha1 IN ('"+ver+"') \
      #     and "+col+" is not null "+fname_like+" and "+col+">0) / 2) as median_"+col+" \
      # ")
    os.system("sqlite3 mydb.sqlite < gen_table.sql")
    os.unlink("gen_table.sql")

gnuplotfn = "run-all.gnuplot"
with open(gnuplotfn, "w") as f:
    f.write("set term postscript eps color lw 1 \"Helvetica\" 12 size 8,4\n")
    f.write("set output \"run.eps\"\n")
    f.write("set title \"Counter arjun\"\n")
    f.write("set notitle\n")
    f.write("set key bottom right\n")
    # f.write("set xtics 200\n")
    f.write("set logscale x\n")
    f.write("unset logscale y\n")
    f.write("set ylabel  \"Instances synthetized\"\n")
    f.write("set xlabel \"Time (s)\"\n")
    # f.write("plot [:][10:]\\\n")
    f.write("plot [:][150:]\\\n")
    i = 0
    # f.write(" \"runkcbox-prearjun.csv.gnuplotdata\" u 2:1 with linespoints  title \"KCBox\",\\\n")
    # f.write(" \"runsharptd-prearjun.csv.gnuplotdata\" u 2:1 with linespoints  title \"SharptTD\",\\\n")
    towrite = ""
    for fn,call,ver,num_solved,dir in fname2_s:
        # if "restart" not in call and num_solved > 142:
        if True:
            call = gnuplot_name_cleanup(call)
            dir  = gnuplot_name_cleanup(dir)
            ver  = gnuplot_name_cleanup(ver)
            oneline = "\""+fn+"\" u 2:1 with linespoints  title \""+ver+"-"+dir+"-"+call+"\""
            towrite += oneline
            towrite +=",\\\n"
    towrite = towrite[:(len(towrite)-4)]
    f.write(towrite)


if os.path.exists("run.eps"):
  os.unlink("run.eps")
if os.path.exists("run.pdf"):
  os.unlink("run.pdf")
if os.path.exists("run.png"):
  os.unlink("run.png")

os.system("gnuplot "+gnuplotfn)
os.system("epstopdf run.eps run.pdf")
os.system("pdftoppm -r 250 -png run.pdf run") # -r controls DPI, default 150
print("okular run.eps")
os.system("okular run.eps")


#### examples
# .mode table
# old = out-arjun-mccomp2324-14675861-0 -- mccomp2025
# new= out-arjun-mccomp2324-15010600-0 -- td start from 0

# old = "out-arjun-mccomp2324-21349-0", # TRILLIUM, arjun_7d97636055e_9104724fa_26d64aac (i.e. old run that was the fastest)
# new = "out-arjun-mccomp2324-35541-0", # TRILLIUM, fixing td starting from 0, now cutting disjoint components at toplevel for correct centroid

# select a1.dirname, a1.fname, a1.arjun_time as "old time", a2.dirname, a2.arjun_time as "new time" from data as a1, data as a2 where  a1.fname=a2.fname and a1.arjun_time is not null and a1.arjun_time is not null and a1.dirname like 'out-arjun-mccomp2324-21349-0' and a2.dirname like 'out-arjun-mccomp2324-35541-0' and a1.arjun_time < a2.arjun_time-100 and a1.arjun_time > 10 order by a1.arjun_time desc limit 50;

