xzgrep -i "terminated" *.timeout_pre.xz |  sed -e "s/.gz[^ ]*//" | awk '{print $1 " " $5}' > signals_pre.csv
ls -- *.out_pre.xz > allFiles_xz_pre.csv
ls -- *.out_pre.xz | sed "s/.gz.*/.gz/" > allFiles_pre.csv
xzgrep "Time to compute the bi-partition" *.out_pre.xz |  awk '!x[$1]++' | sed -e "s/.gz[^ ]*//" | awk '{print $7 " " $1}' > solveTimes_pre.csv
awk '{print $2}' solveTimes_pre.csv > solved_pre.csv
grep -v -f solved_pre.csv allFiles_pre.csv | sed "s/.gz.*/.gz/" > unsolved_pre.csv
cat unsolved_pre.csv | awk '{print "5000.00 " $1}' >> solveTimes_pre.csv
awk '{print $2 " " $1}' solveTimes_pre.csv | sort > solveTimes_rev_pre.csv
awk '{if ($1=="5000.00") {x+=10000} else {x += $1};} END {printf "%d\n", x}' solveTimes_pre.csv > PAR2score_pre
