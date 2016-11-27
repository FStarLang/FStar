
f(x) = m*x
fit f(x) 'stats.csv' using 2:1 via m

set term png size 1920,1080
set output "stats_nonorm_plot.png"
set title "Time versus RLimit"
set xlabel "Time in seconds"
set xtics 2.5
set ylabel "RLimit"
set ytics 10000000
set grid
set timestamp
plot 'stats.csv' using 2:1 with points, f(x)

quit
