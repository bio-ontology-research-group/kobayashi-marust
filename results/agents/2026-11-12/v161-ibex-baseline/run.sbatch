#!/bin/bash
#SBATCH --job-name=km-v161-diag
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --array=1-214%60
#SBATCH --cpus-per-task=1
#SBATCH --mem=96G
#SBATCH --time=00:20:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v161-diag-20261112/logs/%A_%a.out
set -u
R=/ibex/scratch/projects/c2014/hohndor/km/v161-diag-20261112
KM=/ibex/scratch/projects/c2014/hohndor/km/v160-measure-20261111/binaries/km-v1.6.0-rc-pgo-d1a99d67d0728d7db7f12af34c7f939850fd73e68a827284d7e843129a9cf94a
CORPUS=/ibex/scratch/hohndor/km/v143-harness-20260918/corpus/pool_sample/files
n=$(sed -n "${SLURM_ARRAY_TASK_ID}p" $R/names.txt)
case $n in *.ofn) f=$R/$n ;; *) f=$CORPUS/$n ;; esac
O=$R/runs/${n%.*}; mkdir -p $O; cd $O
export TMPDIR=$O/tmp; mkdir -p $TMPDIR
cat > wrap.sh <<W
#!/bin/bash
/usr/bin/time -v -o $O/time.txt $R/km-el-reference "\$@" > $O/ref-stdout.json 2> $O/ref-stderr.txt
rc=\$?; echo \$rc > $O/ref-rc.txt; cat $O/ref-stdout.json; exit \$rc
W
chmod +x wrap.sh
s=$(date +%s.%N)
KM_THREADS=1 KM_TIMING=1 KM_REFERENCE_FORCE=1 KM_EL_REFERENCE_CHECKER=$O/wrap.sh timeout 330 $KM classify $f > km-out.txt 2> km-stderr.txt
kmrc=$?
e=$(date +%s.%N)
rss=$(grep "Maximum resident" time.txt 2>/dev/null | awk '{print $NF}')
rw=$(grep "Elapsed (wall" time.txt 2>/dev/null | awk '{print $NF}')
ref=$(grep -h "KM_REFERENCE_STAGE" km-stderr.txt | head -1 | cut -c1-200 | tr '\t' ' ')
err=$(head -c 300 ref-stderr.txt 2>/dev/null | tr '\n\t' '  ')
outsz=$(stat -c %s ref-stdout.json 2>/dev/null)
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$n" "$kmrc" "$(echo "$e - $s" | bc)" "$(cat ref-rc.txt 2>/dev/null)" "$rw" "$rss" "$outsz" "$ref" "$err" "$(hostname)" > $O/row.tsv
rm -f ref-stdout.json km-out.txt; rm -rf $TMPDIR
