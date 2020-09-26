#!/bin/bash

if [[ ! $# -eq 5 && ! $# -eq 6 ]]
then
    echo "`basename $0` ncpus mem data startId endId [qsubOpt]" 
    echo "qsubOpt=0: use nlpsub, 1: PBS, 2: SGE, 3: display running command only"
    exit
fi

ncpus=$1
mem=$2
data=$3 # data="WSJ"
startId=$4
endId=$5
if [ $# -eq 6 ] 
then
  isQsub=$6
else
  isQsub=1 # PBS
fi

NLPSUB_CLUSTER_CONFIG="-c$ncpus -m$mem"; #"-c4 -m8gb"; #,nodes=1"
CLUSTER_CONFIG="-l ncpus=$ncpus,mem=$mem"; #"-l ncpus=4,mem=8gb"; #,nodes=1"
SGE_CLUSTER_CONFIG="-l mf=$mem -pe fah $ncpus";

ROOT=/afs/ir/users/l/m/lmthang #/home/lmthang
PROGRAM=$ROOT/fg/bin/bestpcfg
TESTNAME="fg"

# cp test data directory
echo "# PROGRAM=$PROGRAM"
echo "# PROGRAM_OPT=$PROGRAM_OPT"
dataDir="$ROOT/fg/data"
sweeps=50
for id in `awk -v M="$startId" -v N="$endId" 'BEGIN{for (i=M; i<=N; i++) print i}'` ; do
  outDir="$ROOT/fg/output/$data-$id"
  echo "# outDir $outDir"
  exec=$outDir/${TESTNAME}.sh 
  logFile=$outDir/${TESTNAME}.LOG  

  echo "# exec=$exec"
  rm -rf $exec

  # check file exists
  if [ -d $outDir ] 
  then
    echo "# Directory exists $outDir"
  else
    mkdir -p $outDir
  fi 


  cat > $exec <<EOF
#!/bin/bash

uname -a
echo "$PROGRAM -corpus-counts $dataDir/$data.counts.txt -corpus-sentences $dataDir/$data.forms.txt -pya 0.5 -pyb 100 -sticky-concen 1 -sticky-dist 0.5 -pi 1 -sweeps $sweeps -seed $id -debug-file $outDir/debug.txt -output-grammar $outDir/$data.FG-output-0 -start-symbol START" 

$PROGRAM -corpus-counts $dataDir/$data.counts.txt -corpus-sentences $dataDir/$data.forms.txt -pya 0.5 -pyb 100 -sticky-concen 1 -sticky-dist 0.5 -pi 1 -sweeps $sweeps -seed $id -debug-file $outDir/debug.txt -output-grammar $outDir/$data.FG-output-0 -start-symbol START
EOF

  echo "chmod +x $exec"
  chmod +x $exec
# don't use nlpsub as it doesn't support the same -d in qsub
#echo "/u/nlp/bin/nlpsub -qlong -ppreemptable $NLPSUB_CLUSTER_CONFIG -d$outDir -j -v $exec"
#/u/nlp/bin/nlpsub -qlong -ppreemptable $NLPSUB_CLUSTER_CONFIG -d$outDir -j -v $exec
  if [ $isQsub -eq 1 ] 
  then # PBS
    echo "qsub $CLUSTER_CONFIG -d /home/lmthang/scr/trainEmb/code -j oe -o $logFile -q verylong -W x=QOS:PREEMPTABLE $exec" 
    qsub $CLUSTER_CONFIG -j oe -o $logFile -q verylong -W x="QOS:PREEMPTABLE" $exec
  else 
    if [ $isQsub -eq 2 ] 
    then # SGE
      cd /afs/ir.stanford.edu/users/l/m/lmthang/fg
      echo "qsub $SGE_CLUSTER_CONFIG -cwd -j y -o $logFile $exec" # -q long.q  
      qsub $SGE_CLUSTER_CONFIG -cwd -j y -o $logFile $exec
    else
      if [ $isQsub -eq 3 ] 
      then # SGE
        echo "\n# Not run. Do it yourself:"
        tail -1 $exec
      fi
    fi
  fi
done
