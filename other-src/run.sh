#!/bin/sh

#data="derivational.num-105000" 
data="WSJ" 
sweeps="20"
#outDir=$1
rootDir="/mnt/glusterfs/lmthang/fg-source-code"
outDir="$rootDir/output/${data}1"
mkdir $outDir
#data="WSJ.500" 
#data="WSJ.noRecursive"
echo "# Data $data"

echo "$rootDir/bin/bestpcfg -corpus-counts $rootDir/data/$data.counts.txt -corpus-sentences $rootDir/data/$data.forms.txt -pya 0.5 -pyb 100 -sticky-concen 1 -sticky-dist 0.5 -pi 1 -sweeps $sweeps -debug-file $data.FG-output-debug-0.txt -output-grammar $outDir/$data.FG-output-0 -seed 0 -start-symbol START"
$rootDir/bin/bestpcfg -corpus-counts $rootDir/data/$data.counts.txt -corpus-sentences $rootDir/data/$data.forms.txt -pya 0.5 -pyb 100 -sticky-concen 1 -sticky-dist 0.5 -pi 1 -sweeps $sweeps -debug-file $data.FG-output-debug-0.txt -output-grammar $outDir/$data.FG-output-0 -seed 0 -start-symbol START

