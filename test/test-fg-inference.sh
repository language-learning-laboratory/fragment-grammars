rootDir=/Users/timo/research-projects/fragment-grammars/

data=WSJ1
outDir=/Users/timo/Projects/fg-source-code/test/test-out

nohup $rootDir/bin/bestpcfg -corpus-counts $rootDir/data/$data.counts.txt -corpus-sentences $rootDir/data/$data.forms.txt -pya 0.5 -pyb 100 -sticky-concen 1 -sticky-dist 0.5 -pi 1 -sweeps 1000 -debug-file $data.FG-output-debug-0.txt -output-grammar $outDir/$data.FG-output-0 -seed 0 -start-symbol START &
