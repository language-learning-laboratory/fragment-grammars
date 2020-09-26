nohup /Users/timo/Projects/fragment-grammar/bin/runpcfg -input-grammar grammars/FG.txt -test-sentences test-sets/training-words.txt -outfile results/training-words-FG-results.txt  -debug-file debug/training-words-FG-debug.txt -start-symbol START &

nohup /Users/timo/Projects/fragment-grammar/bin/runpcfg -input-grammar grammars/AG.txt -test-sentences test-sets/training-words.txt -outfile results/training-words-AG-results.txt  -debug-file debug/training-words-AG-debug.txt -start-symbol START &

nohup /Users/timo/Projects/fragment-grammar/bin/runpcfg -input-grammar grammars/MDPCFG.txt -test-sentences test-sets/training-words.txt -outfile results/training-words-MDPCFG-results.txt  -debug-file debug/training-words-MDPCFG-debug.txt -start-symbol START &