#!/bin/sh

grammarFile=$1
outFile=$2

# Deescape
echo "~/surprisal/bin/deescape.sh $grammarFile $grammarFile.deescaped"
~/surprisal/bin/deescape.sh $grammarFile $grammarFile.deescaped

# Convert to format read by Earleyx
echo "~/surprisal/bin/convert-grammar-format.py -e $grammarFile.deescaped $grammarFile.rules s2p"
~/surprisal/bin/convert-grammar-format.py -e $grammarFile.deescaped $grammarFile.rules s2p

# Concat root and unknown rules
echo "cat ~/surprisal/grammars/WSJ/root.rules $grammarFile.rules ~/surprisal/grammars/WSJ/smooth.rules > $outFile"
cat ~/surprisal/grammars/WSJ/root.rules $grammarFile.rules ~/surprisal/grammars/WSJ/smooth.rules > $outFile

# rm intermediate files
echo "rm -rf $grammarFile.deescaped $grammarFile.rules"
rm -rf $grammarFile.deescaped $grammarFile.rules
