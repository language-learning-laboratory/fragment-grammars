# Command Line

bestpcfg \
    -corpus-counts <count-file> \
    -corpus-sentences <form-file> \
    -pya <Pitman-Yor-a-parameter>\
    -pyb <Pitman-Yor-b-parameter> \
    -sticky-concen <sticky-parameter>\
    -sticky-dist <sticky-distribution>\
    -pi <pi-parameter> \
    -sweeps <number-of-sweeps> \
    -debug-file <debug-file> \
    -output-grammar <output-grammar> \
    -seed 1 \
    -start-symbol <start-symbol>

For example:

bestpcfg \
    -corpus-counts irregularization-day1.counts.txt \
    -corpus-sentences irregularization-day1.forms.txt \
    -pya 0.0 \
    -pyb 1 \
    -sticky-concen 1 \
    -sticky-dist 0.5 \
    -pi 1 \
    -sweeps 100000 \
    -debug-file irregularization.FG-output-debug.txt \
    -output-grammar irregularization.FG-output \
    -seed 1 \
    -start-symbol START

# Form file (with trees)
One form per line, in this format (note the double parentheses around
the whole form):

((V in (V (BND crimin) ate)))
((N (N hog) an))
((N dis (N (BND junct) ion)))
((N (V gain) er))
((B (A (N venom) ous) ly))
((N (V extract) or))
((V (N eulogy) ize))
((V (BND sch) en))
((A (A paramount) ly))
((A (BND impud) ent))
((A (V destruct) ive))
((A (N (V dip) er) ful))
((V gather))

# Count file
Has the count of each input in the form file, one per line:

48
66
3
5
8
6
10
1
1
26
266
1
5

Note that forms on a single line in the form file will be parsed as if
they are one form, and all inference moves will be made at the type
level resampling analyses for all the tokens at once. If you want the
sampler to make smaller steps in posterior space, split each form type
across more lines.
