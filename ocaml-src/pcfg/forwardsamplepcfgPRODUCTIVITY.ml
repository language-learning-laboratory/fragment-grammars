open Sys
open Pcfg
open Unix


let loadGrammar startsymbol file =
  Globals.dbgMsg "top" 1 ("Loading Grammar: \n");
  let grammar = Pcfg.createGrammar 1000 10000 (Pcfg.N {Pcfg.nName=startsymbol})
  in let ch = open_in file
  in let _ = try
      while true; do
	let line = (input_line ch)
	in if not (Str.string_match  (Str.regexp "#") line 0) (* Ignore comment lines*)
	  then	let parts = Str.split (Str.regexp "[ \t]+")  line
	    in let lprob =  float_of_string (List.hd parts)
	    in let head = Pcfg.string2nt (List.hd (List.tl parts))
	    in let rhs = List.map (fun a ->
	      if Str.string_match  (Str.regexp "^_") a 0
	      then Pcfg.string2terminal (Str.string_after a 1)
	      else Pcfg.string2nonTerminal a) 
	      (List.tl (List.tl parts))
	    in Pcfg.createNewProduction grammar head rhs lprob
      done; 
    with End_of_file -> close_in ch;
  in grammar 


let inputgrammarfile = ref ""
and outputfile = ref ""
and debugfile = ref ""
and startsymbol = ref "START"
and numsamples = ref 1000
and seed = ref 1
in let options = [
    "-input-grammar", Arg.String (fun f -> inputgrammarfile := f), "The starting grammar or state file.";
    "-outfile", Arg.String (fun f -> outputfile := f), "Prefix for test sentence expectations file.";
    "-debug-file", Arg.String (fun f -> debugfile := f), "The debug file for this run";
    "-start-symbol", Arg.String (fun f -> startsymbol := f), "The start symbol.";
    "-num-samples", Arg.Int (fun f -> numsamples := f), "Number of sentences to sample";
    "-seed", Arg.Int (fun f -> seed := f), "Random seed"; 

  ] in let msg = "Sample sentences from provided PCFG grammar.\n" in 
  Arg.parse options (fun x -> ()) msg;
  let _ = Utils.makeAbsolutePathToFile !debugfile
  in let _ = Globals.setDebugFile !debugfile in
    Globals.dbgMsg "top" 1 ("Input grammar: " ^ ( !inputgrammarfile) ^ "\n");
    Globals.dbgMsg "top" 1 ("Output File Prefix: " ^ ( !outputfile) ^ "\n");
    Globals.dbgMsg "top" 1 ("Debug file: " ^ ( !debugfile) ^ "\n");
    Globals.dbgMsg "top" 1 ("Start Symbol: " ^ ( !startsymbol) ^ "\n");
    Globals.dbgMsg "top" 1 ("Random seed: " ^ (string_of_int !seed) ^ "\n");

    Random.init !seed;

    Gc.set { (Gc.get ()) with Gc.minor_heap_size = (Gc.get ()).Gc.minor_heap_size*100 }; (* increase the size of the minor heap *)
    Gc.set { (Gc.get ()) with Gc.major_heap_increment = (Gc.get ()).Gc.major_heap_increment*10 }; (* increase the size of the minor heap *) 
        
    let outputCh = open_out !outputfile 
    in let grammar = loadGrammar !startsymbol !inputgrammarfile
    in let forms =["able";"age";"al";"an";"ance";"ary";"ate";"dom";"ee";"eer";"en";"ence";"ent";"er";"ery";"ese";"ess";"ette";"ful";"hood";"ic";"ify";"ion";"ish";"ism";"ist";"itis";"ity";"ive";"ize";"less";"let";"like";"ling";"ly";"ment";"most";"ness";"ology";"or";"ory";"ous";"proof";"ry";"ship";"some";"ster";"th";"ty";"ward";"wise";"y";"esque"]
    (* in let _ = Pcfg.writeGrammar  (open_out "temp.txt") grammar*)		  
    in let _ = for i=1 to !numsamples do  
	let tree =  Pcfg.forwardSampleTree grammar (Pcfg.getStart grammar)
	in let yield = List.map (fun elem -> (Pcfg.symbol2string elem)) (Pcfg.getParseTreeYield tree)
	in if (List.length yield ) > 1 
	  then  let yieldArray= Array.of_list yield
		in let lastI = (Array.length yieldArray) - 1
		in if List.exists (fun elem -> elem = yieldArray.(lastI)) forms
		  then output_string outputCh  ((List.fold_left (fun a v -> a ^ " " ^ v) "" yield) ^ "\n") (* ((Pcfg.parseTree2string tree) ^ "\n")*)
		  else ()
	  else ()
      done
    in exit 0
       
