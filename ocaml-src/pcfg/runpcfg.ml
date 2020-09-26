open Sexp
open Pcfg
open Str
open Cyk

(* Implement a filter on productions *)
let filter (grammar : Pcfg.grammar) (production : Pcfg.production ref) (threshold : float) = 
    ((Pcfg.prodLogprob production) >= threshold)

module CYK =
struct
  type grammar = Pcfg.grammar 
  type state  = int64          
  type constituentSymbol = Pcfg.symbol
  type parseTree = Pcfg.parseTree
  type stateExpectations = Pcfg.stateExpectations
  type constExpectations = Pcfg.constExpectations

  let parseTree2string = Pcfg.parseTree2string
  let tree2spans = Pcfg.tree2spans
  let getRootState = Pcfg.getRootTrie
  let stateConstituentProb = Pcfg.stateConstituentProb
  let stateConstituent = Pcfg.stateConstituent

  let getStateConstituents = (Pcfg.getStateConstituents filter)
  let nextState = Pcfg.stepTrie
  let constituentSymbol2string = Pcfg.symbol2string
  let state2string =  Pcfg.trieId2string_small

  let rootState = Pcfg.isStartTrie
  let getStartSymbol = Pcfg.getStart

  let getTerminals=Pcfg.getTerminals
  let isTerminal=Pcfg.isTerminal
  let getSymbols=Pcfg.getSymbols
  let getNonterminals=Pcfg.getNonterminals
  let matchConstituentSymbol=Pcfg.matchSymbol

  (* expectations *)
  let getROOTStateExpectations = Pcfg.getROOTStateExpectations
  let updateStateExpectations = Pcfg.updateStateExpectations
  let getEmptyConstituentExpectations = Pcfg.getEmptyConstituentExpectations
  let updateConstExpectations = Pcfg.updateConstExpectations

  (* FIXME: probably replace this *)
  let constituentMatches = Pcfg.constituentMatches

end
module Parser = CYKParser(CYK)
module T = SexpTree

let grammar_file = ref ""

let sexp2parseTree startsymbol (t : T.tree) = 
  match startsymbol with 
      Some ss -> 
	let rtFn r ch = Pcfg.Nd (ss, ch)
	and ndFn n ch = Pcfg.Nd ((Pcfg.N {Pcfg.nName=n}), ch)
	and lfFn lf  = Pcfg.Lf (Pcfg.T {Pcfg.tName= lf})
	in  (T.foldTree rtFn ndFn lfFn t)
    | None ->
	let rtFn r ch = List.hd ch
	and ndFn n ch = Pcfg.Nd ((Pcfg.N {Pcfg.nName=n}), ch)
	and lfFn lf  = Pcfg.Lf (Pcfg.T {Pcfg.tName= lf})
	in (T.foldTree rtFn ndFn lfFn t)

let makeOutputHeader () =
  "Sentence,ConditionedTree,MAPTree,InsideScore,MAPScore,MAPInsideRatio,Entropy,Surprisal,KL,NumParses,ExpectedNumConstituents,ExpectedBoundaries\n"

let scoreTests grammar testSentences testSentenceTrees outputCh =
  Globals.dbgMsg "top" 1 ("Scoring tests.\n");
  List.iter2 (fun sentence conditionedTree ->
    (*let _ = Globals.dbgMsg "top" 1 ("Scoring test: " ^ 
				       (Utils.sentence2string Pcfg.symbol2string sentence) ^ 
				       " with parse: " ^ 
				       (match conditionedTree with 
					   Some x -> (Pcfg.parseTree2string x)
					 | None -> "") ^ 
				       "\n")
    in *) let parseResult = (Parser.parse grammar conditionedTree neg_infinity sentence)
    in match parseResult with
	Parser.Success chart -> 
	  let insideScore = (Parser.scoreSentenceFromChart grammar sentence chart)
	  in let mapParseTree = (Parser.getMAPParseFromChart grammar sentence chart)
	  in let mapScore = (Parser.getMAPScoreFromChart grammar sentence chart)
	  in let expectations = (Parser.getExpectationsFromChart grammar chart)
	  (* in let _ = if insideScore = mapScore
	    then Globals.dbgMsg "top" 1 ("Inside and mapscore are identical: " ^ (Printf.sprintf "%.10f" insideScore) ^" "^ (Printf.sprintf "%.10f" mapScore) ^"\n")
	    else Globals.dbgMsg "top" 1 ("Inside and mapscore are different (map/inside): " ^ (Printf.sprintf "%.10f" (exp (mapScore -. insideScore)))  ^"\n")*)
	  in begin 
	    (* Globals.dbgMsg "top" 10 ( "Chart:\n" ^ (Parser.chart2string grammar chart) ^ "\n");*)
	      output_string outputCh (("\""^ (Utils.sentence2string (fun s -> Pcfg.symbol2string s) sentence)) ^ "\",\"" ^
					 (match conditionedTree with None -> "" | Some t -> (CYK.parseTree2string t)) ^ "\",\"" ^
					 (Parser.parseTree2String mapParseTree)  ^ "\"," ^
					 (string_of_float insideScore)  ^ "," ^
					 (string_of_float mapScore)  ^ "," ^
					 (string_of_float (exp (mapScore -. insideScore)))  ^ "," ^
					 (string_of_float (exp expectations.Pcfg.cEntropy)) ^ "," ^
					 (string_of_float (exp expectations.Pcfg.cSurprisal)) ^ "," ^
					 (string_of_float (exp expectations.Pcfg.cKL)) ^ "," ^
					 (string_of_float (exp expectations.Pcfg.cNumParses)) ^ "," ^
					 (string_of_float (exp expectations.Pcfg.cNumConstituents)) ^ "," ^
					 (Array.fold_left (fun acc value -> acc ^ (if acc = "" then "" else ";") ^ (string_of_float (exp value))) "" expectations.Pcfg.cBoundaries) ^ "\n");
	      flush outputCh;
	    end
      | Parser.Failure chart ->
	  begin
	    (* Globals.dbgMsg "top" 10 ( "Chart:\n" ^ (Parser.chart2string grammar chart) ^ "\n");*)
	    Globals.dbgMsg "top" 10  ("Grammar:\n\t" ^ !grammar_file ^ " does not parse sentence:\n\t"^  (Array.fold_left (fun  a v -> a ^ " " ^ (Pcfg.symbol2string v)  ) "" sentence) ^ 
					 "\n\t" ^ 
					 (match conditionedTree with 
					     Some x -> (Pcfg.parseTree2string x)
					   | None -> "") ^ 
					 "\n\tfrom start symbol: " ^ (Pcfg.symbol2string (Pcfg.getStart grammar)));
	  end)
    testSentences testSentenceTrees

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
and testsentencefile  = ref ""
and outputfile = ref ""
and seeded = ref false
and debugfile = ref ""
and startsymbol = ref "START"
in let options = [
    "-input-grammar", Arg.String (fun f -> inputgrammarfile := f), "The starting grammar or state file.";
    "-test-sentences", Arg.String (fun f -> testsentencefile := f), "File of test sentences to score.";
    "-outfile", Arg.String (fun f -> outputfile := f), "Prefix for test sentence expectations file.";
    "-seeded", Arg.Set seeded, "Seed the parse chart with analyses?";
    "-debug-file", Arg.String (fun f -> debugfile := f), "The debug file for this run";
    "-start-symbol", Arg.String (fun f -> startsymbol := f), "The start symbol.";
  ] in let msg = "Parse test sentences with provided PCFG grammar.\n" in 
  Arg.parse options (fun x -> ()) msg;
  let _ = Utils.makeAbsolutePathToFile !debugfile
  in let _ = Globals.setDebugFile !debugfile in
    Globals.dbgMsg "top" 1 ("Input grammar: " ^ ( !inputgrammarfile) ^ "\n");
    Globals.dbgMsg "top" 1 ("Test Sentence File: " ^ ( !testsentencefile) ^ "\n");
    Globals.dbgMsg "top" 1 ("Output File Prefix: " ^ ( !outputfile) ^ "\n");
    Globals.dbgMsg "top" 1 ("Seeded?: " ^ (string_of_bool !seeded) ^ "\n");
    Globals.dbgMsg "top" 1 ("Debug file: " ^ ( !debugfile) ^ "\n");
    Globals.dbgMsg "top" 1 ("Start Symbol: " ^ ( !startsymbol) ^ "\n");

    Gc.set { (Gc.get ()) with Gc.minor_heap_size = (Gc.get ()).Gc.minor_heap_size*100 }; (* increase the size of the minor heap *)
    Gc.set { (Gc.get ()) with Gc.major_heap_increment = (Gc.get ()).Gc.major_heap_increment*10 }; (* increase the size of the minor heap *) 
    
    grammar_file := !inputgrammarfile;
    
    let (testSentences, testSentenceTrees) = 
      begin
	Globals.dbgMsg "top" 1 ("Loading Test Sentences.\n");
	(if !seeded
	  then 
	    begin
	      Globals.dbgMsg "top" 1 ("Seeded Test Sentences.\n"); 
	      (let testTrees = iterSexpFile !testsentencefile (fun t -> Some (sexp2parseTree (Some (Pcfg.N {Pcfg.nName=(!startsymbol)})) t))
		in let sentences = (List.map (fun v -> match v with 
		    None -> failwith "runpcfg: cannot get a sentence from an empty parse tree with seeded tests!"
		  | Some x -> (Array.of_list (Pcfg.getParseTreeYield x))) 
					 testTrees)
		   in (sentences, testTrees));
	    end
	 else let sentences = (Utils.readSentences Pcfg.string2terminal !testsentencefile)
	      in (sentences, (Utils.makeList (List.length sentences) None)));
      end
    in let outputCh = open_out !outputfile 
    in let _ = output_string outputCh (makeOutputHeader ())
    in let grammar = loadGrammar !startsymbol !inputgrammarfile
	    (* in let _ = Pcfg.writeGrammar  (open_out "temp.txt") grammar*)
		in let _ = scoreTests grammar testSentences testSentenceTrees  outputCh
		   in exit 0
		   
      
