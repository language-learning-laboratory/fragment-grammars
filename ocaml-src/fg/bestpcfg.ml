open Sys
open Sexp
open FGStats
open FragmentGrammar
open FragmentGrammarIO
open LoadCorpus
open Sampler
open Unix
open MHSampler
open Unix

module Stats = FGStats
module FG = FragmentGrammar
module IO = FragmentGrammarIO
module MH = MHSampler
module Parser = MH.FGParser


let best20 = ref (Array.make 20 { FG.grammarScore=neg_infinity;
				 FG.pcfgProductions=[];})

(* let bestgrammar = ref { FG.grammarScore=neg_infinity;
			FG.pcfgProductions=[];} *)

let insert_solution grammar =
  let score = (FG.scoreGrammar grammar) 
  in let inserted = ref false
  in let result = Array.mapi 
    (fun i v -> if !inserted
      then !best20.(i - 1)
      else match compare score v.FG.grammarScore with
	  1 -> begin                            (* new score is higher*)
	      inserted := true;                 (* shift *)
	      FG.getpcfgRepresentation grammar;
	    end              
	| -1 -> v                               (* new score is lower *)
	| 0 ->                                  (* scores are equal *) 
	    let newPcfgRep = FG.getpcfgRepresentation grammar
	    in if newPcfgRep = v                (* grammars are identical, just pass through the current one *)
	      then v
	      else begin                  
		  inserted := true;             (* shift *)
		  newPcfgRep;
		end  
	| _ -> failwith "Unknown comparison"
    ) !best20 
  in best20 := result

let improvementfreq = 5
let lastimprovement = ref 1
let outputgrammarfile = ref ""

let readCountFile file =
  let lines = ref [] 
  in let ch = open_in file
  in try
      while true; do
	lines := (float_of_string (input_line ch)) :: !lines
      done; []
    with End_of_file ->
      close_in ch;
      List.rev !lines

let printBestGrammars () =
  Array.iteri (fun i v ->
    let outch = open_out (!outputgrammarfile ^ "." ^ "rank-" ^ (string_of_int (i+1)) ^ ".txt")
    in let _ = output_string outch (FG.pcfgRepresentation2string v)
    in let _ = flush outch
    in close_out outch) !best20

(* The callback to produce sampler output *)
let betweenSweepUpdate gInfo grammar analyses time sweep = 
  (*let _ = Globals.dbgMsg "top" 1  ("Sweep: " ^ (string_of_int sweep) ^ "\n")
  in let _ = Globals.dbgMsg "top" 1  ("\tlastimprovement: " ^ (string_of_int !lastimprovement) ^ "\n")
  in let _ = Globals.dbgMsg "top" 1  ("\timprovementfreq: " ^ (string_of_int improvementfreq) ^ "\n")
  in*) (*let score = (FG.scoreGrammar grammar) 
  in *)
  begin
    (insert_solution grammar);
    
    (* (if score > !bestgrammar.FG.grammarScore
       then let newbest = FG.getpcfgRepresentation grammar
       in bestgrammar := newbest); *)
    
    (if !lastimprovement == improvementfreq
      then begin
	  Globals.dbgMsg "top" 1  ("Printing new grammar at sweep: "^ (string_of_int sweep) ^ "!\n");
	  printBestGrammars ();
	  lastimprovement := 1;
	end
      else begin lastimprovement := !lastimprovement + 1 end);
    
    (gInfo, 0.0);	  
  end
	
let corpussentencefile = ref "" 
and corpuscountfile = ref ""
and debugfile = ref ""
and a = ref 0.0
and b = ref 0.0
and stickyConcen = ref 0.0
and stickyDist = ref 0.0
and pi = ref 1.0  
and seed = ref 1
and sweeps = ref 500
and startsymbol = ref "S"
in let options = [
    "-pya", Arg.Float (fun f -> a := f), "The pitman-yor a parameter.";
    "-pyb", Arg.Float (fun f -> b := f), "The pitman-yor b parameter.";
    "-sticky-concen", Arg.Float (fun f -> stickyConcen := f), "Concentration parameter for slippery/sticky prior.";
    "-sticky-dist", Arg.Float (fun f -> stickyDist := f), "Distribution parameter for slippery sticky prior.";
    "-pi", Arg.Float (fun f -> pi := f), "The base rule pseudo count.";
    "-corpus-sentences", Arg.String (fun f -> corpussentencefile := f), "Input corpus sentences.";
    "-corpus-counts", Arg.String (fun f -> corpuscountfile := f), "Input corpus counts.";
    "-output-grammar", Arg.String (fun f -> outputgrammarfile := f), "Output grammar to write.";
    "-debug-file", Arg.String (fun f -> debugfile := f), "The debug file for this run";
    "-sweeps", Arg.Int (fun f -> sweeps := f), "Number of sweeps";
    "-seed", Arg.Int (fun f -> seed := f), "Random seed"; 
    "-start-symbol", Arg.String (fun f -> startsymbol := f), "The start symbol.";
  ] in let msg = "Run the fragment grammar sampler.\n" in 
  Arg.parse options (fun x -> ()) msg;
  let _ = Utils.makeAbsolutePathToFile !debugfile
  in let _ = Globals.setDebugFile !debugfile in
    Globals.dbgMsg "top" 1 ("a parameter: " ^ (string_of_float !a) ^ "\n");
    Globals.dbgMsg "top" 1 ("b parameter: " ^ (string_of_float !b)^ "\n");
    Globals.dbgMsg "top" 1 ("Sticky concentration parameter: " ^ (string_of_float !stickyConcen) ^ "\n");
    Globals.dbgMsg "top" 1 ("Sticky distribution parameter: " ^ (string_of_float !stickyDist) ^ "\n");
    Globals.dbgMsg "top" 1 ("Pi parameter: " ^ (string_of_float !pi) ^ "\n");
    Globals.dbgMsg "top" 1 ("Random seed: " ^ (string_of_int !seed) ^ "\n");
    Globals.dbgMsg "top" 1 ("Number of sweeps: " ^ (string_of_int !sweeps) ^ "\n");
    Globals.dbgMsg "top" 1 ("Corpus sentence file: " ^ ( !corpussentencefile) ^ "\n");  
    Globals.dbgMsg "top" 1 ("Corpus count file: " ^ ( !corpuscountfile) ^ "\n");  
    Globals.dbgMsg "top" 1 ("Output grammar file: " ^ ( !outputgrammarfile) ^ "\n");  
    Globals.dbgMsg "top" 1 ("Debug file: " ^ ( !debugfile) ^ "\n");  
    Globals.dbgMsg "top" 1 ("Start Symbol: " ^ ( !startsymbol) ^ "\n");

    Random.init !seed;

    Gc.set { (Gc.get ()) with Gc.minor_heap_size = (Gc.get ()).Gc.minor_heap_size*100 }; (* increase the size of the minor heap *)
    Gc.set { (Gc.get ()) with Gc.major_heap_increment = (Gc.get ()).Gc.major_heap_increment*10 }; (* increase the size of the minor heap *)
    
    let _ = Utils.makeAbsolutePathToFile !corpussentencefile
    in let _ =  Globals.dbgMsg "top" 1 ("Thang\n")(* Thang *)
    in let _ = Utils.makeAbsolutePathToFile !corpuscountfile
    in let _ = Utils.makeAbsolutePathToFile !outputgrammarfile
    in let _ = Utils.makeAbsolutePathToFile !debugfile 
    in let stickyTheta = !stickyDist *. !stickyConcen 
    in let slipperyTheta = (1.0 -. !stickyDist) *. !stickyConcen 
    in let _ =  Globals.dbgMsg "top" 1 ("Sticky Theta: " ^ (string_of_float stickyTheta) ^ "\n")
    in let _ =  Globals.dbgMsg "top" 1 ("Slippery Theta: " ^ (string_of_float slipperyTheta) ^ "\n")
    in let grammar =  FG.createGrammar 1000 10000 (FG.N {FG.nName=(!startsymbol)})  (FG.createParams ~a:(!a) ~b:(!b) ~slip:slipperyTheta ~stick:stickyTheta ~pi:(!pi) ());
    in let _ = Globals.dbgMsg "top" 1 ("Loading Sentences.\n")
    in let sentencetrees = (iterSexpFile !corpussentencefile (fun t -> Some (LoadCorpus.sexp2parseTree (Some (FG.getStart grammar)) t)))
    in let counts = if !corpuscountfile <> ""
      then begin Globals.dbgMsg "top" 1 ("Reading Count File.\n"); (readCountFile !corpuscountfile);end
      else Utils.makeList (List.length sentencetrees) 1.0
    in let zipped = (List.fold_left2 (fun a v1 v2 -> ((v1, v2) :: a)) [] sentencetrees counts)
    (* in let _ = Globals.dbgMsg "top" 1 ("Randomizing Sentence Order.\n")*)
    in let (sentencetreesRandomized, counts) = (sentencetrees, counts) (* List.fold_left (fun a v -> ((fst v)::(fst a), (snd v)::(snd a))) ([],[]) (Utils.shuffle_list zipped) *)
    in let sentences =   (List.map 
			     (fun v -> match v with 
				 None -> failwith "Run-fg: Cannot get a sentence from an empty parse tree in corpus style load!"
			       | Some x -> (Array.of_list (FG.getParseTreeYield x))) 
			     sentencetreesRandomized) 
    in let _ = Globals.dbgMsg "top" 1 ("Loading Baserules.\n")
    in let _ = (iterSexpFile !corpussentencefile (LoadCorpus.loadSentenceBaseRules grammar !a !b !pi slipperyTheta stickyTheta))
    in let _ = Globals.dbgMsg "top" 1 ("Initializing Analyses.\n")
    in let analyses = MH.initializeAnalysesRandom grammar sentences sentencetreesRandomized counts;
    in let _ = Globals.dbgMsg "top" 1 ("Beginning Sampling.\n")
    in let _ = Sampler.doNmh true (*<-seeded*) false (*<-slice*) betweenSweepUpdate (fun a b c d e f g h -> a) () grammar analyses counts !sweeps
    in printBestGrammars ()
      
      
      
