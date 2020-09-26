(***********************************************************************************
 ***********************************************************************************
 *                              Module: MHSampler                                    * 
 * --------------------------------------------------------------------------------*
 *            This module implements a partial fragment grammar (PFG)              * 
 ***********************************************************************************)  
open FragmentGrammar
open Cyk
open Utils
(* open HyperParameterSampler*)

module FG = FragmentGrammar
(* module HPS = HyperParameterSampler*)

(* Implement a filter on productions *)
let filter (grammar : FG.grammar) (production : FG.production) (threshold : float) = 
  begin
   (*  if (threshold > neg_infinity) & not(((FG.prodLogprob production) >= threshold))
    then Globals.dbgMsg "mh" 10 ( "removing production: " ^ (Int64.to_string production.FG.pid) ^ " " ^
				    (string_of_float (FG.prodLogprob production)) ^ 
				    " threshold "^ (string_of_float threshold) ^"\n");*)
    
(* Globals.dbgMsg "mh" 10 ( "Production Prob: " ^ (string_of_float (FG.prodLogprob production)) ^ 
				    " threshold "^ (string_of_float threshold) ^ 
				    " result: " ^ (string_of_bool  ((FG.prodLogprob production) >= threshold))^"\n")*)
    ((FG.prodLogprob production) >= threshold);
  end 

module FGCYK =
struct
  type grammar = FG.grammar 
  type state  = int64          
  type constituentSymbol = FG.symbol
  type parseTree = FG.parseTree
  type stateExpectations = FG.stateExpectations
  type constExpectations = FG.constExpectations

  let parseTree2string = FG.parseTree2string
  let tree2spans = FG.tree2spans
  let getRootState = FG.getRootTrie
  let stateConstituentProb = FG.stateConstituentProb
  let stateConstituent = FG.stateConstituent

  let getStateConstituents = (FG.getStateConstituents filter)
  let nextState = FG.stepTrie
  let constituentSymbol2string = FG.symbol2string
  let state2string =  FG.trieId2string_small

  let rootState = FG.isStartTrie
  (* let terminalConstituentSymbol = FG.isTerminal *)
  (* let production2state = FG.prod2trie
  let getTerminalProduction = FG.terminalProduction *)
  let getStartSymbol = FG.getStart

  let getTerminals=FG.getTerminals
  let isTerminal=FG.isTerminal
  let getSymbols=FG.getSymbols
  let getNonterminals=FG.getNonterminals
  let matchConstituentSymbol=FG.matchSymbol

  (* expectations *)
  let getROOTStateExpectations = FG.getROOTStateExpectations
  let updateStateExpectations = FG.updateStateExpectations
  let getEmptyConstituentExpectations = FG.getEmptyConstituentExpectations
  let updateConstExpectations = FG.updateConstExpectations

  (* FIXME: probably replace this *)
  let constituentMatches = FG.constituentMatches

end

(* module FGParser = EarleyParser(FG) *)
module FGParser = CYKParser(FGCYK)

module FGPT = FGParser.ParseTree

(* This function takes a parsetree and returns a fragment grammar analysis. Note that
   this creates the analysis in full, including updating the counts in the grammar. *)
let parse2analysis (grammar : FG.grammar ) (pTree : FGPT.tree) =
   (* let _ = Globals.dbgMsg "mh" 9 ("Converting parse to analysis: " ^ (FGPT.tree2string pTree) ^ "\n") in *)
  (*decide if a child node in the parse tree is a variable that needs to be sampled or not *)
  let rec getPtrees (cl : FG.analysis list) = match cl with
      [] -> []
    | FG.Terminal (term, pt)::tl -> pt :: (getPtrees tl)
    | FG.Constituent (t,l, pt)::tl -> pt :: (getPtrees tl)
  in let getChildVariableMask c = match c with
      FGPT.Rt ((s,c), ch) -> false
    | FGPT.Lf (c) -> true
    | FGPT.Nd ((s,c), l) -> (FG.isStartTrie grammar s)
 in let rec processNode (n : FGPT.tree) =   match n with
      FGPT.Rt (r, ch) -> processNode ch 
    | FGPT.Lf (c) -> FG.Terminal (c, (FG.Lf c))
    | FGPT.Nd ((s,c), l) -> match (FG.sampleStateConstituent grammar s c) with
	  (*FG.Root r -> FG.Terminal (c, (FG.Lf c))
	| *) FG.Tbl tbl -> 
	    let children =  (List.map (fun v -> processNode v) l) 
	    in (FG.expandTable grammar tbl children)
	| FG.Br br -> 
	    let children =  (List.map (fun v -> processNode v) l)  
	    in let mask = (List.map getChildVariableMask l) 
	    in let tbl = (FG.createDanglingTable !br children (FG.sampleStickyDecisions !br !br.FG.rhs !br.FG.stickyCnts mask) )
	    in FG.Constituent (ref tbl, children, (FG.Nd ( (FG.N (FG.tableHead (ref tbl))), (getPtrees children))))
  in (processNode pTree)


(* This function takes a parsetree and the MAP corresponding fragment grammar analysis. Note that
   this creates the analysis in full, including updating the counts in the grammar. *)
let parse2MAPanalysis (grammar : FG.grammar ) (pTree : FGPT.tree) =
   (* let _ = Globals.dbgMsg "mh" 9 ("Converting parse to analysis: " ^ (FGPT.tree2string pTree) ^ "\n") in *)
  (*decide if a child node in the parse tree is a variable that needs to be sampled or not *)
  let rec getPtrees (cl : FG.analysis list) = match cl with
      [] -> []
    | FG.Terminal (term, pt)::tl -> pt :: (getPtrees tl)
    | FG.Constituent (t,l, pt)::tl -> pt :: (getPtrees tl)
  in let getChildVariableMask c = match c with
      FGPT.Rt ((s,c), ch) -> false
    | FGPT.Lf (c) -> true
    | FGPT.Nd ((s,c), l) -> (FG.isStartTrie grammar s)
 in let rec processNode (n : FGPT.tree) =   match n with
      FGPT.Rt (r, ch) -> processNode ch 
    | FGPT.Lf (c) -> FG.Terminal (c, (FG.Lf c))
    | FGPT.Nd ((s,c), l) -> match (FG.getMAPStateConstituent grammar s c) with
	(*  FG.Root r -> FG.Terminal (c, (FG.Lf c))
	|*) FG.Tbl tbl -> 
	    let children =  (List.map (fun v -> processNode v) l) 
	    in (FG.expandTable grammar tbl children)
	| FG.Br br -> 
	    let children =  (List.map (fun v -> processNode v) l)  
	    in let mask = (List.map getChildVariableMask l) 
	    in let tbl = (FG.createDanglingTable !br children (FG.mAPStickyDecisions !br !br.FG.rhs !br.FG.stickyCnts mask) )
	    in FG.Constituent (ref tbl, children, (FG.Nd ( (FG.N (FG.tableHead (ref tbl))), (getPtrees children))))
  in (processNode pTree)

(* Create initial analyses for all the sentences *)
 let rec initializeAnalysis grammar sentence ptree (count : float )=
   let prsr = (FGParser.makeparser grammar) in 
   (*let tm1 = Sys.time () in*)
     match (prsr ptree neg_infinity sentence) with
	 FGParser.Success chart -> 
	   let parseTree = (FGParser.sampleTree grammar chart (FG.getStart grammar) sentence) in
	   let analysis = (parse2analysis grammar parseTree) in
	   (*let tm2 = Sys.time () in*)
	     begin
	       FG.addAnalysis grammar analysis count;
	       analysis; 
	     end
       | FGParser.Failure chart -> 
	 begin
	   Globals.dbgMsg "mh" 10 ("MHSampler.intializeAnalyses: Grammar does not parse sentence: "^  (Array.fold_left (fun  a v -> a ^ " " ^ (FG.symbol2string v)  ) "" sentence));
	   Globals.dbgMsg "mh" 10 ("MHSampler.intializeAnalyses failure with Chart:\n" ^ (FGParser.chart2string grammar chart) ^ "\n");
	   failwith ("MHSampler.intializeAnalyses: Grammar does not parse sentence: "^  (Array.fold_left (fun  a v -> a ^ " " ^ (FG.symbol2string v)  ) "" sentence));
	 end

(* Create initial analyses for all the sentences *)
 let initializeAnalyses grammar sentences structs (counts : float list) = 
   let rec aux s str cnt num = match s, str, cnt with
       ([], [], []) -> []
     | (current :: rest, curstr::rststr, curcnt::rstcnt) -> 
	 let a = (initializeAnalysis grammar current curstr curcnt) in
	   begin
	     Globals.dbgMsg "mh" 1 ("Initialized analysis sequentially: "^ (string_of_int num)^"\n");
	     a :: (aux rest rststr rstcnt (num+1));
	   end
     | _ -> failwith "MHSampler.initializeAnalyses.aux: Structures and sentences not aligned!"
   in (aux sentences structs counts 1)
     
 let rec initializeAnalysisRandom grammar prsr sentence struc =
   match (prsr struc neg_infinity sentence) with
       FGParser.Success chart ->
	 (*   let _ = Globals.dbgMsg "mh" 9 ("Chart: " ^ (FGParser.chart2string grammar chart) ^ "\n") in  *)
	 (* let tm1 = Sys.time () in*)
	 (* let _ = FG.writeGrammar (open_out "grammar.txt") grammar in*)
	 let ps =  (FGParser.sampleTree grammar chart (FG.getStart grammar) sentence) in
	   (* let _ = Globals.dbgMsg "mh" 7 ("Sampled initial parsetree:  " ^  (FGParser.parseTree2String ps)  ^ "\n") in*)
	 let analysis =  (parse2analysis grammar ps ) in
	   (* let tm2 = Sys.time () in *)
	   begin
	     (* Globals.dbgMsg "mh" 7 ("Parsed initialized:  " ^ (FGPT.tree2string ps) ^ "\n");*)
	     (* Globals.dbgMsg "mh" 7 ("Parsed initialized:  " ^ (FGPT.tree2string ps) ^ "\n"); *)
	     (* Globals.dbgMsg "mh" 7 ("Parsed Analysis for initialization in  " ^ (string_of_float (tm2-.tm1)) ^ " seconds.\n");*)
	     analysis;
	   end
     | FGParser.Failure chart ->
	   begin
	   Globals.dbgMsg "mh" 10 ("MHSampler.intializeAnalysisRandom: Grammar does not parse sentence: "^  (Array.fold_left (fun  a v -> a ^ " " ^ (FG.symbol2string v)  ) "" sentence) ^ "\n");
	   Globals.dbgMsg "mh" 10 ("MHSampler.intializeAnalysisRandom failure with Chart:\n" ^ (FGParser.chart2string grammar chart) ^ "\n");
	     failwith ("MHSampler.intializeAnalysisRandom: Grammar does not parse sentence: "^  (Array.fold_left (fun  a v -> a ^ " " ^ (FG.symbol2string v)  ) "" sentence));
	   end	 
       
 (* Create initial analyses randomly for all the sentences *)
 let initializeAnalysesRandom grammar sentences structs counts = 
   let prsr = (FGParser.makeparser grammar) 
   in let results_array = Array.make (List.length sentences) (FG.Terminal ((FG.T {FG.tName="dummy"}), (FG.Lf (FG.T {FG.tName="dummy"})))) (*, FG.T {tName="dummy"})*)
      in begin
	for position = 0 to ((List.length sentences)-1) do
	  results_array.(position) <- (initializeAnalysisRandom grammar prsr (List.nth sentences position) (List.nth structs position));
	    Globals.dbgMsg "mh" 1 ("Initialized analysis: "^ (string_of_int position)^ " with length: " ^ (string_of_int (Array.length  (List.nth sentences position))) ^ (* " with parse:\n\t" ^ (FG.analysis2simpleString results_array.(position)) ^ *) "\n");
	done;
	for position = 0 to ((List.length sentences)-1) do
	  (FG.addAnalysis grammar results_array.(position) (List.nth counts position));
	  (*Globals.dbgMsg "mh" 1 ("Added analysis: "^ (string_of_int position)^"\n");*)
	done;
	
	Array.to_list results_array;
      end

 (* Create initial analyses randomly for all the sentences *)
 (* let initializeAnalysesRandom grammar sentences structs counts = 
   let prsr = (FGParser.makeparser grammar) 
   in let rec makeparses ss strs cnts num = match ss, strs, cnts with
       ([], [], []) -> []
     | (current :: rest, curstr::rstr, count::restcnts) -> let ps = (initializeAnalysisRandom grammar prsr current curstr) 
       in begin
	   (* if (num mod 1000 = 0) then Gc.dump_heap ();*)
	   (* Globals.dbgMsg "mh" 1 ("Initialized analysis: "^ (string_of_int num)^"\n");*)
	   (count, ps) :: (makeparses rest rstr restcnts (num+1));
	 end
     | _ -> failwith "MHSampler.initializeAnalysesRandom.makeparses: Structures and sentences not aligned!"

   in let rec addparses ps num = match ps with
       [] -> []
     | (c, a) :: rest -> begin 
	   (* Globals.dbgMsg "mh" 1 ("Adding initial analysis to grammar: "^ (string_of_int num)^"\n");*)
	    (* if (num mod 1000 = 0) then Gc.dump_heap ();*)
	   (FG.addAnalysis grammar a c);
	   a :: (addparses rest (num+1));
       end
   in let pses = (makeparses sentences structs counts 1)
   (* in let _ = Globals.dbgMsg "mh" 7 ("Adding parses to gammar!\n")*)
   in let anss = (addparses pses 1) 
   in  anss*)

 let rec initializeAnalysisSequentialMAP grammar prsr sentence struc =
   match (prsr struc neg_infinity sentence) with
       FGParser.Success chart -> 
	 let ps =  FGParser.getMAPParseFromChart grammar sentence chart 
	 in (parse2MAPanalysis grammar ps)
     | FGParser.Failure chart -> 
	   begin
	     Globals.dbgMsg "mh" 10 ( "Chart:\n" ^ (FGParser.chart2string grammar chart) ^ "\n");
	     failwith ("MHSampler.intializeAnalysisSequentialMap: Grammar does not parse sentence: "^  (Array.fold_left (fun  a v -> a ^ " " ^ (FG.symbol2string v)  ) "" sentence));
	   end 
   
 (* Create initial analyses randomly for all the sentences *)
 let initializeAnalysesSequentialMAP grammar sentences structs counts = 
   let prsr = (FGParser.makeparser grammar) 
   in let rec makeparses ss strs cnts num = match ss, strs, cnts with
       ([], [], []) -> []
     | (current :: rest, curstr::rstr, count::restcnts) -> let ps = (initializeAnalysisSequentialMAP grammar prsr current curstr) 
       in begin
	   (FG.addAnalysis grammar ps count);
	   ps :: (makeparses rest rstr restcnts (num+1));
	 end
     | _ -> failwith "MHSampler.initializeAnalysesMaximumMAP.makeparses: Structures and sentences not aligned!"
   in (makeparses sentences structs counts 1)

 
(* Pretty print an MH step *)
let mHStep2string result sentence seed oldAnalysis newAnalysis  mhScore oldScore newScore oldAnaScore newAnaScore =
  let seedstring = match seed with
      None -> "None"
    | Some s -> FG.parseTree2string s
  in begin
    "MH PROPOSAL: " ^ result ^ "\n" ^
      "\t Sentence: " ^ (Utils.sentence2string FG.symbol2string sentence ) ^ "\n" ^
      "\t Seed: " ^ (seedstring ) ^ "\n" ^
      "\t Original: " ^ ((FG.analysis2string oldAnalysis )) ^ "\n" ^       
      "\t Proposal: " ^ ((FG.analysis2string newAnalysis )) ^ "\n" ^
      "\t MH score: " ^ (string_of_float mhScore) ^ "\n" ^
      "\t Result LogProb: " ^ (string_of_float newScore) ^ "\n" ^
      "\t Proposal Analysis Score: " ^ (string_of_float newAnaScore) ^ "\n" ^	
      "\t Original Analysis Score: " ^ (string_of_float oldAnaScore) ^ "\n" ^
      "\t Proposal Posterior: " ^ (string_of_float newScore) ^ "\n" ^
      "\t Original Posterior: " ^ (string_of_float oldScore) ^ "\n" 
  end

(* Single MH kernel -- return the sampled analysis *)
let rec sample seeded slice grammar sentence oldAnalysis count =
  (* let _ = Globals.dbgMsg "mh" 9 ("Resampling sentence: " ^ (Utils.sentence2string FG.symbol2string sentence ) ^ "\n") in*)
 (* let _ = Globals.dbgMsg "mh" 9 ("Resampling analysis: " ^ (FG.analysis2string oldAnalysis) ^ "\n") in*)

  (*Get the original score of the grammar *)
  let ptree = if seeded then Some (FG.analysis2parseTree oldAnalysis) else None in
  let oldScore = (FG.scoreGrammar grammar) in
   (*let _ = Globals.dbgMsg "mh" 9 ("Old posterior score: " ^  (string_of_float oldScore)  ^ "\n") in *)
  (* Remove the analysis *)
  (* let tm1 = Sys.time () in*)
  let _ = (FG.removeAnalysis grammar oldAnalysis count)  in
  let threshold = 
    if slice 
    then let minimum = FG.getMinimumScoringProduction oldAnalysis in
    (*let _ = Globals.dbgMsg "mh" 9 ("Miinumum Score: " ^ (string_of_float (exp minimum)) ^ "\n") in*)
    let thresh =  (Random.float (exp minimum))
(*    in let  _ = Globals.dbgMsg "mh" 9 ("Sampled Min: " ^ (string_of_float thresh) ^ "\n")*)
    in (log thresh) 
    else neg_infinity in
  (* Score the old analysis with the updated grammar *)
  let oldAnaScore = (FG.scoreAnalysis grammar oldAnalysis) in
  (*let _ = Globals.dbgMsg "mh" 9 ("Old analysis score: " ^  (string_of_float oldAnaScore)  ^ "\n") in *)
  let prsr = (FGParser.makeparser grammar) in
  (* let (s, e, its, n) = (prsr sentence) in *)
  (* let tm2 = Sys.time () in*)
  let chart = 
    match (prsr ptree threshold sentence) with
	FGParser.Success chart -> chart
      | FGParser.Failure chart ->
	  begin
	    (*Globals.dbgMsg "mh" 10 ( "Failed to find parse "^ (Utils.sentence2string FG.symbol2string sentence ) ^" with threshold: "^ (string_of_float threshold ) ^". Reparsing!\n");*)
	    (*Globals.dbgMsg "mh" 10 ( "Chart:\n" ^ (FGParser.chart2string grammar chart) ^ "\n");*)
	    match  (prsr ptree neg_infinity sentence) with
		FGParser.Success ch -> ch
	      | FGParser.Failure ch -> 
		  begin
		    (*Globals.dbgMsg "mh" 10 ( "Chart:\n" ^ (FGParser.chart2string grammar ch) ^ "\n");*)
		    failwith ("MHSampler.sample: Grammar does not parse sentence: "^  (Array.fold_left (fun  a v -> a ^ " " ^ (FG.symbol2string v)  ) "" sentence));
		  end
	  end in
  (*let tm3 = Sys.time () in*)
  (* let _ = Globals.dbgMsg "mh" 7 ("Parse performed in : " ^ (string_of_float (tm3-.tm2))  ^ " seconds.\n") in*)
     (*let _ = Globals.dbgMsg "mh" 9 ("Chart: " ^ (FGParser.chart2string grammar chart) ^ "\n") in   *)
  let newTree =  (FGParser.sampleTree grammar chart (FG.getStart grammar) sentence) in
  (* let _ = Globals.dbgMsg "mh" 9 ("New tree sampled: " ^  (FGParser.parseTree2String newTree)  ^ "\n") in*)
  let newAnalysis = (parse2analysis grammar newTree ) in
    (*  let _ = Globals.dbgMsg "mh" 9 ("New analysis: " ^  (FG.analysis2string newAnalysis)  ^ "\n") in   *)
    (*Score the new analysis with the updated grammar *)
  let newAnaScore = (FG.scoreAnalysis grammar newAnalysis) in
     (*let _ = Globals.dbgMsg "mh" 9 ("New analysis score: " ^  (string_of_float newAnaScore)  ^ "\n") in *)
  let _ = FG.addAnalysis grammar newAnalysis count in 
  let newScore = (FG.scoreGrammar grammar) in
  (*let _ = Globals.dbgMsg "mh" 9 ("New posterior score: " ^  (string_of_float newScore)  ^ "\n") in *)
  let mhScore = (newScore +. oldAnaScore) -. (oldScore +. newAnaScore) in
    (*let _ = Globals.dbgMsg "mh" 9 ("MH Score: " ^  (string_of_float mhScore)  ^ "\n") in*)
    begin
      (* (print_string (FG.grammar2string grammar)); *)
      if (is_nan mhScore) then failwith "MHSampler.sample: MH score not a number."
      else if (mhScore > 0.0)
      then (*Accept*)
	begin
	  (* Globals.dbgMsg "mh" 9 ("Accepted because over threshhold\n.");*)
	  (* Globals.dbgMsg "mh" 10 (mHStep2string "ACCEPT" sentence ptree oldAnalysis newAnalysis mhScore oldScore newScore oldAnaScore newAnaScore);*)
	  newAnalysis; 
	end
      else if flipLog mhScore
      then (*Accept*)
	begin
	  (* Globals.dbgMsg "mh" 9 ("Accepted by chance\n.");*)
	   (*Globals.dbgMsg "mh" 10  (mHStep2string "ACCEPT" sentence ptree oldAnalysis newAnalysis mhScore oldScore newScore oldAnaScore newAnaScore);*)
	  newAnalysis; 
	end 
      else    (*Reject*)
	begin
	  (* Globals.dbgMsg "mh" 9 ("Rejected.\n.");*)
	  FG.removeAnalysis grammar newAnalysis count;
	  FG.addAnalysis grammar oldAnalysis count;
	   (*Globals.dbgMsg "mh" 10  (mHStep2string "REJECT" sentence ptree oldAnalysis newAnalysis mhScore oldScore newScore oldAnaScore newAnaScore);*)
	  oldAnalysis;
	end
    end

(* Do a single MH sweep through the corpus -- note that this is a
   higher order function which will apply argument func to the grammar,
   current sentence and analysis to obtain *)
 let mhSweep seeded slice func start grammar analyses counts sweepNum (* hyperWithin hyperOutwith hyper*) = 
  let rec aux st gr anals counts results n = match anals, counts with
      ([], []) -> let res = List.rev results in 
	      begin
		(* Globals.dbgMsg "mh" 7 ("ANALYSES:\n"^
					 (List.fold_left (fun acc ana -> acc ^ FG.analysisYield2string ana ^ "\n" ) "" res)
					^"\n"); *)
		(res, st);
	      end
    | (a::ans, count::rstcnts) ->
	 (* let _ =  Globals.dbgMsg "mh" 7 ("MH Sample: "^ (string_of_int n)^" beginning.\n") in*)
	let tm1 = Sys.time () in
	let s =  (Array.of_list (FG.analysisYield a)) in
	let newAna = (sample seeded slice grammar s a count) in
	let tm2 =Sys.time () in
	let time = (tm2-.tm1) in
	let stats = (func st grammar s a newAna (results @ [newAna] @ ans) time n) in
	  begin
	    (* Utils.printLPHashSize ();
	    Utils.printLGHashSize ();
	    Utils.printPFHashSize ();
	    Utils.printPYHashSize (); *)
	     (* Globals.dbgMsg "mh" 7 ("\tMH Sample: "^ (string_of_int n)^" performed on: " ^ (string_of_int (Array.length s)) ^ " word sentence in " 
			     ^ (string_of_float (tm2-.tm1)) 
			     ^ " seconds.\n");*)
	    (aux stats grammar ans rstcnts (newAna::results) (n+1));
	  end
    | _ -> failwith "MHSampler.mhSweep.aux: Analyses and counts are not aligned!"
  in let res = aux start grammar analyses counts [] 1
  (*in let _ = HPS.hyperParameterSweep grammar hyperWithin hyperOutwith hyper*)
  in res

(* Do a full sampler run *)
(*  let mhRun grammar inputs burnin samples =
    let analyses = ref (initializeAnalyses grammar inputs) in
      begin
       
      for i=1 to burnin do
	analyses := (mhSweep grammar inputs !analyses);
      done;
      for i=1 to samples do
	analyses := (mhSweep grammar inputs !analyses);
      done;
      (grammar, !analyses);
    end *)


