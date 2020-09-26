open MHSampler
open MHTableSampler
open GibbsSampler
(* open HyperParameterSampler

module HPS = HyperParameterSampler*)

(* Combined MH/Gibbs sweep *)
(* let combinedSweep func start grammar analyses =
  let (results, stats) = mhSweep func start grammar  analyses
  in  gibbsSweep func stats grammar results *)

(* do N combined sweeps with 1 gibbs and 1 mh per sweep *)
(* let rec doNSweeps func start grammar analyses n =
    if n < 1 
    then (analyses, start)
    else if n = 1
    then (combinedSweep func start grammar analyses)
    else let (results, stats) = (combinedSweep func start grammar analyses)
      in doNSweeps func stats grammar results (n-1) *)
  
(* Do N gibbs sweeps *)
let rec doNgibbs func start grammar analyses gibbs =
    if gibbs < 1 
    then (analyses, start)
    else if gibbs = 1
    then (gibbsSweep func start grammar analyses)
    else let (results, stats) = (gibbsSweep func start grammar  analyses)
      in doNgibbs func stats grammar results (gibbs-1)

(* Do N MH Table sweeps *)
let rec doNmhtable func start grammar mhtbl =
  if mhtbl < 1
  then start (* failwith "Sampler.doNmhtable: Cannot do less than one sweep" *)
  else 
    
    let (stats, n) =  (MHTableSampler.mhTableSweep func start grammar)
    in doNmhtable func stats grammar (mhtbl-1)
      
(* let rec doCorpusSequentially func start grammar iterations sentences = 
  match sentences with
      [] -> []
    | sentence :: rest -> 
	let _ = (initializeAnalysis grammar sentence) in
	  doCorpusSequentially func start grammar iterations *)

(* Do N MH sweeps *)
let  doNmh seeded slice betweenUpdate withinUpdate start grammar analyses counts mh (* hyperWithin hyperOutwith hyper*) =
  let rec aux aux_st aux_an sweepNum totalTime = 
    if sweepNum > mh 
    then (aux_an, aux_st)
    else let tm1 = Sys.time () 
      in let (results, stats) = (mhSweep seeded slice withinUpdate aux_st grammar aux_an counts sweepNum (* hyperWithin hyperOutwith hyper*) )
      in let tm2 =Sys.time () 
      in let time = (tm2-.tm1) in
      let (stats2, time2) = (betweenUpdate stats grammar results (totalTime +. time) sweepNum) 
      in begin 
	 (* Globals.dbgMsg "mh" 7 ("MH: "^ (string_of_int mh)^"\n");*)
	  (* Globals.dbgMsg "mh" 7 ("ANALYSES:\n"^
	     (List.fold_left (fun acc ana -> acc ^ FG.analysisYield2string ana ^ "\n" ) "" an)
	     ^"\n");*)
	  (* Globals.dbgMsg "mh" 7 ("MH Sweep: "^ (string_of_int sweepNum) ^" performed in: "^(string_of_float (time))  ^" seconds.\n"); *)
	  (aux stats2 results (sweepNum+1) time2);
	end
  in if mh = 1
    then 
      (*let _ = Globals.dbgMsg "mh" 7 ("MH: "^ (string_of_int mh)^"\n")
      in*) let tm1 = Sys.time () 
      in let (results, stats) = (mhSweep seeded slice withinUpdate start grammar analyses counts 1 (* hyperWithin hyperOutwith hyper*))
      in let tm2 =Sys.time () 
      in let time = (tm2-.tm1) 
      in let (stats2, time2) = (betweenUpdate stats grammar results time 1)
      in  (results, stats2)
    else (aux start analyses 1 0.0)

(* let sequentialInitialization seeded slice betweenUpdater withinUpdater stats gram sentences structs counts sweepspersentence tail (* hyperWithin hyperOutwith hyper*) =
  let rec loop aux_st aux_an aux_cnt sweepNum num = 
    if sweepNum > num 
    then (aux_an, aux_st)
    else let (results, stats) = 
      begin 
	(mhSweep seeded slice withinUpdater aux_st gram aux_an aux_cnt sweepNum (* hyperWithin hyperOutwith hyper*))
      end
      in (loop stats results (sweepNum+1) num);
  in let rec removeTail l = match l with
      [] -> []
    | hd1::hd2::[] -> [hd1] 
    | hd::tl -> hd::(removeTail tl)
  in let rec doNext st analyses sents strcts totalTime num = match (sents, strcts) with
      ([],[]) -> analyses
    | (sen::restsn, str::restst ) -> 
	(* let _ = Globals.dbgMsg "sampler" 7 ("Processing sentence: " ^ (Utils.sentence2string (fun s -> FG.symbol2string s) sen ) ^ "\n")
	in  let _ = Globals.dbgMsg "sampler" 7 ("Number of Anlyses: "^ (string_of_int (List.length analyses)) ^".\n")
	in  let _ = Globals.dbgMsg "sampler" 7 ("Tail: "^ (string_of_int (tail)) ^".\n")
	in *) let tm1 = Sys.time () 
        in let newAnalysis = MH.initializeAnalysis gram sen (if seeded then str else None) 
	in let tm2 = Sys.time () 
	in let time = (tm2-.tm1)  
	in let analyses = 
	  if (tail == 0) || (List.length analyses) <= tail
	  then analyses
	  else (removeTail analyses)
	in let newAnalyses = (newAnalysis :: analyses)
	in let currentNumAnalyses = (List.length newAnalyses)
	in let numSweeps =   (sweepspersentence st currentNumAnalyses)
	in let (st2, time2) = (betweenUpdater stats gram analyses (totalTime +. time) num) 
	(* in let _ = Globals.dbgMsg "sampler" 7 ("Sequential Initializing by running: " ^ (string_of_int numSweeps) 
						^" sweeps on: "
						^ (string_of_int currentNumAnalyses)
						^" analyses."
						^ " Number of sentences left: " 
						^ (string_of_int (List.length restsn))
						^ "\n") *)
	in if numSweeps > 0 
	  then let (nan, nst) = loop st2 newAnalyses 0 numSweeps
	    in doNext nst nan restsn restst time2 (num+1)
	  else doNext st2 newAnalyses restsn  restst time2 (num+1)
    | _ -> failwith "Sampler.sequentialInitialization: sentences and structures not aligned!"
  in doNext stats [] sentences structs 0.0 1 *)
  

let sampleSequentially updater memory stats gram sentences  =
  let rec doNext st analyses sents n = match sents with
      [] -> analyses
    | sen::restsn ->
	let memAnas = (memory gram analyses)
	in let tm1 = Sys.time ()
	in let newAnalysis = MH.initializeAnalysis gram sen None
	in let tm2 = Sys.time ()
	in let newAnalyses = ((Some newAnalysis) :: memAnas)
	in let time =  (tm2-.tm1)
	in let stts = (updater st gram newAnalyses time n) 
	in doNext stts newAnalyses restsn (n+1)
  in doNext stats [] sentences 1
    
    
(*(* Do one gibbs/mh sweeps with <gibbs> gibss sweeps and <mh> mh sweeps *)
let rec doGibbsMHSweeps func start grammar analyses gibbs mh =
    let (results, stats) = doNgibbs func start grammar analyses gibbs
    in doNmh func stats grammar results mh *)

(*
(* Do N gibbs/MH sweeps with <gibbs> gibss sweeps and <mh> mh sweeps per sweep *)
let rec doNGibbsMHSweeps func start grammar analyses gibbs mh n =
    if n < 1 
    then (analyses, start)
    else if n = 1
    then (doGibbsMHSweeps func start grammar  analyses gibbs mh)
    else let (results, stats) = (doGibbsMHSweeps func start grammar  analyses gibbs mh)
      in doNGibbsMHSweeps func stats grammar  results gibbs mh (n-1) *)
