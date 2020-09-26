(***********************************************************************************
 ***********************************************************************************
 *                              Module: GibbsSampler                               * 
 * --------------------------------------------------------------------------------*
 *            This module implements a gibbs sampler for FG analyses               * 
 ***********************************************************************************)  
open Utils
open FragmentGrammar
open MHSampler

module FG = FragmentGrammar
      
(* Get the distribution over tables. Note this sets the grammar back
   to its start state when it is done. *)
let getTableDistribution grammar (ana : FG.analysis)  (anals : FG.analysis list) =
  let rec aux a als = match als with
      [] -> 
	begin 
	  FG.reseat grammar a ana 1.0; (*FIXME: is this the right count to pass through?*) 
	  [];
	end
    | hd::tl ->
	begin
	  FG.reseat grammar a hd 1.0; (*FIXME: is this the right count to pass through?*) 
	  let lp = FG.scoreGrammar grammar  
	  in begin
	    lp :: (aux hd tl);
	    end
	end
  in let unnormed =(aux ana anals) in
  let normed = (normalizeLog unnormed) in
       begin
	(* print_string (string_of_float (List.hd unnormed));
	 print_string (string_of_float (List.hd normed)); *)
	 normed;
       end

(* String version of Gibbs step *)
let gibbsStep2string proposals dist oldAnalysis newAnalysis =
  (List.fold_left2 (fun a v1 v2 -> (FG.analysis2string v1) ^ "prob: " ^ (string_of_float (exp v2)) ^ "\n" ^ a) "" proposals dist) ^
  "\t\tFormer Analysis: "^ (FG.analysis2string oldAnalysis) ^"\n" ^
  "\t\tNew Analysis: " ^ (FG.analysis2string newAnalysis)  ^ "\n\n"  
  
(* Sample a new analysis node in place of a given table -- update grammar accordingly.*)
let sampleAnalysisNode (grammar : FG.grammar) (analysis : FG.analysis) (l : FG.analysis list) =
  let proposals = FG.getSafeReseats analysis
  in let dist = getTableDistribution grammar analysis  proposals 
  in let newAna = (sampleDiscrete proposals dist)
  in begin
      (* print_float (List.hd dist); *)
      (Globals.dbgMsg "gibbs" 8 (gibbsStep2string proposals dist analysis newAna));
      FG.reseat grammar analysis newAna 1.0; (*FIXME: is this the right count to pass through here?*)
      newAna;
    end

(* Return a new analysis after doing a bottom up gibbs sweep of the
  current one. *)
let gibbsAnalysis grammar a =
  let tFunct pt s = FG.Terminal (  s, pt)
  and pFunct pt t children =  FG.Constituent ( t, children, pt)
  and vFunct pt t children = (sampleAnalysisNode grammar (FG.Constituent (t, children, pt)) children)
  in FG.foldAnalysis tFunct pFunct vFunct a

let gibbsSweep func start grammar analyses = 
  let rec aux st gr  anals results n = match anals with
      [] -> (results, st)
    | a::ans -> 
	let tm1 = Sys.time () in
	let s =  (Array.of_list (FG.analysisYield a)) in
	let newAna = (gibbsAnalysis grammar a) in
	let tm2 =Sys.time () in
	let time = (tm2-.tm1) in
	let stats = (func st grammar s a newAna (results @ [newAna] @ ans) time n) in
	  begin
	   Globals.dbgMsg "gibbs" 6 ("Gibbs Sample performed in  " 
				      ^ (string_of_float (tm2-.tm1)) 
				      ^ " seconds.\n");
	    (aux stats grammar ans (newAna::results) (n+1));
	  end
  in aux start grammar analyses [] 0;
