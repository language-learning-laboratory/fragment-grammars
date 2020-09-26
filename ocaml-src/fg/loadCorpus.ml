(************************************************************************
 ************************************************************************
 *             Module: ReadFragmentGrammar                              *                       
 * ---------------------------------------------------------------------*
 * Functions for reading a fragment grammar from a file.                * 
 ************************************************************************)
open FragmentGrammar
open Sexp
open Globals
open GibbsSampler
open String

module T = SexpTree
module FG = FragmentGrammar
module G = GibbsSampler  

let sexp2parseTree startsymbol (t : T.tree) = 
  match startsymbol with 
      Some ss -> 
	let rtFn r ch = FG.Nd (ss, ch)
	and ndFn n ch = FG.Nd ((FG.N {FG.nName=n}), ch)
	and lfFn lf  = FG.Lf (FG.T {FG.tName= lf})
	in  (T.foldTree rtFn ndFn lfFn t)
    | None ->
	let rtFn r ch = List.hd ch
	and ndFn n ch = FG.Nd ((FG.N {FG.nName=n}), ch)
	and lfFn lf  = FG.Lf (FG.T {FG.tName= lf})
	in (T.foldTree rtFn ndFn lfFn t)
	
	  
let rec getPtrees (cl : FG.analysis list) = match cl with
    [] -> []
  | FG.Terminal (term, pt)::tl -> pt :: (getPtrees tl)
  | FG.Constituent (t,l, pt)::tl -> pt :: (getPtrees tl)
      
(* Load a sentence into the grammar, return its analysis *)
let loadSentence (g: FG.grammar)  a b pi slipTheta stickTheta (t : T.tree) count =
  let start = FG.getStart g 
  in let createNewAnalysisNode br children =
    let tbl = (FG.createDanglingTable br children (List.map (fun v -> (FG.Val v) ) br.FG.rhs))
    in let node = FG.Constituent (ref tbl, children, (FG.Nd ( (FG.N (FG.tableHead (ref tbl))), (getPtrees children))))
    in begin (FG.addAnalysisNode g node count); node; end 
  in let processContentNode headName children = 
    let h = {FG.nName=headName}
    in let _ = if not (FG.hasRestaurant g h) 
      then FG.createEmptyRestaurant g h 
    in let brRhs = (List.map (fun v -> match v with 
	FG.Terminal ( term, pt) ->  term 
      | FG.Constituent (table, _, pt) ->  FG.N (FG.tableHead table)) children)
    in let possibleBr = (FG.getBaseRuleStructure g h brRhs)
    in (match possibleBr with
	None -> let br = (FG.createNewBaseRule g h brRhs ~pi:pi ~slipperyTheta:slipTheta ~stickyTheta:stickTheta) in
		  (createNewAnalysisNode br children)
      | Some br -> (createNewAnalysisNode br children))
  in let rtFn r ch = (processContentNode (FG.symbol2string start) ch)
  and ndFn n ch = (processContentNode n ch)
  and lfFn lf  = (FG.Terminal ((FG.T {FG.tName=  lf}), (FG.Lf (FG.T {FG.tName=  lf}))))
  in let final = (T.foldTree rtFn ndFn lfFn t) in
       begin
	 Globals.dbgMsg "lc" 9 "Loaded sentence.\n";
	 final
       end



let gibbsMergeNumber = ref 0

(* Load a sentence into the grammar, sequentially gibbs-merge 
nodes into existing tables to avoid the grammar getting outrageously 
large. Return the analysis *)
let loadSentenceGibbsMerge (g: FG.grammar)  a b pi slipTheta stickTheta (t : T.tree) count =
  let start = FG.getStart g 
  in let createNewAnalysisNode br children =
    let tbl = (FG.createDanglingTable br children (List.map (fun v -> (FG.Val v) ) br.FG.rhs))
    in let node = FG.Constituent (ref tbl, children, (FG.Nd ( (FG.N (FG.tableHead (ref tbl))), (getPtrees children))))
    in begin (FG.addAnalysisNode  g node count); (G.sampleAnalysisNode g node children); end 
  in let processContentNode headName children = 
    let h = {FG.nName=headName}
    in let _ = if not (FG.hasRestaurant g h) 
      then FG.createEmptyRestaurant g h
    in let brRhs = (List.map (fun v -> match v with 
	FG.Terminal (term, pt) ->  term 
      | FG.Constituent (table, _, pt) ->  FG.N (FG.tableHead table)) children)
    in let possibleBr = (FG.getBaseRuleStructure g h brRhs)
    in (match possibleBr with
	None -> let br = (FG.createNewBaseRule g h brRhs ~pi:pi ~slipperyTheta:slipTheta ~stickyTheta:stickTheta) in
		  (createNewAnalysisNode br children)
      | Some br -> (createNewAnalysisNode br children))
  in let rtFn r ch = (processContentNode (FG.symbol2string start) ch)
  and ndFn n ch = (processContentNode n ch)
  and lfFn lf  = (FG.Terminal ((FG.T {FG.tName=  lf}), (FG.Lf (FG.T {FG.tName=  lf}))))
  in let final = (T.foldTree rtFn ndFn lfFn t) in
       begin
	 gibbsMergeNumber := !gibbsMergeNumber + 1;
	 Globals.dbgMsg "lc" 7  ("Loaded sentence: " 
				  ^ (string_of_int (!gibbsMergeNumber)) 
				  ^ "\n");
	 Utils.printLPHashSize ();
	 Utils.printLGHashSize ();
	 Utils.printPFHashSize ();
	 Utils.printPYHashSize ();
	 final
       end

(* Load a sentence into the grammar, but only load the base rules -- forget
the sentence and analysis though. *)
let loadSentenceBaseRules (g: FG.grammar)  a b pi slipTheta stickTheta (t : T.tree) =
  (* let _ = Globals.dbgMsg "lc" 7 ((T.tree2string t) ^ "\n")
     in *) let start = FG.getStart g 
  in let createNewAnalysisNode br children =
    (* let matchSlippery = List.for_all (fun v -> match v with FG.Val _ -> true | FG.Ptr _ -> false)  
    in *) (* let abr = (* (List.find (fun v -> (matchSlippery (FG.getMem !v))) *) (List.hd (FG.getAbrs br)) (*)*) (* We are just throwing this away so don't do anything fancy *)  *)
    let tbl = (FG.createDanglingTable br children (FG.sampleStickyDecisionsOld br br.FG.rhs br.FG.stickyCnts) )
    in FG.Constituent (ref tbl, children, (FG.Nd ( (FG.N (FG.tableHead (ref tbl))), (getPtrees children))))
  (*  in begin (FG.addAnalysisNode node count); (G.sampleAnalysisNode g node children); end *)
  in let processContentNode headName children = 
    let h = {FG.nName=headName}
    in let _ = if not (FG.hasRestaurant g h) 
      then FG.createEmptyRestaurant g h 
    in let brRhs = (List.map (fun v -> match v with 
	FG.Terminal (term, pt) ->  term 
      | FG.Constituent (table, _, pt) ->  FG.N (FG.tableHead table)) children)
    in let possibleBr = (FG.getBaseRuleStructure g h brRhs)
    in (match possibleBr with
	None -> let br = (FG.createNewBaseRule g h brRhs ~pi:pi ~slipperyTheta:slipTheta ~stickyTheta:stickTheta) in
		  (createNewAnalysisNode br children)
      | Some br -> (createNewAnalysisNode br children))
  in let rtFn r ch = (processContentNode (FG.symbol2string start) ch)
  and ndFn n ch = (processContentNode n ch)
  and lfFn lf  = (FG.Terminal ((FG.T {FG.tName=lf}), (FG.Lf (FG.T {FG.tName=  lf}))))
  in let _ = (T.foldTree rtFn ndFn lfFn t) in
       begin
	 (* Globals.dbgMsg "lc" 7 "Loaded sentence.\n"; *)
	 ()
       end

(* Load a sentence into the grammar, but only load the base rules -- forget
the sentence and analysis though, and do not load any rules corresponding to 
preterminal productions.*)
let loadSentenceBaseRulesNoPreterminals (g: FG.grammar)  a b pi slipTheta stickTheta (t : T.tree) =
  let start = FG.getStart g 
  in let isPreterminal rhs =
    let isTerminal s = match s with
	FG.T t -> true
      | FG.N n -> false
    in if (((List.length rhs) = 1) && (isTerminal (List.hd rhs)))
      then true
      else false 
  in let createNewAnalysisNode br children =
    (* let matchSlippery = List.for_all (fun v -> match v with FG.Val _ -> true | FG.Ptr _ -> false)  
    in *) (* let abr = (* (List.find (fun v -> (matchSlippery (FG.getMem !v))) *) (List.hd (FG.getAbrs br)) (*)*) (* We are just throwing this away so don't do anything fancy *)  *)
    let tbl = (FG.createDanglingTable br children (FG.sampleStickyDecisionsOld br br.FG.rhs br.FG.stickyCnts) )
    in FG.Constituent (ref tbl, children, (FG.Nd ( (FG.N (FG.tableHead (ref tbl))), (getPtrees children))))
  (*  in begin (FG.addAnalysisNode node count); (G.sampleAnalysisNode g node children); end *)
  in let processContentNode headName children = 
    let h = {FG.nName=headName}
    in let _ = if not (FG.hasRestaurant g h) 
      then FG.createEmptyRestaurant g h 
    in let brRhs = (List.map (fun v -> match v with 
	FG.Terminal ( term, pt) ->  term 
      | FG.Constituent (table, _, pt) ->  FG.N (FG.tableHead table)) children)
    in if (isPreterminal brRhs)
      then  (createNewAnalysisNode (FG.createDanglingBaseRule g h brRhs) children)
      else let possibleBr = (FG.getBaseRuleStructure g h brRhs)
	in (match possibleBr with
	    None -> let br = (FG.createNewBaseRule g h brRhs ~pi:pi ~slipperyTheta:slipTheta ~stickyTheta:stickTheta) in
		      (createNewAnalysisNode br children)
	  | Some br -> (createNewAnalysisNode br children))
  in let rtFn r ch = (processContentNode (FG.symbol2string start) ch)
  and ndFn n ch = (processContentNode n ch)
  and lfFn lf  = (FG.Terminal ((FG.T {FG.tName= lf}), (FG.Lf (FG.T {FG.tName=  lf}))))
  in let _ = (T.foldTree rtFn ndFn lfFn t) in
       begin
	 Globals.dbgMsg "lc" 7 "Loaded sentence.\n";
	 ()
       end
