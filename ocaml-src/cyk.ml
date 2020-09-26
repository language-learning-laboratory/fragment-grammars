(************************************************************************
 ************************************************************************
 *                            Module: CYK                                                         *                       
 * ----------------------------------------------------*
 * Probabilistic CYK Parser                                                                   * 
 ************************************************************************)
open Utils
open Tree
open Agenda
(* open SymbolTable

module S = SymbolTable
*)
let unarytolerance  = (log 0.0001) 
let unarydepth  =  3
module type Grammar = 
sig
  type grammar
  type state                     (* This represents a state in the Grammar's FSM *)
  type constituentSymbol         (* This represents an equivalence class of productions from the point that always lead to the same state transition *) 
  type parseTree
  type stateExpectations
  type constExpectations

  val parseTree2string : (parseTree -> string)
  val tree2spans : (int -> constituentSymbol -> int -> 'a) -> parseTree -> int
  val getRootState : grammar  -> state
  val stateConstituentProb : grammar -> state -> constituentSymbol -> float
  val stateConstituent : grammar -> state -> constituentSymbol -> bool
  val getStateConstituents : float -> grammar -> state -> constituentSymbol list
  val nextState : grammar -> state -> constituentSymbol ->  state option
  val constituentSymbol2string : constituentSymbol -> string
  val state2string : grammar -> state -> string
  val rootState : grammar -> state -> bool                      
  val getStartSymbol : grammar -> constituentSymbol
  val getTerminals : grammar -> constituentSymbol list
  val isTerminal : grammar -> constituentSymbol -> bool
  val getSymbols : grammar -> constituentSymbol list
  val getNonterminals : grammar -> constituentSymbol list
  val matchConstituentSymbol : constituentSymbol -> string -> bool
  val getROOTStateExpectations : unit -> stateExpectations
  val updateStateExpectations : stateExpectations option ->  stateExpectations -> constExpectations-> stateExpectations
  val getEmptyConstituentExpectations :  constituentSymbol-> constExpectations
  val updateConstExpectations :  constituentSymbol -> constExpectations option ->  stateExpectations -> float -> float -> constExpectations
  val constituentMatches : constituentSymbol -> constituentSymbol list -> bool
end

module CYKParser (G : Grammar) =
struct   

  (* An active edge is an edge corresponding to a grammar state -- 
     an partially discovered rule *)
  type activeEdge = G.state * int * int

  (* A passive edge is an edge corresponding to a complete constituent *)
  type passiveEdge = G.constituentSymbol * int * int
      
  type edge = Active of activeEdge | Passive of passiveEdge

   (* A seed is a contituent label that a particular span must match *)
  type seedType = Const of G.constituentSymbol list | Noconst | Unspecified

  (* A traversal is a triple (activeEdge, passiveEdge, resultEdge)
     which records a way of building an edge. We don't bother storing
     the resultEdge here. *)
  type traversal =
      {left : activeEdge;
       right : passiveEdge;
       (* logProb : float; *)}

  (* An entry in the parse chart *)
  type chartEntry = 
      {start : int;
       finish : int;
       statesInside :  (G.state, float) Hashtbl.t;                   (* The accumulated inside probability of various state sequences *)
       statesMAP : (G.state, float) Hashtbl.t;
       traversalsInside : (G.state, (traversal, float) Hashtbl.t) Hashtbl.t;
       traversalsMAP : (G.state, (traversal, float) Hashtbl.t) Hashtbl.t;
       constituentInsides :  (G.constituentSymbol, float) Hashtbl.t;
       constituentMAP : (G.constituentSymbol, float) Hashtbl.t;  (* Store the MAP parses for each constituent*)
       constituentExpectations : (G.constituentSymbol, G.constExpectations) Hashtbl.t;  (*  For computing arbitrary chart expectations *)
       stateExpectations : (G.state, G.stateExpectations) Hashtbl.t; (*  For computing arbitrary chart expectations *)
       mutable seed : seedType}

  let getEntryInsideScore entry constituent =
    if Hashtbl.mem entry.constituentInsides constituent  
    then Hashtbl.find entry.constituentInsides constituent
    else neg_infinity  

  let getEntryMAPScore entry constituent =
    if Hashtbl.mem entry.constituentMAP constituent
    then Hashtbl.find entry.constituentMAP constituent
    else neg_infinity
	
  let setEntryInsideScore entry constituent inside =
    begin
      (*Globals.dbgMsg "cyk" 10 ("Setting inside score to: "^ (string_of_float inside) ^" \n");*)
      Hashtbl.replace entry.constituentInsides constituent inside 
    end
  let setEntryMAPScore entry constituent map =
    Hashtbl.replace entry.constituentMAP constituent map 

  type result = Success of chartEntry array array | Failure of chartEntry array array

  let activeEdge2string  grammar ss = match ss with
      state, s, e -> ((G.state2string grammar state) ^ " (" ^ (string_of_int s) ^ " , " ^ (string_of_int e) ^ ")")

  let seedType2string s = match s with
      Const syms -> List.fold_left (fun a v -> a ^ " " ^ G.constituentSymbol2string v) "" syms
    | Noconst  -> "NONE"
    | Unspecified -> "UNSPECIFIED"

  let passiveEdge2string sc  = match sc with
      c, s, e-> ((G.constituentSymbol2string c) ^ " (" ^ (string_of_int s) ^ " , " ^ (string_of_int e) ^ ")")

  let  traversal2string grammar bp =
    "[Left: " ^ (activeEdge2string grammar bp.left) ^ " | " 
    ^ "Right: " ^ (passiveEdge2string bp.right) ^ " | "  ^ "]"  
      
  let chartEntry2string grammar entry =
    "Entry: (" ^ (string_of_int entry.start) ^ " , " ^ (string_of_int entry.finish) ^ ")" ^ " <Seeds: " ^ (seedType2string entry.seed)^ ">" 
    ^ "\n\t\tStates: " 
    ^ (Hashtbl.fold 
	  (fun state inside accum -> 
	    "\n\t\t\t(" ^ (G.state2string grammar state) 
	    ^ " : " 
	    ^ (string_of_float inside) ^ ") " 
	    ^ accum ) 
	  entry.statesInside 
	  "") 
    ^ "\n\t\tState MAPs: " 
    ^ let l1 = (Hashtbl.fold 
		   (fun state inside accum -> 
		     ( ((G.state2string grammar state), inside)::accum)) 
		   entry.statesMAP 
		   []) 
      in let l2 = List.sort (fun (s1,p1) (s2,p2) -> compare p1 p2) l1
      in (List.fold_left 
	     (fun a (s, p) -> 
	       a ^ "\n\t\t\t(" ^ s
	       ^ " : " ^ (string_of_float p) ^ ") ") 
	     "" (List.rev l2)) 
	^ "\n\t\tTraversals: "
	^ (Hashtbl.fold 
	      (fun state traversals accum -> 
		" \n\t\t\t(" ^ (G.state2string  grammar state)
		^ " : " 
		^ (Hashtbl.fold 
		      (fun k v a ->  a ^ "\n\t\t\t\t" ^ (traversal2string grammar k) ^ " : " ^ (string_of_float  v))  
		      traversals
		      "") ^ ") "
		^ accum) 
	      entry.traversalsInside 
	      "")
	^ "\n\t\tTraversal MAPs: "
	^ (Hashtbl.fold 
	      (fun state traversals accum -> 
		" \n\t\t\t(" ^ (G.state2string  grammar state)
		^ " : " 
		^ (Hashtbl.fold 
		      (fun k v a ->  a ^ "\n\t\t\t\t" ^ (traversal2string grammar k) ^ " : " ^ (string_of_float  v))  
		      traversals
		      "") ^ ") "
		^ accum) 
	      entry.traversalsMAP
	      "")
	^ "\n\tConstituent Probs: "
	^ (Hashtbl.fold 
	      (fun eqvC inside accum -> 
		"(" ^ (G.constituentSymbol2string  eqvC)
		^ " : " 
		^ (string_of_float inside)  ^ ") "
		^ accum) 
	      entry.constituentInsides
	      "") 
	^ "\n\tConstituent MAP Probs: "
	^ (Hashtbl.fold 
	      (fun eqvC inside accum -> 
		"(" ^ (G.constituentSymbol2string  eqvC)
		^ " : " 
		^ (string_of_float inside)  ^ ") "
		^ accum) 
	      entry.constituentMAP
	      "")

  let chart2string grammar chart =
    let n = Array.length chart
    in let result = ref ""
    in begin
	for start = 0 to (n-1) do  
	  for finish = start to (n-1) do
	    result := !result ^ ((chartEntry2string grammar chart.(start).(finish)) ^"\n")
	  done;
	done;
	!result;
      end

  (* Initialize a chart entry *)
  let createChartEntry seeded grammar  s f  =
    {start=s;
     finish=f;
     statesInside = Hashtbl.create 500;
     statesMAP = Hashtbl.create 500;
     traversalsInside = Hashtbl.create 500;
     traversalsMAP = Hashtbl.create 500;
     constituentInsides = Hashtbl.create 500;
     constituentMAP = Hashtbl.create 500;
     constituentExpectations = Hashtbl.create 500;
     stateExpectations = Hashtbl.create 500;
     seed = if seeded 
       then Noconst 
       else Unspecified;}

  (* Update a state list with a new state *)
  let updateState grammar entry state traversal logProb bestLogProb =
    begin
      
      (* Globals.dbgMsg "cyk" 10 ("Updating State: "^ (G.state2string grammar state) ^" with traversal: "^ (traversal2string grammar traversal) ^" \n");
      
      Globals.dbgMsg "cyk" 10 ("\twith previous traversal MAPs: "^ 
				  (if  Hashtbl.mem entry.traversalsMAP state
				    then let traversals =  Hashtbl.find entry.traversalsMAP state
				      in( (Hashtbl.fold 
					      (fun k v a ->  a ^ "\n\t\t" ^ (traversal2string grammar k) ^ " : " ^ (string_of_float (exp v)))  
					      traversals
					      ""))
				    else "NONE")
				^" \n"); *)

      (* Update the INSIDE scores of the state.*)
      (if Hashtbl.mem entry.statesInside state
	then let oldStateSeqProb = Hashtbl.find entry.statesInside state
	  in Hashtbl.replace entry.statesInside state (Utils.logsumexp [oldStateSeqProb; logProb])
	else Hashtbl.add entry.statesInside state  logProb);

      (* Update the MAP scores of the state.*)
      (if Hashtbl.mem entry.statesMAP state
	then let oldStateSeqProb = Hashtbl.find entry.statesMAP state
	  in (if (bestLogProb > oldStateSeqProb)
	    then Hashtbl.replace entry.statesMAP state bestLogProb else ())
	else Hashtbl.add entry.statesMAP state bestLogProb);

      (*Update the INSIDE traversals *)
      (if Hashtbl.mem entry.traversalsInside state
	then let traversals = Hashtbl.find entry.traversalsInside state
	  in if Hashtbl.mem traversals traversal
	    then let oldTraversalProb = Hashtbl.find traversals traversal
	      in Hashtbl.replace traversals traversal (Utils.logsumexp [oldTraversalProb; logProb])
	    else Hashtbl.add traversals traversal logProb
	else let traversals = Hashtbl.create 20
	  in let _ = Hashtbl.add traversals traversal logProb
	  in Hashtbl.add entry.traversalsInside state traversals);

      (*Update the MAP traversals *)
      (if Hashtbl.mem entry.traversalsMAP state
	then let besttraversals = Hashtbl.find entry.traversalsMAP state
	  in if Hashtbl.mem besttraversals traversal
	    then let oldTraversalProb = Hashtbl.find besttraversals traversal
	      in (if (bestLogProb > oldTraversalProb)
		then Hashtbl.replace besttraversals traversal bestLogProb
		else ())
	    else Hashtbl.add besttraversals traversal bestLogProb
	else let besttraversals = Hashtbl.create 20
	  in let _ = Hashtbl.add besttraversals traversal bestLogProb
	  in Hashtbl.add entry.traversalsMAP state besttraversals);
    end

  (* If we have successfully completed then go ahead and update based on this:
     entry: a chart entry
     production: a rule that can be completed in this entry
     newStateSeqProb: the product of the inside probabilities of the constituents which match the rule's RHS *)
  let rec updatePassiveEdge grammar entry state constituent traversal logProb bestLogProb =
    let oldCompletionProb = 
      if Hashtbl.mem entry.constituentInsides constituent (* get the sum inside prob of this LHS *) 
      then Hashtbl.find entry.constituentInsides constituent
      else neg_infinity
    and oldCompletionMAP =
      if Hashtbl.mem entry.constituentMAP constituent
      then Hashtbl.find entry.constituentMAP constituent
      else neg_infinity
    (* in let _ = Globals.dbgMsg "cyk" 10 ("Old constituent MAP: " ^ (string_of_float  oldCompletionMAP) ^
					   " Old constituent inside: " ^ (string_of_float  oldCompletionMAP) ^ "\n") *)
    (* This is the inside probability of the current production (rule) *) 
    in let ruleProb =  (G.stateConstituentProb grammar state constituent)
    in let newProductionProb = (logProb +. ruleProb)
    in let newBestProductionProb = (bestLogProb +. ruleProb)
    in begin 
	(* Globals.dbgMsg "cyk" 10 ("Updating passive edge 2: \n" 
				  (* ^ (chartEntry2string entry) ^ " "*)
	                          ^ "\tConstituent: "^ (G.constituentSymbol2string constituent) ^ "\n"); *)

	(* Update the INSIDE probabilty of this completion *)
	(Hashtbl.replace entry.constituentInsides constituent (Utils.logsumexp [oldCompletionProb; newProductionProb]));

	(*Update the MAP probability of this completion*)
	(if (newBestProductionProb > oldCompletionMAP)
	then (Hashtbl.replace entry.constituentMAP constituent newBestProductionProb)
	else ());


      end
      
  (* Add a new state transition to the chart *)
  let addNewStateToEntry threshold grammar entry newState  traversal logProb bestLogProb =
   (*  Globals.dbgMsg "cyk" 10 ("Adding new state to entry. \n"); *)
    let constituents = G.getStateConstituents threshold grammar newState        (* Get the set of productions associated with this state *)
    in begin
	(* Add the new state to the set of states *)
	(updateState grammar entry newState  traversal logProb bestLogProb);
	
	(* If this has led to any completions then update the sums.*)
	(List.iter
	    (fun constituent -> 
	      match entry.seed with
		  Unspecified -> (updatePassiveEdge grammar entry newState constituent  traversal logProb bestLogProb)
		| Noconst -> ()
		| Const seeds -> 
		    if G.constituentMatches constituent seeds 
		    then  (updatePassiveEdge grammar entry newState constituent traversal logProb bestLogProb)
		    else ())
	    constituents);
      end

  (* Do "reverse prediction" -- semi-naive bottom-up evaluation to
     handle unaries approximately correctly. *)
  let addStartsToEntry threshold grammar entry  =
    let root = G.getRootState grammar in
    let rec processNextStep depth childScores childMAPs =  
      if (Hashtbl.length childScores = 0) then ()
      else (let parentConstituentScores = Hashtbl.create 25
	in let parentConstituentMAPs = Hashtbl.create 25
	in let updatedStates = ref []
	in let _ = (Hashtbl.iter (fun child childInside ->
	  let newStateOption = G.nextState grammar root child  
	  in match newStateOption with
	      None -> ()
	    | Some newState ->
		let traversal = {left = (root, entry.start,  entry.finish); right = (child, entry.start, entry.finish);}
		in let childMAP = Hashtbl.find childMAPs child
		in let _ = begin updatedStates := (newState, childInside,childMAP, traversal)::!updatedStates end 
		in let parents = G.getStateConstituents threshold grammar newState        
		in (List.iter (fun parent -> 
		  let validParent = match entry.seed with
		      Unspecified -> true
		    | Noconst -> false
		    | Const seeds ->  G.constituentMatches parent seeds 
		in if validParent
		  then let oldParentInside = if Hashtbl.mem parentConstituentScores parent
		    then Hashtbl.find parentConstituentScores parent
		    else neg_infinity
		    in let oldParentMAP = if Hashtbl.mem parentConstituentMAPs parent
		      then Hashtbl.find parentConstituentMAPs parent
		      else neg_infinity
		    in let newMAPCandidateScore = childMAP +. (G.stateConstituentProb grammar newState parent)
		    in let newInsideIncrement = (childInside +. (G.stateConstituentProb grammar newState parent) )
		    in let newParentInside =  (Utils.logsumexp [oldParentInside; newInsideIncrement])	
 		    in let _ = (Hashtbl.replace parentConstituentScores parent newParentInside)
		    in let newMAP = if newMAPCandidateScore > oldParentMAP
		      then newMAPCandidateScore
		      else oldParentMAP
		    in (Hashtbl.replace parentConstituentMAPs parent newMAP)
		  else ()) parents)) childScores)  
	in let _ = List.iter (fun s -> let state, stateProb, stateMAP, traversal = s in (updateState grammar entry state  traversal stateProb stateMAP)) !updatedStates
	in let newParentScores = Hashtbl.create 25
	in let _ = (Hashtbl.iter  
		       (fun constituent chainInside  -> 
			 let oldInsideScore = getEntryInsideScore entry constituent                          
			 in let newInsideScore = (Utils.logsumexp [oldInsideScore; chainInside])
			 in let _ = setEntryInsideScore entry constituent newInsideScore 
			 in let oldMAPScore = getEntryMAPScore entry constituent
			 in let chainMAPScore = Hashtbl.find parentConstituentMAPs constituent
			 in let _ = (if (chainMAPScore > oldMAPScore) then setEntryMAPScore entry constituent chainMAPScore else ())
			 (*in let changeRatio =  newInsideScore -. oldInsideScore*)
			 (*in if chainInside > unarytolerance then Hashtbl.add newParentScores constituent chainInside else ())
		       parentConstituentScores)*)
			 in if depth < unarydepth then Hashtbl.add newParentScores constituent chainInside else ())
	                    parentConstituentScores)
	in (processNextStep (depth + 1) newParentScores parentConstituentMAPs))
    in (processNextStep 0 entry.constituentInsides entry.constituentMAP)

  (* Set the spans of a chart *)
  let setSpans grammar chart start label finish =
    let entry = chart.(start).(finish-1)
    in match entry.seed with 
	Const oldseeds ->  
	  if G.matchConstituentSymbol label "<+>" 
	  then let ns =  G.getNonterminals grammar
	    in entry.seed <- Unspecified
	  else entry.seed <- Const (label::oldseeds)
      | Noconst ->  entry.seed <- Const [label]
      | Unspecified -> entry.seed <- Const [label]
	  
(* (G.state2string grammar (G.getRootState grammar)) ^*)
  let computeExpectations grammar entry chart  =
    let rec getStateExpectations state entry waiting =
      (*Globals.dbgMsg "cyk" 10 ("Computing expectations for state: " 
				^ (G.state2string grammar state) ^ " in entry: (" 
				^ (string_of_int entry.start) ^ "," 
				^ (string_of_int entry.finish) ^")\n");*)
      if (state = (G.getRootState grammar))
      then (G.getROOTStateExpectations ())
      else if Hashtbl.mem entry.stateExpectations state
      then Hashtbl.find entry.stateExpectations state
      else match
	  Hashtbl.fold 
	    (fun traversal traversalProb acc ->
	      let (lstate, lstart, lfinish) = traversal.left
	      in let (rconst, rstart, rfinish) = traversal.right
	      in let lentry = chart.(lstart).(lfinish)
	      in let rentry = chart.(rstart).(rfinish)
	      in let lExp = (getStateExpectations lstate lentry waiting)
	      in let rExp = (getConstituentExpectations rconst rentry waiting)
		(*in let _ = Globals.dbgMsg "cyk" 10 ("(" ^ (string_of_int entry.start) ^ "," ^ (string_of_int entry.finish) ^ ") ")*)
	      in Some (G.updateStateExpectations acc lExp rExp))
	    (Hashtbl.find entry.traversalsInside state) None
	with
	    Some stateExpectations ->
	      let _ = Hashtbl.add entry.stateExpectations state stateExpectations
	      in stateExpectations
	  | None -> failwith "Cyk.computeExpectations: Got None return value!"
    and getConstituentExpectations constituent entry waiting = 
      (*Globals.dbgMsg "cyk" 10 ("Computing expectations for constituent: " 
				^ (G.constituentSymbol2string  constituent) ^ " in entry: (" 
				^ (string_of_int entry.start) ^ "," 
				^ (string_of_int entry.finish) ^ ")\n");*)
      if List.mem (constituent, entry.start, entry.finish) waiting
      then (G.getEmptyConstituentExpectations constituent) (* FIXME!!!!!! THIS IS VERY BROKEN, DON'T PAY ATTENTION TO RESULTS OF EXPECTATIONS WHEN THERE ARE UNARIES failwith "I cannot handle unary recursion!"*)
      else if entry.start == entry.finish && (G.isTerminal grammar constituent)
      then (G.getEmptyConstituentExpectations constituent)
      else if Hashtbl.mem entry.constituentExpectations constituent
      then Hashtbl.find entry.constituentExpectations constituent
      else match 
	  Hashtbl.fold 
	    (fun state stateProb acc ->
	      if (G.stateConstituent grammar state constituent) 
	      then let stateExp = (getStateExpectations state entry ((constituent, entry.start, entry.finish)::waiting))
		in let prodProb = (G.stateConstituentProb grammar state constituent)
		in let constituentInside = Hashtbl.find entry.constituentInsides constituent
		in Some (G.updateConstExpectations constituent acc stateExp  ((prodProb +. stateProb) -. constituentInside) (prodProb +. stateProb))
	      else acc)
	    entry.statesInside None
	with 
	  | Some constituentExpectations -> 
	      let _ = Hashtbl.add entry.constituentExpectations constituent constituentExpectations
	      in constituentExpectations
	  | None -> failwith "Cyk.getConstituentExpectations: Got None return value!" 
    in Hashtbl.iter (fun const constinside -> let _ = getConstituentExpectations const entry [] in () ) entry.constituentInsides

      (* Parse the sentence bottom up. *)
  let parse (grammar : G.grammar) tree threshold (input : G.constituentSymbol array)  =
    (*let _ = Globals.dbgMsg "cyk" 10 ("Parsing string: " ^ (Array.fold_left (fun  a v -> a ^ " " ^ (G.constituentSymbol2string v)  ) "" input) ^ "\n") in*)
    let n = (Array.length input) 
    in let (chart : chartEntry array array ) =
      (let init_row = (fun s -> Array.init n (createChartEntry (if tree = None then false else true) grammar s))
	in Array.init n init_row)
    in let _ = match tree with 
	None ->  (* Globals.dbgMsg "cyk" 10 ("Seed tree: " ^  "None" ^ "\n"); *) 0
      | Some t ->  (* Globals.dbgMsg "cyk" 10 ("Seed tree: " ^  (G.parseTree2string t) ^ "\n");*)  G.tree2spans (setSpans grammar chart) t
    in begin
	(*Globals.dbgMsg "cyk" 1 ("PARSING!\n");*)
	 (* Initialize the chart *)
	 for position = 0 to (n-1) do
	   (*let _ =  Globals.dbgMsg "cyk" 10 ("Initializing word: " ^ (string_of_int position) ^ "\n") in*)
	   let target = chart.(position).(position)
	   in let word = input.(position)
	   (* in let wordProduction = (G.getTerminalProduction grammar word) *)
	   in let root = G.getRootState grammar 
	   (*in let _ =  Globals.dbgMsg "cyk" 1 ("Word: " ^ (G.constituentSymbol2string word)^"\n")*)
	   in let constituents, probs =
	     if G.matchConstituentSymbol word "<.>" 
	     then let ts = G.getTerminals grammar
	       in (ts, (Utils.repeat 0.0 (List.length ts)))  
	     else if G.matchConstituentSymbol word "<E.>" 
	     then let ts =  G.getTerminals grammar
	       in (ts, (Utils.repeat (log (1.0 /. (float_of_int (List.length ts)))) (List.length ts)))  
	     else if G.matchConstituentSymbol word "<+>" 
	     then let ns =  G.getNonterminals grammar
	       in (ns, (Utils.repeat 0.0 (List.length ns)))
	     else if G.matchConstituentSymbol word "<E+>" 
	     then let ns =  G.getNonterminals grammar
	       in (ns, (Utils.repeat (log (1.0 /. (float_of_int (List.length ns)))) (List.length ns)))
	     else if   G.matchConstituentSymbol word "<*>" 
	     then let ss =  G.getSymbols grammar
	       in (ss, (Utils.repeat 0.0 (List.length ss)))
	     else if   G.matchConstituentSymbol word "<E*>" 
	     then let ss =  G.getSymbols grammar
	       in (ss, (Utils.repeat (log (1.0 /. (float_of_int (List.length ss)))) (List.length ss)))
	     else ([word], [0.0]) 
	   in let _ = List.iter2 
	     (fun w p ->
	       let traversal = {left = (root, target.start,  target.finish);
				right = (w, target.start, target.finish);}
	       in begin
		   (updatePassiveEdge grammar target root w traversal p p);
		   (Hashtbl.add target.constituentExpectations w (G.getEmptyConstituentExpectations w));
		 end)
	     constituents probs
	   in begin
	       (addStartsToEntry threshold grammar target);
	        (*Globals.dbgMsg "cyk" 10 ( "\tEntry: " ^ (chartEntry2string grammar target) ^ "\n" );*)
	       
	       (computeExpectations grammar target chart);
	      (* (unaryExpectations threshold grammar target);*)
	     end

	 done;

	 (* main loop *)
	 for span = 1 to (n-1) do                                        (* Loop through the different span sizes *)
	   for start = 0 to (n-1) - span  do                             (* loop through the different start points *)
	     let targetEntry = chart.(start).(start + span) in
	       (*match targetEntry.seed with
		   Noconst -> ()
		 | _ ->
		     begin*) 
		       for split = 1 to span do                               (* Loop through the different split points *)
			 (*let _ =  Globals.dbgMsg "cyk" 10 
			   ("Current Iteration (span, start, split): (" ^ (string_of_int span) ^ "," ^ (string_of_int (start)) ^   "," ^(string_of_int (split)) ^ ")\n"
			   ^ "\tLeft: (" ^ (string_of_int (start)) ^ ","^ (string_of_int (start+(split-1))) ^ ")\n"
			   ^ "\tRight: (" ^ (string_of_int (start+split))^ "," ^ (string_of_int (start+(span))) ^ ")\n"
			   ^ "\tTarget: (" ^ (string_of_int (start)) ^ ","^ (string_of_int (start+(span))) ^ ")\n" ) in*)
			 let leftEntry =  chart.(start).(start+(split-1))
			 in let rightEntry = chart.(start+(split)).(start+span)
			 in begin
			     (*let startSecondLoop = Sys.time () in *)
			     (Hashtbl.iter                                           (* Loop through the left-split states *) 
				 (fun lstate lstateProb ->                       
				   (* let startInnerLoop = Sys.time () in *) 
				   begin   
				     (Hashtbl.iter                                         (* Loop through the right-split production equivalence classes *)
					 (fun rcompleted rcompletedProb ->
					   let newStateOption = G.nextState grammar lstate rcompleted  
					   in match newStateOption with
					       None -> ()
					     | Some newState ->
						 (* The probability of advancing further in our state sequence is just the last state 
						    prob times the current edge probability. *)
						 let lstateBestProb = 
						   if Hashtbl.mem  leftEntry.statesMAP lstate 
						   then Hashtbl.find leftEntry.statesMAP lstate
						   else failwith ("CYK.parse Cannot fine best score for the left state: " ^ (chartEntry2string grammar leftEntry) )
						 in let rcompleteBestProb =
						   if Hashtbl.mem  rightEntry.constituentMAP rcompleted 
						   then Hashtbl.find rightEntry.constituentMAP rcompleted
						   else failwith ("CYK.parse Cannot fine best score for the right constituent: " ^ (chartEntry2string grammar rightEntry) )
						 in let newStateBestProb = lstateBestProb +. rcompleteBestProb
						 in let newStateProb = lstateProb +. rcompletedProb
						 (*in let _ =    if newStateProb = newStateBestProb
						   then Globals.dbgMsg "cyk" 10 ( "\tState Prob: " ^ (string_of_float newStateProb) ^ "\n"
										  ^ "\tBest State Prob: " ^  (string_of_float newStateBestProb) ^ "\n") *)
						 in let traversal = {left = (lstate, start,  (start+(split-1)));
								     right = (rcompleted, start+(split), start+span);}
						 in begin
						     (addNewStateToEntry threshold grammar targetEntry newState traversal newStateProb newStateBestProb);
					             (* Globals.dbgMsg "cyk" 10 ( "\tLeft Entry: " ^ (chartEntry2string grammar leftEntry) ^ "\n"
							^ "\tRight Entry: " ^ (chartEntry2string grammar rightEntry) ^ "\n" 
							^ "\tTarget Entry: " ^ (chartEntry2string grammar targetEntry) ^ "\n" );*)
						   end) 
					 rightEntry.constituentInsides);
				     (* Globals.dbgMsg "cyk" 10 ( "CYK loop over right passive edges took: " ^ (string_of_float ((Sys.time ()) -. startInnerLoop)) ^ 
					" seconds. With "^ (string_of_int (Hashtbl.length rightEntry.constituentInsides)) ^ " completions to process.\n"); *)
				     
				   end)
				 leftEntry.statesInside);
			   
			 (* Globals.dbgMsg "cyk" 10 ( "CYK loop over left active and right passive edges time is (seconds): " ^ (string_of_float ((Sys.time ()) -. startSecondLoop)) ^ "\n"); *)
			   
			 end
		     done; (* End split iteration *)
	
		       (* This next call does "reverse prediction" -- that
			  is, given the completed constitutents in the
			  target entry it adds all those rules which can
			  start with those completed constitutents. It does
			  this recursively until there are no more rules to
			  add.*)
	               (* let startReversePrediction = Sys.time () in *)
	       begin
		 (*Globals.dbgMsg "cyk" 10 ( "Chart:\n" ^ (chart2string grammar chart) ^ "\n");*)
		 (addStartsToEntry threshold grammar targetEntry);		 
		 (computeExpectations grammar targetEntry chart);
		 
		 (*(unaryExpectations threshold grammar targetEntry);*)
		 

		 (* Globals.dbgMsg "cyk" 10 ( "Reverse prediction time is (seconds): " ^ (string_of_float ((Sys.time ()) -. startReversePrediction)) ^ "\n");*)
		 
	       end
	
	     
	   done; (* End start iteration *)
	   done; (* End span iteration *)
		     	       (* Globals.dbgMsg "cyk" 10 (  "Start Symbol: " ^ (G.constituentSymbol2string (G.getStartSymbol grammar)) ^ "\nChart:\n" ^ (chart2string grammar chart) ^ "\n"); *)

		     
		     (let last = Array.length chart
		       in let finalentry = chart.(0).(last-1)
		       (*in let _ = Globals.dbgMsg "cyk" 10 ("Final Entry:\n" ^ (chartEntry2string grammar finalentry) ^ "\n")*)
 		       in let result =
			 (try
			     let _ = Hashtbl.find finalentry.constituentInsides  (G.getStartSymbol grammar) in (); 
			       Success chart;
			   with Not_found ->  Failure chart);  
		       in result);
		     
			
			(*failwith ("Grammar does not parse sentence: "^  (Array.fold_left (fun  a v -> a ^ " " ^ (G.constituentSymbol2string v)  ) "" input));
			end); *)
		     
		     
      end
      
  (* Curry a parser for a particular grammar *)
  let makeparser grammar  =  parse grammar

   module ParseTree = Tree (
     struct
       type root = (G.state * G.constituentSymbol)
       type node = (G.state * G.constituentSymbol)
       type leaf = (G.constituentSymbol)
	   
       let root2string (s, c) = G.constituentSymbol2string c
       let node2string (s, c) = G.constituentSymbol2string c
       let leaf2string ( c) = G.constituentSymbol2string c
	 
       (* Equality testing on node types *)
       let rootEq r1 r2 = r1 = r2
       let nodeEq n1 n2 = n1 = n2
       let leafEq l1 l2 = l1 = l2 
     end)
     
   let sampleParse  grammar chart start finish constituent (input : G.constituentSymbol array)  =
    let sampleState constituent entry =                        (* Starting with a nonterminal, sample a rule *)
       let (states, probs, total) =  (Hashtbl.fold 
					(fun state prob (ss, ps, t) ->  
	   if (G.stateConstituent grammar state constituent) 
	   then let constProb = (G.stateConstituentProb grammar state constituent)
		in if (constProb > neg_infinity)
	       then (state :: ss, (prob +. constProb) :: ps, Utils.logsumexp [t;  (prob +. constProb)])
	       else (ss, ps, t)
	   else (ss, ps, t))
	 entry.statesInside ([], [], neg_infinity))
       (*in let _ = Globals.dbgMsg "cyk" 1 ("Sampling state from: " ^ (string_of_int (List.length states))^"\n")*)
	  in Utils.sampleDiscreteTotal states probs total
     in let sampleTraversal state entry =                             (* Starting with a state, sample the previous split point and recurse *) 
	 let traversalHash = 
	if Hashtbl.mem entry.traversalsInside state
	then Hashtbl.find entry.traversalsInside state
	else failwith 
	  ("Cyk.sampleParse.sampleStateBackptr: Cannot find a backpoint for state: " 
	   ^ (G.state2string grammar state) ^ " in entry: (" ^ (chartEntry2string grammar entry) ^ "\n")
      in let (traversals, travWeights, total) =  
	   (Hashtbl.fold 
	   (fun traversal logProb (ts, ws, t) 
	    ->  (traversal::ts, logProb::ws, Utils.logsumexp [t; logProb]))
	    traversalHash 
	    ([], [], neg_infinity)) 
	 in let tr = Utils.sampleDiscreteTotal traversals travWeights total
	 in begin
	(* Globals.dbgMsg "cyk" 10  ("\t\tSampled traversal: (" ^ (traversal2string grammar tr) ^ ")\n"); *)
	tr;
      end
       in let rec activeEdge2tree activeEdge =                      (* Unwind a state *)
	 match activeEdge with 
	  (state, _, _) when (G.rootState grammar state) -> []
	| (state, st, fin) ->  
	  (* let _ =  Globals.dbgMsg "cyk" 10 
		("\tSample active edge: (" ^ (string_of_int st) ^ "," ^ (string_of_int fin) ^   "," ^(G.state2string grammar state) ^ ")\n") in *)
	      let entry =  chart.(st).(fin) 
	    in let traversal = (sampleTraversal state entry)
	       (* in let _ =  Globals.dbgMsg "cyk" 10 
		  ("\tChose backpointer: (" ^ (traversal2string grammar traversal) ^ ")\n") *)
		in (List.append (activeEdge2tree traversal.left) [(passiveEdge2tree traversal.right)]) 
    and passiveEdge2tree passiveEdge =                              (* Unwind a completion from a situated nonterminal *)
	 match passiveEdge with
	    cl, st, fin   when (st = fin) && 
	       (input.(st) = cl || 
		   (G.matchConstituentSymbol input.(st) "<.>" && G.isTerminal grammar cl) ||
		   (G.matchConstituentSymbol input.(st) "<E.>" && G.isTerminal grammar cl) ||
		   (G.matchConstituentSymbol input.(st) "<+>" && not (G.isTerminal grammar cl)) || 
		   (G.matchConstituentSymbol input.(st) "<E+>" && not (G.isTerminal grammar cl)) ||
		   (G.matchConstituentSymbol input.(st) "<*>") || 
		   (G.matchConstituentSymbol input.(st) "<E*>"))  ->
	      (* let _ =  Globals.dbgMsg "cyk" 10 ("Terminal: " ^ (G.constituentSymbol2string cl)^"\n") 
	       in *)  ParseTree.Lf (cl) 
	  |  constituent, st, fin -> 
	    (*let _ =  Globals.dbgMsg "cyk" 10 
		  ("Sampling passive edge : (" ^ (string_of_int st) ^ "," ^ (string_of_int fin) ^   "," ^(G.constituentSymbol2string constituent) ^ ")\n")  in *)
		let entry =  chart.(st).(fin)
	      in let state = (sampleState constituent entry)
	         (* in let _ =  Globals.dbgMsg "cyk" 10 ("\t\twith state: " ^ (G.state2string grammar state) ^ "\n")*)
	      in let children = (activeEdge2tree (state, st, fin))
	      in ParseTree.Nd ((state, constituent) , children)
    in passiveEdge2tree (constituent, start, finish)
      
  let getMAPParseChart  grammar chart start finish constituent (input : G.constituentSymbol array)  =
(*    let _ = Globals.dbgMsg "cyk" 10 ( "Chart:\n" ^ (chart2string grammar chart) ^ "\n") in*)
     let getMAPState constituent entry =                        (* Starting with a nonterminal, sample a rule *)
      let (b, bpb) =  begin
	  (Hashtbl.fold 
	      (fun state prob (best, bestprob) ->  
		if (G.stateConstituent grammar state constituent) 
		then begin
		    let constProb = (G.stateConstituentProb grammar state constituent)
		    in if (constProb > neg_infinity)
		      then  let score = (prob +. constProb) in begin
			      (* Globals.dbgMsg "cyk" 10 ( "\t" ^ (G.state2string grammar state) ^ " " ^(string_of_float (prob +. constProb))  ^ " \n");
			      Globals.dbgMsg "cyk" 10 ( "\t\t with inside prob:" ^ (G.state2string grammar state) ^ " " ^(string_of_float prob)  ^ " \n");
			      Globals.dbgMsg "cyk" 10 ( "\t\t with grammar prob:" ^ (G.state2string grammar state) ^ " " ^(string_of_float constProb)  ^ " \n");*)
			  if (score > bestprob)
			  then begin
			      (*Globals.dbgMsg "cyk" 10 ( "\t\tIMPROVED" ^ (G.state2string grammar state) ^ " " ^(string_of_float (prob +. constProb))  ^ " \n");
			      Globals.dbgMsg "cyk" 10 ( "\t\t\t with inside prob:" ^ (G.state2string grammar state) ^ " " ^(string_of_float prob)  ^ " \n");
			      Globals.dbgMsg "cyk" 10 ( "\t\t\t with grammar prob:" ^ (G.state2string grammar state) ^ " " ^(string_of_float constProb)  ^ " \n");*)
			      (Some state, score)
			    end
			  else (best, bestprob);
			end
		      else (best, bestprob);
		  end
		else (best, bestprob))
	      entry.statesMAP (None, neg_infinity))
	end
      in match b with 
	  Some x -> x
	| None -> begin
	      Globals.dbgMsg "cyk" 10 ("Sentence: " ^ (Array.fold_left (fun  a v -> a ^ " " ^ (G.constituentSymbol2string v)  ) "" input));
	      Globals.dbgMsg "cyk" 10 ( "Chart:\n" ^ (chartEntry2string grammar entry)^ "\n");
	      failwith ("Cyk.getMAPParseChart.getMAPState: Did not find a best state for: in entry: (" ^ (chartEntry2string grammar entry) ^ "\n");
	  end
     in let getMAPTraversal state entry =                             (* Starting with a state, sample the previous split point and recurse *) 
       let traversalHash = if Hashtbl.mem entry.traversalsMAP state
	 then Hashtbl.find entry.traversalsMAP state
	 else failwith 
	   ("Cyk.getMAPParseChart.getMAPTraversal: Cannot find a traversal for state: " 
	     ^ (G.state2string grammar state) ^ " in entry: (" ^ (chartEntry2string grammar entry) ^ "\n")
       in let (b, bpb) =  (Hashtbl.fold 
			      (fun traversal logProb (best, bestprob) ->
				if logProb > bestprob
				then (Some traversal, logProb)
				else (best, bestprob))
			      traversalHash 
			      (None, neg_infinity))
       in match b with
	   Some x -> x
	 | None -> failwith ("Cyk.getMAPParse.getMAPTraversal: Cannot find a best traversal: in entry: (" ^ (chartEntry2string grammar entry) ^ "\n")
     in let rec activeEdge2tree activeEdge =                      (* Unwind a state *)
       match activeEdge with 
	   (state, _, _) when (G.rootState grammar state) -> []
	 | (state, st, fin) ->  
	     (* let _ =  Globals.dbgMsg "cyk" 10 
	       ("\tFound MAP active edge: (" ^ (string_of_int st) ^ "," ^ (string_of_int fin) ^   "," ^(G.state2string grammar state) ^ ")\n") in *)
	     let entry =  chart.(st).(fin) 
	     in let traversal = (getMAPTraversal state entry)
	     (* in let _ =  Globals.dbgMsg "cyk" 10 
	       ("\tFound MAP traversal: (" ^ (traversal2string grammar traversal) ^ ")\n") *)
	     in (List.append (activeEdge2tree traversal.left) [(passiveEdge2tree traversal.right)]) 
     and passiveEdge2tree passiveEdge =                              (* Unwind a completion from a situated nonterminal *)
       match passiveEdge with
	   cl, st, fin   
	     when (st = fin) && 
	       (input.(st) = cl || 
		   (G.matchConstituentSymbol input.(st) "<.>" && G.isTerminal grammar cl) || 
		   (G.matchConstituentSymbol input.(st) "<E.>" && G.isTerminal grammar cl)) ->
	     (*let _ =  Globals.dbgMsg "cyk" 10 ("MAP Terminal: " ^ (G.constituentSymbol2string cl)^"\n") 
	     in *) ParseTree.Lf (cl) 
	 |  constituent, st, fin -> 
	      (*let _ =  Globals.dbgMsg "cyk" 10 
		("Finding MAP passive edge : (" ^ (string_of_int st) ^ "," ^ (string_of_int fin) ^   "," ^(G.constituentSymbol2string constituent) ^ ")\n")  in*)
	      let entry =  chart.(st).(fin)
	      in let state = (getMAPState constituent entry)
	      (*in let _ =  Globals.dbgMsg "cyk" 10 ("\t\twith state: " ^ (G.state2string grammar state) ^ "\n")*)
	      in let children = (activeEdge2tree (state, st, fin))
	      in ParseTree.Nd ((state, constituent) , children)
     in passiveEdge2tree (constituent, start, finish)
       
  let sampleTree grammar chart startsymbol =
    let n = Array.length chart
    in (sampleParse grammar chart 0 (n-1) startsymbol)

   let getInsideProbability  chart start stop symbol =
     let entry = chart.(start).(stop) in
       Hashtbl.find entry.constituentInsides symbol
	 
   let scoreSentence grammar tree sentence  = 
     let ch = parse grammar tree neg_infinity sentence 
     in match ch with
	 Success chart -> 
	   (*in let _ = Globals.dbgMsg "cyk" 10 ("Sentence: "  ^ (Array.fold_left (fun  a v -> a ^ " " ^ (G.constituentSymbol2string v)  ) "" sentence) ^ "\n")
	     in let _ = Globals.dbgMsg "cyk" 10 ( "Chart:\n" ^ (chart2string grammar chart) ^ "\n")*)
	   let n = Array.length chart
	   in let prob = getInsideProbability chart 0 (n-1) (G.getStartSymbol grammar) 
	   in prob
       | Failure chart ->
	   begin
	     Globals.dbgMsg "cyk" 10 ( "Cyk.scoreSentence failure with Chart:\n" ^ (chart2string grammar chart) ^ "\n");
	     failwith ("Cyk.scoreSentence: Grammar does not parse sentence: "^  (Array.fold_left (fun  a v -> a ^ " " ^ (G.constituentSymbol2string v)  ) "" sentence));
	   end

   let scoreSentenceFromChart grammar sentence chart = 
     let n = Array.length chart
     in getInsideProbability chart 0 (n-1) (G.getStartSymbol grammar)
       
   let getMAPParse grammar tree sentence  = 
     let ch = parse grammar tree neg_infinity sentence 
     in match ch with
	 Success chart ->
	   let n = Array.length chart
	   in (getMAPParseChart grammar chart 0 (n-1) (G.getStartSymbol grammar) sentence)
       | Failure chart ->
	   begin
	     Globals.dbgMsg "cyk" 10 ( "Cyk.getMAPParse failure with Chart:\n" ^ (chart2string grammar chart) ^ "\n");
	     failwith ("cyk.getMAPParse: Grammar does not parse sentence: "^  (Array.fold_left (fun  a v -> a ^ " " ^ (G.constituentSymbol2string v)  ) "" sentence));
	   end	   
	   
   let getMAPParseFromChart grammar sentence chart = 
     let n = Array.length chart
     in (getMAPParseChart grammar chart 0 (n-1) (G.getStartSymbol grammar) sentence)

   let getMAPProbability  chart start stop symbol =
     let entry = chart.(start).(stop) in
       Hashtbl.find entry.constituentMAP symbol

   let getMAPScoreFromChart grammar sentence chart =
     let n =  Array.length chart
     in getMAPProbability chart 0 (n-1) (G.getStartSymbol grammar)

   let getNTExpectationsFromChartEntry chart start finish symbol =
     let entry = chart.(start).(finish)
     in if Hashtbl.mem entry.constituentExpectations symbol
       then Hashtbl.find entry.constituentExpectations symbol
       else failwith "Cyk.getNTExpectationsFromChartEntry: unable to find expectations!"

   let getExpectationsFromChart grammar chart = 
     let n = Array.length chart
     in (getNTExpectationsFromChartEntry chart 0 (n-1) (G.getStartSymbol grammar))
      
   let numEdges chart =
     let n = Array.length chart in
     let total = ref 0 in
     let list = ref [] in
       begin 
	 for position = 0 to (n-1) do
	   total := !total + (Hashtbl.length chart.(position).(position).constituentInsides);
	   list :=  (Hashtbl.fold 
			(fun k v a -> 
			  ("[(" ^ (string_of_int (position)) ^ ", " ^ (G.constituentSymbol2string k) ^ ", " ^ (string_of_int (position+1)) ^ ") " ^ (string_of_float (exp v)) ^ "]")
			  :: a ) 
			chart.(position).(position).constituentInsides 
			[])   @ !list;
	 done;

	 for span = 1 to (n-1) do                    
	   for start = 0 to (n-1) - span  do
	     total := !total + (Hashtbl.length chart.(start).(start+span).constituentInsides);
	     list :=  (Hashtbl.fold 
			  (fun k v a -> 
			    ("[(" ^ (string_of_int (start)) ^ ", " ^ 
				(G.constituentSymbol2string k) ^ ", " ^ 
				(string_of_int (start+span+1)) ^ ") " ^ 
				(string_of_float (exp v)) ^ "]")
			    :: a ) 
			  chart.(start).(start+span).constituentInsides 
			  [])   @ !list; 
	   done;
       done;
       (!total, (List.rev !list));
       end 

  (*****************************************************************
   *                    DEBUGGING FUNCTIONS                        *
   *****************************************************************)
  let parseTree2String  ptree = 
    let rec nodeList2String l = match l with
	[] -> ""
      |  hd::tl -> (node2string hd) ^ " " ^ (nodeList2String tl)
    and node2string n = match n with
	ParseTree.Rt ((state, constituent), c) -> "(" ^  (G.constituentSymbol2string constituent) ^ " " ^ (nodeList2String [c]) ^ ")"
      | ParseTree.Lf (constituent) -> (G.constituentSymbol2string constituent) 
      | ParseTree.Nd ((state, constituent) , l) -> "(" ^  (G.constituentSymbol2string constituent) ^ " " ^ (nodeList2String l) ^ ")" 
    in (node2string  ptree)
 end
