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

module type Grammar = 
sig
  type grammar
  type state                     (* This represents a state in the Grammar's FSM *)
  type constituentSymbol         (* This represents an equivalence class of productions from the point that always lead to the same state transition *) 
  type parseTree = Nd of constituentSymbol * parseTree list | Lf of constituentSymbol

  val getRootState : grammar  -> state
  val stateConstituentProb : grammar -> state -> constituentSymbol -> float
  val stateConstituent : grammar -> state -> constituentSymbol -> bool
  val getStateConstituents : grammar -> state -> constituentSymbol list
  val nextState : grammar -> state -> constituentSymbol ->  state option
  val constituentSymbol2string : constituentSymbol -> string
  val state2string : grammar -> state -> string
  val rootState : grammar -> state -> bool                      
  val getStartSymbol : grammar -> constituentSymbol
end

module CYKParser (G : Grammar) =
struct   

  (* An active edge is an edge corresponding to a grammar state -- 
     an partially discovered rule *)
  type activeEdge = G.state * int * int

  (* A passive edge is an edge corresponding to a complete constituent *)
  type passiveEdge = G.constituentSymbol * int * int
      
  type edge = Active of activeEdge | Passive of passiveEdge


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
       states :  (G.state, float) Hashtbl.t;                   (* The accumulated inside probability of various state sequences *)
       traversals : (G.state, (traversal, float) Hashtbl.t) Hashtbl.t;
       constituentProbs :  (G.constituentSymbol, float) Hashtbl.t;
       mutable seed : G.constituentSymbol option}

  let activeEdge2string  grammar ss = match ss with
      state, s, e -> ((G.state2string grammar state) ^ " (" ^ (string_of_int s) ^ " , " ^ (string_of_int e) ^ ")")

  let passiveEdge2string sc  = match sc with
      c, s, e-> ((G.constituentSymbol2string c) ^ " (" ^ (string_of_int s) ^ " , " ^ (string_of_int e) ^ ")")

  let  traversal2string grammar bp =
    "[Left: " ^ (activeEdge2string grammar bp.left) ^ " | " 
    ^ "Right: " ^ (passiveEdge2string bp.right) ^ " | "  ^ "]"  

let chartEntry2string grammar entry =
  "Entry: (" ^ (string_of_int entry.start) ^ " , " ^ (string_of_int entry.finish) ^ ")"
  ^ "\n\t\tStates: " 
  ^ (Hashtbl.fold 
	(fun state inside accum -> 
	 "\n\t\t\t(" ^ (G.state2string grammar state) 
	  ^ " : " 
	  ^ (string_of_float (exp inside)) ^ ") " 
	  ^ accum ) 
	entry.states 
	"") 
   ^ "\n\t\tTraversals: "
  ^ (Hashtbl.fold 
	(fun state traversals accum -> 
	  " \n\t\t\t(" ^ (G.state2string  grammar state)
	  ^ " : " 
	  ^ (Hashtbl.fold 
		(fun k v a ->  a ^ "\n\t\t\t\t" ^ (traversal2string grammar k) ^ " : " ^ (string_of_float (exp v)))  
		traversals
		"") ^ ") "
	  ^ accum) 
	entry.traversals 
	"")
  ^ "\n\tConstituent Probs: "
  ^ (Hashtbl.fold 
	(fun eqvC inside accum -> 
	  "(" ^ (G.constituentSymbol2string  eqvC)
	  ^ " : " 
	  ^ (string_of_float (exp inside))  ^ ") "
	  ^ accum) 
	entry.constituentProbs
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
  let createChartEntry grammar s f =
    {start=s;
     finish=f;
     states = Hashtbl.create 200;
     traversals = Hashtbl.create 200;
     constituentProbs = Hashtbl.create 75;
     seed=None;}

  (* Update a state list with a new state *)
  let updateState grammar entry state traversal logProb =
    begin
      (if Hashtbl.mem entry.states state
	then let oldStateSeqProb = Hashtbl.find entry.states state
	  in begin 
	     (*  Globals.dbgMsg "cyk" 10 ("Found redundant path through chart to production. \n"); *)
	     Hashtbl.replace entry.states state (Utils.logsumexp [oldStateSeqProb; logProb]);
	    end
	else begin 
	    (* Globals.dbgMsg "cyk" 10 ("Adding state: "^ (G.state2string grammar  state) ^ "to entry (" ^ (string_of_int entry.start) ^ " , " ^ (string_of_int entry.finish) ^ ")\n");*)
	    Hashtbl.add entry.states state  logProb;
	  end);

      (if Hashtbl.mem entry.traversals state
	then let traversals = Hashtbl.find entry.traversals state
	  in if Hashtbl.mem traversals traversal
	    then let oldTraversalProb = Hashtbl.find traversals traversal
	      in Hashtbl.replace traversals traversal (Utils.logsumexp [oldTraversalProb; logProb])
	    else Hashtbl.add traversals traversal logProb
	else let traversals = Hashtbl.create 20
	  in let _ = Hashtbl.add traversals traversal logProb
	  in Hashtbl.add entry.traversals state traversals)
    end

  (* If we have successfully completed then go ahead and update based on this:
     entry: a chart entry
     production: a rule that can be completed in this entry
     newStateSeqProb: the product of the inside probabilities of the constituents which match the rule's RHS *)
  let rec updatePassiveEdge grammar entry state constituent traversal logProb =
    let oldCompletionProb = 
      if Hashtbl.mem entry.constituentProbs constituent (* get the sum inside prob of this LHS *) 
      then Hashtbl.find entry.constituentProbs constituent
      else neg_infinity
    (* This is the inside probability of the current production (rule) *) 
    in let newProductionProb = (logProb +. (G.stateConstituentProb grammar state constituent) ) in 
      begin 
	(* Globals.dbgMsg "cyk" 10 ("Updating passive edge 2: \n" 
				  (* ^ (chartEntry2string entry) ^ " "*)
	                          ^ "\tConstituent: "^ (G.constituentSymbol2string constituent) ^ "\n"); *)

	(* Update the total probabilty of this completion *)
	(Hashtbl.replace entry.constituentProbs constituent (Utils.logsumexp [oldCompletionProb; newProductionProb]));
      end
      
  (* Add a new state transition to the chart *)
  let addNewStateToEntry grammar entry newState  traversal logProb =
    (* Globals.dbgMsg "cyk" 10 ("Adding new state to entry. \n"); *)
    let constituents = G.getStateConstituents grammar newState        (* Get the set of productions associated with this state *)
    in begin
	(* Add the new state to the set of states *)
	(updateState grammar entry newState  traversal logProb);
	
	(* If this has led to any completions then update the sums.*)
	(List.iter
	    (fun constituent -> 
	      match entry.seed with
		  None -> ()
		| Some seed -> 
		    if constituent = seed
		    then  (updatePassiveEdge grammar entry newState constituent  traversal logProb)
		    else ())
	    constituents);
      end

  (* Do "reverse prediction" -- semi-naive bottom-up evaluation to
     handle unaries approximately correctly. *)
  let addStartsToEntry grammar entry  =
    (* let _ =   Globals.dbgMsg "cyk" 10 ("Adding Starts: \n" 
					^ "\tEntry: " ^ (chartEntry2string grammar entry) ^ " "
					^ "\tCompleted: "^ (G.constituentSymbol2string completion) ^ "\n") in *)
    let root = G.getRootState grammar in
    let unarytolerance  = (log 1.0000000000001) in 
    let rec processNextStep childScores =  
      if (Hashtbl.length childScores = 0) 
      then ()
      else(*let _ =   Globals.dbgMsg "cyk" 10 ("Adding Starts:" ^
						 (Hashtbl.fold (fun k v a -> a ^ "Child: " ^ (G.constituentSymbol2string k) ^ " : " ^ (string_of_float v) ) childScores "") ^ "\n") in *)
	     (let parentScores = Hashtbl.create 25
	       in let _ = (Hashtbl.iter    
			      (fun child childInside ->
				let newStateOption = G.nextState grammar root child  
				in match newStateOption with
				    None -> ()
				  | Some newState ->
				      let traversal = {left = (root, entry.start,  entry.finish);
						       right = (child, entry.start, entry.finish);}
				      in let  _  = (updateState grammar entry newState  traversal childInside)
				      in let parents = G.getStateConstituents grammar newState        
				      in (List.iter
					     (fun parent -> 
					       let oldParentInside = if Hashtbl.mem parentScores parent
						 then Hashtbl.find parentScores parent
						 else neg_infinity
					       in let newInsideIncrement = (childInside +. (G.stateConstituentProb grammar newState parent) )
					       in let newParentInside =  (Utils.logsumexp [oldParentInside; newInsideIncrement])		
					       in (Hashtbl.replace parentScores parent newParentInside))
					     parents))
			      childScores)
	       in let newParentScores = Hashtbl.create 25
	       in let _ = (Hashtbl.iter 
			      (fun constituent chainInside  ->
				let oldChartInside =                          
				  if Hashtbl.mem entry.constituentProbs constituent  
				  then Hashtbl.find entry.constituentProbs constituent
				  else neg_infinity 
				(* in let oldStates =  
				  if Hashtbl.mem entry.constituent2state constituent (* get the sum inside prob of this LHS *) 
				  then Hashtbl.find entry.constituent2state constituent
				  else [] *) 
				in let newChartInside = (Utils.logsumexp [oldChartInside; chainInside])
				in let changeRatio =  newChartInside -. oldChartInside
				in let _ = Hashtbl.replace entry.constituentProbs constituent newChartInside in
				     if changeRatio > unarytolerance
				     then  Hashtbl.add newParentScores constituent chainInside
				     else ())
			      parentScores)
	       in (processNextStep newParentScores))
    in (processNextStep entry.constituentProbs) 

  (* Find the spans of a tree. *)
  let tree2spans proc tree = 
    let rec processChildren (length : int ) (start : int) (children : G.parseTree list)  = match children with
	[] -> length (* Return the total length of these children *)
      | hd :: tl -> let  childLength = (processNode (start+length) hd)
	in processChildren (length+childLength) start tl 
    and  processNode (start : int) (t : G.parseTree) = match t with
	G.Nd (l, ch) -> let length = processChildren 0 start ch
	  in let _ = proc start l (start+length)
	  in length
      | G.Lf (l) -> let _ = proc start l (start + 1) in 1
    in processNode 0 tree

  (* Set the spans of a chart *)
  let setSpans chart start label finish =
    let entry = chart.(start).(finish-1)
    in entry.seed <- Some label
   
  (* Parse the sentence bottom up. *)
  let parse (grammar : G.grammar)  (input : G.constituentSymbol array) tree =
    (* let _ = Globals.dbgMsg "cyk" 10 ("Parsing string: " ^ (Array.fold_left (fun  a v -> (G.constituentSymbol2string v) ^" "^ a ) "" input) ^ "\n") in *)
    let n = (Array.length input) 
    in let (chart : chartEntry array array ) =
      (let init_row = (fun s -> Array.init n (createChartEntry grammar s))
	in Array.init n init_row)
    in let _ = tree2spans (setSpans chart) tree
    in begin
	
	 (* Initialize the chart *)
	 for position = 0 to (n-1) do
	   (* let _ =  Globals.dbgMsg "cyk" 10 ("Initializing word: " ^ (string_of_int position) ^ "\n") in *)
	   let target = chart.(position).(position)
	   in let word = input.(position)
	   (* in let wordProduction = (G.getTerminalProduction grammar word) *)
	   in let root = G.getRootState grammar 
	   in let traversal = {left = (root, target.start,  target.finish);
			       right = (word, target.start, target.finish);}
	   in let _ = (updatePassiveEdge grammar target root word traversal 0.0)
	   in  (addStartsToEntry grammar target)
	     (* Globals.dbgMsg "cyk" 10 ("Initilialized Entry: " ^ (chartEntry2string grammar target) ^ "\n");end *)
	 done;


	 (* main loop *)
	 for span = 1 to (n-1) do                                        (* Loop through the different span sizes *)
	   for start = 0 to (n-1) - span  do                             (* loop through the different start points *)
	     let targetEntry = chart.(start).(start + span) in
	       for split = 1 to span do                               (* Loop through the different split points *)
	         (* let _ =  Globals.dbgMsg "cyk" 10 
		   ("Current Iteration (span, start, split): (" ^ (string_of_int span) ^ "," ^ (string_of_int (start)) ^   "," ^(string_of_int (split)) ^ ")\n"
		     ^ "\tLeft: (" ^ (string_of_int (start)) ^ ","^ (string_of_int (start+(split-1))) ^ ")\n"
		     ^ "\tRight: (" ^ (string_of_int (start+split))^ "," ^ (string_of_int (start+(span))) ^ ")\n"
		     ^ "\tTarget: (" ^ (string_of_int (start)) ^ ","^ (string_of_int (start+(span))) ^ ")\n" ) in *)
		 let leftEntry =  chart.(start).(start+(split-1))
		 in let rightEntry = chart.(start+(split)).(start+span)
		 in begin
		     (* let startSecondLoop = Sys.time () in *)
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
					     let newStateProb = lstateProb +. rcompletedProb   
					     in let traversal = {left = (lstate, start,  (start+(split-1)));
								   right = (rcompleted, start+(split), start+span);}
					     in begin
						 (addNewStateToEntry grammar targetEntry newState traversal newStateProb);
					         (* Globals.dbgMsg "cyk" 10 ( "\tLeft Entry: " ^ (chartEntry2string grammar leftEntry) ^ "\n"
									   ^ "\tRight Entry: " ^ (chartEntry2string grammar rightEntry) ^ "\n" 
									   ^ "\tTarget Entry: " ^ (chartEntry2string grammar targetEntry) ^ "\n" );*)
					       end) 
				     rightEntry.constituentProbs);
				 (* Globals.dbgMsg "cyk" 10 ( "CYK loop over right passive edges took: " ^ (string_of_float ((Sys.time ()) -. startInnerLoop)) ^ 
				    " seconds. With "^ (string_of_int (Hashtbl.length rightEntry.constituentProbs)) ^ " completions to process.\n"); *)

			       end)
			   leftEntry.states);
		       
		   (* Globals.dbgMsg "cyk" 10 ( "CYK loop over left active and right passive edges time is (seconds): " ^ (string_of_float ((Sys.time ()) -. startSecondLoop)) ^ "\n"); *)

		   end
	       done; (* End split iteration *)
	       (* This next call does "reverse prediction" -- that
		  is, given the completed constitutents in the
		  target entry it adds all those rules which can
		  start with those completed constitutents. It does
		  this recursively until there are no more rules to
		  add.*)
	       (* let startReversePrediction = Sys.time () in*)
		 begin
		   (addStartsToEntry grammar targetEntry);
		    (* Globals.dbgMsg "cyk" 10 ( "Reverse prediction time is (seconds): " ^ (string_of_float ((Sys.time ()) -. startReversePrediction)) ^ "\n");*) 
		 end
	       done; (* End start iteration *)
	       done; (* End span iteration *)
		    (* Globals.dbgMsg "cyk" 10 ( "Chart:\n" ^ (chart2string grammar chart) ^ "\n"); *)
		 chart;
       end
       
   (* Curry a parser for a particular grammar *)
   let makeparser grammar =   parse grammar 

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
	 entry.states ([], [], neg_infinity))
       (* in let _ = Globals.dbgMsg "cyk" 1 ("Sampling state from: " ^ (string_of_int (List.length states))^"\n") *)
      in Utils.sampleDiscreteTotal states probs total
    in let sampleTraversal state entry =                             (* Starting with a state, sample the previous split point and recurse *) 
      let traversalHash = if Hashtbl.mem entry.traversals state
	then Hashtbl.find entry.traversals state
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
	      ("\tChose backpointer: (" ^ (traversal2string grammar stBackPtr) ^ ")\n") *) 
	    in (List.append (activeEdge2tree traversal.left) [(passiveEdge2tree traversal.right)]) 
    and passiveEdge2tree passiveEdge =                              (* Unwind a completion from a situated nonterminal *)
	match passiveEdge with
	    cl, st, fin   when (st = fin) && input.(st) = cl ->
	      (* let _ =  Globals.dbgMsg "cyk" 10 ("Terminal: " ^ (G.constituentSymbol2string cl)^"\n") 
	      in *) ParseTree.Lf (cl) 
	  |  constituent, st, fin -> 
	        (* let _ =  Globals.dbgMsg "cyk" 10 
		("Sampling passive edge : (" ^ (string_of_int st) ^ "," ^ (string_of_int fin) ^   "," ^(G.constituentSymbol2string constituent) ^ ")\n")  in *)
	      let entry =  chart.(st).(fin)
	      in let state = (sampleState constituent entry)
	         (*in let _ =  Globals.dbgMsg "cyk" 10 ("\t\twith state: " ^ (G.state2string grammar state) ^ "\n") *)
	      in let children = (activeEdge2tree (state, st, fin))
	      in ParseTree.Nd ((state, constituent) , children)
    in passiveEdge2tree (constituent, start, finish)

  let sampleTree grammar chart startsymbol =
    let n = Array.length chart
    in (sampleParse grammar chart 0 (n-1) startsymbol)


   let getInsideProbability chart start stop symbol =
     let entry = chart.(start).(stop) in
       Hashtbl.find entry.constituentProbs symbol

   let numEdges chart =
     let n = Array.length chart in
     let total = ref 0 in
     let list = ref [] in
       begin 

	 for position = 0 to (n-1) do
	   total := !total + (Hashtbl.length chart.(position).(position).constituentProbs);
	   list :=  (Hashtbl.fold 
			(fun k v a -> 
			  ("[(" ^ (string_of_int (position)) ^ ", " ^ (G.constituentSymbol2string k) ^ ", " ^ (string_of_int (position+1)) ^ ") " ^ (string_of_float (exp v)) ^ "]")
			  :: a ) 
			chart.(position).(position).constituentProbs 
			[])   @ !list;
	 done;

	 for span = 1 to (n-1) do                    
	   for start = 0 to (n-1) - span  do
	     total := !total + (Hashtbl.length chart.(start).(start+span).constituentProbs);
	     list :=  (Hashtbl.fold 
			  (fun k v a -> 
			    ("[(" ^ (string_of_int (start)) ^ ", " ^ 
				(G.constituentSymbol2string k) ^ ", " ^ 
				(string_of_int (start+span+1)) ^ ") " ^ 
				(string_of_float (exp v)) ^ "]")
			    :: a ) 
			  chart.(start).(start+span).constituentProbs 
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
	ParseTree.Rt ((state, constituent), c) -> "[" ^  (G.constituentSymbol2string constituent) ^ " " ^ (nodeList2String [c]) ^ "  ]"
      | ParseTree.Lf (constituent) -> (G.constituentSymbol2string constituent) 
      | ParseTree.Nd ((state, constituent) , l) -> "[" ^  (G.constituentSymbol2string constituent) ^ " " ^ (nodeList2String l) ^ "  ]" 
    in (node2string  ptree)
 end
