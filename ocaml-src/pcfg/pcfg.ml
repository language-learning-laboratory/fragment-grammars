(***********************************************************************************
 ***********************************************************************************
 *                              Module: FragmentGrammar                            * 
 * --------------------------------------------------------------------------------*
 *            This module implements a partial fragment grammar (PFG)              * 
 ***********************************************************************************)    
open Utils
open Id

  
(* ---------------------------------------------------------------------*
 *              Data types for the alphabet of this grammar:            *
 *       A terminal is just a string, a nonterminal needs a unique ID   *          
 *                                                                      *
 * ---------------------------------------------------------------------*)
type nonterminal = {nName : string}  (* String name of this non-terminal *)
type terminal = {tName : string}
    
(* A symbol is a union of terminals and non terminals *)
type symbol = N of nonterminal | T of terminal
  
(* Generate table IDs *)
module ProductionID = ID(struct end)
module StateID = ID(struct end) 

let main_multiplier = (-0.0000001)
let wug_multiplier = (-36.7368)
  
type production = {
    pid : int64;
    head : symbol;
    rhs : symbol list;
    mutable logprob : float;}
and parseTree = Nd of symbol * parseTree list | Lf of symbol
  
type grammarTrie =
    {stateId : int64;
     value : symbol;
     productions : (symbol, production ref) Hashtbl.t;
     next : (symbol, grammarTrie) Hashtbl.t}
      
type grammar =
    {nts : (nonterminal, production ref list) Hashtbl.t;
     ts : (terminal, int) Hashtbl.t;
     id2trie : (int64, grammarTrie ref) Hashtbl.t;   (* trie state id to trie node, for random access *)
     mutable trie : grammarTrie;
     mutable trieSize : int;
     wugs : (symbol list, production ref) Hashtbl.t;
     start : symbol;}
      
(* Parser Expectations *)
type stateExpectations =
    {sNumParses : float;
     sEntropy : float;
     sSurprisal : float;
     sKL : float;
     sNumConstituents : float;
     sBoundaries : float array;}
      
type constExpectations =
    {cNumParses : float;
     cEntropy : float;
     cSurprisal : float;
     cKL : float;
     cNumConstituents : float;
     cBoundaries : float array;}
      
let getTerminals grammar =
  Hashtbl.fold (fun k v a -> (T k)::a) grammar.ts []
    
let getNonterminals grammar =
  Hashtbl.fold (fun k v a -> (N k)::a) grammar.nts []
    
let getSymbols grammar =
  List.append (getTerminals grammar) (getNonterminals grammar)
    
let matchSymbol symbol string = match symbol with
    N n -> n.nName = string
  | T t -> t.tName =string
  
let symbol2string s =
  match s with
      T (t) -> (t.tName) (*^" [T]"*)
    | N (n) -> (n.nName) (*^" [N]"*)
	
(* Get the RHS of this production *)
(* IMPLEMENTS GRAMMAR INTERFACE *)
let getRHS p = p.rhs
  
(*Get the head of a production*)
let head p = p.head
  
(*get the expected probability of a production *)
(* IMPLEMENTS GRAMMAR INTERFACE *)
let prodLogprob  p = !p.logprob
  
  
(* Print NT's *)
let nts2string g =
  Hashtbl.fold (fun k v a -> k.nName^a) g.nts ""
    
(* Nonterminals *)
(* IMPLEMENTS GRAMMAR INTERFACE *)
let nt2string nt = nt.nName
  
(* Terminals *)
(* IMPLEMENTS GRAMMAR INTERFACE *)
let t2string t = t.tName
  
  
(* IMPLEMENTS GRAMMAR INTERFACE *)
let prod2string p = 
  let rhs2string r = match r with
      T t -> t.tName
    | N nt  -> nt.nName
  in     begin 
      (* Globals.dbgMsg "fg" 10 ("Converting production to string.\n"); *)
      "{"^(Int64.to_string p.pid) ^": "^ (symbol2string (head p)) ^ " --> " ^ List.fold_left (fun a v -> a ^ " " ^ (rhs2string v) ) "" (getRHS p) ^ "}";
    end

(* IMPLEMENTS CYK *)
let prod2string_ref p = 
  prod2string !p

    
let parseTree2string p =
  let rec processNode n = match n with
      Lf s -> (symbol2string s) 
    | Nd (s, ch) -> "(" ^ (symbol2string s)  
	^ " " ^ (List.fold_left (fun a e -> a ^ " " ^ (processNode e)) "" ch) ^ ")"
  in  match p with
      Lf s -> (symbol2string s) 
    | Nd (s, ch) ->  "(" ^ (symbol2string s)  
	^ " " ^ (List.fold_left (fun a e -> a ^ " " ^ (processNode e)) "" ch) ^ ")"

	  

(* Compare two RHSs for sorting. *)
let rec rhsCompare rhs1 rhs2 = match (rhs1, rhs2) with
    ([], []) -> 0
  | ([], x) -> (-1)
  | (x, []) -> (1)
  | (hd1::tl1, hd2::tl2) -> 
      let cmp = (compare hd1 hd2)
      in if cmp = 0 
	then rhsCompare tl1 tl2 
	else cmp

	  
let rec trie2prettyString padding trie =
  let children =  (Hashtbl.fold (fun k v a -> a ^ (trie2prettyString (padding ^ "      ")  v) ^ " ") trie.next  "" ) 
  in if (children = "")
    then  "\n" ^  padding ^  "(" ^ (Int64.to_string trie.stateId)^ "; " ^ (symbol2string trie.value) ^ 
      (* " [" ^ (List.fold_left (fun a v -> a ^ " " ^ (symbol2string v)) "" trie.constituents) ^ "]" ^ *)
      " [" ^ (Hashtbl.fold 
		 (fun k v a -> a ^ " " ^ (symbol2string k) ^ ":" ^  (Int64.to_string !v.pid))
		 trie.productions "" ) ^ "]" ^ ")" 
    else "\n" ^ padding ^ "(" ^ (Int64.to_string trie.stateId)^ "; "^ (symbol2string trie.value)  ^
      " [" ^ (Hashtbl.fold 
		 (fun k v a -> a ^ " " ^ (symbol2string k) ^ ":" ^  (Int64.to_string !v.pid))
		 trie.productions "" ) ^ "]" 
      ^ children ^ ")"

let rec trie2string trie =
  trie2prettyString "" trie


let  trie2string_small trie =
  "(" ^ (Int64.to_string trie.stateId)^ "; " ^ (symbol2string trie.value) ^ 	" [" ^ (Hashtbl.fold (fun k v a -> a ^ " " ^ (symbol2string k)^":"^(Int64.to_string !v.pid)^":"^(string_of_float (prodLogprob v)))  trie.productions "") ^ "]) "

let trieId2string_small grammar trieId =
  if Hashtbl.mem grammar.id2trie trieId
  then let trie = Hashtbl.find grammar.id2trie trieId
    in trie2string_small !trie
  else failwith ("FragmentGrammar.trieId2string_small: unable to find trie with value: " ^ (Int64.to_string trieId))

(* Get a string representation of a whole grammar *)
let grammar2string g =
  let string = Hashtbl.fold 
    (fun k v a -> ( List.fold_left (fun a1 v1 -> a1 ^ (prod2string !v1) ^ "\n") "" v) ^ a ) g.nts "" in
    begin
      (* Globals.dbgMsg "fg" 8 ("String form of grammar computer in " 
	 ^ (string_of_float (tm2-.tm1)) 
	 ^ " seconds.\n"); *)
      string
    end

(* Get a string representation of a whole grammar *)
let writeGrammar ch g =
  let keys =  (Hashtbl.fold (fun k _ a -> k :: a) g.nts [] )
  in let nts = (List.sort compare keys)
  in let _ = (List.iter 
		 (fun v -> 
		   (List.iter (fun v1 ->   
		     begin 
		       (output_string ch ((prod2string !v1) ^ "\n")); 
		       flush ch; 
		     end)
		       (Hashtbl.find g.nts v)))
		 nts) 
  in let _ = (output_string ch "TRIE:\n")
  in let _  =  (output_string ch ((trie2prettyString "" g.trie) ^ "\n\n")); flush ch;
  in let _ = (output_string ch "TRIE ID 2 TRIE:\n")
  in let _ =  output_string ch ((Hashtbl.fold 
				    (fun k v a -> (a^ (Int64.to_string k) ^ " --> " ^ ( (* trie2string !v *)  trie2string_small !v ) ^ "\n") ) 
				    g.id2trie
				    "") ^ "\n\n"); flush ch;
  in begin
      (* Globals.dbgMsg "fg" 8 ("String form of grammar computed in " 
	 ^ (string_of_float (tm2-.tm1)) 
	 ^ " seconds.\n"); *)
    end    
    
(* Create a new grammar *)
let createGrammar numNTs numTs start =
  let g = {nts = Hashtbl.create numNTs;
	   ts = Hashtbl.create numTs;
	   id2trie = Hashtbl.create (numNTs);
	   trie =  {stateId=StateID.next (); value = N ({nName="TRIEROOT"}); (*constituents=[];*) next=(Hashtbl.create numNTs); productions=(Hashtbl.create numNTs)};
	   trieSize = 0;
	   wugs = Hashtbl.create 10000;
	   start = start} in begin
      (Hashtbl.add g.nts {nName="ROOT"} []);
      Hashtbl.replace g.id2trie g.trie.stateId  (ref g.trie);
      g;
    end

(* IMPLEMENTS CYK INTERFACE *)
let sizeTrie grammar =
  grammar.trieSize

let getStateConstituents filter threshold grammar trieID =
  if Hashtbl.mem grammar.id2trie trieID
  then let trie = Hashtbl.find grammar.id2trie trieID
    in let res= (Hashtbl.fold 
		    (fun k v a  -> 
		      if (((prodLogprob v) > neg_infinity) && (filter grammar v threshold)) 
		      then begin
			  k :: a;
			end
		      else a)  
		    !trie.productions
		    [])
    in res
  else failwith ("FragmentGrammar.getStateConstituents: unable to find trie with ID: " ^ (Int64.to_string trieID)) 

(* IMPLEMENTS CYK INTERFACE *)
let stepTrie grammar trieId nonterminal =
  if Hashtbl.mem grammar.id2trie trieId
  then let trie = !(Hashtbl.find grammar.id2trie trieId)
    in if Hashtbl.mem trie.next nonterminal
      then let nextTrie =(Hashtbl.find trie.next nonterminal) 
	in Some nextTrie.stateId
      else None
  else failwith ("FragmentGrammar.stepTrie: Unable to find trie with id: " ^ (Int64.to_string trieId))

(* IMPLEMENTS CYK INTERFACE *)
let isTerminal grammar symbol =
  match symbol with
      T t -> Hashtbl.mem grammar.ts t
    | _ -> false

(* IMPLEMENTS CYK INTERFACE *)
let isStartTrie grammar trieId =
  trieId = grammar.trie.stateId

(* IMPLEMENTS CYK INTERFACE *)
let headAsSymbol prod =
  !prod.head

(* Get the number of nonterminals in this grammar *)      
(* IMPLEMENTS GRAMMAR INTERFACE *)
let numNT g = (Hashtbl.length g.nts)

(* Update Trie with a Production *)
let addProductionToTrie grammar (prod : production ref) =
  let rec aux trie rhs =
    match rhs with
	[] -> let _ = Hashtbl.replace trie.productions !prod.head prod
	  in begin
	      Hashtbl.replace grammar.id2trie trie.stateId (ref trie);
	      trie;
	    end
      | rhsNext::rhsRest ->
	  let nextTrie = if Hashtbl.mem trie.next rhsNext
	    then aux (Hashtbl.find trie.next rhsNext) rhsRest
	    else aux {stateId= StateID.next ();
		      value = rhsNext;
		      productions = Hashtbl.create (numNT grammar);
		      next = Hashtbl.create (numNT grammar)} rhsRest
	  in let _ = Hashtbl.replace trie.next rhsNext nextTrie
	  in let _ = Hashtbl.replace grammar.id2trie nextTrie.stateId (ref nextTrie)    (* add the trie to our id -> trie hash *)
	  in trie 
  in begin
      (* Globals.dbgMsg "fg" 10 ("Adding production to trie: " ^ (Int64.to_string prod.pid) ^ "\n");*)
      let roottrie = (aux grammar.trie !prod.rhs) in
	grammar.trie <- roottrie;
    end


(* Add a nonterminal to the grammar *)
let addT g t =
  if Hashtbl.mem g.ts t
  then ()
  else let num = Hashtbl.length g.ts in 
	 begin
	   Hashtbl.add g.ts t (num);
	 end

let getRootTrie g =
  g.trie.stateId

  (*Enumerate all the possible annotations for a base rule rhs.*)
let rec enumerateWUGRules (rhs : symbol list) = match rhs with
    [] -> [[]]
  | T t :: tl -> 
      let first =  (enumerateWUGRules tl) in
      let second = (enumerateWUGRules tl) in
	((List.map (fun e ->  (T t) :: e) first) @ (List.map (fun e ->  (T {tName=("<WUG>")}) :: e) second))
  | N n :: tl ->  
      let rest = (enumerateWUGRules tl) in
	(List.map (fun e -> (N n) :: e) rest)

let annotatedSymbol sym = match sym with
    N n -> begin
	(*if String.contains n.nName '@'
	then Globals.dbgMsg "fg" 10 ("Found annotated symbol: " ^ (n.nName) ^ "\n")
	else Globals.dbgMsg "fg" 10 ("Found unannotated symbol: " ^ (n.nName) ^ "\n"); *)
	String.contains n.nName '@';
      end
  | T t -> false

(* Create a new base rule and populate it's annotated base rules by
   enumerating the possibilities. *)
let rec createNewProduction g h (rhs : symbol list) lprob =
  (*let _ =  Globals.dbgMsg "fg" 1 ("Adding Baserule with category: " ^ (nt2string h) ^ " grammar has category: "^ (symbol2string g.start) ^"\n") in*)
  let wugs = List.filter (fun r -> (List.mem (T {tName=("<WUG>")}) r)) (enumerateWUGRules rhs)
  in let num_wugs = List.length wugs
  in let (wugs, num_wugs) =
       (* This is a Hack to only allow wugs for unary productions *)
       if num_wugs > 1 || (annotatedSymbol (N h))
       then ([],0)
       else (wugs,1)
  in let p = ref { pid = (ProductionID.next ());
		      head=(N h);
		      rhs=rhs;
		      logprob=(if (num_wugs > 0)
			then (lprob +. main_multiplier)
			else lprob);}
	in begin

      if (Hashtbl.mem g.nts h)
      then Hashtbl.replace g.nts h (p::(Hashtbl.find g.nts h))
      else Hashtbl.replace g.nts h [p];
      
      (List.iter (fun symb -> match symb with
	  N n -> ()
	| T t -> addT g t)
	  rhs);
      
      addProductionToTrie g p;
      
      (* create wug rules *)
      (if num_wugs > 0
	then let each_wug_multiplier = (1.0 /. (float_of_int num_wugs)) +. wug_multiplier
	  in let wug_logprob = each_wug_multiplier +. lprob
	  in List.iter 
	    (fun r -> 
	      let wug_signature = ((N h) :: r)
	      in if Hashtbl.mem g.wugs wug_signature
		then let old_production = Hashtbl.find g.wugs wug_signature
		  in !old_production.logprob <- (Utils.logsumexp [!old_production.logprob; wug_logprob]) (* if this wug-rule already exits increment its logprob *)
		else let new_prod = ref { pid = (ProductionID.next ());
					  head = (N h);
					  rhs = r;
					  logprob = wug_logprob;}
		  in let _ = Hashtbl.add g.wugs wug_signature new_prod (* add the new wug production to the list of wug productions *)
		  in let _ = Hashtbl.replace g.nts h (new_prod::(Hashtbl.find g.nts h)) (* add the new production to the grammar *)
		  in addProductionToTrie g new_prod)
	    wugs);
    end
    
(* Update Trie with a Production *)
let removeProductionFromTrie grammar prod =
  let rec aux trie rhs =
    match rhs with
	[] -> let _ = Hashtbl.remove trie.productions prod.head
	  in (*let newTrie =	{trie with constituents = others} in*) begin
	      (* Globals.dbgMsg "fg" 10 ("Removing production from trie: " ^ (Int64.to_string prod.pid) ^ "\n");*)
	      Hashtbl.replace grammar.id2trie trie.stateId (ref trie);
	      trie;
	    end
      | rhsNext::rhsRest ->
	  let nextTrie = 
	    if Hashtbl.mem trie.next rhsNext
	    then aux (Hashtbl.find trie.next rhsNext) rhsRest 
	    else failwith "FragmentGrammar.removeProductionFromTrie: Trying to remove a production which does not exist in trie!"
	  in begin
	      if (((Hashtbl.length nextTrie.next)=0) && (Hashtbl.length nextTrie.productions = 0)) (* Prune the trie *)
	      then begin 

		  Hashtbl.remove trie.next rhsNext;
		  Hashtbl.remove grammar.id2trie nextTrie.stateId;
		end
	      else Hashtbl.replace trie.next rhsNext nextTrie;
	      trie;
	    end
  in begin
      (* Globals.dbgMsg "cyk" 10 ("Removing production from trie: " ^ (Int64.to_string prod.pid) ^ "\n"); *)
      let roottrie = (aux grammar.trie prod.rhs) in
	grammar.trie <- roottrie;
    end

(*Get the start symbol*)
let getStart g =
  g.start

(* Get a unique id for each production *)
(* IMPLEMENTS GRAMMAR INTERFACE *)
let prodID p = p.pid

(* Get the number of nonterminals in this grammar *)      
(* IMPLEMENTS GRAMMAR INTERFACE *)
let numT g = (Hashtbl.length g.ts)
  
(* Get the integer ID for this nonterminal *)
(* IMPLEMENTS GRAMMAR INTERFACE *)
let ntID g n = 
  if Hashtbl.mem g.nts n 
  then (Hashtbl.find g.nts n) 
  else failwith ("Grammar does not contain nonterminal: " ^ n.nName)

(* Get the integer ID for this nonterminal *)
(* IMPLEMENTS GRAMMAR INTERFACE *)
let tID g t = 
  if Hashtbl.mem g.ts t 
  then (Hashtbl.find g.ts t) 
  else failwith ("Grammar does not contain terminal: " ^ t.tName)
    
(* Build a terminal from a string *)
(* IMPLEMENTS GRAMMAR INTERFACE *)
let string2t s =
  {tName=s}

let string2terminal s =
  (T {tName=s})


let string2nt s =
  {nName=s}

let string2nonTerminal s =
  (N {nName=s})
    
(* Get all the nonterminals associated with this grammar *)
(* IMPLEMENTS GRAMMAR INTERFACE *)
let getNTs g = Hashtbl.fold (fun k v a -> k::a) g.nts []


(* IMPLEMENTS GRAMMAR INTERFACE *)
let isROOT p = if p.pid = (-1L) then true else false
    

(* Find the spans of a tree. *)
let tree2spans proc tree = 
  let rec processChildren (length : int ) (start : int) (children : parseTree list)  = match children with
      [] -> length (* Return the total length of these children *)
    | hd :: tl -> let  childLength = (processNode (start+length) hd)
      in processChildren (length+childLength) start tl 
  and  processNode (start : int) (t : parseTree) = match t with
      Nd (l, ch) -> let length = processChildren 0 start ch
	in let _ = proc start l (start+length)
	in length
    | Lf (l) -> let _ = proc start l (start + 1) in 1
  in processNode 0 tree

    
(* Get the yield of a table *)
let getParseTreeYield p =
  let rec processNode n = match n with
      Nd (l, ch) -> List.flatten (List.map processNode ch)
    | Lf l -> [l]
  in (processNode p)

let parseTree2stringNoRoot p =
  let rec processNode n = match n with
      Lf s -> (symbol2string s) 
    | Nd (s, ch) -> "(" ^ (symbol2string s)  
	^ " " ^ (List.fold_left (fun a e -> a ^ (processNode e)) "" ch) ^ ")"
  in  match p with
      Lf s -> (symbol2string s) 
    | Nd (s, ch) ->  (List.fold_left (fun a e -> a ^ (processNode e)) "" ch)

let stateConstituentProb grammar state constituent =
  if Hashtbl.mem grammar.id2trie state
  then
    (let trie = Hashtbl.find grammar.id2trie state
      in if !trie.stateId = grammar.trie.stateId
	then  0.0
	else (if Hashtbl.mem !trie.productions constituent
	  then let prod =  Hashtbl.find !trie.productions constituent
	    in prodLogprob prod
	  else failwith ("FragmentGrammar.stateConstituentProb: unable to find constituent: " ^ (symbol2string constituent) ^ " in trie: " ^ ( trie2string_small !trie) )))
  else failwith ("FragmentGrammar.stateConstituentProb: unable to find trie with ID: " ^ (Int64.to_string state))

let stateConstituent grammar state constituent =
  if Hashtbl.mem grammar.id2trie state
  then (let trie = Hashtbl.find grammar.id2trie state
    in if !trie.stateId = grammar.trie.stateId
      then true
      else Hashtbl.mem !trie.productions constituent)
  else failwith ("FragmentGrammar.stateConstituentProb: unable to find trie with ID: " ^ (Int64.to_string state))

let rec compareParseTrees pt1 pt2 = 
  let compareSymbols s1 s2 = match s1, s2 with
      N n1, T n2 -> n1.nName=n2.tName
    |	N n1, N n2 -> n1.nName=n2.nName
    |	T n1, T n2 -> n1.tName=n2.tName
    |	T n1, N n2 -> n1.tName=n2.nName
  in match pt1, pt2 with
      Nd (s1, ch1), Nd (s2, ch2) -> 
	if compareSymbols s1 s2 
	then if (List.length ch1 = List.length ch2)
	  then begin
	      (* Globals.dbgMsg "fg" 10 ("Comparing subtrees: " ^ 
		 (List.fold_left  
		 (fun a v -> a ^ " " ^ v)
		 "" (List.map parseTree2string ch1)) ^ " to subtree: " ^  
		 (List.fold_left (fun a v -> a ^ " " ^ v)
		 "" (List.map parseTree2string ch2)) ^ "\n"); *)
	      List.for_all (fun v -> v) (List.map2 compareParseTrees ch1 ch2)
	    end
	  else false
	else false
    | Nd _, Lf _ -> false 
    | Lf _, Nd _ -> false
    | Lf s1, Lf s2 -> 
	if compareSymbols s1 s2 
	then true 
	else false



let stripAnnotation sym = 
  if annotatedSymbol sym
  then match sym with
      N n -> (N {nName = (List.hd (Str.split  (Str.regexp "[@]") n.nName))})
    | T t -> sym
  else sym

let getROOTStateExpectations () =
  begin
    (* Globals.dbgMsg "fg" 10 ("Returning the ROOT state expectations object, with entropy: " ^ 
			       (string_of_float neg_infinity) ^ "(" ^ 
			       (string_of_float (exp neg_infinity)) ^ ")" ^ "\n");*)
    {sNumParses = (log 1.0);
     sEntropy = neg_infinity;
     sSurprisal = neg_infinity;
     sKL = neg_infinity;  
     sNumConstituents =  neg_infinity;
     sBoundaries = Array.make 1 (log 0.0);};  
  end

(* CYK interface *)
let updateStateExpectations oldStateExpOpt lStateExp rConstExp  = 
  begin 
    (*  Globals.dbgMsg "fg" 10 ("Updating state expectations\n" ^
	"\tleft State Num: " ^ 
	(string_of_float lStateExp.sNumConstituents) ^ "(" ^ 
	(string_of_float (exp lStateExp.sNumConstituents)) ^ ")" ^ 
	"\n\tRight Constituent Num: " ^
	(string_of_float rConstExp.cNumConstituents) ^ "(" ^ 
	(string_of_float (exp rConstExp.cNumConstituents)) ^ ")" ^ "\n" );*)

   (* Globals.dbgMsg "fg" 10 (" Left: " ^ (string_of_float (exp lStateExp.sNumParses)) ^ " Right: "  
			     ^ (string_of_float (exp rConstExp.cNumParses)) ^ " Old: "  ^ 
			     (string_of_float (exp (match oldStateExpOpt 
			       with Some e -> e.sNumParses
				 | None -> (log 0.0) ))) ^  "\n" );*)

    let leftPosition = (Array.length lStateExp.sBoundaries) - 1 
    in match oldStateExpOpt with
	Some e ->
	  let newNumParses =  Utils.logsumexp [e.sNumParses; (lStateExp.sNumParses +. rConstExp.cNumParses)] (*Utils.logsumexp[e.sNumParses;]*)
	  in let newEntropy = Utils.logsumexp [e.sEntropy; lStateExp.sEntropy; rConstExp.cEntropy]
	  in let newSurprisal = Utils.logsumexp [e.sSurprisal; lStateExp.sSurprisal; rConstExp.cSurprisal]
	  in let newKL = Utils.logsumexp [e.sKL; lStateExp.sKL; rConstExp.cKL]
	  in let newNumConstituents = Utils.logsumexp [e.sNumConstituents; lStateExp.sNumConstituents; rConstExp.cNumConstituents]
	  in let newBoundaryContributions = Array.concat [Array.sub lStateExp.sBoundaries 0 leftPosition; 
							  [| 
							    (*Utils.logsumexp [(log 1.0) +. lStateExp.sBoundaries.(leftPosition); 
									     (log 1.0) +.  rConstExp.cBoundaries.(0)]*)
							      (max lStateExp.sBoundaries.(leftPosition) rConstExp.cBoundaries.(0));

							  |];
							  Array.sub rConstExp.cBoundaries 1 ((Array.length rConstExp.cBoundaries)-1);]
	  (*in let _ = Globals.dbgMsg "fg" 10 ( "Old State Boundaries " ^ (Array.fold_left (fun a v -> a ^ "," ^ (string_of_float (exp v))) "" newBoundaryContributions) ^  "\n" )*)
	  in let newBoundaries = Array.mapi (fun i elem -> Utils.logsumexp [newBoundaryContributions.(i); elem]) e.sBoundaries
	  (*in let _ = Globals.dbgMsg "fg" 10 ( "New State Boundaries " ^ (Array.fold_left (fun a v -> a ^ "," ^ (string_of_float (exp v))) "" newBoundaries) ^  "\n" )*)
	  in {sNumParses = newNumParses;
	      sEntropy =  newEntropy;
	      sSurprisal =  newSurprisal;
	      sKL =  newKL;
	      sNumConstituents = newNumConstituents;
	      sBoundaries = newBoundaries;}
      | None ->
	  let newNumParses = lStateExp.sNumParses +. rConstExp.cNumParses
	  in let newEntropy = Utils.logsumexp [lStateExp.sEntropy; rConstExp.cEntropy];
	  in let newKL = Utils.logsumexp [lStateExp.sKL; rConstExp.cKL];
	  in let newSurprisal = Utils.logsumexp [lStateExp.sSurprisal; rConstExp.cSurprisal];
	  in let newNumConstituents = Utils.logsumexp [lStateExp.sNumConstituents; rConstExp.cNumConstituents]
	  in let newBoundaries = Array.concat [Array.sub lStateExp.sBoundaries 0 leftPosition; 
					       [|
						 (* Utils.logsumexp [(log 1.0) +. lStateExp.sBoundaries.(leftPosition); 
								  (log 1.0) +.  rConstExp.cBoundaries.(0)] *)
						 (max lStateExp.sBoundaries.(leftPosition) rConstExp.cBoundaries.(0));
					       |];
					       Array.sub rConstExp.cBoundaries 1 ((Array.length rConstExp.cBoundaries)-1);]
	  (*in let _ = Globals.dbgMsg "fg" 10 ( "New State Boundaries " ^ (Array.fold_left (fun a v -> a ^ "," ^ (string_of_float (exp v))) "" newBoundaries) ^  "\n" )*)
	  in  {sNumParses = newNumParses;
	       sEntropy = newEntropy;  
	       sSurprisal = newSurprisal;
               sKL = newKL;
	       sNumConstituents =  newNumConstituents;
	       sBoundaries = newBoundaries;}
  end
    
let getEmptyConstituentExpectations (symb : symbol)  =
 (* Globals.dbgMsg "fg" 10 ("Getting Empty Constituent Expectations from symbol: " ^ (symbol2string symb) ^ "\n\n");*)
  {cNumParses = (log 1.0);
   cEntropy = neg_infinity;  
   cSurprisal = neg_infinity;
   cKL = neg_infinity;
   cNumConstituents = (log 0.0);
   cBoundaries = Array.make 2 (log 0.0);} (* We represent boundary averages by an array of constituent_length +1 (one position for each point between two constituents*)

(* CYK interface *)
let updateConstExpectations symb oldConstExpOption childStateExp prob unnormalized_prob = 
  begin
    (* Globals.dbgMsg "fg" 10 ("Updating constituent expectations\n"^
			       "\tSymbol: " ^
			       (symbol2string symb) ^ "\n"^
			       "\tposterior probability: " ^ 
			       (string_of_float prob) ^ " (" ^ 
			       (string_of_float (exp prob)) ^ ")" ^ 
			       "\n\tchild-state Num Constituents: " ^
			       (string_of_float childStateExp.sNumConstituents) ^ "(" ^ 
			       (string_of_float (exp childStateExp.sNumConstituents)) ^ ")" ^ "\n" );

    Globals.dbgMsg "fg" 10 ("\t" ^ (string_of_float (exp childStateExp.sNumParses)) ^ " "  ^ 
			       (string_of_float (exp (match oldConstExpOption 
				 with Some e -> e.cNumParses
				   | None -> (log 0.0) ))) ^  "\n" ); *)
    let constituentContribution = if annotatedSymbol symb then (log 0.0) else (log 1.0) (* Does this constituent count or not *)
    in let lastBoundary = (Array.length childStateExp.sBoundaries) - 1
    in match oldConstExpOption with
	Some  e -> 
	  let newNumParses =    Utils.logsumexp [e.cNumParses; childStateExp.sNumParses (*+.prob*)]
	  in let newEntropy =   Utils.logsumexp [e.cEntropy;   (prob +. (log ((exp childStateExp.sEntropy)   +. (-. prob))))]
	  in let newKL =        Utils.logsumexp [e.cKL;        (prob +. (log ((exp childStateExp.sKL)        +. (prob -. unnormalized_prob))))]
	  (*in let newSurprisal = Utils.logsumexp [e.cSurprisal; (prob +. (log ((exp childStateExp.sSurprisal) +. (-. unnormalized_prob))))]*)
	  in let newSurprisal = Utils.logsumexp [e.cSurprisal; (prob +. (Utils.logsumexp [childStateExp.sSurprisal; unnormalized_prob]))]

	  in let newNumConstituents = Utils.logsumexp [e.cNumConstituents; (prob +.  Utils.logsumexp [childStateExp.sNumConstituents; constituentContribution])]  
	  in let weightedBoundaries = Array.map (fun elem -> prob +. elem) childStateExp.sBoundaries
	  (*in let _ = Globals.dbgMsg "fg" 10 ("Constituent: " ^ (symbol2string symb) ^ " Prob: " ^ (string_of_float (exp prob)) ^  "\n" )*)
	  in let _ = begin weightedBoundaries.(0) <- Utils.logsumexp[weightedBoundaries.(0); prob +. constituentContribution];
	      weightedBoundaries.(lastBoundary) <- Utils.logsumexp[weightedBoundaries.(lastBoundary); prob +. constituentContribution]; end
	  in let newBoundaries = Array.mapi (fun i elem -> Utils.logsumexp [weightedBoundaries.(i); elem]) e.cBoundaries
	  (*in let _ = Globals.dbgMsg "fg" 10 ( "New Boundaries " ^ (Array.fold_left (fun a v -> a ^ "," ^ (string_of_float (exp v))) "" newBoundaries) ^  "\n" )*)
	  in {cNumParses = newNumParses;
	      cEntropy = newEntropy; 
	      cSurprisal = newSurprisal;
	      cKL = newKL;  
	      cNumConstituents = newNumConstituents;
	      cBoundaries = newBoundaries;}
      | None -> 
	  (*let _ = Globals.dbgMsg "fg" 10 ( "Constituent: " ^ (symbol2string symb) ^ " Prob: " ^ (string_of_float (exp prob)) (*^  "\n"*) ) in*)
	  let newNumParses = (*prob +.*) childStateExp.sNumParses
	  in let newEntropy = (prob +. (log ((exp childStateExp.sEntropy) +. (-. prob))))
	  in let newKL =      (prob +. (log ((exp childStateExp.sKL)      +. (prob -. unnormalized_prob))))
	  in let newSurprisal = (prob +. (Utils.logsumexp [childStateExp.sSurprisal; unnormalized_prob]))	  
	  (*in let newSurprisal = (prob +. (log ((exp childStateExp.sSurprisal) +. (-. unnormalized_prob))))*)
	  
	  in let newNumConstituents = prob +.  Utils.logsumexp [childStateExp.sNumConstituents; constituentContribution]
	  in let newBoundaries = Array.map (fun elem -> prob +. elem) childStateExp.sBoundaries
	  in let _ = begin newBoundaries.(0) <- Utils.logsumexp[newBoundaries.(0); prob +. constituentContribution];
	      newBoundaries.(lastBoundary) <- Utils.logsumexp[newBoundaries.(lastBoundary); prob +. constituentContribution]; end
	  (*in let _ =Globals.dbgMsg "fg" 10 ( " " ^ (Array.fold_left (fun a v -> a ^ "," ^ (string_of_float (exp v))) "" newBoundaries) ^  "\n" )*)
	  in {cNumParses = newNumParses;
	      cEntropy = newEntropy;  
	      cSurprisal = newSurprisal;
	      cKL = newKL;  
	      cNumConstituents = newNumConstituents;
	      cBoundaries = newBoundaries;}
	    (*in let newNumConstituents = Utils.logsumexp [oldNumConstituents; 
	      (prob +. Utils.logsumexp 
	      [childStateExp.sNumConstituents;  (log 1.0)])] *)
	    (*in let _ =  Globals.dbgMsg "fg" 10 ("\tOld num Constituents: " ^ (string_of_float oldNumConstituents) ^ " ("^ (string_of_float (exp oldNumConstituents)) ^")"^"\n")
	      in let _ =  Globals.dbgMsg "fg" 10 ("\tNew num Constituents: " ^ (string_of_float newNumConstituents) ^ " ("^ (string_of_float (exp newNumConstituents)) ^")"^"\n\n")*)
  end

    
(* CYK interface *)
let constituentMatches sym list= 
  let stripped = stripAnnotation sym
  in List.mem stripped list


let rec forwardSampleTree (grammar : grammar) (start : symbol) = 
  match start with
      T t ->  Lf (T t)
    | N n -> let productions = Hashtbl.find grammar.nts n
	     in let probs = List.map (fun pr -> !pr.logprob) productions
	     in let index = Utils.sampleIndex probs 
	     in let prod = List.nth productions index
	     in let rhs = !prod.rhs
	     in (Nd ((N n), (List.map (fun s -> (forwardSampleTree grammar s)) rhs)))
