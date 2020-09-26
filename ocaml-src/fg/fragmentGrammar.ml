(***********************************************************************************
 ***********************************************************************************
 *                              Module: FragmentGrammar                            * 
 * --------------------------------------------------------------------------------*
 *            This module implements a partial fragment grammar (PFG)              * 
 ***********************************************************************************)    
open Utils
open Id
  

module FragmentGrammar =
struct
  
  (* ---------------------------------------------------------------------*
   *              Data types for the alphabet of this grammar:            *
   *       A terminal is just a string, a nonterminal needs a unique ID   *          
   *                                                                      *
   * ---------------------------------------------------------------------*)
  type nonterminal = {nName : string}  (* String name of this non-terminal *)
  type terminal = {tName : string}
      
  (* A symbol is a union of terminals and non terminals *)
  type symbol = N of nonterminal | T of terminal
  
  (* TODO -- get rid of the distinction between terminal and nonterminals at least at this level. *)
  (* type symbol = string *)

  (* A memorization decision is either a pointer or a variable *)
  type ('a, 'b) mem = Ptr of 'a | Val of 'b 
    
  (* Generate table IDs *)
  module ProductionID = ID(struct end)
  module AnalysisID = ID(struct end)
  module CollapsedID = ID(struct end)
  module StateID = ID(struct end) 

 (* Some types to store statistics
     TODO make this so that it is 
     modularized *)
 
  (*tables*) 
  type tableStats = {nodes: int;
		     internal : int;
		     leaves: int;
		     leafv : int;
		     leaft : int;
		     leafrv : float;
		     nonterm : int;
		     depth : int;
		     yieldlength : int;
		     discontig: int;}

  type baserule =
      {brid : int64;
       head : nonterminal;
       rhs : symbol list;
       r : restaurant ref;
       pi : float; 
       mutable stickyScore : float;
       mutable stickyScores : float list;
       mutable stickyTheta : float;
       mutable slipperyTheta : float; 
       mutable stickyCnts : float list; 
       mutable brCnt : float;}
  and table =
      {id : int64;
       mutable dangling : bool;
       mutable structure : parseTree;
       rest : restaurant ref;
       base : baserule ref;
       children : (table ref, symbol) mem list;
       mem : (symbol, symbol) mem list;
       yield : symbol list;
       stats : tableStats;
       mutable tCnt : float;
       parseTrees : (parseTree, float) Hashtbl.t;}
  and restaurant =
      {label : nonterminal;
       mutable a : float;
       mutable b : float;
       mutable brScore : float;
       mutable tblScore : float;
       mutable totPi : float;
       tbls : (int64, table ref) Hashtbl.t;
       mutable nTbls : float;
       mutable brs : baserule ref list;
       mutable rCnt : float; 
       prods : (symbol list, production) Hashtbl.t;
       mutable preterminal : bool;}
  and production = {
      pid : int64;
      prodRest : restaurant ref;
      mutable prodTblsCnt : float; (* The total number of customers sitting at tables in this production. *)
      mutable prodTblCnt : float;  (* The total number of tables in this production *)
      mutable prodTotPi : float;
      pHead : symbol;
      pRhs : symbol list;
      members : (int64, pType) Hashtbl.t;
      mutable pCount : int;}
  and pType = (* Root of nonterminal | *) Br of baserule ref | Tbl of table ref
  and analysis =
      Constituent of  (* int64 **) table ref  * analysis list * parseTree
      | Terminal of (*int64 **) symbol * parseTree
  and parseTree = Nd of symbol * parseTree list | Lf of symbol
 
  type parameters =  {
      aDef : float;
      bDef : float;
      slipperyThetaDef : float;
      stickyThetaDef : float;
      piDef : float}

  type grammarTrie =
       {stateId : int64;
        value : symbol;
	productions : (symbol, production) Hashtbl.t;
        next : (symbol, grammarTrie) Hashtbl.t}
  
  type grammar =
      {params : parameters;
       rsts : (nonterminal, restaurant) Hashtbl.t;
       nts : (nonterminal, int) Hashtbl.t;
       ts : (terminal, int) Hashtbl.t;
       id2trie : (int64, grammarTrie ref) Hashtbl.t;   (* trie state id to trie node, for random access *)
       mutable trie : grammarTrie;
       mutable trieSize : int;
       start : symbol;
       structures : (parseTree, float) Hashtbl.t}

  (* Parser Expectations *)
  type stateExpectations =
      {mutable sEntropy : float;
       mutable sNumConstituents : float;}

  type constExpectations =
      {mutable cEntropy : float;
       mutable cNumConstituents : float;}

  let get_a rest =
    rest.a

  let get_b rest =
    rest.b

  (* Score the table portion of a restaurant -- run whenever a tbl.tCnt gets changed. *)
  let rescoreTables (r : restaurant) =
    let tCounts = Array.create (Hashtbl.length r.tbls) 0 in
    let _ = (Hashtbl.fold 
		(fun k v a -> 
		  begin 
		    
		    tCounts.(a) <- (int_of_float !v.tCnt); 
		    (a+1); 
		  end) r.tbls 0) in
    let score = (pitmanyor2 r.a r.b tCounts)
    in score

  (* Get a restaurant from the grammar *)
  let getRestaurant g nt = try 
      Hashtbl.find g.rsts nt
    with Not_found -> failwith ("Restaurant: " ^ nt.nName ^ " not found.")

  (*Compute the expect probability of a position in the RHS of a sticky rule *)
  let annotationsPosExpLogprob (*g*) br mem stickyCnt =
    let grandTotal = (br.brCnt +. br.slipperyTheta +. br.stickyTheta)
    and slipperyCnt = (br.brCnt -. stickyCnt)
    in  match mem with
	Val (T _) -> 0.0                                                    (* Terminal *)
      | Val (N nt) -> log ((slipperyCnt +. br.slipperyTheta) /. grandTotal) (* Slippery *) 
      | Ptr (N nt) -> log ((stickyCnt +. br.stickyTheta)    /. grandTotal)  (* Sticky *) 
      | Ptr (T _) -> (0.0) (* failwith "FragmentGrammar.annotationsPosExpLogProb: Should not have a pointer to a terminal symbol" (* Non-sensical, but ok... *)*)
   

  (* Get the expected probability of an annotated baserule, that is
     the product of its stickiness decisions. *)
  let annotationsExpLogprob g table = 
    let br = !(table.base) in
      List.fold_left2 (fun a v1 v2 -> a +. (annotationsPosExpLogprob br v1 v2 )) 0.0 table.mem br.stickyCnts
      
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
  let getpTypeRHS p = match p with
     (* Root n -> [N n]
    |*) Br br -> !br.rhs
    | Tbl tbl -> !tbl.yield

  (*Get the head of a production*)
  let pTypeHead p = match p with
    (*  Root s -> {nName="ROOT"}
    |*) Br br -> !br.head
    | Tbl t -> !(!t.rest).label

  (* Get the RHS of this production *)
  (* IMPLEMENTS GRAMMAR INTERFACE *)
  let getRHS p = p.pRhs

  (*Get the head of a production*)
  let head p = p.pHead

  (* Get the production associated with a hashtable *)
  let table2production t =
    if Hashtbl.mem  !(t.rest).prods !(t.base).rhs
    then Hashtbl.find !(t.rest).prods !(t.base).rhs 
    else failwith "FragmentGrammar.table2production: restaurant does not have a production for table!"

  (************************************************************************
   *                            Probability Functions                     *                       
   * ---------------------------------------------------------------------*
   * Calculate various probabilities associated with this grammar.        *
   ************************************************************************)

  (* The probability of a new table in this restaurant *)
  let newTableLogprob r = 
    let numTbls = float_of_int (Hashtbl.length r.tbls) in
      log ((numTbls *. r.a) +.  r.b) -. log(r.rCnt +. r.b)
  
  (* Get the expected probability of a baserule *) 
  let baseruleExpLogprob br = 
    let rest = !(br.r) in
      log (br.brCnt +. br.pi) -. log (rest.nTbls +. rest.totPi)
	
  (*get the expected probability of a production *)
  let prodTypeLogprob p = match p with
    (*  Root _ -> 0.0 
    |*) Br br -> 
	let rest = !(!br.r) in
	  (newTableLogprob rest) +. (baseruleExpLogprob !br)
    | Tbl t -> 
	let rest = !(!t.rest) in
	  log (!t.tCnt -. rest.a) -. log (rest.rCnt +. rest.b)

  (* This is the complete score for a new table -- including the cost
     of sitting at a new table, the cost of the baserule (both of
     these are included in prodLogProb) drawn from the baserule
     multinomial-dirichlet and the product of the cost of the the
     stickiness decisions drawn from the sticky dirichlet
     multinomials *)
  let scoreTableCreation g table =
    (prodTypeLogprob (Br table.base ) +. (annotationsExpLogprob g table))

  (*get the expected probability of a production *)
  (* IMPLEMENTS GRAMMAR INTERFACE *)
  let prodLogprob  p = 
    let r = !(p.prodRest) in 
    logsumexp [
	log ( (p.prodTblsCnt -. (p.prodTblCnt *. r.a)) /. (r.rCnt +. r.b ));
	((newTableLogprob r) +. (log ((p.prodTblCnt +. p.prodTotPi) /. (r.totPi +. r.nTbls))))]

  let computeProdLogprob p =  (Utils.logsumexp (Hashtbl.fold (fun k v a ->  (prodTypeLogprob v) :: a )  p.members []))
  let computeTblsProdLogprob p =  
    (Utils.logsumexp 
	(Hashtbl.fold 
	    (fun k v a ->  
	      (match v with
		 (* Root _ -> 0.0
		|*) Br br -> neg_infinity
		| Tbl t -> 
		    let rest = !(!t.rest) in
		      log (!t.tCnt -. rest.a) -. log (rest.rCnt +. rest.b)) :: a ) 
	    p.members 
	    []))

  let computeBrsProdLogprob p =  
    (Utils.logsumexp 
	(Hashtbl.fold 
	    (fun k v a ->  
	      (match v with
		(*  Root _ -> 0.0 
		|*) Br br ->  (baseruleExpLogprob !br)
		| Tbl t -> neg_infinity) :: a ) 
	    p.members 
	    []))
	    
  let prodLogprob_ref p =
    prodLogprob !p

(* Get the score for a restaurant *)
  let scoreRestaurant r =
    (r.brScore) +. (r.tblScore)  (* (r.hyperParamScore) +. r.stickyScore *) +. (List.fold_left (fun a br -> a +. !br.stickyScore) 0.0 r.brs)

(************************************************************************
   *                            Pretty printing Functions                 *                       
   * ---------------------------------------------------------------------*
   * Calculate various probabilities associated with this grammar.        *
   ************************************************************************)

  (* Print NT's *)
  let nts2string g =
    Hashtbl.fold (fun k v a -> (k.nName ^ ":" ^ (string_of_int v))^a) g.nts ""

  (* Nonterminals *)
  (* IMPLEMENTS GRAMMAR INTERFACE *)
  let nt2string nt = nt.nName
    
  (* Terminals *)
  (* IMPLEMENTS GRAMMAR INTERFACE *)
  let t2string t = t.tName

  (* Get a string version of a production *)
  let prodType2string p = 
    let rhs2string r = match r with
	T t -> t.tName
      | N nt  -> nt.nName
    in let typ = match p with
	(*Root n -> "Root"
      | *)Br abr -> "br"
      | Tbl tbl -> "Tbl" ^ (Int64.to_string !tbl.id)      
    in "{"^typ^": "^ (nt2string (pTypeHead p)) ^ " --> " ^ List.fold_left (fun a v -> a ^ " " ^ (rhs2string v) ) "" (getpTypeRHS p) ^ "}"
      
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

  (* Get a fuller version of a production *)
  let fullProd2string p =
    let processPType ptype = match ptype with
	(*Root n -> (nt2string n)
      |*) Br abr ->  (Int64.to_string !abr.brid)  
      | Tbl tbl -> (Int64.to_string !tbl.id)
    in begin 
(*	Globals.dbgMsg "fg" 10 ("Converting production to string: "^  (prod2string p) ^ " with number members: " ^ 
				   (string_of_int (Hashtbl.length p.members)) ^
			       "\n"); *)
	"prob: " ^ (string_of_float (exp (prodLogprob p))) ^ " " 
	^ "Customers: " ^ (string_of_float (p.prodTblsCnt)) ^ " " 
	^ "Tables: " ^ (string_of_float  (p.prodTblCnt)) ^ " " 
	^ "Pi: " ^ (string_of_float  (p.prodTotPi)) ^ " " 
	^ (prod2string p) ^ " members: "
	^ (Hashtbl.fold (fun k v a -> (processPType v) ^ " "^ a ) p.members "" );
      end

  let parseTree2string p =
    let rec processNode n = match n with
	Lf s -> (symbol2string s) 
      | Nd (s, ch) -> "(" ^ (symbol2string s)  
	  ^ " " ^ (List.fold_left (fun a e -> a ^ " " ^ (processNode e)) "" ch) ^ ")"
    in  match p with
	Lf s -> (symbol2string s) 
      | Nd (s, ch) ->  "(" ^ (symbol2string s)  
	  ^ " " ^ (List.fold_left (fun a e -> a ^ " " ^ (processNode e)) "" ch) ^ ")"

  (* Get a short string version of a baserule name *)  
  let brName br =
    let rhs2string r = match r with
	T t -> t.tName
      | N nt  -> nt.nName
    in "{" ^ br.head.nName ^ " --> " ^ (List.fold_left (fun s e ->  s ^ " "  ^ ((rhs2string e))) "" br.rhs) ^ "}"

  (* Baserule to string *)    
  let br2string g br =
    "c:" ^ (string_of_float br.brCnt) ^ " "
    ^ "prod prob: " ^ ( Printf.sprintf "%.3f" (exp (prodTypeLogprob (Br (ref br))))) ^ " "
    ^ "pi:" ^ (string_of_float br.pi) ^ " "
   ^ "slipperyTheta: " ^ (string_of_float br.slipperyTheta) ^ " "
     ^ "stickyTheta: " ^ (string_of_float br.stickyTheta) ^ " "
    ^ "stickiness score: " ^ (Printf.sprintf "%.3f" (exp (br.stickyScore))) ^ " "
    ^ "Exp prob: " ^ (Printf.sprintf "%.3f" (exp (baseruleExpLogprob br))) ^ " " 
    ^ "Sticky Counts: [" ^ List.fold_left (fun a v -> a ^ " " ^ (string_of_float v)  ) "" br.stickyCnts ^ "] "
    ^ "Slippery Counts: [" ^ List.fold_left (fun a v ->a ^ " " ^  (string_of_float (br.brCnt -. v))) "" br.stickyCnts ^ "] "
    ^ "\n\t\t"
    ^ "Sticky probs: ["  
         ^ (List.fold_left2 (fun a v1 v2 -> a ^ " " ^ (string_of_float (exp (annotationsPosExpLogprob br (Ptr v1) v2)))) "" br.rhs br.stickyCnts) 
    ^ "]  "
    ^ "Slippery probs: ["  
          ^ (List.fold_left2 (fun a v1 v2 -> a ^ " " ^ (string_of_float (exp (annotationsPosExpLogprob br (Val v1) v2)))) "" br.rhs br.stickyCnts) 
    ^ "]  "
    ^ (brName br) ^ "\n"


  (* Get a string representation of a table structure *)
  let tableStructure2String ( tl : table )  =
    let rec processNode n = match n with
	Ptr tbl ->  ("(" ^ !(!tbl.rest).label.nName ^ (List.fold_left (fun a v ->  a ^ " " ^ (processNode v) ) "" !tbl.children)  ^ ")" )
      | Val (T t) -> (t2string t)
      | Val (N n) -> (nt2string n)
    in  ("(" ^ !(tl.rest).label.nName ^  (List.fold_left (fun a v ->  a ^ " " ^ (processNode v) ) "" tl.children)  ^ ")" )
    
  (* string representation of a table's statistics *)  
  let tableStats2String stats =
    "nodes:" ^ (string_of_int stats.nodes) ^
      "  internal nodes:" ^ (string_of_int stats.internal) ^
      "  leaves:" ^ (string_of_int stats.leaves) ^
      "  leaf variables:" ^   (string_of_int stats.leafv)^
      "  leaf terminals:" ^   (string_of_int stats.leaft) ^
      "  variabe percent:" ^  (string_of_float stats.leafrv) ^
      "  nonterm:" ^    (string_of_int stats.nonterm) ^
      "  depth:" ^   (string_of_int stats.depth) ^
      "  ylength:" ^   (string_of_int stats.yieldlength) ^
      "  discontig:" ^  (string_of_int stats.discontig)
    
  let table2string tbl =
    let leaf2string l = match l with
	Val (T t) -> t.tName
      |  Val (N n) -> n.nName
      | Ptr t  -> "[Tbl " ^ (Int64.to_string (!t.id)) ^ "]"
    and rhs2string r = match r with
	Val (T t) -> t.tName
      | Val (N nt)  -> "[" ^ nt.nName ^ "]" 
      | Ptr (N nt)  -> "(" ^ nt.nName ^ ")"
      | _ -> failwith "Ill formed RHS of annotated base rule"	  
    in "Id:" ^ (Int64.to_string (tbl.id)) ^ " " ^ 
      "c:" ^ (string_of_float tbl.tCnt) ^ " " ^
      "Production prob: " ^ (Printf.sprintf "%.3f" (exp (prodTypeLogprob (Tbl (ref tbl))))) ^ " " ^
      "table: {" ^ !(tbl.rest).label.nName ^ " --> "  ^ 
      (List.fold_left (fun s e ->  s ^ " " ^  ((leaf2string e) )) "" tbl.children) ^ "}  " ^ 
      "sticky list: " ^ (List.fold_left (fun s e ->  s ^ " "  ^ ((rhs2string e))) "" tbl.mem) ^ "  " ^ 
      "structure: " ^ (tableStructure2String tbl) ^ "  " ^
      "yield: \"" ^ (List.fold_left (fun s e ->  s ^ (match e with N n -> n.nName | T t -> t.tName)  ^ " ") "" tbl.yield) ^"\"\n" ^ 
      "\t\t" ^ (tableStats2String tbl.stats) ^ "\n"

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

  (* Print out a string representation of a restaurant -- sort tables and baserules for ease 
     of reading *)
  let rest2string g (restaurant :restaurant) =
    begin 
      (* Globals.dbgMsg "fg" 10 ("Converting restaurant: " ^ 
				restaurant.label.nName ^
				" with number of productions: " ^
				(string_of_int (Hashtbl.length restaurant.prods)) ^
				" to string.\n"); *)
      "Restaurant: " ^ restaurant.label.nName ^ "\n\t" 
      ^ "preterm: " ^ (string_of_bool restaurant.preterminal) ^ " | "  
      ^ "c: " ^ (string_of_float restaurant.rCnt) ^ " | "  
      ^ "a: " ^ (string_of_float restaurant.a) ^ " | " 
      ^ "b: " ^ (string_of_float restaurant.b)  ^ " | " 
      ^ "totPi: " ^ (string_of_float restaurant.totPi)  ^ " | " 
      ^ "ntables: " ^ (string_of_int (Hashtbl.length restaurant.tbls)) ^ " | "
      ^ "new table prob: " ^ (Printf.sprintf "%.3f" (exp (newTableLogprob restaurant))) ^ " | " 
      ^ "score: " ^ (Printf.sprintf "%.3f" (exp (scoreRestaurant restaurant))) ^ " | " 
      ^ "cache score: " ^ (Printf.sprintf "%.3f" (exp restaurant.tblScore)) ^ " | " 
      ^ "baserules score: " ^ (Printf.sprintf "%.3f" (exp restaurant.brScore)) ^ " \n " 
      ^ "base rules: \n" 
      ^ (List.fold_left (fun a v -> ("\t" ^ (br2string g !v ) ^ "\n" ^ a)) "" (List.sort (fun a b -> compare !a.rhs !b.rhs) restaurant.brs)) 
      ^ "tables: \n" 
      ^ (let assoclist = ( Hashtbl.fold  (fun key value a -> (key, !value) :: a) restaurant.tbls [] )
	in let sorted = (List.sort (fun (id1, tbl1) (id2, tbl2) ->  (compare !(tbl1.base).rhs !(tbl2.base).rhs) ) assoclist) 
	in (List.fold_left (fun a (id, tbl) -> ("\t" ^ (table2string tbl ) ^ "\n" ^ a)) "" sorted) )
      ^ "productions: \n" 
      ^ (Hashtbl.fold (fun k v a -> ("\t" ^ (fullProd2string v ) ^ "\n" ^ a)) restaurant.prods "");
    end

  let rec trie2prettyString padding trie =
    let children =  (Hashtbl.fold (fun k v a -> a ^ (trie2prettyString (padding ^ "      ")  v) ^ " ") trie.next  "" ) 
    in if (children = "")
      then  "\n" ^  padding ^  "(" ^ (Int64.to_string trie.stateId)^ "; " ^ (symbol2string trie.value) ^ 
	(* " [" ^ (List.fold_left (fun a v -> a ^ " " ^ (symbol2string v)) "" trie.constituents) ^ "]" ^ *)
	" [" ^ (Hashtbl.fold 
		   (fun k v a -> a ^ " " ^ (symbol2string k) ^ ":" ^  (Int64.to_string v.pid))
		   trie.productions "" ) ^ "]" ^ ")" 
      else "\n" ^ padding ^ "(" ^ (Int64.to_string trie.stateId)^ "; "^ (symbol2string trie.value)  ^
	" [" ^ (Hashtbl.fold 
		   (fun k v a -> a ^ " " ^ (symbol2string k) ^ ":" ^  (Int64.to_string v.pid))
		   trie.productions "" ) ^ "]" 
	^ children ^ ")"

  let rec trie2string trie =
    trie2prettyString "" trie


  let  trie2string_small trie =
    "(" ^ (Int64.to_string trie.stateId)^ "; " ^ (symbol2string trie.value) ^ 	" [" ^ (Hashtbl.fold (fun k v a -> a ^ " " ^ (symbol2string k)^":"^(Int64.to_string v.pid)^":"^(string_of_float (prodLogprob v)))  trie.productions "") ^ "]) "

  let trieId2string_small grammar trieId =
    if Hashtbl.mem grammar.id2trie trieId
    then let trie = Hashtbl.find grammar.id2trie trieId
      in trie2string_small !trie
    else failwith ("FragmentGrammar.trieId2string_small: unable to find trie with value: " ^ (Int64.to_string trieId))

  (* Get a string representation of a whole grammar *)
  let grammar2string g =
    let string = Hashtbl.fold (fun k v a -> rest2string g v  ^ "\n" ^ a ) g.rsts "" in
      begin
	(* Globals.dbgMsg "fg" 8 ("String form of grammar computer in " 
				^ (string_of_float (tm2-.tm1)) 
				^ " seconds.\n"); *)
	string
      end

  (* Get a string representation of a whole grammar *)
  let writeGrammar ch g =
     let keys =  (Hashtbl.fold (fun k _ a -> k :: a) g.rsts [] )
    in let nts = (List.sort compare keys)
    in let _ = (List.iter 
		   (fun v -> 	(* Globals.dbgMsg "fg" 10 ("Computing string form of: "^ v.nName ^"\n"); *)
		     (output_string ch (rest2string g (Hashtbl.find g.rsts v) ^ "\n")); 
		     flush ch; ) nts) 
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
      
  (* Get a string representation of a whole grammar *)
  let writeStructTypes ch g =
    let writeRestStructTypes rest =
      Hashtbl.iter 
	(fun k v  ->
	  Hashtbl.iter (fun k v  -> output_string ch ((parseTree2string k) ^", "^ (string_of_int (int_of_float v))^"\n"); flush ch;)
	    !v.parseTrees
	) rest.tbls
    in let keys =  (Hashtbl.fold (fun k _ a -> k :: a) g.rsts [] )
    in let nts = (List.sort compare keys)
    in (List.iter (fun v -> (writeRestStructTypes (Hashtbl.find g.rsts v))) nts) 
      
   (* Create the default record *)
  let createParams
      ?a:(a=0.0)
      ?b:(b=1.0)
      ?slip:(slip=1.) 
      ?stick:(stick=1.) 
      ?pi:(pi=1.) 
      () ={aDef=a;
	   bDef=b;
	   slipperyThetaDef=slip;
	   stickyThetaDef=stick;
	   piDef=pi;}
	
  (* Create a new grammar *)
  let createGrammar numNTs numTs start params =
    let g = {params = params;
	     rsts = Hashtbl.create numNTs;
	     nts = Hashtbl.create numNTs;
	     ts = Hashtbl.create numTs;
	     (* prod2trie = Hashtbl.create (numNTs * 10); *)
	     id2trie = Hashtbl.create (numNTs);
	     (* symbol2prod = Hashtbl.create (numNTs + numTs); *)
	     trie =  {stateId=StateID.next (); value = N ({nName="TRIEROOT"}); (*constituents=[];*) next=(Hashtbl.create numNTs); productions=(Hashtbl.create numNTs)};
	     trieSize = 0;
	     structures = Hashtbl.create 100000;
	     start = start} in begin
	(Hashtbl.add g.nts {nName="ROOT"} 0);
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
  (*let isTerminal symbol =
    match symbol with
	T _ -> true
      | _ -> false*)

  (* IMPLEMENTS CYK INTERFACE *)
  let isStartTrie grammar trieId =
    trieId = grammar.trie.stateId

  (* IMPLEMENTS CYK INTERFACE *)
  let headAsSymbol prod =
    !prod.pHead

  (* Get the total number of customers in the whole grammar *)  
  let getGrammarSize grammar =
    Hashtbl.fold (fun k v a -> a +. v.rCnt) grammar.rsts 0.0 

  (* Get the number of nonterminals in this grammar *)      
  (* IMPLEMENTS GRAMMAR INTERFACE *)
  let numNT g = (Hashtbl.length g.nts)

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



  (* Update Trie with a Production *)
  let addProductionToTrie grammar (prod : production) =
    let rec aux trie rhs =
      match rhs with
	  [] -> let _ = Hashtbl.replace trie.productions prod.pHead prod
	    in begin
		(* Globals.dbgMsg "fg" 10 ("Entering production: " ^  (Int64.to_string prod.pid) ^ "\n");*)
		(* Globals.dbgMsg "fg" 10 ("\tOld productions: " ^  (List.fold_left (fun a v -> a ^ (Int64.to_string !v.pid) ^ " ") "" oldprods)  ^ "\n");*)
		(* Globals.dbgMsg "fg" 10 ("\tNew productions: " ^  (List.fold_left (fun a v -> a ^ (Int64.to_string !v.pid) ^ " ") "" newtrie.productions)  ^ "\n"); *)
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
	let roottrie = (aux grammar.trie prod.pRhs) in
	  grammar.trie <- roottrie;
      end

  (* Add a nonterminal to the grammar *)
  let addNT g n =
    if Hashtbl.mem g.nts n
    then ()
    else let num = Hashtbl.length g.nts in 
      begin
	(* Globals.dbgMsg "fg" 10 ("Creating New Nonterminal: " ^ n.nName ^ "\n");*)
	Hashtbl.add g.nts n (num);
      end

  (* Add a nonterminal to the grammar *)
  let addT g t =
    if Hashtbl.mem g.ts t
    then ()
    else let num = Hashtbl.length g.ts in 
      begin
	Hashtbl.add g.ts t (num);
      end

  (*Enumerate all the possible annotations for a base rule rhs.*)
  let rec enumerateAnnotations (rhs : symbol list) = match rhs with
      [] -> [[]]
    | T t :: tl -> 
	let rest = (enumerateAnnotations tl) in
	  (List.map (fun e -> Val (T t) :: e) rest)
    | N n :: tl ->  
	let first =  (enumerateAnnotations tl) in
	let second = (enumerateAnnotations tl) in
	  ((List.map (fun e -> Ptr (N n) :: e) first) @ (List.map (fun e -> Val (N n) :: e) second))
	    
  (* Check to see if a grammar has a restaurant *)
  let hasRestaurant g nt = 
    Hashtbl.mem g.rsts nt
      
  (* Does the grammar already contain a baserule with some particular
     structure. If so return it (Return the first one found) *)
  let getBaseRuleStructure g h (rhs : symbol list) =
    if not (hasRestaurant g h)
    then None
    else let r = (Hashtbl.find g.rsts h) 
      in List.fold_left (fun a v -> match a with 
	  (Some _) -> a 
	| _ ->  if (List.length !v.rhs) <> (List.length rhs) 
	  then None
	  else if (List.for_all2 (=) !v.rhs rhs)
	  then (Some !v) 
	  else a) None r.brs 
	
  let getRootTrie g =
    g.trie.stateId

  (* Test to see if a baserule is preterminal *)
  let isPreterminalBaserule br =
    let isTerminal s = match s with
	T t -> true
      | N n -> false
    in List.for_all isTerminal br.rhs
      
  let createNewBaseRule g
      ?pi:(pi=g.params.piDef) 
      ?slipperyTheta:(slipperyTheta=g.params.slipperyThetaDef)  
      ?stickyTheta:(stickyTheta=g.params.stickyThetaDef)
      h (rhs : symbol list) =
  (* let _ =  Globals.dbgMsg "fg" 1 ("Adding Baserule with category: " ^ (nt2string h) ^ " grammar has category: "^ (symbol2string g.start) ^"\n") in *)
  let r = (Hashtbl.find g.rsts h) 
    
    in let br = {brid=(ProductionID.next ());
		 head=h;
		 rhs=rhs;
		 r=(ref r);
		 pi=if (nt2string h) == (symbol2string g.start) 
		   then 1.0
		   else pi;
		 brCnt=0.0;
		 stickyScore=0.0;
		 slipperyTheta=if (nt2string h) == (symbol2string g.start) 
		   then 1.0
		   else slipperyTheta;
		 stickyTheta=if (nt2string h) == (symbol2string g.start)  
		   then 0.0
		   else stickyTheta;
		 stickyScores=(makeList (List.length rhs) 0.0);
		 stickyCnts=(makeList (List.length rhs) 0.0);} 
    in begin
	r.brs <-ref br :: r.brs;
	r.totPi <- r.totPi +. br.pi;
	
	if not (isPreterminalBaserule br) 
	then begin
	    (* Globals.dbgMsg "fg" 1 ("Changing restaurant to non-preterminal because of base-rule: " ^ (br2string br) ^ "\n");*)
	    r.preterminal <- false;
	  end;
	
	(* Add any terminals to our list of terminals *)
	(List.iter
	    (fun symb -> 
	      match symb with
		  N n -> ()
		| T t -> addT g t)
	    rhs);
	
	(* Maintain the list of structurally equivalent baserules *)
	(if (Hashtbl.mem r.prods br.rhs)
	  then let prod = (Hashtbl.find r.prods br.rhs) 
	    in (begin 
		(Hashtbl.add prod.members br.brid (Br (ref br)) );
		prod.pCount <- prod.pCount + 1; 
		prod.prodTotPi <- prod.prodTotPi +. br.pi;
	      end)
	  else let prod = {pid=(CollapsedID.next ());
			   pHead= N (br.head);
			   prodRest=ref r;
			   prodTblsCnt=0.0;
			   prodTblCnt=0.0;
			   prodTotPi= br.pi;
			   pRhs = br.rhs;
			   members = Hashtbl.create 20;
			   pCount = 0}
	    in (begin
		addProductionToTrie g prod;
		(Hashtbl.add prod.members br.brid (Br (ref br)) );
		prod.pCount <- prod.pCount + 1; 
		(Hashtbl.add r.prods br.rhs prod);
	      end));
	br;
      end

  (* Create an empty restaurant, add it to the grammar, add it's nonterminal 
     to the grammar if it does not exist yet. *)  
  let createEmptyRestaurant g ?a:(a=g.params.aDef) ?b:(b=g.params.bDef) label =
    if (Hashtbl.mem g.rsts label)
    then failwith "Attempt to create a restaurant that already exists!"
    else let r = {
	label=label;
	a=if (nt2string label) == (symbol2string g.start)
	  then 0.0
	  else a;
	b=if (nt2string label) == (symbol2string g.start)
	  then 0.0001
	  else b;
	brScore=0.0;
	tblScore=0.0;
	tbls=(Hashtbl.create 1000);
	nTbls = 0.0;
	brs=[];
	rCnt=0.0;
	totPi=0.0;
	prods=(Hashtbl.create 200);
	preterminal = true;} 
      in let _ = (addNT g label)
      in let _ = Hashtbl.add g.rsts label r
      (*in let _ = createNewBaseRule g label [(T {tName=("<"^label.nName^"_WUG>")})]
	in let _ = createNewBaseRule g label [(T {tName=("<"^label.nName^"_WUG>")}); 
	(T {tName=("<"^label.nName^"_WUG>")})]
	in let _ = createNewBaseRule g label [(T {tName=("<"^label.nName^"_WUG>")}); 
	(T {tName=("<"^label.nName^"_WUG>")});
	(T {tName=("<"^label.nName^"_WUG>")})]
	in let _ = createNewBaseRule g label [(T {tName=("<"^label.nName^"_WUG>")}); 
	(T {tName=("<"^label.nName^"_WUG>")});
	(T {tName=("<"^label.nName^"_WUG>")}); 
	(T {tName=("<"^label.nName^"_WUG>")})]*)
      in ()
	
	
  (* Update Trie with a Production *)
  let removeProductionFromTrie grammar prod =
    let rec aux trie rhs =
      match rhs with
	  [] -> let _ = Hashtbl.remove trie.productions prod.pHead
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
	let roottrie = (aux grammar.trie prod.pRhs) in
	  grammar.trie <- roottrie;
      end



 
  (* Create a baserule but don't add it to our grammar *)      
  let createDanglingBaseRule g
      ?pi:(pi=g.params.piDef) 
      ?slipperyTheta:(slipperyTheta=g.params.slipperyThetaDef)  
      ?stickyTheta:(stickyTheta=g.params.stickyThetaDef)
      h (rhs : symbol list) =
    let r = (Hashtbl.find g.rsts h)
    in {brid=(ProductionID.next ());
	head=h;
	rhs=rhs;
	r=(ref r);
	pi=pi;
	brCnt=0.0;
	stickyScore=0.0;
	slipperyTheta=slipperyTheta;
	stickyTheta=stickyTheta;
	stickyScores=(makeList (List.length rhs) 0.0);
	stickyCnts=(makeList (List.length rhs) 0.0);} 
      
  (*Get the start symbol*)
  let getStart g =
    g.start

  (* Get a unique id for each production *)
  let prodTypeID p = match p with
     (* Root r -> -1L
    |*) Tbl tbl -> !tbl.id
    | Br abr -> !abr.brid

  (* Get a unique id for each production *)
  (* IMPLEMENTS GRAMMAR INTERFACE *)
  let prodID p = p.pid

  (* Get the head of a table *)
  let tableHead t =
     !(!t.rest).label
    
  (* Test if a table is a preterminal table *)
  let isPreterminal table =
    let isTerminal s = match s with
	Val (T _) -> true
      | _ -> false
    in if (((List.length table.children) = 1) && (isTerminal (List.hd table.children)))
      then true
      else false 

  let isPreterminalRest rest = rest.preterminal
	
  (* Count the number of discontiguities present in the table structure *)
  let countDiscontig (yield : symbol list) = 
    let rec aux l total (b1, b2) = match l with
	[] -> total
      | hd::tl -> (match (b1, b2) with
	    (None, None) -> aux tl total (Some hd, None)
	  | (None, Some x) -> failwith "FragmentGrammar.countDiscontig: You have a value for the positin 2-back without 1-back"
	  | (Some x, None) -> aux  tl total (Some hd, Some x) 
	  | (Some (N n), Some (T t)) -> (match hd with
		N n ->  aux  tl total (Some hd, Some (T t) ) 
	      | T t -> aux  tl (total+1) (Some hd, Some (T t) )) (*bingo -- we found a discontiguity *)
	  | (Some x, Some y) -> aux tl total (Some hd, Some x ))
    in (aux yield 0 (None, None))

 (* Count the number of nodes in a table every which way 
     n  = number of nodes
     nt = number of nonterminals
     d = depth
     i = number of internal nodes
     l =  number of leaves
     vl = number of leaf variables
     tl = number of leaf terinals 
     *)
  let getTableSize ( l: (table ref, symbol) mem list)  =
    let rec processChildren children (n, nt, d, i, l, vl, tl) = match children with
	[] -> (n, nt, d, i, l, vl, tl)
      | hd::rest -> let (n2, nt2, d2, i2, l2, vl2, tl2) = (processNode hd) 
	in (processChildren rest ((n+n2), (nt+nt2), (max d d2), (i+i2), (l+l2), (vl + vl2), (tl+tl2)))
    and processNode n = match n with
	Ptr tbl -> let (n, nt, d, i, l, vl, tl) = (processChildren !tbl.children (0, 0, 0, 0, 0, 0, 0))
	  in (n+1, nt+1, d+1, i+1, l, vl, tl)
      | Val (T t) -> (1, 1, 0, 0, 1, 0, 1)
      | Val (N n) -> (1, 0, 0, 0, 1, 1, 0)
    in let (n, nt, d, i, l, vl, tl) = (processChildren l (0, 0, 0, 0, 0, 0, 0))
    in (n+1, nt+1, d+1, i+1, l, vl, tl)
      
  (* calculate all the stats on this table *)      
  let getTableStats ( l: (table ref, symbol) mem list)  (yield :  symbol list) =
    let (n, nt, d, i, l, vl, tl) = (getTableSize l)
    in  {nodes = n;
	 internal = i;
	 leaves = l;
	 leafv=vl;
	 leaft=tl;
	 yieldlength=vl + tl ;
	 leafrv = (float_of_int vl) /. (float_of_int (vl + tl));
	 nonterm=nt;
	 depth=d;
	 discontig=(countDiscontig yield);}

  (* Get the yield of a table *)
  let table2parseTree table =
    let rec processNode n = match n with
	Ptr tbl -> Nd ( (N !(!tbl.rest).label), (List.map processNode !tbl.children))
      | Val s -> Lf s
    in Nd ((N !(table.rest).label), (List.map processNode table.children))

 let tableChildren2parseTrees ( l: (table ref, symbol) mem list)  =
    let rec processNode n = match n with
	Ptr tbl -> Nd ( (N !(!tbl.rest).label), (List.map processNode !tbl.children))
      | Val s -> Lf s
    in (List.map processNode l)
	  
  (* Get the yield of a table *)
  let getTableYield ( l: (table ref, symbol) mem list) =
    let rec processNode n = match n with
	Ptr tbl -> List.flatten (List.map processNode !tbl.children)
      | Val (T t) -> [T t]
      | Val (N n) -> [N n]
    in List.flatten (List.map processNode l)

  (* Get the memorizations as a list of booleans*)
  let getMemBool tbl  = 
    let rec aux l = match l with
      [] -> []
    | hd :: tl -> match hd with 
	  Ptr a -> true :: (aux tl)
	| Val b -> false :: (aux tl)
    in (aux tbl.children)

  (* Create a table without using analyses *)
  let createTable (br : baserule) (children : (table ref, symbol) mem list) (mem : (symbol, symbol) mem list) (yield : symbol list) (stats : tableStats) (count : float) =
       {id=(ProductionID.next ());
	dangling = true;
	rest=(br.r);
	base=ref br;
	children=children;
	mem=mem;
	stats=stats;
	yield=yield;
	tCnt = count;
	structure = (Nd ((N !(br.r).label), (tableChildren2parseTrees children)));
	parseTrees = Hashtbl.create 100;}

  (* Create a table not yet part of our grammar from an annotated base
     rule and the list of children for this new table. *)
  let createDanglingTable (br : baserule) (children : analysis list) (mems : (symbol, symbol) mem list) =
    let alignTableChildren (aBaseRuleCh : (symbol, symbol) mem) (analysisCh : analysis) = 
      match (aBaseRuleCh, analysisCh) with
	  (Ptr (N n), Constituent ((* id, *) tbl, ch, ptree)) -> 
	    if (tableHead tbl)=n 
	    then (Ptr tbl)
	    else failwith 
	      ("FragmentGrammar.createDanglingTable: Pointer table child type and Constituent analysis node do not match in category value." ^
		  (tableHead tbl).nName ^ " " ^
		  n.nName)
 	| (Val (T t), Terminal ((*id,*) (T ter), ptree))  ->
	    if  t=ter 
	    then Val (T t)
	    else failwith 
	      ("FragmentGrammar.createDanglingTable: Terminal table child type and Terminal analysis node do not match in terminal value." ^
		  t.tName ^ " " ^
		  ter.tName)
	| (Val (N n), Constituent ((*id,*) tbl, ch, ptree)) -> 
	    if (tableHead tbl)=n 
	    then Val (N n)
	    else failwith 
	      ("FragmentGrammar.createDanglingTable: Variable table child type and Constituent analysis node  do not match in category value." ^
		  (tableHead tbl).nName ^ " " ^
		  n.nName)
	| (Val (N n1), Terminal ((*id,*) (N n2), ptree)) -> 
	    if (n1=n2) 
	    then Val (N n1)
	    else failwith 
	      ("FragmentGrammar.createDanglingTable: Variable table child and Terminal analysis node do not match in category value: " ^ 
		  n1.nName ^ " " ^
		  n2.nName)
	| (Val (T t), Constituent ((*id,*) tbl, ch, ptree)) -> 
	    failwith "FragmentGrammar.createDanglingTable: Terminal table child misaligned with Constituent analysis node."
	| (Val (T _), Terminal ((*_,*) N _, ptree)) ->
	    failwith "FragmentGrammar.createDanglingTable: Terminal table child misaligned with Terminal category analysis node."
	| (Val (N _), Terminal ((*_,*) T _, ptree)) ->
	    failwith "FragmentGrammar.createDanglingTable: Variable table child misaligned with Terminal terminal analysis node."
	| (Ptr (N n1), Terminal ((*id,*) N n2, ptree)) ->
	    failwith
	      ("FragmentGrammar.createDanglingTable: Pointer table child misaligned with Terminal nonterminal analysis node: " ^ 
		  n1.nName ^ " " ^
		  n2.nName)
	| (Ptr (N _), Terminal ((*_,*) T _, ptree)) ->
	    failwith "What?"
	| (Ptr (T _), _) ->
	    failwith "FragmentGrammar.createDanglingTable: Pointer table child  has terminal in pointer."
    in let tblChildren = (List.map2 (alignTableChildren) mems children )
    in let yield = (getTableYield tblChildren) 
    in {id=(ProductionID.next ());
	dangling = true;
	rest=br.r;
	base=ref br;
	children=tblChildren;
	mem=mems;
	yield= yield;
	stats=(getTableStats tblChildren yield);
	structure = (Nd ((N !(br.r).label), (tableChildren2parseTrees tblChildren)));
	tCnt = 0.0;
	parseTrees = Hashtbl.create 100;}

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
  let getNTs g = Hashtbl.fold (fun k v a -> k::a) g.rsts []

  (* Get all the productions in a restaurant. *)
  let getRestaurantpTypes r =
    (List.fold_left (fun a v -> (Br v) :: a) [] r.brs) @ (Hashtbl.fold (fun k v a -> (Tbl v) :: a) r.tbls [])

  let getRestaurantProductions r =
    Hashtbl.fold 
      (fun k v a -> 
	if (prodLogprob v) > 0.0 
	then begin
	    (*Globals.dbgMsg "fg" 10 ("prob: "^ (string_of_float (prodLogprob v)) ^ "\n"); *)
	    v :: a;
	  end
	else a) r.prods []
      
  (* Get all the productions in the grammar *)
  (* IMPLEMENTS GRAMMAR INTERFACE *)
  let getProductions g = 
    Hashtbl.fold (fun k v a -> (getRestaurantProductions v) @ a) g.rsts []
      
  (* Take a production and return one of its members at random *)
  let sampleProductionMember p =
    let (prods, probs, total) = Hashtbl.fold 
      (fun k v (pds, pbs, t) -> 
	let pb = (prodTypeLogprob v)
	in (v::pds, pb::pbs, (logsumexp [t;pb]))) 
      !p.members 
      ([], [], neg_infinity)
    in Utils.sampleDiscreteTotal prods probs total

  (* Implement Earley Grammar interface *)
  let nthead p = match p.pHead with
      N n -> n
    | T t -> failwith "FragmentGrammar.nthead: Attempt to access a terminal head with nthead\n"

  (*Get all the productions associated with some head*)
  let getpTypesByHead g nt =
    let r = Hashtbl.find g.rsts nt in
      getRestaurantpTypes r
  
  (*Get all the productions associated with some head*)
  (* IMPLEMENTS GRAMMAR INTERFACE *)
  let getProdsByHead g nt =
    let r = Hashtbl.find g.rsts nt in
      getRestaurantProductions r
  
  (* Get a nonterminal by id *)
  (* IMPLEMENTS GRAMMAR INTERFACE *)
  let getNonterminal g i =
    let num = i in
      match Hashtbl.fold (fun k v a -> if v = num then Some k else a) g.nts None with
    Some x -> x 
  | None -> failwith ("No nonterminal has code: " ^ (string_of_int i))
 
  (* IMPLEMENTS GRAMMAR INTERFACE *)
  let isROOT p = if p.pid = (-1L) then true else false
        
  (* Does this terminal generate this word *)
  (* IMPLEMENTS GRAMMAR INTERFACE *)
  let generatesWord s t = 
    if (s = t.tName)
    then begin (* print_string (s ^ " " ^ t.tName); *)true end
    else false
    
  (* Get the immediate children of a table *)    
  let getTableChildren t =
    t.children
      
  (*Is this an active table in the grammar?*)
  let activeTable t =
    let rest = !(t.rest) in
      Hashtbl.mem rest.tbls t.id

  (* Test whether it is "safe" to reseat an analysis sitting at
     the source table to the target table in this
     grammar. Reseating is safe if it cannot break any of other
     pointers in the cache. In other words moves
     Ptr X -> Ptr X are allowed, as are moves Ptr N -> Var NT or
     Var NT -> Var NT, however moves Var NT -> Ptr X are only safe
     if the analysis happens to be sitting at Ptr X in the first 
     place.*)
  let safeReseat (ana : analysis) (targ : table) = 
    let testPosition analysis (source, target) = match (analysis, source, target) with
	Terminal ((*_,*) s1, pt), Val (T s2), Val (T s3) when s2=s3 -> true       (*If all have same terminal*)
      | Constituent ((*_,*) t1, _, pt), Val (N n1), Val (N n2) when n1=n2 -> true   (*If the we move from a variable to a variable*)
      | Constituent ((*_,*) t1, _, pt), Val (N n), Ptr t2 when !t1 == !t2 -> true   (*If the we move to the same pointer from a variable*)
      | Constituent ((*_,*) t1, _, pt), Ptr t2, Val (N n) when (tableHead t2) = n -> true (*If we move to a variable with the same head *)
      | Constituent ((*_,*) t1, _, pt), Ptr t2, Ptr t3 when !t2 == !t3 -> true      (*If we preserve pointers*)
      | (_, _, _) -> false
    in match ana with
	Terminal _ -> false
      | Constituent ((*id,*) tbl, ch, pt) -> List.fold_left2 (fun a v1 v2 -> if not a then false else (testPosition v1 v2)) true ch (List.combine !tbl.children targ.children) 

  (* Get the tables in a restaurant based on some base rule *)
  let getBRTables rest br =
    (Hashtbl.fold (fun k v a -> if !(!v.base) == br then v :: a else a) rest.tbls [])

  (* Get all the safe reseats of a table *)
  let getSafeReseats analysis = match analysis with
      Terminal _ -> []
    | Constituent ((*id,*) tbl, ch, pt) -> 
  let rest = !(!tbl.rest)
  in let br = !(!tbl.base)
  in let mems = (enumerateAnnotations br.rhs) 
  in let oldTbls = List.fold_left (fun a v -> if (safeReseat analysis !v) then Constituent ((* (AnalysisID.next ()),*) v, ch, pt)::a else a) [] (getBRTables rest br)
  in let newTbls = List.fold_left (fun a v -> (Constituent ((* (AnalysisID.next ()),*) ref (createDanglingTable br ch v), ch, pt)) :: a ) [] mems
  in oldTbls @ newTbls 


  (************************************************************************)
  (*                           Scoring  Functions                         *)                       
  (* ---------------------------------------------------------------------*)
  (*                         Add and remove tables, etc.                  *)
  (************************************************************************)

  let numCustomers table =
    table.tCnt

  (* Posterior score on an adaptor grammar *)
  let scoreGrammar g =
    (* let tm1 = Sys.time () in *)
    let score =   Hashtbl.fold (fun k v a -> a +. scoreRestaurant v )  g.rsts 0.0 in
    (* let tm2 =Sys.time () in *)
      begin
	(* Globals.dbgMsg "fg" 8 ("Grammar rescored in " 
				^ (string_of_float (tm2-.tm1)) 
				^ " seconds.\n"); *)
	score
      end
      
  (************************************************************************)
  (*                            Bookeeping  Functions                     *)                       
  (* ---------------------------------------------------------------------*)
  (*                         Add and remove tables, etc.                  *)
  (************************************************************************)
      
  (* Decremement an existing table by n, remove it if it's count falls below zero *)
  let rec decrExistingTable g (tbl : table) pto n = 
    if tbl.dangling = false
    then
      let rest = !(tbl.rest) 
      in let prod = Hashtbl.find rest.prods tbl.yield
      in begin


	  rest.rCnt <- rest.rCnt -. n;
	  tbl.tCnt <- tbl.tCnt -. n;                 	  
	  prod.prodTblsCnt <- prod.prodTblsCnt -. n;

	  (* If we have emptied the table we need to remove it *)
	  (if tbl.tCnt = 0.0 
	    then  begin
		(* Rescore the restaurant -- do this first as the recursive
		   call to removeTable can remove more tables in this
		   restaurant and thus screw up rest.nTbls *)
		for count = 1 to ((int_of_float n) - 1) do
		  let numToSubtr = n -. (float_of_int count)
		  in rest.tblScore <- rest.tblScore -. log (((tbl.tCnt +. numToSubtr) -. rest.a) /. (rest.rCnt +. rest.b));
		done;

		rest.tblScore <- rest.tblScore -. log ((((rest.nTbls-.1.0) *. rest.a) +. rest.b) /. (rest.rCnt +. rest.b));

		removeTable g tbl; 

		(* DEBUGGING SCORING -- LEAVE ME IN TO TEST CHANGES

		   let newTbls = Hashtbl.copy rest.tbls
	       	   in let _ = Hashtbl.remove newTbls tbl.id
		   in let compscore = (pitmanyor rest.a rest.b (Array.of_list (Hashtbl.fold (fun k v a -> (int_of_float !v.tCnt) :: a) newTbls [])))
		   in  begin
		   if (abs_float (compscore -. rest.tblScore)) > 0.00001
		   then Globals.dbgMsg "fg" 10 (("Decremented new table score: "
		   ^ " Incremental: ") ^ (string_of_float rest.tblScore) 
		   ^ (" Function: ")    ^ (string_of_float compscore) ^ "\n");
		   end; *)
		
	      end
	    else begin

		for count = 1 to (int_of_float n)  do
		  let numToSubtr = n -. (float_of_int count)
		  in rest.tblScore <- rest.tblScore -. log (((tbl.tCnt +. numToSubtr) -. rest.a) /. (rest.rCnt +. rest.b));
		done;

		
	      (* DEBUGGING SCORING -- LEAVE ME IN TO TEST CHANGES
		 let compscore = (pitmanyor rest.a rest.b (Array.of_list (Hashtbl.fold (fun k v a -> (int_of_float !v.tCnt) :: a) rest.tbls [])))
		 in begin
		 if (abs_float (compscore -. rest.tblScore)) > 0.00001
		 then Globals.dbgMsg "fg" 10 (("Decremented table score: "
		 ^ " Incremental: ") ^ (string_of_float rest.tblScore) 
		 ^ (" Function: ")    ^ (string_of_float compscore) ^ "\n");
		 end; *)
	      end);

	  (* Update the count of the structure corresponding to this table*)
	  (let strucCnt = Hashtbl.find g.structures tbl.structure
	  in let newCnt =  (strucCnt -. n (*1.0*) )
	  in if newCnt = 0.0 then Hashtbl.remove g.structures tbl.structure
	    else Hashtbl.replace g.structures tbl.structure newCnt);
	  
	(*  Globals.dbgMsg  "mh" 1  ("\nREMOVING: " ^ (Int64.to_string tbl.id) ^ "\n" 
				    ^ (table2string tbl) ^ "\n\tparse tree: " 
				    ^ (parseTree2string pt) ^ "\n");*)
	
	  (match pto with 
	      Some pt ->
		(* Manipulate structure counts *)
		if Hashtbl.mem tbl.parseTrees pt
		then let ptCnt = Hashtbl.find tbl.parseTrees pt
		  in if ptCnt = 1.0
		    then begin
			Hashtbl.remove tbl.parseTrees pt;
		      end
		    else begin
			Hashtbl.replace tbl.parseTrees pt (ptCnt -. n (*1.0*) );
		      end
		else let _ =  Globals.dbgMsg  "mh" 1  ("FragmentGrammar.decrExistingTable: Attempt to decrement a structure type which does not exist in the grammar!:\n\ttable: " 
							^ (table2string tbl) ^ "\n\tparse tree: " 
							^ (parseTree2string pt))
		  in failwith "See debug file for information."
	    | None -> ());

	    
	  (* Sanity check *)
	  if tbl.tCnt < 0.0
	  then failwith "FragmentGrammar.decrExistingTable: Somehow you have managed to make a table's count less than 0!";
	    
	end
    else failwith ("FragmentGrammar.decrExistingTable: Attempt to decrement a table which is not in the grammar: " ^ (table2string tbl))
  and removeTable g tbl = 
    let handleChild  (tb : (table ref, symbol) mem)  = match tb with
	Ptr tb  -> (decrExistingTable g !tb None 1.0) 
      | Val  x -> ()
    in let br = !(tbl.base) and rest = !(tbl.rest)
    in begin

	tbl.dangling <- true;
	(Hashtbl.remove rest.tbls tbl.id);                (* remove this table from the restaurant *)
	rest.nTbls <- rest.nTbls -. 1.0;
	br.brCnt <- br.brCnt -. 1.0;                      (* Update the baserule count *)

	rest.brScore <- rest.brScore -.	log (( br.pi +. br.brCnt) /. (rest.nTbls +. rest.totPi));
  
	(* DEBUGGING SCORING -- LEAVE ME IN TO TEST CHANGES 
	let compscore = (rescoreBaseRules rest)
	in begin
	    if (abs_float (compscore -. rest.brScore)) > 0.00001
	    then Globals.dbgMsg "fg" 10 ("Decremented baserule score: " 
	   ^ (" Incremental: ") ^ (string_of_float rest.brScore) 
					  ^ (" Function: ") ^ (string_of_float compscore) 
					  ^"\n");
	  end;*) 

	(decrStickyCounts br tbl);

	(* Remove the corresponding table from the production *)
	let prod = Hashtbl.find rest.prods tbl.yield 
	in begin
	    (Hashtbl.remove prod.members tbl.id);
	    prod.pCount <- prod.pCount - 1;
	    prod.prodTblCnt <- prod.prodTblCnt -. 1.0;

	    (* If this production has no members remove it. *)
	    (if prod.pCount < 1
	      then begin
		  removeProductionFromTrie g prod; 
		  Hashtbl.remove rest.prods tbl.yield;
		end)
	  end;

	  (* make sure we deal with any children which are in the grammar *)
	  List.iter handleChild tbl.children;
      
      end
  and decrStickyCounts br tbl = 
    let aux mem =  match mem with
	Val (T _) -> 0
      | Val (N _) -> 0
      | Ptr _ -> 1
    in let newCounts = List.map2 (fun v1 v2 -> (v1 -. (float_of_int (aux v2))) ) br.stickyCnts tbl.mem 
    in let dispatch oldCount mem =  match mem with
	Val (T _) -> 0.0
      | Val (N _) ->  log ((br.slipperyTheta +.  (br.brCnt -. oldCount)) /. (br.brCnt +. (br.stickyTheta +. br.slipperyTheta)))
      | Ptr _ -> 
	  begin
	    (* Globals.dbgMsg "fg" 1 ("term: " ^ "( " 
	       ^ (string_of_float br.stickyTheta) ^ " + " 
	       ^ (string_of_float oldCount) ^")/(" 
	       ^ (string_of_float br.brCnt) ^ " + " 
	       ^ (string_of_float (br.stickyTheta +. br.slipperyTheta)) ^")\n");*)
	    log ((br.stickyTheta +.  oldCount) /. (br.brCnt +. (br.stickyTheta +. br.slipperyTheta)));
	  end
    in let updates = List.map2 (fun oldCount mem ->  (dispatch oldCount mem)) newCounts tbl.mem
    in let newScores = List.map2 (fun oldscore update -> (oldscore -. update)) br.stickyScores updates
    in begin 
	
	(br.stickyScores <- newScores);
	(br.stickyCnts <- newCounts);
	(br.stickyScore <- List.fold_left (+.) 0.0 newScores);
	
      (* DEBUGGING SCORING -- LEAVE ME IN TO TEST CHANGES
	 let compscores = (List.map2 
	 (fun cnt sym -> match sym with  
	 N n -> (lpolya2 [|br.stickyTheta; br.slipperyTheta|] [|cnt; (br.brCnt -. cnt)|] )
	 | T t -> 0.0)  
		   br.stickyCnts 
	 br.rhs)	 
	 in let compscore = List.fold_left (+.) 0.0 compscores in begin
	 if (abs_float (compscore -. br.stickyScore)) > 0.00001
	 then Globals.dbgMsg "fg" 10 ("Decremented sticky scores:"
	 ^ ("\n\tIncremental: ") ^ (string_of_float br.stickyScore) 
	 ^ ("\n\tFunction: ")^ (string_of_float compscore)
	 ^ ("\n\tbr.brCnt: ")^ (string_of_float br.brCnt)
	 ^ ("\n\tSticky theta: ")^ (string_of_float br.stickyTheta)
	 ^ ("\n\tslippery theta: ")^ (string_of_float br.slipperyTheta)
	 ^ ("\n\tcounts:" ^ (List.fold_left (fun a v -> a ^ " " ^ (string_of_float v)) "" br.stickyCnts))
	 ^ ("\n\told counts:" ^ (List.fold_left (fun a v -> a ^ " " ^ (string_of_float v)) "" oldCounts))
	 ^ ("\n\tUpdates: " ^ (List.fold_left (fun a v -> a ^ " " ^ (string_of_float v)) "" updates))
	 ^ ("\n\tOld Scores: " ^ (List.fold_left (fun a v -> a ^ " " ^ (string_of_float v)) "" oldScores))
	 ^ ("\n\tIncremental Scores: " ^ (List.fold_left (fun a v -> a ^ " " ^ (string_of_float v)) "" newScores))
	 ^ ("\n\tFunction Scores: " ^ (List.fold_left (fun a v -> a ^ " " ^ (string_of_float v)) "" compscores))
	 ^"\n");
	 end *)
      end 
         
  (* Incremement an existing table by n *)
  let rec incrExistingTable g tbl pto n = 
    let rest = !(tbl.rest)
    in begin

	(* We have to increment counts first thing. If this table is a
	   new one, and it has pointers to other tables which are also
	   new, and one of those tables is in the same restaurant then 
	   their scores are going to depend on having correctly updated 
	   rest.rCnt *before* recursing in the call to addTable. *)

	tbl.tCnt <- tbl.tCnt +. n;         
	rest.rCnt <- rest.rCnt +. n;

	(if tbl.dangling = true
	  then begin
	      (* new table --- remember to subtract back off the increments above *)
	      rest.tblScore <- rest.tblScore +. log (((rest.nTbls *. rest.a) +. rest.b) /. ((rest.rCnt-.1.0) +. rest.b));	      
	      
	      for count = 1 to ((int_of_float n) - 1) do
		let numToAdd = n -. (float_of_int count)
		in rest.tblScore <- rest.tblScore +. log (((tbl.tCnt-.numToAdd) -. rest.a) /. ((rest.rCnt-.numToAdd) +. rest.b));
	      done;

	      addTable g tbl;
	    end
	  else 
	    begin
	      for count = 0 to ((int_of_float n) - 1) do
		let numToAdd = n -. (float_of_int count)
		in rest.tblScore <- rest.tblScore +. log (((tbl.tCnt-.numToAdd) -. rest.a) /. ((rest.rCnt-.numToAdd) +. rest.b));
	      done;
	    end);

	
	(let prod = Hashtbl.find rest.prods tbl.yield
	  in prod.prodTblsCnt <- prod.prodTblsCnt +. n (*1.0*)); 
	
	(if Hashtbl.mem g.structures tbl.structure
	  then let strucCnt = Hashtbl.find g.structures tbl.structure
	    in Hashtbl.replace g.structures tbl.structure (strucCnt +. n (*1.0*))
	  else Hashtbl.add g.structures tbl.structure n (*1.0*));

	(* Globals.dbgMsg  "mh" 1  ("\nADDING: "^ (Int64.to_string tbl.id) ^ "\n" 
				  ^ (table2string tbl) ^ "\n\tparse tree: " 
				  ^ (parseTree2string pt) ^ "\n");*)
	
	(match pto with
	    Some pt -> 
	      if Hashtbl.mem tbl.parseTrees pt
	      then begin
		  Hashtbl.replace tbl.parseTrees pt ((Hashtbl.find tbl.parseTrees pt) +. n);
		end
	      else begin
		  Hashtbl.add tbl.parseTrees pt n;
		end
	  | None -> ());
	
      end
  and addTable g tbl = 
    (* When we create a new table with pointers to sub tables we need
       to add one count to those tables which are now pointed
       to. Tables which are variables in an analysis will get
       updated normally. *)
    let handleChild  (tb : (table ref, symbol) mem)   = match tb with
	Ptr tb  -> (incrExistingTable  g !tb None 1.0) (* we only add a single count to the pointed-to table b/c we only pay to create the pointer *)
      | Val  x -> ()
    in  let br = !(tbl.base) and rest = !(tbl.rest)
    in begin	
	  
	  tbl.dangling <- false;
	  
	  rest.brScore <- rest.brScore +. log ((br.pi +. br.brCnt) /. (rest.nTbls +. rest.totPi));
	  
	  (* Recalculate sticky count scores -- this must be done before brCnt is incremented *)
	  (incrStickyCounts br tbl);
	  
	  rest.nTbls <- rest.nTbls +. 1.0;
	  (Hashtbl.add rest.tbls tbl.id (ref tbl));     (* Add this table to the restaurant *)
	  br.brCnt <- br.brCnt +. 1.0;                  (* Update the baserule count *)
	 
	  (* DEBUGGING SCORING -- LEAVE ME IN TO TEST CHANGES 
	     let (als, cs) = List.fold_left (fun (a,c) br -> (!br.pi::a, !br.brCnt::c)) ([], []) rest.brs
	     in let compscore = lpolya2 (Array.of_list als) (Array.of_list cs)
	     in begin
	     if (abs_float (compscore -.  rest.brScore)) > 0.00001
	     then Globals.dbgMsg "fg" 10 ("Incremented base rule scores: "
	     ^ "Incremental: " ^ (string_of_float rest.brScore) 
	     ^ "Function: "^ (string_of_float compscore) 
	     ^ "\n\tCounts: "^ (List.fold_left (fun a v-> a ^ " " ^ (string_of_float v)) "" cs)
	     ^ "\n\tbr.pi: "^ (string_of_float br.pi)
	     ^ "\n\tbr.brCnt: "^ (string_of_float br.brCnt)
	     ^ "\n\tprevious br.brCnt: "^ (string_of_float (br.brCnt-.1.0))
	     ^ "\n\trest.nTbls " ^ (string_of_float (rest.nTbls))
	     ^ "\n\tprevious rest.nTbls " ^ (string_of_float (rest.nTbls-.1.0))
	     ^ "\n\trest.totPi " ^ (string_of_float (rest.totPi))
	     ^ "\n\tincrement: " ^ (string_of_float (log ((br.pi +. (br.brCnt-.1.0)) /. ((rest.nTbls-.1.0) +. rest.totPi))))
      	     ^"\n");
	     end; *)
	  
	  List.iter handleChild tbl.children;
	  (* DEBUGGING SCORING -- LEAVE ME IN TO TEST CHANGES 
	     let compscore = rescoreStickiness br	 
	     in begin
	     if (abs_float (compscore -. br.stickyScore)) > 0.00001
	     then Globals.dbgMsg "fg" 10 ( "Incremented Sticky Scores: "
	     ^  (" Incremental: ") ^ (string_of_float br.stickyScore) 
	     ^ ("\tFunction: ") ^ (string_of_float compscore) 
	     ^"\n");
	     end;*)
	  
	  (* Deal with production bookeeping *)
	  if Hashtbl.mem rest.prods tbl.yield
	  then let prod = Hashtbl.find rest.prods tbl.yield 
	    in begin 
		Hashtbl.add prod.members tbl.id (Tbl (ref tbl)); 
		prod.pCount <- prod.pCount + 1; 
		prod.prodTblCnt <- prod.prodTblCnt +. 1.0;
	      end
	  else let prod = {pid=(CollapsedID.next ());
			   pHead=N(rest.label);
			   prodRest=ref rest;
			   prodTblsCnt=0.0;
			   prodTblCnt=1.0;
			   prodTotPi=0.0;
			   pRhs = tbl.yield;
			   members = Hashtbl.create 20;
			   pCount = 1;} 
	    in begin
		addProductionToTrie g prod; 
		Hashtbl.add prod.members tbl.id (Tbl  (ref tbl)); 
		(Hashtbl.add rest.prods tbl.yield prod);
	      end;
	    
      end
  and incrStickyCounts  br tbl = 
    let aux mem =  match mem with
	Val (T _) -> 0
      | Val (N _) -> 0
      | Ptr _ -> 1
    in let newCounts = List.map2 (fun v1 v2 -> (v1 +. (float_of_int (aux v2))))  br.stickyCnts tbl.mem 
    in let dispatch oldCount mem =  match mem with
	Val (T _) -> 0.0
      | Val (N _) ->  log ((br.slipperyTheta +.  (br.brCnt -. oldCount)) /. (br.brCnt +. (br.stickyTheta +. br.slipperyTheta)))
      | Ptr _ -> log ((br.stickyTheta +.  oldCount) /. (br.brCnt +. (br.stickyTheta +. br.slipperyTheta))) 
    in let updates = List.map2 (fun oldCount mem ->  (dispatch oldCount mem)) br.stickyCnts tbl.mem
    in let newScores = List.map2 (fun oldscore update -> (oldscore+.update)) br.stickyScores updates
    in begin 
	(br.stickyScores <- newScores);
	(br.stickyCnts <- newCounts);	
	(br.stickyScore <- List.fold_left (+.) 0.0 newScores);
      end 

  (************************************************************************
   *                            Analysis  Functions                       *                       
   * ---------------------------------------------------------------------*
   * These functions create and manipulate analyses.                      *
   ************************************************************************)

  
  (* This provides a general purpose tree fold for dealing with
     analyses. Note that it does a right most depth first walk. *)
  let foldAnalysis tFunct pFunct vFunct analysis =
    let rec processNode (a : analysis) (tl : (table ref, symbol) mem) = match (a, tl) with
	(Terminal ((*id,*) term1, pt), Val term2) -> 
	  if term1=term2 
	  then (tFunct pt term1)
	  else failwith "Terminals do not align"
      | (Constituent ((*id,*) t,l, pt), Ptr tbl) ->
	  if !t == !tbl
	  then (pFunct pt t (List.map2 processNode l !t.children))
	  else failwith "Pointer does not align"
      | (Constituent ((*id,*) t,l, pt), Val (N n)) ->
	  if n = !(!t.rest).label 
	  then (vFunct pt t (List.map2 processNode l !t.children))
	  else failwith "Variable does not align"
      | (_,_) -> failwith ("FragmentGrammar.foldAnalysis: Unaligned tree")
    in match analysis with
	Constituent ((*id,*) t,l, pt) -> 
	  (vFunct pt t (List.map2 processNode l !t.children))
      | _ -> failwith "Must begin recursion with a variable"       
    
  (* Iterate over an analysis applying a unit-return function to each node *)
  let iterAnalysis tFunct pFunct vFunct analysis =
    let rec processNode (a : analysis) (tl : (table ref, symbol) mem) = match (a, tl) with
	(Terminal ((*id,*) term1, pt), Val term2) -> 
	  if term1=term2 
	  then (tFunct pt term1)
	  else failwith "Terminals do not align"
      | (Constituent ((*id,*) t,l, pt), Ptr tbl) ->
	  if !t == !tbl 
	  then  begin (List.iter2 processNode l !t.children); (pFunct pt t l) end
	  else failwith "Pointer does not align"
      | (Constituent ((* id,*) t,l, pt), Val (N n)) ->
	  if n = !(!t.rest).label 
	  then begin (List.iter2 processNode l !t.children); (vFunct pt t l) end
	  else failwith "Variable does not align"
      | _, _ -> failwith ("FragmentGrammar.iterAnalysis: Unaligned tree." ^ " analysis node: ")
    in match analysis with
	Constituent ((*id,*) t,l, pt) -> 
    begin (List.iter2 processNode l !t.children); (vFunct pt t l) end 
      | _ -> failwith "Must begin recursion with a variable"
    
  (* One layer deep dispatch analysis matching *)
  let matchAnalysis tFunct pFunct vFunct analysis table =
    let rec processNode (a : analysis) (tl : (table ref, symbol) mem) = match (a, tl) with
	(Terminal ((*id,*) term1, pt), Val term2) -> 
	  if term1=term2 
	  then (tFunct pt term1)
	  else failwith "Terminals do not align"
      | (Constituent ((*id,*) t,l, pt), Ptr tbl) ->
	  if !t == !tbl
	  then begin (pFunct pt t l) end
	  else failwith "Pointer does not align"
      | (Constituent ((*id,*) t,l, pt), Val (N n)) ->
	  if n = !(!t.rest).label 
	  then begin (vFunct pt t l) end
	  else failwith "Variable does not align"
      | (_,_) -> failwith ("FragmentGrammar.matchAnalysis: Unaligned tree")
    in processNode analysis table
     

  let rec removeAnalysisNode g analysis count =
    match analysis with  
	Constituent ((* id,*) tbl, children, pt)  -> (decrExistingTable g !tbl (Some pt) count)
      | _ -> () 

  (* Remove an analysis from the grammar. *)
  let removeAnalysis g a count =
    let tFunct pt s = ()
    and pFunct pt t children = ()
    and vFunct pt t children = 
      begin 
(*	(Globals.dbgMsg "fg" 10 ("Removing analysis variable node:\n\tid: "^ (Int64.to_string id) ^ "\n\ttable: " ^(table2string !t) ^ "\n"));*)
	(decrExistingTable g !t (Some pt) count);
      end 
    in iterAnalysis tFunct pFunct vFunct a


  (* Add a single analysis node to our grammar. *)
  let rec addAnalysisNode g analysis count = 
    match analysis with  
	Constituent ((*id,*) tbl, children, pt) ->  (incrExistingTable g !tbl (Some pt) count)
      | _ -> ()
	  
  (* Add an analysis to our grammar *)
  let addAnalysis g a count =
    let tFunct pt s = ()
    and pFunct pt t children = ()
    and vFunct pt t children= addAnalysisNode g (Constituent (t, children, pt)) count
    in iterAnalysis tFunct pFunct vFunct a

  (* Reseat an analysis to a table. When we take a leaf from a pointer
     to a variable add a count, and when we take a leaf from a
     variable to a pointer subtract a count. N.B. in the case that
     we are deleting our old table entirely this ensures that we don't
     subtract the places where the pointer turned into a
     leaf. Likewise when we are adding our new table this ensures
     that we count old variables which turn into pointers only
     once for the new pointer.  *)
  let reseat g oldAnalysis newAnalysis count =
    let bookKeep (oAnaChild, nAnaChild) (oldTableChild, newTableChild) = match (oldTableChild, newTableChild) with
	(Ptr otl, Val (N n)) -> (addAnalysisNode g nAnaChild count)
      | (Val (N o), Ptr ntl) -> (removeAnalysisNode g oAnaChild count)
      | _ -> ()
    in match (oldAnalysis, newAnalysis) with
	Constituent ((*_,*) otbl, och, opt), Constituent ((*_,*) ntbl, nch, npt) ->
	  begin
	    List.iter2 bookKeep (List.combine och nch) (List.combine !otbl.children !ntbl.children);
	    removeAnalysisNode g oldAnalysis count;
	    addAnalysisNode  g newAnalysis count;
	   (* (Globals.dbgMsg "fg" 8 ("Reseated from table in: " ^ !(!otbl.rest).label.nName ^ " to table in: " ^ !(!ntbl.rest).label.nName ^ "\n")); *)
	  end   
      | _ -> failwith "Must reseat an analysis from an analysis to an analysis."
	  
  (*Score an analysis from expected values. *)
  let scoreAnalysis g a =
    let tFunct pt s = 0.0
    and pFunct pt t children =   (List.fold_left (fun a e -> a +. e) 0.0 children)
    and vFunct pt t children =
      let  nodeScore = (if !t.dangling = true then (scoreTableCreation g !t) else prodTypeLogprob (Tbl t))
      in begin 
	  (* (Globals.dbgMsg "fg" 8 ("\nScoring node with table:\n\t" ^ (table2string !t) ^ "\twith score " ^ (string_of_float nodeScore) ^ "\n"));*)
	  (List.fold_left (fun a e -> a +. e) 0.0 children) +. nodeScore;
	end
    in foldAnalysis tFunct pFunct vFunct a
      
  (* Get the next analysis ID *)
  let getAnalysisID () =
    AnalysisID.next ()
  
  let analysisYield a = 
    let tFunct pt s =  [s] (* [s.tName] *)
    and pFunct pt t children =  (List.flatten children)
    and vFunct pt t children =  (List.flatten children)
    in foldAnalysis tFunct pFunct vFunct a

  let analysisYield2string ana =
    List.fold_left (fun a v -> a ^ " " ^ (symbol2string v)) "" (analysisYield ana)

  (* Get an analysis corresponding to a table *)
  let rec getTableAnalysis table = 
    let processChild c = match c with
	Ptr tbl -> getTableAnalysis !tbl
      | Val x -> Terminal ((*(getAnalysisID ()),*) x, (Lf x)) 
    in let aChildren = List.map processChild table.children
    in  Constituent ((*(getAnalysisID ()),*) ref table, aChildren, table.structure) 
    

  (************************************************************************
   *                            Iterators                                 *                       
   * ---------------------------------------------------------------------*
   *                                                                      *
   ************************************************************************)

  let foldRests f g startall =
      Hashtbl.fold f g.rsts startall

  (* iterate through the tables of this restaurant *)
  let iterRests g f =
    Hashtbl.iter (fun k v -> (f v)) g.rsts 


  (*fold over the tables in some restaurant *)
  let foldRestTables f rest startrest = (Hashtbl.fold (fun k v a -> (f !v a)) rest.tbls startrest)

  (*fold over all the tables in a grammar *)
  let foldTables f g startall  =
    let foldRestTables f rest startrest = (Hashtbl.fold (fun k v a -> (* let _ = Globals.dbgMsg "mh-table" 10  "Table" in *) (f !v a)) rest.tbls startrest)
    in Hashtbl.fold (fun k v a -> (foldRestTables f v a) ) g.rsts startall 
 

  (*fold over all the tables in a grammar *)
  let foldAnalyses f g startall  =
    let foldRestTables f rest startrest = (Hashtbl.fold (fun k v a -> (f v a)) rest.tbls startrest)
    in Hashtbl.fold (fun k v a -> (foldRestTables f v a) ) g.rsts startall 


  (************************************************************************
   *                            Forward Sampling Functions                *                       
   * ---------------------------------------------------------------------*
   *                                                                      *
   ************************************************************************)

  (* Expand the internal structure of a table in place in an analysis
     -- N.B. be careful not to pass an already expanded analysis into
     this function, it is very fragile and doesn't do enough error checking. *)
  let expandTable (grammar : grammar) (tbl : table ref) (children : analysis list) =
    let rec getPtrees (cl : analysis list) = match cl with
	[] -> []
      | Terminal (term, pt)::tl -> pt :: (getPtrees tl)
      | Constituent (t,l, pt)::tl -> pt :: (getPtrees tl)
    in let stack = ref children in
    let rec consume (leaves :  (table ref, symbol) mem list) = 
      match (!stack, leaves) with
	  ([], []) -> []
	| (_, []) -> []
	| (Terminal (term, pt)::_, Val s::tl) when s=term -> 
	    stack := List.tl !stack; 
	    Terminal (s, pt) :: (consume tl)
	| (Constituent (t,l, pt)::_,  Val (N v)::tl) when (pTypeHead (Tbl t)) = v ->
	    stack := List.tl !stack; 
	    Constituent (t, l, pt) :: (consume tl)
	| (_, (Ptr tbl)::tl) ->
	    let newAnaChildren =  (consume (getTableChildren !tbl )) in
	    let pTree = Nd ((N !(!tbl.base).head), (getPtrees newAnaChildren))
	    in Constituent (tbl, newAnaChildren, pTree) :: (consume tl) 
	| (_, _) -> failwith "FragmentGrammar.expandTable: Unknown Combination of Table children and analysis children"
    in let anaCh = consume (getTableChildren !tbl)
    in Constituent (tbl, anaCh, Nd ((N (tableHead tbl)), (getPtrees anaCh)))

  (*Compute the expect probability of a position in the RHS of a sticky rule *)
  let sampleStickyDecisionPosition br symbol stickyCnt =
    let grandTotal = (br.brCnt +. br.slipperyTheta +. br.stickyTheta)
    and slipperyCnt = (br.brCnt -. stickyCnt)
    in let choice= sampleIndex [log ((slipperyCnt +. br.slipperyTheta) /. grandTotal);  log ((stickyCnt +. br.stickyTheta)    /. grandTotal)]
    in if (choice = 0)
      then (Val symbol)
      else (Ptr symbol)

  (*Compute the expect probability of a position in the RHS of a sticky rule *)
  let mAPStickyDecisionPosition br symbol stickyCnt =
    let grandTotal = (br.brCnt +. br.slipperyTheta +. br.stickyTheta)
    and slipperyCnt = (br.brCnt -. stickyCnt)
    in if (log ((slipperyCnt +. br.slipperyTheta) /. grandTotal)) >  (log ((stickyCnt +. br.stickyTheta)    /. grandTotal))
      then (Val symbol)
      else (Ptr symbol)

  (* sample a series of sticky decisions *)
  let rec sampleStickyDecisions br rhs stickyCnts instructions = 
    match (rhs, stickyCnts, instructions) with
	([], [], []) -> []
      | (symbol::symbols, count::counts, instruction::instructions) ->
	  (match instruction with
	      true ->   (Val symbol) :: (sampleStickyDecisions br symbols counts instructions) (* If true then don't try to sample this *)
	    | false -> (sampleStickyDecisionPosition br symbol count) :: (sampleStickyDecisions br symbols counts instructions)) (* If false, then do try to sample this *)
      | _ -> failwith "FragmentGrammar.sampleStickyDecisionPosition : the lengths of your sticky count list and your mem list do not match" 

  (* sample a series of sticky decisions *)
  let rec mAPStickyDecisions br rhs stickyCnts instructions = match (rhs, stickyCnts, instructions) with
      ([], [], []) -> []
    | (symbol::symbols, count::counts, instruction::instructions) ->
	(match instruction with
	    true ->   (Val symbol) :: (sampleStickyDecisions br symbols counts instructions) (* If true then don't try to sample this *)
	  | false -> (mAPStickyDecisionPosition br symbol count) :: (mAPStickyDecisions br symbols counts instructions)) (* If false, then do try to sample this *)
    | _ -> failwith "FragmentGrammar.sampleStickyDecisionPosition : the lengths of your sticky count list and your mem list do not match" 
	

  (* sample a series of sticky decisions *)
   let rec sampleStickyDecisionsOld br rhs stickyCnts  = match (rhs, stickyCnts) with
     ([], []) -> []
     | (symbol::symbols, count::counts) ->
     (match symbol with
     (T t) ->   (Val symbol) :: (sampleStickyDecisionsOld br symbols counts) (* If true then don't try to sample this *)
     | (N n) -> (sampleStickyDecisionPosition br symbol count) :: (sampleStickyDecisionsOld br symbols counts)) (* If false, then do try to sample this *)
     | _ -> failwith "FragmentGrammar.sampleStickyDecisionPosition : the lengths of your sticky count list and your mem list do not match"  
 

  

  (************************************************************************
   *                         Stats functions                              *                       
   * ---------------------------------------------------------------------*
   * Some functions for computing various statistics on the grammar.      *
   ************************************************************************)

  (* Count various things about the analysis --
     returns: (numNodes, numTables, yieldLength, yieldAttributions, meanShared) *)
  let getAnalysisStats a = 
    let rec replace a l = match l with
	[] -> []
      | hd :: tl -> 
	  let nw = (if hd = -10L then a else hd)
	  in nw :: (replace a tl) 
    in let tFunct pt s =   (1.0, 0.0, 1.0, [-10L], [])
    and pFunct pt tbl children = 
      let (n, t, y, ya, m) = 
	List.fold_left 
	  (fun  (n1, t1, y1, ya1, m1)  (n2, t2, y2, ya2, m2) -> 
	    ((n1+.n2), (t1+.t2), (y1+.y2), (ya1 @ ya2), (m1 @ m2))) 
	  (0.0, 0.0, 0.0 , [], []) 
	  children
      in ((n+.1.0), t, y, ya, m)	      
    and vFunct pt tbl children =  
      let (n, t, y, ya, m) = 
	List.fold_left 
	  (fun  (n1, t1, y1, ya1, m1)  (n2, t2, y2, ya2, m2) -> 
	    (n1+.n2, t1+.t2, y1+.y2, (ya1 @ ya2), (m1 @ m2)))
	  (0.0, 0.0, 0.0, [], []) 
	  children
      in ((n+.1.0), (t+.1.0), y, (replace !tbl.id ya),  (!tbl.tCnt::m))
    in foldAnalysis tFunct pFunct vFunct a


 (*Get the string form of an analysis *)
  let analysis2string a = 
    let tFunct pt s =   (symbol2string s) ^ " " 
    and pFunct pt t children = "(" ^ (nt2string (pTypeHead (Tbl t)))  
      ^ ":" ^ (Int64.to_string !t.id) ^ " " ^ (List.fold_left (fun a e -> a ^ e) " " children) ^ ")"
    and vFunct pt t children = "[" ^ (nt2string (pTypeHead (Tbl t))) 
      ^  ":" ^ (Int64.to_string !t.id) ^ " " ^ (List.fold_left (fun a e -> a ^ e) " " children) ^ "]"
    in foldAnalysis tFunct pFunct vFunct a


 (*Get the string form of an analysis without bells and whistles *)
  let analysis2simpleString a = 
    let tFunct pt s =   (symbol2string s)  
    and pFunct pt t children = "(" ^ (nt2string (pTypeHead (Tbl t)))  
      ^ " " ^ (List.fold_left (fun a e -> a ^ e) "" children) ^ ")"
    and vFunct pt t children = "(" ^ (nt2string (pTypeHead (Tbl t))) 
      ^  " " ^ (List.fold_left (fun a e -> a ^ e) "" children) ^ ")"
    in foldAnalysis tFunct pFunct vFunct a

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

  let analysis2parseTree a =  match a with
      Terminal (s, pt) -> pt
    | Constituent (s, ch, pt) -> pt
      
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

  (* Write out a simple representation of a static snapshot of this grammar *)
  let writeSimplePcfg g ch =
    let keys =  (Hashtbl.fold (fun k _ a -> k :: a) g.rsts [] )
    in let nts = (List.sort compare keys)
    in let simpleProd2string p = 
      let rhs2string r = match r with
	  T t -> t.tName
	| N nt  -> nt.nName
      in  (string_of_float (exp (prodLogprob p))) ^ " " ^ (symbol2string (head p)) ^ " --> " ^ List.fold_left (fun a v -> a ^ " " ^ (rhs2string v) ) "" (getRHS p)
    in let restProdsString r =
      (Hashtbl.fold (fun k v a -> ((simpleProd2string v ) ^ "\n" ^ a)) r.prods "")
    in (List.iter 
	(fun v -> 
	  (output_string ch (restProdsString (Hashtbl.find g.rsts v))); 
	  flush ch; ) nts) 


  type pcfgProduction = {pcfgpdScore: float;
			 pcfgpdHead : string;
			 pcfgpdRhs : string list;}

  let pcfgProduction2string p =
    (string_of_float p.pcfgpdScore) ^" " ^  p.pcfgpdHead ^" "^ (List.fold_left (fun a v -> a ^" "^ v ) "" p.pcfgpdRhs)
      
  type pcfgRepresentation = 
      { grammarScore: float;
	pcfgProductions : pcfgProduction list;}

  let pcfgRepresentation2string p =
    "# " ^ (string_of_float p.grammarScore) ^"\n"^ (List.fold_left (fun a v -> a ^ (pcfgProduction2string v) ^ "\n" ) "" p.pcfgProductions)

  let getpcfgRepresentation g =
    let keys =  (Hashtbl.fold (fun k _ a -> k :: a) g.rsts [] )
    in let nts = (List.sort compare keys)
    in let sym2s s = match s with
	T t -> "_"^t.tName
      | N nt  -> nt.nName
    in let pList = 
      List.flatten 
	(List.map 
	    (fun nt -> 
	      let r = (Hashtbl.find g.rsts nt)
	      in  (Hashtbl.fold (fun k prod acc -> {pcfgpdScore=(prodLogprob prod);
						    pcfgpdHead= (sym2s prod.pHead);
						    pcfgpdRhs= (List.map sym2s prod.pRhs);}:: acc)) r.prods [])
	    nts)
    in { grammarScore = (scoreGrammar g);
	 pcfgProductions = pList;}

  (* Write out a simple representation of a static snapshot of this grammar *)
  let writeTableStructs g ch =
    let keys =  (Hashtbl.fold (fun k _ a -> k :: a) g.rsts [] )
    in let nts = (List.sort compare keys)
    in (List.iter 
	(fun v -> 
	  let rest = (Hashtbl.find g.rsts v)
	  in (Hashtbl.iter 
		 (fun k tbl -> 
		   begin
		     output_string ch ((Int64.to_string k) ^": " ^(parseTree2string !tbl.structure) ^ " " ^(string_of_float !tbl.tCnt) ^ "\n");
		     flush ch;
		   end)
		 rest.tbls)) 
	nts) 

 let sampleProductionMember p =
    (* let _ = Globals.dbgMsg "fg" 10 ("Sampling from production with: " ^(string_of_int (Hashtbl.length !p.members))^" members.\n") in*)
    let (prods, probs, total) = Hashtbl.fold 
      (fun k v (pds, pbs, t) -> 
	let pb = (prodTypeLogprob v)
	in (v::pds, pb::pbs, (logsumexp [t;pb]))) 
      !p.members 
      ([], [], neg_infinity)
    in Utils.sampleDiscreteTotal prods probs total

  (* Take a production and get its most probable member *)
  let getMAPStateConstituent grammar state constituent = 
    if Hashtbl.mem grammar.id2trie state
    then let trie = Hashtbl.find grammar.id2trie state
      in if Hashtbl.mem !trie.productions constituent
	then let prod =  Hashtbl.find !trie.productions constituent
	  in let (b, bpb) = (Hashtbl.fold 
				(fun k v (best, bestprob) -> 
				  let pb = (prodTypeLogprob v)
				  in if pb > bestprob
				    then (Some v, pb)
				    else (best, bestprob)) 
				prod.members 
				(None, neg_infinity))
	  in match b with
	      Some x -> x
	    | None -> failwith ("FragmentGrammar.getMAPStateConstituent: unable to find best production member: " ^ (symbol2string constituent) ^ " in trie: " ^ (trie2string !trie))
	else failwith ("FragmentGrammar.getMAPStateConstituent: unable to find constituent: " ^ (symbol2string constituent) ^ " in trie: " ^ (trie2string !trie))
    else failwith ("FragmentGrammar.getMAPStateConstituent: unable to find trie with ID: " ^ (Int64.to_string state))
      

  (* Take a production and return one of its members at random *)
  let sampleStateConstituent grammar state constituent =
    if Hashtbl.mem grammar.id2trie state
    then let trie = Hashtbl.find grammar.id2trie state
      in if Hashtbl.mem !trie.productions constituent
	then let prod =  Hashtbl.find !trie.productions constituent
	  in sampleProductionMember (ref prod)
	else failwith ("FragmentGrammar.sampleStateConstituent: unable to find constituent: " ^ (symbol2string constituent) ^ " in trie: " ^ (trie2string !trie))
    else failwith ("FragmentGrammar.sampleStateConstituent: unable to find trie with ID: " ^ (Int64.to_string state))

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
      
  let matchTableStructures grammar f =
    match f with
	Nd ((N label), ch) ->
	  let rest = getRestaurant grammar label
	  in Hashtbl.fold 
	    (fun k tbl a ->
	      begin
		(* Globals.dbgMsg "fg" 10 ("Comparing fragment: " ^ (parseTree2string f) ^ " to table: " ^  (parseTree2string !tbl.structure) ^ " \n"); *)
		if compareParseTrees !tbl.structure f
		then !tbl::a
		else a;
	      end ) 
	    rest.tbls
	    []
      | _ -> failwith "FragmentGrammar.matchTableStructures: trying to match table structures to a leaf symbol!"


  (* Get the score of the minumum scoring production that is used in this analysis*)
  let getMinimumScoringProduction  analysis =
    let tFunct pt s = 0.0
    and pFunct pt t children = 
      begin 
	(* Globals.dbgMsg "fg" 10 ("Getting minimum (ptr): " ^ (List.fold_left (fun a v -> a ^ " " ^ (string_of_float (exp v))) "" children) ^ "\n");
	Globals.dbgMsg "fg" 10 ("\tminimum: " ^ (string_of_float (exp (List.fold_left min 0.0 children))) ^ " \n");*)
	(List.fold_left min 0.0 children);
      end
    and vFunct pt t children =
      let childMin = (List.fold_left min 0.0 children)
      in begin 
	 (* Globals.dbgMsg "fg" 10 ("Production: " ^ (Int64.to_string (table2production !t).pid) ^ "\n");*)
(*	Globals.dbgMsg "fg" 10 ("Getting minimum (var): " ^ (List.fold_left (fun a v -> a ^ " " ^ (string_of_float (exp v))) "" children) ^ "\n");
	Globals.dbgMsg "fg" 10 ("\t child minimum: " ^ (string_of_float (exp childMin)) ^ " \n");
	Globals.dbgMsg "fg" 10 ("\t current node: " ^ (string_of_float (exp (prodLogprob (table2production !t)))) ^ " \n");
	Globals.dbgMsg "fg" 10 ("\t min: " ^ (string_of_float (exp (min childMin (prodLogprob (table2production !t))))) ^ " \n");*)
	(min childMin (prodLogprob (table2production !t)));
      end
    in foldAnalysis tFunct pFunct vFunct analysis


let getROOTStateExpectations () =
  begin
    (* Globals.dbgMsg "fg" 10 ("Returning the ROOT state expectations object, with entropy: " ^ 
			       (string_of_float neg_infinity) ^ "(" ^ 
			       (string_of_float (exp neg_infinity)) ^ ")" ^ "\n");*)
    {sEntropy = neg_infinity;  
     sNumConstituents =  neg_infinity;};  
  end

(* CYK interface *)
let updateStateExpectations oldStateExpOpt lStateExp rConstExp = 
  begin 
  (*  Globals.dbgMsg "fg" 10 ("Updating state expectations\n" ^
			       "\tleft State Num: " ^ 
			       (string_of_float lStateExp.sNumConstituents) ^ "(" ^ 
			       (string_of_float (exp lStateExp.sNumConstituents)) ^ ")" ^ 
			       "\n\tRight Constituent Num: " ^
			       (string_of_float rConstExp.cNumConstituents) ^ "(" ^ 
			       (string_of_float (exp rConstExp.cNumConstituents)) ^ ")" ^ "\n" );*)
  match oldStateExpOpt with
      Some e ->  
	begin 
	  let newNumConstituents = Utils.logsumexp [e.sNumConstituents; lStateExp.sNumConstituents; rConstExp.cNumConstituents]
	 (* in let _ =  Globals.dbgMsg "fg" 10 ("\tOld num Constituents: " ^ (string_of_float e.sNumConstituents) ^ " ("^ (string_of_float (exp e.sNumConstituents)) ^")"^"\n")
	  in let _ =  Globals.dbgMsg "fg" 10 ("\tNew num Constituents: " ^ (string_of_float newNumConstituents) ^ " ("^ (string_of_float (exp newNumConstituents)) ^")"^"\n\n")*)
	  in {sEntropy = Utils.logsumexp [e.sEntropy; lStateExp.sEntropy; rConstExp.cEntropy];  
	      sNumConstituents = newNumConstituents;};
	end
    | None ->
	let newNumConstituents = Utils.logsumexp [lStateExp.sNumConstituents; rConstExp.cNumConstituents] 
	(*in let _ =  Globals.dbgMsg "fg" 10 ("\tOld num Constituents: " ^ (string_of_float neg_infinity) ^ " ("^ (string_of_float (exp neg_infinity)) ^")"^"\n")
	in let _ =  Globals.dbgMsg "fg" 10 ("\tNew num Constituents: " ^ (string_of_float newNumConstituents) ^ " ("^ (string_of_float (exp newNumConstituents)) ^")"^"\n\n")*)
	in  {sEntropy = Utils.logsumexp [lStateExp.sEntropy; rConstExp.cEntropy];  
	     sNumConstituents =  newNumConstituents;}
  end 


let getEmptyConstituentExpectations (symb : symbol) =
 (* Globals.dbgMsg "fg" 10 ("Getting Empty Constituent Expectations from symbol: " ^ (symbol2string symb) ^ "\n\n");*)
  {cEntropy = neg_infinity;  
   cNumConstituents = (log 0.0)}

(* CYK interface *) 
let updateConstExpectations symb oldConstExpOption childStateExp prob  unnormalized_prob =  
  begin
   (* Globals.dbgMsg "fg" 10 ("Updating constituent expectations\n"^
			       "\tSymbol: " ^
			       (symbol2string symb) ^"\n"^
			       "\tposterior probability: " ^ 
			       (string_of_float prob) ^ " (" ^ 
			       (string_of_float (exp prob)) ^ ")" ^ 
			       "\n\tchild-state Num: " ^
			       (string_of_float childStateExp.sNumConstituents) ^ "(" ^ 
			       (string_of_float (exp childStateExp.sNumConstituents)) ^ ")" ^ "\n" );*)
    let (oldEntropy, oldNumConstituents) = match oldConstExpOption with
	Some e -> (e.cEntropy, e.cNumConstituents)
      | None -> (neg_infinity,neg_infinity)
    in let newEntropy = Utils.logsumexp [oldEntropy; (log ((exp prob) *. ((exp childStateExp.sEntropy) +. (-. prob))))]
    in let newNumConstituents = Utils.logsumexp [oldNumConstituents; 
					    (prob +. 
						Utils.logsumexp [childStateExp.sNumConstituents; (log 1.0)])]
    (*in let _ =  Globals.dbgMsg "fg" 10 ("\tOld num Constituents: " ^ (string_of_float oldNumConstituents) ^ " ("^ (string_of_float (exp oldNumConstituents)) ^")"^"\n")
    in let _ =  Globals.dbgMsg "fg" 10 ("\tNew num Constituents: " ^ (string_of_float newNumConstituents) ^ " ("^ (string_of_float (exp newNumConstituents)) ^")"^"\n\n")*)
    in {cEntropy = newEntropy;  
	cNumConstituents = newNumConstituents;};  
  end
    
  (* CYK interface *)
  let constituentMatches = List.mem

  let sampleProduction (rest : restaurant ref) =
    let (prods, probs, total) = Hashtbl.fold 
      (fun rhs prod (pds, pbs, t) -> 
	let pb = (prodLogprob prod)
	in (prod::pds, pb::pbs, (logsumexp [t;pb]))) 
      !rest.prods 
      ([], [], neg_infinity)
    in Utils.sampleDiscreteTotal prods probs total

 let rec forwardSampleAnalysis (grammar : grammar) start = 
   (*let _ =  Globals.dbgMsg "fg" 10 ("\tForward Sampling from symbol: " ^ (symbol2string start) ^"\n")
   in*) match start with
       T t ->  Terminal ((T t), (Lf (T t)))
     | N n -> let startRest = 
	 if Hashtbl.mem grammar.rsts n
	 then Hashtbl.find grammar.rsts n
	 else failwith ("FragmentGrammar.forwardSampleAnalysis: Cannot find restaurant for nonterminal: " ^ (symbol2string start) ^"\n")
       in let production = sampleProduction (ref startRest)
       in match sampleProductionMember (ref production) with 
	   (* Root r -> Terminal (r, (Lf r))
	      | *) Tbl tbl -> let children = List.map (fun s -> forwardSampleAnalysis grammar s) !tbl.yield
	     in (expandTable grammar tbl children)
	 | Br br -> let children = List.map (fun s -> forwardSampleAnalysis grammar s) !br.rhs
	   in let mask = (List.map (fun c -> match c with Terminal _ -> true | Constituent _ -> false) children) 
	   in let tbl = (createDanglingTable !br children (sampleStickyDecisions !br !br.rhs !br.stickyCnts mask) )
	   in Constituent (ref tbl, children, (Nd ( (N (tableHead (ref tbl))), 
						  (List.map 
							  (fun c -> match c with 
							      Terminal (term, pt) -> pt
							    | Constituent (t,l,pt) -> pt) 
							  children))))
	     
end
  
