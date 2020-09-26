 (************************************************************************
 ************************************************************************
 *             Module: ReadFragmentGrammar                              *                       
 * ---------------------------------------------------------------------*
 * Functions for reading a fragment grammar from a file.                * 
 ************************************************************************)
open FragmentGrammar
open Sexp

module FG = FragmentGrammar

(* Build a grammar from a s-expression file *)
let buildGrammar filename a b pi slipperyTheta stickyTheta  =
  let gTree = (List.hd (parseSexpFile filename))
  in let start = (FG.N {FG.nName=(SexpTree.liftULeaf (SexpTree.findNode "start-symbol" gTree))})
  in  let defaults = (SexpTree.findNode "defaults" gTree) 
  in let a = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "a" defaults))) 
  and b = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "b" defaults)))  
  and slipperyTheta = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "slippery-theta" defaults))) 
  and stickyTheta = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "sticky-theta" defaults))) 
  and pi = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "pi" defaults)))
  in  let params = (FG.createParams ~a:a ~b:b ~slip:slipperyTheta ~stick:stickyTheta ~pi:pi ())
  in let g = (FG.createGrammar 1000 10000 start params) in 
  let addBaseRule h rhs  =
    begin 
      (if not (FG.hasRestaurant g h) 
	then let _ = (FG.createEmptyRestaurant g h) in ());
      let _ = (FG.createNewBaseRule g h rhs ~pi:pi (*~slipperyTheta:slipperyTheta ~stickyTheta:stickyTheta*)) in ();
    end
  in let rec getRHS (rhsChildren : SexpTree.tree list) = match rhsChildren with
      [] -> []
    | SexpTree.Nd ("T", ch) as n :: tl -> FG.T {FG.tName=(SexpTree.liftULeaf n)} :: (getRHS tl)
    | SexpTree.Nd ("N", ch) as n :: tl -> FG.N {FG.nName=(SexpTree.liftULeaf n)} :: (getRHS tl)
    | x ->  failwith "Unknown symbol type on RHS of rule" 
  in let processRestaurant restNode =
    let head = {FG.nName = (SexpTree.liftULeaf (SexpTree.findNode "head" restNode))}
    and brules = SexpTree.children (SexpTree.findNode "baserules" restNode)
    in (List.iter  (fun brul -> (addBaseRule head (getRHS (SexpTree.children (SexpTree.findNode "rhs" brul))))) brules)
  in begin (List.iter (fun rest -> processRestaurant rest) (SexpTree.children (SexpTree.findNode "restaurants" gTree))); g end    

(* Build a grammar from a s-expression file *)


let buildGrammarNoDefaults 
    ?pi:(pi=1.0) 
    ?slipperyTheta:(slipperyTheta=1.0)  
    ?stickyTheta:(stickyTheta=1.0)
    filename 
    a 
    b =
  let gTree = (List.hd (parseSexpFile filename))
  in let start = (FG.N {FG.nName=(SexpTree.liftULeaf (SexpTree.findNode "start-symbol" gTree))})
  in let g = (FG.createGrammar 1000 10000 start (FG.createParams ~a:a ~b:b ~slip:slipperyTheta ~stick:stickyTheta ~pi:pi ())) in 
  let addBaseRule h rhs resta restb brpi =
    begin 
      (if not (FG.hasRestaurant g h) 
	then let _ = (FG.createEmptyRestaurant g h) in ());
      let _ = (FG.createNewBaseRule g h rhs ~pi:brpi (*~slipperyTheta:slipperyTheta ~stickyTheta:stickyTheta*)) in ();
    end
  in let rec getRHS (rhsChildren : SexpTree.tree list) = match rhsChildren with
      [] -> []
    | SexpTree.Nd ("T", ch) as n :: tl -> FG.T {FG.tName=(SexpTree.liftULeaf n)} :: (getRHS tl)
    | SexpTree.Nd ("N", ch) as n :: tl -> FG.N {FG.nName=(SexpTree.liftULeaf n)} :: (getRHS tl)
    | x ->  failwith "Unknown symbol type on RHS of rule" 
  in let processBaseRule head resta restb brulNode =
    let brpi = match (SexpTree.findNodeOption "pi" brulNode) with Some n -> (float_of_string (SexpTree.liftULeaf n)) | None -> pi
    in let rhs = (getRHS (SexpTree.children (SexpTree.findNode "rhs" brulNode)))
    in (addBaseRule head rhs resta restb brpi)
  in let processRestaurant restNode  =
    let head = {FG.nName = (SexpTree.liftULeaf (SexpTree.findNode "head" restNode))}
    and brules = SexpTree.children (SexpTree.findNode "baserules" restNode)
      (* Get the optional a/b params per restaurant and use default if not specified *)
    in let resta = match (SexpTree.findNodeOption "a" restNode) with Some n -> (float_of_string (SexpTree.liftULeaf n)) | None -> a
    and restb =  match (SexpTree.findNodeOption "b" restNode) with Some n -> (float_of_string (SexpTree.liftULeaf n)) | None -> b
    in (List.iter (processBaseRule head resta restb) brules)
  in begin (List.iter (fun rest -> processRestaurant rest) (SexpTree.children (SexpTree.findNode "restaurants" gTree))); g end 

(* Serialize a representation of an analysis that can be read back in *)
let analysis2sexp a = 
  let tFunct id s =  (* "(leaf " ^ (FG.t2string s) ^ " )"  *)  (FG.symbol2string s)
  and pFunct id t children = "(constituent (mem true)" ^ "(head " ^(FG.nt2string (FG.pTypeHead (FG.Tbl t)))^")" ^ " (table " ^ (Int64.to_string !t.FG.id) ^ " ) (children " ^ (List.fold_left (fun a e -> a ^ e) " " children) ^ "))"
  and vFunct id t children = "(constituent (mem false)" ^ "(head " ^(FG.nt2string (FG.pTypeHead (FG.Tbl t)))^")" ^" (table "  ^ (Int64.to_string !t.FG.id) ^ " ) (children " ^ (List.fold_left (fun a e -> a ^ e) " " children) ^ "))"
  in "(" ^ (FG.foldAnalysis tFunct pFunct vFunct a) ^ ")"


let baseRule2sexp (br : FG.baserule) =
  let rec getRHS rhs = match rhs with
      [] -> []
    | FG.N nt :: tl -> (SexpTree.Nd ("N", [SexpTree.Lf (FG.nt2string nt)])) :: (getRHS tl)
    | FG.T t :: tl -> (SexpTree.Nd ("T", [SexpTree.Lf (FG.t2string t)])) :: (getRHS tl)
  in let head = SexpTree.Nd ("head", [(SexpTree.Lf (FG.nt2string br.FG.head))])
  and rhs = SexpTree.Nd ("rhs", (getRHS br.FG.rhs))
  and pi = SexpTree.Nd ("baserule-pseudo", [SexpTree.Lf (string_of_float br.FG.pi)])
  (*and stickyTheta = SexpTree.Nd ("sticky-pseudo", [SexpTree.Lf (string_of_float br.FG.stickyTheta)])
  and slipperyTheta = SexpTree.Nd ("slippery-pseudo",  [SexpTree.Lf (string_of_float br.FG.slipperyTheta)])*)
  (* and stickyCnts = SexpTree.Nd ("sticky-count", [List.fold_left (fun a v ->  SexpTree.Lf (string_of_float v) :: a) [] br.FG.stickyCnts] ) *)
  (* and brCnt = SexpTree.Nd ("count", [SexpTree.Lf (string_of_float br.FG.brCnt)]) *)
  (* and abrs = SexpTree.Nd ("annotated-base-rules", List.fold_left (fun a v -> (annotatedBaseRule2sexp !v) :: a ) [] br.FG.abrs) *)
  in SexpTree.Nd ("baserule", [head;rhs;pi;(*stickyTheta;slipperyTheta*)])

(* Get a restaurant Node *)
let restaurant2sexp (rest : FG.restaurant) = 
  let label = SexpTree.Nd ("label", [SexpTree.Lf (FG.nt2string rest.FG.label)])
  and a =  SexpTree.Nd ("a", [SexpTree.Lf (string_of_float rest.FG.a)])
  and b =  SexpTree.Nd ("b", [SexpTree.Lf (string_of_float rest.FG.b)])
  (* and totPi = SexpTree.Nd ("baserule-total-prior", [SexpTree.Lf (string_of_float rest.FG.totPi)]) *)
  (* and rCnt = SexpTree.Nd ("count", [SexpTree.Lf ((string_of_float rest.FG.rCnt))]) *)
  and baseRules = SexpTree.Nd ("baserules", (List.fold_left (fun a v -> (baseRule2sexp !v) :: a ) [] rest.FG.brs))
  (*and tables = SexpTree.Nd ("tables", (Hashtbl.fold (fun k v a -> (table2sexp !v) :: a) rest.FG.tbls [])) *)
  in SexpTree.Nd ("restaurant", [label;a;b;baseRules])

 
(* Get an s-exp node for the defaults *)
let params2sexp (grammar : FG.grammar) =
  (* let a =  SexpTree.Nd ("a", [SexpTree.Lf (string_of_float grammar.FG.defs.FG.aDef)])
  and b =  SexpTree.Nd ("b", [SexpTree.Lf (string_of_float grammar.FG.defs.FG.bDef)])*)
  let (* slip = SexpTree.Nd ("slippery-pseudo",  [SexpTree.Lf (string_of_float grammar.FG.params.FG.slipperyThetaDef)])
  and stick = SexpTree.Nd ("sticky-pseudo", [SexpTree.Lf (string_of_float grammar.FG.params.FG.stickyThetaDef)])
  and *) pi = SexpTree.Nd ("baserule-pseudo", [SexpTree.Lf (string_of_float grammar.FG.params.FG.piDef)])
  and start = SexpTree.Nd ("start-symbol",[(SexpTree.Lf (FG.symbol2string grammar.FG.start))])
  and rests= SexpTree.Nd ("restaurants", (Hashtbl.fold (fun k v a ->  (restaurant2sexp v) :: a ) grammar.FG.rsts []))
  in SexpTree.Nd ("parameters", [start; (*a;b; slip;stick;*) pi;rests])

(* Serialize entire list of analyses. *) 
let saveState filename grammar analyses =
    let ch = open_out filename in
      begin
	output_string ch ("("^(SexpTree.tree2prettyString (params2sexp grammar))^")");
        List.iter (fun v -> output_string ch ((analysis2sexp v) ^"\n"); flush ch; ) analyses;
	close_out ch;
      end
 
(* Load a sentence into the grammar, return its analysis *)
let loadAnalysis (g: FG.grammar) (t : SexpTree.tree) (tbls :  (int64, FG.table ref) Hashtbl.t) count =
  let rec getPtrees cl = match cl with
      [] -> []
    | FG.Terminal (term, pt)::tl -> pt :: (getPtrees tl)
    | FG.Constituent (t,l, pt)::tl -> pt :: (getPtrees tl)
  in let getBaseRule head brCh =
    let h = {FG.nName=head}
    in let _ = if not (FG.hasRestaurant g h) 
      then failwith "FragmentGrammarIO.loadAnalysis: Grammar does not have restaurant!"
    in let brRhs = (List.map (fun v -> match v with 
	FG.Terminal ((*_,*) term, pt) -> (* FG.T *) term 
      | FG.Constituent ((*_,*) table, _, pt) ->  FG.N (FG.tableHead table)) brCh)
    in let possibleBr = (FG.getBaseRuleStructure g h brRhs)
    in (match possibleBr with
	None ->  failwith "FragmentGrammarIO.loadAnalysis: Grammar does not have base rule!!"
      | Some br -> br)
  in let getTable id head brCh memCh =
    if (Hashtbl.mem tbls id)
    then (Hashtbl.find tbls id)
    else (* let matchSlippery = List.for_all2 (=) memCh   *)
     (* in let abr = (List.find (fun v -> (matchSlippery (FG.getMemBool !v))) (FG.getAbrs (getBaseRule head brCh))) *)
      let br = (getBaseRule head brCh)
      in let tbl = (FG.createDanglingTable br brCh memCh)
      in begin Hashtbl.add tbls id (ref tbl); ref tbl; end 
  in let rec processNode n  = match n with
(* SexpTree.Rt (r, ch) -> FG.Constituent  (processChildren [ch]) *)
      SexpTree.Nd (n, ch) ->
	let chldrn = (SexpTree.children (SexpTree.getNodeFromList "children" ch))   (* Get the actual analysis children *)
	in let (anaCh, memCh) = List.split (processChildren chldrn)         (* Recurse on those *)
	in let mem = (bool_of_string (SexpTree.liftULeaf (SexpTree.getNodeFromList "mem" ch)))
	in let head = (SexpTree.liftULeaf (SexpTree.getNodeFromList "head" ch))
	in let table = (Int64.of_string (SexpTree.liftULeaf (SexpTree.getNodeFromList "table" ch)))
	in let tbl = getTable table head anaCh memCh
	in let node = (FG.Constituent (tbl, anaCh, (FG.Nd ((FG.N (FG.tableHead tbl)), (getPtrees anaCh)  ) )))
	in let memType = if mem 
	  then (FG.Ptr (FG.N !(!tbl.FG.rest).FG.label))
	  else (FG.Val (FG.N !(!tbl.FG.rest).FG.label))  
	in begin (node, memType) end
    | SexpTree.Lf l ->  (FG.Terminal ( (FG.T {FG.tName=l}), (FG.Lf  (FG.T {FG.tName=l}))), (FG.Val (FG.T {FG.tName=l})))
    | x -> failwith "Unknown node type"
  and processChildren ch = match ch with
      [] -> []
    | hd :: tl -> (processNode hd) :: (processChildren tl)
  in match t with 
      SexpTree.Rt (r, ch) ->  
	let (a, _) = (processNode ch) in begin (FG.addAnalysis g a count); a end
    | x -> failwith "No root node"

(* Load the baserules of our grammar *)
let loadBaseRules brnds g =
  let rec getRHS (rhsChildren : SexpTree.tree list) = match rhsChildren with
      [] -> []
    | SexpTree.Nd ("T", ch) as n :: tl -> FG.T {FG.tName=(SexpTree.liftULeaf n)} :: (getRHS tl)
    | SexpTree.Nd ("N", ch) as n :: tl -> FG.N {FG.nName=(SexpTree.liftULeaf n)} :: (getRHS tl)
    | x ->  failwith "Unknown symbol type on RHS of rule"
  in let processBr brnd = 
    let pi = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "baserule-pseudo" brnd)))
    (* and slip = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "slippery-pseudo" brnd))) 
    and stick =(float_of_string (SexpTree.liftULeaf (SexpTree.findNode "sticky-pseudo" brnd))) *) 
    in let head = {FG.nName = (SexpTree.liftULeaf (SexpTree.findNode "head" brnd))}
    in let rhs = (getRHS (SexpTree.children (SexpTree.findNode "rhs" brnd)))
    in let _= (FG.createNewBaseRule g head rhs ~pi:pi (*~slipperyTheta:slip ~stickyTheta:stick*)) in ()
  in let brules = (SexpTree.children brnds)
  in (List.iter processBr brules)

(* Reload the restaurants *)
let loadRestaurants  g rnd =
  let (* a = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "a" rnd))) 
  and b = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "b" rnd))) 
  and *) head = {FG.nName = (SexpTree.liftULeaf (SexpTree.findNode "label" rnd))}
  in begin
      (FG.createEmptyRestaurant g head);
      (loadBaseRules (SexpTree.findNode "baserules" rnd) g);
    end
    
(* Read in a new grammar and list of analyses *)
let restoreState filename =
  let infile =  (parseSexpFile filename)
  in let params = (List.hd infile)
  in let start = (FG.N {FG.nName=(SexpTree.liftULeaf (SexpTree.findNode "start-symbol" params))})
  in  let  a = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "a" params))) 
  and b = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "b" params)))  
  and slipperyTheta = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "slippery-pseudo" params))) 
  and stickyTheta = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "sticky-pseudo" params))) 
  and pi = (float_of_string (SexpTree.liftULeaf (SexpTree.findNode "baserule-pseudo" params)))
  in  let g = (FG.createGrammar 1000 10000 start (FG.createParams ~a:a ~b:b ~slip:slipperyTheta ~stick:stickyTheta ~pi:pi ()))
  and tbls = Hashtbl.create 100000
  in let _ = (List.iter (loadRestaurants g)  (SexpTree.children (SexpTree.findNode "restaurants" params)) )
  in let analyses = List.fold_left (fun a v -> (loadAnalysis g v tbls) :: a ) [] (List.tl infile) 
  in (g, (List.rev analyses))

(* write out the tables in a friendly readable format *)
let writeTables g filename =
  let ch = open_out filename
  in let printTables tables = (Hashtbl.iter 
       (fun k v -> 
	 (output_string ch 
	     ("(" ^ " " ^
		 (string_of_float !v.FG.tCnt) ^ " " ^ 
		 (FG.tableStructure2String !v ) ^
		 ")\n")))
	   tables)
  in (Hashtbl.iter (fun k v -> (printTables v.FG.tbls)) g.FG.rsts)
    
