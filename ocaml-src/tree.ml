(************************************************************************
 ************************************************************************
 *                            Module: Tree                              *                       
 * ---------------------------------------------------------------------*
 * This module implements an abstract tree.                             * 
 ************************************************************************)
module type NodeTypes =
sig
  type root
  type node
  type leaf
      
  val root2string : root -> string
  val node2string : node -> string
  val leaf2string : leaf -> string

  (* Equality testing on node types *)
  val rootEq : root -> root -> bool
  val nodeEq : node -> node -> bool
  val leafEq : leaf -> leaf -> bool 
end

module Tree (N : NodeTypes) =
struct 
  
  (* Basic tree type *)
  type tree = 
      Rt of N.root  * tree
      | Nd of N.node * tree list
      | Lf of N.leaf 	  
	  
  (* This is a right, or "child" fold on the tree*)	  
  (* Tree fold operation *)	  
  let foldTree 
      (rtFn : N.root -> 'a list -> 'a ) 
      (ndFn : N.node -> 'a list -> 'a) 
      (lfFn : N.leaf -> 'a) 
      (t : tree) =
    let rec processNode n = match n with
	Rt (r, ch) -> (rtFn r (processChildren [ch]))
      | Nd (n, ch) -> (ndFn n (processChildren ch))
      | Lf l -> (lfFn l)
    and processChildren ch = match ch with
	[] -> []
      | hd :: tl -> (processNode hd) :: (processChildren tl)
    in (processNode t)

 let tree2prettyString t =
    let rec processNode padding n = match n with
	Rt (r, ch) -> "(" ^ (N.root2string  r) ^ (List.fold_left (fun a e -> a ^" " ^ e) "" (processChildren padding [ch])) ^ " )"
      | Nd (n, ch) -> "\n" ^ padding ^  "(" ^ (N.node2string  n) ^  (List.fold_left (fun a e -> a ^" " ^ e) ""   (processChildren padding ch) ) ^ " )"
      | Lf l -> " " ^ (N.leaf2string  l) ^ " "
    and processChildren padding ch = match ch with
	[] -> []
      | hd :: tl -> (processNode (padding ^ "    ") hd) :: (processChildren padding tl)
    in (processNode "" t)
        
  (* Get a string representation of a tree *)
  let tree2string t =
    let rtFn r ch = "(" ^ (N.root2string  r) ^  (List.fold_left (fun a e -> a ^" " ^ e) ""  ch) ^ " ) "
    and ndFn n ch = "(" ^ (N.node2string  n) ^  (List.fold_left (fun a e -> a ^" " ^ e) ""  ch) ^ " ) "
    and lfFn l = " " ^ (N.leaf2string  l) ^ " "
    in (foldTree rtFn ndFn lfFn t)

  let trees2string ts =
    List.fold_left (fun a v -> (tree2string v) ^ " " ^ a) "" ts

  (* Apply three the three functions appropriately *)
  let applyFns rtFn ndFn lfFn t = match t with
      Rt (r, ch) -> rtFn r ch
    | Nd (n, ch) -> ndFn n ch
    | Lf l -> lfFn l

  (*Find the highest, left most node where mtFn returns true *)
  let matchNode fn t =
    let rec processNode n = match n with
	Rt (r, ch) ->
	  let res =  List.filter (fun e -> match e with Some x -> true | _ -> false) (processChildren [ch]) 
	  in if res= [] 
	    then None
	    else (List.hd res)
      | Nd (n, ch) ->
	  if (fn n)
	  then Some (Nd (n, ch))
	  else let res = (List.filter (fun e -> match e with Some x -> true | _ -> false) (processChildren ch))
	    in if res = [] 
	      then None
	      else (List.hd res)
      | Lf l -> None
    and processChildren ch = match ch with
	[] -> []
      | hd :: tl -> (processNode hd) :: (processChildren tl)
    in match (processNode t) with
	Some x -> x
      | None -> failwith "Node not found"

  (*Find the highest, left most node where mtFn returns true, return Some node if found and None if not. *)
  let matchNodeOption fn t =
    let rec processNode n = match n with
	Rt (r, ch) ->
	  let res =  List.filter (fun e -> match e with Some x -> true | _ -> false) (processChildren [ch]) 
	  in if res= [] 
	    then None
	    else (List.hd res)
      | Nd (n, ch) ->
	  if (fn n)
	  then Some (Nd (n, ch))
	  else let res = (List.filter (fun e -> match e with Some x -> true | _ -> false) (processChildren ch))
	    in if res = [] 
	      then None
	      else (List.hd res)
      | Lf l -> None
    and processChildren ch = match ch with
	[] -> []
      | hd :: tl -> (processNode hd) :: (processChildren tl)
    in (processNode t) 

   
  (* Find a node which is equal to the node passed as a parameter *)
  let findNode (n : N.node) t =
    try
      matchNode (N.nodeEq n) t
    with Failure s -> failwith (s ^ ": " ^(N.node2string n))

  (* Find a node which is equal to the node passed as a parameter *)
  let findNodeOption (n : N.node) t =
    try
      matchNodeOption (N.nodeEq n) t
    with Failure s -> failwith (s ^ ": " ^(N.node2string n))

  (* Get leaf *)
  let getLeaf t = match t with
      Rt (r, ch) -> failwith "Must be a leaf node to grab contents!"
    | Nd (n, ch) -> failwith "Must be a leaf node to grab contents!"
    | Lf l -> l

  (* Get the contents of a node's leaves as a list *)
  let  getLeaves t =
    let rtFn r ch = (List.flatten ch)
    and ndFn n ch = (List.flatten ch)
    and lfFn l = [l]
    in (foldTree rtFn ndFn lfFn t)

  (* Grab the children of a node conditionally *)
  let getChildren ndFn lfFn t = match t with
      Rt (r, ch) -> List.filter (applyFns (fun r ch -> false) ndFn lfFn) [ch]
    | Nd (n, ch) -> List.filter (applyFns (fun r ch -> false) ndFn lfFn) ch
    | Lf l -> failwith "Leaves do not have children"

  (* Grab the children of a node. *)
  let children t = match t with
      Rt (r, ch) -> [ch]
    | Nd (n, ch) -> ch
    | Lf l -> failwith "Leaves do not have children"

  (* Get the children of a node whose values are equal to the specified inputs *)
  let getChildrenEq n l t =
    getChildren (fun nd ch -> (N.nodeEq n nd)) (N.leafEq l) t 

  (* Get a node from a list of nodes *)
  let rec getNodeFromList name l = match l with
      [] -> failwith ("No match found to node with name: " ^ name)
    | hd :: tl -> match hd with
	  Rt (r, ch) -> if ((N.root2string  r) = name)
	    then Rt (r,ch)
	    else (getNodeFromList name tl)
	| Nd (n, ch) ->if ((N.node2string  n) = name)
	    then Nd (n,ch)
	    else (getNodeFromList name tl)
	| Lf l -> if ((N.leaf2string l) = name)
	    then Lf l
	    else (getNodeFromList name tl)


  (* If this tree node is a unary preterminal get the leaf's contents *)
  let liftULeaf t = match t with
      Rt (r, (Lf l)) -> l
    | Nd (n, [Lf l]) -> l
    | Lf l -> l
    | _ -> failwith ("Can only lift unary leaves" ^ (tree2prettyString t))
end


