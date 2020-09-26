open Tree

module SexpTree = Tree (
  struct
    type root = unit
    type node = string
    type leaf = string
	
    let root2string r = ""
    let node2string n = n
    let leaf2string l = l
      
    (* Equality testing on node types *)
    let rootEq r1 r2 = true
    let nodeEq n1 n2 = (n1 = n2)
    let leafEq l1 l2 = (l1 = l2) 
  end)
  
open SexpTree

(* Data type for the sexp lexer input stream *)
type sexpLex = O | C | S of string

(* Initial string buffer *)
let initialBuffer = String.create 32

let buffer = ref initialBuffer
let bufpos = ref 0

(* Reset the buffer *)
let resetBuffer () = buffer := initialBuffer; bufpos := 0

(*Store a character in the string buffer *)
let store c =
  if !bufpos >= String.length !buffer then
    begin
      let newbuffer = String.create (2 * !bufpos) in
	String.blit !buffer 0 newbuffer 0 !bufpos; buffer := newbuffer
    end;
  String.set !buffer !bufpos c;
  incr bufpos
    
(* Tokenize a character stream into sexp lexer types *)
let tokenize s =
  let rec nextToken strm =
    match (Stream.peek strm) with
	Some (' ' | '\010' | '\013' | '\009' | '\026' | '\012') ->
          Stream.junk strm; 
	  [<(nextToken strm)>]
      | Some '(' ->
          Stream.junk strm;
          [<'O; (nextToken strm)>]
      | Some ')' ->
          Stream.junk strm;
          [<'C; (nextToken strm)>]
      | Some _ ->
	  resetBuffer ();
	  let s = readString strm in
	    [<'S s; (nextToken strm)>]
      | None -> raise Stream.Failure (* "Sexp.tokenize.readToken: No Matching Character, or Parser Action" *)
  and readString strm =
    match (Stream.peek strm) with
	Some (' ' | '\010' | '\013' | '\009' | '\026' | '\012') ->
	  String.sub !buffer 0 !bufpos;
      | Some '(' ->
	  String.sub !buffer 0 !bufpos;
      | Some ')' ->
	  String.sub !buffer 0 !bufpos;
      | Some c ->
          Stream.junk strm; 
	  store c;
	  readString strm
      | None -> raise Stream.Failure (* "Sexp.tokenize.readString: No Matching Character, or Parser Action"*)
  in nextToken s
    
(* Make the file lexer*)
let fileLexer filename = let fch = open_in filename in tokenize (Stream.of_channel fch)

(*Parse a single s-expression *)		
let parseSexp =
  try let rec parseNode = parser
      [<'O; 'S n; contents=(parseChildren); 'C>] ->
	SexpTree.Nd (n, contents) 
    | [<'S s>] ->  SexpTree.Lf s 
  and parseChildren = parser
      [<hd=(parseNode); tl=(parseChildren)>] -> hd::tl
    | [<>] -> []
  and matchRoot = parser
      [<'O; n=(parseNode); 'C>] ->
	SexpTree.Rt ((), n)
  in matchRoot
  with Stream.Failure -> failwith "Sexp.parseSexp failure"

(* Parse a sexp file *)
let parseSexpFile filename =
  try let rec aux =  parser
      [<sxp=parseSexp; rest=aux>] -> sxp::rest
    | [<>] -> []  
    in aux (fileLexer filename)
  with Stream.Failure -> failwith "Sexp.parseSexpFile failure"

(* parse a sexp file but don't read the whole thing into memory in one go,
rather make callbacks as you go *)
let iterSexpFile filename callback =
  try let rec aux = parser
      [<sxp=parseSexp; rest=aux>] -> begin (callback sxp) end :: rest
    | [<>] -> []
    in aux (fileLexer filename)
  with Stream.Failure -> failwith "Sexp.iterSexpFile failure"

(* parse a sexp file but don't read the whole thing into memory in one go,
rather make callbacks as you go *)
let iterSexpFileNum filename callback =
  try let n = ref 0
    in let rec aux = parser
	[<sxp=parseSexp; rest=aux>] ->begin n := !n+1; (callback !n sxp) :: rest end
      | [<>] -> []
    in aux (fileLexer filename)
  with Stream.Failure -> failwith "Sexp.iterSexpFileNum failure"

(*Parse a single s-expression *)		
let parseSexpNoRoot =
  try let rec parseNode = parser
      [<'O; 'S n; contents=(parseChildren); 'C>] ->
	SexpTree.Nd (n, contents) 
    | [<'S s>] ->  SexpTree.Lf s 
  and parseChildren = parser
      [<hd=(parseNode); tl=(parseChildren)>] -> hd::tl
    | [<>] -> []
    in parseNode
  with Stream.Failure -> failwith "Sexp.parseSexpNoRoot failure"

let string2sexp str =
  try let rec aux = parser
      [<sxp=parseSexpNoRoot; rest=aux>] -> sxp :: rest
    | [<>] -> []
    in aux (tokenize (Stream.of_string str))
  with Stream.Failure -> failwith "Sexp.string2sexp failure"
