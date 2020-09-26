(************************************************************************
 ************************************************************************
 *                            Module: Utils                             *       
 * ---------------------------------------------------------------------*
 * General interest functions                                           * 
 ************************************************************************)

open Unix
open Str

(* Initialize a matrix *)
let matrix_init rows cols f =
    let g i = Array.init cols (f i)
    in Array.init rows g


let rec addSuffix suffix list = match list with
    [] -> []
  | hd :: tl -> (hd ^ suffix) :: (addSuffix suffix tl)

(* Rotate a list by one element *)
let rotate l = 
  let first = (List.hd l) 
  in (List.tl l) @ [first]

(* Takes a list of strings and a list of values and returns a list of
   strings where each value has been concatenated on the end of the
   corresponding string. This is useful in building output in matrix
   format for input to matlab or R*)
let accumulateStrings strings vals f padding =
  if (List.length strings) <> (List.length vals)
  then failwith "Lists must be the same langth" 
  else List.map2 (fun v1 v2 -> v1 ^ padding ^ (f v2)) strings vals


let rec appendArrays ars = match ars with
    [] -> [||]
  | hd:: tl -> Array.append hd (appendArrays tl)

(* Create a list of length N by applying the function f N times *)
let rec listn f n = match n with
    0 -> []
  | x when x > 0 -> (f (n-1)) :: (listn f (n-1))
  | _  -> failwith "n must be greater than or equal to 0"

(* Make N numbered symbols *)
let rec makeSymbols s n =
  if n = 0 
  then []
  else (s^(string_of_int (n-1))) :: makeSymbols s (n-1)

(* Calculate the Cartesian product of a list of lists *)
let rec cartesianProduct lol =
  let rec processList l products = match l with
      [] -> []
    | item::tl -> (List.map (fun v -> item :: v) products)  @ (processList tl products)
  in  match lol with
      [] -> [[]]
    | hd::tl -> let products = (cartesianProduct tl) in (processList hd products) 
    
(* Make n copies of a list *)
let rec copyList l n =
  if n=0 
  then []
  else l @ (copyList l (n-1))

(* Enumerate all the lists that come from applying either f1 or f2 to
   each element of the input list *)
let rec binaryEnumerate f1 f2 list = 
  match list with
      [] -> [[]]
    | hd :: tl -> 
	let first =  (binaryEnumerate f1 f2 tl) in
	let second = (binaryEnumerate f1 f2 tl) in
	  ((List.map (fun e -> (f1 hd) :: e) first) @ (List.map (fun e -> (f2 hd) :: e) second))

(* Read in input "sentences", one sentence per line -- into a list of
   string lists. *)
let readSentences typeProc filename =
  let split = (Str.split (Str.regexp " ")) in
  let rec processFile ch = 
    try 
      let line =  (input_line ch) in
        (Array.of_list (List.map typeProc (split line))) :: (processFile ch)
    with End_of_file -> []
  in (processFile (open_in filename))

(* Get a string version of the sentence *)
let sentence2string f s  =
  let string = ref "" in 
    begin
      for i=0 to (Array.length s)-2 do
	string := !string ^ (f s.(i)) ^ " "
      done;
      string := !string ^ (f s.((Array.length s)-1));
      !string;
    end
      
(* Return the maximum of two floats *)
let fmax a b = 
  if a > b then a else b

(* Add probabilities in the log domain *) 
let logsumexp l = 
  let mx = 
    let tmp = List.fold_left (fun a v -> if v > a then v else a) neg_infinity l
    in if tmp = neg_infinity
      then 0.0
      else tmp
  in (log 
	 (List.fold_left 
	     (fun a v -> a +. (exp (v -. mx))) 0.0 l) +. mx)
    
(* Add probabilities in the log domain *) 
let logminusexp l1 l2 = 
  let mx = 
    if l1 > l2 then l1 else l2 
  in (log ((exp (l1 -. mx)) -. (exp (l2 -. mx)))) +. mx

(* Subtract a matrix from the identity *)
 let get_ident_subtr m =
  for i=0 to (Array.length m) -1 do
    for j=0 to (Array.length m) -1 do
      if i = j 
      then m.(i).(j) <- 1.0 -. m.(i).(j)
      else m.(i).(j) <- -1.0 *. m.(i).(j)
    done; done;
      m

(* Flip a weighted coin in the log domain *)
let flipLog weight = 
  begin    
    (log (Random.float 1.0) ) < weight;
  end

(* Normalize a list of floats into a distribution, 
   assuming they are in the log domain  *)
let normalizeLog ls =
  let total = (logsumexp ls) in
  let rec aux l =
    match l with 
	[] -> []
      | hd::tl -> (hd -. total) :: (aux tl)
  in aux ls

let rec sampleDiscreteTotal objects weights mass = match (objects, weights) with
    ([], []) -> failwith "Utils.sampleDiscreteTotal: Attempting to sample from an empty object and probability lists!"
  | (ohd::[], whd::[])  -> ohd 
  | (ohd::otl, whd::wtl) -> 
      if (flipLog (whd -. mass)) 
      then ohd
      else sampleDiscreteTotal otl wtl (logminusexp mass whd) 
  | (_, _) -> failwith "Utils.sampleDiscreteTotal: Misaligned objects and weights!"

let  getBest objects weights =
  let rec aux (besto, bestw) os ws =
    match (os, ws) with
	([], []) -> failwith "Utils.getBestTotal: Attempting to find the best object from an empty object and probability lists!"
      | (ohd::[], whd::[])  -> 
	  if (whd > bestw)
	  then (ohd, whd)
	  else (besto, bestw)
      | (ohd::otl, whd::wtl) -> 
	  if (whd > bestw)
	  then aux (ohd, whd) otl wtl
	  else aux (besto, bestw) otl wtl
      | (_, _) -> failwith "Utils.getBestTotal: Misaligned objects and weights!"
  in let (o, w) = aux ((List.hd objects), (List.hd weights)) (List.tl objects) (List.tl weights)
  in o

let rec sampleIndexTotal weights mass i = match weights with
    [] -> failwith "Utils.sampleIndexTotal: Attempting to sample from an empty list!"
  | hd::[] -> i 
  | hd::tl -> 
      if (flipLog (hd -. mass)) 
      then i
      else sampleIndexTotal tl (logminusexp mass hd) (i+1) 
	
let sampleIndex dist =
  sampleIndexTotal dist (logsumexp dist) 0

(*Sample from a list of objects *)
let sampleDiscrete objects dist =
  let index = (sampleIndex dist) 
  in List.nth objects index

(* Sample n objects from list l uniformly with replacement *)
let sampleNUniform l n =
  let len = List.length l
  in let f x  =  1.0 /. (float_of_int len)
  in let dist = listn f len
  in let sampleOne y =
    (List.nth l (sampleIndex (List.map log dist)))
  in (listn sampleOne n)


(* (* Memoize the lngamma function *)
let lnghash :  (float, float) Hashtbl.t   = Hashtbl.create 1000
let lgamma x =
  if Hashtbl.mem lnghash x
  then Hashtbl.find lnghash x
  else let result = (Gsl_sf.lngamma x) in
	 begin 
	   Hashtbl.add lnghash x result;
	   result;
	 end *)

let printLGHashSize () =
  begin
    (* Globals.dbgMsg "utils" 10 ("Lngamma has size: " 
				^ (string_of_int (Hashtbl.length lnghash))
				^ "\n");*)
    ();
  end

(* type lpparam = float array (* float array *)
let lphash :  (lpparam, float) Hashtbl.t   = Hashtbl.create 1000
(* Implement a multivariate polya distribution --
   aka a multinomial-dirichlet distribution *)
let lpolya (alpha : float array) (counts: float array)  =
  begin
    if (Array.length counts) <> (Array.length alpha) then failwith "Arrays must be the same length";      

    (* Remove any entries with zero hyperparameters *)
    let (alpha2, counts2, len) = (Array.fold_left 
				(fun (aa, ca, i) v -> 
				  if v > 0.0 
				  then ((Array.append [|v|] aa),  (Array.append [|counts.(i)|] ca), i+1 ) 
				  else (aa, ca, i+1)) 
				  ([||], [||], 0) 
				  alpha) in
    let countsAlphaSum = (Array.mapi (fun i a -> a +. alpha2.(i)) counts2) in
    let _ = (Array.sort compare countsAlphaSum); (* (Array.sort compare alpha); *)
    (* in let _ = Globals.dbgMsg "utils" 10 ("\tLpolya Array: ["^(Array.fold_left (fun a v -> a ^ " " ^(string_of_float v) ) "" countsAlphaSum) ^"]\n")  *)
    in if Hashtbl.mem lphash countsAlphaSum
      then Hashtbl.find lphash countsAlphaSum
      else let sum = Array.fold_left (fun a e -> e +. a) 0.0 in
	(* let countsF = Array.map float_of_int counts in *)
      let result = if sum counts = 0.0
	then 0.0
	else (((lgamma  (sum alpha2)) -. sum (Array.map lgamma alpha2))) +. 
	  ((sum (Array.map lgamma countsAlphaSum)) -. (lgamma (sum (countsAlphaSum)))) in
	begin 
	   Hashtbl.add lphash countsAlphaSum result;
	  result;
	 end
  end *)


let lpolya2 (alpha : float array) (counts: float array)  =
  let alphaTotal = Array.fold_left (fun a e -> e +. a) 0.0 alpha
  in  let addCustomer a_i n_i m  =
    log ((a_i +. n_i) /. (m +. alphaTotal))
  in let totalCustomers = ref 0.0
  in let logProb = ref 0.0
  in begin
      for table = 0 to (Array.length counts)-1 do
	
	if counts.(table) > 0.0
	then begin
	    let a_i = alpha.(table) in
	      (* Seat the first customer at this table. *)
	      logProb := !logProb +. (addCustomer a_i 0.0 !totalCustomers);
	      
	      (* Update totals *)
	      totalCustomers := !totalCustomers +. 1.0;
              
	      let nTable = ref 1.0 in
		for customer = 2 to (int_of_float counts.(table)) do
		  logProb := !logProb +. (addCustomer a_i !nTable !totalCustomers);
		  totalCustomers := !totalCustomers +. 1.0;
		  nTable := !nTable +. 1.0;
		done;
	  end
      done;
      !logProb;
    end

let lpincr (alpha : float) (alphaTotal : float) (totalCount: float) (previousCount : float) (n: int)  =
  let addCustomer  n_i m  =
    log ((alpha +. n_i) /. (alphaTotal +. m))
  in let totalCustomers = ref totalCount
  in let logProb = ref 0.0
  in begin
      (if n > 0 (* && alpha > 0.0 *)
      then let nTable = ref previousCount in
	     for customer = 1 to n do
	       logProb := !logProb +. (addCustomer !nTable !totalCustomers);
	       totalCustomers := !totalCustomers +. 1.0;
	       nTable := !nTable +. 1.0;
	     done);

       (* Globals.dbgMsg "utils" 10 ("Calculating lpolya increment:\n\tnum: " 
				  ^ (string_of_int n)
				  ^ "\n\talpha: "^ (string_of_float alpha)
				  ^ "\n\talphaTotal: "^ (string_of_float alphaTotal)
				  ^ "\n\ttotalCount: "^ (string_of_float totalCount)
				  ^ "\n\tpreviousCount: "^ (string_of_float previousCount)
				  ^ "\n\tlog prob: "^ (string_of_float !logProb)
				  ^ "\n"); *)
      !logProb;
    end
 
let addMultDirObs a_i n_i m a_total =
    log ((a_i +. n_i) /. (m +. a_total))

let lpdecr (alpha : float) (alphaTotal : float) (totalCount: float) (previousCount : float)(n: int)  =
  let addCustomer a_i n_i m  =
    log ((a_i +. n_i) /. (m +. alphaTotal))
  in let totalCustomers = ref totalCount
  in let logProb = ref 0.0
  in begin
      (if n > 0
      then let nTable = ref previousCount in
	     nTable := !nTable -. 1.0;
	     totalCustomers := !totalCustomers -. 1.0;
	     for customer = n downto 1 do
	       logProb := !logProb +. (addCustomer alpha !nTable !totalCustomers);
	       totalCustomers := !totalCustomers -. 1.0;
	       nTable := !nTable -. 1.0;
	     done);

       Globals.dbgMsg "utils" 10 ("Calculating lpolya decrement:\n\tnum: " 
				  ^ (string_of_int n)
				  ^ "\n\talpha: "^ (string_of_float alpha)
				  ^ "\n\talphaTotal: "^ (string_of_float alphaTotal)
				  ^ "\n\ttotalCount: "^ (string_of_float totalCount)
				  ^ "\n\tpreviousCount: "^ (string_of_float previousCount)
				  ^ "\n\tlog prob: "^ (string_of_float !logProb)
				  ^ "\n"); 
      !logProb;
    end


let printLPHashSize () =
  begin
    (* Globals.dbgMsg "utils" 10 ("Multinomial dirichlet hash size: " 
				^ (string_of_int (Hashtbl.length lphash))
				^ "\n");*)
    ();
  end


(* This function is a generalization of the factorial function
used in the pitman yor distribution:

pitmanFactorial x m a =
   1                         if m=0 
   x(x+a)(x+2a)...(x+(m-1)a) if m>1

In other words the function multiplies m numbers
starting from x and increasing by steps of size a.

note that:

f 1 m 1 = m! -- starting from one and increasing by whole 
unit integers we get the factorial function

This function returns this result in the log domain.

Note this is memoizing and tail recursive. 
 *)
type pfparam = float * int * float
let pfhash :  (pfparam, float) Hashtbl.t   = Hashtbl.create 1000
let rec pitmanFactorial (x1 : float) (m1 : int) (a1 : float) = 
  let rec aux accum x2 m2 a2 =
   (* if Hashtbl.mem pfhash  (x2,m2,a2)
    then Hashtbl.find pfhash (x2,m2,a2)
    else *) match m2 with
	0 -> accum
      | v -> 
	  let res = (aux (accum +.(log x2))  (x2 +.a2) (m2-1) a2) 
	  in begin
	      (* Hashtbl.add pfhash (x2,m2,a2) res;*)
	      res
	    end
  in if Hashtbl.mem pfhash (x1,m1,a1)
    then begin
	(* Globals.dbgMsg "utils" 10 ("Retrieving from  pitman factorial Hash: "
				    ^ (string_of_float (x1)) ^ " "
				    ^ (string_of_int (m1)) ^ " "
				    ^ (string_of_float (a1))  
				    ^"\n"); *)
	Hashtbl.find pfhash (x1,m1,a1);
      end
    else (* let tm1 = Sys.time () 
      in *) let result = (aux 0.0 x1 m1 a1)
      (* in let tm2 = Sys.time () *) 
      in begin
	  Hashtbl.add pfhash (x1,m1,a1) result;
	 (* Globals.dbgMsg "utils" 8 ("Hashing pitman factorial values: " 
				      ^ (string_of_float (x1)) ^ " "
				      ^ (string_of_int (m1)) ^ " "
				      ^ (string_of_float (a1)) ^ " "
				      ^ "computed in: "
				      ^ (string_of_float (tm2-.tm1)) ^
				      " seconds\n"); *)
	  result;
	end

let printPFHashSize () =
  begin
(*    Globals.dbgMsg "utils" 10 ("Pitman factorial  hash size: " 
				^ (string_of_int (Hashtbl.length pfhash))
				^ "\n");*)
    ();
  end

(* Pitman Yor distribution 
a : 0 <= a <= 1
b : 0 < b  --- this is the same as the CRP alpha parameter 

N.B. This function is memoized.
*)
type pyparam = float * float * int array
let pyhash :  (pyparam, float) Hashtbl.t   = Hashtbl.create 1000

let pitmanyor (a:float) (b:float) (counts:int array) =

   (* Globals.dbgMsg "utils" 10 ("Pitman-yor  : " 
			      ^ (Array.fold_left (fun a v -> a ^  " "^(string_of_int v)) "" counts) 
			      ^ "\n"); *)
    let counts2 =  (Array.fold_left (fun a e -> if e > 0 then (Array.append [|e|] a) else a) [||] counts) in
    let _ = (Array.sort compare counts2) in
      if counts2 = [||] (* || counts = [|0|] *) then 0.0 
      else if Hashtbl.mem pyhash  (a,b,counts2)
      then Hashtbl.find pyhash (a,b,counts2)
      else begin 
	  (* Globals.dbgMsg "utils" 10 ("Computing Pitman-yor.\n"); *)
	  (* let _ = Globals.dbgMsg "utils" 10 ("Normalized counts: "  ^ 
	     (Array.fold_left (fun a v -> a ^  " "^(string_of_int v)) "" counts2) 
	     ^ "\n") in*)
	  let total = (Array.fold_left (fun a e -> e + a) 0 counts2) in
	  let nTables = (Array.length counts2) in
	  let t3 = ref 0.0 
	  in let result = 
	    begin
	      for j = 1 to total do
		(* Get the number of tables with count j *)
		let num = (Array.fold_left (fun a e -> if e = j then (a +. 1.0) else a) 0.0 counts ) in
		  if num > 0.0 then t3 := !t3 +. ((pitmanFactorial (1.0-.a) (j-1) 1.0) *. num)
	      done;
	      ((pitmanFactorial (b+.a) (nTables-1) a) -. (pitmanFactorial (b+.1.0) (total-1) 1.0) +. !t3);
	    end in begin
		Hashtbl.add pyhash (a,b,counts2) result;
		result;
	      end
	end


let addPYNewTable k a b m =
  log (((k *. a) +. b) /. (m +. b))
    
let  addPYCustExistingTable a b m n =
  log ((n -. a) /. (m +. b))

let pitmanyor2 (a:float) (b:float) (counts:int array) =
  let newTableProb k a b m =
   log (((k *. a) +. b) /. (m +. b))
  and oldTableProb a b m n =
    log ((n -. a) /. (m +. b))
  in let totalCustomers = ref 0.0
  in let totalTables = ref 0.0
  in let logProb = ref 0.0
  in begin 
      for table = 0 to (Array.length counts)-1 do
	
	if counts.(table) > 0
	then begin
	    (* Seat the first customer at this table. *)
	    logProb := !logProb +. (newTableProb !totalTables a b !totalCustomers);
	    
	    (* Update totals *)
	    totalTables := !totalTables +. 1.0;
	    totalCustomers := !totalCustomers +. 1.0;
            
	    let nTable = ref 1.0 in
	      for customer = 2 to counts.(table) do
		logProb := !logProb +. (oldTableProb a b !totalCustomers !nTable);
		totalCustomers := !totalCustomers +. 1.0;
		nTable := !nTable +. 1.0;
	      done;
	  end
      done;
      !logProb;
    end

(* Increment a pitman yor distribution by n customers at a single table *)
let pyincr (a:float) (b:float) (resttotal : float) (tabletotal : float) (numtables : float) (n : float) =
  let newTableProb k a b m =
   log (((k *. a) +. b) /. (m +. b))
  and oldTableProb a b m n =
    log ((n -. a) /. (m +. b))
  in let totalCustomers = ref resttotal
  in let totalTables = ref numtables
  in let logProb = ref 0.0
  in begin 
      (if n > 0.0
	then if tabletotal = 0.0 
	  then begin(* Seat the first customer at this table. *)
	      logProb := !logProb +. (newTableProb !totalTables a b !totalCustomers);
	      (* Update totals *)
	      totalTables := !totalTables +. 1.0;
	      totalCustomers := !totalCustomers +. 1.0;
	      
	      let nTable = ref 1.0 in
		for customer = 2 to (int_of_float n) do
		  logProb := !logProb +. (oldTableProb a b !totalCustomers !nTable);
		  totalCustomers := !totalCustomers +. 1.0;
		  nTable := !nTable +. 1.0;
		done;
	    end
	  else begin
	      let nTable = ref tabletotal in
		for customer = 1 to (int_of_float n) do
		  logProb := !logProb +. (oldTableProb a b !totalCustomers !nTable);
		  totalCustomers := !totalCustomers +. 1.0;
		  nTable := !nTable +. 1.0;
		done;
	    end);
	
      !logProb;
    end


(* Increment a pitman yor distribution by n customers at a single table *)
let pydecr (a:float) (b:float) (resttotal : float) (tabletotal : float) (numtables : float) (n : float) =
  let newTableProb k a b m =
   log (((k *. a) +. b) /. (m +. b))
  and oldTableProb a b m n =
    log ((n -. a) /. (m +. b))
  in let totalCustomers = ref resttotal
  in let totalTables = ref numtables
  in let logProb = ref 0.0
  in begin 
      (if n > 0.0
	then 
	  let nTable = ref tabletotal in
	    begin
	      (* Remove the last customer from the table and restaurant *)
	      totalCustomers := !totalCustomers -. 1.0;
	      nTable := !nTable -. 1.0;
	      for customer = (int_of_float n) downto 1 do
		(* If there are still customers at the table, remove the mass added by the last customer *)
		(if !nTable > 0.0          
		  then begin 
		      logProb := !logProb +. (oldTableProb a b !totalCustomers !nTable);
		      totalCustomers := !totalCustomers -. 1.0;
		      nTable := !nTable -. 1.0;
		    end
		    (*Otherwise remove the mass added by the new table *)
		  else (if !nTable = 0.0
		    then begin 
			totalTables := !totalTables -. 1.0;
			logProb := !logProb +. (newTableProb !totalTables a b !totalCustomers); 
		      end
		    else failwith "Utils.pydecr: invalid number of customers (less than 1) at table!\n"));
	      done;
	    end);
      !logProb;
    end



let printPYHashSize () =
  begin
    (* Globals.dbgMsg "utils" 10 ("Pitman-yor  hash size: " 
				^ (string_of_int (Hashtbl.length pyhash))
				^ "\n"); *)
    ();
  end
    
(* unique and array *)
let rec unique = function 
  | [] -> []
  | x :: xs -> [x] @ (unique (List.filter (fun y->y<>x) xs))
      
(* Harmonic Mean -- not in log domain *)
let harmonicMean l =
  let n = float_of_int (List.length l)
  in (n /. (List.fold_left (fun a v -> a +. (1.0 /. v) ) 0.0 l))

(* Arithmetic mean *)
let arithmeticMean l =
  let n = float_of_int (List.length l)
  and sum = List.fold_left (+.) 0.0 l
  in if n = 0.0
    then failwith "Utils.arithmeticMean: Cannot take the arithmetic mean of a list of length 0!"
    else  (sum /. n)

(* Take a mean over number in the log domain *)
let logArithmeticMean l = 
  let n = (List.length l)
  in ((logsumexp l) -. (log (float_of_int n)))

(* Test if a float is a NaN *)
let is_nan (x : float) = x <> x

(* Make a list of length initialized with this 
   value *)
let makeList length value =
  let rec aux i =
    if i=0 then [] else value :: aux (i-1)
  in (aux length)

(* take a list of string and return it as a string of 
comma separated values *)
let getCSV strings = 
  let rec aux accum strs = match strs with
      [] -> ""
    | last::[] -> (accum ^ last)
    | hd::tl -> aux (accum ^ hd ^ ",") tl
  in aux "" strings


(* Take the path argument and recursive make these 
   directories if they don't exist *)
let makeAbsolutePathToFile filepath =
  let rec aux l p = match l with
      [] -> ()
    | hd :: tl ->
	let path = (p  ^ hd ^ "/") in
	  if (Sys.file_exists path) 
	  then (aux tl path)
	  else begin 
	      (Unix.mkdir path 0o777);
	      (aux tl path);
	    end
  in aux (Str.split (Str.regexp "/") (Filename.dirname filepath)) "/"
    

(* Open a system process, pipe data into it, and capture output *)
let syscall cmd data =                                    
  let readme, writeme = Unix.open_process cmd 
  in let buf = Buffer.create 1000  
  in let _ = output_string writeme data
  in let _ = close_out writeme 
  in (try
     while true do
       Buffer.add_channel buf readme 1
     done
   with End_of_file -> ());
  let _ = close_in readme 
  in let _status = Unix.close_process (readme, writeme) 
  in Buffer.contents buf


let rec repeat k n =
  if n=0 then []
  else k :: repeat k (n-1) 

let rec repeatthunk k n =
  if n=0 then []
  else (k ()) :: repeatthunk k (n-1) 

(* Fisher-Yates shuffle. *)
let shuffle a =
  for n = ((Array.length a) - 1) downto 0 do
    Random.self_init ();
    let k = Random.int (n + 1) in
    let temp = a.(n) in
      a.(n) <- a.(k);
      a.(k) <- temp
  done

(* shuffle a list *)
let shuffle_list l =
  let a =  (Array.of_list l)
  in let _ = shuffle a
  in  Array.to_list a
