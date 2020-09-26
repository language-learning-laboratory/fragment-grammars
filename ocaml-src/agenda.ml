(* This implements a non-duplicate stack with 
   constant time lookup into the stack.  *)

type 'a t =   
    {(* mutable next : 'a option; *)
      q : 'a Queue.t;
     added :  ('a, bool) Hashtbl.t}
(*     todo : ('a ,   'a option)  Hashtbl.t;
     did :  ('a, bool) Hashtbl.t} *)
      
let create size = 
  {q = Queue.create ();
   added =   Hashtbl.create size;
   (* did = Hashtbl.create size *) }

let add  item hs =
  begin
    (* 
    if (Hashtbl.mem hs.todo item)
    then  Globals.dbgMsg "agenda" 10 ("Re-adding todo item to agenda.\n"); 
    if Hashtbl.mem hs.did item
    then Globals.dbgMsg "agenda" 10 ("Re-adding done item to agenda.\n"); *)
  
    if (Hashtbl.mem hs.added item)
    then ()
    else 
    begin
      Hashtbl.add hs.added item  true;
      Queue.add item hs.q;
    end
  end
    
let isEmpty hs =
  Queue.is_empty hs.q

let next hs =
  Queue.take hs.q
    
(*  match hs.next with
      None -> failwith "Attemp to extract from empty agenda"
    | Some item ->
	begin
	  let oneDeep = Hashtbl.find hs.todo item
	  in begin 
	      Hashtbl.add hs.did item true;
	      Hashtbl.remove hs.todo item;
	      hs.next <- oneDeep;
	      item;
	    end
	end *)

 (* let hasIterm hs item =
    Hashtbl.mem hs.todo item *)

let agenda2string hs f =
  (" Queue: " ^ (Queue.fold (fun a v -> a ^ " " ^ (f v) ) "" hs.q)) ^ "  |  Added: " ^(Hashtbl.fold (fun k v a -> a ^ " " ^(f k) )  hs.added "")
