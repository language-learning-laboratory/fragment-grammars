module ID (S : (sig end)) = 
struct 
  let mx : int64 ref = ref 0L
  let q : int64 Stack.t = (Stack.create ())

  (* reset the counter *)
  let reset () = 
    begin 
      mx:=0L; 
      Stack.clear q
    end

  (* Get the next id *)
  let next () =
    begin
      if not (Stack.is_empty q) 
      then Stack.pop q 
      else begin mx := (Int64.succ !mx); !mx end
    end

  (* Remove a used ID*)
  let release i =
    if i = !mx
    then mx := Int64.pred !mx
    else Stack.push i q
end
