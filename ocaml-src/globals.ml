(***********************************************************************************
 ***********************************************************************************
 *                              Module: Globals                                    * 
 * --------------------------------------------------------------------------------*
 *                             Global Variables                                    * 
 ***********************************************************************************)  
let debugB = ref true (* ref false *)
let debugch = ref stdout (* Set the debug output file *)

let setDebug d = (* ()  *)
  debugB := d 

let setDebugFile filename = (* () *)
  begin
    debugch := open_out filename;
  end 

(* Output a debug message *)
let dbgMsg md level message = (* () *)
  if !debugB
  then let debuglevel = (11) (* Set debug level to 1-10 *)
  and mods = ["utils"; "lc"; "top";  "mh"; "sampler"; "agenda"; "cyk";  "fg"; "stats"; "hist" ] (*  "earley"; "gibbs";  "mh-table";*)
  in if ((level <= debuglevel) && (List.exists (fun v -> v = md) mods))
  then begin (output_string !debugch message); flush !debugch; end 
