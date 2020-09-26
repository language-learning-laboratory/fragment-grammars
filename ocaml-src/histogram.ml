(*********************************************
 *             Module: Histogram             *
 * This module implemets dynamic array backed* 
 * histograms.                               *
 *********************************************)
open DynArray
open Utils

module DA = DynArray

type t = {
    name : string;
    counts : int DA.t;
    binsize : float;}

let create name binsize guess =
  {name=name;
   counts=DA.make guess;
   binsize=binsize;}

let add hist point =
  let index = (int_of_float (floor ( point /. hist.binsize)))
  (*in let _ = print_string ("Adding point: " ^ (string_of_float point) ^ " to histogram: " ^ hist.name ^ " in bin: "^ (string_of_int index) ^"\n") *)
  (*in let _ = Globals.dbgMsg "hist" 1 ("Adding point: " ^ (string_of_float point) ^ " to histogram: " ^ hist.name ^ " in bin: "^ (string_of_int index) ^"\n")
  in *) in let last = (DA.length hist.counts) - 1 
  in let _ = if last < index 
    then  let _ = Utils.repeatthunk (fun () -> DA.add hist.counts 0 ) (index-last) in ()  
    else ()
  in let oldCount = (DA.get hist.counts index)
  in DA.set hist.counts index (oldCount + 1)

let hist2string hist =
 (string_of_float hist.binsize) ^ ", " ^ (Utils.getCSV (List.map (fun v -> string_of_int v) (DA.to_list hist.counts)))
  
let writeHist ch hist =
  begin
    output_string ch ((hist2string hist)^ "\n");
    flush ch;
  end

(* Merge two histograms into the first destructively *)
let merge hist1 hist2 =
  let last1 = ((DA.length hist1.counts)-1)
  in let last2 = ((DA.length hist2.counts)-1)
  in let _ = if last1 < last2
    then let _ = Utils.repeatthunk (fun () -> DA.add hist1.counts 0 ) (last2-last1) in ()
    else if last2 < last1
    then let _ = Utils.repeatthunk (fun () -> DA.add hist2.counts 0 ) (last1-last2) in ()
    else ()
  in for index = 0 to (DA.length hist1.counts)-1 do
      DA.set hist1.counts index ((DA.get hist1.counts index) + (DA.get hist2.counts index))
    done;
