(***********************************************************************************
 ***********************************************************************************
 *                              Module: MHSampler                                    * 
 * --------------------------------------------------------------------------------*
 *            This module implements a partial fragment grammar (PFG)              * 
 ***********************************************************************************)  
open FragmentGrammar
open Cyk
open Utils
open MHSampler

module FG = FragmentGrammar

module MH = MHSampler

(* module FGParser = EarleyParser(FG) *)
module FGParser = CYKParser(MH.FGCYK)

module FGPT = FGParser.ParseTree

(* Pretty print an MH step *)
let mHTableStep2string result table oldAnalysis newAnalysis mhScore oldScore newScore oldAnaScore newAnaScore =
  begin
     result ^ "\n" ^
    "\t Table: " ^ ((FG.table2string table )) ^ "\n" ^
    "\t Table Original: " ^ ((FG.analysis2string oldAnalysis )) ^ "\n" ^
    "\t Table Proposal: " ^ ((FG.analysis2string newAnalysis )) ^ "\n" ^
    "\t MH score: " ^ (string_of_float mhScore) ^ "\n" ^
    "\t Result LogProb: " ^ (string_of_float newScore) ^ "\n" ^
    "\t Proposal Analysis Score: " ^ (string_of_float newAnaScore) ^ "\n" ^	
    "\t Original Analysis Score: " ^ (string_of_float oldAnaScore) ^ "\n" ^
    "\t Proposal LogProb: " ^ (string_of_float newScore) ^ "\n" ^
    "\t Original LogProb: " ^ (string_of_float oldScore) ^ "\n" 
  end

(* Single MH kernel*)
let rec resampleTable grammar table =
  let category = (FG.N (FG.tableHead (ref table))) in
  let oldPosterior = (FG.scoreGrammar grammar) in                                               (* Calculate the old score of the table *)
  let numCustomers =  FG.numCustomers table in
  let oldAnalysis = FG.getTableAnalysis table in                                                (* Get the analysis corresponding to this table *)
  let _ = (Utils.repeat (fun () -> FG.removeAnalysis grammar oldAnalysis) (int_of_float numCustomers)) in                               (* Remove the table from the grammar *)
  
  (* Removed Table*)
  let minimum = FG.getMinimumScoringProduction oldAnalysis in
  let threshold = (log (Random.float (exp minimum))) in
  let oldAnaScore = (FG.scoreAnalysis grammar oldAnalysis) in                                           (* Calculate the old score of the analysis associated with this table. *)
  let prsr = (FGParser.makeparser grammar) in                                                   (* Make a parser with the new grammar *)
  let tableYield = Array.of_list table.FG.yield in                                              (* Get the yield of the table *)
  let chart = 
    match (prsr None threshold tableYield) with
	FGParser.Success chart -> chart
      | FGParser.Failure chart -> match  (prsr None neg_infinity tableYield) with
	    FGParser.Success ch -> ch
	  | FGParser.Failure ch -> 
	      begin
		Globals.dbgMsg "mh-table" 10 ( "Chart:\n" ^ (FGParser.chart2string grammar ch) ^ "\n");
		failwith ("Grammar does not parse sentence: "^  (Array.fold_left (fun  a v -> a ^ " " ^ (FG.symbol2string v)  ) "" tableYield));
	      end in
  (*let chart = (prsr None threshold  tableYield) in                                                              (* Parse the sentence *)*)
  let newAnalysis =  (MH.parse2analysis grammar (FGParser.sampleTree grammar chart category tableYield) ) in        (* Get the new analysis for this table *)
  let newAnaScore = (FG.scoreAnalysis grammar newAnalysis) in                                           (* Score the new analysis *)
  (* Adding Table *)

  let _ = (Utils.repeat (fun () -> FG.addAnalysis grammar newAnalysis) (int_of_float numCustomers)) in                                    (* Add the new analysis to the grammar *)
  let newPosterior = (FG.scoreGrammar grammar) in                                               (* Get the new posterior *)
  let mhScore = (newPosterior +. oldAnaScore) -. (oldPosterior +. newAnaScore) in
    begin
      if (is_nan mhScore) then failwith "Bad Score"
      else if (mhScore > 0.0)
      then (*Accept*)
	begin
	   Globals.dbgMsg "mh-table" 10 (mHTableStep2string "ACCEPT" table oldAnalysis newAnalysis mhScore oldPosterior newPosterior oldAnaScore newAnaScore);
	  newAnalysis;
	end
      else if (mhScore = 0.0) (* If we are perfectly tied, no point in accepting *)
      then (*Reject*)	
	let _ = (Utils.repeat (fun () -> FG.removeAnalysis grammar newAnalysis) (int_of_float numCustomers)) 
	in let _ = (Utils.repeat (fun () -> FG.addAnalysis grammar oldAnalysis) (int_of_float numCustomers))
	in let _ = Globals.dbgMsg "mh-table" 10  (mHTableStep2string "REJECT" table oldAnalysis newAnalysis mhScore oldPosterior newPosterior oldAnaScore newAnaScore)
	in oldAnalysis
      else if flipLog mhScore
      then (*Accept*)
	begin
	  Globals.dbgMsg "mh-table" 10  (mHTableStep2string "ACCEPT" table oldAnalysis newAnalysis mhScore oldPosterior newPosterior oldAnaScore newAnaScore);
	  newAnalysis; 
	end 
      else    (*Reject*)
	let _ = (Utils.repeat (fun () -> FG.removeAnalysis grammar newAnalysis)  (int_of_float numCustomers))
	in let _ = (Utils.repeat (fun () -> FG.addAnalysis grammar oldAnalysis) (int_of_float numCustomers))
	in let _ = Globals.dbgMsg "mh-table" 10  (mHTableStep2string "REJECT" table oldAnalysis newAnalysis mhScore oldPosterior newPosterior oldAnaScore newAnaScore)
	in oldAnalysis
    end

(* Do a single MH sweep through the corpus -- note that this is a
   higher order function *)
let mhTableSweep func start grammar  = 
  let aux table (st, n) = 
    let tm1 = Sys.time () in
    let newAna = (resampleTable grammar table) in
    let tm2 =Sys.time () in
  
    let time = (tm2-.tm1) in
    let stats = (func st grammar [||] newAna newAna [] time n) in
  let _ = 	Globals.dbgMsg "mh-table" 7 ("Here.") in
      begin
	Globals.dbgMsg "mh-table" 7 ("MH Table Sample performed in  " 
				      ^ (string_of_float (tm2-.tm1)) 
				      ^ " seconds.\n");
	(stats, (n+1));
      end
  in  FG.foldTables aux grammar (start,0)
