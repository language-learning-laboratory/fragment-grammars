open FragmentGrammar
open Utils
open Histogram

module FG = FragmentGrammar
module H = Histogram

module FGStats =
struct
  
  (**************
   * Table Info *
   **************)
  
  (*  Stats to keep per table *)
  type tableInfo = {  
      mutable count: float;        
      mutable nodes: float;        
      mutable internal : float;   
      mutable leaves: float;       
      mutable leafv : float;        
      mutable leaft : float;       
      mutable leafrv : float;       
      mutable nonterm : float;     
      mutable depth : float;        
      mutable yieldlength : float;  
      mutable discontig: float;
      mutable structTypes: float;
      countHist : H.t;         
      nodesHist : H.t;     
      internalHist : H.t; 
      leavesHist : H.t; 
      leafvHist : H.t;
      leaftHist : H.t;
      leafrvHist : H.t;
      nontermHist : H.t;
      depthHist : H.t;
      yieldlengthHist : H.t;
      discontigHist : H.t; 
      structTypesHist : H.t;}
      
  let tableInfoHeader = 
    ["TableCount"; "Nodes"; "Internal"; "Leaves"; "LeafVariables"; "LeafTerminals";
     "LeafVarPercent"; "Nonterminals"; "Depth"; "YieldLength"; "Discontig"; "StructTypes"]
      
  let getInitialTableInfo  () = 
    {count=0.0;
     nodes=0.0;
     internal=0.0;
     leaves=0.0;
     leafv=0.0;
     leaft=0.0;
     leafrv=0.0;
     nonterm=0.0;
     depth=0.0; 
     yieldlength=0.0;
     discontig=0.0; 
     structTypes=0.0;
     countHist = H.create        "TableCount" 1.0 100;
     nodesHist = H.create        "Nodes" 1.0 100;     
     internalHist = H.create     "Internal-nodes" 1.0 100; 
     leavesHist = H.create       "Leaves" 1.0 100; 
     leafvHist = H.create        "LeafVariables" 1.0 100;
     leaftHist = H.create        "LeafTerminals" 1.0 100;
     leafrvHist = H.create       "LeafVarPercent" 0.01 100;
     nontermHist = H.create      "Nonterminals" 1.0 100;
     depthHist = H.create        "Depth" 1.0 50;
     yieldlengthHist = H.create  "YieldLength" 1.0 50;
     discontigHist = H.create    "Discontig" 1.0 50;
     structTypesHist = H.create   "StructTypes" 1.0 50; } 
      
  let tableInfoStringList   tableStats =
    [(string_of_float tableStats.count);
     (string_of_float tableStats.nodes);
     (string_of_float tableStats.internal);
     (string_of_float tableStats.leaves);
     (string_of_float tableStats.leafv);
     (string_of_float tableStats.leaft);
     (string_of_float tableStats.leafrv);
     (string_of_float tableStats.nonterm);
     (string_of_float tableStats.depth);
     (string_of_float tableStats.yieldlength);
     (string_of_float tableStats.discontig);
     (string_of_float tableStats.structTypes);]


  let openTableHists hash prefix suffix =
    begin
      (Hashtbl.add hash "TableCount" (open_out (prefix ^ ".TableCount" ^ suffix)));
       (Hashtbl.add hash "Nodes" (open_out (prefix ^ ".Nodes" ^ suffix)));
       (Hashtbl.add hash "Internal-nodes" (open_out (prefix ^ ".Internal-nodes" ^ suffix)));
       (Hashtbl.add hash "Leaves" (open_out (prefix ^ ".Leaves"  ^ suffix)));
       (Hashtbl.add hash "LeafVariables" (open_out (prefix ^ ".LeafVariables"  ^ suffix)));
       (Hashtbl.add hash "LeafTerminals" (open_out (prefix ^ ".LeafTerminals" ^ suffix)));
       (Hashtbl.add hash "LeafVarPercent" (open_out (prefix ^ ".LeafVarPercent"  ^ suffix)));
       (Hashtbl.add hash "Nonterminals" (open_out (prefix ^ ".Nonterminals"  ^ suffix)));
       (Hashtbl.add hash "Depth" (open_out (prefix ^ ".Depth"  ^ suffix)));
       (Hashtbl.add hash "YieldLength" (open_out (prefix ^ ".YieldLength" ^ suffix)));
       (Hashtbl.add hash "Discontig" (open_out (prefix ^ ".Discontig" ^ suffix)));
       (Hashtbl.add hash "StructTypes" (open_out (prefix ^ ".StructTypes" ^ suffix)));
    end

  let writeTableHists hash tableStats =
    begin
      try 
	H.writeHist (Hashtbl.find hash tableStats.countHist.name) tableStats.countHist;
	H.writeHist (Hashtbl.find hash tableStats.nodesHist.name) tableStats.nodesHist;
	H.writeHist (Hashtbl.find hash tableStats.internalHist.name) tableStats.internalHist;
	H.writeHist (Hashtbl.find hash tableStats.leavesHist.name) tableStats.leavesHist;
	H.writeHist (Hashtbl.find hash tableStats.leafvHist.name) tableStats.leafvHist;
	H.writeHist (Hashtbl.find hash tableStats.leaftHist.name) tableStats.leaftHist;
	H.writeHist (Hashtbl.find hash tableStats.leafrvHist.name) tableStats.leafrvHist;
	H.writeHist (Hashtbl.find hash tableStats.nontermHist.name) tableStats.nontermHist;
	H.writeHist (Hashtbl.find hash tableStats.depthHist.name) tableStats.depthHist;
	H.writeHist (Hashtbl.find hash tableStats.yieldlengthHist.name) tableStats.yieldlengthHist;
	H.writeHist (Hashtbl.find hash tableStats.discontigHist.name) tableStats.discontigHist;
	H.writeHist (Hashtbl.find hash tableStats.structTypesHist.name) tableStats.structTypesHist;
      with  Not_found -> failwith ("Name not found.")
    end
      
  let updateTableInfo stats table  =
    (* let _ = Globals.dbgMsg "stats" 1 ("Collecting stats on table in restaurant: "^ (FG.nt2string (FG.tableHead (ref table))) ^"\n")
    in let _ = if (FG.isPreterminalRest !(table.FG.rest)) then failwith "PRETERMIANL REST" else ()
    in let _ = Globals.dbgMsg "stats" 1 ("preterminal?: "^ (string_of_bool (FG.isPreterminalRest !(table.FG.rest))) ^"\n")
    in *) let structTypes = (float_of_int (Hashtbl.length table.FG.parseTrees))
    in begin
	stats.count     <- table.FG.tCnt     +. stats.count;
	stats.nodes     <- (float_of_int  table.FG.stats.FG.nodes)     +. stats.nodes;
	stats.internal  <- (float_of_int  table.FG.stats.FG.internal) +. stats.internal;
	stats.leaves    <- (float_of_int  table.FG.stats.FG.leaves)   +. stats.leaves;
	stats.leafv     <- (float_of_int  table.FG.stats.FG.leafv)    +. stats.leafv;
	stats.leaft     <- (float_of_int  table.FG.stats.FG.leaft)    +. stats.leaft;
	stats.leafrv    <- table.FG.stats.FG.leafrv                   +. stats.leafrv;
	stats.nonterm    <- (float_of_int table.FG.stats.FG.nonterm)   +. stats.nonterm;
	stats.depth      <- (float_of_int table.FG.stats.FG.depth)     +. stats.depth;
	stats.yieldlength<- (float_of_int table.FG.stats.FG.yieldlength) +.   stats.yieldlength;
	stats.discontig  <- (float_of_int table.FG.stats.FG.discontig) +. stats.discontig;
	stats.structTypes  <-  structTypes +. stats.structTypes;  
	H.add stats.countHist table.FG.tCnt;
	H.add stats.nodesHist (float_of_int table.FG.stats.FG.nodes);     
	H.add stats.internalHist (float_of_int table.FG.stats.FG.internal); 
	H.add stats.leavesHist (float_of_int table.FG.stats.FG.leaves); 
	H.add stats.leafvHist (float_of_int table.FG.stats.FG.leafv);
	H.add stats.leaftHist (float_of_int table.FG.stats.FG.leaft);
	H.add stats.leafrvHist table.FG.stats.FG.leafrv;
	H.add stats.nontermHist (float_of_int table.FG.stats.FG.nonterm);
	H.add stats.depthHist (float_of_int table.FG.stats.FG.depth);
	H.add stats.yieldlengthHist (float_of_int table.FG.stats.FG.yieldlength);
	H.add stats.discontigHist (float_of_int table.FG.stats.FG.discontig);
	H.add stats.structTypesHist  structTypes;
      end

  let accumulateTableInfo first second =
    begin
      first.count     <- first.count +. second.count;
      first.nodes     <- first.nodes +. second.nodes;
      first.internal  <- first.nodes +. second.nodes;
      first.leaves    <- first.nodes +. second.nodes;
      first.leafv     <- first.leafv +. second.leafv;
      first.leaft     <- first.leaft +. second.leaft;
      first.leafrv    <-  first.leafrv +. second.leafrv;
      first.nonterm   <- first.nonterm +. second.nonterm;
      first.depth     <- first.depth   +. second.depth;
      first.yieldlength<- first.yieldlength +.   second.yieldlength;
      first.discontig  <- first.discontig +. second.discontig;
      first.structTypes  <- first.structTypes +. second.structTypes;
      H.merge first.countHist second.countHist;   
      H.merge first.nodesHist second.nodesHist;          
      H.merge first.internalHist second.internalHist;
      H.merge first.leavesHist second.leavesHist; 
      H.merge first.leafvHist  second.leafvHist;
      H.merge first.leaftHist  second.leaftHist;
      H.merge first.leafrvHist  second.leafrvHist;
      H.merge first.nontermHist second.nontermHist;
      H.merge first.depthHist  second.depthHist;
      H.merge first.yieldlengthHist second.yieldlengthHist;
      H.merge first.discontigHist  second.discontigHist;
      H.merge first.structTypesHist  second.structTypesHist;
    end

 (* (**************
   * Baserule Info *
   **************)
  (*  Stats to keep per table *)
  type brInfo = {  
      mutable brStructTypes: float;        
      brStructTypesHist : H.t;}
      
  let brInfoHeader = 
    ["BaseruleStructTypes"]
      
  let getInitialBrInfo  () = 
    {brStructTypes=0.0;
     brStructTypesHist = H.create   "BaseruleStructTypes" 1.0 50; } 
      
  let brInfoStringList   tableStats = 
    [ (string_of_float tableStats.brStructTypes);]

  let openBrHists hash prefix suffix =
     begin
       (Hashtbl.add hash "BaseruleStructTypes" (open_out (prefix ^ "BaseruleStructTypes" ^ suffix)));
    end

  let writeBrHists hash brStats =
    begin
      H.writeHist (Hashtbl.find hash brStats.brStructTypesHist.name) brStats.brStructTypesHist;
    end
      
  let updateBrInfo stats br  =
    begin
      (* Globals.dbgMsg "stats" 1 ((FG.br2string br)^"\n");*)
      stats.brStructTypes  <-  (float_of_int (Hashtbl.length br.FG.structTypes)) +. stats.brStructTypes;  
      H.add stats.brStructTypesHist (float_of_int (Hashtbl.length br.FG.structTypes));
    end

  let accumulateBrInfo first second =
    begin
      first.brStructTypes  <- first.brStructTypes +. second.brStructTypes; 
      H.merge first.brStructTypesHist  second.brStructTypesHist;
    end *)
      
  (*******************
   * Restaurant Info *
   *******************)
      
  type restaurantInfo = {
      mutable numRestaurants : float;   (* Total number of restaurants with more than customer in the grammar *)
      mutable numTables : float;        (* Total number of tables in the grammar *)
      mutable numCustomers : float;     (* Total number of customers in the grammar *)
      mutable typeTokenRatio : float;   (* Total type-to-token ratio added over restaurants in the grammar *) 
      mutable numBaserules : float;     (* Total number of baserules in the grammar *)
      mutable avgBaseRuleUsage : float; (* Total of the mean number of tables each baserule is used at in the grammar. *)
      restNumTablesHist : H.t;
      numCustomersHist : H.t; 
      typeTokenRatioHist : H.t;
      numBaserulesHist : H.t; 
      avgBaseRuleUsageHist : H.t;}

  let restaurantInfoHeader = ["NumRestaurants"; "NumTables"; "NumCustomers"; "TypeTokenRatio"; "NumBaseRules"; "BaseRuleUsage"]
    
  let getInitialRestaurantInfo () = 
    {numRestaurants = 0.0;
     numTables = 0.0;
     numCustomers=0.0;
     typeTokenRatio=0.0;
     numBaserules=0.0;
     avgBaseRuleUsage=0.0;
     restNumTablesHist = H.create "NumTables" 10.0 100;
     numCustomersHist = H.create "NumCustomers" 10.0 1000;
     typeTokenRatioHist = H.create "TypeTokenRatio" 0.01 100;
     numBaserulesHist = H.create "NumBaseRules" 1.0 100;
     avgBaseRuleUsageHist = H.create "BaseRuleUsage" 1.0 100;}
      
  let restaurantInfoStringList   restaurantStats = 
    [  (string_of_float restaurantStats.numRestaurants);
       (string_of_float restaurantStats.numTables);
      (string_of_float restaurantStats.numCustomers);
      (string_of_float restaurantStats.typeTokenRatio);
      (string_of_float restaurantStats.numBaserules);
      (string_of_float restaurantStats.avgBaseRuleUsage);]


  let openRestaurantHists hash prefix suffix =
     begin
       (Hashtbl.add hash "NumTables" (open_out (prefix ^ ".NumTables"  ^ suffix)));
       (Hashtbl.add hash "NumCustomers" (open_out (prefix ^ ".NumCustomers" ^ suffix)));
       (Hashtbl.add hash "TypeTokenRatio" (open_out (prefix ^ ".TypeTokenRatio" ^ suffix)));
       (Hashtbl.add hash "NumBaseRules" (open_out (prefix ^ ".NumBaseRules"  ^ suffix)));
       (Hashtbl.add hash "BaseRuleUsage" (open_out (prefix ^ ".BaseRuleUsage"  ^ suffix)));
    end

 let writeRestaurantHists hash restStats =
   begin
     try
       H.writeHist (Hashtbl.find hash restStats.restNumTablesHist.name) restStats.restNumTablesHist;
       H.writeHist (Hashtbl.find hash restStats.numCustomersHist.name) restStats.numCustomersHist;
       H.writeHist (Hashtbl.find hash restStats.typeTokenRatioHist.name) restStats.typeTokenRatioHist;
       H.writeHist (Hashtbl.find hash restStats.numBaserulesHist.name) restStats.numBaserulesHist;
       H.writeHist (Hashtbl.find hash restStats.avgBaseRuleUsageHist.name) restStats.avgBaseRuleUsageHist;
     with  Not_found -> failwith ("Name not found.")
    end
      
  let updateRestaurantInfo stats rest =
    let nCsts = rest.FG.rCnt
    in if nCsts > 0.0 
      then let nTbls = (float_of_int (Hashtbl.length rest.FG.tbls))
	in let ratio = (nTbls /. nCsts)
	in let numBase = (float_of_int (List.length rest.FG.brs))
	in let avgBRUse =  (Utils.arithmeticMean (List.fold_left (fun a v -> !v.FG.brCnt :: a) [] rest.FG.brs))
	in if (Utils.is_nan ratio) 
	  then (failwith ("FGStats.updateRestaurantInfo: The ratio is not a number in restaurant: " 
			   ^ rest.FG.label.FG.nName ^ " (number tables) " 
			   ^ (string_of_float nTbls) ^ " (number customers) " 
			   ^ (string_of_float nCsts) ))
	  else begin
	      stats.numRestaurants <- stats.numRestaurants +. 1.0;
	      stats.numTables <- stats.numTables +. nTbls;
	      stats.numCustomers  <- nCsts +.   stats.numCustomers;
	      stats.typeTokenRatio<- ratio +.   stats.typeTokenRatio;
	      stats.numBaserules  <- numBase +. stats.numBaserules;
	      stats.avgBaseRuleUsage <- avgBRUse +. stats.avgBaseRuleUsage;
	      H.add stats.restNumTablesHist nTbls;
	      H.add stats.numCustomersHist nCsts;
	      H.add stats.typeTokenRatioHist  ratio;
	      H.add stats.numBaserulesHist  numBase;
	      H.add stats.avgBaseRuleUsageHist  avgBRUse;
	    end
      else ()
	
  (*******************
   * Per Restaurant  *
   *******************)
	
  type restaurantStats = {
      label : string;
      (* rs_a : float;
	 rs_b : float;
	 rs_stick : float;*)
      count : float;
      info : restaurantInfo;
      restaurantTables : tableInfo;}
      
  let restaurantStringList restStats =
    List.flatten 
      [[ (restStats.label); (*(string_of_float restStats.rs_a); (string_of_float restStats.rs_b); (string_of_float restStats.rs_stick);*)];
       (restaurantInfoStringList restStats.info);
       (tableInfoStringList restStats.restaurantTables);]
      
  let restaurantHeader rest =
    List.flatten
      [["Label"; (* "a";"b"; "stickiness"*)];
       restaurantInfoHeader;
       tableInfoHeader; ]
      
  (*******************
   * Analyses        *
   *******************)
  (* Stats for all analyses *)
  type analysisInfo = {
      mutable numAnalyses : float; (* The number of analyses in these totals *)
      mutable numNodesAna : float; (*Average number of nodes per analysis *)
      mutable tableNodeRatio : float; (* Average ratio of table/node per analysis *)
      mutable yieldLengthAna : float; (* Average yield length per analysis *)
      mutable tableYieldLenRatio : float; (*Average ratio of tables to the length of the analysis *) 
      mutable tblsPerYield : float; (* ratio of the number of tables which have yield items to length of the yield  *)
      mutable meanShared : float; (* The mean number of other analyses which share some part of an analysis *)
      numTablesAnaHist : H.t;
      numNodesAnaHist : H.t; 
      tableNodeRatioHist : H.t;
      yieldLengthAnaHist : H.t; 
      tableYieldLenRatioHist : H.t;
      tblsPerYieldHist : H.t; 
      meanSharedHist : H.t; }
      
  let analysisInfoHeader = ["NumAnalyses"; "NumNodes"; "TableNodeRatio"; "AnalysisYieldLength"; "TableYieldRatio"; "LeavedTablesPerYield"; "MeanSharedCustomers"]
    
  let getEmptyAnalysisInfo () =
    {numAnalyses = 0.0;
     numNodesAna= 0.0;
     tableNodeRatio= 0.0;
     yieldLengthAna= 0.0;
     tableYieldLenRatio= 0.0;
     tblsPerYield= 0.0;
     meanShared = 0.0;
     numTablesAnaHist = H.create "NumTablesAna" 1.0 100; 
     numNodesAnaHist = H.create "NumNodes" 1.0 100; 
     tableNodeRatioHist = H.create "TableNodeRatio" 0.01 100 ;
     yieldLengthAnaHist = H.create "AnalysisYieldLength" 1.0 100 ; 
     tableYieldLenRatioHist = H.create "TableYieldRatio" 0.01 100;
     tblsPerYieldHist = H.create "LeavedTablesPerYield" 0.05 100; 
     meanSharedHist = H.create "MeanSharedCustomers" 1.0 100; }
      
  let analysisInfoStringList  anaStats = 
    [ (string_of_float  anaStats.numAnalyses);
      (string_of_float  anaStats.numNodesAna);
      (string_of_float  anaStats.tableNodeRatio);
      (string_of_float  anaStats.yieldLengthAna);
      (string_of_float  anaStats.tableYieldLenRatio);
      (string_of_float  anaStats.tblsPerYield);
      (string_of_float  anaStats.meanShared);]
      
  let openAnalysisHists hash prefix suffix =
     begin
       (Hashtbl.add hash "NumTablesAna" (open_out (prefix ^ ".NumTablesAna" ^ suffix)));
       (Hashtbl.add hash "NumNodes" (open_out (prefix ^ ".NumNodes" ^ suffix)));
       (Hashtbl.add hash "TableNodeRatio" (open_out (prefix ^ ".TableNodeRatio" ^ suffix)));
       (Hashtbl.add hash "AnalysisYieldLength" (open_out (prefix ^ ".AnalysisYieldLength" ^ suffix)));
       (Hashtbl.add hash "TableYieldRatio" (open_out (prefix ^ ".TableYieldRatio" ^ suffix)));
       (Hashtbl.add hash "LeavedTablesPerYield" (open_out (prefix ^ ".LeavedTablesPerYield" ^ suffix)));
       (Hashtbl.add hash "MeanSharedCustomers" (open_out (prefix ^ ".MeanSharedCustomers" ^ suffix)));
    end

  let writeAnalysisHists hash anaStats =
    begin
      try
	H.writeHist (Hashtbl.find hash anaStats.numTablesAnaHist.name) anaStats.numTablesAnaHist;
	H.writeHist (Hashtbl.find hash anaStats.numNodesAnaHist.name) anaStats.numNodesAnaHist;
	H.writeHist (Hashtbl.find hash anaStats.tableNodeRatioHist.name) anaStats.tableNodeRatioHist;
	H.writeHist (Hashtbl.find hash anaStats.yieldLengthAnaHist.name) anaStats.yieldLengthAnaHist;
	H.writeHist (Hashtbl.find hash anaStats.tableYieldLenRatioHist.name) anaStats.tableYieldLenRatioHist;
	H.writeHist (Hashtbl.find hash anaStats.tblsPerYieldHist.name) anaStats.tblsPerYieldHist;
	H.writeHist (Hashtbl.find hash anaStats.meanSharedHist.name) anaStats.meanSharedHist;
      with Not_found -> failwith "Name not found"
    end

  let updateAnalysisInfo stats ana  = 
    let (numNodes, numTables, yieldLength, yieldAttributions, meanShared1) = (FG.getAnalysisStats ana)
    in let meanShared = (Utils.arithmeticMean meanShared1)
    in let tableNodeRatio = (numTables /.numNodes)
    in let tableYieldLenRatio = (numTables /. yieldLength)
    in let numTableYield = (float_of_int (List.length (Utils.unique yieldAttributions)))
    in let tblsPerYield = (numTableYield /. yieldLength)
    in begin 
	stats.numAnalyses <- stats.numAnalyses +. 1.0;
	stats.numNodesAna<- numNodes +. stats.numNodesAna;
	stats.tableNodeRatio<- tableNodeRatio +. stats.tableNodeRatio;
	stats.yieldLengthAna<- yieldLength +. stats.yieldLengthAna;
	stats.tableYieldLenRatio<- tableYieldLenRatio +. stats.tableYieldLenRatio;
	stats.tblsPerYield<- tblsPerYield +. stats.tblsPerYield;
	stats.meanShared <- meanShared +. stats.meanShared;
	
	H.add stats.numTablesAnaHist numTables;
	H.add stats.numNodesAnaHist numNodes; 
	H.add stats.tableNodeRatioHist  tableNodeRatio ;
	H.add stats.yieldLengthAnaHist  yieldLength; 
	H.add stats.tableYieldLenRatioHist tableYieldLenRatio;
	H.add stats.tblsPerYieldHist tblsPerYield; 
	H.add stats.meanSharedHist meanShared;
      end

(*******************
   * All Statistics     *
   *******************)
      
  type stats = {
      (*globalBaserules : brInfo;*)
      globalTables : tableInfo;
      globalRests : restaurantInfo;
      analyses : analysisInfo;
      restaurants : (FG.nonterminal, restaurantStats) Hashtbl.t;}
      
  (******************************************
   *  Accumulation Functions                   *
   ******************************************)
  (* Calculated means and histograms for the tables in the grammar **globally** *)
  let calculateGlobalTables grammar =
    let doRest rest =
      let tinfo = getInitialTableInfo ()
      in begin 
	  (Hashtbl.iter (fun k tbl ->  (updateTableInfo tinfo !tbl)) rest.FG.tbls);
	  tinfo;
	end
    in let gtinfo = (getInitialTableInfo ())
    in begin (Hashtbl.iter 
		 (fun label rest -> 
		   (*if not (FG.isPreterminalRest rest)
		   then*) (accumulateTableInfo gtinfo (doRest rest)))
		 grammar.FG.rsts);
	gtinfo;
      end

  (* Calculated means and histograms for the tables in the grammar **globally** *)
 (* let calculateGlobalBaserules grammar =
    let doRest rest =
      let brinfo = getInitialBrInfo ()
      in begin 
	  (List.iter (fun br ->  (updateBrInfo brinfo !br)) rest.FG.brs);
	  brinfo;
	end
    in let gbrinfo = (getInitialBrInfo ())
    in begin (Hashtbl.iter 
		 (fun label rest -> 
		   if not (FG.isPreterminalRest rest)
		   then (accumulateBrInfo gbrinfo (doRest rest)))
		 grammar.FG.rsts);
	gbrinfo;
      end*)
      
  (* Calculated means and histograms for the restaurants in the grammar **globally** *)    
  let calculateGlobalRests grammar  =
    let rinfo =  (getInitialRestaurantInfo ())
    in begin 
	(Hashtbl.iter 	      
	    (fun label rest -> 
	      (*if not (FG.isPreterminalRest rest)
	      then*) if rest.FG.rCnt > 0.0
		then (updateRestaurantInfo rinfo rest))
	    grammar.FG.rsts);
	rinfo;
      end
      
  (* Calculated means and histograms for the tables in **each** restaurant. *)
  let calculateRestaurants grammar =
    let doRest r = 
      { label =r.FG.label.FG.nName;
	(*rs_a = r.FG.a;
	rs_b = r.FG.b;
	 rs_stick = r.FG.stickiness;*)
	count =r.FG.rCnt;
	info= (let rinfo = (getInitialRestaurantInfo ()) in 
		 begin  
		   if r.FG.rCnt > 0.0
		   then (updateRestaurantInfo rinfo r);
		   rinfo; 
		 end);
	restaurantTables = (let tinfo = getInitialTableInfo () in 
			      begin 
				(Hashtbl.iter (fun k tbl ->  (updateTableInfo tinfo !tbl)) r.FG.tbls);
				tinfo;
			      end);}
    in let result = Hashtbl.create 1000
    in begin 
	( Hashtbl.iter 	      
	    (fun label rest ->  (* if not (FG.isPreterminalRest rest) then*) Hashtbl.add result label (doRest rest)) 
	    grammar.FG.rsts );
	result;
      end
      
  let calculateAnalyses anas =  
    let ainfo = (getEmptyAnalysisInfo ()) in
      begin
	List.iter (fun v -> updateAnalysisInfo ainfo v) anas;
	ainfo;
      end 
    
  let calculateStats grammar anas =
    {globalTables = (calculateGlobalTables grammar);
     (*globalBaserules = (calculateGlobalBaserules grammar);*)
     globalRests = (calculateGlobalRests grammar);
     analyses = calculateAnalyses anas;
     restaurants  = (calculateRestaurants grammar);}
	
  (******************************************
   *  Make output arrays                            *
   ******************************************)
      
  let statsStringList stats = List.flatten
    [(tableInfoStringList stats.globalTables);
     (*(brInfoStringList stats.globalBaserules);*)
     (restaurantInfoStringList stats.globalRests);
     (analysisInfoStringList stats.analyses);]
    
  (******************************************
   *  Make Header List                      *
   ******************************************)
    
  let statsHeader grammar = List.flatten
    [ (tableInfoHeader);
      (restaurantInfoHeader);
      (analysisInfoHeader);]

  (******************************************
   *  Manage individual restaurant files     *
   ******************************************)
  let createRestaurantOutChannels resthash grammar prefix suffix =
    let doRest r =
      let outfilename = prefix^"."^r.FG.label.FG.nName^suffix 
      in let ch = open_out outfilename
      in begin
	  output_string ch ((Utils.getCSV (restaurantHeader r)) ^ "\n");
	  flush ch;
	  ch;
	end
    in ( Hashtbl.iter 	      
	  (* (fun label rest ->  if not (FG.isPreterminalRest rest) then Hashtbl.add resthash label (doRest rest)  ) *)
	  (fun label rest ->  Hashtbl.add resthash label (doRest rest)  )
	   grammar.FG.rsts)
      
  let writeRestaurants g hash stats =
    let doRest label ch =
      let info = try
	  (Hashtbl.find stats.restaurants label)
	with  Not_found -> failwith ("Restaurant: " ^ (FG.nt2string label) ^ " not found.")
      in begin
	  output_string ch ((Utils.getCSV (restaurantStringList info)) ^  "\n");
	  flush ch;
	end
    in ( Hashtbl.iter 	      
	   (*(fun label ch -> if not (FG.isPreterminalRest (FG.getRestaurant g label)) then (doRest label ch)) *)
	   (fun label ch -> (doRest label ch)) 
	   hash)
    
  let initHistograms hash prefix suffix =
    begin
      openTableHists hash prefix suffix;
      (*openBrHists hash prefix suffix;*)
      openRestaurantHists hash prefix suffix;
      openAnalysisHists hash prefix suffix;
    end 

   let writeHistograms hash stats = 
     begin
	
       writeTableHists hash stats.globalTables;
       (*writeBrHists hash stats.globalBaserules;*)
       writeRestaurantHists hash stats.globalRests;
       writeAnalysisHists hash stats.analyses;
     end


end
  
