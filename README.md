# fragment-grammars

* Generate AG
vicare --r6rs-script code/generate-AG.ss inPrefix outPrefix inDir/ outDir/

* Generate other grammars (MDPCFG, DOP, GDMN) 
vicare --r6rs-script code/generate-alternate-grammars.ss inPrefix outPrefix inDir/ outDir/

Note: outDir/ must have been created before caling the scripts.
