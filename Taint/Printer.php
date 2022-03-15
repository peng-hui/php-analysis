<?php

include_once __DIR__ ."/../includes.php";

// Gets the string representation of the LHS variable
// in an assignment.


/// add by lph to print the constraints because they combine both of them.
function PrintStmt_Expr($stmts) {
	 $prettyPrinter = new PhpParser\PrettyPrinter\Standard;
     $code = '';
     foreach($stmts as $stmt) {
         if($stmt && $stmt instanceof PhpParser\Node\Stmt)
	     $code .= $prettyPrinter->prettyPrint(array($stmt));
         else if($stmt && $stmt instanceof PhpParser\Node\Expr)
                $code .= $prettyPrinter->prettyPrintExpr(array($stmt));
     }
     print $code .'\n';

}
// Prints a sequence of statements with a pretty printer.

function printStmts($stmts) {
	 $prettyPrinter = new PhpParser\PrettyPrinter\Standard;
     if (is_array($stmts))
	    $code = $prettyPrinter->prettyPrint($stmts);
     else
	    $code = $prettyPrinter->prettyPrint([$stmts]);
	 //print $code."\n";
     return $code ."\n";
 }

// Prints an expression with a pretty printer.

function PrintExpr($exprs) {
    $prettyPrinter = new PhpParser\PrettyPrinter\Standard;
    $code = '';
    if (!$exprs)
        return '';
    if(is_string($exprs)) {
        $code =  "WARNING: IS_STRING: ".$exprs . "\n";
        print $code;
        return $code;
    }
    if (is_array($exprs)){
        foreach($exprs as $expr) {
            $code .= $prettyPrinter->prettyPrintExpr($expr);
        }
    }
    else
        $code .= $prettyPrinter->prettyPrintExpr($exprs);
    
    //print $code."\n";
    return (string)$code."";
 }


// dump into a array/json format
function dumpExpr($expr){
    $dumper = new PhpParser\NodeDumper();
    $dumpdata = $dumper->dump($expr);
    return $dumpdata;

}

function dumpJSON($ast){
    $r = json_encode($ast, JSON_PRETTY_PRINT);
    //echo $r ."\n";
    return $r;
}
