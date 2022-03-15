<?php
//@file include files

// Genral order is required
// the early use, early includs
define ("IfCond", "IfCond", true);
define ("Cond", "Cond", true);
define ("LoopCond", "LoopCond", true);
define ("Stmt", "Stmt", true);
define ("Terminal", "Terminal", true);
define ("IfStmt", "IfStmt", true);
define ("LoopStmt", "LoopStmt", true);
define ("SwitchStmt", "SwitchStmt", true);
define ("Start", "Start", true);
define ("End", "End", true);
define ("ForEachLoop", "ForEachLoop", true);
define ("WhileLoop", "WhileLoop", true);
define ("ForLoop", "ForLoop", true);
define ("DoWhileLoop", "DoWhileLoop", true);
define ("MAIN_CLASS", "MAIN_CLASS", true);
define ("GLOBAL_SPACE", "GLOBAL_SPACE", true); # global namespace
define ("MAIN_FUNCTION_NAME", "MAIN_FUNCTION_NAME", true);

require __DIR__  . '/PHP-Parser-master/vendor/autoload.php';
require_once __DIR__ . '/DeepCopy/vendor/autoload.php';

// Definition files
include_once __DIR__ . '/Taint/Definitions.php';
include_once __DIR__ . '/Taint/CFGNode.php';
include_once __DIR__ . '/Taint/Class.php';
include_once __DIR__ . '/Taint/Namespace.php';
include_once __DIR__ . '/Taint/Function.php';

include_once __DIR__ . '/Taint/CFG.php';
include_once __DIR__ . '/Taint/Printer.php';

#include_once __DIR__ . '/Taint/Fuzz.php';
include_once __DIR__ .'/constructcfg_app.php';



#include_once __DIR__ ."/Taint/SymbolicOp.php";
// include_once __DIR__ ."/Taint/tmp2.php";
include_once __DIR__ ."/Taint/TaintAnalysis.php";
#include_once __DIR__ ."/Taint/SymbolicExecution.php";
#include_once __DIR__ ."/Taint/untitled.php";



?>
