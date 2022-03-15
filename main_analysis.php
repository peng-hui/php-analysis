<?php
if (count($argv) <= 1){
    print("Please Input File/Directory Location\n");
    exit(1);
}

include_once "includes.php";
$appdir = $argv[1];
if(file_exists($appdir)) {
    //$superglobal = ["_GET", "_POST", "_FILES", "_SESSION", "_REQUEST", "_COOKIE", "_SERVER"];
    $abspath = realpath($appdir);
    $spaces_classes = constructcfg_app($abspath);
    //$functionmap = []; //@global
    // if only one function/method with this function name
    //      funcname => class
    // else
    //      funcname => number of appear
    $nodeindex = 1; // @global
    Store::$true_node =  new PhpParser\Node\Expr\ConstFetch(new PhpParser\Node\Name('True'));

    //$idmaptonode = []; // @global

    //$analysisinformation = [];  // @global
    // init data for global use
    $path = str_replace('/', '_', $abspath);
    foreach($spaces_classes[1] as $classname => $class){
        Store::$analysisinformation[$classname] = [];
        foreach($class->classmethods as $name => $method) {
            $analyser_name = str_replace('/', '_', $abspath) ."_" . str_replace('/', '_', $name);
            $analyser = new TaintAnalysis($method, $analyser_name, $path); // something actions in the constructor functions

            // add filename to our analyser
            $filename = $method->filename;
            $analyser->rundir = dirname($filename);

            $analyser->currentfiledir = $filename;
            // $analyser->starttaintanalysis();  inside analyser, will use global analysisinformation
            Store::$analysisinformation[$classname][$name] = $analyser; // record the analyser information for replay usage
        }
    }
    // run analyser
    foreach(Store::$analysisinformation as $classname => $class){
        foreach($class as $name => $analyser) {
            
            $analyser->starttaintanalysis(); 
        }
    }
}
else{
    print("File/Directory " . $appdir . "Not Exists\n");
}
?>
