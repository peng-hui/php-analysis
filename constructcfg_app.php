<?php
// construct cfgs for the whole apps

include_once "includes.php";
use PhpParser\ParserFactory;


function constructcfg_app($appdir){
    $filelist = traversefolder($appdir); # get abs path of files
    Store::$filenamelist = $filelist;
    //$functionmap = []; //@good
    // if only one function/method with this function name
    //      funcname => class
    // else
    //      funcname => number of appear

    $allclasses = [];
    $allclasses[MAIN_CLASS] = new MyClass(MAIN_CLASS);
    $allnamespaces = [];
    $allnamespaces[GLOBAL_SPACE] = new MyNamespace(GLOBAL_SPACE);
    foreach($filelist as $filename){
        $maincfg_space = constructcfg_file($filename);

        //foreach($maincfg_space->namespaces as $space) {
        //    $allnamespaces[$space->spacename] = $space;
        //}
        foreach($maincfg_space->classes as $classname => $class ){
            if($classname == MAIN_CLASS) {
                foreach($class->classmethods as $methodname => $method){
                    $allclasses[MAIN_CLASS]->classmethods[$methodname] = $method;
                }
            }
            else{
                $allclasses[$class->classname] = $class;
            }
        }
        #$allclasses[MAIN_CLASS]->classmethods[$filename] = $maincfg_space_class[0];
        #filename
        Store::$file2classfunc[$filename] = $maincfg_space;
    }
    /*
    foreach($allnamespaces as $spacename => $namespace){
        printcfg_namespace($namespace);
    }
     */
    #foreach($allclasses as $classname => $class)
    #    printcfg_class($class);

    //printcfg_app($allclasses, $allnamespaces);
    return [$allnamespaces, $allclasses];
}

function printcfg_namespace($space){
    print("n: ". $space->spacename ."\n");
    if(count($space->classes) > 0){
        foreach($space->classes as $class)
            printcfg_class($class);
    }
    if(count($space->namespaces) > 0){
        foreach($space->namespaces as $subspacename => $subspace)
            printcfg_namespace($subspace);
            #$x = 1;
    }
}

function printcfg_class($class){
    #foreach($classes as $classname => $class) {
        $string = "c: " .$class->classname . ":\n";
        foreach($class->classmethods as $methodname => $method) {
            $string .= "   f: " . $methodname ."\n";
        }
    #}
    print($string);
}
function printcfg_app($classes, $allnamespaces) {
    $string = "";
    foreach($classes as $classname => $class) {
        printcfg_class($class);
    }
    foreach($allnamespaces as $spacename => $space) {
        if(count($space->classes ) > 0)
            printcfg_namespace($space);
    }
    
    print($string);
}


function constructcfg_file($filename) {
    // Here we cannot simply open file using filename
    // maybe path needed
	$file = fopen($filename, "r");
	$parser = (new ParserFactory)->create(ParserFactory::PREFER_PHP7);
	$contents = fread($file, filesize($filename));
	$stmts=array();
	try {
		$stmts = $parser->parse($contents);	
	} catch(PhpParser\Error $e) {
	  	echo 'Parse Error: ',$e->getMessage();
	}
	fclose($file);	
    $space = constructcfg_namespace(GLOBAL_SPACE, $stmts, $filename);
    $space->filename = $filename;
    return $space;
}


function constructcfg_namespace($spacename, $stmts, $main_funcname) {
    $space = new MyNamespace($spacename);
    //print("length ". count($stmts). "\n");
	$body = CFG::constructcfg($stmts); // it shoudl ignore the classes and functions
    // constructcfg returns 
	$space_class = constructcfg_namespace_and_class($spacename, $stmts, $main_funcname);
    // construct namespace
    //
    $main_cfg = new MyFunction($spacename, "MAIN_CLASS", $main_funcname);
    $main_cfg->filename = $main_funcname;
    $main_cfg->start = $body[0];
    $main_cfg->end = $body[1];

    $space->namespaces = $space_class[0];
    $space->classes = $space_class[1];
    $space->classes[MAIN_CLASS]->classmethods[$main_funcname] = $main_cfg;
    
    #$classes["MAIN_CLASS"]->classmethods[$filename] = $main_cfg;# here construct a main class
    //foreach($classes["MAIN_CLASS"]->classmethods as $name => $method){
    //    echo "why??? ". $name ."\n";
    //}
    //print"==============================================================\n";
    //print "END OF FILE [ ". $filename   . " ]\n";
	return $space;
}

function updatefunctionmap($funcname, $classname){
    //global $functionmap;
    if(isset(Store::$functionmap[$funcname])) {
        if(!is_int(Store::$functionmap[$funcname]))
            Store::$functionmap[$funcname] = 2;
        else{
            Store::$functionmap[$funcname] += 1;
        }
    }
    else{
        Store::$functionmap[$funcname] = $classname;
    }
}


function constructcfg_namespace_and_class($spacename, $stmts, $main_funcname) { 
    //print("comming into process_funcClass\n");
    $classes = [];
    $class_node = new MyClass($spacename, "MAIN_CLASS");
    $class_node->filename = $main_funcname; 
    $namespaces = [];
	foreach($stmts as $stmt) {
	    if($stmt instanceof PhpParser\Node\Stmt\Function_ ){ ///|| $stmt instanceof PhpParser\Node\Stmt\ClassMethod) {
            // here we conclude it into main class because it is a global function.
            $cfg = constructcfg_function($spacename, $stmt, "MAIN_CLASS");
            $cfg->filename = $main_funcname;
            $class_node->classmethods[$cfg->funcname] = $cfg;
            updatefunctionmap($cfg->funcname, MAIN_CLASS);
	    }
        elseif($stmt instanceof PhpParser\Node\Stmt\Class_) {
            //print "in constructing file: found a class xixi\n";
            $class = constructcfg_class($spacename, $stmt, $main_funcname);
            $class->filename = $main_funcname;
            $classes[$class->classname] = $class;
        }
        /*
        elseif($stmt instanceof PhpParser\Node\Stmt\Namespace_) {
            $spacename1 = getspacename($stmt->name);
            #$space = new MyNamespace($spacename);
            $space = constructcfg_namespace($spacename1, $stmt->stmts, $spacename . "_" . MAIN_FUNCTION_NAME ); // return namespaces classes and functions
            $space->filename = $main_funcname;
            #$space->namespaces = $space_class[0];
            #$space->classes = $space_class[1];
            $namespaces[$space->spacename] = $space;
        }
         */
        else{
            // print get_class($stmt);
            // print get_class($stmt->expr);
        }
    }
    $classes["MAIN_CLASS"] = $class_node;
	return [$namespaces, $classes];
}

function getspacename($name) {
    if ($name instanceof PhpParser\Node\Name){
        // name->parts
        $spacename = "";
        foreach($name->parts as $part) {
            $spacename .= $part . "\\";
        }
    }
    elseif($name instanceof PhpParser\Node\Identifier) {
        $spacename = (string)$name->name;
    }
    else{
        try{
            $spacename = (string)$name;
        }
        catch(Exception $e){
            $spacename = "WRONG_SPACE";
        }
    }
    if ($spacename == ""){
        $spacename = GLOBAL_SPACE;
    }
    return $spacename;
}

function constructcfg_function($spacename, $stmt, $classname) {
    $func = new MyFunction($spacename, $classname, (string)$stmt->name);
    //print("construct function\n");
    //print(get_class($stmt) ."\n");
    $body = CFG::constructcfg($stmt->stmts);
    //print("after construct function\n");
    $func->start = $body[0];
    $func->end = $body[1];
    foreach($stmt->params as $param) {
        $func->params[] = $param;
        #$func->Vars[(string)$param->var->name] = $param->var;
    }
    $func->classname = $classname;
    $func->startnodeid = $func->start->nodeid;
    $func->endnodeid = $func->end->nodeid;
    return $func;
}


function constructcfg_class($spacename, $class_stmt, $main_funcname) {
    $class_node = new MyClass($spacename, (string)$class_stmt->name);
    foreach($class_stmt->stmts as $stmt) { 
    	// it is not function, then it should be something like assignments, variables...
        if($stmt instanceof  PhpParser\Node\Stmt\Property) {
            //print "In class [" .$class_node->classname ."] Found a non function elements\n";
            foreach($stmt->props as $prop) {
                if($prop->default)
                    $class_node->props[(string)$prop->name] = $prop->default; #new PhpParser\Node\Expr\Variable((string)$prop->name);// new CFGNodeClassProperty($stmt->flags, $prop);
                else
                    $class_node->props[(string)$prop->name] = new PhpParser\Node\Expr\Variable((string)$prop->name);// new CFGNodeClassProperty($stmt->flags, $prop);
                // here we should split the properties into several parts
                // since it is allowed in the grammer of PHP to use only one 
                // flag for several property, separated by ",";
            }
        }
        else if ($stmt instanceof PhpParser\Node\Stmt\ClassMethod) {
            //print "In class [" .$class_node->classname ."] Found a ".get_class($stmt) . " [".$stmt->name  . "] \n";
            $cfg = constructcfg_function($spacename, $stmt, $class_node->classname);
            $cfg->filename = $main_funcname;
            $class_node->classmethods[$cfg->funcname] = $cfg;
            updatefunctionmap($cfg->funcname, $class_node->classname);
        }
        else if($stmt instanceof PhpParser\Node\Stmt\ClassConst) {
            //print "In class [" .$class_node->classname ."] Found a ".get_class($stmt) ." \n";
            foreach($stmt->consts as $const){
                $class_node->consts[(string)$const->name->name] = $const->value;
            }
        }
        else
            print "unrecognized type: " . get_class($stmt) . "\n";
    }
    return $class_node;
}
/**
 * Define a function to traverse all files ending with '.php'
 * absolute file name/address is returned in an array
 */
function traversefolder($path){
    $filelist = [];
    if(is_dir($path))
        $handle = opendir($path);
    else
        return [$path];
    
    while($entry = readdir($handle)){
        if($entry == '.' or $entry == '..'){
            // skip coming back
        }
        elseif(!is_dir($path . "/" . $entry)){
            if (substr($entry, -4) == '.php')
                $filelist[] = $path . "/" .$entry;
        }
        else{
            $files = traversefolder($path . "/" . $entry);
            foreach($files as $file){
                $filelist[] = $file;
            }
        }
    }
    return $filelist;
}

