<?php
include_once __DIR__ ."/../includes.php";

define ("OBJECT_START", 1000, true); // 1000 - 100000
define ("ARRAY_START", 10000000, true); // 10000000 -> 

class TaintAnalysis{
    public $spacename = "";
    public $classname = "";
    public $funcname = "";
	public $params = [];
	public $taintedvars = [];
	public $sanitizedvars = [];
    public $taintreturn = false;
    public $arrays = [];
    public $objects = [];
    public $objectindex = OBJECT_START;
    public $arrayindex = ARRAY_START;
    public $arraymap = []; # name => object index
    public $objectmap = []; # name => object index

    public $analysername = "";
    public $resultpath = "";
    public $currentfiledir = "";
    public $rundir = "";

    public $current;
    public $testparamname = "";
    public $testparamid = ""; // idx insteadof name;

    public $paramaffectvars = [];
    // plan to have something like 
    // param1 => var1, var2 ...
    // param2 => var2, var2 ...

    public $paramaffectreturn = [];

    // param => true/false
    public $paramaffectloops = [];
    // param1 => [loopid1, loopid2....]
    // param2 => [loopid1, loopid2....]
    public $paramaffectcallsites = [];
    public $paramaffectcallsiteswithloops = [];

    public $loops = [];
    // nodeid => loop node
    public $taintedloops = [];

    public $withloop = false; // if it is set to false mean no loop inside
    // a list of nodeids
    public $taintedcallsites = [];

    public $callsites = []; // used for all callsites in this function. and the key is the nodeid, and the value is a list of callsites. 
    // each callsite is in the structure of callsite.
    public $callsiteindex = 0;
    // for interprecedural analysis, we log
    // callsite information, whth arg information.
    public $returnnodes = []; # records the nodes of return
    public $returncvpairs = [];
    public $issource = false; // in istaintedexpr see whether current node is a source
    public $sources = [];
    // should consider loop pah
    // maybe can construct new structure for loop

    public $start;
    public $end; 

    public $taintanalysisflag = false;
    public $symbolicexecutionflag = false;

    public $logs = "";
    // Note that, it is for interprocedural analysis only.
    // to match the function you need.

    public function __construct($method, $analysername, $path){
        $this->analysername = $analysername;
        $this->resultpath = $path;
        $this->taintanalysisflag = false; // unvisited
        $this->symbolicexecutionflag = false;
        $superglobal = ["_GET", "_POST", "_FILES", "_SESSION", "_REQUEST", "_COOKIE", "_SERVER"];
        $this->start = $method->start;
        $this->end = $method->end;
        foreach($method->params as $param){
            $paramname = $param->var->name;
            $this->params[$paramname] = $param->var;
        }

        for($i = 0; $i < count($method->params); $i ++){
            $this->paramaffectreturn[$i] = false;

            // add superglobal to tainted of param
            $this->paramaffectvars[$i] = [];
            $this->paramaffectloops[$i] = [];
            $this->paramaffectcallsites[$i] = [];
            $this->paramaffectcallsiteswithloops[$i] = [];

            // add param itself
            $this->paramaffectvars[$i][$paramname] = true;
            foreach($superglobal as $v){
                $this->paramaffectvars[$i][$v] = true;
            }
        }
    }

    public function writecst2file($cstlist, $filename) {
        $t = "";
        $thr = "";
        //$cstlist = array_slice($cstlist, 0, 10); 
        foreach($cstlist as $cst){
            try{
                foreach($cst as $c){
                    if($c){
                       // $t .= "\t". PrintExpr($c); #
                        $t .= dumpJSON($c) . "==========";
                        $thr .= PrintExpr($c) . "   ";
                    }
                }
                $t .= "----------";
            }
            catch (Exception  $e){
                $t = "Unable to log constraints, error raised\n";
            }

            file_put_contents($filename, $t, FILE_APPEND);
            file_put_contents($filename . ".hr", $thr, FILE_APPEND);
        }
    }

    // $cstlist = $this->callsites($callsite);
    // bug in recursive function calls that causes into DoS iteself.
    public function callsiteanalysis($callsite, $taintargs, $filename, $callsiteflag, $layer) { 
        // taintedargs is in format like [true, true, false]
        // multilayer
        if($layer > 10)
            return;
        $layer ++;
        $filename = $filename . '-';

        $expr = $callsite->expr;
        $function = $this->fetchfunction($expr);
        $function = $this->fetchfunction($callsite->expr); // fetch the analyser
        if (is_string($function)) {
            // it is a builtin function
            return;
        }
        if(!file_exists($filename))
            mkdir($filename, 0777);
        // function paramaffect
        $loopindex = 0;
        foreach($taintargs as $i => $v) {
            if($v) {
                foreach($function->paramaffectloops[$i] as $nodeid) {
                    if($loopindex > 10)
                        return;
                    // from node id to start
                    $loopfilename = $filename . "/loop" . $loopindex;
                    $loopindex ++;
                    $cstlist = $this->backwardsse_rec($function->start, Store::$idmaptonode[$nodeid], [[Store::$true_node]]);
                    // write thing down
                    $this->writecst2file($cstlist, $loopfilename);
                }
            }
        }

        $callsiteindex = 0;
        foreach($taintargs as $i => $v) {
            if($v) {
                foreach($function->paramaffectcallsiteswithloops[$i] as $nodeid => $callsiteid) {
                    if($callsiteindex > 10)
                        return;
                    # test whether it is visited before
                    # see whether it is in the current callsiteflag
                    #
                    // provent from the parent? call graph
                    if(isset($callsiteflag[$nodeid]) && isset($callsiteflag[$nodeid][$callsiteid])) {
                        // has already been visited
                        continue;
                    }
                    if(!isset($callsiteflag[$nodeid])) {
                        $callsiteflag[$nodeid] = [];
                    }
                    

                    // provent from current layer of callsite, avoid repeat
                    if(!isset($callsitevisited[$nodeid]))
                        $callsitevisited[$nodeid] = [];
                    if(array_key_exists($callsiteid, $callsitevisited[$nodeid])) {
                        continue;
                    }
                    else{
                        $callsitevisited[$nodeid][$callsiteid] = true;
                    }

                    $subcallsiteflag = [];
                    foreach($callsiteflag as $nodeid => $callsiteidlist){
                        $subcallsiteflag[$nodeid] = [];
                        foreach($callsiteidlist as $id => $v) {
                            $subcallsiteflag[$nodeid][$id] = $v;
                        }
                    }// get $calltainted_args
                    $subcallsiteflag[$nodeid][$callsiteid] = true;

                    $callsitefilename = $filename . "/call" . $callsiteindex;
                    $callsiteindex ++;
                    $cstlist = $this->backwardsse_rec($function->start, Store::$idmaptonode[$nodeid], [[Store::$true_node]]);
                    $this->writecst2file($cstlist, $callsitefilename);
                    // write things down
                    $n_callsite = $function->callsites[$nodeid][$callsiteid];
                    $call_taintargs = [];
                    foreach($taintargs as $i => $v) {
                        if($v) {
                            $ii = 0;
                            foreach($n_callsite->paramaffectargs[$i] as $r) {
                                if($r) {
                                    $call_taintargs[$ii] = true;
                                }
                                else{
                                    if(!isset($call_taintargs[$ii])) {
                                        $call_taintargs[$ii] = false;
                                    }
                                }
                                $ii ++;
                            }
                        }
                    }
                    $function->callsiteanalysis($n_callsite, $call_taintargs, $callsitefilename, $subcallsiteflag, $layer);
                }
            }
        }
        /*
        foreach($callsite->affectloops as $loopid => $v) {
            // inside the function.
            
            // if it is analysed!! it should definitely be analyzed before
            // then we should be able to get constraints by the id directly!! instead of analyze it again.
            // however I am not able to reach certain level
            // analyser get here
            $cstlist = $this->backwardsse_rec($function->start, Store::$idmaptonode[$loopid], [[Store::$true_node]]);
        }

        foreach($callsite->affectcallsiteswithloops as $callsiteid => $e) {
            // traverse from the callsitedid to the function start.
            // then together with constraints outside
            // given the callsiteid. we shoule also be able to get the callsides.
            $cstlist = $this->backwardsse_rec($function->start, Store::$idmaptonode[$callsidesid], [[Store::$true_node]]);
            // get another callsite again.
            // $nestedcallsite = $function->paramaffectcallsiteswithloops[];
        }
         */
    }
   
	public function starttaintanalysis(){
        //global $true_node;
        if($this->taintanalysisflag == True)
            return;
        $this->taintanalysisflag = true; // mark as visited
        $path = $this->taintanalysis_rec($this->start, $this->end);
        // can write down information here instead at each loop
        $resultdir = "/home/users/phli/cpu_dos/results/" .$this->resultpath ."/";

        if(! file_exists($resultdir))
            mkdir($resultdir, 0777);
        $source = "";
        foreach($this->sources as $s){
            $source .= $s . "\t";
        }
        file_put_contents($resultdir . "sources", $source, FILE_APPEND);
        file_put_contents($resultdir . "path", printpath($path)."\n\n=====\n", FILE_APPEND);

        // below just writing down what we need.
        $loopidx = 0;
        foreach($this->taintedloops as $nodeid){
            $current = Store::$idmaptonode[$nodeid];
            $loopstmts = printStmts([$current->stmt]);
            $filename = "loop"  . $loopidx;
            $loopidx += 1;
            file_put_contents($resultdir . $filename . ".php",  "<?php\n" .$loopstmts, FILE_APPEND);
            //if($printflag == false){
            //     $printflag == true;
            $cstlist = $this->backwardsse_rec($this->start, Store::$idmaptonode[$nodeid], [[Store::$true_node]]);
            $t = "";
            $thr = "";
            //$cstlist = array_slice($cstlist, 0, 10); 
            foreach($cstlist as $cst){
                try{
                    foreach($cst as $c){
                        if($c){
                            //$t .= "\t". PrintExpr($c);
                            $t .= dumpJSON($c) . "==========";
                            $thr .= PrintExpr($c) . "   ";
                        }
                    }
                    $t .= "----------";
                }
                catch (exception  $e){
                    $t = "unable to log: fatal error\n";
                }
                file_put_contents($resultdir . $filename , $t, FILE_APPEND);
                file_put_contents($resultdir . $filename . ".hr", $thr, FILE_APPEND);
            }
        }

        foreach($this->taintedcallsites as $nodeid_cid){ // writedowncallsie
            // comes here there are two posibilities, one is the callsites with loops directly another is nested for several layers with loops
            //
            $nodeid = $nodeid_cid[0];
            $callsiteid = $nodeid_cid[1];
            $taintargs = $nodeid_cid[2];
            $callsite = $this->callsites[$nodeid][$callsiteid];
            $expr = PrintExpr($callsite->expr);

            $filename = "callsite-" .  $callsite->nodeid . "-" . $callsiteid;
            $cstlist = $this->backwardsse_rec($this->start, Store::$idmaptonode[$nodeid], [[Store::$true_node]]);
            $this->writecst2file($cstlist, $resultdir . $filename);
            $callsiteflag = [];
            $callsiteflag[$nodeid] = [];
            $callsiteflag[$nodeid][$callsiteid] = true;
            $layer = 0;
            $this->callsiteanalysis($callsite, $taintargs, $resultdir . $filename, $callsiteflag, $layer);

        }
        // write log file
        file_put_contents($resultdir . "log", $this->logs, FILE_APPEND);
    }

 	/**
     * Recursively ananlyze the function
     * record the path for each node
     */
    public function taintanalysis_rec($start, $end){
        $current = $start;
        $returnpath = new Path();
        while($current && $current != $end) {
            //print($current->type."\n");
            $this->current = $current;
            $returnpath->steps[] = $current->nodeid;
            if($current->type == IfStmt) {
                $len = count($current->conds);
                $subpath = [];
                for($i = 0; $i < $len; $i ++) {
                    $this->current = $current;
                    $affectresult = $this->parampropagation_start($current->conds[$i]->cond);
                    $this->istaintedexpr($current->conds[$i]->cond);
                    if($this->issource && ! in_array($current->nodeid, $this->sources)) {
                        $this->sources[] = $current->nodeid;
                    }
                    $this->issource = false;
                    $subpath[] = $this->taintanalysis_rec($current->bodystarts[$i], $current->bodyends[$i]); //
                }

                if (isset($current->bodystarts[$len])){
                    $this->current = $current;
                    $affectresult = $this->parampropagation_start($current->conds[$len]->cond);
                    $subpath[] = $this->taintanalysis_rec($current->bodystarts[$len], $current->bodyends[$len]);
                }
                $returnpath->steps[]  = $subpath;
            } 
            elseif ($current->type == LoopStmt) {
                $this->Loops[$current->nodeid] = $current->stmt;
                $affectresult = $this->parampropagation_start($current->cond);
                foreach($affectresult as $paramid => $v){
                    if($v && ! array_key_exists($current->nodeid, $this->paramaffectloops[$paramid])) {
                        $this->paramaffectloops[$paramid][] = $current->nodeid; // add nodeid;
                    }
                }
                if($current->looptype == ForLoop) {
                    $istainted = false;
                    foreach($current->init as $ini){
                        $affectresult = $this->parampropagation_start($ini); //
                        /*
                        foreach($affectresult as $paramname => $v){
                            if($v && ! array_key_exists($current->nodeid, $this->paramaffectloops[$paramname])) {
                                $this->paramaffectloops[$paramname][] = $current->nodeid; // add nodeid;
                            }
                        }
                        */
                        $re1 = $this->istaintedexpr($ini);// || $re1[1]; // add this into foor wloops
                        if($re1 === true or $re1 === 1 or $re1 %2 === 1)
                            $istainted = true;
                    }
                    $re = $this->istaintedexpr($current->cond);
                    $re = $re === true or $re === 1 or $re %2 === 1;
                    $re2 = $this->istaintedexpr($current->loop);
                    $re2 = $re2 === true or $re2 === 1 or $re2 %2 === 1;
                    $affectresult = $this->parampropagation_start($current->loop); //

                    foreach($affectresult as $paramid => $v){
                        if($v && ! array_key_exists($current->nodeid, $this->paramaffectloops[$paramid])) {
                            $this->paramaffectloops[$paramid][] = $current->nodeid; // add nodeid;
                        }
                    }

                    $re = $re || $istainted || $re2;

                }
                elseif ($current->looptype == DoWhileLoop) {
                    $re = $this->istaintedexpr($current->cond);
                }
                elseif ($current->looptype == ForEachLoop) {
                    $re = $this->istaintedexpr($current->cond);
                }
                elseif ($current->looptype == WhileLoop) {
                    $re = $this->istaintedexpr($current->cond);
                }
                $re  = $re === true or $re === 1 or $re %2 === 1;
                if($re){
                    $this->taintedloops[] = $current->nodeid;
                    print("TAINTED LOOP " .$current->nodeid  . "\n");
                    // Do not write file here
                    // put it in the last
                }
                if($this->issource && ! in_array($current->nodeid,$this->sources))
                    $this->sources[] = $current->nodeid;
                $this->issource = false;
                //     // write down the constraints
                //     $printcst = dumpJSON($constraints);
                //     file_put_contents(dirname(__FILE__) ."/../output/". $this->writefilename ."/constraints". $GLOBAL_COUNT .".txt", $printcst, FILE_APPEND);
                //     $printcst = PrintExpr($constraints);
                //     file_put_contents(dirname(__FILE__) ."/../output/". $this->writefilename ."/constraints". $GLOBAL_COUNT .".hr", $printcst, FILE_APPEND);
                $subpath = $this->taintanalysis_rec($current->bodystart, $current->bodyend);
                $returnpath->steps[] = $subpath; // write down the path for each taint // do we need that?
            }

            elseif($current->type == Stmt){
                $affectresult = $this->parampropagation_start($current->stmt);
                $this->istaintedexpr($current->node);
                if($this->issource && ! in_array($current->nodeid, $this->sources))
                    $this->sources[] = $current->nodeid;
                $this->issource = false;
            }
            $current = $current->child; 
        }
        return $returnpath;
    }


	/** 
     *
	 * false: not tainted
     *
	 * true : tained
     *
	 **/
	public function istaintedexpr($expr){

		if($expr == null || $expr == NULL) {
			return false;
        }

        if($expr instanceof PhpParser\Node\Stmt\Expression){
            return $this->istaintedexpr($expr->expr);
        }

        else if($expr instanceof PhpParser\Node\Expr\BinaryOp){
        	$left = $this->istaintedexpr($expr->left);
            $right = $this->istaintedexpr($expr->right);
            return $left || $right;
        }
        else if ($expr instanceof PhpParser\Node\Expr\Assign ||
            $expr instanceof PhpParser\Node\Expr\AssignOp ||
            $expr instanceof PhpParser\Node\Expr\AssignRef){
            $right = $this->istaintedexpr($expr->expr);
            $lhs = $expr->var;
            if ($lhs instanceof PhpParser\Node\Expr\Variable) {
                $lhs_var = $lhs->name;
                if(is_string($lhs_var)) {
                    if($right === true || $right === 1 || $right % 2 === 1) { 
                        $this->taintedvars[$lhs_var] = true;
                        #$this->sanitizedvars[$lhs_var] = false;
                    }
                    else if($right === false || $right === 0 || $right %2 === 0){
                        #$this->taintedvars[$lhs_var] = false;
                        #$this->sanitizedvars[$lhs_var] = true;
                    }
                    if($right > ARRAY_START){ # which means newed a object or array 
                        $this->arraymap[$lhs_var] = $right >> 2;
                    }
                    else if ($right > OBJECT_START) {
                        $this->objectmap[$lhs_var] = $right >> 2;
                    }
                }
            }

            else if ($lhs instanceof PhpParser\Node\Expr\ArrayDimFetch) {
            
                if($lhs->var instanceof PhpParser\Node\Expr\Variable){
                    $arrayname = $lhs->var->name;
                }
                else{
                    return $right;
                }

                if(is_string($arrayname)) {
                    if(!isset($this->arraymap[$arrayname])){
                        return $right;
                    }
                    $arrayindex = $this->arraymap[$arrayname];
                    $dim = getvalofdim($lhs->dim);
                    if($dim == NULL){
                        return $right;
                    }
                    #if(!isset($this->arrays[$arrayname]->items[$dim])){
                    #    $this->arrays[$arrayname]->items[$dim] = $right;
                    #}
                    #else{
                    $this->arrays[$arrayindex]->items[$dim] = (bool)$right % 2;
                    #}
                }
            }
            else if($lhs instanceof PhpParser\Node\Expr\PropertyFetch){

                if($lhs->name instanceof PhpParser\Node\Expr\Variable){
                    // cannot infer variable type
                    return $right;
                }
                elseif($lhs->name instanceof PhpParser\Node\Identifier){
                    if(is_string($lhs->name->name))
                        $property_name = (string)$lhs->name->name;
                    elseif($lhs->name->name instanceof PhpParser\Node\Scalar\String_)
                        $property_name = (string)$lhs->name->name->value;
                    else{
                        return $right;
                    }

                }
                elseif($lhs->name instanceof PhpParser\Node\Scalar\String_){
                    $property_name = (string)$lhs->value;
                }

                $var = $lhs->var;
                if($var->name instanceof PhpParser\Node\Scalar\String_) {
                    $varname = (string)$var->name->value;
                }

                elseif(is_string($var->name)){
                    $varname = $var->name;
                }
                else{
                    return $right;
                }
                if(isset($this->objectmap[$varname])) {
                    #$this->sanitizedvars[$varname] = false;
                    $objectindex = $this->objectmap[$varname];
                    $this->objects[$objectindex]->props[$property_name] = (bool)$right % 2;
                }

                #if(! isset($this->objects[$varname]->props[$property_name])) {
                #}
                #return $this->objects[$varname]->props[$property_name];
            }
            return $right;

        }

        else if ($expr instanceof PhpParser\Node\Expr\ArrayDimFetch) {
            if(! $expr->var instanceof PhpParser\Node\Expr\Variable){
                return false;
            }
            $arrayname = $expr->var->name;

            if(strcasecmp($arrayname,"_GET") == 0 or strcasecmp($arrayname, "_POST") == 0 or strcasecmp($arrayname, "_FILES") == 0 or
                strcasecmp($arrayname, "_SESSION")== 0 or strcasecmp($arrayname, "_REQUEST") == 0 or strcasecmp($arrayname, "_COOKIE")== 0 or 
                strcasecmp($arrayname, "_SERVER") == 0){
                $this->issource = true; // current node is the source.
                return true;
            }
            if(is_string($arrayname)) {
                if(!isset($this->arraymap[$arrayname])){
                    return false;
                }
                $arrayindex = $this->arraymap[$arrayname];
                $dim = getvalofdim($expr->dim);
                if($dim == NULL){
                    return false;
                }
                if(!isset($this->arrays[$arrayindex]->items[$dim])){
                    $this->arrays[$arrayindex]->items[$dim] = false;
                }
                else{
                    return $this->arrays[$arrayindex]->items[$dim];
                }
            }
            return false;
        }

        else if($expr instanceof PhpParser\Node\Expr\Variable){
            if($expr->name instanceof PhpParser\Node\Scalar\String_){
                $varname = (string)$expr->name->value;
            }
            else if(is_string($expr->name)){
                $varname = $expr->name;
            }
            if(is_string($varname)){
                return array_key_exists($varname, $this->taintedvars) and $this->taintedvars[$varname] == true;
            }
            return false;
        }

        else if($expr instanceof PhpParser\Node\Expr\PostInc || 
                $expr instanceof PhpParser\Node\Expr\PostDec ||
                $expr instanceof PhpParser\Node\Expr\PreDec  ||
                $expr instanceof PhpParser\Node\Expr\PreInc ){
            
            return $this->istaintedexpr($expr->var);
        }

        else if($expr instanceof PhpParser\Node\Expr\UnaryMinus ||
                $expr instanceof PhpParser\Node\Expr\UnaryPlus){
            return $this->istaintedexpr($expr->expr);
        }
        
        else if($expr instanceof PhpParser\Node\Expr\FuncCall||  
                $expr instanceof PhpParser\Node\Expr\MethodCall||
            	$expr instanceof PhpParser\Node\Expr\StaticCall) { 
            // mark4
            // 8.29 how to do interprocedural analysis
            // 1. first find the function, especially when with namespace
            // analyze it if it is not yet
            // concat the information, can add the loop id.
            // manage all loop ids, one loop can come from several paths

            // function find method
            $istainted = false;
            $taintargs = [];
            $i = 0;
            foreach($expr->args as $arg) {
                $re = $this->istaintedexpr($arg->value);
                if($re === true or $re === 1 or $re %2 === 1){
                    $istainted = true;
                    $taintargs[$i] = true;
                }
                else{
                    $taintargs[$i] = false;
                }
                $i ++;
            }

            $function = $this->fetchfunction($expr);



            if($function instanceof TaintAnalysis){
                // find function, start analysis or just use the data.
                if($function->taintanalysisflag == false){
                    // flag wil be set in the function below
                    $function->starttaintanalysis(); // change property of objects can apply to storing array
                }

                //////////////////////////////////
                // start integrate information
                $affectloops = []; // log ids
                $affectcallsiteswithloops = [];

                for($i = 0; $i < count($taintargs); $i ++){
                    $t = $taintargs[$i];
                    if($t){
                        if($function->paramaffectreturn[$i])
                            $istainted = true;
                        foreach($function->paramaffectloops[$i] as $id){
                            $affectloops[$id] = true;
                        }
                        foreach($function->paramaffectcallsiteswithloops[$i] as $nodeid => $callsiteid){
                            $affectcallsiteswithloops[$nodeid] = $callsiteid;
                        }

                    }
                }

                if($function->taintreturn)
                    $istainted = true;

                foreach($function->taintedloops as $nodeid)
                    $affectloops[$nodeid] = true;
                // then there are several loops that make it tainted. 

                // record this call side
                if(count($affectloops) > 0 || count($affectcallsiteswithloops) > 0){
                    /*
                    $callsite = new CallSite();
                    $callsite->node = $this->current;
                    $callsite->nodeid = $this->current->nodeid;
                    //print("in call site node id is " . $callsite->nodeid . "\n");
                    $callsite->taintargs = $taintargs;
                    $callsite->affectloops = $affectloops;
                    $callsite->affectcallsiteswithloops = $affectcallsiteswithloops;
                    $callsite->expr = $expr; // use this expr can find the function analyser 
                    # add the path to this callsite. and the path inside the callsite. how to get that kind of informations
                    // using TaintAnalysis:fetchfunction
                     */

                    $this->taintedcallsites[] = [$this->current->nodeid, $this->findcallsite($expr, $this->current->nodeid), $taintargs]; 
                }
            }
            else{
                // object->methods
                if(is_string($function)){
                    // built-in functions
                    /*
                    if (strcasecmp($CallFuncName, 'md5') == 0 || strcasecmp($CallFuncName, 'crypt') == 0 || strcasecmp($CallFuncName, 'password_hash') == 0 || 
                        strcasecmp($CallFuncName,'password_verify') == 0 || strcasecmp($CallFuncName, 'bin2hex') == 0 || strcasecmp($CallFuncName, 'chunk_split') == 0 ||
                        strcasecmp($CallFuncName, 'count_chars') == 0 || strcasecmp($CallFuncName, 'implode') == 0 || strcasecmp($CallFuncName, 'ltrim') == 0 ||
                        strcasecmp($CallFuncName, 'metaphone') == 0 || strcasecmp($CallFuncName, 'printf') == 0 || strcasecmp($CallFuncName, 'similar_text') == 0 ||
                        strcasecmp($CallFuncName, 'ucfirst')  == 0|| strcasecmp($CallFuncName, 'ucwords') == 0|| 
                        */
                    
                    if(strcasecmp( $function, 'mysqli_select_db') == 0 || 
                        strcasecmp($function, 'mysqli_query') == 0 || 
                        strcasecmp($function, 'mysqli_result') == 0 || 
                        strcasecmp($function, 'mysqli_fetch_object') == 0 ||
                        strcasecmp($function, 'mysqli_fetch_field') == 0 ||
                        /*strcasecmp($CallFuncName, 'func_get_args') == 0 ||*/
                        strcasecmp($function, 'search') == 0) { 
                        if($istainted) {
                            $this->taintedcallsites[] = [$this->current->nodeid, $this->findcallsite($expr, $this->current->nodeid), $taintargs]; 
                            return true; // todo
                        }
                    }

                }
                else{
                    return $istainted;

                }
            }
        }


        else if($expr instanceof PhpParser\Node\Stmt\Return_ ){ 
 
            if( !in_array($this->current->nodeid, $this->returnnodes)) {
                $this->returnnodes[] = $this->current->nodeid;
            }
            $re = $this->istaintedexpr($expr->expr);
            if($re === true or $re === 1 or $re %2 === 1)
                $this->taintreturn = true;

        }

        // kind of function calls
        else if( $expr  instanceof PhpParser\Node\Expr\New_){
            $istainted = false;
            foreach($expr->args as $arg) {
                $re = $this->istaintedexpr($arg->value);
                if($re === true || $re === 1 || $re %2 === 1){
                    $istainted = true;
                }
            }
            $newobject =  new MyObject();
            $this->objects[$this->objectindex ] = $newobject;
            $this->objectindex += 2;
            return $this->objectindex - 2 + (int)$istainted;
        }

        else if ($expr instanceof PhpParser\Node\Expr\StaticPropertyFetch 
            || $expr instanceof PhpParser\Node\Expr\PropertyFetch) {
            // class name
            if($expr->name instanceof PhpParser\Node\Expr\Variable){
                // cannot infer variable type
                return false;
            }
            elseif($expr->name instanceof PhpParser\Node\Identifier){
                if(is_string($expr->name->name))
                    $property_name = (string)$expr->name->name;
                elseif($expr->name->name instanceof PhpParser\Node\Scalar\String_)
                    $property_name = (string)$expr->name->name->value;
                else{
                    return false;
                }

            }
            elseif($expr->name instanceof PhpParser\Node\Scalar\String_){
                $property_name = (string)$expr->name->value;
            }
            if ($expr instanceof PhpParser\Node\Expr\StaticPropertyFetch) {

                if(is_string($expr->class)){
                    $classname = $expr->class;
                }
                else if ($expr->class instanceof PhpParser\Node\Name) {
                    $classname = implode('', $expr->class->parts); // 
                }
                else{
                    print "in static property fetch "  .get_class($expr->class)."\n";
                    return false;
                }
                if($classname == 'static' || $classname == 'self')
                    $classname = $this->classname;
                // might return false directly as we have nothing about this static property fetch

            }
            else{ // property fetch obj
                // $expr->var
                $var = $expr->var;
                if($var->name instanceof PhpParser\Node\Scalar\String_) {
                    $varname = (string)$var->name->value;
                }
                elseif(is_string($var->name)){
                    $varname = $var->name;
                }
                else{
                    return false;
                }
                if(! isset($this->objectmap[$varname])) {
                    return false;
                }
                $objectindex = $this->objectmap[$varname];
                if(! isset($this->objects[$objectindex]->props[$property_name])) {
                    $this->objects[$objectindex]->props[$property_name] = false;
                }
                return $this->objects[$objectindex]->props[$property_name];
            }
        }
      
        else if ($expr instanceof PhpParser\Node\Expr\Include_) {
            #print("include\n");
            $openfilename = $this->getopenfilename($expr->expr); //mark1 might to do some guess. and matching
            if($openfilename != null) {
                $tmpcurrentfiledir = $this->currentfiledir;
                #print "=================INCLUDE [ ". $openfilename." ]\n";
                $this->currentfiledir = $openfilename;
                #print "From ".$tmpcurrentfiledir." type " . $expr->type. "\n";
                switch($expr->type){
                case 2: // TYPE_INCLUDE_ONCE
                case 4: // REQUIRE_ONCE
                    if(array_key_exists($openfilename, Store::$filevisitflag) and Store::$filevisitflag[$openfilename] == True)
                        break; // if unvisited then break
                case 1: // TYPE_INCLDUE
                case 3: // TYPE_REQUIRE
                    if(array_key_exists($openfilename, Store::$file2classfunc)) {//@todo
                        Store::$filevisitflag[$openfilename] = True;
                        //////////////////////////// #@todo
                        foreach(Store::$file2classfunc[$openfilename]->classes as $classname => $class){
                            foreach($class->classmethods as $methodname => $method) {
                                #echo $classname , "  ", $methodname , "\n";
                                $analyser = Store::$analysisinformation[$classname][$methodname];  # this does not need to check the existence.
                                $analyser->starttaintanalysis(); 
                            }
                        }
                    }
                }
                $this->currentfiledir = $tmpcurrentfiledir;
            }
            else{
                print "open file name unfound\n";
            }
        }
        else if ($expr instanceof PhpParser\Node\Expr\Array_) {
            $istainted = false;
            $items = [];
            foreach($expr->items as $key => $item) {
                $dim = getvalofdim($key);
                $re = $this->istaintedexpr($item->value);
                $items[$dim] = (bool)(int)$re % 2;
                if($re === true or $re === 1 or $re % 2 === 1)
                    $istainted = true;
            }
            $array = new MyArray($items);
            $this->arrays[$this->arrayindex] = $array;
            $this->arrayindex += 2;
            return $this->arrayindex  -2 + (int)$istainted;
        }
        else if ($expr instanceof PhpParser\Node\Expr\Ternary) {
            $r1 = $this->istaintedexpr($expr->cond);
            $r2 = $this->istaintedexpr($expr->if);
            $r3 = $this->istaintedexpr($expr->else);
            return $r1 || $r2 || $r3;
        }
      
        else if ($expr instanceof PhpParser\Node\Expr\Isset_) {
            $istainted = false;
            foreach($expr->vars as $var) {
                $re = $this->istaintedexpr($var);
                if ($re  === true or $re === 1 or $re %2 === 1)
                    $istainted = true;
            }
            return $istainted;
        }
        
        else {
        	if(isset($expr->expr))
        		return $this->istaintedexpr($expr->expr);
        	if(isset($expr->var))
        		return $this->istaintedexpr($var);
        }
        return false;
	}

    /**
     * @return the whole array of param=>affected or not
     *         During this process, whill also update teh 
     *         return value of $this->paramaffectreturn
     */
    public function parampropagation_start($expr){
        $re = [];
        //foreach($this->params as $paramname => $var) {
        //    if(is_string($paramname)){
        for($i = 0; $i < count($this->params); $i ++){
                $this->testparamid = $i;
                $re[$i] = $this->parampropagation($expr);
        }
        return $re;
    }

	public function parampropagation($expr){
		if($expr == null)
			return false;

        if($expr instanceof PhpParser\Node\Stmt\Expression){
            return $this->parampropagation($expr->expr);
        }

        else if($expr instanceof PhpParser\Node\Expr\BinaryOp){
        	$left = $this->parampropagation($expr->left);
            $right = $this->parampropagation($expr->right);
            return $left || $right;
        }
        else if ($expr instanceof PhpParser\Node\Expr\Assign ||
            $expr instanceof PhpParser\Node\Expr\AssignOp ||
            $expr instanceof PhpParser\Node\Expr\AssignRef){

            $right = $this->parampropagation($expr->expr);
            $lhs = $expr->var;
            if ($lhs instanceof PhpParser\Node\Expr\Variable) {
                $lhs_var = $lhs->name;
                if(is_string($lhs_var)) {
                    if($right == true) { 
                        $this->paramaffectvars[$this->testparamid][$lhs_var] = true;
                        
                        #$this->sanitizedvars[$lhs_var] = false;
                    }
                    else if($right === false || $right == 0 || $right %2 === 0){
                        #$this->paramaffectvars[$this->testparamid][$lhs_var] = false;
                        #$this->sanitizedvars[$lhs_var] = true;
                    }
                }
            }

            else if ($lhs instanceof PhpParser\Node\Expr\ArrayDimFetch) {
            
                if($lhs->var instanceof PhpParser\Node\Expr\Variable){
                    $arrayname = $lhs->var->name;
                }
                else{
                    return $right;
                }

                if(is_string($arrayname)) {
                    if($right == true)
                        $this->paramaffectvars[$this->testparamid][$arrayname] = true;
                }
            }
            else if($lhs instanceof PhpParser\Node\Expr\PropertyFetch){

                $var = $lhs->var;
                if($var->name instanceof PhpParser\Node\Scalar\String_) {
                    $varname = (string)$var->name->value;
                }
                elseif(is_string($var->name)){
                    $varname = $var->name;
                }
                else{
                    return $right;
                }
                if(is_string($varname) && $right)
                    $this->paramaffectvars[$this->testparamid][$varname] = true;
            }
            return $right;

        }

        else if ($expr instanceof PhpParser\Node\Expr\ArrayDimFetch) {
            if(! $expr->var instanceof PhpParser\Node\Expr\Variable){
                return false;
            }
            $arrayname = $expr->var->name;

            if(strcasecmp($arrayname,"_GET") == 0 or strcasecmp($arrayname, "_POST") == 0 or strcasecmp($arrayname, "_FILES") == 0 or
                strcasecmp($arrayname, "_SESSION")== 0 or strcasecmp($arrayname, "_REQUEST") == 0 or strcasecmp($arrayname, "_COOKIE")== 0 or 
                strcasecmp($arrayname, "_SERVER") == 0){
                return true;
            }
            if(is_string($arrayname)) {
                if(isset($this->paramaffectvars[$this->testparamid][$arrayname]) && $this->paramaffectvars[$this->testparamid][$arrayname] == true)
                    return true;
            }
            return false;
        }

        else if($expr instanceof PhpParser\Node\Expr\Variable){

            if($expr->name instanceof PhpParser\Node\Scalar\String_){
                $varname = (string)$expr->name->value;
            }
            else if(is_string($expr->name)){
                $varname = $expr->name;
            }
            if(is_string($varname)){
                if(isset($this->paramaffectvars[$this->testparamid][$varname])){
                    if($this->paramaffectvars[$this->testparamid][$varname] == true)
                        return true;
                }
            }
            return false;
        }
        else if($expr instanceof PhpParser\Node\Expr\PostInc || 
                $expr instanceof PhpParser\Node\Expr\PostDec ||
                $expr instanceof PhpParser\Node\Expr\PreDec  ||
                $expr instanceof PhpParser\Node\Expr\PreInc ){
            return $this->parampropagation($expr->var);
        }
        else if($expr instanceof PhpParser\Node\Expr\UnaryMinus ||
                $expr instanceof PhpParser\Node\Expr\UnaryPlus){
            return $this->parampropagation($expr->expr);
        }
        else if($expr instanceof PhpParser\Node\Expr\FuncCall ||  // mark parampropagation funccall
                $expr instanceof PhpParser\Node\Expr\MethodCall||
            	$expr instanceof PhpParser\Node\Expr\StaticCall) { 

            $paramaffectargs = [];
            $i = 0;
            foreach($expr->args as $arg) {
                $re = $this->parampropagation($arg->value);
                $paramaffectargs[$i] = $re;
                $i ++;
            }

            // a callsite should include 
            // expr to get nested analyser,  nodeid to perform se, other informations like affectloops, 
            // affect callsite can be retrive from the tainted arg together with the analyser 
            // markpropagate 
            $function = $this->fetchfunction($expr);
            if($function instanceof TaintAnalysis){
                // find function, start analysis or just use the data.
                if($function->taintanalysisflag == false){
                    // flag wil be set in the function below
                    $function->starttaintanalysis(); // change property of objects can apply to storing array
                }

                // start integrate information
                // write a callsite
                // how to write a callsite in such format.
                //
                // if not newed. because there function can be invoked several times for different parameters
                $callsiteid = $this->findcallsite($expr, $this->current->nodeid);
                $callsite = $this->callsites[$this->current->nodeid][$callsiteid];
                $callsite->paramaffectargs[$this->testparamid] = $paramaffectargs;

                $affectloops = []; // log ids
                for($i = 0; $i < count($paramaffectargs); $i ++){
                    $t = $paramaffectargs[$i];
                    if($t){
                        $this->paramaffectcallsites[$this->testparamid][$this->current->nodeid] = $callsiteid;
                        if(count($function->paramaffectloops[$i]) > 0 || count($function->paramaffectcallsiteswithloops[$i]) > 0) {
                            #if(array_key_exists($this->current->nodeid, $this->paramaffectcallsiteswithloops[$this->testparamid])){
                            $this->paramaffectcallsiteswithloops[$this->testparamid][$this->current->nodeid] = $callsiteid;
                            // @todo current only log nodeid, but without arg-loop-callsite-info.
                            #}
                        }
                    }
                }
            

                for($i = 0; $i < count($paramaffectargs); $i ++ ){
                    $t = $paramaffectargs[$i];
                    if($t) {
                        if($function->paramaffectreturn[$i])
                            return true;
                    }
                }
                return false;

            }
            else{
                for($i = 0; $i < count($paramaffectargs); $i ++ ){
                    $t = $paramaffectargs[$i];
                    if($t) {
                            return true;
                    }
                }
            }
            return false;
        }


        else if($expr instanceof PhpParser\Node\Stmt\Return_ ){ // mark2
            $re = $this->parampropagation($expr->expr);
            if($re) {
                $this->paramaffectreturn[$this->testparamid] = true;
            }
            return $re;
        }

        // kind of function calls
        else if( $expr  instanceof PhpParser\Node\Expr\New_){
            foreach($expr->args as $arg) {
                $re = $this->parampropagation($arg->value);
                if($re){
                    return true;
                }
            }
            return false; // generally return false;
        }

        else if ($expr instanceof PhpParser\Node\Expr\StaticPropertyFetch 
            || $expr instanceof PhpParser\Node\Expr\PropertyFetch) {

            if ($expr instanceof PhpParser\Node\Expr\StaticPropertyFetch) {
                return false;

            }
            else{ // property fetch obj
                // $expr->var
                $var = $expr->var;
                if($var instanceof PhpParser\Node\Expr\Variable && 
                    $var->name instanceof PhpParser\Node\Scalar\String_) {
                    $varname = (string)$var->name->value;
                }
                elseif(is_string($var->name)){
                    $varname = $var->name;
                }
                else{
                    return false;
                }
                if(is_string($varname) && isset($this->paramaffectvars[$this->testparamid][$varname]) 
                    && $this->paramaffectvars[$this->testparamid][$varname] == true) {
                    return true;
                }
            }
        }
      
        else if ($expr instanceof PhpParser\Node\Expr\Array_) {
            $isaffected = false;
            foreach($expr->items as $key => $item) {
                $re = $this->parampropagation($item->value);
                if($re)
                    $isaffected = true;
            }
            return $isaffected;
        }
        else if ($expr instanceof PhpParser\Node\Expr\Ternary) {
            $r1 = $this->parampropagation($expr->cond);
            $r2 = $this->parampropagation($expr->if);
            $r3 = $this->parampropagation($expr->else);
            return $r1 || $r2 || $r3;
        }
      
        else if ($expr instanceof PhpParser\Node\Expr\Isset_) {
            $isaffected = false;
            foreach($expr->vars as $var) {
                $re = $this->parampropagation($var);
                if ($re)
                    $isaffected = true;
            }
            return $isaffected;
        }
        
        else {
        	if(isset($expr->expr))
        		return $this->parampropagation($expr->expr);
        	if(isset($expr->var))
        		return $this->isset($var);
        }
        return false;
	}
    public function findcallsite($expr, $nodeid){
        if(!isset($this->callsites[$nodeid])) {
            $this->callsites[$nodeid] = [];
        }
        foreach($this->callsites[$nodeid] as $callsiteid => $callsite) {
            if(PrintExpr($callsite->expr) == PrintExpr($expr)) {
                return $callsiteid;
            }
        }
        $callsite = new CallSite();
        $callsite->expr = $expr;
        $callsite->nodeid = $nodeid;
        $this->callsites[$nodeid][$this->callsiteindex ++] = $callsite;
        return $this->callsiteindex - 1;

    }
    public function findfunction($funcname, $classname = ''){
        //global $analysisinformation; 
        //global $functionmap;
        if($classname != ''){
            if(isset(Store::$analysisinformation[$classname][$funcname])){
                return Store::$analysisinformation[$classname][$funcname]; 
                // return function's analyser back
            }
            elseif($classname == MAIN_CLASS){
                return $funcname; // builtin functions we assume
                // if there is no matching analyser
                // and also in main_class 
                // just return its name
            }
            else{
                $log = "In findfunction: " . $classname . "::" . $funcname . " Not found\n";
                $this->logs .= $log;
                //print($log);
                return NULL;
            }
        }
        else{ 
            if(!isset(Store::$functionmap[$funcname]) || is_int(Store::$functionmap[$funcname])){
                return NULL;
            }
            $classname = Store::$functionmap[$funcname];
            return $this->findfunction($funcname, $classname);
        }

    }


    public function fetchfunction($expr){
        // funccall, staticcall/ methodcall/
        if($expr instanceof PhpParser\Node\Expr\StaticCall) {
            // $class, $name, $args
            if(is_string($expr->class)) {
                $classname = $expr->class;
            }
            elseif($expr->class instanceof PhpParser\Node\Name) {
                $classname = implode('', $expr->class->parts);
            }
            else{ // unfound classname
                return NULL;
            }
            if($classname == 'self' || $classname == 'this'){
                $classname = $this->classname;
            }

            if($expr->name instanceof PhpParser\Node\Identifier){
                $funcname = $expr->name->name;
            }
            elseif(is_string($expr->name)) {
                $funcname = $expr->name;
            }
            else{ // unfound classname
                return NULL;
            }
        }

        elseif($expr instanceof PhpParser\Node\Expr\FuncCall){
            if($expr->name instanceof PhpParser\Node\Name){
                $funcname = implode('', $expr->name->parts);
            }
            elseif($expr->name instanceof PhpParser\Node\Identifier){
                $funcname = $expr->name->name;
            }
            elseif(is_string($expr->name)){
                $funcname = $expr->name;
            }
            else{
                return NULL;
            }
            $classname = MAIN_CLASS;

        }
        else{ // methodcall
            if($expr->name instanceof PhpParser\Node\Identifier){
                $funcname = $expr->name->name;
            }
            elseif(is_string($expr->name)) {
                $funcname = $expr->name;
            }
            else{ // unfound classname
                return NULL;
            }
            $classname = '';
        
            if($expr->var instanceof PhpParser\Node\Expr\Variable)
                $calssname = $expr->var->name;
            if($classname == 'self' || $classname == 'this'){
                $classname = $this->calssname;
            }
        }
        return $this->findfunction($funcname, $classname);
            
        // temporarily forget namespace problem
        // find the function is has to have.
    }

    public function p($constraints){
        $t = "---- PrintConstraints   \n";
        foreach($constraints as $cst){
            foreach($cst as $c){
                $t .= PrintExpr($c) ."\t";
            }
            $t .= "\n";
        }
        print($t);
    }

    /**
     * perform something similar to backwards_rec_dataflow
     * return c-v pairs
     */
    public function backwardsse_rec_dataflow($start, $end, $cvpairs) { // cvpairs is an array of c-v
        $current = $end;
        if(count($cvpairs) > 10)
            $cvpairs = array_slice($cvpairs, 0, 20); // @todo
        while($current && $current != $start){
            $nextcvpairs = [];
            if($current->type == IfStmt){
                $len = count($current->conds);
                for($i = 0; $i < $len; $i ++) {    
                    $tlist = $this->backwardsse_rec_dataflow($current->bodystarts[$i], $current->bodyends[$i], $cvpairs); 
                    // @todo what if there is something changed in data flow.
                    foreach($tlist as $t){
                        $t[0][] = $this->copyexpr($current->conds[$i]->cond);
                        
                        $nextcvpairs[] = $t;
                    }
                }
                $cvpairs = $nextcvpairs;
            } 
            elseif ($current->type == LoopStmt) {

                $cvpairs = $this->backwardsse_rec_dataflow($current->bodystart, $current->bodyend, $cvpairs);
                // the cond???
                /*
                if ($current->looptype == ForLoop){
                    foreach($current->init as $ini)
                        $constraints = $this->BSEonExpr($ini, $constraints);
                }
                */
            
            }
            elseif($current->type == Stmt){
                //  print('comes into stmt'."\n");
                $cvpairs = $this->backwardsexpr_dataflow($current->node, $cvpairs); 
//              print("IN stmt cvpairs "));

            }elseif($current->type == Cond){
                foreach($cvpairs as $cv){
                    $cv[0][] = $this->copyexpr($current->cond);
                    $nextcvpairs[] = $cv;
                }
                $current = $current->parent; // skip its parent
                $cvpairs = $nextcvpairs;
            }
            elseif($current->type == Start){

            }
            elseif($current->type == End){

            }
            $current = $current->parent;
        }
        //print("get type" . gettype($cvpairs[0][1]) . "\n");
        return $cvpairs;
    }

    // perform forwardsse
    public function forwardsse_rec($start, $end, $constraints){
        // several constraints only
        // should based on basic blocks
        
        $current = $start; // from start to end
        while($current && $current != $start){
            //  print($current->type. " " .$current->nodeid." \n");
            $multicstlist = [];
            $this->current = $current;
            if($current->type == IfStmt){
                $len = count($current->conds);
                for($i = 0; $i < $len; $i ++) {    
                    $this->current = $current;
                    $tlist = $this->forwardsse_rec($current->bodystarts[$i], $current->bodyends[$i], $constraints);

                    foreach($tlist as $t){
                        $t[] = $this->copyexpr($current->conds[$i]->cond);
                        $multicstlist[] = $t; // add a path
                    }
                }
                $constraints = $multicstlist; // change name back
            }
            elseif ($current->type == LoopStmt) {
                    $tlist = $this->forwardsse_rec($current->bodystart, $current->bodyend, $constraints);
                    foreach($tlist as $t){
                        $t[] = $this->copyexpr($current->cond);
                        $multicstlist[] = $t;
                    }

                /*
                if ($current->looptype == ForLoop){
                    foreach($current->init as $ini)
                        $constraints = $this->BSEonExpr($ini, $constraints);
                }
                */
                $constraints = $multicstlist;
            }
            elseif($current->type == Stmt){
//              print('comes into stmt ' ."\n");
                $constraints = $this->forwardsexpr($current->node, $constraints);

            }elseif($current->type == Cond){
                //print("come into cond\n");
                for($i = 0; $i < count($constraints); $i ++){
                    $constraints[$i][] = $this->copyexpr($current->cond);
                }
                $current = $current->parent;
                if($current->type == LoopStmt){
                    /*
                    if($current->looptype == ForLoop)
                        foreach($current->init as $ini)
                        $constraints = $this->BSEonExpr($ini, $constraints);
                     */
                }
                elseif($current->type == IfStmt){
                    
                    //print("comes into cond->ifstmt\n");
                }
                else{
                    echo "ERROR: first cond then else what/ not if/loop\n";
                }
            }
            elseif($current->type == Start){
            }
            elseif($current->type == End){

            }
            $current = $current->parent;
        }
        //print("return constraints\n");
        if ($constraints){
            return $constraints;
        }
        else
            [[Store::$true_node]];
    }


    public function backwardsexpr_dataflow($expr, $cvpairs) {
        $nextcvpairs = [];

        $pair = getassignment($expr);
        $lhs = $pair[0];
        $rhs = $pair[1];
        // if you change the rhs node inside
        $rhs = $this->getcvpair($this->copyexpr($rhs)); //[c,v]

        foreach($rhs as $r) {
            foreach($cvpairs as $cv) {

                //$c = $this->backwardsexpr($expr, $cv[0]); // this might cause error in line 1348
                $nc = [];
                foreach($cv[0] as $c) {
                    $nc[] = $this->replaceconstraint($c, $lhs, $r[1]);
                }
                $v = $this->backwardsexpr_value($expr, $cv[1]);
                $nextcvpairs[] = [$nc, $v];
            }
        }
        return $nextcvpairs;
    }

    
    public function backwardsexpr_value($expr, $value){
        $multicstlist = [];
        $pair = getassignment($expr);
        $lhs = $pair[0];
        $rhs = $pair[1];
        return $this->replaceconstraint($value, $lhs, $rhs);
    }

    // perform backwardsse
    public function backwardsse_rec($start, $end, $constraints){
        $current = $end;
        //////////////////////
        // pruning now
        if(count($constraints) > 10)
            $constraints = array_slice($constraints, 0, 20); // @todo
        //////////////////////
        //////////////////////
        //$this->p($constraints);

        while($current && $current != $start){
        //  print($current->type. " " .$current->nodeid." \n");
            $multicstlist = [];
            $this->current = $current;
            if($current->type == IfStmt){
                $len = count($current->conds);
                for($i = 0; $i < $len; $i ++) {    
                    $this->current = $current;
                    $tlist = $this->backwardsse_rec($current->bodystarts[$i], $current->bodyends[$i], $constraints);

                    foreach($tlist as $t){
                        $t[] = $this->copyexpr($current->conds[$i]->cond);
                        $multicstlist[] = $t; // add a path
                    }
                }
                $constraints = $multicstlist; // change name back
            } 
            elseif ($current->type == LoopStmt) {
                    $tlist = $this->backwardsse_rec($current->bodystart, $current->bodyend, $constraints);
                    foreach($tlist as $t){
                        $t[] = $this->copyexpr($current->cond);
                        $multicstlist[] = $t;
                    }

                /*
                if ($current->looptype == ForLoop){
                    foreach($current->init as $ini)
                        $constraints = $this->BSEonExpr($ini, $constraints);
                }
                */
                $constraints = $multicstlist;
            }
            elseif($current->type == Stmt){
//              print('comes into stmt ' ."\n");
                $constraints = $this->backwardsexpr($current->node, $constraints);

            }elseif($current->type == Cond){
                //print("come into cond\n");
                for($i = 0; $i < count($constraints); $i ++){
                    $constraints[$i][] = $this->copyexpr($current->cond);
                }
                $current = $current->parent;
                if($current->type == LoopStmt){
                    /*
                    if($current->looptype == ForLoop)
                        foreach($current->init as $ini)
                        $constraints = $this->BSEonExpr($ini, $constraints);
                     */
                }
                elseif($current->type == IfStmt){
                    
                    //print("comes into cond->ifstmt\n");
                }
                else{
                    echo "ERROR: first cond then else what/ not if/loop\n";
                }
            }
            elseif($current->type == Start){
            }
            elseif($current->type == End){

            }
            $current = $current->parent;
        }
        //print("return constraints\n");
        if ($constraints){
            return $constraints;
        }
        else
            [[Store::$true_node]];
    }

    // see when will overwrite 
    public function backwardsexpr($expr, $constraints){
        $multicstlist = [];
        $pair = getassignment($expr);
        $lhs = $pair[0];
        $rhs = $pair[1];
        // if you change the rhs node inside
        $rhs = $this->getcvpair($this->copyexpr($rhs)); //[c,v]
        // the rhs applied with getcvpair should be an array of cv pairs
        // the c should be integrate with v.
        foreach($rhs as $r){
            foreach($constraints as $cst) {
                $tcst = [];
                foreach($cst as $c) {
                    $tcst[] = $this->replaceconstraint($c, $lhs, $r[1]);
                }
                $multicstlist[] = $tcst;
            }
        }
        return $multicstlist;
    }

    public static function getreturnvaluefromnode($expr) {

        if($expr instanceof PhpParser\Node\Stmt\Return_){
            return $expr->expr;
        }
        elseif($expr instanceof PhpParser\Node\Stmt\Expression){
            return getreturnfromnode($expr->expr);
        }

    
    }


    public function getreturns($function){
        // if the function is not symbolically executed then do it 
        // else directly get the return c,v pairs
        $cvpairs = [];
        if($function->symbolicexecutionflag == false) {
            $function->symbolicexecutionflag = true; 
            foreach($function->returnnodes as $id){
                $returnnode = Store::$idmaptonode[$id];
                // apply backwards se to get the return value and its
                $returnvalue = $this->getreturnvaluefromnode($returnnode->stmt);
                $cvs= $function->backwardsse_rec_dataflow($function->start, $returnnode,  [[[Store::$true_node], $returnvalue]]); 
                foreach($cvs as $cv)
                    $cvpairs[] = $cv;
                // currently only control flow
                // how to do in data flow
            }
            $function->returncvpairs = $cvpairs;
        }
        return $function->returncvpairs;
    }

    public function replaceparams_c($csts, $params, $args){
        $rcsts = [];
        foreach($csts as $c){
            $i = 0;
            foreach($params as $paramname => $value){
                if(isset($args[$i]))
                    $rcsts[] = $this->replaceconstraint($this->copyexpr($c), $value, $args[$i]->value);
                $i ++;
            }
        }
        return $rcsts;
    }

    public function replaceparams($expr, $params, $args) {
        // replace params with args?? the same things???
        //for($i = 0; $i < count($args); $i ++) {
        $i = 0;
        foreach($params as $paramname => $value){
            if(isset($args[$i]))
                $expr = $this->replaceconstraint($this->copyexpr($expr), $value, 
                $args[$i]->value);
            $i ++;
        }
        return $expr;
    }

    // get pair of constraints and value pair or rhs when BSE below
    // before coming in this function should first do a copyexpr @warning
    public function getcvpair ($expr) {
        // the expr passed here should be a value-like expr instead of verb-like var
        // **continious assignments????
        // before entering this function, should break down the expression, and rid of assignments
        // return value format [[c, v], [c1, v1], ... , []]

        if($expr == null)
            return [[[Store::$true_node], null]];
        if($expr instanceof PhpParser\Node\Stmt\Expression){
            return $this->getcvpair($expr->expr);
        }
        # else if($expr instanceof PhpParser\Node\Expr\BinaryOp\BitwiseAnd){
        # Integrate all binary ops here.
        else if($expr instanceof PhpParser\Node\Expr\BinaryOp){

            $left = $this->getcvpair($expr->left);
            $right = $this->getcvpair($expr->right);

            $class = \get_class($expr);
            $re = [];
            foreach($left as $l){
                foreach($right as $r){
                    $v = new $class($l[1], 
                        $r[1]); # get value
                    # @todo warnings the expressions here are reused
                    $c = array_merge($l[0], $r[0]);
                    $re[] = [$c, $v];
                }
            }
            return $re;
        }
        else if($expr instanceof PhpParser\Node\Expr\FuncCall||  //@todo markgetcvpair funccall
                $expr instanceof PhpParser\Node\Expr\MethodCall) { 
            // jump to the return expr
            $function = $this->fetchfunction($expr);
            if($function instanceof TaintAnalysis){
                // jump to return expression of it and get the return value
                $cvpairs = $this->getreturns($function); 
                // retrieve the summary of specific function
                // both constraints and returns have to replace params with args
                $re = [];
                foreach($cvpairs as $cv) {
                    //@bug number of args and params are sometimes not the same
                    //and the default value of params are not set sometimes.
                    $c = $this->replaceparams_c($cv[0], $function->params, $expr->args);
                    $v = $this->replaceparams($cv[1], $function->params, $expr->args);
                    $re[] = [$c, $v];
                }
                return $re;
            }
        }

        else if ($expr instanceof PhpParser\Node\Expr\Ternary) {
            $recond = $this->getcvpair($expr->cond);
            $reif = $this->getcvpair($expr->if);
            $reelse = $this->getcvpair($expr->else);
            $cvpairs = [];
            $class = \get_class($expr);
            foreach($recond as $re) {
                foreach($reif as $if) {
                    foreach($reelse as $else) {
                        $newexpr = new $class($re[1], $if[1], $else[1]);
                        $c = array_merge($re[0], $if[0], $else[0]);
                        $cvpairs[] = [$c, $newexpr];
                    }
                }
            }
            return $cvpairs;
        }
        else{
            if(isset($expr->expr)) {
                $cvpairs = $this->getcvpair($expr->expr);
                $nextcvpairs = [];
                foreach($cvpairs as $cv) {
                    $v = $this->copyexpr($expr);
                    $v->expr = $cv[1];
                    $nextcvpairs[] = [$cv[0], $v];
                }
                return $nextcvpairs;
            }
        }
        return [[[Store::$true_node], $expr]];
    }
   

    /*  
     * Replace lhs with rhs for expr
     * @todo there is bug maybe
     */
    public function replaceconstraint($expr, $lhs, $rhs){ 
        if($expr == null)
            return null;
        if($expr instanceof PhpParser\Node\Stmt\Expression){
            return $this->replaceconstraint($expr->expr, $lhs, $rhs);
        }
        else if($expr instanceof PhpParser\Node\Expr\BinaryOp){
            $expr->left = $this->replaceconstraint($expr->left, $lhs, $rhs);
            $expr->right = $this->replaceconstraint($expr->right, $lhs, $rhs);
            return $expr;
        }
        else if($expr instanceof PhpParser\Node\Expr\BooleanNot){
            $expr->expr = $this->replaceconstraint($expr->expr, $lhs, $rhs);
            return $expr;
        }
        else if($expr instanceof PhpParser\Node\Expr\Variable){
            if(PrintExpr($lhs) == PrintExpr($expr)){
            #if(CmpExpr($expr, $lhs)){ // why printexpr works and cmpexpr not
                return $this->copyexpr($rhs);
            }
            //return new PhpParser\Node\Expr\Variable($this->replaceconstraint($expr->name, $lhs, $rhs));
            return $expr;
        }
        else if(
            $expr instanceof PhpParser\Node\Expr\PostInc || 
            $expr instanceof PhpParser\Node\Expr\PostDec || 
            $expr instanceof PhpParser\Node\Expr\PreDec ||
            $expr instanceof PhpParser\Node\Expr\PreInc){

            $expr->var = $this->replaceconstraint($expr->var, $lhs, $rhs);
            return $expr;
        }
        else if($expr instanceof PhpParser\Node\Expr\UnaryMinus || $expr instanceof PhpParser\Node\Expr\UnaryPlus){
            $expr->expr = $this->replaceconstraint($expr->expr, $lhs, $rhs);
            return $expr;
        }
        else if($expr instanceof PhpParser\Node\Scalar\DNumber ||
                $expr instanceof PhpParser\Node\Scalar\LNumber ||
                $expr instanceof PhpParser\Node\Scalar\String_){
            // nop stmts
        }
        else if(
            $expr instanceof PhpParser\Node\Expr\FuncCall ||
            $expr instanceof PhpParser\Node\Expr\MethodCall ||
            $expr instanceof PhpParser\Node\Expr\StaticCall 
        ){ // mark2
            // if we want to replace the expr of function
            // 1. get its return value
            // 2. try to use its return value
            $function = $this->fetchfunction($expr); // get the analyser from it.
            $targs = [];
            foreach($expr->args as $arg){
                $targs[] = new PhpParser\Node\Arg($this->replaceconstraint($arg->value, $lhs, $rhs));
            }
            return new PhpParser\Node\Expr\FuncCall($expr->name, $targs);
        }
        elseif($expr instanceof PhpParser\Node\Expr\MethodCall) {
            $targs = [];
            foreach($expr->args as $arg){
                $targs[] = new PhpParser\Node\Arg($this->replaceconstraint($arg->value, $lhs, $rhs));
            }
            return new PhpParser\Node\Expr\MethodCall($expr->var, $expr->name, $targs);
        }
        else if($expr instanceof PhpParser\Node\Expr\StaticCall) {
            $targs = [];
            foreach($expr->args as $arg){
                $targs[] = new PhpParser\Node\Arg($this->replaceconstraint($arg->value, $lhs, $rhs));
            }
            return new PhpParser\Node\Expr\StaticCall($expr->class, $expr->name, $targs);
        }
        else if( $expr instanceof PhpParser\Node\Expr\ConstFetch) {
        }
        else if( $expr  instanceof PhpParser\Node\Expr\New_){
            print "WARNING: this->replaceconstraint  *New_*\n";
        }
        else if($expr instanceof PhpParser\Node\Expr\PropertyFetch) {
            //print "replaceconstraint property fetch\n";
            foreach($lhs as $l)
                if(CmpExpr($expr, $l)) {
                    return $this->copyexpr($rhs);
                }
            return new PhpParser\Node\Expr\PropertyFetch($this->replaceconstraint($expr->var, $lhs, $rhs), $this->replaceconstraint($expr->name, $lhs, $rhs));
        }
        else if($expr instanceof PhpParser\Node\Expr\ArrayDimFetch){
            foreach($lhs as $l)
                if(CmpExpr($expr, $l))
                    return  $this->copyexpr($rhs);
            return $expr;
            //return new PhpParser\Node\Expr\ArrayDimFetch($this->replaceconstraint($expr->var, $lhs, $rhs), $this->replaceconstraint($expr->dim, $lhs, $rhs));
        }
        else if ($expr instanceof PhpParser\Node\Expr\Ternary) {
            $expr->cond = $this->replaceconstraint($expr->cond, $lhs, $rhs);
            $expr->if = $this->replaceconstraint($expr->if, $lhs, $rhs);
            $expr->else = $this->replaceconstraint($expr->else, $lhs, $rhs);
            return $expr;
        }
        else if($expr instanceof PhpParser\Node\Expr\BitwiseNot) {
           $expr->expr = $this->replaceconstraint($expr->expr, $lhs, $rhs);
            return $expr;
        }
        else if ($expr instanceof PhpParser\Node\Expr\ClassConstFetch) {
            if(is_string($expr->class)){
                $classname0 = $expr->class;
            }
            else if ($expr->class instanceof PhpParser\Node\Name) {
                $classname0 = implode('', $expr->class->parts); // 
            }
            else{
                print "in classconst fetch "  .get_class($expr->class)."\n";
            }

            if($classname0 == 'static' || $classname0 == 'self'){
                $classname0 = $this->classname;
            }
            $constname = (string)$expr->name->name;
            if(isset($this->classes[$classname0]->consts[$constname])) {
                return $this->classes[$classname0]->consts[$constname];
            }
            return $expr;
        }
        else if ($expr instanceof PhpParser\Node\Expr\Empty_) {
            // Empty_ means  the expr is empty or not
            // return true or false
            $expr->expr = $this->replaceconstraint($expr->expr, $lhs, $rhs);
            return $expr;
        }
        else if ($expr instanceof PhpParser\Node\Expr\Instanceof_) {
            $expr->expr = $this->replaceconstraint($expr->expr, $lhs, $rhs);
            return $expr;
        }
        else if($expr instanceof PhpParser\Node\Expr\StaticPropertyFetch){
            if($expr->name instanceof PhpParser\Node\Expr\Variable){
                $re = $this->getValofVar($expr->name);
                $prop_name = $re[0];
                if($re[1])
                    $istainted = true;
            }elseif($expr->name instanceof PhpParser\Node\Identifier){
                if(is_string($expr->name->name))
                    $prop_name = (string)$expr->name->name;
                elseif($expr->name->name instanceof PhpParser\Node\Scalar\String_)
                    $prop_name = (string)$expr->name->name->value;
            }elseif($expr->name instanceof PhpParser\Node\Scalar\String_){
                $prop_name = (string)$expr->value;
            }
            if(is_string($expr->class)){
                $classname0 = $expr->class;
            }
            else if ($expr->class instanceof PhpParser\Node\Name) {
                $classname0 = implode('', $expr->class->parts); // 
            }

            else{
                print "in static property fetch "  .get_class($expr->class)."\n";
            }

            if($classname0 == 'static' || $classname0 == 'self'){
                $classname0 = $this->classname;
            }
            if(isset($this->classes[$classname0]->props[$prop_name])) {
                return $this->classes[$classname0]->props[$prop_name];
            }
        }
        return $expr;
    }

    public function copyexpr($expr){ // each time call copyexpr will use memory and get a new objects.
        // please also consider the memory usage as well.
        $copy = DeepCopy\deep_copy($expr); // use the deepcopy function from other project
        return $copy;
    }

	// this is used to get the name of a file
	// with absolute path
    // put it into future work
	public function getopenfilename($expr){
	   // print "in function getopenfilename ".$ProgramInfo->currentfiledir ."\n";
        $filename = "";
	    if($expr instanceof PhpParser\Node\Scalar\MagicConst\File) {
	        return $this->currentfiledir;
	    }
	    else if($expr instanceof PhpParser\Node\Expr\BinaryOp\Concat){
	        $left = $expr->left;
	        $leftpath = "";
	        $rightpath = "";
	        if($left instanceof PhpParser\Node\Expr\FuncCall) {
	            // if it is dirname
	            // do something here
	            $funcname = implode('', $left->name->parts);
	            if($funcname = "dirname") {
	                if($left->args[0]->value instanceof PhpParser\Node\Scalar\String_) {
	                    $leftpath = dirname((string)$left->args[0]->value->value);
	                }
	                else if ($left->args[0]->value instanceof PhpParser\Node\Scalar\MagicConst\File) {
	                    $leftpath = dirname($this->currentfiledir);
	                }
	                else if($left->args[0]->value instanceof PhpParser\Node\Scalar\MagicConst\DIR)  {
	                    $pos = strrpos($this->currentfiledir, "/");
	                    $leftpath = dirname(substr($this->currentfiledir, 0, $pos));
	                }
	                else print "unhandled left \n";
	            }
	        }
	        else if($left instanceof PhpParser\Node\Scalar\MagicConst\DIR) {
	            $leftpath = dirname($this->currentfiledir);
	        }
	        else if($left instanceof PhpParse\Node\Scalar\String_){
	            $leftpath = (string)$left->value;
            }
            else if($left instanceof PhpParser\Node\Expr\ConstFetch){
                $name = implode('', $left->name->parts); // 
                print $name."<-  constant name \n";
                if(isset($this->classes['MAIN_CLASS']->consts[$name])){ //  bug here. this->   
                    $leftpath = $this->classes['MAIN_CLASS']->consts[$name];
                    #print "leftpath concat constfetch ". get_class($leftpath)."\n";
                    print PrintExpr($leftpath);
                    if ($leftpath instanceof PhpParser\Node\Scalar\String_)
                        $leftpath = $leftpath->value;
                }
                else{
                    print"not set\n";
                }
            }

	        #print "left path  ".$leftpath ."\n";
	        
	        $right = $expr->right;
	        //print get_class($right);
	        if($right instanceof PhpParser\Node\Expr\FuncCall) {
	            $funcname = implode('', $right->name->parts);
	            if($funcname = "dirname") {
	                if($right->args[0]->value instanceof PhpParser\Node\Scalar\String_) {
	                    $rightpath = dirname((string)$right->args[0]->value->value);
	                }
	                else if ($right->args[0]->value instanceof PhpParser\Node\Scalar\MagicConst\File) {
	                    $rightpath = dirname($this->currentfiledir);
	                
	                }
	                else if($right->args[0]->value instanceof PhpParser\Node\Scalar\MagicConst\DIR)  {
	                    $pos = strrpos($this->currentfiledir, "/");
	                    $rightpath = dirname(substr($PrograInfo->currentfiledir, 0, $pos));
	                }
	                else print "unhandled right \n";
	            }
	        }

	        else if($right instanceof PhpParser\Node\Scalar\String_)
	            $rightpath = (string)$right->value;
	        //print "right path  ".$rightpath."\n";
	        $filename = $leftpath .$rightpath;
	    }
	    else if($expr instanceof PhpParser\Node\Scalar\String_)
	        $filename = (string)$expr->value;

	    //print "initial file name ".$filename ."\n";
	    $openfilename = null;
	    $filepath = file_absolute_path($filename, "");
	    if($filepath != "" && is_file($filepath)){
	        //print "absolute path alredy \n";
	        $openfilename = $filepath;
	    }
	    else {
	        $filepath = file_absolute_path($filename, $this->rundir);
	        if($filepath != "" && is_file($filepath)) {
	            print "find in run dir\n";
	            $openfilename = $filepath;
	        }
	        else {
	            $pos = strrpos($this->currentfiledir, "/");
	            if ($pos == 0)
	                $dir = "";
	            else $dir = substr($this->currentfiledir, $pos);
	            $filepath = file_absolute_path($filename, $dir);
	            //print is_file($filepath);
	            if($filepath != "" && is_file($filepath)) {
	                print "find in currentdir\n";
	                $openfilename = $filepath;
	            }
	        }
	    }
	    return $openfilename;
    }
} // ==== endofclass


function getvalofdim($key){
    if($key instanceof PhpParser\Node\Scalar\DNumber ||
       $key instanceof PhpParser\Node\Scalar\LNumber){
        return (int)$key->value;
    }

    else if($key instanceof PhpParser\Node\Scalar\String_){
        if(is_numeric($key->value) && strpos($key->value, ".") == false && $key->value[0] != "0") 
            return (int) $key->value;
        else
            return $key->value;
    }
    return NULL;
}
?>
