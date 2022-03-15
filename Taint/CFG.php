<?php
include_once __DIR__ ."/../includes.php";
//$true_node =  new PhpParser\Node\Expr\ConstFetch(new PhpParser\Node\Name('True'));
class CFG{

	/**
	 * Created temperally used
	 */
	public static function constructcfg($stmts){
        //print("comes into constructcfg\n");
        global $nodeindex;
        //global $idmaptonode;

	    $start = new CFGTreeNode($nodeindex ++);
        Store::$idmaptonode[$nodeindex - 1] = $start; // add id map => node
	    $start->parent = null;  # if parent is null, then it reaches the beginings
	    $parent = $start;
	    $parent->type = Start;

        /*
        if(!is_array($stmts))
            print(get_class($stmts) . "\n");
        if(is_null($stmts))
            print("yes it is null\n");

        print("before come to stmts\n");
         */
        if(!is_null($stmts)) {
            foreach ($stmts as $stmt) {
                #print get_class($stmt)."\n";
                if ($stmt instanceof PhpParser\Node\Stmt\If_) {
                    #inconsistent
                    $current = new CFGTreeIfNode($nodeindex ++);
                    Store::$idmaptonode[$nodeindex - 1] = $current; // add id map => node
                    $if= CFG::processStmtIf($stmt);//
                    $current->conds = $if[0];
                    foreach($current->conds as $cond){
                        $cond->parent = $current;
                    }
                    // should define the types of body starts and body ends
                    $current->bodystarts = $if[1];
                    $current->bodyends = $if[2];
                }
                else if ($stmt instanceof PhpParser\Node\Stmt\Foreach_ || 
                    $stmt instanceof PhpParser\Node\Stmt\For_ || 
                    $stmt instanceof PhpParser\Node\Stmt\While_ || 
                    $stmt instanceof PhpParser\Node\Stmt\Do_) {
                    //print "here comes into loop\n";
                    $current = new CFGTreeLoopNode($nodeindex ++);
                    Store::$idmaptonode[$nodeindex - 1] = $current; 
                    // add id map => node
                    // $current->type = LoopStmt;
                    $loop = CFG::processStmtLoop($stmt);
                    $current->looptype = $loop[0];
                    $current->bodystart = $loop[1];
                    $current->bodyend = $loop[2];
                    $current->cond = $loop[3];
                    $current->init = $loop[4];
                    $current->loop = $loop[5];
                    $current->bodystart->parent = $current;
                    //print($current->bodystart->parent->type);
                } 
                else if($stmt instanceof PhpParser\Node\Stmt\Switch_){          
                    $current = new CFGTreeIfNode($nodeindex ++ );
                    Store::$idmaptonode[$nodeindex - 1] = $current; 
                    // add id map => node
                    $switch = CFG::processStmtSwitch($stmt);
                    $current->conds = $switch[0];
                    $current->bodystarts = $switch[1];
                    $current->bodyends = $switch[2];
                    foreach($current->conds as $cond) {
                        $cond->parent = $current;
                    }
                }
                else if($stmt instanceof PhpParser\Node\Stmt\TryCatch) {
                    // print "here in trycatcch\n";
                    $trycfg = CFG::constructcfg($stmt->stmts);
                    $current = $trycfg[0];
                    $parent->child = $current;
                    $current->parent = $parent;
                    $parent = $trycfg[1]->parent;
                }
                /*
                else if ($stmt instanceof PhpParser\Node\Stmt\Namespace_){
                    print("name space\n");
                    $ns = CFG::constructcfg($stmt->stmts);
                    $current = $ns[0];
                    $parent->child = $current;
                    $current->parent = $parent;
                    $parent = $ns[1]->parent;

                }
                 */
                elseif(($stmt instanceof PhpParser\Node\Stmt\Nop) || ($stmt instanceof PhpParser\Node\Stmt\Function_) || ($stmt instanceof PhpParser\Node\Expr\Stmt\Class_)) {
                    //print("constructcfg CLASS/FUNCTION\n");
                }
                else {                    
                    $current = new CFGTreeNode($nodeindex ++);
                    Store::$idmaptonode[$nodeindex - 1] = $current; 
                    // add id map => node
                    $current->type = Stmt;
                    $current->node = $stmt;     
                }
                /**
                 * except the situations when nop/functions/classes/
                 */
                if((!$stmt instanceof PhpParser\Node\Stmt\Nop) && (! $stmt instanceof PhpParser\Node\Stmt\Function_) && (! $stmt instanceof PhpParser\Node\Expr\Stmt\Class_) && (! $stmt instanceof PhpParser\Node\Stmt\TryCatch)) {
                    $current->stmt = $stmt;
                    $current->parent = $parent;
                    $parent->child = $current;
                    $parent = $current;
                }       
                else{
                    #print get_class($stmt)."\n";
                    #print "should not happend\n";
                }
            }
        }
        
	    $end = new CFGTreeNode($nodeindex ++);
        Store::$idmaptonode[$nodeindex - 1] = $end;
        // add id map => node
	    $end->type = end;
	    $parent->child = $end;
	    $end->parent = $parent;
	    $end->child = null;
	    return array($start, $end);
    }


	// now reconstruct conditon node/ if /else if/  else and so on/
	// it should follow with several branches(at least one)
	// and transfer it into
	// and one dummy node after that
	/**
	 * return order should be like
	 * ifcond, elseifconds(array), ifstmtNodes, elseifstmtNodes, enda
	 */
	public static function processStmtIf($stmtIf) {
        global $nodeindex;
        //global $idmaptonode;
	    // stmtIf has keys 'cond', 'stmts', 'elseifs', and 'else'.
	    // Array of CFG nodes representing the conditions.
	    $ifconds = array();
	    $ifcond = new CFGTreeCondNode($nodeindex ++);
        Store::$idmaptonode[$nodeindex - 1] = $ifcond;
        // add id map => node
	    $ifcond->cond = $stmtIf->cond;
	    $bodystarts = array();
	    $bodyends = array();
        // print("processstmtif\n");
	    $body = CFG::constructcfg($stmtIf->stmts);
	    $body[0]->parent = $ifcond;
	    $ifconds[] = $ifcond;
	    $bodystarts[] = $body[0];
	    $bodyends[] = $body[1];

	    foreach($stmtIf->elseifs as $elseif) {
	        $cond_node = new CFGTreeCondNode($nodeindex ++);
            Store::$idmaptonode[$nodeindex - 1] = $cond_node;
            // add id map => node
	        $cond_node->cond = $elseif->cond;
	        $body = CFG::constructcfg($elseif->stmts);
	        $ifconds[] = $cond_node;
	        $body[0]->parent = $cond_node;
	        $bodystarts[] = $body[0];
	        $bodyends[] = $body[1];
	    }
	     // Create and add the else body node if it exists
	    $cond_node = new CFGTreeCondNode($nodeindex ++);
        Store::$idmaptonode[$nodeindex - 1] = $cond_node;
        // add id map => node
	    $cond_node->cond = null;
	    if ($stmtIf->else) {
	        $body = CFG::constructcfg($stmtIf->else->stmts);
	    }
	    else{
	         $body = CFG::constructcfg([]);
	    }
	    $body[0]->parent = $cond_node;
	    $ifconds[] = $cond_node;
	    $bodystarts[] = $body[0];
	    $bodyends[] = $body[1];
	    return array($ifconds, $bodystarts, $bodyends);
	}


	// Constructs a node of loop.
	// 1) Creates a CFG node for the loop condition that
	// acts as the loop header.
	// 2) Creates a CFG of the body of the loop.
	// 3) Links the exit of the body CFG to the loop header CFG.
	// 4) Creates an exit dummy node.
	// 5) Links the condition node to the CFG of the body and the dummy
	// exit node.
	public function processStmtLoop($stmtLoop) {
	    // Create the CFG node for the loop header.
	    $init = $loop = null;
	    $looptype = null;
	    $cond = null;
	    if ($stmtLoop instanceof PhpParser\Node\Stmt\Foreach_) {
	        $cond = $stmtLoop->expr;
	        $looptype = ForeachLoop;
	    }
	    else if ($stmtLoop instanceof PhpParser\Node\Stmt\For_) {
	        $init = $stmtLoop->init;
	        foreach($stmtLoop->cond as $co)
	            $cond = And_($cond, $co);
	        $loop = $stmtLoop->loop; 
	        $looptype = ForLoop;
	    }
	    else if ($stmtLoop instanceof PhpParser\Node\Stmt\While_) {
	        $cond = $stmtLoop->cond;
	        $looptype = WhileLoop;
	    }
	    else if ($stmtLoop instanceof PhpParser\Node\Stmt\Do_) {
	        $cond = $stmtLoop->cond;
	        $looptype = DoWhileLoop;
	    }
	    else {
	        print "ERROR Unrecognized loop type while construction CFG node.\n";
	    }
        // print("processstmtloop\n");
	    $body = CFG::constructcfg($stmtLoop->stmts);
	    return array($looptype, $body[0], $body[1], $cond, $init, $loop);
	}

	/**
	 * Switch it into if elseif else structure
	 */
	public function processStmtSwitch($stmtSwitch){
        global $nodeindex;
        //global $idmaptonode;

	    $conds = array();
	    $bodystarts = array();
	    $bodyends = array();
	    $elsebody = null;
	    foreach($stmtSwitch->cases as $case){        
	        $body = CFG::constructcfg($case->stmts);
	        if($case->cond){
	            $cond = new CFGTreeCondNode($nodeindex ++);
                Store::$idmaptonode[$nodeindex - 1] = $cond; 
                // add id map => node
	            $cond->cond = new PhpParser\Node\Expr\BinaryOp\Equal($case->cond, $stmtSwitch->cond);
	            $conds[] = $cond;
	            $bodystarts[] = $body[0];
	            $body[0]->parent = $cond;
	            $bodyends[] = $body[1];
	        }
	        else{
	            $elsebody = $body;
	        }
	    }
	    $cond = new CFGTreeCondNode($nodeindex ++);
        Store::$idmaptonode[$nodeindex - 1] = $cond;
        // add id map => node
	    $cond->cond = null;
	    $conds[] = $cond;
	    if (!$elsebody){
	        $elsebody = CFG::constructcfg([]);
	    }
	    $bodystarts[] = $elsebody[0];
	    $elsebody[0]->parent = $cond;
	    $bodyends[] = $elsebody[1];
	    // print count($bodystarts) ."\n";
	    return array($conds, $bodystarts, $bodyends);
	}
}

?>
