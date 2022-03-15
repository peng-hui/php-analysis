<?php
include_once __DIR__ ."/../includes.php";

class store{
    public static $idmaptonode = [];
    public static $analysisinformation = [];
    public static $functionmap = [];
    public static $true_node = ""; 
    public static $file2classfunc = []; // map class func
    public static $filevisitflag = []; // map class func
    public static $filenamelist = []; // for global inclusion matching



    public function __construct(){
        $this->idmaptonode = [];
        $this->analysisinformation = [];
        $this->functionmap = [];
        $this->true_node = new PhpParser\Node\Expr\ConstFetch(new PhpParser\Node\Name('True'));
    }
}

/**
 * item in call stack, for each function
 */
class stackitem{
    public $start = null;
    public $end = null;// this end does not mean the end for END OF FUNCTIONS but the place a new function invokes.  
    public $funcname = '';

    // Should replace params with args 
    public $params = [];
    public $args = [];

    public function __construct(){
        // nop??
    }
    public function copyitem(){
        $re = new stackitem();
        $re->start = $this->start;
        $re->end = $this->end;
        $re->args = $this->args;
        $re->params = $this->params;
        return $re;
    }
}

// log source
// do not perform any change on the cfg.
class CallSite{
    #public $node; // that stmt node in CFG.
    public $nodeid; // stmt node id in CFG

    public $expr = null; // single expr

    public $paramaffectargs = [];

    #public $taintedargs;
    #public $constraints; // the constraints to the loop?? or callsite? 

    // it can be in two sites, either loops directly or callsite recursively
    #public $affectloops; // log ids
    #public $affectcallsiteswithloops; // points to the callsite that it affects

}
 

class Path{
    public $steps = []; // step, each step is a node?
}

function printpath($path, $deepth = 0){
    
    $tabs = "";
    for($i = 0; $i < $deepth; $i ++)
        $tabs .= "  ";
    $result = "";
    foreach($path->steps as $s){
        if($s instanceof Path){
            $tr = printpath($s, $deepth + 1);
            $result .= $tr;

        }
        elseif(is_array($s)){
            foreach($s as $es){
                $tr = printpath($es, $deepth + 1);
                $tr .= "\n";
                $result .= $tr;
            }
        }
        else
            $result .= $tabs . $s ."\n";
    }
    return $result;
}


function findpath($path, $src, $dst){
    // start
    foreach($path->steps as $s){
        if($s instanceof Path){
            $tr = find($s, $deepth + 1);
            $result .= $tr;

        }
        elseif(is_array($s)){
            foreach($s as $es){
                $tr = printpath($es, $deepth + 1);
                $tr .= "\n";
                $result .= $tr;
            }
        }
        else
            $result .= $tabs . $s ."\n";
    }
    return $result;
}


class MyObject{
    public $params = [];
    public $classname = "";

}

class MyArray{
    public $items = [];

    public function __construct($items = []){
        $this->items = $items;
    }
}


/**
 * define a class for call stack which saves the function calls informations
 */
class callstack{
    public $items = [];
    public $index = -1; #the current index of item in items

    public function push($item){
        $this->index ++;
        $this->items[$this->index] = $item;
        return true;
    }

    public function pop(){
        if($this->isempty())
            return null;
        $this->index --;
        return $this->items[$this->index + 1];
    }

    public function isempty(){
        return ($this->index == -1) ? true: false;
    }
    public function copystack(){
        $re = new callstack();
        for($i = 0; $i <= $this->index; $i ++){
            $tmpitem = $this->items[$i];
            $re->push($tmpitem->copyitem());
        }
        return $re;
    }
    public function size(){
        return $this->index + 1;
    }
}


/**
 * Act And on lhs and rhs
 * make sure there is none null
 */
function And_($left, $right){
    if($left != null && $right != null && $left instanceof PhpParser\Node\Expr && $right instanceof PhpParser\Node\Expr) {
        return new PhpParser\Node\Expr\BinaryOp\BooleanAnd($left, $right);
    }
    if($left)
        return $left;
    if($right)
        return $right;
    return null;
}
/**
 * Act Or on lhs and rhs
 */
function Or_($left, $right) {
    if($left != null && $right != null && $left instanceof PhpParser\Node\Expr && $right instanceof PhpParser\Node\Expr) {
        return new PhpParser\Node\Expr\BinaryOp\BooleanOr($left, $right);
    }
    if($left)
        return $left;
    if($right)
        return $right;
    return null;
}
/**
 * Act not
 */
function Not_($expr){
    if($expr instanceof PhpParser\Node\Expr\BooleanNot){
        return $expr->expr;
    }
    else return new PhpParser\Node\Expr\BooleanNot($expr);

}

/**
 * Get All assignment in this expression
 * postinc postdec preinc predec ??? forgot @todo
 */
function isassignment($expr){
    if($expr instanceof PhpParser\Node\Expr\Assign || $expr instanceof PhpParser\Node\Expr\AssignOp || $expr instanceof PhpParser\Node\Expr\AssignRef){
        return true;
    }
    return false;
}
/**
 *
 * Retrieve the assignments from current $expr, and make sure the "assignment of assignment situations"
 */
// left hand side can be a 
// obj->property
// variable
// array fetch
// even recursive array
//
function getassignment($expr){
    $lhs = [];
    $rhs = null;
    if($expr instanceof PhpParser\Node\Stmt\Expression){
        return getassignment($expr->expr);
    }
    else if (isassignment($expr)) {
        $lhs[] = $expr->var;
        if(isassignment($expr->expr)){ // continiously assignment
            $re = getassignment($expr->expr);
            foreach($re[0] as $l){
                $lhs[] = $l;
            }
        }
        else{
            $rhs = $expr->expr;
        }
        return [$lhs, $rhs];
    }
    else if($expr instanceof PhpParser\Node\Expr\PostInc || $expr instanceof PhpParser\Node\Expr\PreInc){
        $lhs[] = $expr->var;
        $rhs = new PhpParser\Node\Expr\BinaryOp\Plus($expr->var, new PhpParser\Node\Scalar\LNumber(1));
        return [$lhs, $rhs];
    }
    else if ( $expr instanceof PhpParser\Node\Expr\PostDec || $expr instanceof PhpParser\Node\Expr\PreDec){
        $lhs[] = $expr->var;
        $rhs = new PhpParser\Node\Expr\BinaryOp\Minus($expr->var, new PhpParser\Node\Scalar\LNumber(1));
        return [$lhs, $rhs]; 
    }
    else if( $expr instanceof PhpParser\Node\Expr\ConstFetch) {
       // if(strcasecmp($constname,"true") == 0) // commpare without case
    }
    else if ($expr instanceof PhpParser\Node\Expr\ClassConstFetch) {
        //@todo
        // This is not done
        print "This is TODO Node\ClassConstFetch\n";       
    }   
    return [$lhs, $rhs];
}

/**
 * Compare two expression whether they are the same when print out
 * Did something tricky??
 */
function CmpExpr($expr1, $expr2){
    #print "here comexpr\n";
    if($expr1 instanceof PhpParser\Node && $expr2 instanceof PhpParser\Node) {
        $t1 = PrintExpr($expr1);
        $t2 = PrintExpr($expr2);
        return $t1 == $t2;
    }
    else
        return false;
}


function file_absolute_path($filename, $currentdir){
    if($currentdir && $currentdir[strlen($currentdir) - 1] == "/")
        $currentdir = substr($currentdir, 0, strlen($currentdir) - 1);
    if($filename[0] == "/")
        $filename = substr($filename, 1);
    if(strpos($filename, "/") == false) 
        return $currentdir . "/" . $filename;
    // this is relative path from current path
    if($filename[0] == "." && $filename[1] == "/") {
        return file_absolute_path(substr($filename, 2), $currentdir);
    }
    // previous localtion
    else if($filename[0] == "." && $filename[1] == "." && $filename[2] == "/")  {
        $last_pos = strrpos($currentdir, "/");
        if($last_pos == 0) { // 0 or flase
            $dir = "/";
        }
        else{
            $dir = substr($currentdir, 0, $last_pos);
        }
        //print "exceed error ". $filename."\n";
        //print $currentdir."\n";
        return file_absolute_path(substr($filename, 3), $dir);
    }
    else{
        $first_pos = strpos($filename, "/");
        return file_absolute_path(substr($filename, $first_pos + 1), $currentdir . "/".substr($filename, 0, $first_pos));
    }
}

// try to find current path, whether a certaint filename exists
function file_exists_inpath($path, $filename){
    if(!is_dir($path)) {
        print "WARNINGS: Not a path [".$path."] when find FILE[ ".$filename."]\n";
    }
    else {
        $files = scandir($path); // scan all files in this path
        if(in_array($filename, $files))
            return true;
        else return false;
    }
}
