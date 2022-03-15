<?php
function convertype($val, $type) {
    switch($type){
    case 1:
        return (bool)$val;
    case 2:
        return (int)$val;
    case 4:
        return (string)$val;
    default:
        return (string)$val;
    }

}


if (count($argv) <= 1) {
    echo "No input and exits\n";
    exit();
}

//echo count($argv) ."\n";
$funcname = $argv[1];
$numofarg = (int)$argv[2];
$args = [];
$types = [];

//$args_dump = $argv[3];
$jsonargs = json_decode(file_get_contents('args/' . $funcname . 'args'), true);
//print_r($jsonargs);
foreach($jsonargs as $idx => $arg){
    $args[] = convertype($arg['val'], $arg['type']);
}


if (function_exists($funcname)) {
    $result = [];
    $r = call_user_func_array($funcname, $args);
    var_dump($r);

    //print('return value is  ' . $r . "\n" );
    //$x = var_dump($r);// print with typeinfo down
    //file_put_contents('result.txt', $x);
    return $r;

}
else{
    echo 'then its a user defined function';
    return false;
}


/*
 *
class ffff{
    public function px() {
        if ($this->gs()) {
            return 1;
        }
        return 0;
    }
    public function gs() {
        return 3;
    }
}
 */
