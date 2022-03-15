<?php
include_once __DIR__ ."/../includes.php";

class MyClass{
    public $spacename;
    public $classname;
    public $filename = "";
    public $consts = [];
    public $props = [];
    public $classmethods = [];
    public function __construct($spacename, $classname = "MAIN_CLASS") {
        $this->spacename = $spacename;
    	$this->classname = $classname;
    }
}
