<?php
include_once __DIR__ ."/../includes.php";
class MyFunction{
    public $spacename = '';
	public $classname = '';
	public $funcname = '';
    public $filename = "";
	public $params = [];
	public $start = null;
	public $end = null;
    public $startnodeid = 0;
    public $endnodeid = 0;
	public function __construct($spacename, $classname, $funcname) {
        $this->spacename = $spacename;
		$this->classname = $classname;
		$this->funcname = $funcname;
	}
}
