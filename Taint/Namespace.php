<?php
/**
 * define a namespace
 */

class MyNamespace {
    public $spacename = "";
    public $namespaces = []; // sub namespaces
    public $filename = "";
    public $classes = [];
    public function __construct($spacename) {
        $this->spacename = $spacename;
    }
}

?>
