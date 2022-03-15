<?php

/**
 * This is for construct a linked table for CFG
 */
class CFGTreeNode{
    public $node = null;
    public $stmt = null;
    public $parent = null;
    public $child = null;
    public $type = '';
    public $nodeid = 0;

    public function __construct($id) {
        $this->nodeid = $id;
    }

}

class CFGTreeIfNode extends CFGTreeNode{
    public $conds = array();
    public $bodystarts = array();
    public $bodyends = array();

    public function __construct($id) {
        parent::__construct($id);
        $this->type = IfStmt;
    }
}

class CFGTreeCondNode extends CFGTreeNode{
    public $cond = null;

    public function __construct($id) {
        parent::__construct($id);
        $this->type = Cond;
    }
}


class CFGTreeSwitchNode extends CFGTreeNode{
    public $cond = null;
    public $cases = array();

    public function __construct($id) {
        parent::__construct($id);
        $this->type = SwitchStmt;
    }
}

class CFGTreeLoopNode extends CFGTreeNode{
    public $init = null;
    public $loop = null;
    public $cond = null; // Not sure it is excatly true
    public $looptype = null;
    public $bodystart = null;
    public $bodyend = null;


    public function __construct($id) {
        parent::__construct($id);
        $this->type = LoopStmt;
    }
}
