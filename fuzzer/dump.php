<?php
require __DIR__  . '/../PHP-Parser-master/vendor/autoload.php';

use PhpParser\Error;
use PhpParser\NodeDumper;
use PhpParser\ParserFactory;

$code = <<<'CODE'
<?php
$x == 1 && $y == 1 && strlen($z) == 10;

CODE;

$parser = (new ParserFactory)->create(ParserFactory::PREFER_PHP7);
try {
    $ast = $parser->parse($code);
} catch (Error $error) {
    echo "Parse error: {$error->getMessage()}\n";
    return;
}

//echo json_encode($ast, JSON_PRETTY_PRINT);
#$dumper = new NodeDumper;
#echo $dumper->dump($ast) . "\n";
include __DIR__ .'/../Taint/Printer.php';
echo dumpJSON($ast);
file_put_contents('constraints.txt', dumpJSON($ast));

