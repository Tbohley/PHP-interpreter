<?php
declare(strict_types=1);

/** Progress: Full VEBG4 in PHP — parser ({…} syntax), interp, primops, tests. */

// --- AST & values ---
interface ExprC {}
class NumC implements ExprC { public function __construct(public float|int $n) {} }
class IdC implements ExprC { public function __construct(public string $s) {} }
class StringC implements ExprC { public function __construct(public string $s) {} }
class IfC implements ExprC {
    public function __construct(public ExprC $test, public ExprC $then, public ExprC $else) {}
}
class LamC implements ExprC {
    public function __construct(public array $args, public ExprC $body) {}
}
class AppC implements ExprC {
    public function __construct(public ExprC $fun, public array $args) {}
}

interface Value {}
class NumV implements Value { public function __construct(public float|int $n) {} }
class BoolV implements Value { public function __construct(public bool $b) {} }
class StringV implements Value { public function __construct(public string $s) {} }
class CloV implements Value {
    public function __construct(public array $args, public ExprC $body, public Environment $env) {}
}
class PrimV implements Value {
    public function __construct(public $callback) {}
}

class Binding { public function __construct(public string $name, public Value $val) {} }
class Environment {
    public function __construct(public array $bindings = [], public ?Environment $parent = null) {}
}

const RESERVED = ['if', '=', 'given', 'fn', '->', 'do'];

function vebg(string $msg, string $src = ''): never {
    throw new Exception('VEBG: ' . $msg . ($src !== '' ? " in {$src}" : ''));
}

function lookup(string $sym, Environment $env): Value {
    foreach ($env->bindings as $b) {
        if ($b->name === $sym) return $b->val;
    }
    return $env->parent ? lookup($sym, $env->parent) : vebg("unbound identifier '{$sym}'");
}

function unique_names(array $names, string $ctx, string $src): void {
    if (count($names) !== count(array_unique($names))) {
        vebg("duplicate name in {$ctx}", $src);
    }
}

function check_id(string $name, string $src): IdC {
    if (in_array($name, RESERVED, true)) vebg("'{$name}' is reserved", $src);
    return new IdC($name);
}

// --- Lexer: returns list of [tag, text] ---
function tokenize(string $src): array {
    $toks = [];
    $n = strlen($src);
    $i = 0;
    while ($i < $n) {
        while ($i < $n && ctype_space($src[$i])) $i++;
        if ($i >= $n) break;
        $start = $i;
        $c = $src[$i];
        if ($c === '=') {
            $toks[] = ['=', '='];
            $i++;
            continue;
        }
        if (str_contains('{[()]}', $c)) {
            $toks[] = [$c, $c];
            $i++;
            continue;
        }
        if ($c === '"') {
            $i++;
            $buf = '';
            while ($i < $n && $src[$i] !== '"') {
                if ($src[$i] === '\\') {
                    $i++;
                    $buf .= match ($src[$i] ?? '') { 'n' => "\n", 't' => "\t", '\\' => '\\', '"' => '"', default => vebg('bad escape', $src) };
                } else {
                    $buf .= $src[$i];
                }
                $i++;
            }
            if ($i >= $n) vebg('unterminated string', $src);
            $i++;
            $toks[] = ['str', $buf];
            continue;
        }
        if ($i + 1 < $n && $src[$i] === '-' && $src[$i + 1] === '>') {
            $toks[] = ['->', '->'];
            $i += 2;
            continue;
        }
        if (ctype_digit($c) || ($c === '-' && ($src[$i + 1] ?? '') !== '' && ctype_digit($src[$i + 1]))) {
            if ($src[$i] === '-') $i++;
            while ($i < $n && ctype_digit($src[$i])) $i++;
            if ($i < $n && $src[$i] === '.') {
                $i++;
                if ($i >= $n || !ctype_digit($src[$i])) vebg('bad number', $src);
                while ($i < $n && ctype_digit($src[$i])) $i++;
            }
            $toks[] = ['num', substr($src, $start, $i - $start)];
            continue;
        }
        while ($i < $n && !ctype_space($src[$i]) && !str_contains('{[()]}', $src[$i])) {
            if ($src[$i] === '=' && ($i === $start || !in_array($src[$i - 1], ['<', '>'], true))) {
                break;
            }
            $i++;
        }
        $text = substr($src, $start, $i - $start);
        if ($text === '') vebg('unexpected char', $src);
        $toks[] = [match ($text) { 'if', 'given', 'fn', 'do' => $text, default => 'id' }, $text];
    }
    $toks[] = ['eof', ''];
    return $toks;
}

// --- Parser ---
final class P {
    private int $i = 0;
    public function __construct(private array $t, private string $src) {}

    public static function parse(string $src): ExprC {
        $src = trim($src);
        if ($src === '') vebg('empty program');
        $p = new self(tokenize($src), $src);
        $e = $p->expr();
        if ($p->tag() !== 'eof') vebg('extra input', $src);
        return $e;
    }

    private function tag(): string { return $this->t[$this->i][0]; }
    private function text(): string { return $this->t[$this->i][1]; }
    private function eat(?string $want = null): string {
        if ($this->tag() === 'eof') vebg('unexpected eof', $this->src);
        if ($want !== null && $this->tag() !== $want) {
            vebg("expected {$want}, got {$this->text()}", $this->src);
        }
        return ($this->t[$this->i++])[1];
    }

    private function expr(): ExprC {
        return match ($this->tag()) {
            'num' => new NumC(($t = $this->eat('num')) && str_contains($t, '.') ? (float)$t : (int)$t),
            'str' => new StringC($this->eat('str')),
            'id' => check_id($this->eat('id'), $this->src),
            '{' => $this->brace(),
            default => vebg('expected expression', $this->src),
        };
    }

    private function brace(): ExprC {
        $this->eat('{');
        return match ($this->tag()) {
            'if' => $this->ifForm(),
            'given' => $this->givenForm(),
            'fn' => $this->fnForm(),
            default => $this->appForm(),
        };
    }

    private function ifForm(): IfC {
        $this->eat('if');
        $t = $this->expr();
        $th = $this->expr();
        if ($this->tag() === '}') vebg('if missing else', $this->src);
        $el = $this->expr();
        $this->eat('}');
        return new IfC($t, $th, $el);
    }

    private function fnForm(): LamC {
        $this->eat('fn');
        $this->eat('(');
        $args = [];
        while ($this->tag() !== ')') {
            $args[] = check_id($this->eat('id'), $this->src)->s;
        }
        $this->eat(')');
        unique_names($args, 'fn', $this->src);
        $this->eat('->');
        $body = $this->expr();
        $this->eat('}');
        return new LamC($args, $body);
    }

    private function givenForm(): ExprC {
        $this->eat('given');
        $this->eat('{');
        $names = [];
        $rhss = [];
        while ($this->tag() === '[') {
            $this->eat('[');
            $names[] = check_id($this->eat('id'), $this->src)->s;
            $this->eat('=');
            $rhss[] = $this->expr();
            $this->eat(']');
        }
        $this->eat('}');
        unique_names($names, 'given', $this->src);
        $this->eat('do');
        $body = $this->expr();
        $this->eat('}');
        return new AppC(new LamC($names, $body), $rhss);
    }

    private function appForm(): ExprC {
        $fun = $this->expr();
        $args = [];
        while ($this->tag() !== '}') $args[] = $this->expr();
        $this->eat('}');
        return new AppC($fun, $args);
    }
}

function parse(string $src): ExprC { return P::parse($src); }

function expr_str(ExprC $e): string {
    return match (true) {
        $e instanceof NumC => (string)$e->n,
        $e instanceof IdC => $e->s,
        $e instanceof StringC => json_encode($e->s),
        $e instanceof IfC => '{if ' . expr_str($e->test) . ' ' . expr_str($e->then) . ' ' . expr_str($e->else) . '}',
        $e instanceof LamC => '{fn (' . implode(' ', $e->args) . ') -> ' . expr_str($e->body) . '}',
        $e instanceof AppC => '{' . expr_str($e->fun) . ' ' . implode(' ', array_map(expr_str(...), $e->args)) . '}',
    };
}

// --- Interpreter ---
function interp(ExprC $e, Environment $env): Value {
    if ($e instanceof NumC) return new NumV($e->n);
    if ($e instanceof StringC) return new StringV($e->s);
    if ($e instanceof IdC) return lookup($e->s, $env);
    if ($e instanceof LamC) return new CloV($e->args, $e->body, $env);
    if ($e instanceof IfC) {
        $t = interp($e->test, $env);
        if (!$t instanceof BoolV) vebg('if test must be boolean', expr_str($e));
        return $t->b ? interp($e->then, $env) : interp($e->else, $env);
    }
    $fv = interp($e->fun, $env);
    $av = array_map(fn($a) => interp($a, $env), $e->args);
    if ($fv instanceof PrimV) return ($fv->callback)($av);
    if ($fv instanceof CloV) {
        if (count($fv->args) !== count($av)) {
            vebg('wrong arity', expr_str($e));
        }
        $bs = [];
        foreach ($fv->args as $i => $n) $bs[] = new Binding($n, $av[$i]);
        return interp($fv->body, new Environment($bs, $fv->env));
    }
    vebg('cannot apply ' . serialize_value($fv), expr_str($e));
}

function serialize_value(Value $v): string {
    return match (true) {
        $v instanceof NumV => (string)$v->n,
        $v instanceof BoolV => $v->b ? 'true' : 'false',
        $v instanceof StringV => json_encode($v->s, JSON_UNESCAPED_UNICODE),
        $v instanceof CloV => '#<procedure>',
        $v instanceof PrimV => '#<primop>',
        default => vebg('bad value'),
    };
}

function nat_idx(Value $v, string $op): int {
    if (!$v instanceof NumV || $v->n < 0 || (is_float($v->n) && $v->n != floor($v->n))) {
        vebg("{$op} expected natural");
    }
    return (int)$v->n;
}

function vals_eq(Value $a, Value $b): bool {
    if ($a instanceof CloV || $a instanceof PrimV || $b instanceof CloV || $b instanceof PrimV) return false;
    return ($a instanceof NumV && $b instanceof NumV && $a->n === $b->n)
        || ($a instanceof BoolV && $b instanceof BoolV && $a->b === $b->b)
        || ($a instanceof StringV && $b instanceof StringV && $a->s === $b->s);
}

function binop(string $op, callable $f): PrimV {
    return new PrimV(function (array $a) use ($op, $f): Value {
        if (count($a) !== 2 || !$a[0] instanceof NumV || !$a[1] instanceof NumV) vebg("{$op} expects 2 numbers");
        return $f($a[0], $a[1]);
    });
}

function top_env(): Environment {
    return new Environment([
        new Binding('true', new BoolV(true)),
        new Binding('false', new BoolV(false)),
        new Binding('+', binop('+', fn($x, $y) => new NumV($x->n + $y->n))),
        new Binding('-', binop('-', fn($x, $y) => new NumV($x->n - $y->n))),
        new Binding('*', binop('*', fn($x, $y) => new NumV($x->n * $y->n))),
        new Binding('/', new PrimV(function (array $a): Value {
            if (count($a) !== 2 || !$a[0] instanceof NumV || !$a[1] instanceof NumV) vebg('/ expects 2 numbers');
            if ($a[1]->n == 0) vebg('division by zero');
            return new NumV($a[0]->n / $a[1]->n);
        })),
        new Binding('<=', binop('<=', fn($x, $y) => new BoolV($x->n <= $y->n))),
        new Binding('strlen', new PrimV(fn($a) => count($a) === 1 && $a[0] instanceof StringV
            ? new NumV(strlen($a[0]->s)) : vebg('strlen expects 1 string'))),
        new Binding('substring', new PrimV(function (array $a): Value {
            if (count($a) !== 3 || !$a[0] instanceof StringV || !$a[1] instanceof NumV || !$a[2] instanceof NumV) {
                vebg('substring expects string and two naturals');
            }
            $s = $a[0]->s;
            $lo = nat_idx($a[1], 'substring');
            $hi = nat_idx($a[2], 'substring');
            $len = strlen($s);
            if ($lo > $len || $hi > $len || $hi < $lo) vebg('substring bad range');
            return new StringV(substr($s, $lo, $hi - $lo));
        })),
        new Binding('equal?', new PrimV(fn($a) => count($a) === 2 ? new BoolV(vals_eq($a[0], $a[1])) : vebg('equal? expects 2 args'))),
        new Binding('error', new PrimV(fn($a) => count($a) === 1
            ? throw new Exception('user-error ' . serialize_value($a[0])) : vebg('error expects 1 arg'))),
    ]);
}

function top_interp(string $src): string {
    return serialize_value(interp(parse($src), top_env()));
}

// --- Tests ---
if (PHP_SAPI === 'cli' && realpath($argv[0] ?? '') === realpath(__FILE__)) {
    $ok = $fail = 0;
    $eq = function (string $src, string $want, string $name) use (&$ok, &$fail) {
        $got = top_interp($src);
        if ($got === $want) { echo "PASS: {$name}\n"; $ok++; }
        else { echo "FAIL: {$name} want {$want} got {$got}\n"; $fail++; }
    };
    $ex = function (callable $fn, string $sub, string $name) use (&$ok, &$fail) {
        try { $fn(); echo "FAIL: {$name}\n"; $fail++; }
        catch (Exception $e) {
            if (str_contains($e->getMessage(), $sub)) { echo "PASS: {$name}\n"; $ok++; }
            else { echo "FAIL: {$name} {$e->getMessage()}\n"; $fail++; }
        }
    };

    $eq('{+ 10 5}', '15', 'add');
    $eq('{if true 1 2}', '1', 'if true');
    $eq('{if false 1 2}', '2', 'if false');
    $eq('{ {fn (x y) -> {+ x y}} 10 20}', '30', 'closure');
    $eq('{given {[z = {+ 9 14}] [y = 98]} do {+ z y}}', '121', 'given');
    $eq('"hi"', '"hi"', 'string');
    $eq('{strlen "calpoly"}', '7', 'strlen');
    $eq('{substring "abcdef" 1 4}', '"bcd"', 'substring');
    $eq('{equal? 3 3}', 'true', 'equal?');
    $eq('{equal? + +}', 'false', 'equal? primop');
    $eq('{given {[+ = 1]} do +}', '1', 'shadow');
    $eq('{if {<= 5 3} 100 200}', '200', 'if cmp');

    $ex(fn() => parse('{if 1 2}'), 'VEBG', 'if no else');
    $ex(fn() => parse('{fn (x x) -> 1}'), 'VEBG', 'dup fn');
    $ex(fn() => top_interp('bad'), 'VEBG', 'unbound');
    $ex(fn() => top_interp('{if 5 1 2}'), 'VEBG', 'if not bool');
    $ex(fn() => top_interp('{/ 1 0}'), 'VEBG', 'div0');
    $ex(fn() => top_interp('{ {fn (x y) -> {+ x y}} 1}'), 'VEBG', 'arity');
    $ex(fn() => top_interp('{error 99}'), 'user-error', 'error');

    echo str_repeat('-', 40) . "\n{$ok} passed, {$fail} failed\n";
}
