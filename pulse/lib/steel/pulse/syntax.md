# Goals

* Pure, ghost, and effectful constructs are distinguished
* Full F* syntax is available for types, pure and ghost things
* Effectful syntax cleans up various F* oddities (match/end etc.)

## General structure: Expressions and Statements

The full syntax of F* is available for expressions, useful for pure
and ghost constructs.

A new statement syntax introduced for effectful constructs

We do not have explicit syntax for return, break, and other imperative
control operators (at least not yet).

Every statement has an implicit return value, i.e, the return value of
its last statement.

We use the metavariable `e` and `t` for expressions and `s` for
statements.

## Variable declarations, initializations, and assignments

We have two kinds of variables, mutable and immutable.
Some of them may be declared without initialization

1. Variable declaration

```
var x : t
```

Declares an uninitialized variable `x:t`, which can be initialized
only once in `s`

2. Mutable variable declaration

```
var mut x : t
```

Declares an uninitialized mutable variable `x:t`, which can be
assigned and read after initialization repeatedly in `s`.

Variables can also be initialized when declared, where the initializer
is a statement `s`.

```
var [mut] x = s
```

3. Assignment

A variable `x` declared as `var mut` can be assigned using:

`x := s`

4. Dereference

Rather than distinguishing l-values and r-values, dereference is
explicit. There is no address-taking operation. An un-dereferenced
local variable is passed by reference.

## Block scopes

A statement `s` can be enclosed within a block `{ s }` to enclose it
in a new scope.

## Control constructs

### Sequential composition

Is always of the form `s1; s2`

E.g., one can write the following:


```
var mut x = e; s
x := s; s2
```

etc.

### Branching

1. If and else

```
if e [: computation type annotation ] { s }
```

or 

```
if e [: computation type annotation ] { s }
else { s }
```

2. Match

```
match e [:type annotation] {
 | Pattern -> s
  ... 
 | Pattern -> s
}
```

## Grammar

```
expressions e, t ::= ...          full F* syntax for atomic expressions

statement s ::= a
              | x := a            assignment
              | var x : t         declarations
              | var mut x : t
              | var x [:t] = a
              | var mut x [:t] = a
              | s ; s             sequencing
              | {  s  }          block
              | if e [: t]
                { s } 
                [else { s } ]
              | match e [:t] {
                  | p -> s
                  ...
                  | p -> s
                }
              | while(s) 
                invariant e
                { s } 
    
        
atomic forms 
          a ::= e                expression statement
              | f(a1,..,an)      call
              | *x               dereference

computation type
          c ::= [ATOMIC | GHOST]
                REQUIRES vp
                RETURNS  x : t
                ENSURES  vp

vprop     vp ::= e
              |  vp * vp
              |  exists (x:t). vp
              |  forall (x:t). vp

top-level d  ::= FN f (x1:t1, ..., xn:tn) : c { s }
```


For example, here's how an iterative fibonacci would look

```
fn fibonacci(n:nat)
  requires emp
  returns  _ : nat
  ensures emp
 {
   var mut i0 = 1;
   var mut i1 = 1;
   var mut ctr = 1;   
   while (!ctr < n) 
   invariant (...) 
   {
      var tmp = !i0;
      i0 := i1;
      i1 := !tmp + !i0;
      ctr := !ctr + 1
   };
   !i1
}
```
