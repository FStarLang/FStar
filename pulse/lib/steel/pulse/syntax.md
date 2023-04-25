FYI, I've been working on syntax extension support and thinking about
the best way to do it.

My current thinking is that an extension can register a
parsing/desugaring callback with a signature like:

```    
val extension_parser (d:DsEnv.env) (start_pos:range) (blob:string)
  : either error_message Parser.AST.decl
```

* An extension registers an extension parser dynamically. 

* The extension parser is called by F* during desugaring, i.e., in
  FStar.ToSyntax, passing it the current desugaring environment, the
  source position at which the extension blob begins, and the blob
  itself.
  
* The extension parser can 

   - Fail, returning an error message (e.g., extension syntax error)
   
   - Succeed completely, returning a `Complete {decl}`, an AST of the
     extension syntax expressed as a FStar.Parser.AST.decl, which will
     then be further processed as usual by the F* compiler pipeline
     (e.g, desugaring by tosyntax etc.)
     
   - `Deferred {spliced_name}`: In this case, the extension parser
     chooses to not fully parse the extension syntax yet (e.g.,
     extension parsing may require some type information that is not
     yet available at this stage of the compiler).



An `extension_parser`



Some extension parsers can ignore the DsEnv.env and just directly parse their custom syntax into an AST.decl. In that case, ToSyntax will take care of name resolution, and desugaring into FStar.Syntax.Syntax.



For Pulse, I don't want to have to go through the indirection of expressing source Pulse syntax in FStar.Syntax.Syntax (equivalently, FStar.Reflection.Data). I would like to see FStar.Reflection.Data as the target language of the Pulse checker, rather than also consuming some mangled form of FStar.Reflection.Data as the source language too.



So, the way I am going is to for Pulse's extension parser to parse some concrete syntax into a custom AST, and then to desugar that AST directly into Pulse.Syntax, relying on the interface provided by FStar.Syntax.DsEnv to do name resolution. Pulse's syntax is stratified, separation pure terms from effectful ones. So, this desugaring will take care of that, relying on name resolution 


# Goals

* Pure, ghost, and effectful constructs are distinguished syntactically
* Full F* syntax is available for types, pure and ghost things
* Effectful syntax cleans up various F* oddities (match/end etc.)

## General structure: Expressions and Statements

The full syntax of F* is available for expressions, useful for pure
and ghost constructs.

A new statement syntax introduced for effectful programs.

Expressions can be promoted to statements in various syntactic ways,
including a specific explicit expression-statement form,
`pure(e)`. This `pure` overlaps with the `pure` vprop constructor, but
is syntactically distinct, since it only appears in statement
position.

We do not have explicit syntax for return, break, and other imperative
control operators (at least not yet).

Every statement has an implicit return value, i.e, the return value of
its last statement.

We use the metavariable `e` and `t` for expressions and `s` for
statements.

## Variable declarations, initializations, and assignments

We have four kinds of variables, two forms of let and two forms of var

1. Let-binding pure definitions

```
let x = e
```

This introduces `x:t { x = e }` in the environment

2. Let-binding ghost definitions

```
let ghost x = e
```

This introduces `x:erased t { x = e }` in the environment

3. Variable declaration

```
var x : t
```

Declares an uninitialized variable `x:t`, which can be initialized
only once in `s`

4. Mutable variable declaration

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

* A pure let binding

```
let x = e; s
```

* A ghost let binding

```
let ghost x = e; s
```

* Assignment

```
x := s; s2
```

etc.

### Branching

1. If and else

```
if e [: type annotation ] { s }
```

or 

```
if e [: type annotation ] { s }
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

## An grammar for statements


```
expressions e, t ::= ...          full F* syntax

statement s ::= a
              | d ; s 
              | s ; s             sequencing
              | {  s   }          block
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
    
                
variable
intro    d ::=  let x = e
              | let ghost x = e
              | var x : t
              | var mut x : t
              | var x = s
              | var mut x = s


atomic 
statement a ::= pure(e)          expression statement
              | f(e1,..,en)      call
              | *x               dereference
              | x := s           assignment              
```


For example, here's how an iterative fibonacci would look

```
fn fibonacci(n:nat) {
   var mut i0 = pure 1;
   var mut i1 = pure 1;
   var mut ctr = 0;   
   while (!ctr < nat) 
   invariant (...) 
   {
      var tmp = !i0;
      i0 := i1;
      i1 := !tmp + !i0;
   };
   !i1
}
```
