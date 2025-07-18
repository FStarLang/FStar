module Bug431
#lang-pulse
open Pulse

fn foo ()
  requires pure False
  returns int
{ 0; }

[@@expect_failure [19]]
fn let_mut_not_anf ()
{
  let mut x = foo();
  ()
}

fn array_initializer ()
returns v:int
ensures pure (v == 0)
{
  0
}

fn test_with_local_array ()
returns v:int
ensures pure (v == 0)
{
  let mut x = [| array_initializer(); 17sz |];
  x.(16sz);
}

fn effectful_length()
returns x : SizeT.t
ensures pure (SizeT.v x == 17)
{
  17sz;
}

fn test_with_local_array2 ()
returns v:int
ensures pure (v == 0)
{
  //We do also hoist the length
  let mut x = [| array_initializer(); effectful_length() |];
  x.(16sz);
}

inline_for_extraction
fn effectful_length2()
returns FStar.SizeT.t
{
  17sz;
}

[@@expect_failure [19]]
fn test_with_local_array2' ()
returns v:int
ensures pure (v == 0)
{
  // This one fails, since there is no guarantee that
  // the value returned by effectful_length2 is > 16.
  let mut x = [| array_initializer(); effectful_length2() |];
  x.(16sz);
}

let pure_length () = 17sz

fn test_with_local_array3 ()
returns v:int
ensures pure (v == 0)
{
  let mut x = [| array_initializer(); pure_length() |];
  x.(16sz);
}

inline_for_extraction
let pure_length_inline () = 17sz

fn test_with_local_array4 ()
returns v:int
ensures pure (v == 0)
{
  let mut x = [| array_initializer(); pure_length_inline() |];
  x.(16sz);
}


inline_for_extraction
let pure_length_inline2 () = pure_length()

fn test_with_local_array5 ()
returns v:int
ensures pure (v == 0)
{
  //this succeeeds too, although it does not fully inline
  //the syntactic check on the constant does not actually
  //do the inlining
  let mut x = [| array_initializer(); pure_length_inline2() |];
  x.(16sz);
}


fn hoist_nested_stateful_apps_let_mut
(arr : array bool)
(i : ref SizeT.t)
(#s:erased _ { Seq.length s > 0 })
requires arr |-> s
requires i |-> 0sz
returns b:bool
ensures arr |-> s
ensures i |-> 0sz
ensures pure (b == Seq.index s 0)
{
  pts_to_len arr;
  let mut x = arr.(!i);
  !x;
}

fn hoist_nested_stateful_apps_let_mut_array
(arr : array bool)
(i : ref SizeT.t)
(#s:erased _ { Seq.length s > 0 })
requires arr |-> s
requires i |-> 0sz
returns b:bool
ensures arr |-> s
ensures i |-> 0sz
ensures pure (b == Seq.index s 0)
{
  pts_to_len arr;
  let mut x = [| arr.(!i); 17sz |];
  (x.(0sz));
}

fn hoist_nested_stateful_apps_if
(arr : array bool)
(i : ref SizeT.t)
(#s:erased _ { Seq.length s > 0 })
requires arr |-> s
requires i |-> 0sz
returns b:bool
ensures arr |-> s
ensures i |-> 0sz
ensures pure (b == Seq.index s 0)
{
  pts_to_len arr;
  if (arr.(!i))
  {
    true;
  }
  else
  { 
    false
  }
}

fn test2 (x:ref (ref int)) (#v:erased (ref int))
requires x |-> v
requires (Ghost.reveal v) |-> 'n
returns n:int
ensures x |-> v
ensures (Ghost.reveal v) |-> 'n
ensures pure (n == 'n)
{
  let mut v = !(!x);
  !v
}