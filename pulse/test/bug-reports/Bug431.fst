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
returns FStar.SizeT.t
{
  17sz;
}

[@@expect_failure [228]]
fn test_with_local_array2 ()
returns v:int
ensures pure (v == 0)
{
  //We do not hoist the length---expected a constant
  let mut x = [| array_initializer(); effectful_length() |];
  x.(16sz);
}

let pure_length () = 17sz

[@@expect_failure [228]]
fn test_with_local_array3 ()
returns v:int
ensures pure (v == 0)
{
  //This fails too: The length should be a constant
  let mut x = [| array_initializer(); pure_length() |];
  x.(16sz);
}