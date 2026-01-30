(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module PulseTutorial.Ref
#lang-pulse
open Pulse.Lib.Pervasives


//incr$
fn incr (r:ref int)
requires pts_to r 'v
ensures pts_to r ('v + 1)
{
    let v = !r;
    r := v + 1;
}
//end incr$

//swap$
fn swap u#a (#a: Type u#a) (r0 r1:ref a)
requires pts_to r0 'v0
requires pts_to r1 'v1
ensures pts_to r0 'v1
ensures pts_to r1 'v0
{
    let v0 = !r0;
    let v1 = !r1;
    r0 := v1;
    r1 := v0;
}
//end swap$


 //value_of$
fn value_of u#a (#a:Type u#a) (r:ref a)
preserves pts_to r 'v
returns v:a
ensures pure (v == 'v)
{
    !r;
}
//end value_of$



 //value_of_explicit$
fn value_of_explicit u#a (#a:Type u#a) (r:ref a) (#w:erased a)
preserves pts_to r w
returns v:a
ensures pure (v == reveal w)
{
    !r;
}
//end value_of_explicit$


[@@expect_failure [228]]
 //value_of_explicit_fail$
fn value_of_explicit_fail u#a (#a:Type u#a) (r:ref a) (#w:erased a)
preserves pts_to r w
returns v:a
ensures pure (v == reveal w)
{
    reveal w
}
//end value_of_explicit_fail$


 //value_of_explicit_alt$
fn value_of_explicit_alt u#a (#a:Type u#a) (r:ref a) (#w:erased a)
preserves pts_to r w
returns v:(x:a { x == reveal w } )
{
    let v = !r;
    v
}
//end value_of_explicit_alt$


 //assign$
fn assign u#a (#a:Type u#a) (r:ref a) (v:a)
requires pts_to r 'v
ensures pts_to r v
{
    r := v;
}
//end assign$



 //add$
fn add (r:ref int) (n:int)
requires pts_to r 'v
ensures pts_to r ('v + n)
{
    let v = !r;
    r := v + n;
}
//end add$


open FStar.Mul //can we include this in Pulse.Lib.Pervasives


 //quadruple$
fn quadruple (r:ref int)
requires pts_to r 'v
ensures pts_to r (4 * 'v)
{
    let v1 = !r;
    add r v1;
    let v2 = !r;
    add r v2;
}
//end quadruple$


[@@expect_failure]
 //quadruple_show_proof_state$
fn quadruple (r:ref int)
requires pts_to r 'v
ensures pts_to r (4 * 'v)
{
    let v1 = !r; // Env=v1:int; _:squash (v1 == 'v)       Ctxt= pts_to r v1
    add r v1;    // ...                                   Ctxt= pts_to r (v1 + v1)
    show_proof_state;
    let v2 = !r; // Env=...; v2:int; _:squash(v2==v1+v1)  Ctxt= pts_to r v2 
    add r v2;    // Env=...                               Ctxt= pts_to r (v2 + v2)
                 // ..                                    Ctxt= pts_to r (4 * 'v)
}
//end quadruple_show_proof_state$


//quad FAIL$
fn quad_fail (r:ref int)
requires pts_to r 'v
ensures pts_to r (4 * 'v)
{
    add r (!r);
    add r (!r);
}
//end quad FAIL$




 //assign_1.0R$
fn assign_full_perm u#a (#a:Type u#a) (r:ref a) (v:a)
requires pts_to r #1.0R 'v
ensures pts_to r #1.0R v
{
    r := v;
}
//end assign_1.0R$


 //value_of_perm$
fn value_of_perm u#a (#a: Type u#a) #p (r:ref a)
preserves pts_to r #p 'v
returns v:a
ensures pure (v == 'v)
{
    !r;
}
//end value_of_perm$


//assign_perm FAIL$
[@@expect_failure [19]]

fn assign_perm u#a (#a: Type u#a) #p (r:ref a) (v:a) (#w:erased a)
preserves pts_to r #p w
{
    r := v;
}
//end assign_perm FAIL$


 //share_ref$
fn share_ref u#a (#a: Type u#a) #p (r:ref a)
requires pts_to r #p 'v
ensures pts_to r #(p /. 2.0R) 'v
ensures pts_to r #(p /. 2.0R) 'v
{
    share r;
}
//end share_ref$


 //gather_ref$
fn gather_ref u#a (#a: Type u#a) (#p:perm) (r:ref a)
requires
    pts_to r #(p /. 2.0R) 'v0 **
    pts_to r #(p /. 2.0R) 'v1
ensures
    pts_to r #p 'v0 **
    pure ('v0 == 'v1)
{
    gather r
}
//end gather_ref$



fn max_perm u#a (#a: Type u#a) (r:ref a) #p anything
requires pts_to r #p 'v
requires pure (~ (p <=. 1.0R))
returns _:squash False
ensures anything
{
    pts_to_perm_bound r;
    unreachable();
}


 //alias_ref$
fn alias_ref u#a (#a: Type u#a) #p (r:ref a)
requires pts_to r #p 'v
returns s:ref a
ensures
    pts_to r #(p /. 2.0R) 'v **
    pts_to s #(p /. 2.0R) 'v **
    pure (r == s)
{
    share r;
    r
}
//end alias_ref$



 //one
fn one ()
returns v:int
ensures pure (v == 1)
{
                   //     .     |- emp
    let mut i = 0; // i:ref int |- pts_to i 0
    incr i;        // i:ref int |- pts_to i (0 + 1)
    !i             //      .    |- v:int. emp ** pure (v == 1) 

}
//end one


[@@expect_failure [228]]
 //refs_as_scoped FAIL
fn refs_are_scoped ()
returns s:ref int
ensures pts_to s 0
{
    let mut s = 0;
    s
}
//end refs_as_scoped FAIL






