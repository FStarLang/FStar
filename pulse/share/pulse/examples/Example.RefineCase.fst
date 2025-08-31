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

module Example.RefineCase
#lang-pulse
open Pulse.Lib.Pervasives

noeq
type t = 
  | A : r:ref int -> t
  | B : r:ref bool -> t

type t_rep =
  | AR of int
  | BR of bool

let t_perm ([@@@mkey]x:t) (v:t_rep) : slprop =
    match x with
    | A r -> (
      match v with
      | AR i -> pts_to r i
      | _ -> pure False
    )
    | B r -> (
      match v with
      | BR b -> pts_to r b
      | _ -> pure False
    )


ghost
fn elim_false (#a:Type0) (p: (a -> slprop))
    requires pure False
    returns x:a
    ensures p x
{
    let x = false_elim #a ();
    rewrite emp as (p x);
    x
}


//can't reveal in a match scrutinee yet

ghost
fn refine (x:ref int) (v:erased t_rep)
  requires t_perm (A x) v
  returns i:erased int
  ensures pts_to x i ** pure (v == AR i)
{
   let u = reveal v;
   match u {
    AR i -> {
      rewrite (t_perm (A x) v)
          as  (pts_to x i);
      hide i
    }
    BR b -> {
      rewrite (t_perm (A x) v)
          as  (pure False);
      let x = elim_false #int (pts_to x);
      hide x
    }
  }
}


//Or this style

ghost
fn refine_alt (x:ref int) (v:t_rep)
  requires t_perm (A x) v
  returns i:int
  ensures pts_to x i ** pure (v == AR i)
{
   match v {
    AR i -> {
      rewrite (t_perm (A x) v)
          as  (pts_to x i);
      i
    }
    BR b -> {
      rewrite (t_perm (A x) v)
          as  (pure False);
      elim_false (pts_to x)
    }
  }
}




ghost
fn refine_ghost (x:ref int) (v:erased t_rep)
  requires t_perm (A x) v
  returns i:erased int
  ensures pts_to x i ** pure (v == AR i)
{
   let r = refine_alt x v;
   hide r
}

   

// assume
// val refine_ghost (x:ref int) (v:erased t_rep)
//   : stt_ghost (erased int) emp_inames
//     (requires t_perm (A x) v)
//     (ensures (fun i -> pts_to x i ** pure (reveal v == AR i)))
    