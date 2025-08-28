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

module PledgeArith
#lang-pulse

(* automation wishlist for pledges *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge


ghost
fn pledge_return_now (f:slprop) (r : ref int)
  requires pts_to r 123
  ensures pledge emp_inames f (pts_to r 123)
{
  return_pledge f (pts_to r 123); // ideally automated
}



ghost
fn pledge_join (f:slprop) (v1 v2 : slprop)
  requires pledge emp_inames f v1 ** pledge emp_inames f v2
  ensures pledge emp_inames f (v1 ** v2)
{
  join_pledge #emp_inames #f v1 v2; // ideally automated
}



fn pledge_comm (f:slprop) (v1 v2 : slprop)
  requires pledge emp_inames f (v2 ** v1)
  ensures pledge emp_inames f (v1 ** v2)
{
  rewrite_pledge (v2 ** v1) (v1 ** v2) #emp_inames =_{};
  
  // if not fully automated (certainly cannot be for all rewrites)
  // maybe some syntax like
  (*
  rewrite_pledge #emp_inames #f (v2 ** v1) (v1 ** v2) {
    ()
  };
  *)
  // where the block is checked at the type of the `pf` function above
}



ghost
fn pledge_squash (f:slprop) (v1 v2 : slprop)
  requires pledge emp_inames f (pledge emp_inames f v1)
  ensures pledge emp_inames f v1
{
  squash_pledge emp_inames f v1;  // ideally automated
}



ghost
fn pledge_squash_and_join (f:slprop) (v1 v2 : slprop)
  requires pledge emp_inames f (pledge emp_inames f v1) ** pledge emp_inames f v2
  ensures pledge emp_inames f (v1 ** v2)
{
  squash_pledge emp_inames f v1;  // ideally automated
  join_pledge #emp_inames #f v1 v2; // ideally automated
}

