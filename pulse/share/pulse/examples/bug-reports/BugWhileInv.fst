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

module BugWhileInv
#lang-pulse
open Pulse.Lib.Pervasives

let workaround (b:bool) (v:nat) : slprop =
    pure (not b ==> v == 0)


fn count_down_ugly (x:ref nat)
requires exists* v. pts_to x v
ensures pts_to x 0
{
  with v. assert (pts_to x v);
  fold (workaround true v);
  while (
    let v = !x;
    with b v'. unfold (workaround b v');
    if (v = 0)
    {
      fold (workaround false v);
      false;
    }
    else
    {
      x := v - 1;
      fold (workaround true (v - 1));
      true;
    }
  )
  invariant b.
    exists* v. 
        pts_to x v **
        workaround b v
  { () };
  with v. unfold (workaround false v);
 }



fn count_down (x:ref nat)
requires exists* v. pts_to x v
ensures pts_to x 0
{
  while (
    let v = !x;
    if (v = 0)
    {
      false;
    }
    else
    {
      x := v - 1;
      true;
    }
  )
  invariant b.
    exists* v. 
        pts_to x v **
        pure ((b == false) ==> (v == 0))
  { () };
 }
