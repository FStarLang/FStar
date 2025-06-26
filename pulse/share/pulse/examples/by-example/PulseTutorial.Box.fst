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

module PulseTutorial.Box
#lang-pulse
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box

//new_heap_ref$
fn new_heap_ref (#a:Type) (v:a)
requires emp
returns r:Box.box a
ensures Box.pts_to r v
{
    Box.alloc v
}
//end new_heap_ref$


//last_value_of$
fn last_value_of #a (r:Box.box a)
requires Box.pts_to r 'v
returns v:a
ensures pure (v == 'v)
{
    open Box;
    let v = !r;
    free r;
    v
}
//end last_value_of$


fn incr (r:ref int)
requires pts_to r 'v
ensures pts_to r ('v + 1)
{
    let v = !r;
    r := v + 1
}


//incr_box$
fn incr_box (r:Box.box int)
requires Box.pts_to r 'v
ensures Box.pts_to r ('v + 1)
{
    Box.to_ref_pts_to r;     //Box.pts_to (box_to_ref r) 'v
    incr (Box.box_to_ref r); //pts_to (box_to_ref r) ('v + 1)
    Box.to_box_pts_to r      //Box.pts_to r ('v + 1)
}
//end incr_box$



//copy_free_box$
fn copy_free_box (#a:Type) (r:Box.box a)
requires Box.pts_to r 'v
returns r':Box.box a
ensures Box.pts_to r' 'v
{
    open Box;
    let v = !r;
    free r;
    alloc v
}
//end copy_free_box$



//copy_box$
fn copy_box #a #p (r:Box.box a)
requires Box.pts_to r #p 'v
returns s:Box.box a
ensures Box.pts_to s 'v ** Box.pts_to r #p 'v
{
    open Box;
    let v = !r;
    alloc v
}
//end copy_box$