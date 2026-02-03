(*
   Copyright 2024 Microsoft Research

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

module Pulse.Lib.LinkedList.Iter

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LinkedList
open Pulse.Lib.Trade.Util
module T = Pulse.Lib.Trade.Util
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box }

/// Iterator implementation: 
/// - orig field is pure data (the original pointer)
/// - cur_box holds the mutable current position
noeq
type iter (t:Type0) = {
  orig : llist t;      // Original list head (pure, for returning at end)
  cur_box : box (llist t);  // Current position in the list (mutable)
}

/// Pure projection to get the original list pointer
let llist_of (#t:Type0) (it:iter t) : llist t = it.orig

/// The is_iter predicate:
/// - The cur_box holds the current position
/// - A trade allows reconstruction of the full original list from current position
let is_iter (#t:Type0) ([@@@mkey]it:iter t) 
            (original:erased (list t)) 
            (remaining:erased (list t))
  : Tot slprop
  = exists* (cur:llist t).
      Box.pts_to it.cur_box cur **
      is_list cur remaining **
      (is_list cur remaining @==> is_list it.orig original)

/// Create an iterator - the list hasn't been consumed yet, so remaining == original
fn create_iter (#t:Type0) (x:llist t)
  requires is_list x 'l
  returns it:iter t
  ensures is_iter it 'l 'l
  ensures pure (llist_of it == x)
{
  let cur_box = Box.alloc x;
  let it : iter t = { orig = x; cur_box = cur_box };
  // Rewrite cur_box to it.cur_box (they're equal)
  rewrite (Box.pts_to cur_box x) as (Box.pts_to it.cur_box x);
  // We have: is_list x 'l
  // Need: is_list x 'l @==> is_list x 'l (reflexive trade)
  T.refl (is_list x 'l);
  // Rewrite to use it.orig (which equals x)
  rewrite (is_list x 'l @==> is_list x 'l) 
       as (is_list x 'l @==> is_list it.orig 'l);
  fold (is_iter it 'l 'l);
  it
}

/// Check if there are more elements
fn has_next (#t:Type0) (it:iter t) 
            (#original #remaining: erased (list t))
  requires is_iter it original remaining
  returns b:bool
  ensures is_iter it original remaining ** 
          pure (b <==> Cons? remaining)
{
  unfold (is_iter it original remaining);
  
  // Read the current position
  let cur = Box.(!it.cur_box);
  
  // Check if current position is empty
  let b = is_empty cur;
  
  // Fold back the iterator predicate
  fold (is_iter it original remaining);
  
  // Return negation of b (non-empty means has_next)
  not b
}

/// Get current element and advance to next
fn next (#t:Type0) (it:iter t)
         (#original #remaining: erased (list t))
  requires is_iter it original remaining
  requires pure (Cons? remaining)
  returns v:t
  ensures exists* tl. 
          pure (remaining == v :: tl) **
          is_iter it original tl
{
  unfold (is_iter it original remaining);
  
  with cur. _;
  
  // Read current position
  let c = Box.(!it.cur_box);
  
  // Get the head value using the LinkedList.head function
  let v = head c;
  
  // Move to next element
  let next_cur = move_next c;
  
  with tl. _;
  
  // Update the current position
  Box.(it.cur_box := next_cur);
  
  // Compose the trades: 
  // We have: is_list next_cur tl @==> is_list c remaining
  // We have: is_list c remaining @==> is_list it.orig original
  // We need: is_list next_cur tl @==> is_list it.orig original
  T.trans _ _ (is_list it.orig original);
  
  fold (is_iter it original tl);
  
  v
}

/// Finish iteration and return the original list head
fn finish_iter (#t:Type0) (it:iter t)
               (#original: erased (list t))
  requires is_iter it original []
  returns x:llist t
  ensures is_list x original
  ensures pure (x == llist_of it)
{
  unfold (is_iter it original []);
  
  with cur. _;
  
  // cur represents [] (remaining is empty)
  // We have: is_list cur []
  // We have: trade (is_list cur []) (is_list it.orig original)
  
  // Use the trade to reconstruct the original
  elim_trade (is_list cur []) (is_list it.orig original);
  
  // Free the cur_box
  Box.free it.cur_box;
  
  // Return the original list head (which is llist_of it)
  it.orig
}
