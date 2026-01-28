(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.Stack

#lang-pulse
open Pulse.Lib.Pervasives
open FStar.List.Tot
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }

/// Internal node structure for the stack
/// Each node contains a value and an optional pointer to the next node
noeq
type node (t:Type0) = {
    value : t;
    next : option (node_ptr t);
}

and node_ptr (t:Type0) = box (node t)

/// A stack is represented as an optional pointer to the top node
and stack (t:Type0) = option (node_ptr t)

/// Recursive predicate: a stack pointer represents a list
/// The list is in LIFO order (head of list = top of stack)
let rec is_stack #t ([@@@mkey]s:stack t) (l:list t)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (s == None)
    | hd::tl -> 
      exists* (v:node_ptr t) (next:stack t).
        pure (s == Some v) **
        pts_to v { value = hd; next } **
        is_stack next tl

/// Alternative view of is_stack for case analysis
let is_stack_cases #t ([@@@mkey]s:stack t) (l:list t)
  : Tot slprop
  = match s with
    | None -> pure (l == [])
    | Some v -> 
      exists* (n:node t) (tl:list t).
        pts_to v n **
        pure (l == n.value::tl) **
        is_stack n.next tl

/// Ghost lemma: convert is_stack to is_stack_cases
ghost
fn cases_of_is_stack (#t:Type) (s:stack t) (l:list t)
    requires is_stack s l
    ensures is_stack_cases s l
{
    match l {
        [] -> {
            unfold (is_stack s []);
            fold (is_stack_cases None l);
            rewrite (is_stack_cases None l) as (is_stack_cases s l);
        }
        hd :: tl -> {
            unfold (is_stack s (hd::tl));
            with v next. _;
            let Some v_ptr = s;
            rewrite each v as v_ptr;
            rewrite each next as (({ value = hd; next }).next) in (is_stack next tl);
            fold (is_stack_cases (Some v_ptr) l);
            rewrite (is_stack_cases (Some v_ptr) l) as (is_stack_cases s l)
        }
    }
}

/// Ghost lemma: convert is_stack_cases back to is_stack
ghost
fn is_stack_of_cases (#t:Type) (s:stack t) (l:list t)
    requires is_stack_cases s l
    ensures is_stack s l
{
    match s {
        None -> { 
            unfold (is_stack_cases None l);
            fold (is_stack s []);
            rewrite (is_stack s []) as (is_stack s l)
        }
        Some v -> {
            unfold (is_stack_cases (Some v) l);
            with _n _tl. _;
            fold (is_stack s (_n.value::_tl));
            rewrite (is_stack s (_n.value::_tl)) as (is_stack s l)
        }
    }
}

/// Ghost lemma: handle None case
ghost 
fn is_stack_cases_none (#t:Type) (s:stack t) (#l:list t)
    requires is_stack s l ** pure (s == None)
    ensures is_stack s l ** pure (l == [])
{
  match l {
    Nil -> {
      ();
    }
    Cons _ _ -> {
      unfold is_stack;
      assert (pure False);
      unreachable ();
    }
  }
}

/// Ghost lemma: handle Some case
ghost
fn is_stack_cases_some (#t:Type) (s:stack t) (v:node_ptr t) (#l:list t) 
    requires is_stack s l ** pure (s == Some v)
    ensures exists* (node:node t) (tl:list t).
                pts_to v node **
                pure (l == node.value::tl) **
                is_stack node.next tl
{
    cases_of_is_stack s l;
    rewrite (is_stack_cases s l) as (is_stack_cases (Some v) l);
    unfold (is_stack_cases (Some v) l);
}

/// Ghost lemma: introduce is_stack from components
ghost
fn intro_is_stack_cons (#t:Type0) (s:stack t) (v:node_ptr t) (#node:node t) (#tl:list t)
    requires pts_to v node ** is_stack node.next tl ** pure (s == Some v)
    ensures is_stack s (node.value::tl)
{
  fold (is_stack s (node.value::tl));
}

/// Create an empty stack
fn create (#t:Type0) (_:unit)
  requires emp
  returns s : stack t
  ensures is_stack s []
{
  let s = None #(node_ptr t);
  fold (is_stack s []);
  s
}

/// Check if stack is empty
fn is_empty (#t:Type0) (s:stack t)
  requires is_stack s 'l
  returns b:bool
  ensures is_stack s 'l ** pure (b <==> ('l == []))
{
  match s {
    None -> {
      is_stack_cases_none None;
      assert (pure ('l == []));
      rewrite (is_stack None 'l) as (is_stack s 'l);
      true
    }
    Some v -> {
      is_stack_cases_some (Some v) v;
      intro_is_stack_cons s v;
      false
    }
  }
}

/// Push an element onto the stack
/// Creates a new node with the value and links it to the current stack
fn push (#t:Type0) (s:stack t) (v:t)
  requires is_stack s 'l
  returns s':stack t
  ensures is_stack s' (v::'l)
{
  // Create a new node
  let new_node_ptr = Box.alloc { value = v; next = s };
  
  // Rewrite to help F* understand the structure
  rewrite each s as ({value = v; next = s}).next in (is_stack s 'l);
  
  // Fold the is_stack predicate for the new stack
  fold (is_stack (Some new_node_ptr) (v::'l));
  
  Some new_node_ptr
}

/// Pop an element from the stack
/// Removes and returns the top element
fn pop (#t:Type0) (s:stack t)
  (#hd:erased t)
  (#tl:erased (list t))
  requires is_stack s (reveal hd :: tl)
  returns sv:(stack t & t)
  ensures is_stack (fst sv) tl ** pure (snd sv == hd)
{
  // Prove that s must be Some since list is non-empty
  ghost fn prove_some ()
    requires is_stack s (reveal hd :: tl)
    ensures is_stack s (reveal hd :: tl) ** pure (Some? s)
  {
    unfold (is_stack s (reveal hd :: tl));
    fold (is_stack s (reveal hd :: tl));
  };
  prove_some ();
  
  // Use case analysis to extract the node
  let Some v_ptr = s;
  is_stack_cases_some (Some v_ptr) v_ptr;
  
  with _node _tl. _;
  
  // Read the node value
  let node_val = !v_ptr;
  let value = node_val.value;
  let next = node_val.next;
  
  // Rewrite to connect next with _node.next
  rewrite each _node.next as next;
  
  // Free the node
  Box.free v_ptr;
  
  // Return the new stack and the value
  (next, value)
}

/// Peek at the top element without removing it
fn peek (#t:Type0) (s:stack t)
  (#hd:erased t)
  (#tl:erased (list t))
  requires is_stack s (reveal hd :: tl)
  returns v:t
  ensures is_stack s (reveal hd :: tl) ** pure (v == hd)
{
  // Prove that s must be Some since list is non-empty
  ghost fn prove_some ()
    requires is_stack s (reveal hd :: tl)
    ensures is_stack s (reveal hd :: tl) ** pure (Some? s)
  {
    unfold (is_stack s (reveal hd :: tl));
    fold (is_stack s (reveal hd :: tl));
  };
  prove_some ();
  
  let Some v_ptr = s;
  is_stack_cases_some (Some v_ptr) v_ptr;
  
  with _node _tl. _;
  
  // Read the node value
  let node_val = !v_ptr;
  let value = node_val.value;
  
  // Reconstruct the stack predicate
  intro_is_stack_cons s v_ptr;
  
  value
}

/// Get the size of the stack by recursively traversing it
fn rec size (#t:Type0) (s:stack t)
  (#l:erased (list t))
  requires is_stack s l
  returns n:nat
  ensures is_stack s l ** pure (n == List.Tot.length l)
{
  match s {
    None -> {
      is_stack_cases_none None;
      rewrite (is_stack None l) as (is_stack s l);
      0
    }
    Some v -> {
      is_stack_cases_some (Some v) v;
      with _node _tl. _;
      let node_val = !v;
      let tail_size = size node_val.next;
      intro_is_stack_cons s v;
      1 + tail_size
    }
  }
}

