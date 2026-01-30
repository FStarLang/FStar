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
module LL = Pulse.Lib.LinkedList

/// A stack is implemented using a linked list
/// The head of the list is the top of the stack (LIFO order)
let stack (t:Type0) = LL.llist t

/// The stack predicate: a stack represents a list in LIFO order
/// We just use is_list directly to avoid rewrite issues
let is_stack #t ([@@@mkey]s:stack t) (l:list t) : slprop = LL.is_list s l

/// Create an empty stack
fn create (#t:Type0) (_:unit)
  requires emp
  returns s : stack t
  ensures is_stack s []
{
  let s = LL.create t;
  rewrite (LL.is_list s []) as (is_stack s []);
  s
}

/// Check if stack is empty
fn is_empty (#t:Type0) (s:stack t)
  requires is_stack s 'l
  returns b:bool
  ensures is_stack s 'l ** pure (b <==> ('l == []))
{
  rewrite (is_stack s 'l) as (LL.is_list s 'l);
  let b = LL.is_empty s;
  rewrite (LL.is_list s 'l) as (is_stack s 'l);
  b
}

/// Push an element onto the stack
/// Creates a new node with the value and links it to the current stack
fn push (#t:Type0) (s:stack t) (v:t)
  requires is_stack s 'l
  returns s':stack t
  ensures is_stack s' (v::'l)
{
  rewrite (is_stack s 'l) as (LL.is_list s 'l);
  let s' = LL.cons v s;
  rewrite (LL.is_list s' (v::'l)) as (is_stack s' (v::'l));
  s'
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
  rewrite (is_stack s (reveal hd :: tl)) as (LL.is_list s (reveal hd :: tl));
  let sv = LL.pop s;
  rewrite (LL.is_list (fst sv) tl) as (is_stack (fst sv) tl);
  sv
}

/// Peek at the top element without removing it
fn peek (#t:Type0) (s:stack t)
  (#hd:erased t)
  (#tl:erased (list t))
  requires is_stack s (reveal hd :: tl)
  returns v:t
  ensures is_stack s (reveal hd :: tl) ** pure (v == hd)
{
  rewrite (is_stack s (reveal hd :: tl)) as (LL.is_list s (reveal hd :: tl));
  let v = LL.head s;
  rewrite (LL.is_list s (reveal hd :: tl)) as (is_stack s (reveal hd :: tl));
  v
}

/// Get the size of the stack
fn size (#t:Type0) (s:stack t)
  (#l:erased (list t))
  requires is_stack s l
  returns n:nat
  ensures is_stack s l ** pure (n == List.Tot.length l)
{
  rewrite (is_stack s l) as (LL.is_list s l);
  let n = LL.length s;
  rewrite (LL.is_list s l) as (is_stack s l);
  n
}

