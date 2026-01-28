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

/// A stack data structure with LIFO (Last-In-First-Out) semantics
val stack (t:Type0) : Type0

/// Abstract predicate relating a concrete stack to an abstract list
/// The list represents the stack with the head being the top of the stack
val is_stack #t ([@@@mkey]s:stack t) (l:list t)
  : Tot slprop

/// Create an empty stack
fn create (#t:Type0) (_:unit)
  requires emp
  returns s : stack t
  ensures is_stack s []

/// Check if the stack is empty
fn is_empty (#t:Type0) (s:stack t)
  requires is_stack s 'l
  returns b:bool
  ensures is_stack s 'l ** pure (b <==> ('l == []))

/// Push an element onto the stack
/// Maintains LIFO invariant: the element becomes the new top
fn push (#t:Type0) (s:stack t) (v:t)
  requires is_stack s 'l
  returns s':stack t
  ensures is_stack s' (v::'l)

/// Pop an element from the stack
/// Requires: stack must be non-empty (proven by 'l being a Cons)
/// Returns: tuple of (new stack, popped element)
fn pop (#t:Type0) (s:stack t)
  (#hd:erased t)
  (#tl:erased (list t))
  requires is_stack s (reveal hd :: tl)
  returns sv:(stack t & t)
  ensures is_stack (fst sv) tl ** pure (snd sv == hd)

/// Peek at the top element without removing it
/// Requires: stack must be non-empty
fn peek (#t:Type0) (s:stack t)
  (#hd:erased t)
  (#tl:erased (list t))
  requires is_stack s (reveal hd :: tl)
  returns v:t
  ensures is_stack s (reveal hd :: tl) ** pure (v == hd)

/// Get the size of the stack
fn size (#t:Type0) (s:stack t)
  (#l:erased (list t))
  requires is_stack s l
  returns n:nat
  ensures is_stack s l ** pure (n == List.Tot.length l)
