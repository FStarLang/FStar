module Matches

#lang-pulse

open Pulse

let is_deque_suffix
  (#t:Type0)
  (l:list t {Cons? l})
  : Tot slprop (decreases l)
  = match l with
    | [n] -> emp
    | n::ns -> emp

let is_deque_suffix_factored_next
  (#t:Type0)
  (l:list t{Cons? l})
  : Tot slprop
= match l with
  | [n] -> emp
  | n::ns -> emp

ghost
fn test0 (#t:_) (x:t) (l:list t)
  requires
    pure (Cons? l) **
    is_deque_suffix_factored_next (x::l)
  ensures
    is_deque_suffix_factored_next (x::l)
{
  unfold (is_deque_suffix_factored_next (x::l));
  fold (is_deque_suffix_factored_next (x::l));
}

ghost
fn test1 (#t:_) (x:t) (l:list t)
  requires
    pure (Cons? l) **
    is_deque_suffix_factored_next (x::l)
  ensures
    is_deque_suffix_factored_next (x::l)
{
  unfold (is_deque_suffix_factored_next (x::l));
  match l {
    Cons y ys -> {
      fold (is_deque_suffix_factored_next (x::l));
    }
  }
}

ghost
fn test2 (#t:_) (x:t) (l:list t)
  requires
    is_deque_suffix_factored_next (x::l)
  ensures
    is_deque_suffix_factored_next (x::l)
{
  unfold (is_deque_suffix_factored_next (x::l));
  match l {
    Cons y ys -> {
      fold (is_deque_suffix_factored_next (x::l));
    }
    Nil -> {
      fold (is_deque_suffix_factored_next (x::l));
    }
  }
}
