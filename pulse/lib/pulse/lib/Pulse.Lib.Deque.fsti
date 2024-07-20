module Pulse.Lib.Deque
#lang-pulse

open Pulse
open FStar.List.Tot

new
val deque (t:Type0) : Type0

val is_deque #t (x:deque t) (l:list t)
  : Tot slprop


fn mk_empty (#t:Type) (_:unit)
  requires emp
  returns  p : deque t
  ensures  is_deque p []



fn push_front (#t:Type) (l : deque t) (x : t)
  (#xs:erased (list t))
  requires is_deque l xs
  returns  l' : deque t
  ensures  is_deque l' (x::xs)



fn pop_front (#t:Type) (l : deque t)
  (#x : erased t)
  (#xs : erased (list t))
  requires is_deque l (reveal x :: xs)
  returns  l'x : (deque t & t)
  ensures  is_deque (fst l'x) xs ** pure (snd l'x == x)



fn push_back (#t:Type) (l : deque t) (x : t)
  (#xs:erased (list t))
  requires is_deque l xs
  returns  l' : deque t
  ensures  is_deque l' (xs @ [x])



fn pop_back (#t:Type) (l : deque t)
  (#x : erased t)
  (#xs : erased (list t))
  requires is_deque l (xs @ [reveal x])
  returns  l'x : (deque t & t)
  ensures  is_deque (fst l'x) xs ** pure (snd l'x == x)

