module Pulse.Lib.DequeRef
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.List.Tot

val dq (t:Type0) : Type0

val is_dq (#t:Type0) ([@@@mkey]x:dq t) (l:list t) : slprop

fn mk_empty (#t:Type) (_:unit)
  requires emp
  returns  p : dq t
  ensures  is_dq p []

fn push_front (#t:Type) (l : dq t) (x : t) (#xs:erased (list t))
  requires is_dq l xs
  ensures  is_dq l (x::xs)

fn pop_front (#t:Type) (l : dq t) (#x : erased t) (#xs : erased (list t))
  requires is_dq l (reveal x :: xs)
  returns  y : t
  ensures  is_dq l xs ** pure (y == x)

fn pop_alt (#t:Type) (l : dq t) (#xs : erased (list t) { Cons? xs })
  requires is_dq l xs
  returns  y: (y : t { Cons?.hd xs == y })
  ensures  is_dq l (Cons?.tl xs)

fn push_back (#t:Type) (l : dq t) (x : t) (#xs:erased (list t))
  requires is_dq l xs
  ensures  is_dq l (xs @ [x])

fn pop_back (#t:Type) (l : dq t) (#x : erased t) (#xs : erased (list t))
  requires is_dq l (xs @ [reveal x])
  returns  y : t
  ensures  is_dq l xs ** pure (y == x)
