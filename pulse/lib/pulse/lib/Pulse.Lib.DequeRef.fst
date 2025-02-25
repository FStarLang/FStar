module Pulse.Lib.DequeRef
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Deque
module B = Pulse.Lib.Box
open FStar.List.Tot

let dq (t:Type0) = B.box (deque t)

let is_dq (#t:Type0) ([@@@mkey]x:dq t) (l:list t) 
: slprop
= exists* xx. B.pts_to x xx ** is_deque xx l

fn mk_empty (#t:Type) (_:unit)
  requires emp
  returns  p : dq t
  ensures  is_dq p []
{
  let v = mk_empty #t ();
  let x = B.alloc v;
  fold is_dq;
  x
}


fn push_front (#t:Type) (l : dq t) (x : t) (#xs:erased (list t))
requires is_dq l xs
ensures  is_dq l (x::xs)
{
  open Pulse.Lib.Box;
  unfold is_dq;
  with xx0. assert (B.pts_to l xx0);
  let xx = !l;
  rewrite each xx0 as xx;
  let yy = push_front xx x;
  l := yy;
  fold is_dq;
}


fn pop_front (#t:Type) (l : dq t) (#x : erased t) (#xs : erased (list t))
requires is_dq l (reveal x :: xs)
returns  y : t
ensures  is_dq l xs ** pure (y == x)
{
  open Pulse.Lib.Box;
  unfold is_dq;
  with xx0. assert (B.pts_to l xx0);
  let xx = !l;
  rewrite each xx0 as xx;
  let yy = pop_front xx;
  l := fst yy;
  fold is_dq;
  snd yy
}

fn pop_alt (#t:Type) (l : dq t) (#xs : erased (list t) { Cons? xs })
requires is_dq l xs
returns  y: (y : t { Cons?.hd xs == y })
ensures  is_dq l (Cons?.tl xs)
{
  let y = pop_front l #(Cons?.hd xs) #(Cons?.tl xs);
  y
}


fn push_back (#t:Type) (l : dq t) (x : t) (#xs:erased (list t))
requires is_dq l xs
ensures  is_dq l (xs @ [x])
{
  open Pulse.Lib.Box;
  unfold is_dq;
  with xx0. assert (B.pts_to l xx0);
  let xx = !l;
  rewrite each xx0 as xx;
  let yy = push_back xx x;
  l := yy;
  fold is_dq;
}


fn pop_back (#t:Type) (l : dq t) (#x : erased t) (#xs : erased (list t))
requires is_dq l (xs @ [reveal x])
returns  y : t
ensures  is_dq l xs ** pure (y == x)
{
  open Pulse.Lib.Box;
  unfold is_dq;
  with xx0. assert (B.pts_to l xx0);
  let xx = !l;
  rewrite each xx0 as xx;
  let yy = pop_back xx;
  l := fst yy;
  fold is_dq;
  snd yy
}



#push-options "--no_smt"
fn test #t 
    (x1 x2 x3 x4:dq t)
    (v:t)
requires
  is_dq x1 'l1 **
  is_dq x2 'l2 **
  is_dq x3 'l3 **
  is_dq x4 'l4
ensures
  is_dq x1 'l1 **
  is_dq x2 'l2 **
  is_dq x3 'l3 **
  is_dq x4 'l4
{
  push_front x1 v;
  push_front x2 v;
  push_front x3 v;
  push_front x4 v;

  let _ = pop_front x1;
  let _ = pop_front x2;
  let _ = pop_front x3;
  let _ = pop_front x4;
  ()
}
#pop-options
