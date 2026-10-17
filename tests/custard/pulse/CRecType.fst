module CRecType
#lang-pulse
open Pulse
module U32 = FStar.UInt32
module I32 = FStar.Int32
module B = Pulse.Lib.Box

(* Section 17.3: a type that reaches itself, or reaches a type declared later,
   *through a pointer*.  A C struct cannot contain itself by value and Custard
   rejects that outright, but this is ordinary C -- and it used to be emitted
   as an anonymous [typedef struct { ... } t;], whose fields therefore named
   [t] before [t] existed.  Every struct now carries a tag, and every tag is
   forward-declared before any type is defined.

   Three shapes, because the anonymous typedef broke them in three different
   ways: a variant reaching itself through a record declared *after* it,
   mutual recursion between a record and a variant, and a variant reaching
   itself directly. *)

noeq type tree =
  | Leaf : U32.t -> tree
  | Node : node -> tree
and node = { left : B.box tree; right : B.box tree }

noeq type ping = { p_n : U32.t; p_next : B.box pong }
and pong =
  | PEnd
  | PMore : B.box ping -> pong

noeq type chain =
  | Stop
  | Link : U32.t -> B.box chain -> chain

let leaf_val (t : tree) : U32.t =
  match t with
  | Leaf b -> b
  | Node _ -> 0ul

let head (c : chain) : U32.t =
  match c with
  | Stop -> 0ul
  | Link n _ -> n

let pong_val (p : pong) : U32.t =
  match p with
  | PEnd -> 8ul
  | PMore _ -> 0ul

fn root (n : node) (#a #b : erased tree)
  preserves B.pts_to n.left a ** B.pts_to n.right b
  returns r : U32.t
{
  let x = B.op_Bang n.left;
  let y = B.op_Bang n.right;
  U32.add_mod (leaf_val x) (leaf_val y)
}

fn walk (p : ping) (#v : erased pong)
  preserves B.pts_to p.p_next v
  returns r : U32.t
{
  let x = B.op_Bang p.p_next;
  U32.add_mod p.p_n (pong_val x)
}

fn main ()
  returns r : I32.t
{
  let l = B.alloc (Leaf 3ul);
  let rt = B.alloc (Leaf 4ul);
  let n = { left = l; right = rt };
  rewrite each l as n.left, rt as n.right;
  let t1 = root n;
  rewrite each n.left as l, n.right as rt;
  B.free l;
  B.free rt;
  let c2 = B.alloc Stop;
  let c1 = B.alloc (Link 6ul c2);
  let c = Link 5ul c1;
  let c1v = B.op_Bang c1;
  let t2 = U32.add_mod (head c) (head c1v);
  B.free c1;
  B.free c2;
  let nx = B.alloc PEnd;
  let p = { p_n = 7ul; p_next = nx };
  rewrite each nx as p.p_next;
  let t3 = walk p;
  rewrite each p.p_next as nx;
  B.free nx;
  if (U32.eq t1 7ul && U32.eq t2 11ul && U32.eq t3 15ul) { 0l } else { 1l }
}
