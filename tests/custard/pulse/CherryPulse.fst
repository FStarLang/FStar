module CherryPulse
#lang-pulse
(* The Cherry backend (cherry.md, "References"): Pulse references
   and arrays holding reference-counted values.  [let mut] and an array
   allocated and freed in one function are on the stack, released when the
   scope ends; a box, and a vector freed somewhere else, are on the heap,
   with the length in a header.  Every value stored is marked shared. *)
open Pulse
module A  = Pulse.Lib.Array
module R  = Pulse.Lib.Reference
module B  = Pulse.Lib.Box
module V  = Pulse.Lib.Vec
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT

let rec sum (l: list int) : int = match l with [] -> 0 | x :: t -> x + sum t

fn stack_ref (l: list int)
  returns r: int
{
  let mut x = l;
  x := 1 :: !x;
  let v = !x;
  sum v
}

fn heap_ref (l: list int)
  returns r: int
{
  let p = R.alloc l;
  p := 2 :: !p;
  let v = !p;
  R.free p;
  sum v
}

fn box (l: list int)
  returns r: int
{
  let p = B.alloc l;
  B.op_Colon_Equals p (3 :: B.op_Bang p);
  let v = B.op_Bang p;
  B.free p;
  sum v
}

fn arr (l: list int) (n: SZ.t)
  requires pure (SZ.v n > 3)
  returns r: int
{
  let a = A.alloc l n;
  A.pts_to_len a;
  a.(1sz) <- 4 :: l;
  let v = a.(1sz);
  let w = a.(3sz);
  A.free a;
  sum v + sum w
}

fn mk (l: list int)
  returns v: V.vec (list int)
  ensures exists* s. V.pts_to v s ** pure (V.length v == 4 /\ V.is_full_vec v /\ Seq.length s == 4)
{
  let v = V.alloc l 4sz;
  V.pts_to_len v;
  v
}

fn consume (v: V.vec (list int)) (#s: erased (Seq.seq (list int)))
  requires V.pts_to v s ** pure (V.length v == 4 /\ V.is_full_vec v)
  returns r: int
{
  V.pts_to_len v;
  open V;
  v.(2sz) <- [10; 20];
  let x = v.(2sz);
  let y = v.(0sz);
  V.free v;
  sum x + sum y
}

fn copy (l m: list int)
  returns r: int
{
  let mut a = [| l; 4sz |];
  let mut b = [| m; 4sz |];
  A.pts_to_len a;
  A.pts_to_len b;
  A.memcpy 4sz a b;
  let x = b.(1sz);
  let y = a.(3sz);
  sum x + sum y
}

fn zero (l: list int)
  returns r: int
{
  let v = V.alloc l 0sz;
  V.free v;
  0
}

fn blit (l m: list int)
  returns r: int
{
  let mut a = [| l; 3sz |];
  let mut b = [| m; 3sz |];
  A.pts_to_len a;
  A.pts_to_len b;
  let p = AP.from_array a;
  let q = AP.from_array b;
  AP.memcpy p 0sz q 0sz 2sz;
  AP.to_array p a;
  AP.to_array q b;
  let x = b.(0sz);
  let y = b.(2sz);
  sum x + sum y
}

fn main ()
  returns x: FStar.Int32.t
{
  let l = [1; 2; 3];
  let a = stack_ref l;
  let b = heap_ref l;
  let c = box l;
  let d = arr l 5sz;
  let v = mk l;
  let e = consume v;
  let f = copy l [5];
  let g = zero [7];
  let h = blit [1; 2] [5];
  if (a = 7 && b = 8 && c = 9 && d = 16 && e = 36 && f = 12 && g = 0 && h = 8) { 0l } else { 1l }
}
