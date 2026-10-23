module Postfix
#lang-pulse

open Pulse
module A = Pulse.Lib.Array
module U32 = FStar.UInt32
module Seq = FStar.Seq
open Pulse.Lib.Comment

noeq
type view = {
  data: A.array U32.t;
  apply: U32.t -> U32.t
}

let increment (x:U32.t) : U32.t = U32.add_mod x 1ul
let get_data (v:view) : A.array U32.t = v.data

fn exercise (v:view)
  requires A.pts_to v.data (Seq.create 2 7ul)
  returns r:FStar.Int32.t
  ensures A.pts_to v.data (Seq.upd (Seq.create 2 7ul) 0 9ul)
{
  A.pts_to_len v.data;
  let before = A.op_Dot_Lparen_Rparen v.data 0sz;
  A.op_Dot_Lparen_Rparen_Less_Minus v.data 0sz 9ul;
  let after = A.op_Dot_Lparen_Rparen v.data 0sz;
  let via_call = A.op_Dot_Lparen_Rparen (get_data v) 0sz;
  rewrite each (get_data v) as v.data;
  rewrite each v.data as (comment_gen "buffer" v.data "end");
  let commented = A.op_Dot_Lparen_Rparen (comment_gen "buffer" v.data "end") 0sz;
  rewrite each (comment_gen "buffer" v.data "end") as v.data;
  let buffer = v.data;
  rewrite each v.data as buffer;
  let apply = v.apply;
  let via_alias = A.op_Dot_Lparen_Rparen buffer 0sz;
  rewrite each buffer as v.data;
  let answer = apply via_alias;
  let commented_answer = (comment_gen "callee" v.apply "end") via_alias;
  if (U32.eq before 7ul && U32.eq after 9ul &&
      U32.eq via_call 9ul && U32.eq commented 9ul &&
      U32.eq answer 10ul && U32.eq commented_answer 10ul)
  { 0l } else { 1l }
}

fn main ()
  returns r:FStar.Int32.t
{
  let a = A.alloc 7ul 2sz;
  let v = { data = a; apply = increment };
  rewrite each a as v.data;
  let result = exercise v;
  rewrite each v.data as a;
  A.free a;
  result
}
