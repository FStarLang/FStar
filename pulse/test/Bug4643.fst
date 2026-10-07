module Bug4643
#lang-pulse

(* https://github.com/FStarLang/FStar/issues/4643

   A non-final [if] whose branches' inferred postconditions are existential
   used to be joined to a [match] on the condition, which nothing after the
   [if] could see through, even when both branches were identical. *)

open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array

fn dbl (r: A.array nat) (#v: erased (Seq.lseq nat 1))
requires A.pts_to r v
ensures exists* (w: Seq.lseq nat 1). A.pts_to r w
{
  A.pts_to_len r;
  let x = A.(r.(0sz));
  A.(r.(0sz) <- x + x);
}

(* The repro from the issue. *)
fn step (r: A.array nat) (b: bool) (#v: erased (Seq.lseq nat 1))
requires A.pts_to r v
ensures exists* (w: Seq.lseq nat 1). A.pts_to r w
{
  if b { () } else { dbl r };
  ()
}

(* Identical branches. *)
fn step_same (r: A.array nat) (b: bool) (#v: erased (Seq.lseq nat 1))
requires A.pts_to r v
ensures exists* (w: Seq.lseq nat 1). A.pts_to r w
{
  if b { dbl r } else { dbl r };
  ()
}

(* The continuation uses the joined resource. *)
fn step_then (r: A.array nat) (b: bool) (#v: erased (Seq.lseq nat 1))
requires A.pts_to r v
ensures exists* (w: Seq.lseq nat 1). A.pts_to r w
{
  if b { dbl r } else { () };
  dbl r
}
