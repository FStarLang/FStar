module Bug100
#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
// Rightly fails
[@@expect_failure [19]]
val tst0 (a1 : A.array int) (s1 : Seq.Base.seq nat)
  : stt unit (A.pts_to #int a1 s1) (fun _ -> emp)

assume
val array (t:Type0) : Type0

assume
val pts_to (a:Type u#0) (x:array a) (s: Seq.seq a) : slprop

[@@expect_failure [19]]
let tst (a : array int) (s : Seq.seq nat) = pts_to int a s

[@@expect_failure [228; 19]]

fn init (a1 : array int) (s1 : Seq.Base.seq nat)
  requires pts_to int a1 s1
  ensures  emp
{
  admit();
  ()
}

