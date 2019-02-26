module SeqCalc

open FStar.Mul
open FStar.Calc
open FStar.Preorder
open FStar.Seq

let seq_assoc_4 (s1 s2 s3 s4: seq 'a)
  : Lemma ( ((s1 @| s2) @| s3) @| s4 ==
              s1 @| (s2 @| (s3 @| s4)))
  = calc (==) {
      ((s1 @| s2) @| s3) @| s4;
      == { admit () }
      s1 @| (s2 @| (s3 @| s4));
    }
