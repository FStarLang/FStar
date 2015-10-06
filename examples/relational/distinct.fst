module Distinct
(* Statements of this form are often needed.. *)
type distinct2 (#t:Type)  (a1:t) (a2:t) =
      a1 <> a2

type distinct3 (#t:Type) (a1:t) (a2:t) (a3:t) =
      a1 <> a2 /\ a1 <> a3
  /\  a2 <> a3

type distinct4 (#t:Type) (a1:t) (a2:t) (a3:t) (a4:t) =
      a1 <> a2 /\ a1 <> a3 /\ a1 <> a4
  /\  a2 <> a3 /\ a2 <> a4 /\  a3 <> a4

type distinct5 (#t:Type) (a1:t) (a2:t) (a3:t) (a4:t) (a5:t) =
      a1 <> a2 /\ a1 <> a3 /\ a1 <> a4 /\ a1 <> a5
  /\  a2 <> a3 /\ a2 <> a4 /\ a2 <> a5
  /\  a3 <> a4 /\ a3 <> a5
  /\  a4 <> a5

type distinct6 (#t:Type) (a1:t) (a2:t) (a3:t) (a4:t) (a5:t) (a6:t) =
      a1 <> a2 /\ a1 <> a3 /\ a1 <> a4 /\ a1 <> a5 /\ a1 <> a6
  /\  a2 <> a3 /\ a2 <> a4 /\ a2 <> a5 /\ a2 <> a6
  /\  a3 <> a4 /\ a3 <> a5 /\ a3 <> a6
  /\  a4 <> a5 /\ a4 <> a6
  /\  a5 <> a6

type distinct7 (#t:Type) (a1:t) (a2:t) (a3:t) (a4:t) (a5:t) (a6:t) (a7:t) =
      a1 <> a2 /\ a1 <> a3 /\ a1 <> a4 /\ a1 <> a5 /\ a1 <> a6 /\ a1 <> a7
  /\  a2 <> a3 /\ a2 <> a4 /\ a2 <> a5 /\ a2 <> a6 /\ a2 <> a7
  /\  a3 <> a4 /\ a3 <> a5 /\ a3 <> a6 /\ a3 <> a7
  /\  a4 <> a5 /\ a4 <> a6 /\ a4 <> a7
  /\  a5 <> a6 /\ a5 <> a7
  /\  a6 <> a7

type distinct8 (#t:Type) (a1:t) (a2:t) (a3:t) (a4:t) (a5:t) (a6:t) (a7:t) (a8:t) =
      a1 <> a2 /\ a1 <> a3 /\ a1 <> a4 /\ a1 <> a5 /\ a1 <> a6 /\ a1 <> a7 /\ a1 <> a8
  /\  a2 <> a3 /\ a2 <> a4 /\ a2 <> a5 /\ a2 <> a6 /\ a2 <> a7 /\ a2 <> a8
  /\  a3 <> a4 /\ a3 <> a5 /\ a3 <> a6 /\ a3 <> a7 /\ a3 <> a8
  /\  a4 <> a5 /\ a4 <> a6 /\ a4 <> a7 /\ a4 <> a8
  /\  a5 <> a6 /\ a5 <> a7 /\ a5 <> a8
  /\  a6 <> a7 /\ a6 <> a8
  /\  a7 <> a8

type distinct9 (#t:Type) (a1:t) (a2:t) (a3:t) (a4:t) (a5:t) (a6:t) (a7:t) (a8:t) (a9:t) =
      a1 <> a2 /\ a1 <> a3 /\ a1 <> a4 /\ a1 <> a5 /\ a1 <> a6 /\ a1 <> a7 /\ a1 <> a8 /\ a1 <> a9
  /\  a2 <> a3 /\ a2 <> a4 /\ a2 <> a5 /\ a2 <> a6 /\ a2 <> a7 /\ a2 <> a8 /\ a2 <> a9
  /\  a3 <> a4 /\ a3 <> a5 /\ a3 <> a6 /\ a3 <> a7 /\ a3 <> a8 /\ a3 <> a9
  /\  a4 <> a5 /\ a4 <> a6 /\ a4 <> a7 /\ a4 <> a8 /\ a4 <> a9
  /\  a5 <> a6 /\ a5 <> a7 /\ a5 <> a8 /\ a5 <> a9
  /\  a6 <> a7 /\ a6 <> a8 /\ a6 <> a9
  /\  a7 <> a8 /\ a7 <> a9
  /\  a8 <> a9

type distinct10 (#t:Type) (a1:t) (a2:t) (a3:t) (a4:t) (a5:t) (a6:t) (a7:t) (a8:t) (a9:t) (a10:t) =
      a1 <> a2 /\ a1 <> a3 /\ a1 <> a4 /\ a1 <> a5 /\ a1 <> a6 /\ a1 <> a7 /\ a1 <> a8 /\ a1 <> a9 /\ a1 <> a10
  /\  a2 <> a3 /\ a2 <> a4 /\ a2 <> a5 /\ a2 <> a6 /\ a2 <> a7 /\ a2 <> a8 /\ a2 <> a9 /\ a2 <> a10
  /\  a3 <> a4 /\ a3 <> a5 /\ a3 <> a6 /\ a3 <> a7 /\ a3 <> a8 /\ a3 <> a9 /\ a3 <> a10
  /\  a4 <> a5 /\ a4 <> a6 /\ a4 <> a7 /\ a4 <> a8 /\ a4 <> a9 /\ a4 <> a10
  /\  a5 <> a6 /\ a5 <> a7 /\ a5 <> a8 /\ a5 <> a9 /\ a5 <> a10
  /\  a6 <> a7 /\ a6 <> a8 /\ a6 <> a9 /\ a6 <> a10
  /\  a7 <> a8 /\ a7 <> a9 /\ a7 <> a10
  /\  a8 <> a9 /\ a8 <> a10
  /\  a9 <> a10

