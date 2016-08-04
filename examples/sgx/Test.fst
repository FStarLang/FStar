module Test
open Ast

  (* let mylambda = ("main", [(Store(1uL,(Register "rax"),(Register "rcx")))])  *)

 (*
  rbx := 1400uL
  store rbx 10uL 
  rcx := load(rbx)
  rax := 0
 L: add rax 1
    jump L
    return
  let mylambda = ("main", Seq (1200uL, [(Assign (1200uL, (Register "rbx"), (Constant 1400uL)))]))
  let mylambda = ("main", Seq (1200uL, [(Assign (1200uL, (Register "rbx"), (Constant 1400uL)));(Store (1201uL, 1uL, (Register "rbx"), (Constant 10uL)))]))
  *)
  let mylambda = ("main", Seq (1200uL, [(Assign (1200uL, (Register "rbx"), (Constant 1400uL)));(Store (1201uL, 1uL, (Register "rbx"), (Constant 10uL)));(Load (1202uL, (Register "rcx"), 1uL, (Register "rbx")));(Assign (1203uL, (Register "rax"), (Constant 0uL)));(Add (1204uL, (Register "rax"), (Register "rax"), (Constant 1uL)));(Jump (1205uL, Constant 1204uL)); (Return 1206uL)])) 
  let testprogram = [mylambda] 
