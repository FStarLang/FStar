module Test
open Ast

  (* let mylambda = ("main", [(Store(1uL,(Register "rax"),(Register "rcx")))])  *)

  let mylambda = ("main", Seq (1200uL, [(Load (1200uL, (Register "rax"), 4uL, (Register "rbx"))); (Jump (1201uL, Constant 1200uL)); (Return 1202uL)])) 
  let testprogram = [mylambda] 
