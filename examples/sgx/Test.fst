module Test
open Ast

 (*
	Calling Convention:
	1. First four arguments are sent via rcx, rdx, r8 and r9
	2. Remaining arguments are sent via stack
	

 In the below example, we are using only stack (but not heap because bitmap for heap should be set by V)
 The example is complicated by making callee access caller for parameters. Hence the bitmap is set by caller
 before invoking the callee 

 main:

  rbp := 2100
  push rbp
  rbp := rsp

  rbx := 10uL
  push rbx 

  rbx := 1300uL
  sub rax rsp rbx  
  rbx := 1200uL
  div rcx rax 64uL
  mod rdx rax 64uL
  add rbx rbx rcx
  load rcx rbx
  lsr rdx 1uL rdx
  lor rax rcx rdx
  store rbx rax 
  rcx := 0
  rdx := 0
  r8 := 0
  r9 := 0

  call "foo"
  rsp := rbp
  return

 counter:
    push rbp
    rbp := rsp
    add rbx rsp 3uL 
    load rdx rbx

 L1: add rcx rcx 1
    cmp flag rdx rcx
    if flag = 1 then 
      rax := rcx
      jump L2 
    else
      jump L1
 L2: rsp := rbp
     return 
  *)

  let mylambda = [
		 ("main", 
		 Seq (1200uL, [(Assign (1200uL, (Register "rbp"), (Constant 2100uL)));
				(Push (1201uL, (Register "rbp")));
				(Assign (1202uL, (Register "rbp"), (Register "rsp")));
				(Assign (1203uL, (Register "rbx"), (Constant 10uL)));
		 		(Push (1204uL, (Register "rbx")));
				(Assign (1205uL, (Register "rbx"), (Constant 1300uL)));
				(Sub (1206uL, (Register "rax"), (Register "rsp"),  (Register "rbx")));
				(Assign (1207uL, (Register "rbx"), (Constant 1200uL)));
				(Div (1208uL, (Register "rcx"), (Register "rax"),  (Constant 64uL)));
				(Mod (1209uL, (Register "rdx"), (Register "rax"),  (Constant 64uL)));
				(Add (1210uL, (Register "rbx"), (Register "rbx"),  (Register "rcx")));
				(Load (1211uL, (Register "rcx"), 1uL, (Register "rbx")));
				(Lsr (1212uL, (Register "rdx"), (Constant 1uL), (Register "rdx")));
				(Lor (1213uL, (Register "rax"), (Register "rcx"), (Register "rdx")));
				(Store (1214uL, 1uL, (Register "rbx"), (Register "rax")));
				(Assign (1215uL, (Register "rcx"), (Constant 0uL)));
				(Assign (1216uL, (Register "rdx"), (Constant 0uL)));
				(Assign (1217uL, (Register "r8"), (Constant 0uL)));
				(Assign (1218uL, (Register "r9"), (Constant 0uL)));
				(Call (1219uL, (Constant 1230uL)));
		 		(Assign (1220uL, (Register "rsp"), (Register "rbp")));
				(Pop (1221uL, (Register "rbp")));
				(Return 1222uL)	
				]));
		("counter", 
		 Seq (1230uL, [(Push (1230uL, (Register "rbp")));
				(Assign (1231uL, (Register "rbp"), (Register "rsp")));
				(Add (1232uL, (Register "rbx"), (Register "rsp"),(Constant 3uL)));
				(Load (1233uL, (Register "rdx"), 1uL, (Register "rbx")));
				(Add (1234uL, (Register "rcx"), (Register "rcx"),(Constant 1uL)));
				(Cmp (1235uL, (Register "flag"), (Register "rdx"),(Register "rcx")));
		 		(If (1236uL, (Register "flag"), Seq (1237uL, [  
						(Assign (1237uL, (Register "rax"), (Register "rcx")));
						(Jump (1238uL, (Constant 1240uL) ))
						 ]),
					     Seq (1239uL, [  
						(Jump (1239uL, (Constant 1234uL) ))
						 ])
				    )
				);
		 		(Assign (1240uL, (Register "rsp"), (Register "rbp")));
				(Pop (1241uL, (Register "rbp")));
				(Return 1242uL)
				]))
		]
let testprogram = mylambda 
let make_callentry = [(MkCallentry 1200uL "main" [] Public false);(MkCallentry 1230uL "counter" [Mkintarg;Mkintarg] Public false)]
let make_calltable = 
		   let calltabentry = make_callentry in
			(MkCalltable calltabentry)

 (* Place holder for parsing manifest and getting the start addresses and  
    calltable. For now just making calltable
 *)
let parse_manifest _ = make_calltable

