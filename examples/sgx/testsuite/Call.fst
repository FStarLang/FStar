module Test
open Ast

 (*
	Calling Convention:
	1. First four arguments are sent via rcx, rdx, r8 and r9
	2. Remaining arguments are sent via stack
	

 In the below example, we are using only stack (but not heap because bitmap for heap should be set by V)

 main:

  rbp := 2100
  push rbp
  rbp := rsp

  rbx := 10uL
  push rbx 
  pop rdx
  rcx := 0
  call "foo"
  rsp := rbp
  return

 counter:
    push rbp
    rbp := rsp

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
				(Pop  (1205uL, (Register "rdx")));
				(Assign (1206uL, (Register "rcx"), (Constant 0uL)));
				(Call (1207uL, (Constant 1220uL)));
		 		(Assign (1208uL, (Register "rsp"), (Register "rbp")));
				(Pop (1209uL, (Register "rbp")));
				(Return 1210uL)	
				]));
		("counter", 
		 Seq (1220uL, [(Push (1220uL, (Register "rbp")));
				(Assign (1221uL, (Register "rbp"), (Register "rsp")));
				(Add (1222uL, (Register "rcx"), (Register "rcx"),(Constant 1uL)));
				(Cmp (1223uL, (Register "flag"), (Register "rdx"),(Register "rcx")));
		 		(If (1224uL, (Register "flag"), Seq (1215uL, [  
						(Assign (1225uL, (Register "rax"), (Register "rcx")));
						(Jump (1226uL, (Constant 1218uL) ))
						 ]),
					     Seq (1227uL, [  
						(Jump (1227uL, (Constant 1222uL) ))
						 ])
				    )
				);
		 		(Assign (1228uL, (Register "rsp"), (Register "rbp")));
				(Pop (1229uL, (Register "rbp")));
				(Return 1230uL)
				]))
		]
let testprogram = mylambda 
let make_callentry = [(MkCallentry 1200uL "main" [] Public false);(MkCallentry 1220uL "counter" [Mkintarg;Mkintarg] Public false)]
let make_calltable = 
		   let calltabentry = make_callentry in
			(MkCalltable calltabentry)

 (* Place holder for parsing manifest and getting the start addresses and  
    calltable. For now just making calltable
 *)
let parse_manifest _ = make_calltable

