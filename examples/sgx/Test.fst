module Test
open Ast

(*
  let mylambda = [("main", Seq (1200uL, [(Assign (1200uL, (Register "rbx"), (Constant 1400uL)))]))]
  let mylambda = [("main", Seq (1200uL, [(Assign (1200uL, (Register "rbx"), (Constant 1400uL)));(Store (1201uL, 1uL, (Register "rbx"), (Constant 10uL)))]))]
 *)

 (*
 main:
  rbp := rsp
  rbx := 1400uL
  store rbx 10uL 
  rdx := load(rbx)
  rcx := 0
  call "foo"
  rsp := rbp
  return

 counter:
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
		 Seq (1200uL, [(Assign (1200uL, (Register "rbp"), (Constant 1000uL)));(Push (1200uL, (Register "rbp")));
				(Assign (1201uL, (Register "rbp"), (Register "rsp")));
				(Assign (1202uL, (Register "rbx"), (Constant 1402uL)));
		 		(Store (1203uL, 1uL, (Register "rbx"), (Constant 10uL)));
				(Load (1204uL, (Register "rdx"), 1uL, (Register "rbx")));
				(Call (1205uL, (Constant 1210uL)));
		 		(Assign (1206uL, (Register "rsp"), (Register "rbp")));
				(Pop (1207uL, (Register "rbp")));
				(Return 1208uL)	
				]));
		("counter", 
		 Seq (1210uL, [(Push (1210uL, (Register "rbp")));
				(Assign (1211uL, (Register "rbp"), (Register "rsp")));
				(Add (1212uL, (Register "rcx"), (Register "rcx"),(Constant 1uL)));
				(Cmp (1213uL, (Register "flag"), (Register "rdx"),(Register "rcx")));
		 		(If (1214uL, (Register "flag"), Seq (1215uL, [  
						(Assign (1215uL, (Register "rax"), (Register "rcx")));
						(Jump (1216uL, (Constant 1218uL) ))
						 ]),
					     Seq (1217uL, [  
						(Jump (1217uL, (Constant 1212uL) ))
						 ])
				    )
				);
		 		(Assign (1218uL, (Register "rsp"), (Register "rbp")));
				(Pop (1219uL, (Register "rbp")));
				(Return 1220uL)
				]))
		]
let testprogram = mylambda 
let make_callentry = [(MkCallentry 1200uL "main" [] Public);(MkCallentry 1210uL "counter" [Mkintarg;Mkintarg] Public)]
let make_calltable = 
		   let calltabentry = make_callentry in
			(MkCalltable calltabentry)

 (* Place holder for parsing manifest and getting the start addresses and  
    calltable. For now just making calltable
 *)
let parse_manifest _ = make_calltable

