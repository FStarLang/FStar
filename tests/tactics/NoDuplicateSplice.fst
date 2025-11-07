module NoDuplicateSplice

open FStar.Tactics

let mk (nm:string) (i:int) : Tac decls =
  let lb = { lb_fv = pack_fv (cur_module() @ [nm])
           ; lb_us = []
           ; lb_typ = `int
           ; lb_def = pack (Tv_Const (C_Int i)) } in
  [pack_sigelt (Sg_Let {isrec=false; lbs=[lb]})]

%splice[] (mk "x" 1)

[@@expect_failure [47]]
%splice[] (mk "x" 2)
