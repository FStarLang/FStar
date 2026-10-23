module CExternStmt
open FStar.All
open FStar.Attributes
module U32 = FStar.UInt32

type choice = | A | B | C

[@@custard_extern "CS_STORE"; custard_c_header "CExternStmt_stubs.h"]
assume val store (x:U32.t) : ML unit
[@@custard_extern "CS_BLOCK"; custard_c_header "CExternStmt_stubs.h"]
assume val block (x:U32.t) : ML unit
[@@custard_extern "CS_PAIR"; custard_c_header "CExternStmt_stubs.h"]
assume val pair (x:U32.t) : ML unit
[@@custard_extern "cs_reset"; custard_c_header "CExternStmt_stubs.h"]
assume val reset (_:unit) : ML unit
[@@custard_extern "cs_get"; custard_c_header "CExternStmt_stubs.h"]
assume val get (_:unit) : ML U32.t
[@@custard_extern "cs_count"; custard_c_header "CExternStmt_stubs.h"]
assume val count (_:unit) : ML U32.t

let conditional (a:bool) : ML U32.t =
  reset ();
  (if a then store 1ul else store 2ul);
  get ()

let blocked (a:bool) : ML U32.t =
  reset ();
  (if a then block 1ul else block 2ul);
  get ()

let multiple (a:bool) : ML U32.t =
  reset ();
  (if a then pair 1ul else ());
  count ()

let matching (x:choice) : ML U32.t =
  reset ();
  (match x with A -> store 1ul | B -> store 2ul | C -> store 3ul);
  get ()

let main () : ML FStar.Int32.t =
  let a = conditional true in
  let b = conditional false in
  let c = blocked true in
  let d = blocked false in
  let e = multiple true in
  let f = multiple false in
  let g = matching A in
  let h = matching B in
  let i = matching C in
  if U32.eq a 1ul && U32.eq b 2ul &&
     U32.eq c 1ul && U32.eq d 2ul &&
     U32.eq e 1ul && U32.eq f 0ul &&
     U32.eq g 1ul && U32.eq h 2ul && U32.eq i 3ul
  then 0l else 1l
