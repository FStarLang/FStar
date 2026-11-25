module EarlyReturn

open FStar.All
module U32 = FStar.UInt32

[@@custard_extern "er_tick"; custard_c_header "EarlyReturn_stubs.h"]
assume val tick : U32.t -> ML U32.t

[@@custard_extern "er_note"; custard_c_header "EarlyReturn_stubs.h"]
assume val note : U32.t -> ML unit

[@@custard_extern "er_trace"; custard_c_header "EarlyReturn_stubs.h"]
assume val trace : unit -> ML U32.t

[@@custard_extern "er_reset"; custard_c_header "EarlyReturn_stubs.h"]
assume val reset : unit -> ML unit

let choose (x:U32.t) : ML U32.t =
  if U32.eq x 0ul then tick 1ul
  else if U32.eq x 1ul then tick 2ul
  else tick 3ul

type shape = | Circle | Square | Other

let classify (s:shape) : ML U32.t =
  match s with
  | Circle -> tick 4ul
  | Square -> tick 5ul
  | Other -> tick 6ul

let nested (a b:bool) : ML U32.t =
  if a then (if b then tick 1ul else tick 2ul) else tick 3ul

(* No early return: unchanged in every mode. *)
let plain (x:U32.t) : U32.t = U32.add_mod x 1ul

let effect_only (x:U32.t) : ML unit =
  if U32.eq x 0ul then note 1ul
  else if U32.eq x 1ul then note 2ul
  else note 3ul

(* An else-branch with nothing to do: nothing to return early from. *)
let maybe_note (b:bool) : ML unit =
  if b then note 7ul else ()

(* A then-branch with nothing to do: the condition is negated. *)
let skip_note (b:bool) : ML unit =
  if b then () else note 8ul

type point = { px: U32.t; py: U32.t }

let make_point (x:U32.t) : ML point =
  if U32.eq x 0ul then { px = U32.add_mod x 1ul; py = 2ul }
  else { px = x; py = 4ul }

(* Locals named like the result variable and the exit label. *)
let named (x:U32.t) : ML U32.t =
  let result = tick x in
  let exit = tick 1ul in
  if U32.eq result 0ul then exit else U32.add_mod result exit

let main () : ML FStar.Int32.t =
  reset ();
  let a = choose 0ul in
  let b = choose 1ul in
  let c = choose 7ul in
  let t1 = trace () in
  reset ();
  let d = classify Circle in
  let e = classify Square in
  let f = classify Other in
  let t2 = trace () in
  reset ();
  let g = nested true true in
  let h = nested true false in
  let i = nested false true in
  let t3 = trace () in
  reset ();
  effect_only 0ul;
  effect_only 1ul;
  effect_only 5ul;
  let t4 = trace () in
  reset ();
  maybe_note true;
  maybe_note false;
  skip_note true;
  skip_note false;
  let t5 = trace () in
  reset ();
  let p = make_point 0ul in
  let q = make_point 1ul in
  let t6 = trace () in
  reset ();
  let n = named 0ul in
  let m = named 5ul in
  let t7 = trace () in
  if U32.eq a 1ul && U32.eq b 2ul && U32.eq c 3ul && U32.eq t1 123ul
     && U32.eq d 4ul && U32.eq e 5ul && U32.eq f 6ul && U32.eq t2 456ul
     && U32.eq g 1ul && U32.eq h 2ul && U32.eq i 3ul && U32.eq t3 123ul
     && U32.eq t4 123ul && U32.eq t5 78ul
     && U32.eq p.px 1ul && U32.eq p.py 2ul && U32.eq q.px 1ul && U32.eq q.py 4ul
     && U32.eq t6 0ul
     && U32.eq n 1ul && U32.eq m 6ul && U32.eq t7 151ul
     && U32.eq (plain 1ul) 2ul
  then 0l else 1l
