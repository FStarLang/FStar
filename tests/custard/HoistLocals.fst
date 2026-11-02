module HoistLocals

open FStar.All
module U32 = FStar.UInt32

[@@custard_extern "hl_tick"; custard_c_header "HoistLocals_stubs.h"]
assume val tick : U32.t -> ML U32.t

[@@custard_extern "hl_trace"; custard_c_header "HoistLocals_stubs.h"]
assume val trace : unit -> ML U32.t

[@@custard_extern "hl_reset"; custard_c_header "HoistLocals_stubs.h"]
assume val reset : unit -> ML unit

let uint32_inhabited : nonempty U32.t = nonempty_intro 0ul

let first : U32.t =
  let x = tick 1ul in
  if U32.eq x 1ul then tick 2ul else tick 9ul

let second : U32.t = tick 3ul

let choose (b:bool) : ML U32.t =
  if b then
    let value = tick 2ul in U32.add_mod value 1ul
  else
    let value = tick 3ul in U32.add_mod value 1ul

let short_or (b:bool) : ML bool =
  b || (let x = tick 9ul in U32.eq x 9ul)

let short_and (b:bool) : ML bool =
  b && (let x = tick 9ul in U32.eq x 9ul)

noeq type item = | Number : U32.t -> item | Missing : item

let matched (x:item) : ML U32.t =
  match x with
  | Number value -> let y = tick value in U32.add_mod y 1ul
  | Missing -> tick 8ul

let indirect (f:U32.t -> ML U32.t) (x:U32.t) : ML U32.t = f x

[@@custard_c_ifdef "defined(HOIST_LEFT)"]
assume val left : bool

[@@custard_extern "hl_left_t"; custard_c_header "HoistLocals_stubs.h"]
assume val left_t : Type0
[@@custard_extern "hl_right_t"; custard_c_header "HoistLocals_stubs.h"]
assume val right_t : Type0
[@@custard_extern "hl_make_left"; custard_c_header "HoistLocals_stubs.h"]
assume val make_left : unit -> ML left_t
[@@custard_extern "hl_make_right"; custard_c_header "HoistLocals_stubs.h"]
assume val make_right : unit -> ML right_t
[@@custard_extern "hl_get_left"; custard_c_header "HoistLocals_stubs.h"]
assume val get_left : left_t -> ML U32.t
[@@custard_extern "hl_get_right"; custard_c_header "HoistLocals_stubs.h"]
assume val get_right : right_t -> ML U32.t

let configured () : ML U32.t =
  if left then
    let x = make_left () in get_left x
  else
    let x = make_right () in get_right x

let main () : ML FStar.Int32.t =
  let initial = trace () in
  reset ();
  let a = choose false in
  let b = choose true in
  let c = short_or true in
  let d = short_and false in
  let e = matched (Number 4ul) in
  let f = indirect tick 5ul in
  let g = configured () in
  let final = trace () in
  if U32.eq first 2ul && U32.eq second 3ul && U32.eq initial 123ul
     && U32.eq a 4ul && U32.eq b 3ul && c && not d
     && U32.eq e 5ul && U32.eq f 5ul && U32.eq g 4ul
     && U32.eq final 3245ul
  then 0l else 1l
