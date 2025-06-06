module Bug3800
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

assume new val u32: Type0
assume new val u16: Type0
assume new val i16: Type0
assume new val i32: Type0

assume new val (<>.) (#t: eqtype) (a b: t): bool
assume new val (^.) (a b: u32): u32
assume new val ( &. ) #t: t -> t -> t
assume new val ( <<! ) #t (x: t) (s: i32): t

assume new val cast (x: u16): u32
assume new val mk_u32: int -> u32
assume new val mk_i16: int -> i16
assume new val mk_i32: int -> i32
assume new val mk_u16: int -> u16

[@@"opaque_to_smt"; expect_failure [19]]
let poly_mul (a b: u16) : u32 =
  let (v: u32):u32 = mk_u32 0 in
  let me:u32 = cast (a <: u16) <: u32 in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 0 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 0 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 1 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 1 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 2 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 2 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 3 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 3 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 4 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 4 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 5 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 5 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 6 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 6 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 7 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 7 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 8 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 8 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 9 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 9 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 10 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 10 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 11 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 11 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 12 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 12 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 13 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 13 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 14 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 14 <: u32) in
      v
    else v
  in
  let v:u32 =
    if mk_u16 0 <>. (b &. (mk_u16 1 <<! mk_i32 15 <: u16) <: u16)
    then
      let v:u32 = v ^. (me <<! mk_i32 15 <: u32) in
      v
    else v
  in
  v