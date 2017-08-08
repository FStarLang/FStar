module FStar.Integers

#set-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 0 --max_fuel 0"

type signed =
  | Signed
  | Unsigned

let int_t (s:signed) (n:nat) : Tot Type0 =
  match s, n with
  | Unsigned, 0 -> nat
  | Unsigned, 8 -> FStar.UInt8.t
  | Unsigned, 16 -> FStar.UInt16.t
  | Unsigned, 31 -> FStar.UInt31.t
  | Unsigned, 32 -> FStar.UInt32.t
  | Unsigned, 63 -> FStar.UInt63.t
  | Unsigned, 64 -> FStar.UInt64.t
  | Signed, 0 -> int
  | Signed, 8 -> FStar.Int8.t
  | Signed, 16 -> FStar.Int16.t
  | Signed, 31 -> FStar.Int31.t
  | Signed, 32 -> FStar.Int32.t
  | Signed, 63 -> FStar.Int63.t
  | Signed, 64 -> FStar.Int64.t
  | Signed, 128 -> FStar.Int128.t
  | _ -> False

let size (x:int) (n:nat) (s:signed) =
  match s, n with
  | _, 0 -> True
  | Unsigned, n -> FStar.UInt.size x n
  | Signed, n -> FStar.Int.size x n

let v (#s:signed) (#n:nat) (x:int_t s n) : Tot (y:int_t Signed 0{size y n s}) =
  match s with
  | Unsigned ->
    (match n with
    | 0 -> (x <: nat)
    | 8 -> FStar.UInt8.v x
    | 16 -> FStar.UInt16.v x
    | 31 -> FStar.UInt31.v x
    | 32 -> FStar.UInt32.v x
    | 63 -> FStar.UInt63.v x
    | 64 -> FStar.UInt64.v x)
  | Signed ->
    (match n with
    | 0 -> x
    | 8 -> FStar.Int8.v x
    | 16 -> FStar.Int16.v x
    | 31 -> FStar.Int31.v x
    | 32 -> FStar.Int32.v x
    | 63 -> FStar.Int63.v x
    | 64 -> FStar.Int64.v x
    | 128 -> FStar.Int128.v x)

let ok (s:signed) (n:nat) (x:int) =
  match s, n with
  | Unsigned, 0 -> b2t (x >= 0)
  | Unsigned, _ -> FStar.UInt.size x n
  | Signed, 0 -> True
  | Signed, _ -> FStar.Int.size x n

unfold let op_Plus (#s:signed) (#n:nat) (x:int_t s n) (y:int_t s n{ok s n (v x + v y)})
  : Tot (z:int_t s n{v z = v x + v y})
  = match s, n with
    | _, 0 -> x + y
    | Unsigned, 8 -> FStar.UInt8.(x +^ y)
    | Unsigned, 16 -> FStar.UInt16.(x +^ y)
    | Unsigned, 31 -> FStar.UInt31.(x +^ y)
    | Unsigned, 32 -> FStar.UInt32.(x +^ y)
    | Unsigned, 63 -> FStar.UInt63.(x +^ y)
    | Unsigned, 64 -> FStar.UInt64.(x +^ y)
    | Signed, 8 -> FStar.Int8.(x +^ y)
    | Signed, 16 -> FStar.Int16.(x +^ y)
    | Signed, 31 -> FStar.Int31.(x +^ y)
    | Signed, 32 -> FStar.Int32.(x +^ y)
    | Signed, 63 -> FStar.Int63.(x +^ y)
    | Signed, 64 -> FStar.Int64.(x +^ y)
    | Signed, 128 -> FStar.Int128.(x +^ y)

unfold let op_Plus_Question (#n:nat) (x:int_t Unsigned n) (y:int_t Unsigned n)
  : Tot (z:int_t Unsigned n{ok Unsigned n (v x + v y) ==> v z = v x + v y})
  = match n with
    | 0 -> x + y
    | 8 -> FStar.UInt8.(x +?^ y)
    | 16 -> FStar.UInt16.(x +?^ y)
    | 31 -> FStar.UInt31.(x +?^ y)
    | 32 -> FStar.UInt32.(x +?^ y)
    | 63 -> FStar.UInt63.(x +?^ y)
    | 64 -> FStar.UInt64.(x +?^ y)

let modulo (s:signed) (x:int) (y:pos{s=Signed ==> y%2=0}) =
  match s with
  | Unsigned ->  x % y
  | _ -> FStar.Int.(x @% y)

#reset-options "--z3rlimit 5 --initial_fuel 1 --max_fuel 1"

unfold let op_Plus_Percent (#n:pos) (x:int_t Unsigned n) (y:int_t Unsigned n)
  : Tot (z:int_t Unsigned n{v z = modulo Unsigned (v x + v y) (pow2 n)})
  = match n with
    | 8 -> FStar.UInt8.(x +%^ y)
    | 16 -> FStar.UInt16.(x +%^ y)
    | 31 -> FStar.UInt31.(x +%^ y)
    | 32 -> FStar.UInt32.(x +%^ y)
    | 63 -> FStar.UInt63.(x +%^ y)
    | 64 -> FStar.UInt64.(x +%^ y)

#reset-options "--z3rlimit 5"

unfold let op_Subtraction (#s:signed) (#n:nat) (x:int_t s n) (y:int_t s n{ok s n (v x - v y)})
  : Tot (z:int_t s n{v z = v x - v y})
  = match s, n with
    | _, 0 -> x - y
    | Unsigned, 8 -> FStar.UInt8.(x -^ y)
    | Unsigned, 16 -> FStar.UInt16.(x -^ y)
    | Unsigned, 31 -> FStar.UInt31.(x -^ y)
    | Unsigned, 32 -> FStar.UInt32.(x -^ y)
    | Unsigned, 63 -> FStar.UInt63.(x -^ y)
    | Unsigned, 64 -> FStar.UInt64.(x -^ y)
    | Signed, 8 -> FStar.Int8.(x -^ y)
    | Signed, 16 -> FStar.Int16.(x -^ y)
    | Signed, 31 -> FStar.Int31.(x -^ y)
    | Signed, 32 -> FStar.Int32.(x -^ y)
    | Signed, 63 -> FStar.Int63.(x -^ y)
    | Signed, 64 -> FStar.Int64.(x -^ y)
    | Signed, 128 -> FStar.Int128.(x -^ y)

unfold let op_Subtraction_Question (#n:nat) (x:int_t Unsigned n) (y:int_t Unsigned n)
  : Tot (z:int_t Unsigned n{ok Unsigned n (v x - v y) ==> v z = v x - v y})
  = match n with
    | 0 -> if v x - v y >= 0 then x - y else 0
    | 8 -> FStar.UInt8.(x -?^ y)
    | 16 -> FStar.UInt16.(x -?^ y)
    | 31 -> FStar.UInt31.(x -?^ y)
    | 32 -> FStar.UInt32.(x -?^ y)
    | 63 -> FStar.UInt63.(x -?^ y)
    | 64 -> FStar.UInt64.(x -?^ y)

#reset-options "--z3rlimit 20"

unfold let op_Subtraction_Percent (#n:pos) (x:int_t Unsigned n) (y:int_t Unsigned n)
  : Tot (z:int_t Unsigned n{v z = modulo Unsigned (v x - v y) (pow2 n)})
  = match n with
    | 8 -> FStar.UInt8.(x -%^ y)
    | 16 -> FStar.UInt16.(x -%^ y)
    | 31 -> FStar.UInt31.(x -%^ y)
    | 32 -> FStar.UInt32.(x -%^ y)
    | 63 -> FStar.UInt63.(x -%^ y)
    | 64 -> FStar.UInt64.(x -%^ y)

#reset-options "--z3rlimit 5"

open FStar.Mul

unfold let op_Star (#s:signed) (#n:nat) (x:int_t s n) (y:int_t s n{ok s n (v x * v y)})
  : Tot (z:int_t s n{v z = v x * v y})
  = match s, n with
    | _, 0 -> x * y
    | Unsigned, 8 -> FStar.UInt8.(x *^ y)
    | Unsigned, 16 -> FStar.UInt16.(x *^ y)
    | Unsigned, 31 -> FStar.UInt31.(x *^ y)
    | Unsigned, 32 -> FStar.UInt32.(x *^ y)
    | Unsigned, 63 -> FStar.UInt63.(x *^ y)
    | Unsigned, 64 -> FStar.UInt64.(x *^ y)
    | Signed, 8 -> FStar.Int8.(x *^ y)
    | Signed, 16 -> FStar.Int16.(x *^ y)
    | Signed, 31 -> FStar.Int31.(x *^ y)
    | Signed, 32 -> FStar.Int32.(x *^ y)
    | Signed, 63 -> FStar.Int63.(x *^ y)
    | Signed, 64 -> FStar.Int64.(x *^ y)
    | Signed, 128 -> FStar.Int128.(x *^ y)

#reset-options "--z3rlimit 20"

unfold let op_Star_Question (#n:nat) (x:int_t Unsigned n) (y:int_t Unsigned n)
  : Tot (z:int_t Unsigned n{ok Unsigned n (v x * v y) ==> v z = v x * v y})
  = match n with
    | 0 -> x * y
    | 8 -> FStar.UInt8.(x *?^ y)
    | 16 -> FStar.UInt16.(x *?^ y)
    | 31 -> FStar.UInt31.(x *?^ y)
    | 32 -> FStar.UInt32.(x *?^ y)
    | 63 -> FStar.UInt63.(x *?^ y)
    | 64 -> FStar.UInt64.(x *?^ y)

#reset-options "--z3rlimit 5"

unfold let op_Star_Percent (#n:pos) (x:int_t Unsigned n) (y:int_t Unsigned n)
  : Tot (z:int_t Unsigned n{v z = modulo Unsigned (v x * v y) (pow2 n)})
  = match n with
    | 8 -> FStar.UInt8.(x *%^ y)
    | 16 -> FStar.UInt16.(x *%^ y)
    | 31 -> FStar.UInt31.(x *%^ y)
    | 32 -> FStar.UInt32.(x *%^ y)
    | 63 -> FStar.UInt63.(x *%^ y)
    | 64 -> FStar.UInt64.(x *%^ y)


unfold let nat      = int_t Unsigned 0
unfold let uint_8   = int_t Unsigned 8
unfold let uint_16  = int_t Unsigned 16
unfold let uint_31  = int_t Unsigned 31
unfold let uint_32  = int_t Unsigned 32
unfold let uint_63  = int_t Unsigned 63
unfold let uint_64  = int_t Unsigned 64

unfold let int      = int_t Signed 0
unfold let int_8   = int_t Signed 8
unfold let int_16  = int_t Signed 16
unfold let int_31  = int_t Signed 31
unfold let int_32  = int_t Signed 32
unfold let int_63  = int_t Signed 63
unfold let int_64  = int_t Signed 64
unfold let int_128 = int_t Signed 128
let ok_for (#s:signed) (#n:nat) ($x:int_t s n) (i:int) = ok s n i
////////////////////////////////////////////////////////////////////////////////
//Test
////////////////////////////////////////////////////////////////////////////////
let f_int (x:int) (y:int) = x + y
let f_nat (x:nat) (y:nat) = x + y
let f_uint_8 (x:uint_8) (y:uint_8{ok_for x (v x + v y)}) = x + y
let f_int_16 (x:int_16) (y:int_16{ok_for x (v x + v y)}) = x + y
let g (x:uint_32) (y:uint_32{ok_for x (v y * v y) /\ ok_for x (v x + v y * v y)}) = x + y * y

(* TODO: A bit boring ... *)
(* let op_Slash_Hat = div *)
(* let op_Percent_Hat = rem *)
(* let op_Hat_Hat = logxor *)
(* let op_Amp_Hat = logand *)
(* let op_Bar_Hat = logor *)
(* let op_Less_Less_Hat = shift_left *)
(* let op_Greater_Greater_Hat = shift_right *)
(* let op_Equals_Hat = eq *)
(* let op_Greater_Hat = gt *)
(* let op_Greater_Equals_Hat = gte *)
(* let op_Less_Hat = lt *)
(* let op_Less_Equals_Hat = lte *)
