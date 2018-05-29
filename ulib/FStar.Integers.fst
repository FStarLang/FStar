module FStar.Integers

#set-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 0 --max_fuel 0"
irreducible
private
let mark_for_norm = ()

unfold
let norm (#a:Type) (x:a) = norm [iota; delta_attr mark_for_norm] x

type signedness =
  | Signed
  | Unsigned

type width =
  | W8
  | W16
  | W31
  | W32
  | W63
  | W64
  | W128
  | Winfinite

let fixed_width = w:width{w <> Winfinite}

[@mark_for_norm]
let join (s1, w1) (s2, w2) =
  match w1, w2 with
  | Winfinite, Winfinite ->
    //Any operation on infinite width types
    //uses the full range of mathematical integers
    //This is to support the existing behavior from Prims
    //of the basic arithmetic operations being defined on Prims.int
    Some (Signed, Winfinite)

  | _ ->
    //No other heterogeneous combinations are supported
    if (s1, w1) = (s2, w2)
    then Some (s1, w1)
    else None

[@mark_for_norm]
let nat_of_width = function
  | W8   -> Some 8
  | W16  -> Some 16
  | W31  -> Some 31
  | W32  -> Some 32
  | W63  -> Some 63
  | W64  -> Some 64
  | W128 -> Some 128
  | Winfinite -> None

[@mark_for_norm]
let nat_of_fixed_width (w:fixed_width) =
  match nat_of_width w with
  | Some v -> v

[@mark_for_norm]
inline_for_extraction
let int_t (s:signedness) (w:width) : Tot Type0 =
  match s, w with
  | Unsigned, Winfinite -> nat
  | Unsigned, W8 -> FStar.UInt8.t
  | Unsigned, W16 -> FStar.UInt16.t
  | Unsigned, W31 -> FStar.UInt31.t
  | Unsigned, W32 -> FStar.UInt32.t
  | Unsigned, W63 -> FStar.UInt63.t
  | Unsigned, W64 -> FStar.UInt64.t
  | Unsigned, W128 -> FStar.UInt128.t
  | Signed, Winfinite -> int
  | Signed, W8 -> FStar.Int8.t
  | Signed, W16 -> FStar.Int16.t
  | Signed, W31 -> FStar.Int31.t
  | Signed, W32 -> FStar.Int32.t
  | Signed, W63 -> FStar.Int63.t
  | Signed, W64 -> FStar.Int64.t
  | Signed, W128 -> FStar.Int128.t

[@mark_for_norm]
inline_for_extraction
let join_types #s1 #w1 (x:int_t s1 w1)
               #s2 #w2 (y:int_t s2 w2{Some? (join (s1, w1) (s2, w2))}) : Type0 =
  let Some (s, w) = join (s1, w1) (s2, w2) in
  int_t s w

[@mark_for_norm]
let within_bounds' (s:signedness) (w:width) (x:int) =
  match s, nat_of_width w with
  | Signed,   None   -> True
  | Unsigned, None   -> b2t (x >= 0)
  | Signed  , Some n -> FStar.Int.size x n
  | Unsigned, Some n -> FStar.UInt.size x n

unfold
let within_bounds s w x = norm (within_bounds' s w x)

unfold
let join_within_bounds #s1 #w1 (_:int_t s1 w1)
                       #s2 #w2 (_:int_t s2 w2)
                       (x:Prims.int) =
  norm (match join (s1, w1) (s2, w2) with
        | None -> False
        | Some (s, w) -> within_bounds' s w x)

[@mark_for_norm]
let v (#s:signedness) (#w:width) (x:int_t s w)
  : Tot (y:int_t Signed Winfinite{within_bounds s w y})
  = match s with
    | Unsigned ->
      (match w with
       | Winfinite -> (x <: nat)
       | W8 -> FStar.UInt8.v x
       | W16 -> FStar.UInt16.v x
       | W31 -> FStar.UInt31.v x
       | W32 -> FStar.UInt32.v x
       | W63 -> FStar.UInt63.v x
       | W64 -> FStar.UInt64.v x
       | W128 -> FStar.UInt128.v x)
    | Signed ->
      (match w with
       | Winfinite -> x
       | W8 -> FStar.Int8.v x
       | W16 -> FStar.Int16.v x
       | W31 -> FStar.Int31.v x
       | W32 -> FStar.Int32.v x
       | W63 -> FStar.Int63.v x
       | W64 -> FStar.Int64.v x
       | W128 -> FStar.Int128.v x)

[@mark_for_norm]
let u   (#s:signedness) (#w:width)
        (x:int_t Signed Winfinite{within_bounds s w x})
  : Tot (y:int_t s w{norm (v x == v y)})
  = match s with
    | Unsigned ->
      (match w with
       | Winfinite -> (x <: nat)
       | W8 -> FStar.UInt8.uint_to_t x
       | W16 -> FStar.UInt16.uint_to_t x
       | W31 -> FStar.UInt31.uint_to_t x
       | W32 -> FStar.UInt32.uint_to_t x
       | W63 -> FStar.UInt63.uint_to_t x
       | W64 -> FStar.UInt64.uint_to_t x
       | W128 -> FStar.UInt128.uint_to_t x)
    | Signed ->
      (match w with
       | Winfinite -> x
       | W8 -> FStar.Int8.int_to_t x
       | W16 -> FStar.Int16.int_to_t x
       | W31 -> FStar.Int31.int_to_t x
       | W32 -> FStar.Int32.int_to_t x
       | W63 -> FStar.Int63.int_to_t x
       | W64 -> FStar.Int64.int_to_t x
       | W128 -> FStar.Int128.int_to_t x)

abstract
let cast (#s:signedness) (#s':signedness)
         (#w:width)      (#w':width)
         (from:int_t s w{within_bounds s' w' (v from)})
   : Tot (to:int_t s' w'{norm (v from == v to)})
   = u (v from)

[@mark_for_norm]
unfold
let ( + ) (#s1:signedness) (#w1:width)
          (x:int_t s1 w1)
          (#s2:signedness) (#w2:width)
          (y:int_t s2 w2{join_within_bounds x y (v x + v y)})
  : Tot   (z:join_types x y{norm (v z == v x + v y)})
  = match join (s1, w1) (s2, w2) with
    | _, Winfinite -> x + y
    | Unsigned, W8   -> FStar.UInt8.(x +^ y)
    | Unsigned, W16  -> FStar.UInt16.(x +^ y)
    | Unsigned, W31  -> FStar.UInt31.(x +^ y)
    | Unsigned, W32  -> FStar.UInt32.(x +^ y)
    | Unsigned, W63  -> FStar.UInt63.(x +^ y)
    | Unsigned, W64  -> FStar.UInt64.(x +^ y)
    | Unsigned, W128 -> FStar.UInt128.(x +^ y)
    | Signed, W8   -> FStar.Int8.(x +^ y)
    | Signed, W16  -> FStar.Int16.(x +^ y)
    | Signed, W31  -> FStar.Int31.(x +^ y)
    | Signed, W32  -> FStar.Int32.(x +^ y)
    | Signed, W63  -> FStar.Int63.(x +^ y)
    | Signed, W64  -> FStar.Int64.(x +^ y)
    | Signed, W128 -> FStar.Int128.(x +^ y)

[@mark_for_norm]
unfold
let ( +? ) (#w:width)
           (x:int_t Unsigned w)
           (y:int_t Unsigned w)
  : Tot    (z:int_t Unsigned w{within_bounds Unsigned w (v x + v y) ==> norm (v z == v x + v y)})
  = match w with
    | Winfinite -> x + y
    | W8 -> FStar.UInt8.(x +?^ y)
    | W16 -> FStar.UInt16.(x +?^ y)
    | W31 -> FStar.UInt31.(x +?^ y)
    | W32 -> FStar.UInt32.(x +?^ y)
    | W63 -> FStar.UInt63.(x +?^ y)
    | W64 -> FStar.UInt64.(x +?^ y)
    | W128 -> FStar.UInt128.(x +?^ y)

[@mark_for_norm]
let modulo (s:signedness) (x:int) (y:pos{s=Signed ==> y%2=0}) =
  match s with
  | Unsigned ->  x % y
  | _ -> FStar.Int.(x @% y)

[@mark_for_norm]
unfold
let ( +% ) (#w:fixed_width)
           (x:int_t Unsigned w)
           (y:int_t Unsigned w)
  : Tot    (z:int_t Unsigned w{norm (v z == modulo Unsigned (v x + v y) (pow2 (nat_of_fixed_width w)))})
  = match w with
    | W8 -> FStar.UInt8.(x +%^ y)
    | W16 -> FStar.UInt16.(x +%^ y)
    | W31 -> FStar.UInt31.(x +%^ y)
    | W32 -> FStar.UInt32.(x +%^ y)
    | W63 -> FStar.UInt63.(x +%^ y)
    | W64 -> FStar.UInt64.(x +%^ y)
    | W128 -> FStar.UInt128.(x +%^ y)

[@mark_for_norm]
unfold
let op_Subtraction (#s:signedness) (#w:width)
                   (x:int_t s w)
                   (y:int_t s w{within_bounds s w (v x - v y)})
    : Tot          (z:int_t s w{norm (v z == v x - v y)})
  = match s, w with
    | _, Winfinite -> x - y
    | Unsigned, W8 -> FStar.UInt8.(x -^ y)
    | Unsigned, W16 -> FStar.UInt16.(x -^ y)
    | Unsigned, W31 -> FStar.UInt31.(x -^ y)
    | Unsigned, W32 -> FStar.UInt32.(x -^ y)
    | Unsigned, W63 -> FStar.UInt63.(x -^ y)
    | Unsigned, W64 -> FStar.UInt64.(x -^ y)
    | Unsigned, W128 -> FStar.UInt128.(x -^ y)
    | Signed, W8 -> FStar.Int8.(x -^ y)
    | Signed, W16 -> FStar.Int16.(x -^ y)
    | Signed, W31 -> FStar.Int31.(x -^ y)
    | Signed, W32 -> FStar.Int32.(x -^ y)
    | Signed, W63 -> FStar.Int63.(x -^ y)
    | Signed, W64 -> FStar.Int64.(x -^ y)
    | Signed, W128 -> FStar.Int128.(x -^ y)

[@mark_for_norm]
unfold
let op_Subtraction_Question
        (#w:width)
        (x:int_t Unsigned w)
        (y:int_t Unsigned w)
  : Tot (z:int_t Unsigned w{within_bounds Unsigned w (v x - v y) ==> norm (v z == v x - v y)})
  = match w with
    | Winfinite -> if v x - v y >= 0 then x - y else 0
    | W8 -> FStar.UInt8.(x -?^ y)
    | W16 -> FStar.UInt16.(x -?^ y)
    | W31 -> FStar.UInt31.(x -?^ y)
    | W32 -> FStar.UInt32.(x -?^ y)
    | W63 -> FStar.UInt63.(x -?^ y)
    | W64 -> FStar.UInt64.(x -?^ y)
    | W128 -> FStar.UInt128.(x -?^ y)

[@mark_for_norm]
unfold
let op_Subtraction_Percent
         (#w:fixed_width)
         (x:int_t Unsigned w)
         (y:int_t Unsigned w)
  : Tot  (z:int_t Unsigned w{norm (v z == modulo Unsigned (v x - v y) (pow2 (nat_of_fixed_width w)))})
  = match w with
    | W8 -> FStar.UInt8.(x -%^ y)
    | W16 -> FStar.UInt16.(x -%^ y)
    | W31 -> FStar.UInt31.(x -%^ y)
    | W32 -> FStar.UInt32.(x -%^ y)
    | W63 -> FStar.UInt63.(x -%^ y)
    | W64 -> FStar.UInt64.(x -%^ y)
    | W128 -> FStar.UInt128.(x -%^ y)

open FStar.Mul

[@mark_for_norm]
unfold
let ( * ) (#s:signedness) (#w:width{w <> W128})
          (x:int_t s w)
          (y:int_t s w{within_bounds s w (v x * v y)})
  : Tot   (z:int_t s w{norm (v z == v x * v y)})
  = match s, w with
    | _, Winfinite -> x * y
    | Unsigned, W8 -> FStar.UInt8.(x *^ y)
    | Unsigned, W16 -> FStar.UInt16.(x *^ y)
    | Unsigned, W31 -> FStar.UInt31.(x *^ y)
    | Unsigned, W32 -> FStar.UInt32.(x *^ y)
    | Unsigned, W63 -> FStar.UInt63.(x *^ y)
    | Unsigned, W64 -> FStar.UInt64.(x *^ y)
    | Signed, W8 -> FStar.Int8.(x *^ y)
    | Signed, W16 -> FStar.Int16.(x *^ y)
    | Signed, W31 -> FStar.Int31.(x *^ y)
    | Signed, W32 -> FStar.Int32.(x *^ y)
    | Signed, W63 -> FStar.Int63.(x *^ y)
    | Signed, W64 -> FStar.Int64.(x *^ y)
    | Signed, W128 -> FStar.Int128.(x *^ y)

[@mark_for_norm]
unfold
let ( *? ) (#w:width{w <> W128})
           (x:int_t Unsigned w)
           (y:int_t Unsigned w)
  : Tot    (z:int_t Unsigned w{within_bounds Unsigned w (v x * v y) ==> norm (v z == v x * v y)})
  = match w with
    | Winfinite -> x * y
    | W8 -> FStar.UInt8.(x *?^ y)
    | W16 -> FStar.UInt16.(x *?^ y)
    | W31 -> FStar.UInt31.(x *?^ y)
    | W32 -> FStar.UInt32.(x *?^ y)
    | W63 -> FStar.UInt63.(x *?^ y)
    | W64 -> FStar.UInt64.(x *?^ y)

[@mark_for_norm]
unfold
let ( *% ) (#w:fixed_width{w <> W128})
           (x:int_t Unsigned w)
           (y:int_t Unsigned w)
  : Tot    (z:int_t Unsigned w{norm (v z == modulo Unsigned (v x * v y) (pow2 (nat_of_fixed_width w)))})
  = match w with
    | W8 -> FStar.UInt8.(x *%^ y)
    | W16 -> FStar.UInt16.(x *%^ y)
    | W31 -> FStar.UInt31.(x *%^ y)
    | W32 -> FStar.UInt32.(x *%^ y)
    | W63 -> FStar.UInt63.(x *%^ y)
    | W64 -> FStar.UInt64.(x *%^ y)

[@mark_for_norm]
inline_for_extraction
let nat        = int_t Unsigned Winfinite

[@mark_for_norm]
inline_for_extraction
let uint_8   = int_t Unsigned W8

[@mark_for_norm]
inline_for_extraction
let uint_16  = int_t Unsigned W16

[@mark_for_norm]
inline_for_extraction
let uint_31  = int_t Unsigned W31

[@mark_for_norm]
inline_for_extraction
let uint_32  = int_t Unsigned W32

[@mark_for_norm]
inline_for_extraction
let uint_63  = int_t Unsigned W63

[@mark_for_norm]
inline_for_extraction
let uint_64  = int_t Unsigned W64

[@mark_for_norm]
inline_for_extraction
let int       = int_t Signed Winfinite

[@mark_for_norm]
inline_for_extraction
let int_8   = int_t Signed W8

[@mark_for_norm]
inline_for_extraction
let int_16  = int_t Signed W16

[@mark_for_norm]
inline_for_extraction
let int_31  = int_t Signed W31

[@mark_for_norm]
inline_for_extraction
let int_32  = int_t Signed W32

[@mark_for_norm]
inline_for_extraction
let int_63  = int_t Signed W63

[@mark_for_norm]
inline_for_extraction
let int_64  = int_t Signed W64

[@mark_for_norm]
inline_for_extraction
let int_128 = int_t Signed W128

[@mark_for_norm]
unfold
let ok (#s:signedness) (#w:width)
       (op:(int_t Signed Winfinite
          -> int_t Signed Winfinite
          -> int_t Signed Winfinite))
       (x:int_t s w)
       (y:int_t s w)
   = within_bounds s w (op (v x) (v y))
////////////////////////////////////////////////////////////////////////////////
//Test
////////////////////////////////////////////////////////////////////////////////
let f_int (x:int) (y:int) = x + y
let f_nat (x:nat) (y:nat) = x + y
let f_uint_8 (x:uint_8) (y:uint_8{ok (+) x y}) = x + y
let f_int_16 (x:int_16) (y:int_16{ok (+) x y}) = x + y
let g (x:uint_32) (y:uint_32{ok ( * ) y y /\ ok (+) x (y * y)}) = x + y * y
let h (x:Prims.nat) (y:Prims.nat): nat  = u x + u y
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
