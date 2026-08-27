open Prims
type signedness =
  | Unsigned 
  | Signed [@@deriving yojson,show]
let uu___is_Unsigned (projectee : signedness) : Prims.bool=
  match projectee with | Unsigned -> true | uu___ -> false
let uu___is_Signed (projectee : signedness) : Prims.bool=
  match projectee with | Signed -> true | uu___ -> false
type width =
  | Int8 
  | Int16 
  | Int32 
  | Int64 
  | Sizet [@@deriving yojson,show]
let uu___is_Int8 (projectee : width) : Prims.bool=
  match projectee with | Int8 -> true | uu___ -> false
let uu___is_Int16 (projectee : width) : Prims.bool=
  match projectee with | Int16 -> true | uu___ -> false
let uu___is_Int32 (projectee : width) : Prims.bool=
  match projectee with | Int32 -> true | uu___ -> false
let uu___is_Int64 (projectee : width) : Prims.bool=
  match projectee with | Int64 -> true | uu___ -> false
let uu___is_Sizet (projectee : width) : Prims.bool=
  match projectee with | Sizet -> true | uu___ -> false
type sconst =
  | Const_effect 
  | Const_unit 
  | Const_bool of Prims.bool 
  | Const_int of (Prims.int * FStar_IntegerLiteral.int_base) 
  | Const_machine_int of (Prims.int * FStar_IntegerLiteral.int_base *
  signedness * width) 
  | Const_char of FStar_Char.char 
  | Const_real of FStarC_Real.real 
  | Const_string of (Prims.string * FStarC_Range_Type.range) 
  | Const_range_of 
  | Const_set_range_of 
  | Const_range of FStarC_Range_Type.range 
  | Const_reify of FStarC_Ident.lid FStar_Pervasives_Native.option 
  | Const_reflect of FStarC_Ident.lid [@@deriving yojson,show]
let uu___is_Const_effect (projectee : sconst) : Prims.bool=
  match projectee with | Const_effect -> true | uu___ -> false
let uu___is_Const_unit (projectee : sconst) : Prims.bool=
  match projectee with | Const_unit -> true | uu___ -> false
let uu___is_Const_bool (projectee : sconst) : Prims.bool=
  match projectee with | Const_bool _0 -> true | uu___ -> false
let __proj__Const_bool__item___0 (projectee : sconst) : Prims.bool=
  match projectee with | Const_bool _0 -> _0
let uu___is_Const_int (projectee : sconst) : Prims.bool=
  match projectee with | Const_int _0 -> true | uu___ -> false
let __proj__Const_int__item___0 (projectee : sconst) :
  (Prims.int * FStar_IntegerLiteral.int_base)=
  match projectee with | Const_int _0 -> _0
let uu___is_Const_machine_int (projectee : sconst) : Prims.bool=
  match projectee with | Const_machine_int _0 -> true | uu___ -> false
let __proj__Const_machine_int__item___0 (projectee : sconst) :
  (Prims.int * FStar_IntegerLiteral.int_base * signedness * width)=
  match projectee with | Const_machine_int _0 -> _0
let uu___is_Const_char (projectee : sconst) : Prims.bool=
  match projectee with | Const_char _0 -> true | uu___ -> false
let __proj__Const_char__item___0 (projectee : sconst) : FStar_Char.char=
  match projectee with | Const_char _0 -> _0
let uu___is_Const_real (projectee : sconst) : Prims.bool=
  match projectee with | Const_real _0 -> true | uu___ -> false
let __proj__Const_real__item___0 (projectee : sconst) : FStarC_Real.real=
  match projectee with | Const_real _0 -> _0
let uu___is_Const_string (projectee : sconst) : Prims.bool=
  match projectee with | Const_string _0 -> true | uu___ -> false
let __proj__Const_string__item___0 (projectee : sconst) :
  (Prims.string * FStarC_Range_Type.range)=
  match projectee with | Const_string _0 -> _0
let uu___is_Const_range_of (projectee : sconst) : Prims.bool=
  match projectee with | Const_range_of -> true | uu___ -> false
let uu___is_Const_set_range_of (projectee : sconst) : Prims.bool=
  match projectee with | Const_set_range_of -> true | uu___ -> false
let uu___is_Const_range (projectee : sconst) : Prims.bool=
  match projectee with | Const_range _0 -> true | uu___ -> false
let __proj__Const_range__item___0 (projectee : sconst) :
  FStarC_Range_Type.range= match projectee with | Const_range _0 -> _0
let uu___is_Const_reify (projectee : sconst) : Prims.bool=
  match projectee with | Const_reify _0 -> true | uu___ -> false
let __proj__Const_reify__item___0 (projectee : sconst) :
  FStarC_Ident.lid FStar_Pervasives_Native.option=
  match projectee with | Const_reify _0 -> _0
let uu___is_Const_reflect (projectee : sconst) : Prims.bool=
  match projectee with | Const_reflect _0 -> true | uu___ -> false
let __proj__Const_reflect__item___0 (projectee : sconst) : FStarC_Ident.lid=
  match projectee with | Const_reflect _0 -> _0
let eq_const (c1 : sconst) (c2 : sconst) : Prims.bool=
  match (c1, c2) with
  | (Const_int (v1, uu___), Const_int (v2, uu___1)) -> v1 = v2
  | (Const_machine_int (v1, uu___, s1, w1), Const_machine_int
     (v2, uu___1, s2, w2)) -> ((v1 = v2) && (s1 = s2)) && (w1 = w2)
  | (Const_string (a, uu___), Const_string (b, uu___1)) -> a = b
  | (Const_real r1, Const_real r2) ->
      (FStarC_Real.cmp r1 r2) = FStarC_Order.Eq
  | (Const_reflect l1, Const_reflect l2) -> FStarC_Ident.lid_equals l1 l2
  | (Const_reify uu___, Const_reify uu___1) -> true
  | uu___ -> c1 = c2
let rec pow2 (x : Prims.int) : Prims.int=
  if x = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int 2) * (pow2 (x - Prims.int_one))
let bounds (signedness1 : signedness) (width1 : width) :
  (Prims.int * Prims.int)=
  let n =
    match width1 with
    | Int8 -> Prims.of_int 8
    | Int16 -> Prims.of_int 16
    | Int32 -> Prims.of_int 32
    | Int64 -> Prims.of_int 64
    | Sizet -> Prims.of_int 16 in
  let uu___ =
    match signedness1 with
    | Unsigned -> (Prims.int_zero, ((pow2 n) - Prims.int_one))
    | Signed ->
        let upper = pow2 (n - Prims.int_one) in
        ((- upper), (upper - Prims.int_one)) in
  match uu___ with | (lower, upper) -> (lower, upper)
let within_bounds (value : Prims.int) (signedness1 : signedness)
  (width1 : width) : Prims.bool=
  let uu___ = bounds signedness1 width1 in
  match uu___ with | (lower, upper) -> (lower <= value) && (value <= upper)
let digit_char (d : Prims.int) : Prims.string=
  if d = Prims.int_zero
  then "0"
  else
    if d = Prims.int_one
    then "1"
    else
      if d = (Prims.of_int 2)
      then "2"
      else
        if d = (Prims.of_int 3)
        then "3"
        else
          if d = (Prims.of_int 4)
          then "4"
          else
            if d = (Prims.of_int 5)
            then "5"
            else
              if d = (Prims.of_int 6)
              then "6"
              else
                if d = (Prims.of_int 7)
                then "7"
                else
                  if d = (Prims.of_int 8)
                  then "8"
                  else
                    if d = (Prims.of_int 9)
                    then "9"
                    else
                      if d = (Prims.of_int 10)
                      then "a"
                      else
                        if d = (Prims.of_int 11)
                        then "b"
                        else
                          if d = (Prims.of_int 12)
                          then "c"
                          else
                            if d = (Prims.of_int 13)
                            then "d"
                            else if d = (Prims.of_int 14) then "e" else "f"
let string_of_int_literal (i : Prims.int) (b : FStar_IntegerLiteral.int_base)
  : Prims.string=
  match b with
  | FStar_IntegerLiteral.Dec -> Prims.string_of_int i
  | uu___ ->
      let uu___1 =
        match b with
        | FStar_IntegerLiteral.Hex -> ((Prims.of_int 16), "0x")
        | FStar_IntegerLiteral.Oct -> ((Prims.of_int 8), "0o")
        | FStar_IntegerLiteral.Bin -> ((Prims.of_int 2), "0b")
        | FStar_IntegerLiteral.Dec -> ((Prims.of_int 10), "") in
      (match uu___1 with
       | (base, prefix) ->
           let uu___2 = if i < Prims.int_zero then ("-", (- i)) else ("", i) in
           (match uu___2 with
            | (sign, n) ->
                let rec go n1 acc =
                  if n1 = Prims.int_zero
                  then acc
                  else
                    go (n1 / base)
                      (Prims.strcat (digit_char ((mod) n1 base)) acc) in
                Prims.strcat sign
                  (Prims.strcat prefix
                     (if n = Prims.int_zero then "0" else go n ""))))
let parse_int_literal (s : Prims.string) :
  (Prims.int * FStar_IntegerLiteral.int_base)=
  let s' =
    if FStarC_Util.starts_with s "-"
    then FStarC_Util.substring_from s Prims.int_one
    else s in
  let b =
    if (FStarC_Util.starts_with s' "0x") || (FStarC_Util.starts_with s' "0X")
    then FStar_IntegerLiteral.Hex
    else
      if
        (FStarC_Util.starts_with s' "0o") ||
          (FStarC_Util.starts_with s' "0O")
      then FStar_IntegerLiteral.Oct
      else
        if
          (FStarC_Util.starts_with s' "0b") ||
            (FStarC_Util.starts_with s' "0B")
        then FStar_IntegerLiteral.Bin
        else FStar_IntegerLiteral.Dec in
  let uu___ = FStarC_Util.int_of_string s in (uu___, b)
