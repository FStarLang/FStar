open Prims
type name =
  {
  ns: Prims.string Prims.list ;
  id: Prims.string ;
  spec: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkname__item__ns (projectee : name) : Prims.string Prims.list=
  match projectee with | { ns; id; spec;_} -> ns
let __proj__Mkname__item__id (projectee : name) : Prims.string=
  match projectee with | { ns; id; spec;_} -> id
let __proj__Mkname__item__spec (projectee : name) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { ns; id; spec;_} -> spec
let mangled_name (n : name) : Prims.string=
  let base = FStarC_String.concat "_" (FStarC_List.op_At n.ns [n.id]) in
  match n.spec with
  | FStar_Pervasives_Native.None -> base
  | FStar_Pervasives_Native.Some s -> Prims.strcat base (Prims.strcat "__" s)
let string_of_name (n : name) : Prims.string=
  let base = FStarC_String.concat "." (FStarC_List.op_At n.ns [n.id]) in
  match n.spec with
  | FStar_Pervasives_Native.None -> base
  | FStar_Pervasives_Native.Some s -> Prims.strcat base (Prims.strcat "@" s)
let uniq (base : Prims.string) (i : Prims.int) : Prims.string=
  let uu___ =
    let uu___1 = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
    Prims.strcat "#" uu___1 in
  Prims.strcat base uu___
let base_name (s : Prims.string) : Prims.string=
  match FStarC_String.split [35] s with | b::uu___::uu___1 -> b | uu___ -> s
type eff =
  | E_Ghost 
  | E_Pure 
  | E_Impure 
let uu___is_E_Ghost (projectee : eff) : Prims.bool=
  match projectee with | E_Ghost -> true | uu___ -> false
let uu___is_E_Pure (projectee : eff) : Prims.bool=
  match projectee with | E_Pure -> true | uu___ -> false
let uu___is_E_Impure (projectee : eff) : Prims.bool=
  match projectee with | E_Impure -> true | uu___ -> false
let eff_rank (e : eff) : Prims.int=
  match e with
  | E_Ghost -> Prims.int_zero
  | E_Pure -> Prims.int_one
  | E_Impure -> Prims.of_int 2
let join_eff (e1 : eff) (e2 : eff) : eff=
  if (eff_rank e1) >= (eff_rank e2) then e1 else e2
let is_pure (e : eff) : Prims.bool=
  match e with | E_Ghost -> true | E_Pure -> true | E_Impure -> false
type iwidth =
  | W8 
  | W16 
  | W32 
  | W64 
  | W128 
  | WSizet 
let uu___is_W8 (projectee : iwidth) : Prims.bool=
  match projectee with | W8 -> true | uu___ -> false
let uu___is_W16 (projectee : iwidth) : Prims.bool=
  match projectee with | W16 -> true | uu___ -> false
let uu___is_W32 (projectee : iwidth) : Prims.bool=
  match projectee with | W32 -> true | uu___ -> false
let uu___is_W64 (projectee : iwidth) : Prims.bool=
  match projectee with | W64 -> true | uu___ -> false
let uu___is_W128 (projectee : iwidth) : Prims.bool=
  match projectee with | W128 -> true | uu___ -> false
let uu___is_WSizet (projectee : iwidth) : Prims.bool=
  match projectee with | WSizet -> true | uu___ -> false
let rec strip_zeros (m : Prims.int) (e : Prims.int) :
  (Prims.int * Prims.int)=
  if (m <> Prims.int_zero) && (((mod) m (Prims.of_int 10)) = Prims.int_zero)
  then strip_zeros (m / (Prims.of_int 10)) (e + Prims.int_one)
  else (m, e)
let iwidth_of_width (w : FStarC_Const.width) : iwidth=
  match w with
  | FStarC_Const.Int8 -> W8
  | FStarC_Const.Int16 -> W16
  | FStarC_Const.Int32 -> W32
  | FStarC_Const.Int64 -> W64
  | FStarC_Const.Sizet -> WSizet
let width_bits (w : iwidth) : Prims.int=
  match w with
  | W8 -> Prims.of_int 8
  | W16 -> Prims.of_int 16
  | W32 -> Prims.of_int 32
  | W64 -> Prims.of_int 64
  | W128 -> Prims.of_int 128
  | WSizet -> Prims.of_int 64
type fwidth =
  | Float32 
  | Float64 
  | Float16 
  | BFloat16 
let uu___is_Float32 (projectee : fwidth) : Prims.bool=
  match projectee with | Float32 -> true | uu___ -> false
let uu___is_Float64 (projectee : fwidth) : Prims.bool=
  match projectee with | Float64 -> true | uu___ -> false
let uu___is_Float16 (projectee : fwidth) : Prims.bool=
  match projectee with | Float16 -> true | uu___ -> false
let uu___is_BFloat16 (projectee : fwidth) : Prims.bool=
  match projectee with | BFloat16 -> true | uu___ -> false
type float_lit =
  | FLNum of (Prims.bool * FStarC_Real.real) 
  | FLNan 
  | FLInf of Prims.bool 
let uu___is_FLNum (projectee : float_lit) : Prims.bool=
  match projectee with | FLNum _0 -> true | uu___ -> false
let __proj__FLNum__item___0 (projectee : float_lit) :
  (Prims.bool * FStarC_Real.real)= match projectee with | FLNum _0 -> _0
let uu___is_FLNan (projectee : float_lit) : Prims.bool=
  match projectee with | FLNan -> true | uu___ -> false
let uu___is_FLInf (projectee : float_lit) : Prims.bool=
  match projectee with | FLInf _0 -> true | uu___ -> false
let __proj__FLInf__item___0 (projectee : float_lit) : Prims.bool=
  match projectee with | FLInf _0 -> _0
type constant =
  | CUnit 
  | CBool of Prims.bool 
  | CInt of (Prims.int * FStar_IntegerLiteral.int_base *
  (FStarC_Const.signedness * iwidth) FStar_Pervasives_Native.option) 
  | CFloat of (float_lit * fwidth) 
  | CChar of FStarC_BaseTypes.char 
  | CString of Prims.string 
let uu___is_CUnit (projectee : constant) : Prims.bool=
  match projectee with | CUnit -> true | uu___ -> false
let uu___is_CBool (projectee : constant) : Prims.bool=
  match projectee with | CBool _0 -> true | uu___ -> false
let __proj__CBool__item___0 (projectee : constant) : Prims.bool=
  match projectee with | CBool _0 -> _0
let uu___is_CInt (projectee : constant) : Prims.bool=
  match projectee with | CInt _0 -> true | uu___ -> false
let __proj__CInt__item___0 (projectee : constant) :
  (Prims.int * FStar_IntegerLiteral.int_base * (FStarC_Const.signedness *
    iwidth) FStar_Pervasives_Native.option)=
  match projectee with | CInt _0 -> _0
let uu___is_CFloat (projectee : constant) : Prims.bool=
  match projectee with | CFloat _0 -> true | uu___ -> false
let __proj__CFloat__item___0 (projectee : constant) : (float_lit * fwidth)=
  match projectee with | CFloat _0 -> _0
let uu___is_CChar (projectee : constant) : Prims.bool=
  match projectee with | CChar _0 -> true | uu___ -> false
let __proj__CChar__item___0 (projectee : constant) : FStarC_BaseTypes.char=
  match projectee with | CChar _0 -> _0
let uu___is_CString (projectee : constant) : Prims.bool=
  match projectee with | CString _0 -> true | uu___ -> false
let __proj__CString__item___0 (projectee : constant) : Prims.string=
  match projectee with | CString _0 -> _0
type cty =
  | TVar of Prims.string 
  | TInt of (FStarC_Const.signedness * iwidth) 
  | TFloat of fwidth 
  | TArrow of (cty * eff * cty) 
  | TApp of (name * cty Prims.list) 
  | TConst of constant 
  | TBuf of cty 
  | TInline of cty 
  | TRef of cty 
  | TExn 
  | TTuple of cty Prims.list 
  | TUnit 
  | TAny 
let uu___is_TVar (projectee : cty) : Prims.bool=
  match projectee with | TVar _0 -> true | uu___ -> false
let __proj__TVar__item___0 (projectee : cty) : Prims.string=
  match projectee with | TVar _0 -> _0
let uu___is_TInt (projectee : cty) : Prims.bool=
  match projectee with | TInt _0 -> true | uu___ -> false
let __proj__TInt__item___0 (projectee : cty) :
  (FStarC_Const.signedness * iwidth)= match projectee with | TInt _0 -> _0
let uu___is_TFloat (projectee : cty) : Prims.bool=
  match projectee with | TFloat _0 -> true | uu___ -> false
let __proj__TFloat__item___0 (projectee : cty) : fwidth=
  match projectee with | TFloat _0 -> _0
let uu___is_TArrow (projectee : cty) : Prims.bool=
  match projectee with | TArrow _0 -> true | uu___ -> false
let __proj__TArrow__item___0 (projectee : cty) : (cty * eff * cty)=
  match projectee with | TArrow _0 -> _0
let uu___is_TApp (projectee : cty) : Prims.bool=
  match projectee with | TApp _0 -> true | uu___ -> false
let __proj__TApp__item___0 (projectee : cty) : (name * cty Prims.list)=
  match projectee with | TApp _0 -> _0
let uu___is_TConst (projectee : cty) : Prims.bool=
  match projectee with | TConst _0 -> true | uu___ -> false
let __proj__TConst__item___0 (projectee : cty) : constant=
  match projectee with | TConst _0 -> _0
let uu___is_TBuf (projectee : cty) : Prims.bool=
  match projectee with | TBuf _0 -> true | uu___ -> false
let __proj__TBuf__item___0 (projectee : cty) : cty=
  match projectee with | TBuf _0 -> _0
let uu___is_TInline (projectee : cty) : Prims.bool=
  match projectee with | TInline _0 -> true | uu___ -> false
let __proj__TInline__item___0 (projectee : cty) : cty=
  match projectee with | TInline _0 -> _0
let uu___is_TRef (projectee : cty) : Prims.bool=
  match projectee with | TRef _0 -> true | uu___ -> false
let __proj__TRef__item___0 (projectee : cty) : cty=
  match projectee with | TRef _0 -> _0
let uu___is_TExn (projectee : cty) : Prims.bool=
  match projectee with | TExn -> true | uu___ -> false
let uu___is_TTuple (projectee : cty) : Prims.bool=
  match projectee with | TTuple _0 -> true | uu___ -> false
let __proj__TTuple__item___0 (projectee : cty) : cty Prims.list=
  match projectee with | TTuple _0 -> _0
let uu___is_TUnit (projectee : cty) : Prims.bool=
  match projectee with | TUnit -> true | uu___ -> false
let uu___is_TAny (projectee : cty) : Prims.bool=
  match projectee with | TAny -> true | uu___ -> false
type tmpl_piece =
  | TP_lit of Prims.string 
  | TP_arg of Prims.int 
let uu___is_TP_lit (projectee : tmpl_piece) : Prims.bool=
  match projectee with | TP_lit _0 -> true | uu___ -> false
let __proj__TP_lit__item___0 (projectee : tmpl_piece) : Prims.string=
  match projectee with | TP_lit _0 -> _0
let uu___is_TP_arg (projectee : tmpl_piece) : Prims.bool=
  match projectee with | TP_arg _0 -> true | uu___ -> false
let __proj__TP_arg__item___0 (projectee : tmpl_piece) : Prims.int=
  match projectee with | TP_arg _0 -> _0
let template_of_string (s : Prims.string) : tmpl_piece Prims.list=
  let cs = FStarC_String.list_of_string s in
  let flush acc out =
    match acc with
    | [] -> out
    | uu___ -> (TP_lit (FStarC_String.string_of_list (FStarC_List.rev acc)))
        :: out in
  let rec go cs1 acc out =
    match cs1 with
    | [] -> FStarC_List.rev (flush acc out)
    | 123::123::rest -> go rest (123 :: acc) out
    | 123::rest ->
        let rec digits cs2 ds =
          match cs2 with
          | 125::rest1 ->
              (match ds with
               | [] -> FStar_Pervasives_Native.None
               | uu___ ->
                   let n =
                     FStarC_List.fold_left
                       (fun acc1 d ->
                          (acc1 * (Prims.of_int 10)) +
                            ((FStarC_Util.int_of_char d) - (Prims.of_int 48)))
                       Prims.int_zero (FStarC_List.rev ds) in
                   FStar_Pervasives_Native.Some (n, rest1))
          | c::rest1 when
              ((FStarC_Util.int_of_char c) >= (Prims.of_int 48)) &&
                ((FStarC_Util.int_of_char c) <= (Prims.of_int 57))
              -> digits rest1 (c :: ds)
          | uu___ -> FStar_Pervasives_Native.None in
        let uu___ = digits rest [] in
        (match uu___ with
         | FStar_Pervasives_Native.Some (n, rest') ->
             go rest' [] ((TP_arg n) :: (flush acc out))
         | FStar_Pervasives_Native.None -> go rest (123 :: acc) out)
    | c::rest -> go rest (c :: acc) out in
  go cs [] []
let is_template (ps : tmpl_piece Prims.list) : Prims.bool=
  FStarC_List.existsb uu___is_TP_arg ps
let fwidth_to_string (fw : fwidth) : Prims.string=
  match fw with
  | Float32 -> "f32"
  | Float64 -> "f64"
  | Float16 -> "f16"
  | BFloat16 -> "bf16"
let float_lit_to_string (f : float_lit) : Prims.string=
  match f with
  | FLNan -> "nan"
  | FLInf neg -> Prims.strcat (if neg then "-" else "") "inf"
  | FLNum (neg, mag) ->
      let sign = if neg then "-" else "" in
      let m = FStarC_Real.mantissa mag in
      let e = FStarC_Real.exponent mag in
      let plain = FStarC_Real.to_string mag in
      if
        (e = Prims.int_zero) &&
          ((FStarC_String.length plain) > (Prims.of_int 24))
      then
        let uu___ = strip_zeros m e in
        (match uu___ with
         | (m1, e1) ->
             Prims.strcat sign
               (Prims.strcat (Prims.string_of_int m1)
                  (if e1 = Prims.int_zero
                   then ".0"
                   else Prims.strcat "e" (Prims.string_of_int e1))))
      else Prims.strcat sign plain
let float_lit_of_string (s : Prims.string) :
  float_lit FStar_Pervasives_Native.option=
  match s with
  | "nan" -> FStar_Pervasives_Native.Some FLNan
  | "inf" -> FStar_Pervasives_Native.Some (FLInf false)
  | "infinity" -> FStar_Pervasives_Native.Some (FLInf false)
  | "+inf" -> FStar_Pervasives_Native.Some (FLInf false)
  | "+infinity" -> FStar_Pervasives_Native.Some (FLInf false)
  | "-inf" -> FStar_Pervasives_Native.Some (FLInf true)
  | "-infinity" -> FStar_Pervasives_Native.Some (FLInf true)
  | uu___ ->
      let cs = FStarC_String.list_of_string s in
      let is_digit c =
        let n = FStarC_Util.int_of_char c in
        (n >= (Prims.of_int 48)) && (n <= (Prims.of_int 57)) in
      let rec digits cs1 =
        match cs1 with
        | c::cs' when is_digit c ->
            let uu___1 = digits cs' in
            (match uu___1 with | (ds, rest) -> ((c :: ds), rest))
        | uu___1 -> ([], cs1) in
      let rec value acc ds =
        match ds with
        | [] -> acc
        | c::ds1 ->
            value
              ((acc * (Prims.of_int 10)) +
                 ((FStarC_Util.int_of_char c) - (Prims.of_int 48))) ds1 in
      let value1 ds = value Prims.int_zero ds in
      let uu___1 =
        match cs with
        | 45::cs1 -> (true, cs1)
        | 43::cs1 -> (false, cs1)
        | uu___2 -> (false, cs) in
      (match uu___1 with
       | (neg, cs1) ->
           let uu___2 = digits cs1 in
           (match uu___2 with
            | (ipart, cs2) ->
                let uu___3 =
                  match cs2 with
                  | 46::cs3 ->
                      let uu___4 = digits cs3 in
                      (match uu___4 with | (fs, cs4) -> (fs, cs4))
                  | uu___4 -> ([], cs2) in
                (match uu___3 with
                 | (fpart, cs3) ->
                     if
                       (match ipart with | [] -> true | uu___4 -> false) &&
                         ((match fpart with | [] -> true | uu___4 -> false))
                     then FStar_Pervasives_Native.None
                     else
                       (let uu___4 =
                          match cs3 with
                          | c::cs4 when (c = 101) || (c = 69) ->
                              let uu___5 =
                                match cs4 with
                                | 45::cs5 -> (true, cs5)
                                | 43::cs5 -> (false, cs5)
                                | uu___6 -> (false, cs4) in
                              (match uu___5 with
                               | (eneg, cs5) ->
                                   let uu___6 = digits cs5 in
                                   (match uu___6 with
                                    | (ds, cs6) ->
                                        if
                                          (match ds with
                                           | [] -> true
                                           | uu___7 -> false)
                                        then
                                          (FStar_Pervasives_Native.None, cs6)
                                        else
                                          ((FStar_Pervasives_Native.Some
                                              (if eneg
                                               then - (value1 ds)
                                               else value1 ds)), cs6)))
                          | uu___5 ->
                              ((FStar_Pervasives_Native.Some Prims.int_zero),
                                cs3) in
                        match uu___4 with
                        | (expo, cs4) ->
                            (match (expo, cs4) with
                             | (FStar_Pervasives_Native.Some expo1, []) ->
                                 let m =
                                   value1 (FStarC_List.op_At ipart fpart) in
                                 FStar_Pervasives_Native.Some
                                   (FLNum
                                      (neg,
                                        (FStarC_Real.mk m
                                           (expo1 -
                                              (FStarC_List.length fpart)))))
                             | uu___5 -> FStar_Pervasives_Native.None)))))
let significand_bits (fw : fwidth) : Prims.int=
  match fw with
  | Float32 -> Prims.of_int 24
  | Float64 -> Prims.of_int 53
  | Float16 -> Prims.of_int 11
  | BFloat16 -> Prims.of_int 8
let rec fits_in_bits (n : Prims.nat) (bits : Prims.nat) : Prims.bool=
  if n = Prims.int_zero
  then true
  else
    if bits = Prims.int_zero
    then false
    else fits_in_bits (n / (Prims.of_int 2)) (bits - Prims.int_one)
let rec odd_part (n : Prims.nat) : Prims.nat=
  if (n = Prims.int_zero) || (((mod) n (Prims.of_int 2)) = Prims.int_one)
  then n
  else odd_part (n / (Prims.of_int 2))
let float_lit_of_int (fw : fwidth) (n : Prims.int) :
  float_lit FStar_Pervasives_Native.option=
  let a = if n < Prims.int_zero then - n else n in
  if fits_in_bits (odd_part a) (significand_bits fw)
  then
    FStar_Pervasives_Native.Some
      (FLNum ((n < Prims.int_zero), (FStarC_Real.mk a Prims.int_zero)))
  else FStar_Pervasives_Native.None
let int_lit_to_string (v : Prims.int) (b : FStar_IntegerLiteral.int_base) :
  Prims.string= FStarC_Const.string_of_int_literal v b
let rec oct_digits (n : Prims.int) (acc : Prims.string) : Prims.string=
  if n <= Prims.int_zero
  then acc
  else
    oct_digits (n / (Prims.of_int 8))
      (Prims.strcat (Prims.string_of_int ((mod) n (Prims.of_int 8))) acc)
let c_int_lit_to_string (v : Prims.int) (b : FStar_IntegerLiteral.int_base) :
  Prims.string=
  match b with
  | FStar_IntegerLiteral.Oct ->
      if v = Prims.int_zero
      then "0"
      else
        if v < Prims.int_zero
        then Prims.strcat "-0" (oct_digits (- v) "")
        else Prims.strcat "0" (oct_digits v "")
  | FStar_IntegerLiteral.Bin ->
      FStarC_Const.string_of_int_literal v FStar_IntegerLiteral.Dec
  | uu___ -> FStarC_Const.string_of_int_literal v b
let const_eq (c1 : constant) (c2 : constant) : Prims.bool=
  match (c1, c2) with
  | (CInt (v1, uu___, sw1), CInt (v2, uu___1, sw2)) ->
      (v1 = v2) && (sw1 = sw2)
  | uu___ -> c1 = c2
type pat =
  | PWild 
  | PVar of Prims.string 
  | PConst of constant 
  | PCtor of (name * pat Prims.list) 
  | PRecord of (name * (Prims.string * pat) Prims.list) 
  | PTuple of pat Prims.list 
  | POr of pat Prims.list 
let uu___is_PWild (projectee : pat) : Prims.bool=
  match projectee with | PWild -> true | uu___ -> false
let uu___is_PVar (projectee : pat) : Prims.bool=
  match projectee with | PVar _0 -> true | uu___ -> false
let __proj__PVar__item___0 (projectee : pat) : Prims.string=
  match projectee with | PVar _0 -> _0
let uu___is_PConst (projectee : pat) : Prims.bool=
  match projectee with | PConst _0 -> true | uu___ -> false
let __proj__PConst__item___0 (projectee : pat) : constant=
  match projectee with | PConst _0 -> _0
let uu___is_PCtor (projectee : pat) : Prims.bool=
  match projectee with | PCtor _0 -> true | uu___ -> false
let __proj__PCtor__item___0 (projectee : pat) : (name * pat Prims.list)=
  match projectee with | PCtor _0 -> _0
let uu___is_PRecord (projectee : pat) : Prims.bool=
  match projectee with | PRecord _0 -> true | uu___ -> false
let __proj__PRecord__item___0 (projectee : pat) :
  (name * (Prims.string * pat) Prims.list)=
  match projectee with | PRecord _0 -> _0
let uu___is_PTuple (projectee : pat) : Prims.bool=
  match projectee with | PTuple _0 -> true | uu___ -> false
let __proj__PTuple__item___0 (projectee : pat) : pat Prims.list=
  match projectee with | PTuple _0 -> _0
let uu___is_POr (projectee : pat) : Prims.bool=
  match projectee with | POr _0 -> true | uu___ -> false
let __proj__POr__item___0 (projectee : pat) : pat Prims.list=
  match projectee with | POr _0 -> _0
type binder = {
  b_name: Prims.string ;
  b_ty: cty }
let __proj__Mkbinder__item__b_name (projectee : binder) : Prims.string=
  match projectee with | { b_name; b_ty;_} -> b_name
let __proj__Mkbinder__item__b_ty (projectee : binder) : cty=
  match projectee with | { b_name; b_ty;_} -> b_ty
type lifetime =
  | LStack 
  | LHeap 
let uu___is_LStack (projectee : lifetime) : Prims.bool=
  match projectee with | LStack -> true | uu___ -> false
let uu___is_LHeap (projectee : lifetime) : Prims.bool=
  match projectee with | LHeap -> true | uu___ -> false
type op =
  | Add 
  | AddW 
  | Sub 
  | SubW 
  | Mult 
  | MultW 
  | Div 
  | DivW 
  | Mod 
  | BOr 
  | BAnd 
  | BXor 
  | BShiftL 
  | BShiftR 
  | BNot 
  | Eq 
  | Neq 
  | Lt 
  | Lte 
  | Gt 
  | Gte 
  | And 
  | Or 
  | Not 
  | BufCreate of lifetime 
  | BufRead 
  | BufWrite 
  | BufSub 
  | BufFree 
  | BufNull 
  | BufIsNull 
  | BufBlit 
  | BufLit 
  | BufUnconst 
  | Commented of (Prims.string * Prims.string) 
let uu___is_Add (projectee : op) : Prims.bool=
  match projectee with | Add -> true | uu___ -> false
let uu___is_AddW (projectee : op) : Prims.bool=
  match projectee with | AddW -> true | uu___ -> false
let uu___is_Sub (projectee : op) : Prims.bool=
  match projectee with | Sub -> true | uu___ -> false
let uu___is_SubW (projectee : op) : Prims.bool=
  match projectee with | SubW -> true | uu___ -> false
let uu___is_Mult (projectee : op) : Prims.bool=
  match projectee with | Mult -> true | uu___ -> false
let uu___is_MultW (projectee : op) : Prims.bool=
  match projectee with | MultW -> true | uu___ -> false
let uu___is_Div (projectee : op) : Prims.bool=
  match projectee with | Div -> true | uu___ -> false
let uu___is_DivW (projectee : op) : Prims.bool=
  match projectee with | DivW -> true | uu___ -> false
let uu___is_Mod (projectee : op) : Prims.bool=
  match projectee with | Mod -> true | uu___ -> false
let uu___is_BOr (projectee : op) : Prims.bool=
  match projectee with | BOr -> true | uu___ -> false
let uu___is_BAnd (projectee : op) : Prims.bool=
  match projectee with | BAnd -> true | uu___ -> false
let uu___is_BXor (projectee : op) : Prims.bool=
  match projectee with | BXor -> true | uu___ -> false
let uu___is_BShiftL (projectee : op) : Prims.bool=
  match projectee with | BShiftL -> true | uu___ -> false
let uu___is_BShiftR (projectee : op) : Prims.bool=
  match projectee with | BShiftR -> true | uu___ -> false
let uu___is_BNot (projectee : op) : Prims.bool=
  match projectee with | BNot -> true | uu___ -> false
let uu___is_Eq (projectee : op) : Prims.bool=
  match projectee with | Eq -> true | uu___ -> false
let uu___is_Neq (projectee : op) : Prims.bool=
  match projectee with | Neq -> true | uu___ -> false
let uu___is_Lt (projectee : op) : Prims.bool=
  match projectee with | Lt -> true | uu___ -> false
let uu___is_Lte (projectee : op) : Prims.bool=
  match projectee with | Lte -> true | uu___ -> false
let uu___is_Gt (projectee : op) : Prims.bool=
  match projectee with | Gt -> true | uu___ -> false
let uu___is_Gte (projectee : op) : Prims.bool=
  match projectee with | Gte -> true | uu___ -> false
let uu___is_And (projectee : op) : Prims.bool=
  match projectee with | And -> true | uu___ -> false
let uu___is_Or (projectee : op) : Prims.bool=
  match projectee with | Or -> true | uu___ -> false
let uu___is_Not (projectee : op) : Prims.bool=
  match projectee with | Not -> true | uu___ -> false
let uu___is_BufCreate (projectee : op) : Prims.bool=
  match projectee with | BufCreate _0 -> true | uu___ -> false
let __proj__BufCreate__item___0 (projectee : op) : lifetime=
  match projectee with | BufCreate _0 -> _0
let uu___is_BufRead (projectee : op) : Prims.bool=
  match projectee with | BufRead -> true | uu___ -> false
let uu___is_BufWrite (projectee : op) : Prims.bool=
  match projectee with | BufWrite -> true | uu___ -> false
let uu___is_BufSub (projectee : op) : Prims.bool=
  match projectee with | BufSub -> true | uu___ -> false
let uu___is_BufFree (projectee : op) : Prims.bool=
  match projectee with | BufFree -> true | uu___ -> false
let uu___is_BufNull (projectee : op) : Prims.bool=
  match projectee with | BufNull -> true | uu___ -> false
let uu___is_BufIsNull (projectee : op) : Prims.bool=
  match projectee with | BufIsNull -> true | uu___ -> false
let uu___is_BufBlit (projectee : op) : Prims.bool=
  match projectee with | BufBlit -> true | uu___ -> false
let uu___is_BufLit (projectee : op) : Prims.bool=
  match projectee with | BufLit -> true | uu___ -> false
let uu___is_BufUnconst (projectee : op) : Prims.bool=
  match projectee with | BufUnconst -> true | uu___ -> false
let uu___is_Commented (projectee : op) : Prims.bool=
  match projectee with | Commented _0 -> true | uu___ -> false
let __proj__Commented__item___0 (projectee : op) :
  (Prims.string * Prims.string)= match projectee with | Commented _0 -> _0
type prim_ty =
  | PInt of (FStarC_Const.signedness * iwidth) 
  | PFloat of fwidth 
let uu___is_PInt (projectee : prim_ty) : Prims.bool=
  match projectee with | PInt _0 -> true | uu___ -> false
let __proj__PInt__item___0 (projectee : prim_ty) :
  (FStarC_Const.signedness * iwidth)= match projectee with | PInt _0 -> _0
let uu___is_PFloat (projectee : prim_ty) : Prims.bool=
  match projectee with | PFloat _0 -> true | uu___ -> false
let __proj__PFloat__item___0 (projectee : prim_ty) : fwidth=
  match projectee with | PFloat _0 -> _0
type prim_op = {
  po_op: op ;
  po_ty: prim_ty FStar_Pervasives_Native.option }
let __proj__Mkprim_op__item__po_op (projectee : prim_op) : op=
  match projectee with | { po_op; po_ty;_} -> po_op
let __proj__Mkprim_op__item__po_ty (projectee : prim_op) :
  prim_ty FStar_Pervasives_Native.option=
  match projectee with | { po_op; po_ty;_} -> po_ty
let at_int_width (o : prim_op) : Prims.bool=
  match o.po_ty with
  | FStar_Pervasives_Native.Some (PInt uu___) -> true
  | uu___ -> false
type expr = {
  e: expr' ;
  ty: cty ;
  eff: eff }
and expr' =
  | EConst of constant 
  | EVar of Prims.string 
  | EQual of (name * cty Prims.list) 
  | ELet of (Prims.string * cty * expr * expr) 
  | EApp of (expr * expr Prims.list) 
  | EFun of (binder Prims.list * expr) 
  | EMatch of (expr * (pat * expr FStar_Pervasives_Native.option * expr)
  Prims.list) 
  | EIf of (expr * expr * expr) 
  | ESeq of (expr * expr) 
  | ECtor of (name * expr Prims.list) 
  | ETuple of expr Prims.list 
  | ERecord of (name * (Prims.string * expr) Prims.list) 
  | EProj of (expr * name * Prims.string) 
  | EDiscrim of (expr * name) 
  | ECoerce of (expr * cty) 
  | ECast of (expr * cty) 
  | EAny 
  | EAbort of Prims.string 
  | EOp of (prim_op * expr Prims.list) 
  | EWhile of (expr * expr) 
  | ERaise of expr 
  | ETry of (expr * (pat * expr FStar_Pervasives_Native.option * expr)
  Prims.list) 
let __proj__Mkexpr__item__e (projectee : expr) : expr'=
  match projectee with | { e; ty; eff = eff1;_} -> e
let __proj__Mkexpr__item__ty (projectee : expr) : cty=
  match projectee with | { e; ty; eff = eff1;_} -> ty
let __proj__Mkexpr__item__eff (projectee : expr) : eff=
  match projectee with | { e; ty; eff = eff1;_} -> eff1
let uu___is_EConst (projectee : expr') : Prims.bool=
  match projectee with | EConst _0 -> true | uu___ -> false
let __proj__EConst__item___0 (projectee : expr') : constant=
  match projectee with | EConst _0 -> _0
let uu___is_EVar (projectee : expr') : Prims.bool=
  match projectee with | EVar _0 -> true | uu___ -> false
let __proj__EVar__item___0 (projectee : expr') : Prims.string=
  match projectee with | EVar _0 -> _0
let uu___is_EQual (projectee : expr') : Prims.bool=
  match projectee with | EQual _0 -> true | uu___ -> false
let __proj__EQual__item___0 (projectee : expr') : (name * cty Prims.list)=
  match projectee with | EQual _0 -> _0
let uu___is_ELet (projectee : expr') : Prims.bool=
  match projectee with | ELet _0 -> true | uu___ -> false
let __proj__ELet__item___0 (projectee : expr') :
  (Prims.string * cty * expr * expr)= match projectee with | ELet _0 -> _0
let uu___is_EApp (projectee : expr') : Prims.bool=
  match projectee with | EApp _0 -> true | uu___ -> false
let __proj__EApp__item___0 (projectee : expr') : (expr * expr Prims.list)=
  match projectee with | EApp _0 -> _0
let uu___is_EFun (projectee : expr') : Prims.bool=
  match projectee with | EFun _0 -> true | uu___ -> false
let __proj__EFun__item___0 (projectee : expr') : (binder Prims.list * expr)=
  match projectee with | EFun _0 -> _0
let uu___is_EMatch (projectee : expr') : Prims.bool=
  match projectee with | EMatch _0 -> true | uu___ -> false
let __proj__EMatch__item___0 (projectee : expr') :
  (expr * (pat * expr FStar_Pervasives_Native.option * expr) Prims.list)=
  match projectee with | EMatch _0 -> _0
let uu___is_EIf (projectee : expr') : Prims.bool=
  match projectee with | EIf _0 -> true | uu___ -> false
let __proj__EIf__item___0 (projectee : expr') : (expr * expr * expr)=
  match projectee with | EIf _0 -> _0
let uu___is_ESeq (projectee : expr') : Prims.bool=
  match projectee with | ESeq _0 -> true | uu___ -> false
let __proj__ESeq__item___0 (projectee : expr') : (expr * expr)=
  match projectee with | ESeq _0 -> _0
let uu___is_ECtor (projectee : expr') : Prims.bool=
  match projectee with | ECtor _0 -> true | uu___ -> false
let __proj__ECtor__item___0 (projectee : expr') : (name * expr Prims.list)=
  match projectee with | ECtor _0 -> _0
let uu___is_ETuple (projectee : expr') : Prims.bool=
  match projectee with | ETuple _0 -> true | uu___ -> false
let __proj__ETuple__item___0 (projectee : expr') : expr Prims.list=
  match projectee with | ETuple _0 -> _0
let uu___is_ERecord (projectee : expr') : Prims.bool=
  match projectee with | ERecord _0 -> true | uu___ -> false
let __proj__ERecord__item___0 (projectee : expr') :
  (name * (Prims.string * expr) Prims.list)=
  match projectee with | ERecord _0 -> _0
let uu___is_EProj (projectee : expr') : Prims.bool=
  match projectee with | EProj _0 -> true | uu___ -> false
let __proj__EProj__item___0 (projectee : expr') :
  (expr * name * Prims.string)= match projectee with | EProj _0 -> _0
let uu___is_EDiscrim (projectee : expr') : Prims.bool=
  match projectee with | EDiscrim _0 -> true | uu___ -> false
let __proj__EDiscrim__item___0 (projectee : expr') : (expr * name)=
  match projectee with | EDiscrim _0 -> _0
let uu___is_ECoerce (projectee : expr') : Prims.bool=
  match projectee with | ECoerce _0 -> true | uu___ -> false
let __proj__ECoerce__item___0 (projectee : expr') : (expr * cty)=
  match projectee with | ECoerce _0 -> _0
let uu___is_ECast (projectee : expr') : Prims.bool=
  match projectee with | ECast _0 -> true | uu___ -> false
let __proj__ECast__item___0 (projectee : expr') : (expr * cty)=
  match projectee with | ECast _0 -> _0
let uu___is_EAny (projectee : expr') : Prims.bool=
  match projectee with | EAny -> true | uu___ -> false
let uu___is_EAbort (projectee : expr') : Prims.bool=
  match projectee with | EAbort _0 -> true | uu___ -> false
let __proj__EAbort__item___0 (projectee : expr') : Prims.string=
  match projectee with | EAbort _0 -> _0
let uu___is_EOp (projectee : expr') : Prims.bool=
  match projectee with | EOp _0 -> true | uu___ -> false
let __proj__EOp__item___0 (projectee : expr') : (prim_op * expr Prims.list)=
  match projectee with | EOp _0 -> _0
let uu___is_EWhile (projectee : expr') : Prims.bool=
  match projectee with | EWhile _0 -> true | uu___ -> false
let __proj__EWhile__item___0 (projectee : expr') : (expr * expr)=
  match projectee with | EWhile _0 -> _0
let uu___is_ERaise (projectee : expr') : Prims.bool=
  match projectee with | ERaise _0 -> true | uu___ -> false
let __proj__ERaise__item___0 (projectee : expr') : expr=
  match projectee with | ERaise _0 -> _0
let uu___is_ETry (projectee : expr') : Prims.bool=
  match projectee with | ETry _0 -> true | uu___ -> false
let __proj__ETry__item___0 (projectee : expr') :
  (expr * (pat * expr FStar_Pervasives_Native.option * expr) Prims.list)=
  match projectee with | ETry _0 -> _0
type branch = (pat * expr FStar_Pervasives_Native.option * expr)
type flag =
  | Rec of name Prims.list 
  | Private 
  | Root 
  | Entrypoint 
  | NoNewtype 
  | Inline 
  | Erased 
  | Comment of Prims.string 
  | Prologue of Prims.string 
  | Epilogue of Prims.string 
  | ClosurePrologue of (Prims.string * Prims.string) 
  | CMacro 
  | CReference 
  | CInline 
  | Realized 
  | Modelled 
  | Extern of (Prims.string FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option) 
  | SourceRecord 
  | Existential of (Prims.string * Prims.string) 
  | Imported of (Prims.string * Prims.string FStar_Pervasives_Native.option) 
let uu___is_Rec (projectee : flag) : Prims.bool=
  match projectee with | Rec _0 -> true | uu___ -> false
let __proj__Rec__item___0 (projectee : flag) : name Prims.list=
  match projectee with | Rec _0 -> _0
let uu___is_Private (projectee : flag) : Prims.bool=
  match projectee with | Private -> true | uu___ -> false
let uu___is_Root (projectee : flag) : Prims.bool=
  match projectee with | Root -> true | uu___ -> false
let uu___is_Entrypoint (projectee : flag) : Prims.bool=
  match projectee with | Entrypoint -> true | uu___ -> false
let uu___is_NoNewtype (projectee : flag) : Prims.bool=
  match projectee with | NoNewtype -> true | uu___ -> false
let uu___is_Inline (projectee : flag) : Prims.bool=
  match projectee with | Inline -> true | uu___ -> false
let uu___is_Erased (projectee : flag) : Prims.bool=
  match projectee with | Erased -> true | uu___ -> false
let uu___is_Comment (projectee : flag) : Prims.bool=
  match projectee with | Comment _0 -> true | uu___ -> false
let __proj__Comment__item___0 (projectee : flag) : Prims.string=
  match projectee with | Comment _0 -> _0
let uu___is_Prologue (projectee : flag) : Prims.bool=
  match projectee with | Prologue _0 -> true | uu___ -> false
let __proj__Prologue__item___0 (projectee : flag) : Prims.string=
  match projectee with | Prologue _0 -> _0
let uu___is_Epilogue (projectee : flag) : Prims.bool=
  match projectee with | Epilogue _0 -> true | uu___ -> false
let __proj__Epilogue__item___0 (projectee : flag) : Prims.string=
  match projectee with | Epilogue _0 -> _0
let uu___is_ClosurePrologue (projectee : flag) : Prims.bool=
  match projectee with | ClosurePrologue _0 -> true | uu___ -> false
let __proj__ClosurePrologue__item___0 (projectee : flag) :
  (Prims.string * Prims.string)=
  match projectee with | ClosurePrologue _0 -> _0
let uu___is_CMacro (projectee : flag) : Prims.bool=
  match projectee with | CMacro -> true | uu___ -> false
let uu___is_CReference (projectee : flag) : Prims.bool=
  match projectee with | CReference -> true | uu___ -> false
let uu___is_CInline (projectee : flag) : Prims.bool=
  match projectee with | CInline -> true | uu___ -> false
let uu___is_Realized (projectee : flag) : Prims.bool=
  match projectee with | Realized -> true | uu___ -> false
let uu___is_Modelled (projectee : flag) : Prims.bool=
  match projectee with | Modelled -> true | uu___ -> false
let uu___is_Extern (projectee : flag) : Prims.bool=
  match projectee with | Extern _0 -> true | uu___ -> false
let __proj__Extern__item___0 (projectee : flag) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option)=
  match projectee with | Extern _0 -> _0
let uu___is_SourceRecord (projectee : flag) : Prims.bool=
  match projectee with | SourceRecord -> true | uu___ -> false
let uu___is_Existential (projectee : flag) : Prims.bool=
  match projectee with | Existential _0 -> true | uu___ -> false
let __proj__Existential__item___0 (projectee : flag) :
  (Prims.string * Prims.string)= match projectee with | Existential _0 -> _0
let uu___is_Imported (projectee : flag) : Prims.bool=
  match projectee with | Imported _0 -> true | uu___ -> false
let __proj__Imported__item___0 (projectee : flag) :
  (Prims.string * Prims.string FStar_Pervasives_Native.option)=
  match projectee with | Imported _0 -> _0
type tydef =
  | TAbbrev of cty 
  | TRecord of (Prims.string * cty) Prims.list 
  | TVariant of (name * (Prims.string * cty) Prims.list) Prims.list 
  | TAbstract 
let uu___is_TAbbrev (projectee : tydef) : Prims.bool=
  match projectee with | TAbbrev _0 -> true | uu___ -> false
let __proj__TAbbrev__item___0 (projectee : tydef) : cty=
  match projectee with | TAbbrev _0 -> _0
let uu___is_TRecord (projectee : tydef) : Prims.bool=
  match projectee with | TRecord _0 -> true | uu___ -> false
let __proj__TRecord__item___0 (projectee : tydef) :
  (Prims.string * cty) Prims.list= match projectee with | TRecord _0 -> _0
let uu___is_TVariant (projectee : tydef) : Prims.bool=
  match projectee with | TVariant _0 -> true | uu___ -> false
let __proj__TVariant__item___0 (projectee : tydef) :
  (name * (Prims.string * cty) Prims.list) Prims.list=
  match projectee with | TVariant _0 -> _0
let uu___is_TAbstract (projectee : tydef) : Prims.bool=
  match projectee with | TAbstract -> true | uu___ -> false
type dtype =
  {
  dt_name: name ;
  dt_params: Prims.string Prims.list ;
  dt_body: tydef ;
  dt_flags: flag Prims.list }
let __proj__Mkdtype__item__dt_name (projectee : dtype) : name=
  match projectee with
  | { dt_name; dt_params; dt_body; dt_flags;_} -> dt_name
let __proj__Mkdtype__item__dt_params (projectee : dtype) :
  Prims.string Prims.list=
  match projectee with
  | { dt_name; dt_params; dt_body; dt_flags;_} -> dt_params
let __proj__Mkdtype__item__dt_body (projectee : dtype) : tydef=
  match projectee with
  | { dt_name; dt_params; dt_body; dt_flags;_} -> dt_body
let __proj__Mkdtype__item__dt_flags (projectee : dtype) : flag Prims.list=
  match projectee with
  | { dt_name; dt_params; dt_body; dt_flags;_} -> dt_flags
type dlet =
  {
  dl_name: name ;
  dl_typars: Prims.string Prims.list ;
  dl_binders: binder Prims.list ;
  dl_ret: cty ;
  dl_eff: eff ;
  dl_body: expr ;
  dl_flags: flag Prims.list }
let __proj__Mkdlet__item__dl_name (projectee : dlet) : name=
  match projectee with
  | { dl_name; dl_typars; dl_binders; dl_ret; dl_eff; dl_body; dl_flags;_} ->
      dl_name
let __proj__Mkdlet__item__dl_typars (projectee : dlet) :
  Prims.string Prims.list=
  match projectee with
  | { dl_name; dl_typars; dl_binders; dl_ret; dl_eff; dl_body; dl_flags;_} ->
      dl_typars
let __proj__Mkdlet__item__dl_binders (projectee : dlet) : binder Prims.list=
  match projectee with
  | { dl_name; dl_typars; dl_binders; dl_ret; dl_eff; dl_body; dl_flags;_} ->
      dl_binders
let __proj__Mkdlet__item__dl_ret (projectee : dlet) : cty=
  match projectee with
  | { dl_name; dl_typars; dl_binders; dl_ret; dl_eff; dl_body; dl_flags;_} ->
      dl_ret
let __proj__Mkdlet__item__dl_eff (projectee : dlet) : eff=
  match projectee with
  | { dl_name; dl_typars; dl_binders; dl_ret; dl_eff; dl_body; dl_flags;_} ->
      dl_eff
let __proj__Mkdlet__item__dl_body (projectee : dlet) : expr=
  match projectee with
  | { dl_name; dl_typars; dl_binders; dl_ret; dl_eff; dl_body; dl_flags;_} ->
      dl_body
let __proj__Mkdlet__item__dl_flags (projectee : dlet) : flag Prims.list=
  match projectee with
  | { dl_name; dl_typars; dl_binders; dl_ret; dl_eff; dl_body; dl_flags;_} ->
      dl_flags
type dexternal =
  {
  dx_name: name ;
  dx_typars: Prims.string Prims.list ;
  dx_ty: cty ;
  dx_target: Prims.string FStar_Pervasives_Native.option ;
  dx_header: Prims.string FStar_Pervasives_Native.option ;
  dx_flags: flag Prims.list }
let __proj__Mkdexternal__item__dx_name (projectee : dexternal) : name=
  match projectee with
  | { dx_name; dx_typars; dx_ty; dx_target; dx_header; dx_flags;_} -> dx_name
let __proj__Mkdexternal__item__dx_typars (projectee : dexternal) :
  Prims.string Prims.list=
  match projectee with
  | { dx_name; dx_typars; dx_ty; dx_target; dx_header; dx_flags;_} ->
      dx_typars
let __proj__Mkdexternal__item__dx_ty (projectee : dexternal) : cty=
  match projectee with
  | { dx_name; dx_typars; dx_ty; dx_target; dx_header; dx_flags;_} -> dx_ty
let __proj__Mkdexternal__item__dx_target (projectee : dexternal) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { dx_name; dx_typars; dx_ty; dx_target; dx_header; dx_flags;_} ->
      dx_target
let __proj__Mkdexternal__item__dx_header (projectee : dexternal) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { dx_name; dx_typars; dx_ty; dx_target; dx_header; dx_flags;_} ->
      dx_header
let __proj__Mkdexternal__item__dx_flags (projectee : dexternal) :
  flag Prims.list=
  match projectee with
  | { dx_name; dx_typars; dx_ty; dx_target; dx_header; dx_flags;_} ->
      dx_flags
type dexn =
  {
  de_name: name ;
  de_args: cty Prims.list ;
  de_flags: flag Prims.list }
let __proj__Mkdexn__item__de_name (projectee : dexn) : name=
  match projectee with | { de_name; de_args; de_flags;_} -> de_name
let __proj__Mkdexn__item__de_args (projectee : dexn) : cty Prims.list=
  match projectee with | { de_name; de_args; de_flags;_} -> de_args
let __proj__Mkdexn__item__de_flags (projectee : dexn) : flag Prims.list=
  match projectee with | { de_name; de_args; de_flags;_} -> de_flags
type decl =
  | DType of dtype 
  | DLet of dlet 
  | DExternal of dexternal 
  | DExn of dexn 
let uu___is_DType (projectee : decl) : Prims.bool=
  match projectee with | DType _0 -> true | uu___ -> false
let __proj__DType__item___0 (projectee : decl) : dtype=
  match projectee with | DType _0 -> _0
let uu___is_DLet (projectee : decl) : Prims.bool=
  match projectee with | DLet _0 -> true | uu___ -> false
let __proj__DLet__item___0 (projectee : decl) : dlet=
  match projectee with | DLet _0 -> _0
let uu___is_DExternal (projectee : decl) : Prims.bool=
  match projectee with | DExternal _0 -> true | uu___ -> false
let __proj__DExternal__item___0 (projectee : decl) : dexternal=
  match projectee with | DExternal _0 -> _0
let uu___is_DExn (projectee : decl) : Prims.bool=
  match projectee with | DExn _0 -> true | uu___ -> false
let __proj__DExn__item___0 (projectee : decl) : dexn=
  match projectee with | DExn _0 -> _0
type program = decl Prims.list
type slot =
  | S_erased 
  | S_at of Prims.int 
let uu___is_S_erased (projectee : slot) : Prims.bool=
  match projectee with | S_erased -> true | uu___ -> false
let uu___is_S_at (projectee : slot) : Prims.bool=
  match projectee with | S_at _0 -> true | uu___ -> false
let __proj__S_at__item___0 (projectee : slot) : Prims.int=
  match projectee with | S_at _0 -> _0
type ctor_layout =
  {
  cl_name: name ;
  cl_tag: Prims.int FStar_Pervasives_Native.option ;
  cl_slots: slot Prims.list ;
  cl_arity: Prims.int ;
  cl_fields: (Prims.string * cty) Prims.list }
let __proj__Mkctor_layout__item__cl_name (projectee : ctor_layout) : 
  name=
  match projectee with
  | { cl_name; cl_tag; cl_slots; cl_arity; cl_fields;_} -> cl_name
let __proj__Mkctor_layout__item__cl_tag (projectee : ctor_layout) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { cl_name; cl_tag; cl_slots; cl_arity; cl_fields;_} -> cl_tag
let __proj__Mkctor_layout__item__cl_slots (projectee : ctor_layout) :
  slot Prims.list=
  match projectee with
  | { cl_name; cl_tag; cl_slots; cl_arity; cl_fields;_} -> cl_slots
let __proj__Mkctor_layout__item__cl_arity (projectee : ctor_layout) :
  Prims.int=
  match projectee with
  | { cl_name; cl_tag; cl_slots; cl_arity; cl_fields;_} -> cl_arity
let __proj__Mkctor_layout__item__cl_fields (projectee : ctor_layout) :
  (Prims.string * cty) Prims.list=
  match projectee with
  | { cl_name; cl_tag; cl_slots; cl_arity; cl_fields;_} -> cl_fields
type newtype_layout =
  {
  nt_ctor: name ;
  nt_field: Prims.string ;
  nt_index: Prims.int ;
  nt_ty: cty }
let __proj__Mknewtype_layout__item__nt_ctor (projectee : newtype_layout) :
  name=
  match projectee with | { nt_ctor; nt_field; nt_index; nt_ty;_} -> nt_ctor
let __proj__Mknewtype_layout__item__nt_field (projectee : newtype_layout) :
  Prims.string=
  match projectee with | { nt_ctor; nt_field; nt_index; nt_ty;_} -> nt_field
let __proj__Mknewtype_layout__item__nt_index (projectee : newtype_layout) :
  Prims.int=
  match projectee with | { nt_ctor; nt_field; nt_index; nt_ty;_} -> nt_index
let __proj__Mknewtype_layout__item__nt_ty (projectee : newtype_layout) : 
  cty=
  match projectee with | { nt_ctor; nt_field; nt_index; nt_ty;_} -> nt_ty
type layout =
  | L_erased 
  | L_newtype of newtype_layout 
  | L_struct of ctor_layout Prims.list 
  | L_abbrev of cty 
  | L_opaque 
let uu___is_L_erased (projectee : layout) : Prims.bool=
  match projectee with | L_erased -> true | uu___ -> false
let uu___is_L_newtype (projectee : layout) : Prims.bool=
  match projectee with | L_newtype _0 -> true | uu___ -> false
let __proj__L_newtype__item___0 (projectee : layout) : newtype_layout=
  match projectee with | L_newtype _0 -> _0
let uu___is_L_struct (projectee : layout) : Prims.bool=
  match projectee with | L_struct _0 -> true | uu___ -> false
let __proj__L_struct__item___0 (projectee : layout) : ctor_layout Prims.list=
  match projectee with | L_struct _0 -> _0
let uu___is_L_abbrev (projectee : layout) : Prims.bool=
  match projectee with | L_abbrev _0 -> true | uu___ -> false
let __proj__L_abbrev__item___0 (projectee : layout) : cty=
  match projectee with | L_abbrev _0 -> _0
let uu___is_L_opaque (projectee : layout) : Prims.bool=
  match projectee with | L_opaque -> true | uu___ -> false
type expansion =
  {
  ex_ty: cty ;
  ex_type: name ;
  ex_ctor: name FStar_Pervasives_Native.option ;
  ex_src: (Prims.string * cty) Prims.list ;
  ex_dst: (Prims.string * cty) Prims.list }
let __proj__Mkexpansion__item__ex_ty (projectee : expansion) : cty=
  match projectee with
  | { ex_ty; ex_type; ex_ctor; ex_src; ex_dst;_} -> ex_ty
let __proj__Mkexpansion__item__ex_type (projectee : expansion) : name=
  match projectee with
  | { ex_ty; ex_type; ex_ctor; ex_src; ex_dst;_} -> ex_type
let __proj__Mkexpansion__item__ex_ctor (projectee : expansion) :
  name FStar_Pervasives_Native.option=
  match projectee with
  | { ex_ty; ex_type; ex_ctor; ex_src; ex_dst;_} -> ex_ctor
let __proj__Mkexpansion__item__ex_src (projectee : expansion) :
  (Prims.string * cty) Prims.list=
  match projectee with
  | { ex_ty; ex_type; ex_ctor; ex_src; ex_dst;_} -> ex_src
let __proj__Mkexpansion__item__ex_dst (projectee : expansion) :
  (Prims.string * cty) Prims.list=
  match projectee with
  | { ex_ty; ex_type; ex_ctor; ex_src; ex_dst;_} -> ex_dst
type fplan =
  (Prims.string * Prims.string * expansion FStar_Pervasives_Native.option)
    Prims.list
type type_info =
  {
  ti_erased: Prims.bool ;
  ti_layout: layout ;
  ti_ctors: ctor_layout Prims.list ;
  ti_record: Prims.bool ;
  ti_plans: (name * fplan) Prims.list }
let __proj__Mktype_info__item__ti_erased (projectee : type_info) :
  Prims.bool=
  match projectee with
  | { ti_erased; ti_layout; ti_ctors; ti_record; ti_plans;_} -> ti_erased
let __proj__Mktype_info__item__ti_layout (projectee : type_info) : layout=
  match projectee with
  | { ti_erased; ti_layout; ti_ctors; ti_record; ti_plans;_} -> ti_layout
let __proj__Mktype_info__item__ti_ctors (projectee : type_info) :
  ctor_layout Prims.list=
  match projectee with
  | { ti_erased; ti_layout; ti_ctors; ti_record; ti_plans;_} -> ti_ctors
let __proj__Mktype_info__item__ti_record (projectee : type_info) :
  Prims.bool=
  match projectee with
  | { ti_erased; ti_layout; ti_ctors; ti_record; ti_plans;_} -> ti_record
let __proj__Mktype_info__item__ti_plans (projectee : type_info) :
  (name * fplan) Prims.list=
  match projectee with
  | { ti_erased; ti_layout; ti_ctors; ti_record; ti_plans;_} -> ti_plans
type verdicts =
  {
  vd_records: name FStarC_SMap.t ;
  vd_plans: fplan FStarC_SMap.t }
let __proj__Mkverdicts__item__vd_records (projectee : verdicts) :
  name FStarC_SMap.t=
  match projectee with | { vd_records; vd_plans;_} -> vd_records
let __proj__Mkverdicts__item__vd_plans (projectee : verdicts) :
  fplan FStarC_SMap.t=
  match projectee with | { vd_records; vd_plans;_} -> vd_plans
let rec subst_cty (s : (Prims.string * cty) Prims.list) (c : cty) : cty=
  match c with
  | TVar v ->
      let uu___ =
        FStarC_List.tryFind
          (fun uu___1 -> match uu___1 with | (p, uu___2) -> p = v) s in
      (match uu___ with
       | FStar_Pervasives_Native.Some (uu___1, c') -> c'
       | FStar_Pervasives_Native.None -> c)
  | TArrow (a, e, b) ->
      let uu___ =
        let uu___1 = subst_cty s a in
        let uu___2 = subst_cty s b in (uu___1, e, uu___2) in
      TArrow uu___
  | TTuple cs -> let uu___ = FStarC_List.map (subst_cty s) cs in TTuple uu___
  | TBuf c1 -> let uu___ = subst_cty s c1 in TBuf uu___
  | TRef c1 -> let uu___ = subst_cty s c1 in TRef uu___
  | TInline c1 -> let uu___ = subst_cty s c1 in TInline uu___
  | TApp (n, args) ->
      let uu___ =
        let uu___1 = FStarC_List.map (subst_cty s) args in (n, uu___1) in
      TApp uu___
  | c1 -> c1
let mk (e : expr') (ty : cty) (eff1 : eff) : expr= { e; ty; eff = eff1 }
let unit_expr : expr= mk (EConst CUnit) TUnit E_Pure
let name_of_decl (d : decl) : name=
  match d with
  | DType t -> t.dt_name
  | DLet l -> l.dl_name
  | DExternal e -> e.dx_name
  | DExn e -> e.de_name
let extern_template_of_flags (fs : flag Prims.list) :
  tmpl_piece Prims.list FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.tryPick
      (fun f ->
         match f with
         | Extern (t, uu___1) -> t
         | uu___1 -> FStar_Pervasives_Native.None) fs in
  match uu___ with
  | FStar_Pervasives_Native.Some t ->
      let ps = template_of_string t in
      let uu___1 = is_template ps in
      if uu___1
      then FStar_Pervasives_Native.Some ps
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let decl_flags (d : decl) : flag Prims.list=
  match d with
  | DType t -> t.dt_flags
  | DLet l -> l.dl_flags
  | DExternal e -> e.dx_flags
  | DExn e -> e.de_flags
let has_flag (fs : flag Prims.list) (f : flag) : Prims.bool=
  FStarC_List.existsb (fun f' -> f' = f) fs
let rec type_names_of_cty (c : cty) : Prims.string Prims.list=
  match c with
  | TArrow (a, uu___, b) ->
      let uu___1 = type_names_of_cty a in
      let uu___2 = type_names_of_cty b in FStarC_List.op_At uu___1 uu___2
  | TTuple cs -> FStarC_List.collect type_names_of_cty cs
  | TBuf c1 -> type_names_of_cty c1
  | TRef c1 -> type_names_of_cty c1
  | TInline c1 -> type_names_of_cty c1
  | TApp (n, args) ->
      let uu___ = string_of_name n in
      let uu___1 = FStarC_List.collect type_names_of_cty args in uu___ ::
        uu___1
  | uu___ -> []
let type_names_of_decl (d : decl) : Prims.string Prims.list=
  match d with
  | DType t ->
      (match t.dt_body with
       | TAbbrev c -> type_names_of_cty c
       | TRecord fs ->
           FStarC_List.collect
             (fun uu___ ->
                match uu___ with | (uu___1, c) -> type_names_of_cty c) fs
       | TVariant cs ->
           FStarC_List.collect
             (fun uu___ ->
                match uu___ with
                | (uu___1, fs) ->
                    FStarC_List.collect
                      (fun uu___2 ->
                         match uu___2 with
                         | (uu___3, c) -> type_names_of_cty c) fs) cs
       | TAbstract -> [])
  | DLet l ->
      let uu___ =
        FStarC_List.collect (fun b -> type_names_of_cty b.b_ty) l.dl_binders in
      let uu___1 = type_names_of_cty l.dl_ret in
      FStarC_List.op_At uu___ uu___1
  | DExternal x -> type_names_of_cty x.dx_ty
  | DExn e -> FStarC_List.collect type_names_of_cty e.de_args
let imported_unit (d : decl) : Prims.string FStar_Pervasives_Native.option=
  FStarC_List.tryPick
    (fun uu___ ->
       match uu___ with
       | Imported (u, uu___1) -> FStar_Pervasives_Native.Some u
       | uu___1 -> FStar_Pervasives_Native.None) (decl_flags d)
let imported_home (d : decl) : Prims.string FStar_Pervasives_Native.option=
  FStarC_List.tryPick
    (fun uu___ ->
       match uu___ with
       | Imported (uu___1, h) -> h
       | uu___1 -> FStar_Pervasives_Native.None) (decl_flags d)
let branch_children (br : branch) : expr Prims.list=
  let uu___ = br in
  match uu___ with
  | (uu___1, g, b) ->
      FStarC_List.op_At
        (match g with
         | FStar_Pervasives_Native.Some g1 -> [g1]
         | FStar_Pervasives_Native.None -> []) [b]
let children (x : expr) : expr Prims.list=
  match x.e with
  | EConst uu___ -> []
  | EVar uu___ -> []
  | EQual uu___ -> []
  | EAny -> []
  | EAbort uu___ -> []
  | ELet (uu___, uu___1, e1, e2) -> [e1; e2]
  | EApp (h, es) -> h :: es
  | EFun (uu___, b) -> [b]
  | EMatch (s, brs) ->
      let uu___ = FStarC_List.collect branch_children brs in s :: uu___
  | EIf (c, a, b) -> [c; a; b]
  | ESeq (a, b) -> [a; b]
  | ECtor (uu___, es) -> es
  | ETuple es -> es
  | EOp (uu___, es) -> es
  | ERecord (uu___, fs) -> FStarC_List.map FStar_Pervasives_Native.snd fs
  | EProj (e1, uu___, uu___1) -> [e1]
  | EDiscrim (e1, uu___) -> [e1]
  | ECoerce (e1, uu___) -> [e1]
  | ECast (e1, uu___) -> [e1]
  | ERaise e1 -> [e1]
  | EWhile (a, b) -> [a; b]
  | ETry (a, brs) ->
      let uu___ = FStarC_List.collect branch_children brs in a :: uu___
let map_branch (g : expr -> expr) (br : branch) : branch=
  let uu___ = br in
  match uu___ with
  | (p, guard, b) ->
      let uu___1 =
        match guard with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some e ->
            let uu___2 = g e in FStar_Pervasives_Native.Some uu___2 in
      let uu___2 = g b in (p, uu___1, uu___2)
let map_children (g : expr -> expr) (x : expr) : expr=
  match x.e with
  | EConst uu___ -> x
  | EVar uu___ -> x
  | EQual uu___ -> x
  | EAny -> x
  | EAbort uu___ -> x
  | ELet (v, ty, e1, e2) ->
      let uu___ =
        let uu___1 =
          let uu___2 = g e1 in let uu___3 = g e2 in (v, ty, uu___2, uu___3) in
        ELet uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | EApp (h, es) ->
      let uu___ =
        let uu___1 =
          let uu___2 = g h in
          let uu___3 = FStarC_List.map g es in (uu___2, uu___3) in
        EApp uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | EFun (bs, b) ->
      let uu___ =
        let uu___1 = let uu___2 = g b in (bs, uu___2) in EFun uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | EMatch (s, brs) ->
      let uu___ =
        let uu___1 =
          let uu___2 = g s in
          let uu___3 = FStarC_List.map (map_branch g) brs in (uu___2, uu___3) in
        EMatch uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | EIf (c, a, b) ->
      let uu___ =
        let uu___1 =
          let uu___2 = g c in
          let uu___3 = g a in let uu___4 = g b in (uu___2, uu___3, uu___4) in
        EIf uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | ESeq (a, b) ->
      let uu___ =
        let uu___1 = let uu___2 = g a in let uu___3 = g b in (uu___2, uu___3) in
        ESeq uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | ECtor (n, es) ->
      let uu___ =
        let uu___1 = let uu___2 = FStarC_List.map g es in (n, uu___2) in
        ECtor uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | ETuple es ->
      let uu___ = let uu___1 = FStarC_List.map g es in ETuple uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | EOp (o, es) ->
      let uu___ =
        let uu___1 = let uu___2 = FStarC_List.map g es in (o, uu___2) in
        EOp uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | ERecord (n, fs) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_List.map
              (fun uu___3 ->
                 match uu___3 with
                 | (f, e) -> let uu___4 = g e in (f, uu___4)) fs in
          (n, uu___2) in
        ERecord uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | EProj (e1, n, f) ->
      let uu___ =
        let uu___1 = let uu___2 = g e1 in (uu___2, n, f) in EProj uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | EDiscrim (e1, n) ->
      let uu___ =
        let uu___1 = let uu___2 = g e1 in (uu___2, n) in EDiscrim uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | ECoerce (e1, c) ->
      let uu___ =
        let uu___1 = let uu___2 = g e1 in (uu___2, c) in ECoerce uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | ECast (e1, c) ->
      let uu___ =
        let uu___1 = let uu___2 = g e1 in (uu___2, c) in ECast uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | ERaise e1 ->
      let uu___ = let uu___1 = g e1 in ERaise uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | EWhile (a, b) ->
      let uu___ =
        let uu___1 = let uu___2 = g a in let uu___3 = g b in (uu___2, uu___3) in
        EWhile uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
  | ETry (a, brs) ->
      let uu___ =
        let uu___1 =
          let uu___2 = g a in
          let uu___3 = FStarC_List.map (map_branch g) brs in (uu___2, uu___3) in
        ETry uu___1 in
      { e = uu___; ty = (x.ty); eff = (x.eff) }
let iter_children (f : expr -> unit) (x : expr) : unit=
  let uu___ = children x in FStarC_List.iter f uu___
let fold_children (f : 'a -> expr -> 'a) (init : 'a) (x : expr) : 'a=
  let uu___ = children x in FStarC_List.fold_left f init uu___
let exists_child (f : expr -> Prims.bool) (x : expr) : Prims.bool=
  let uu___ = children x in FStarC_List.existsb f uu___
let for_all_children (f : expr -> Prims.bool) (x : expr) : Prims.bool=
  let uu___ = children x in FStarC_List.for_all f uu___
let rec is_droppable (e : expr) : Prims.bool=
  let all es = FStarC_List.for_all is_droppable es in
  if
    match e.e with
    | EOp ({ po_op = Commented uu___; po_ty = uu___1;_}, uu___2) -> true
    | uu___ -> false
  then false
  else
    if is_pure e.eff
    then true
    else
      (match e.e with
       | EConst uu___ -> true
       | EVar uu___ -> true
       | EQual uu___ -> true
       | EAny -> true
       | EApp uu___ -> false
       | EFun uu___ -> false
       | EWhile uu___ -> false
       | EAbort uu___ -> false
       | ERaise uu___ -> false
       | ETry uu___ -> false
       | EOp ({ po_op = BufRead; po_ty = uu___;_}, es) -> all es
       | EOp ({ po_op = BufCreate uu___; po_ty = uu___1;_}, uu___2) -> false
       | EOp ({ po_op = BufWrite; po_ty = uu___;_}, uu___1) -> false
       | EOp ({ po_op = BufFree; po_ty = uu___;_}, uu___1) -> false
       | EOp ({ po_op = BufBlit; po_ty = uu___;_}, uu___1) -> false
       | EOp (uu___, es) -> all es
       | ECtor uu___ -> for_all_children is_droppable e
       | ETuple uu___ -> for_all_children is_droppable e
       | ELet uu___ -> for_all_children is_droppable e
       | ESeq uu___ -> for_all_children is_droppable e
       | EIf uu___ -> for_all_children is_droppable e
       | EMatch uu___ -> for_all_children is_droppable e
       | ERecord uu___ -> for_all_children is_droppable e
       | EProj uu___ -> for_all_children is_droppable e
       | EDiscrim uu___ -> for_all_children is_droppable e
       | ECast uu___ -> for_all_children is_droppable e
       | ECoerce uu___ -> for_all_children is_droppable e)
let text (s : Prims.string) : FStar_Pprint.document=
  FStar_Pprint.doc_of_string s
let parens_if (b : Prims.bool) (d : FStar_Pprint.document) :
  FStar_Pprint.document= if b then FStar_Pprint.parens d else d
let sep_by (s : FStar_Pprint.document)
  (ds : FStar_Pprint.document Prims.list) : FStar_Pprint.document=
  FStar_Pprint.separate s ds
let name_to_doc (n : name) : FStar_Pprint.document=
  let uu___ = string_of_name n in text uu___
let eff_to_string (e : eff) : Prims.string=
  match e with | E_Ghost -> "Ghost" | E_Pure -> "Pure" | E_Impure -> "Impure"
let eff_to_doc (e : eff) : FStar_Pprint.document= text (eff_to_string e)
let iwidth_to_string (w : iwidth) : Prims.string=
  match w with
  | W8 -> "8"
  | W16 -> "16"
  | W32 -> "32"
  | W64 -> "64"
  | W128 -> "128"
  | WSizet -> "size"
let width_to_string (sw : (FStarC_Const.signedness * iwidth)) : Prims.string=
  let uu___ = sw in
  match uu___ with
  | (s, w) ->
      Prims.strcat
        (match s with
         | FStarC_Const.Unsigned -> "u"
         | FStarC_Const.Signed -> "i") (iwidth_to_string w)
let op_to_string (o : prim_op) : Prims.string=
  Prims.strcat
    (match o.po_op with
     | Add -> "+"
     | AddW -> "+."
     | Sub -> "-"
     | SubW -> "-."
     | Mult -> "*"
     | MultW -> "*."
     | Div -> "/"
     | DivW -> "/."
     | Mod -> "%"
     | BOr -> "|"
     | BAnd -> "&"
     | BXor -> "^"
     | BShiftL -> "<<"
     | BShiftR -> ">>"
     | BNot -> "~"
     | Eq -> "="
     | Neq -> "<>"
     | Lt -> "<"
     | Lte -> "<="
     | Gt -> ">"
     | Gte -> ">="
     | And -> "&&"
     | Or -> "||"
     | Not -> "not"
     | BufCreate (LStack) -> "alloca"
     | BufCreate (LHeap) -> "malloc"
     | BufRead -> "read"
     | BufWrite -> "write"
     | BufSub -> "sub"
     | BufFree -> "free"
     | BufNull -> "null"
     | BufIsNull -> "is_null"
     | BufBlit -> "blit"
     | BufLit -> "lit"
     | BufUnconst -> "unconst"
     | Commented uu___ -> "comment")
    (match o.po_ty with
     | FStar_Pervasives_Native.None -> ""
     | FStar_Pervasives_Native.Some (PInt sw) -> width_to_string sw
     | FStar_Pervasives_Native.Some (PFloat fw) -> fwidth_to_string fw)
let escape_char (c : FStarC_BaseTypes.char) : Prims.string=
  match c with
  | 10 -> "\\n"
  | 9 -> "\\t"
  | 13 -> "\\r"
  | 34 -> "\\\""
  | 92 -> "\\\\"
  | c1 -> FStarC_Util.string_of_char c1
let escape_string (s : Prims.string) : Prims.string=
  let uu___ = FStarC_List.map escape_char (FStarC_String.list_of_string s) in
  FStarC_String.concat "" uu___
let constant_to_doc (c : constant) : FStar_Pprint.document=
  match c with
  | CUnit -> text "()"
  | CBool b -> text (if b then "true" else "false")
  | CInt (v, b, FStar_Pervasives_Native.None) -> text (int_lit_to_string v b)
  | CInt (v, b, FStar_Pervasives_Native.Some (sg, w)) ->
      text
        (Prims.strcat (int_lit_to_string v b)
           (Prims.strcat "<"
              (Prims.strcat
                 (match sg with
                  | FStarC_Const.Unsigned -> "u"
                  | FStarC_Const.Signed -> "i")
                 (Prims.strcat (iwidth_to_string w) ">"))))
  | CFloat (v, fw) ->
      text
        (Prims.strcat (float_lit_to_string v)
           (Prims.strcat "<" (Prims.strcat (fwidth_to_string fw) ">")))
  | CChar c1 -> text (Prims.strcat "'" (Prims.strcat (escape_char c1) "'"))
  | CString s ->
      let uu___ = let uu___1 = escape_string s in text uu___1 in
      FStar_Pprint.dquotes uu___
let constant_to_string (c : constant) : Prims.string=
  let uu___ = constant_to_doc c in FStar_Pprint.render uu___
let rec cty_to_doc' (prec : Prims.int) (t : cty) : FStar_Pprint.document=
  match t with
  | TVar x -> text (Prims.strcat "'" x)
  | TInt sw -> text (width_to_string sw)
  | TFloat fw -> text (fwidth_to_string fw)
  | TUnit -> text "unit"
  | TExn -> text "exn"
  | TAny -> text "any"
  | TConst c -> constant_to_doc c
  | TArrow (t1, e, t2) ->
      let arrow =
        match e with
        | E_Pure -> text "->"
        | E_Ghost -> text "-[G]->"
        | E_Impure -> text "-[I]->" in
      let uu___ =
        let uu___1 =
          let uu___2 = cty_to_doc' Prims.int_one t1 in
          let uu___3 =
            let uu___4 = cty_to_doc' Prims.int_zero t2 in
            FStar_Pprint.op_Hat_Slash_Hat arrow uu___4 in
          FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
        FStar_Pprint.group uu___1 in
      parens_if (prec >= Prims.int_one) uu___
  | TApp (n, []) -> name_to_doc n
  | TApp (n, args) ->
      let uu___ =
        let uu___1 =
          let uu___2 = name_to_doc n in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  FStarC_List.map (cty_to_doc' Prims.int_zero) args in
                sep_by
                  (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                     FStar_Pprint.space) uu___6 in
              FStar_Pprint.op_Hat_Hat uu___5 FStar_Pprint.rangle in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu___4 in
          FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStar_Pprint.group uu___1 in
      parens_if (prec >= (Prims.of_int 2)) uu___
  | TBuf t1 ->
      let uu___ =
        let uu___1 =
          let uu___2 = cty_to_doc' (Prims.of_int 2) t1 in
          FStar_Pprint.op_Hat_Slash_Hat (text "buf") uu___2 in
        FStar_Pprint.group uu___1 in
      parens_if (prec >= (Prims.of_int 2)) uu___
  | TRef t1 ->
      let uu___ =
        let uu___1 =
          let uu___2 = cty_to_doc' (Prims.of_int 2) t1 in
          FStar_Pprint.op_Hat_Slash_Hat (text "ref") uu___2 in
        FStar_Pprint.group uu___1 in
      parens_if (prec >= (Prims.of_int 2)) uu___
  | TInline t1 ->
      let uu___ =
        let uu___1 =
          let uu___2 = cty_to_doc' (Prims.of_int 2) t1 in
          FStar_Pprint.op_Hat_Slash_Hat (text "inline") uu___2 in
        FStar_Pprint.group uu___1 in
      parens_if (prec >= (Prims.of_int 2)) uu___
  | TTuple ts ->
      let uu___ =
        let uu___1 = FStarC_List.map (cty_to_doc' Prims.int_one) ts in
        sep_by
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
             (FStar_Pprint.op_Hat_Hat (text "*") FStar_Pprint.space)) uu___1 in
      FStar_Pprint.parens uu___
let cty_to_doc (t : cty) : FStar_Pprint.document=
  cty_to_doc' Prims.int_zero t
let cty_to_string (t : cty) : Prims.string=
  let uu___ = cty_to_doc t in FStar_Pprint.render uu___
let rec pat_to_doc (p : pat) : FStar_Pprint.document=
  match p with
  | PWild -> FStar_Pprint.underscore
  | PVar x -> text x
  | PConst c -> constant_to_doc c
  | PCtor (n, []) -> name_to_doc n
  | PCtor (n, ps) ->
      let uu___ =
        let uu___1 = name_to_doc n in
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_List.map pat_to_doc ps in
            sep_by
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma FStar_Pprint.space)
              uu___4 in
          FStar_Pprint.parens uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | PRecord (uu___, fs) ->
      let uu___1 =
        let uu___2 =
          FStarC_List.map
            (fun uu___3 ->
               match uu___3 with
               | (f, q) ->
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = pat_to_doc q in
                       FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                         uu___6 in
                     FStar_Pprint.op_Hat_Slash_Hat (text f) uu___5 in
                   FStar_Pprint.group uu___4) fs in
        sep_by (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi FStar_Pprint.space)
          uu___2 in
      FStar_Pprint.braces uu___1
  | PTuple ps ->
      let uu___ =
        let uu___1 = FStarC_List.map pat_to_doc ps in
        sep_by
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma FStar_Pprint.space)
          uu___1 in
      FStar_Pprint.parens uu___
  | POr ps ->
      let uu___ =
        let uu___1 = FStarC_List.map pat_to_doc ps in
        sep_by
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
             (FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space))
          uu___1 in
      FStar_Pprint.group uu___
let pat_to_string (p : pat) : Prims.string=
  let uu___ = pat_to_doc p in FStar_Pprint.render uu___
let binder_to_doc (b : binder) : FStar_Pprint.document=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = cty_to_doc b.b_ty in
        FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___3 in
      FStar_Pprint.op_Hat_Hat (text b.b_name) uu___2 in
    FStar_Pprint.group uu___1 in
  FStar_Pprint.parens uu___
let rec expr_to_doc' (prec : Prims.int) (e : expr) : FStar_Pprint.document=
  match e.e with
  | EConst c -> constant_to_doc c
  | EVar x -> text x
  | EQual (n, []) -> name_to_doc n
  | EQual (n, tys) ->
      let uu___ =
        let uu___1 = name_to_doc n in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_List.map cty_to_doc tys in
              sep_by
                (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                   FStar_Pprint.space) uu___5 in
            FStar_Pprint.op_Hat_Hat uu___4 FStar_Pprint.rangle in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | ELet (x, t, e1, e2) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 = cty_to_doc t in
                        let uu___10 =
                          let uu___11 = expr_to_doc' Prims.int_zero e1 in
                          FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                            uu___11 in
                        FStar_Pprint.op_Hat_Slash_Hat uu___9 uu___10 in
                      FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___8 in
                    FStar_Pprint.op_Hat_Hat (text x) uu___7 in
                  FStar_Pprint.op_Hat_Slash_Hat (text "let") uu___6 in
                FStar_Pprint.nest (Prims.of_int 2) uu___5 in
              FStar_Pprint.group uu___4 in
            FStar_Pprint.op_Hat_Slash_Hat uu___3 (text "in") in
          FStar_Pprint.group uu___2 in
        let uu___2 =
          let uu___3 = expr_to_doc' Prims.int_zero e2 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      parens_if (prec >= Prims.int_one) uu___
  | EApp (h, args) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = expr_to_doc' Prims.int_one h in
            let uu___4 =
              let uu___5 = FStarC_List.map (expr_to_doc' Prims.int_one) args in
              sep_by (FStar_Pprint.break_ Prims.int_one) uu___5 in
            FStar_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
          FStar_Pprint.nest (Prims.of_int 2) uu___2 in
        FStar_Pprint.group uu___1 in
      parens_if (prec >= Prims.int_one) uu___
  | EFun (bs, body) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_List.map binder_to_doc bs in
                sep_by (FStar_Pprint.break_ Prims.int_one) uu___5 in
              let uu___5 =
                let uu___6 = expr_to_doc' Prims.int_zero body in
                FStar_Pprint.op_Hat_Slash_Hat (text "->") uu___6 in
              FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
            FStar_Pprint.op_Hat_Slash_Hat (text "fun") uu___3 in
          FStar_Pprint.nest (Prims.of_int 2) uu___2 in
        FStar_Pprint.group uu___1 in
      parens_if (prec >= Prims.int_one) uu___
  | EMatch (scrut, brs) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = expr_to_doc' Prims.int_zero scrut in
                FStar_Pprint.op_Hat_Slash_Hat uu___5 (text "with") in
              FStar_Pprint.op_Hat_Slash_Hat (text "match") uu___4 in
            FStar_Pprint.group uu___3 in
          let uu___3 =
            let uu___4 = FStarC_List.map branch_to_doc brs in
            FStar_Pprint.concat uu___4 in
          FStar_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStar_Pprint.group uu___1 in
      parens_if (prec >= Prims.int_one) uu___
  | EIf (c, t, e2) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = expr_to_doc' Prims.int_zero c in
                FStar_Pprint.op_Hat_Slash_Hat (text "if") uu___5 in
              FStar_Pprint.nest (Prims.of_int 2) uu___4 in
            FStar_Pprint.group uu___3 in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = expr_to_doc' Prims.int_one t in
                  FStar_Pprint.op_Hat_Slash_Hat (text "then") uu___7 in
                FStar_Pprint.nest (Prims.of_int 2) uu___6 in
              FStar_Pprint.group uu___5 in
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 = expr_to_doc' Prims.int_one e2 in
                  FStar_Pprint.op_Hat_Slash_Hat (text "else") uu___8 in
                FStar_Pprint.nest (Prims.of_int 2) uu___7 in
              FStar_Pprint.group uu___6 in
            FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
          FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
        FStar_Pprint.group uu___1 in
      parens_if (prec >= Prims.int_one) uu___
  | ESeq (e1, e2) ->
      let uu___ =
        let uu___1 = expr_to_doc' Prims.int_one e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 = expr_to_doc' Prims.int_zero e2 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      parens_if (prec >= Prims.int_one) uu___
  | ECtor (n, []) -> name_to_doc n
  | ECtor (n, args) ->
      let uu___ =
        let uu___1 = name_to_doc n in
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_List.map (expr_to_doc' Prims.int_zero) args in
            sep_by
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma FStar_Pprint.space)
              uu___4 in
          FStar_Pprint.parens uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | ETuple es ->
      let uu___ =
        let uu___1 = FStarC_List.map (expr_to_doc' Prims.int_zero) es in
        sep_by
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma FStar_Pprint.space)
          uu___1 in
      FStar_Pprint.parens uu___
  | ERecord (n, fs) ->
      let uu___ =
        let uu___1 = name_to_doc n in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_List.map
                (fun uu___5 ->
                   match uu___5 with
                   | (f, e1) ->
                       let uu___6 =
                         let uu___7 =
                           let uu___8 = expr_to_doc' Prims.int_zero e1 in
                           FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                             uu___8 in
                         FStar_Pprint.op_Hat_Slash_Hat (text f) uu___7 in
                       FStar_Pprint.group uu___6) fs in
            sep_by
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi FStar_Pprint.space)
              uu___4 in
          FStar_Pprint.braces uu___3 in
        FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
      FStar_Pprint.group uu___
  | EProj (e1, n, f) ->
      let uu___ = expr_to_doc' Prims.int_one e1 in
      let uu___1 =
        let uu___2 =
          let uu___3 = name_to_doc n in
          FStar_Pprint.op_Hat_Hat uu___3
            (FStar_Pprint.op_Hat_Hat FStar_Pprint.dot (text f)) in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu___2 in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | EDiscrim (e1, n) ->
      let uu___ = name_to_doc n in
      let uu___1 =
        let uu___2 =
          let uu___3 = expr_to_doc' Prims.int_zero e1 in
          FStar_Pprint.parens uu___3 in
        FStar_Pprint.op_Hat_Hat (text "?") uu___2 in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | ECoerce (e1, t) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = expr_to_doc' Prims.int_zero e1 in
            let uu___4 =
              let uu___5 = cty_to_doc t in
              FStar_Pprint.op_Hat_Slash_Hat (text "<:") uu___5 in
            FStar_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
          FStar_Pprint.nest (Prims.of_int 2) uu___2 in
        FStar_Pprint.parens uu___1 in
      FStar_Pprint.group uu___
  | ECast (e1, t) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = expr_to_doc' Prims.int_zero e1 in
            let uu___4 =
              let uu___5 = cty_to_doc t in
              FStar_Pprint.op_Hat_Slash_Hat (text ":>") uu___5 in
            FStar_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
          FStar_Pprint.nest (Prims.of_int 2) uu___2 in
        FStar_Pprint.parens uu___1 in
      FStar_Pprint.group uu___
  | EOp (op1, args) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_List.map (expr_to_doc' Prims.int_zero) args in
            sep_by
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma FStar_Pprint.space)
              uu___3 in
          FStar_Pprint.parens uu___2 in
        FStar_Pprint.op_Hat_Hat
          (text (Prims.strcat "`" (Prims.strcat (op_to_string op1) "`")))
          uu___1 in
      FStar_Pprint.group uu___
  | EWhile (c, body) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = expr_to_doc' Prims.int_one c in
                FStar_Pprint.op_Hat_Slash_Hat (text "while") uu___5 in
              FStar_Pprint.nest (Prims.of_int 2) uu___4 in
            FStar_Pprint.group uu___3 in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 = expr_to_doc' Prims.int_zero body in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___8 in
                  FStar_Pprint.op_Hat_Hat (text "{") uu___7 in
                FStar_Pprint.nest (Prims.of_int 2) uu___6 in
              FStar_Pprint.group uu___5 in
            FStar_Pprint.op_Hat_Hat uu___4
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline (text "}")) in
          FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
        FStar_Pprint.group uu___1 in
      parens_if (prec >= Prims.int_one) uu___
  | EAny -> text "any"
  | EAbort s ->
      FStar_Pprint.group
        (FStar_Pprint.op_Hat_Slash_Hat (text "abort")
           (FStar_Pprint.dquotes (text s)))
  | ERaise e1 ->
      let uu___ =
        let uu___1 = expr_to_doc' Prims.int_one e1 in
        FStar_Pprint.op_Hat_Slash_Hat (text "raise") uu___1 in
      FStar_Pprint.group uu___
  | ETry (e1, brs) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = expr_to_doc' Prims.int_zero e1 in
                FStar_Pprint.op_Hat_Slash_Hat (text "try") uu___5 in
              FStar_Pprint.nest (Prims.of_int 2) uu___4 in
            FStar_Pprint.group uu___3 in
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_List.map branch_to_doc brs in
              FStar_Pprint.concat uu___5 in
            FStar_Pprint.op_Hat_Hat (text "with") uu___4 in
          FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
        FStar_Pprint.group uu___1 in
      parens_if (prec >= Prims.int_one) uu___
and branch_to_doc (br : branch) : FStar_Pprint.document=
  let uu___ = br in
  match uu___ with
  | (p, guard, body) ->
      let g =
        match guard with
        | FStar_Pervasives_Native.None -> FStar_Pprint.empty
        | FStar_Pervasives_Native.Some g1 ->
            let uu___1 =
              let uu___2 =
                let uu___3 = expr_to_doc' Prims.int_one g1 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
              FStar_Pprint.op_Hat_Hat (text "when") uu___2 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1 in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = pat_to_doc p in
                let uu___7 =
                  let uu___8 =
                    let uu___9 = expr_to_doc' Prims.int_zero body in
                    FStar_Pprint.op_Hat_Slash_Hat (text "->") uu___9 in
                  FStar_Pprint.op_Hat_Slash_Hat g uu___8 in
                FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu___4 in
          FStar_Pprint.nest (Prims.of_int 2) uu___3 in
        FStar_Pprint.group uu___2 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___1
let expr_to_doc (e : expr) : FStar_Pprint.document=
  expr_to_doc' Prims.int_zero e
let expr_to_string (e : expr) : Prims.string=
  let uu___ = expr_to_doc e in FStar_Pprint.render uu___
let flag_to_doc (f : flag) : FStar_Pprint.document=
  match f with
  | Rec ns ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_List.map string_of_name ns in
            FStarC_String.concat "," uu___3 in
          Prims.strcat uu___2 "]" in
        Prims.strcat "rec[" uu___1 in
      text uu___
  | Private -> text "private"
  | Root -> text "root"
  | Entrypoint -> text "entrypoint"
  | NoNewtype -> text "no_newtype"
  | Inline -> text "inline"
  | Erased -> text "erased"
  | Comment s -> text (Prims.strcat "(* " (Prims.strcat s " *)"))
  | Prologue s -> text (Prims.strcat "prologue " s)
  | Epilogue s -> text (Prims.strcat "epilogue " s)
  | ClosurePrologue (a, b) ->
      text
        (Prims.strcat "closure_prologue "
           (Prims.strcat a (Prims.strcat " / " b)))
  | CMacro -> text "c_macro"
  | CReference -> text "c_reference"
  | CInline -> text "c_inline"
  | Realized -> text "realized"
  | Extern (n, h) ->
      text
        (Prims.strcat "extern"
           (Prims.strcat
              (match n with
               | FStar_Pervasives_Native.Some n1 -> Prims.strcat " " n1
               | FStar_Pervasives_Native.None -> "")
              (match h with
               | FStar_Pervasives_Native.Some h1 ->
                   Prims.strcat " <" (Prims.strcat h1 ">")
               | FStar_Pervasives_Native.None -> "")))
  | SourceRecord -> text "source-record"
  | Existential (c, f1) ->
      text
        (Prims.strcat "existential["
           (Prims.strcat c (Prims.strcat "." (Prims.strcat f1 "]"))))
  | Modelled -> text "modelled"
  | Imported (u, h) ->
      text
        (Prims.strcat "imported["
           (Prims.strcat u
              (Prims.strcat
                 (match h with
                  | FStar_Pervasives_Native.Some m -> Prims.strcat "@" m
                  | FStar_Pervasives_Native.None -> "") "]")))
let flags_to_doc (fs : flag Prims.list) : FStar_Pprint.document=
  match fs with
  | [] -> FStar_Pprint.empty
  | uu___ ->
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_List.map flag_to_doc fs in
          sep_by
            (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma FStar_Pprint.space)
            uu___3 in
        FStar_Pprint.op_Hat_Hat uu___2
          (FStar_Pprint.op_Hat_Hat (text "]") FStar_Pprint.hardline) in
      FStar_Pprint.op_Hat_Hat (text "[@@") uu___1
let params_to_doc (ps : Prims.string Prims.list) : FStar_Pprint.document=
  match ps with
  | [] -> FStar_Pprint.empty
  | uu___ ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_List.map (fun p -> text (Prims.strcat "'" p)) ps in
            FStar_Pprint.separate
              (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma FStar_Pprint.space)
              uu___4 in
          FStar_Pprint.op_Hat_Hat uu___3 FStar_Pprint.rangle in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu___2 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___1
let tydef_to_doc (d : tydef) : FStar_Pprint.document=
  match d with
  | TAbstract ->
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space (text "<abstract>")
  | TAbbrev t ->
      let uu___ = cty_to_doc t in
      FStar_Pprint.op_Hat_Hat (FStar_Pprint.break_ Prims.int_one) uu___
  | TRecord fs ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    FStarC_List.map
                      (fun uu___7 ->
                         match uu___7 with
                         | (f, t) ->
                             let uu___8 =
                               let uu___9 =
                                 let uu___10 = cty_to_doc t in
                                 FStar_Pprint.op_Hat_Slash_Hat
                                   FStar_Pprint.colon uu___10 in
                               FStar_Pprint.op_Hat_Hat (text f) uu___9 in
                             FStar_Pprint.group uu___8) fs in
                  sep_by
                    (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                       (FStar_Pprint.break_ Prims.int_one)) uu___6 in
                FStar_Pprint.op_Hat_Hat (FStar_Pprint.break_ Prims.int_one)
                  uu___5 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu___4 in
            FStar_Pprint.nest (Prims.of_int 2) uu___3 in
          FStar_Pprint.op_Hat_Hat uu___2
            (FStar_Pprint.op_Hat_Hat (FStar_Pprint.break_ Prims.int_one)
               FStar_Pprint.rbrace) in
        FStar_Pprint.group uu___1 in
      FStar_Pprint.op_Hat_Hat (FStar_Pprint.break_ Prims.int_one) uu___
  | TVariant cs ->
      let ctor_to_doc cf =
        let uu___ = cf in
        match uu___ with
        | (c, fs) ->
            (match fs with
             | [] -> name_to_doc c
             | uu___1 ->
                 let uu___2 =
                   let uu___3 = name_to_doc c in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStarC_List.map
                           (fun uu___7 ->
                              match uu___7 with
                              | (f, t) ->
                                  let uu___8 =
                                    let uu___9 =
                                      let uu___10 = cty_to_doc t in
                                      FStar_Pprint.op_Hat_Slash_Hat
                                        FStar_Pprint.colon uu___10 in
                                    FStar_Pprint.op_Hat_Hat (text f) uu___9 in
                                  FStar_Pprint.group uu___8) fs in
                       sep_by
                         (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            (FStar_Pprint.op_Hat_Hat (text "&")
                               FStar_Pprint.space)) uu___6 in
                     FStar_Pprint.op_Hat_Slash_Hat (text "of") uu___5 in
                   FStar_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
                 FStar_Pprint.group uu___2) in
      let uu___ =
        FStarC_List.map
          (fun c ->
             let uu___1 =
               let uu___2 =
                 let uu___3 = ctor_to_doc c in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___3 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu___2 in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___1) cs in
      FStar_Pprint.concat uu___
let decl_to_doc (d : decl) : FStar_Pprint.document=
  match d with
  | DType t ->
      let uu___ = flags_to_doc t.dt_flags in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = name_to_doc t.dt_name in
                let uu___7 =
                  let uu___8 = params_to_doc t.dt_params in
                  let uu___9 =
                    let uu___10 =
                      let uu___11 = tydef_to_doc t.dt_body in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu___11 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___10 in
                  FStar_Pprint.op_Hat_Hat uu___8 uu___9 in
                FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
            FStar_Pprint.op_Hat_Hat (text "type") uu___4 in
          FStar_Pprint.nest (Prims.of_int 2) uu___3 in
        FStar_Pprint.group uu___2 in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | DLet l ->
      let uu___ = flags_to_doc l.dl_flags in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 = name_to_doc l.dl_name in
                    let uu___9 =
                      let uu___10 = params_to_doc l.dl_typars in
                      let uu___11 =
                        let uu___12 =
                          match l.dl_binders with
                          | [] -> FStar_Pprint.empty
                          | bs ->
                              let uu___13 =
                                let uu___14 =
                                  FStarC_List.map binder_to_doc bs in
                                sep_by (FStar_Pprint.break_ Prims.int_one)
                                  uu___14 in
                              FStar_Pprint.op_Hat_Hat
                                (FStar_Pprint.break_ Prims.int_one) uu___13 in
                        let uu___13 =
                          let uu___14 =
                            let uu___15 = cty_to_doc l.dl_ret in
                            let uu___16 =
                              let uu___17 =
                                let uu___18 =
                                  let uu___19 = eff_to_doc l.dl_eff in
                                  FStar_Pprint.brackets uu___19 in
                                FStar_Pprint.op_Hat_Slash_Hat uu___18
                                  FStar_Pprint.equals in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu___17 in
                            FStar_Pprint.op_Hat_Hat uu___15 uu___16 in
                          FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                            uu___14 in
                        FStar_Pprint.op_Hat_Slash_Hat uu___12 uu___13 in
                      FStar_Pprint.op_Hat_Hat uu___10 uu___11 in
                    FStar_Pprint.op_Hat_Hat uu___8 uu___9 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___7 in
                FStar_Pprint.op_Hat_Hat (text "let") uu___6 in
              FStar_Pprint.nest (Prims.of_int 2) uu___5 in
            FStar_Pprint.group uu___4 in
          let uu___4 =
            let uu___5 =
              let uu___6 = expr_to_doc l.dl_body in
              FStar_Pprint.nest (Prims.of_int 2) uu___6 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___5 in
          FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
        FStar_Pprint.group uu___2 in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | DExternal e ->
      let uu___ = flags_to_doc e.dx_flags in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = name_to_doc e.dx_name in
                let uu___7 =
                  let uu___8 =
                    let uu___9 = cty_to_doc e.dx_ty in
                    FStar_Pprint.op_Hat_Hat uu___9
                      (match e.dx_target with
                       | FStar_Pervasives_Native.None -> FStar_Pprint.empty
                       | FStar_Pervasives_Native.Some t ->
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             (FStar_Pprint.op_Hat_Slash_Hat
                                FStar_Pprint.equals
                                (FStar_Pprint.dquotes (text t)))) in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___8 in
                FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
            FStar_Pprint.op_Hat_Hat (text "external") uu___4 in
          FStar_Pprint.nest (Prims.of_int 2) uu___3 in
        FStar_Pprint.group uu___2 in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
  | DExn e ->
      let uu___ = flags_to_doc e.de_flags in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = name_to_doc e.de_name in
                let uu___7 =
                  match e.de_args with
                  | [] -> FStar_Pprint.empty
                  | args ->
                      let uu___8 =
                        let uu___9 =
                          let uu___10 = FStarC_List.map cty_to_doc args in
                          sep_by
                            (FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               (FStar_Pprint.op_Hat_Hat (text "&")
                                  FStar_Pprint.space)) uu___10 in
                        FStar_Pprint.op_Hat_Slash_Hat (text "of") uu___9 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___8 in
                FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu___5 in
            FStar_Pprint.op_Hat_Hat (text "exception") uu___4 in
          FStar_Pprint.nest (Prims.of_int 2) uu___3 in
        FStar_Pprint.group uu___2 in
      FStar_Pprint.op_Hat_Hat uu___ uu___1
let decl_to_string (d : decl) : Prims.string=
  let uu___ = decl_to_doc d in FStar_Pprint.render uu___
let program_to_doc (p : program) : FStar_Pprint.document=
  FStarC_Pprint.separate_map
    (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline FStar_Pprint.hardline)
    decl_to_doc p
let program_to_string (p : program) : Prims.string=
  let uu___ = program_to_doc p in FStar_Pprint.render uu___
let showable_name : name FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = string_of_name }
let showable_eff : eff FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = eff_to_string }
let showable_cty : cty FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = cty_to_string }
let showable_constant : constant FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = constant_to_string }
let showable_pat : pat FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = pat_to_string }
let showable_expr : expr FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = expr_to_string }
let showable_decl : decl FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = decl_to_string }
let pp_cty : cty FStarC_Class_PP.pretty= { FStarC_Class_PP.pp = cty_to_doc }
let pp_expr : expr FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = expr_to_doc }
let pp_decl : decl FStarC_Class_PP.pretty=
  { FStarC_Class_PP.pp = decl_to_doc }
