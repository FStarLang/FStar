open Prims
type expr =
  | Lit of Prims.int
  | Atom of Prims.nat* FStar_Reflection_Types.term
  | Plus of expr* expr
  | Mult of expr* expr
  | Minus of expr* expr
  | Land of expr* expr
  | Lxor of expr* expr
  | Lor of expr* expr
  | Shl of expr* expr
  | Shr of expr* expr
  | Neg of expr
  | Udiv of expr* expr
  | Umod of expr* expr
  | MulMod of expr* expr
  | NatToBv of expr
let uu___is_Lit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Lit _0 -> true | uu____121 -> false
let __proj__Lit__item___0: expr -> Prims.int =
  fun projectee  -> match projectee with | Lit _0 -> _0
let uu___is_Atom: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Atom (_0,_1) -> true | uu____143 -> false
let __proj__Atom__item___0: expr -> Prims.nat =
  fun projectee  -> match projectee with | Atom (_0,_1) -> _0
let __proj__Atom__item___1: expr -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Atom (_0,_1) -> _1
let uu___is_Plus: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Plus (_0,_1) -> true | uu____186 -> false
let __proj__Plus__item___0: expr -> expr =
  fun projectee  -> match projectee with | Plus (_0,_1) -> _0
let __proj__Plus__item___1: expr -> expr =
  fun projectee  -> match projectee with | Plus (_0,_1) -> _1
let uu___is_Mult: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult (_0,_1) -> true | uu____223 -> false
let __proj__Mult__item___0: expr -> expr =
  fun projectee  -> match projectee with | Mult (_0,_1) -> _0
let __proj__Mult__item___1: expr -> expr =
  fun projectee  -> match projectee with | Mult (_0,_1) -> _1
let uu___is_Minus: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus (_0,_1) -> true | uu____260 -> false
let __proj__Minus__item___0: expr -> expr =
  fun projectee  -> match projectee with | Minus (_0,_1) -> _0
let __proj__Minus__item___1: expr -> expr =
  fun projectee  -> match projectee with | Minus (_0,_1) -> _1
let uu___is_Land: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Land (_0,_1) -> true | uu____297 -> false
let __proj__Land__item___0: expr -> expr =
  fun projectee  -> match projectee with | Land (_0,_1) -> _0
let __proj__Land__item___1: expr -> expr =
  fun projectee  -> match projectee with | Land (_0,_1) -> _1
let uu___is_Lxor: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Lxor (_0,_1) -> true | uu____334 -> false
let __proj__Lxor__item___0: expr -> expr =
  fun projectee  -> match projectee with | Lxor (_0,_1) -> _0
let __proj__Lxor__item___1: expr -> expr =
  fun projectee  -> match projectee with | Lxor (_0,_1) -> _1
let uu___is_Lor: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Lor (_0,_1) -> true | uu____371 -> false
let __proj__Lor__item___0: expr -> expr =
  fun projectee  -> match projectee with | Lor (_0,_1) -> _0
let __proj__Lor__item___1: expr -> expr =
  fun projectee  -> match projectee with | Lor (_0,_1) -> _1
let uu___is_Shl: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Shl (_0,_1) -> true | uu____408 -> false
let __proj__Shl__item___0: expr -> expr =
  fun projectee  -> match projectee with | Shl (_0,_1) -> _0
let __proj__Shl__item___1: expr -> expr =
  fun projectee  -> match projectee with | Shl (_0,_1) -> _1
let uu___is_Shr: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Shr (_0,_1) -> true | uu____445 -> false
let __proj__Shr__item___0: expr -> expr =
  fun projectee  -> match projectee with | Shr (_0,_1) -> _0
let __proj__Shr__item___1: expr -> expr =
  fun projectee  -> match projectee with | Shr (_0,_1) -> _1
let uu___is_Neg: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Neg _0 -> true | uu____480 -> false
let __proj__Neg__item___0: expr -> expr =
  fun projectee  -> match projectee with | Neg _0 -> _0
let uu___is_Udiv: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Udiv (_0,_1) -> true | uu____502 -> false
let __proj__Udiv__item___0: expr -> expr =
  fun projectee  -> match projectee with | Udiv (_0,_1) -> _0
let __proj__Udiv__item___1: expr -> expr =
  fun projectee  -> match projectee with | Udiv (_0,_1) -> _1
let uu___is_Umod: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | Umod (_0,_1) -> true | uu____539 -> false
let __proj__Umod__item___0: expr -> expr =
  fun projectee  -> match projectee with | Umod (_0,_1) -> _0
let __proj__Umod__item___1: expr -> expr =
  fun projectee  -> match projectee with | Umod (_0,_1) -> _1
let uu___is_MulMod: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | MulMod (_0,_1) -> true | uu____576 -> false
let __proj__MulMod__item___0: expr -> expr =
  fun projectee  -> match projectee with | MulMod (_0,_1) -> _0
let __proj__MulMod__item___1: expr -> expr =
  fun projectee  -> match projectee with | MulMod (_0,_1) -> _1
let uu___is_NatToBv: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____611 -> false
let __proj__NatToBv__item___0: expr -> expr =
  fun projectee  -> match projectee with | NatToBv _0 -> _0
type connective =
  | C_Lt
  | C_Eq
  | C_Gt
  | C_Ne
let uu___is_C_Lt: connective -> Prims.bool =
  fun projectee  -> match projectee with | C_Lt  -> true | uu____629 -> false
let uu___is_C_Eq: connective -> Prims.bool =
  fun projectee  -> match projectee with | C_Eq  -> true | uu____636 -> false
let uu___is_C_Gt: connective -> Prims.bool =
  fun projectee  -> match projectee with | C_Gt  -> true | uu____643 -> false
let uu___is_C_Ne: connective -> Prims.bool =
  fun projectee  -> match projectee with | C_Ne  -> true | uu____650 -> false
type prop =
  | CompProp of expr* connective* expr
  | AndProp of prop* prop
  | OrProp of prop* prop
  | NotProp of prop
let uu___is_CompProp: prop -> Prims.bool =
  fun projectee  ->
    match projectee with | CompProp (_0,_1,_2) -> true | uu____695 -> false
let __proj__CompProp__item___0: prop -> expr =
  fun projectee  -> match projectee with | CompProp (_0,_1,_2) -> _0
let __proj__CompProp__item___1: prop -> connective =
  fun projectee  -> match projectee with | CompProp (_0,_1,_2) -> _1
let __proj__CompProp__item___2: prop -> expr =
  fun projectee  -> match projectee with | CompProp (_0,_1,_2) -> _2
let uu___is_AndProp: prop -> Prims.bool =
  fun projectee  ->
    match projectee with | AndProp (_0,_1) -> true | uu____751 -> false
let __proj__AndProp__item___0: prop -> prop =
  fun projectee  -> match projectee with | AndProp (_0,_1) -> _0
let __proj__AndProp__item___1: prop -> prop =
  fun projectee  -> match projectee with | AndProp (_0,_1) -> _1
let uu___is_OrProp: prop -> Prims.bool =
  fun projectee  ->
    match projectee with | OrProp (_0,_1) -> true | uu____788 -> false
let __proj__OrProp__item___0: prop -> prop =
  fun projectee  -> match projectee with | OrProp (_0,_1) -> _0
let __proj__OrProp__item___1: prop -> prop =
  fun projectee  -> match projectee with | OrProp (_0,_1) -> _1
let uu___is_NotProp: prop -> Prims.bool =
  fun projectee  ->
    match projectee with | NotProp _0 -> true | uu____823 -> false
let __proj__NotProp__item___0: prop -> prop =
  fun projectee  -> match projectee with | NotProp _0 -> _0
let lt: expr -> expr -> prop = fun e1  -> fun e2  -> CompProp (e1, C_Lt, e2)
let le: expr -> expr -> prop =
  fun e1  ->
    fun e2  -> CompProp (e1, C_Lt, (Plus ((Lit (Prims.parse_int "1")), e2)))
let eq: expr -> expr -> prop = fun e1  -> fun e2  -> CompProp (e1, C_Eq, e2)
let ne: expr -> expr -> prop = fun e1  -> fun e2  -> CompProp (e1, C_Ne, e2)
let gt: expr -> expr -> prop = fun e1  -> fun e2  -> CompProp (e1, C_Gt, e2)
let ge: expr -> expr -> prop =
  fun e1  ->
    fun e2  -> CompProp ((Plus ((Lit (Prims.parse_int "1")), e1)), C_Gt, e2)
type st =
  (Prims.nat,FStar_Reflection_Types.term Prims.list)
    FStar_Pervasives_Native.tuple2
type 'Aa tm =
  st ->
    (Prims.string,('Aa,st) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives.either
let return: 'a . 'a -> 'a tm =
  fun x  -> fun i  -> FStar_Pervasives.Inr (x, i)
let bind: 'a 'b . 'a tm -> ('a -> 'b tm) -> 'b tm =
  fun m  ->
    fun f  ->
      fun i  ->
        match m i with
        | FStar_Pervasives.Inl s -> FStar_Pervasives.Inl s
        | FStar_Pervasives.Inr (x,j) -> f x j
let liftM: 'a 'b . ('a -> 'b) -> 'a tm -> 'b tm =
  fun f  -> fun x  -> bind x (fun xx  -> return (f xx))
let liftM2: 'a 'b 'c . ('a -> 'b -> 'c) -> 'a tm -> 'b tm -> 'c tm =
  fun f  ->
    fun x  ->
      fun y  -> bind x (fun xx  -> bind y (fun yy  -> return (f xx yy)))
let liftM3:
  'a 'b 'c 'd . ('a -> 'b -> 'c -> 'd) -> 'a tm -> 'b tm -> 'c tm -> 'd tm =
  fun f  ->
    fun x  ->
      fun y  ->
        fun z  ->
          bind x
            (fun xx  ->
               bind y (fun yy  -> bind z (fun zz  -> return (f xx yy zz))))
let rec find_idx:
  'a .
    ('a -> Prims.bool) ->
      'a Prims.list ->
        (Prims.nat,'a) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> FStar_Pervasives_Native.None
      | x::xs ->
          if f x
          then FStar_Pervasives_Native.Some ((Prims.parse_int "0"), x)
          else
            (match find_idx f xs with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (i,x1) ->
                 FStar_Pervasives_Native.Some
                   ((i + (Prims.parse_int "1")), x1))
let atom: FStar_Reflection_Types.term -> expr tm =
  fun t  ->
    fun uu____2465  ->
      match uu____2465 with
      | (n,atoms) ->
          (match find_idx (FStar_Reflection_Basic.term_eq t) atoms with
           | FStar_Pervasives_Native.None  ->
               FStar_Pervasives.Inr
                 ((Atom (n, t)), ((n + (Prims.parse_int "1")), (t :: atoms)))
           | FStar_Pervasives_Native.Some (i,t1) ->
               FStar_Pervasives.Inr
                 ((Atom (((n - (Prims.parse_int "1")) - i), t1)), (n, atoms)))
let fail: 'Aa . Prims.string -> 'Aa tm =
  fun s  -> fun i  -> FStar_Pervasives.Inl s
let rec forall_list: 'a 'Ap . 'a Prims.list -> Obj.t =
  fun a289  -> (Obj.magic (fun l  -> ())) a289
let rec is_arith_expr: FStar_Reflection_Types.term -> expr tm =
  fun t  ->
    match FStar_Reflection_Syntax_Lemmas.collect_app_ref t with
    | (hd1,tl1) ->
        (match ((FStar_Reflection_Basic.inspect hd1), tl1) with
         | (FStar_Reflection_Data.Tv_FVar fv,e1::e2::e3::[]) ->
             if
               (FStar_Reflection_Basic.inspect_fv fv) =
                 FStar_Reflection_Syntax.land_qn
             then
               liftM2 (fun _0_2  -> fun _0_3  -> Land (_0_2, _0_3))
                 (is_arith_expr e2) (is_arith_expr e3)
             else
               if
                 (FStar_Reflection_Basic.inspect_fv fv) =
                   FStar_Reflection_Syntax.lxor_qn
               then
                 liftM2 (fun _0_4  -> fun _0_5  -> Lxor (_0_4, _0_5))
                   (is_arith_expr e2) (is_arith_expr e3)
               else
                 if
                   (FStar_Reflection_Basic.inspect_fv fv) =
                     FStar_Reflection_Syntax.lor_qn
                 then
                   liftM2 (fun _0_6  -> fun _0_7  -> Lor (_0_6, _0_7))
                     (is_arith_expr e2) (is_arith_expr e3)
                 else
                   if
                     (FStar_Reflection_Basic.inspect_fv fv) =
                       FStar_Reflection_Syntax.shiftr_qn
                   then
                     liftM2 (fun _0_8  -> fun _0_9  -> Shr (_0_8, _0_9))
                       (is_arith_expr e2) (is_arith_expr e3)
                   else
                     if
                       (FStar_Reflection_Basic.inspect_fv fv) =
                         FStar_Reflection_Syntax.shiftl_qn
                     then
                       liftM2
                         (fun _0_10  -> fun _0_11  -> Shl (_0_10, _0_11))
                         (is_arith_expr e2) (is_arith_expr e3)
                     else
                       if
                         (FStar_Reflection_Basic.inspect_fv fv) =
                           FStar_Reflection_Syntax.udiv_qn
                       then
                         liftM2
                           (fun _0_12  -> fun _0_13  -> Udiv (_0_12, _0_13))
                           (is_arith_expr e2) (is_arith_expr e3)
                       else
                         if
                           (FStar_Reflection_Basic.inspect_fv fv) =
                             FStar_Reflection_Syntax.umod_qn
                         then
                           liftM2
                             (fun _0_14  -> fun _0_15  -> Umod (_0_14, _0_15))
                             (is_arith_expr e2) (is_arith_expr e3)
                         else
                           if
                             (FStar_Reflection_Basic.inspect_fv fv) =
                               FStar_Reflection_Syntax.mul_mod_qn
                           then
                             liftM2
                               (fun _0_16  ->
                                  fun _0_17  -> MulMod (_0_16, _0_17))
                               (is_arith_expr e2) (is_arith_expr e3)
                           else
                             fail
                               (Prims.strcat "triary: "
                                  (FStar_Reflection_Syntax.fv_to_string fv))
         | (FStar_Reflection_Data.Tv_FVar fv,l::r::[]) ->
             if
               (FStar_Reflection_Basic.inspect_fv fv) =
                 FStar_Reflection_Syntax.add_qn
             then
               liftM2 (fun _0_18  -> fun _0_19  -> Plus (_0_18, _0_19))
                 (is_arith_expr l) (is_arith_expr r)
             else
               if
                 (FStar_Reflection_Basic.inspect_fv fv) =
                   FStar_Reflection_Syntax.minus_qn
               then
                 liftM2 (fun _0_20  -> fun _0_21  -> Minus (_0_20, _0_21))
                   (is_arith_expr l) (is_arith_expr r)
               else
                 if
                   (FStar_Reflection_Basic.inspect_fv fv) =
                     FStar_Reflection_Syntax.mult_qn
                 then
                   liftM2 (fun _0_22  -> fun _0_23  -> Mult (_0_22, _0_23))
                     (is_arith_expr l) (is_arith_expr r)
                 else
                   if
                     (FStar_Reflection_Basic.inspect_fv fv) =
                       FStar_Reflection_Syntax.mult'_qn
                   then
                     liftM2 (fun _0_24  -> fun _0_25  -> Mult (_0_24, _0_25))
                       (is_arith_expr l) (is_arith_expr r)
                   else
                     if
                       (FStar_Reflection_Basic.inspect_fv fv) =
                         FStar_Reflection_Syntax.nat_bv_qn
                     then
                       liftM (fun _0_26  -> NatToBv _0_26) (is_arith_expr r)
                     else
                       fail
                         (Prims.strcat "binary: "
                            (FStar_Reflection_Syntax.fv_to_string fv))
         | (FStar_Reflection_Data.Tv_FVar fv,a::[]) ->
             if
               (FStar_Reflection_Basic.inspect_fv fv) =
                 FStar_Reflection_Syntax.neg_qn
             then liftM (fun _0_27  -> Neg _0_27) (is_arith_expr a)
             else
               fail
                 (Prims.strcat "unary: "
                    (FStar_Reflection_Syntax.fv_to_string fv))
         | (FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int
            i),uu____2876) -> return (Lit i)
         | (FStar_Reflection_Data.Tv_FVar uu____2883,[]) -> atom t
         | (FStar_Reflection_Data.Tv_Var uu____2888,[]) -> atom t
         | (uu____2893,uu____2894) ->
             fail
               (Prims.strcat "unk ("
                  (Prims.strcat (FStar_Reflection_Basic.term_to_string t) ")")))
let rec is_arith_prop: FStar_Reflection_Types.term -> prop tm =
  fun t  ->
    match FStar_Reflection_Formula.term_as_formula t with
    | FStar_Reflection_Formula.Comp
        (FStar_Reflection_Formula.Eq ,uu____2953,l,r) ->
        liftM2 eq (is_arith_expr l) (is_arith_expr r)
    | FStar_Reflection_Formula.Comp
        (FStar_Reflection_Formula.BoolEq ,uu____2956,l,r) ->
        liftM2 eq (is_arith_expr l) (is_arith_expr r)
    | FStar_Reflection_Formula.Comp
        (FStar_Reflection_Formula.Lt ,uu____2959,l,r) ->
        liftM2 lt (is_arith_expr l) (is_arith_expr r)
    | FStar_Reflection_Formula.Comp
        (FStar_Reflection_Formula.Le ,uu____2962,l,r) ->
        liftM2 le (is_arith_expr l) (is_arith_expr r)
    | FStar_Reflection_Formula.And (l,r) ->
        liftM2 (fun _0_28  -> fun _0_29  -> AndProp (_0_28, _0_29))
          (is_arith_prop l) (is_arith_prop r)
    | FStar_Reflection_Formula.Or (l,r) ->
        liftM2 (fun _0_30  -> fun _0_31  -> OrProp (_0_30, _0_31))
          (is_arith_prop l) (is_arith_prop r)
    | uu____2969 ->
        fail
          (Prims.strcat "connector ("
             (Prims.strcat (FStar_Reflection_Basic.term_to_string t) ")"))
let run_tm: 'a . 'a tm -> (Prims.string,'a) FStar_Pervasives.either =
  fun m  ->
    match m ((Prims.parse_int "0"), []) with
    | FStar_Pervasives.Inl s -> FStar_Pervasives.Inl s
    | FStar_Pervasives.Inr (x,uu____3104) -> FStar_Pervasives.Inr x
let rec expr_to_string: expr -> Prims.string =
  fun e  ->
    match e with
    | Atom (i,uu____3143) -> Prims.strcat "a" (Prims.string_of_int i)
    | Lit i -> Prims.string_of_int i
    | Plus (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " + " (Prims.strcat (expr_to_string r) ")")))
    | Minus (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " - " (Prims.strcat (expr_to_string r) ")")))
    | Mult (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " * " (Prims.strcat (expr_to_string r) ")")))
    | Neg l -> Prims.strcat "(- " (Prims.strcat (expr_to_string l) ")")
    | Land (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " & " (Prims.strcat (expr_to_string r) ")")))
    | Lor (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " | " (Prims.strcat (expr_to_string r) ")")))
    | Lxor (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " ^ " (Prims.strcat (expr_to_string r) ")")))
    | Shl (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " << " (Prims.strcat (expr_to_string r) ")")))
    | Shr (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " >> " (Prims.strcat (expr_to_string r) ")")))
    | NatToBv l ->
        Prims.strcat "("
          (Prims.strcat "to_vec " (Prims.strcat (expr_to_string l) ")"))
    | Neg l -> Prims.strcat "~ " (expr_to_string l)
    | Udiv (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " / " (Prims.strcat (expr_to_string r) ")")))
    | Umod (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " % " (Prims.strcat (expr_to_string r) ")")))
    | MulMod (l,r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " ** " (Prims.strcat (expr_to_string r) ")")))
let rec compare_expr: expr -> expr -> FStar_Order.order =
  fun e1  ->
    fun e2  ->
      match (e1, e2) with
      | (Lit i,Lit j) -> FStar_Order.compare_int i j
      | (Atom (uu____3238,t),Atom (uu____3240,s)) ->
          FStar_Reflection_Syntax.compare_term t s
      | (Plus (l1,l2),Plus (r1,r2)) ->
          FStar_Order.lex (compare_expr l1 r1)
            (fun uu____3247  -> compare_expr l2 r2)
      | (Minus (l1,l2),Minus (r1,r2)) ->
          FStar_Order.lex (compare_expr l1 r1)
            (fun uu____3253  -> compare_expr l2 r2)
      | (Mult (l1,l2),Mult (r1,r2)) ->
          FStar_Order.lex (compare_expr l1 r1)
            (fun uu____3259  -> compare_expr l2 r2)
      | (Neg e11,Neg e21) -> compare_expr e11 e21
      | (Lit uu____3262,uu____3263) -> FStar_Order.Lt
      | (uu____3264,Lit uu____3265) -> FStar_Order.Gt
      | (Atom (uu____3266,uu____3267),uu____3268) -> FStar_Order.Lt
      | (uu____3269,Atom (uu____3270,uu____3271)) -> FStar_Order.Gt
      | (Plus (uu____3272,uu____3273),uu____3274) -> FStar_Order.Lt
      | (uu____3275,Plus (uu____3276,uu____3277)) -> FStar_Order.Gt
      | (Mult (uu____3278,uu____3279),uu____3280) -> FStar_Order.Lt
      | (uu____3281,Mult (uu____3282,uu____3283)) -> FStar_Order.Gt
      | (Neg uu____3284,uu____3285) -> FStar_Order.Lt
      | (uu____3286,Neg uu____3287) -> FStar_Order.Gt
      | uu____3288 -> FStar_Order.Gt