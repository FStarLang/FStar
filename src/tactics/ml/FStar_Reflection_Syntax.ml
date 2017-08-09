open Prims
let rec flatten_name: FStar_Reflection_Types.name -> Prims.string =
  fun ns  ->
    match ns with
    | [] -> ""
    | n::[] -> n
    | n::ns1 -> Prims.strcat n (Prims.strcat "." (flatten_name ns1))
let imp_qn: Prims.string Prims.list = ["Prims"; "l_imp"]
let and_qn: Prims.string Prims.list = ["Prims"; "l_and"]
let or_qn: Prims.string Prims.list = ["Prims"; "l_or"]
let not_qn: Prims.string Prims.list = ["Prims"; "l_not"]
let iff_qn: Prims.string Prims.list = ["Prims"; "l_iff"]
let eq2_qn: Prims.string Prims.list = ["Prims"; "eq2"]
let eq1_qn: Prims.string Prims.list = ["Prims"; "eq"]
let true_qn: Prims.string Prims.list = ["Prims"; "l_True"]
let false_qn: Prims.string Prims.list = ["Prims"; "l_False"]
let b2t_qn: Prims.string Prims.list = ["Prims"; "b2t"]
let forall_qn: Prims.string Prims.list = ["Prims"; "l_Forall"]
let exists_qn: Prims.string Prims.list = ["Prims"; "l_Exists"]
let squash_qn: Prims.string Prims.list = ["Prims"; "squash"]
let bool_true_qn: Prims.string Prims.list = ["Prims"; "true"]
let bool_false_qn: Prims.string Prims.list = ["Prims"; "false"]
let int_lid: Prims.string Prims.list = ["Prims"; "int"]
let bool_lid: Prims.string Prims.list = ["Prims"; "bool"]
let unit_lid: Prims.string Prims.list = ["Prims"; "unit"]
let add_qn: Prims.string Prims.list = ["Prims"; "op_Addition"]
let neg_qn: Prims.string Prims.list = ["Prims"; "op_Minus"]
let minus_qn: Prims.string Prims.list = ["Prims"; "op_Subtraction"]
let mult_qn: Prims.string Prims.list = ["Prims"; "op_Multiply"]
let mult'_qn: Prims.string Prims.list = ["FStar"; "Mul"; "op_Star"]
let div_qn: Prims.string Prims.list = ["Prims"; "op_Division"]
let lt_qn: Prims.string Prims.list = ["Prims"; "op_LessThan"]
let lte_qn: Prims.string Prims.list = ["Prims"; "op_LessThanOrEqual"]
let gt_qn: Prims.string Prims.list = ["Prims"; "op_GreaterThan"]
let gte_qn: Prims.string Prims.list = ["Prims"; "op_GreaterThanOrEqual"]
let mod_qn: Prims.string Prims.list = ["Prims"; "op_Modulus"]
let land_qn: Prims.string Prims.list = ["FStar"; "UInt"; "logand"]
let lxor_qn: Prims.string Prims.list = ["FStar"; "UInt"; "logxor"]
let lor_qn: Prims.string Prims.list = ["FStar"; "UInt"; "logor"]
let shiftl_qn: Prims.string Prims.list = ["FStar"; "UInt"; "shift_left"]
let shiftr_qn: Prims.string Prims.list = ["FStar"; "UInt"; "shift_right"]
let udiv_qn: Prims.string Prims.list = ["FStar"; "UInt"; "udiv"]
let umod_qn: Prims.string Prims.list = ["FStar"; "UInt"; "mod"]
let mul_mod_qn: Prims.string Prims.list = ["FStar"; "UInt"; "mul_mod"]
let nat_bv_qn: Prims.string Prims.list = ["FStar"; "BV"; "int2bv"]
let rec collect_app':
  FStar_Reflection_Data.argv Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term,FStar_Reflection_Data.argv Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun args  ->
    fun t  ->
      match FStar_Reflection_Basic.inspect t with
      | FStar_Reflection_Data.Tv_App (l,r) -> collect_app' (r :: args) l
      | uu____121 -> (t, args)
let collect_app:
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term,FStar_Reflection_Data.argv Prims.list)
      FStar_Pervasives_Native.tuple2
  = collect_app' []
let rec mk_app:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Data.argv Prims.list -> FStar_Reflection_Types.term
  =
  fun t  ->
    fun args  ->
      match args with
      | [] -> t
      | x::xs ->
          mk_app
            (FStar_Reflection_Basic.pack
               (FStar_Reflection_Data.Tv_App (t, x))) xs
let mk_e_app:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list -> FStar_Reflection_Types.term
  =
  fun t  ->
    fun args  ->
      mk_app t
        (FStar_List_Tot_Base.map
           (fun t1  -> (t1, FStar_Reflection_Data.Q_Explicit)) args)
let rec collect_arr':
  FStar_Reflection_Types.typ Prims.list ->
    FStar_Reflection_Types.typ ->
      (FStar_Reflection_Types.typ,FStar_Reflection_Types.typ Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun typs  ->
    fun t  ->
      match FStar_Reflection_Basic.inspect t with
      | FStar_Reflection_Data.Tv_Arrow (b,r) ->
          collect_arr' ((FStar_Reflection_Basic.type_of_binder b) :: typs) r
      | uu____201 -> (t, typs)
let collect_arr:
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.typ,FStar_Reflection_Types.typ Prims.list)
      FStar_Pervasives_Native.tuple2
  = collect_arr' []
let rec eqlist:
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun f  ->
    fun xs  ->
      fun ys  ->
        match (xs, ys) with
        | ([],[]) -> true
        | (x::xs1,y::ys1) -> (f x y) && (eqlist f xs1 ys1)
        | uu____283 -> false
let fv_to_string: FStar_Reflection_Types.fv -> Prims.string =
  fun fv  -> FStar_String.concat "." (FStar_Reflection_Basic.inspect_fv fv)
let compare_fv:
  FStar_Reflection_Types.fv -> FStar_Reflection_Types.fv -> FStar_Order.order
  =
  fun f1  ->
    fun f2  ->
      FStar_Order.compare_list
        (fun s1  ->
           fun s2  -> FStar_Order.order_from_int (FStar_String.compare s1 s2))
        (FStar_Reflection_Basic.inspect_fv f1)
        (FStar_Reflection_Basic.inspect_fv f2)
let rec compare_const:
  FStar_Reflection_Data.vconst ->
    FStar_Reflection_Data.vconst -> FStar_Order.order
  =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (FStar_Reflection_Data.C_Unit ,FStar_Reflection_Data.C_Unit ) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_Int i,FStar_Reflection_Data.C_Int j) ->
          FStar_Order.order_from_int (i - j)
      | (FStar_Reflection_Data.C_True ,FStar_Reflection_Data.C_True ) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_False ,FStar_Reflection_Data.C_False ) ->
          FStar_Order.Eq
      | (FStar_Reflection_Data.C_String s1,FStar_Reflection_Data.C_String s2)
          -> FStar_Order.order_from_int (FStar_String.compare s1 s2)
      | (FStar_Reflection_Data.C_Unit ,uu____345) -> FStar_Order.Lt
      | (uu____346,FStar_Reflection_Data.C_Unit ) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_Int uu____347,uu____348) -> FStar_Order.Lt
      | (uu____349,FStar_Reflection_Data.C_Int uu____350) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_True ,uu____351) -> FStar_Order.Lt
      | (uu____352,FStar_Reflection_Data.C_True ) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_False ,uu____353) -> FStar_Order.Lt
      | (uu____354,FStar_Reflection_Data.C_False ) -> FStar_Order.Gt
      | (FStar_Reflection_Data.C_String uu____355,uu____356) ->
          FStar_Order.Lt
      | (uu____357,FStar_Reflection_Data.C_String uu____358) ->
          FStar_Order.Gt
let rec compare_term:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Order.order
  =
  fun s  ->
    fun t  ->
      match ((FStar_Reflection_Basic.inspect s),
              (FStar_Reflection_Basic.inspect t))
      with
      | (FStar_Reflection_Data.Tv_Var sv,FStar_Reflection_Data.Tv_Var tv) ->
          FStar_Reflection_Basic.compare_binder sv tv
      | (FStar_Reflection_Data.Tv_FVar sv,FStar_Reflection_Data.Tv_FVar tv)
          -> compare_fv sv tv
      | (FStar_Reflection_Data.Tv_App (h1,a1),FStar_Reflection_Data.Tv_App
         (h2,a2)) ->
          FStar_Order.lex (compare_term h1 h2)
            (fun uu____474  -> compare_argv a1 a2)
      | (FStar_Reflection_Data.Tv_Abs (b1,e1),FStar_Reflection_Data.Tv_Abs
         (b2,e2)) ->
          FStar_Order.lex (FStar_Reflection_Basic.compare_binder b1 b2)
            (fun uu____480  -> compare_term e1 e2)
      | (FStar_Reflection_Data.Tv_Arrow
         (b1,e1),FStar_Reflection_Data.Tv_Arrow (b2,e2)) ->
          FStar_Order.lex (FStar_Reflection_Basic.compare_binder b1 b2)
            (fun uu____486  -> compare_term e1 e2)
      | (FStar_Reflection_Data.Tv_Refine
         (b1,e1),FStar_Reflection_Data.Tv_Refine (b2,e2)) ->
          FStar_Order.lex (FStar_Reflection_Basic.compare_binder b1 b2)
            (fun uu____492  -> compare_term e1 e2)
      | (FStar_Reflection_Data.Tv_Type (),FStar_Reflection_Data.Tv_Type ())
          -> FStar_Order.Eq
      | (FStar_Reflection_Data.Tv_Const c1,FStar_Reflection_Data.Tv_Const c2)
          -> compare_const c1 c2
      | (FStar_Reflection_Data.Tv_Uvar
         (u1,uu____496),FStar_Reflection_Data.Tv_Uvar (u2,uu____498)) ->
          FStar_Order.compare_int u1 u2
      | (FStar_Reflection_Data.Tv_Match
         (uu____499,uu____500),FStar_Reflection_Data.Tv_Match
         (uu____501,uu____502)) -> FStar_Order.Eq
      | (FStar_Reflection_Data.Tv_Unknown ,FStar_Reflection_Data.Tv_Unknown )
          -> FStar_Order.Eq
      | (FStar_Reflection_Data.Tv_Var uu____507,uu____508) -> FStar_Order.Lt
      | (uu____509,FStar_Reflection_Data.Tv_Var uu____510) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_FVar uu____511,uu____512) -> FStar_Order.Lt
      | (uu____513,FStar_Reflection_Data.Tv_FVar uu____514) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_App (uu____515,uu____516),uu____517) ->
          FStar_Order.Lt
      | (uu____518,FStar_Reflection_Data.Tv_App (uu____519,uu____520)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Abs (uu____521,uu____522),uu____523) ->
          FStar_Order.Lt
      | (uu____524,FStar_Reflection_Data.Tv_Abs (uu____525,uu____526)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Arrow (uu____527,uu____528),uu____529) ->
          FStar_Order.Lt
      | (uu____530,FStar_Reflection_Data.Tv_Arrow (uu____531,uu____532)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Type (),uu____533) -> FStar_Order.Lt
      | (uu____534,FStar_Reflection_Data.Tv_Type ()) -> FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Refine (uu____535,uu____536),uu____537) ->
          FStar_Order.Lt
      | (uu____538,FStar_Reflection_Data.Tv_Refine (uu____539,uu____540)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Const uu____541,uu____542) ->
          FStar_Order.Lt
      | (uu____543,FStar_Reflection_Data.Tv_Const uu____544) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Uvar (uu____545,uu____546),uu____547) ->
          FStar_Order.Lt
      | (uu____548,FStar_Reflection_Data.Tv_Uvar (uu____549,uu____550)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Match (uu____551,uu____552),uu____553) ->
          FStar_Order.Lt
      | (uu____556,FStar_Reflection_Data.Tv_Match (uu____557,uu____558)) ->
          FStar_Order.Gt
      | (FStar_Reflection_Data.Tv_Unknown ,uu____561) -> FStar_Order.Lt
      | (uu____562,FStar_Reflection_Data.Tv_Unknown ) -> FStar_Order.Gt
and compare_argv:
  FStar_Reflection_Data.argv ->
    FStar_Reflection_Data.argv -> FStar_Order.order
  =
  fun a1  ->
    fun a2  ->
      match a1 with
      | (a11,q1) ->
          (match a2 with
           | (a21,q2) ->
               (match (q1, q2) with
                | (FStar_Reflection_Data.Q_Implicit
                   ,FStar_Reflection_Data.Q_Explicit ) -> FStar_Order.Lt
                | (FStar_Reflection_Data.Q_Explicit
                   ,FStar_Reflection_Data.Q_Implicit ) -> FStar_Order.Gt
                | (uu____569,uu____570) -> compare_term a11 a21))