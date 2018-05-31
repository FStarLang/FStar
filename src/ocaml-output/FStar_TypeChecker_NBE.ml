open Prims
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun a  -> fun b  -> if a > b then a else b 
let map_rev : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____56 = let uu____59 = f x  in uu____59 :: acc  in
            aux xs uu____56
         in
      aux l []
  
let rec drop : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p  ->
    fun l  ->
      match l with
      | [] -> []
      | x::xs ->
          let uu____88 = p x  in if uu____88 then x :: xs else drop p xs
  
let (debug : (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun f  ->
    let uu____100 =
      FStar_Options.debug_at_level "Test" (FStar_Options.Other "NBE")  in
    if uu____100 then f () else ()
  
let (debug_term : FStar_Syntax_Syntax.term -> Prims.unit) =
  fun t  ->
    let uu____105 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____105
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> Prims.unit)
  =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____120 = FStar_Syntax_Print.sigelt_to_string_short v1  in
             FStar_Util.print2 "%s -> %%s\n" k uu____120) ()
  
let (primops : Prims.string Prims.list) =
  ["op_Minus";
  "op_Addition";
  "op_Subtraction";
  "op_GreaterThan";
  "equals";
  "op_Negation";
  "l_and";
  "l_or";
  "b2t"] 
type var = FStar_Syntax_Syntax.bv[@@deriving show]
type sort = Prims.int[@@deriving show]
type constant =
  | Unit 
  | Bool of Prims.bool 
  | Int of FStar_BigInt.t 
  | String of (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  
  | Char of FStar_Char.char [@@deriving show]
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____147 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____152 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____164 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____180 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____205 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
type atom =
  | Var of var 
  | Match of (t,t -> t,FStar_Syntax_Syntax.branch Prims.list)
  FStar_Pervasives_Native.tuple3 
  | Rec of
  (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
  t Prims.list) FStar_Pervasives_Native.tuple3 [@@deriving show]
and t =
  | Lam of (t -> t,t,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple3 
  | Accu of
  (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
          Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Construct of
  (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
  FStar_Pervasives_Native.tuple3 
  | Constant of constant 
  | Type_t of FStar_Syntax_Syntax.universe 
  | Univ of FStar_Syntax_Syntax.universe 
  | Unknown 
  | Refinement of (FStar_Syntax_Syntax.binder,t)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____320 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____342 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Rec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____394 -> false
  
let (__proj__Rec__item___0 :
  atom ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____444 -> false
  
let (__proj__Lam__item___0 :
  t -> (t -> t,t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____490 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____546 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____600 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____612 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____624 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____635 -> false
  
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____644 -> false
  
let (__proj__Refinement__item___0 :
  t -> (FStar_Syntax_Syntax.binder,t) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
type args =
  (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
type head = t[@@deriving show]
type annot = t FStar_Pervasives_Native.option[@@deriving show]
let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____681) -> FStar_Util.format1 "\"%s\"" s
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam uu____687 -> "Lam"
    | Accu (a,l) ->
        let uu____710 =
          let uu____711 = atom_to_string a  in
          let uu____712 =
            let uu____713 =
              let uu____714 =
                let uu____715 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____715  in
              Prims.strcat uu____714 ")"  in
            Prims.strcat ") (" uu____713  in
          Prims.strcat uu____711 uu____712  in
        Prims.strcat "Accu (" uu____710
    | Construct (fv,us,l) ->
        let uu____747 =
          let uu____748 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____749 =
            let uu____750 =
              let uu____751 =
                let uu____752 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____752  in
              let uu____755 =
                let uu____756 =
                  let uu____757 =
                    let uu____758 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____758  in
                  Prims.strcat uu____757 ")"  in
                Prims.strcat "] (" uu____756  in
              Prims.strcat uu____751 uu____755  in
            Prims.strcat ") [" uu____750  in
          Prims.strcat uu____748 uu____749  in
        Prims.strcat "Construct (" uu____747
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____773 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____773
    | Type_t u ->
        let uu____775 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____775
    | Refinement ((b,uu____777),t) ->
        let uu____783 =
          let uu____784 = FStar_Syntax_Print.bv_to_string b  in
          let uu____785 =
            let uu____786 =
              let uu____787 = t_to_string t  in Prims.strcat uu____787 ")"
               in
            Prims.strcat ", " uu____786  in
          Prims.strcat uu____784 uu____785  in
        Prims.strcat "Refinement (" uu____783
    | Unknown  -> "Unknown"

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____790 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____790
    | Match (t,uu____792,uu____793) ->
        let uu____802 = t_to_string t  in Prims.strcat "Match " uu____802
    | Rec (uu____803,uu____804,l) ->
        let uu____814 =
          let uu____815 =
            let uu____816 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____816  in
          Prims.strcat uu____815 ")"  in
        Prims.strcat "Rec (" uu____814

let (is_not_accu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____822,uu____823) -> false | uu____836 -> true
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
        -> t)
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts) 
let (mkAccuVar : var -> t) = fun v1  -> Accu ((Var v1), []) 
let (mkAccuMatch :
  t -> (t -> t) -> FStar_Syntax_Syntax.branch Prims.list -> t) =
  fun s  -> fun c  -> fun bs  -> Accu ((Match (s, c, bs)), []) 
let (mkAccuRec :
  FStar_Syntax_Syntax.letbinding ->
    FStar_Syntax_Syntax.letbinding Prims.list -> t Prims.list -> t)
  = fun b  -> fun bs  -> fun env  -> Accu ((Rec (b, bs, env)), []) 
let (isAccu : t -> Prims.bool) =
  fun trm  -> match trm with | Accu uu____949 -> true | uu____960 -> false 
let (pickBranch :
  t ->
    FStar_Syntax_Syntax.branch Prims.list ->
      (FStar_Syntax_Syntax.term,t Prims.list) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun scrut  ->
    fun branches  ->
      let rec pickBranch_aux scrut1 branches1 branches0 =
        let rec matches_pat scrutinee p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var bv -> FStar_Util.Inl [scrutinee]
          | FStar_Syntax_Syntax.Pat_wild bv -> FStar_Util.Inl [scrutinee]
          | FStar_Syntax_Syntax.Pat_dot_term uu____1046 -> FStar_Util.Inl []
          | FStar_Syntax_Syntax.Pat_constant s ->
              let matches_const c s1 =
                match c with
                | Constant (Unit ) -> s1 = FStar_Const.Const_unit
                | Constant (Bool b) ->
                    (match s1 with
                     | FStar_Const.Const_bool p1 -> b = p1
                     | uu____1065 -> false)
                | Constant (Int i) ->
                    (match s1 with
                     | FStar_Const.Const_int
                         (p1,FStar_Pervasives_Native.None ) ->
                         let uu____1078 = FStar_BigInt.big_int_of_string p1
                            in
                         i = uu____1078
                     | uu____1079 -> false)
                | Constant (String (st,uu____1081)) ->
                    (match s1 with
                     | FStar_Const.Const_string (p1,uu____1083) -> st = p1
                     | uu____1084 -> false)
                | Constant (Char c1) ->
                    (match s1 with
                     | FStar_Const.Const_char p1 -> c1 = p1
                     | uu____1089 -> false)
                | uu____1090 -> false  in
              let uu____1091 = matches_const scrutinee s  in
              if uu____1091 then FStar_Util.Inl [] else FStar_Util.Inr false
          | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
              let rec matches_args out a p1 =
                match (a, p1) with
                | ([],[]) -> FStar_Util.Inl out
                | ((t,uu____1206)::rest_a,(p2,uu____1209)::rest_p) ->
                    let uu____1243 = matches_pat t p2  in
                    (match uu____1243 with
                     | FStar_Util.Inl s ->
                         matches_args (FStar_List.append out s) rest_a rest_p
                     | m -> m)
                | uu____1268 -> FStar_Util.Inr false  in
              (match scrutinee with
               | Construct (fv',_us,args_rev) ->
                   let uu____1312 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                   if uu____1312
                   then matches_args [] (FStar_List.rev args_rev) arg_pats
                   else FStar_Util.Inr false
               | uu____1326 -> FStar_Util.Inr true)
           in
        match branches1 with
        | [] -> failwith "Branch not found"
        | (p,_wopt,e)::branches2 ->
            let uu____1395 = matches_pat scrut1 p  in
            (match uu____1395 with
             | FStar_Util.Inl matches ->
                 FStar_Pervasives_Native.Some (e, matches)
             | FStar_Util.Inr (false ) ->
                 pickBranch_aux scrut1 branches2 branches0
             | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
         in
      pickBranch_aux scrut branches branches
  
let rec test_args :
  'Auu____1442 .
    (t,'Auu____1442) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int -> Prims.bool
  =
  fun ts  ->
    fun cnt  ->
      match ts with
      | [] -> cnt <= (Prims.parse_int "0")
      | t::ts1 ->
          (Prims.op_Negation (isAccu (FStar_Pervasives_Native.fst t))) &&
            (test_args ts1 (cnt - (Prims.parse_int "1")))
  
let rec (count_abstractions : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    let uu____1486 =
      let uu____1487 = FStar_Syntax_Subst.compress t  in
      uu____1487.FStar_Syntax_Syntax.n  in
    match uu____1486 with
    | FStar_Syntax_Syntax.Tm_delayed uu____1490 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____1515 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_name uu____1516 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_fvar uu____1517 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_constant uu____1518 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_type uu____1519 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_arrow uu____1520 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uvar uu____1533 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_refine uu____1550 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_unknown  -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1558) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1565) ->
        let uu____1586 = count_abstractions body  in
        (FStar_List.length xs) + uu____1586
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1613 =
          let uu____1614 = count_abstractions head1  in
          uu____1614 - (FStar_List.length args)  in
        max uu____1613 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____1673,uu____1674,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____1723,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1742) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1748,uu____1749) ->
        count_abstractions t1
  
let (find_sigelt_in_gamma :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let mapper uu____1823 =
        match uu____1823 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                 FStar_Pervasives_Native.Some elt
             | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                 (debug
                    (fun uu____1908  ->
                       let uu____1909 = FStar_Syntax_Print.univs_to_string us
                          in
                       FStar_Util.print1
                         "Universes in local declaration: %s\n" uu____1909);
                  FStar_Pervasives_Native.Some elt)
             | uu____1910 -> FStar_Pervasives_Native.None)
         in
      let uu____1925 = FStar_TypeChecker_Env.lookup_qname env lid  in
      FStar_Util.bind_opt uu____1925 mapper
  
let (translate_univ : t Prims.list -> FStar_Syntax_Syntax.universe -> t) =
  fun bs  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar i ->
            let uu____1980 = FStar_List.nth bs i  in
            (match uu____1980 with | Univ u3 -> u3)
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1983 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1983
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1987 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1987
        | FStar_Syntax_Syntax.U_name uu____1990 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_unif uu____1991 ->
            failwith "Unknown or unconstrained universe"
        | FStar_Syntax_Syntax.U_unknown  ->
            failwith "Unknown or unconstrained universe"
         in
      let uu____2000 = aux u  in Univ uu____2000
  
let (is_univ : t -> Prims.bool) =
  fun tm  -> match tm with | Univ uu____2004 -> true | uu____2005 -> false 
let (un_univ : t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with | Univ u -> u | uu____2010 -> failwith "Not a universe"
  
let (make_rec_env :
  FStar_Syntax_Syntax.letbinding Prims.list -> t Prims.list -> t Prims.list)
  =
  fun lbs  ->
    fun bs  ->
      let rec aux lbs1 lbs0 bs1 bs0 =
        match lbs1 with
        | [] -> bs1
        | lb::lbs' -> aux lbs' lbs0 ((mkAccuRec lb lbs0 bs0) :: bs1) bs0  in
      aux lbs lbs bs bs
  
let (find_let :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.letbinding FStar_Pervasives_Native.option)
  =
  fun lbs  ->
    fun fvar1  ->
      FStar_Util.find_map lbs
        (fun lb  ->
           match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inl uu____2083 -> failwith "impossible"
           | FStar_Util.Inr name ->
               let uu____2087 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____2087
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
  
let rec (app : t -> t -> FStar_Syntax_Syntax.aqual -> t) =
  fun f  ->
    fun x  ->
      fun q  ->
        debug
          (fun uu____2161  ->
             let uu____2162 = t_to_string f  in
             let uu____2163 = t_to_string x  in
             FStar_Util.print2 "When creating app: %s applied to %s\n"
               uu____2162 uu____2163);
        (match f with
         | Lam (f1,uu____2165,uu____2166) -> f1 x
         | Accu (a,ts) -> Accu (a, ((x, q) :: ts))
         | Construct (i,us,ts) ->
             (match x with
              | Univ u -> Construct (i, (u :: us), ts)
              | uu____2223 -> Construct (i, us, ((x, q) :: ts)))
         | Refinement (b,r) ->
             let uu____2238 = let uu____2243 = app r x q  in (b, uu____2243)
                in
             Refinement uu____2238
         | Constant uu____2244 -> failwith "Ill-typed application"
         | Univ uu____2245 -> failwith "Ill-typed application"
         | Type_t uu____2246 -> failwith "Ill-typed application"
         | Unknown  -> failwith "Ill-typed application")

and (iapp :
  t ->
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
      -> t)
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____2259 ->
          let uu____2266 =
            let uu____2267 =
              let uu____2268 = FStar_List.hd args  in
              FStar_Pervasives_Native.fst uu____2268  in
            let uu____2277 =
              let uu____2278 = FStar_List.hd args  in
              FStar_Pervasives_Native.snd uu____2278  in
            app f uu____2267 uu____2277  in
          let uu____2287 = FStar_List.tl args  in iapp uu____2266 uu____2287

and (translate_fv :
  FStar_TypeChecker_Env.env -> t Prims.list -> FStar_Syntax_Syntax.fv -> t) =
  fun env  ->
    fun bs  ->
      fun fvar1  ->
        let find_in_sigtab env1 lid =
          FStar_Util.smap_try_find env1.FStar_TypeChecker_Env.sigtab
            (FStar_Ident.text_of_lid lid)
           in
        let uu____2314 =
          let uu____2319 =
            let uu____2324 =
              find_sigelt_in_gamma env
                (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____2327 =
              let uu____2332 =
                find_in_sigtab env
                  (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              [uu____2332]  in
            uu____2324 :: uu____2327  in
          FStar_List.find FStar_Util.is_some uu____2319  in
        match uu____2314 with
        | FStar_Pervasives_Native.Some elt ->
            (match elt with
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,lbs),names1);
                   FStar_Syntax_Syntax.sigrng = uu____2351;
                   FStar_Syntax_Syntax.sigquals = uu____2352;
                   FStar_Syntax_Syntax.sigmeta = uu____2353;
                   FStar_Syntax_Syntax.sigattrs = uu____2354;_}
                 ->
                 let lbm = find_let lbs fvar1  in
                 (match lbm with
                  | FStar_Pervasives_Native.Some lb ->
                      if is_rec
                      then mkAccuRec lb [] []
                      else
                        (debug
                           (fun uu____2381  ->
                              FStar_Util.print
                                "Translate fv: it's a Sig_let\n" []);
                         debug
                           (fun uu____2389  ->
                              let uu____2390 =
                                let uu____2391 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                FStar_Syntax_Print.tag_of_term uu____2391  in
                              let uu____2392 =
                                let uu____2393 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                FStar_Syntax_Print.term_to_string uu____2393
                                 in
                              FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                uu____2390 uu____2392);
                         debug
                           (fun uu____2401  ->
                              let uu____2402 =
                                let uu____2403 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                FStar_Syntax_Print.tag_of_term uu____2403  in
                              let uu____2404 =
                                let uu____2405 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                FStar_Syntax_Print.term_to_string uu____2405
                                 in
                              FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                uu____2402 uu____2404);
                         (let uu____2406 =
                            let uu____2407 =
                              FStar_Syntax_Print.lid_to_string
                                (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_List.mem uu____2407 primops  in
                          if uu____2406
                          then mkConstruct fvar1 [] []
                          else translate_letbinding env [] lb))
                  | FStar_Pervasives_Native.None  ->
                      failwith "Could not find mutually recursive definition")
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel =
                     FStar_Syntax_Syntax.Sig_datacon
                     (uu____2413,uu____2414,uu____2415,lid,uu____2417,[]);
                   FStar_Syntax_Syntax.sigrng = uu____2418;
                   FStar_Syntax_Syntax.sigquals = uu____2419;
                   FStar_Syntax_Syntax.sigmeta = uu____2420;
                   FStar_Syntax_Syntax.sigattrs = uu____2421;_}
                 ->
                 (debug
                    (fun uu____2433  ->
                       let uu____2434 = FStar_Syntax_Print.lid_to_string lid
                          in
                       FStar_Util.print1
                         "Translate fv %s: it's a Sig_datacon\n" uu____2434);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel =
                     FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,univs1,bs1,ty,uu____2443,uu____2444);
                   FStar_Syntax_Syntax.sigrng = uu____2445;
                   FStar_Syntax_Syntax.sigquals = uu____2446;
                   FStar_Syntax_Syntax.sigmeta = uu____2447;
                   FStar_Syntax_Syntax.sigattrs = uu____2448;_}
                 ->
                 (debug
                    (fun uu____2466  ->
                       let uu____2467 = FStar_Syntax_Print.lid_to_string lid
                          in
                       FStar_Util.print1
                         "Translate fv %s: it's a Sig_inductive_type\n"
                         uu____2467);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel =
                     FStar_Syntax_Syntax.Sig_declare_typ
                     (lid,uu____2473,uu____2474);
                   FStar_Syntax_Syntax.sigrng = uu____2475;
                   FStar_Syntax_Syntax.sigquals = uu____2476;
                   FStar_Syntax_Syntax.sigmeta = uu____2477;
                   FStar_Syntax_Syntax.sigattrs = uu____2478;_}
                 ->
                 (debug
                    (fun uu____2488  ->
                       let uu____2489 = FStar_Syntax_Print.lid_to_string lid
                          in
                       FStar_Util.print1
                         "Translate fv %s: it's a Sig_declare_typ\n"
                         uu____2489);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.None  ->
                 (debug
                    (fun uu____2497  ->
                       FStar_Util.print
                         "Translate fv: it's not in the environment\n" []);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.Some s ->
                 let uu____2503 =
                   let uu____2504 = FStar_Syntax_Print.sigelt_to_string s  in
                   FStar_Util.format1 "Sig %s\n" uu____2504  in
                 FStar_All.pipe_right uu____2503 failwith)
        | FStar_Pervasives_Native.None  -> mkConstruct fvar1 [] []

and (translate_letbinding :
  FStar_TypeChecker_Env.env ->
    t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)
  =
  fun env  ->
    fun bs  ->
      fun lb  ->
        let rec make_univ_abst us bs1 def =
          match us with
          | [] ->
              let translated_def = translate env bs1 def  in
              let translated_type =
                let uu____2536 =
                  let uu____2537 =
                    FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp
                     in
                  uu____2537.FStar_Syntax_Syntax.n  in
                match uu____2536 with
                | FStar_Syntax_Syntax.Tm_refine uu____2540 ->
                    let uu____2547 =
                      translate env bs1 lb.FStar_Syntax_Syntax.lbtyp  in
                    app uu____2547 translated_def
                      FStar_Pervasives_Native.None
                | uu____2548 -> Constant Unit  in
              (debug
                 (fun uu____2562  ->
                    let uu____2563 =
                      let uu____2564 =
                        FStar_Syntax_Subst.compress
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      uu____2564.FStar_Syntax_Syntax.n  in
                    match uu____2563 with
                    | FStar_Syntax_Syntax.Tm_refine uu____2567 ->
                        let readback_type = readback env translated_type  in
                        let uu____2575 = t_to_string translated_def  in
                        let uu____2576 =
                          FStar_Syntax_Print.term_to_string readback_type  in
                        FStar_Util.print2 "<<< Type of %s is %s\n" uu____2575
                          uu____2576
                    | uu____2577 -> ());
               translated_def)
          | u::us' ->
              Lam
                (((fun u1  -> make_univ_abst us' (u1 :: bs1) def)),
                  (Constant Unit), FStar_Pervasives_Native.None)
           in
        make_univ_abst lb.FStar_Syntax_Syntax.lbunivs bs
          lb.FStar_Syntax_Syntax.lbdef

and (translate_constant : FStar_Syntax_Syntax.sconst -> constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> Unit
    | FStar_Const.Const_bool b -> Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____2601 = FStar_BigInt.big_int_of_string s  in Int uu____2601
    | FStar_Const.Const_string (s,r) -> String (s, r)
    | FStar_Const.Const_char c1 -> Char c1
    | uu____2605 ->
        let uu____2606 =
          let uu____2607 =
            let uu____2608 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____2608 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____2607  in
        failwith uu____2606

and (translate_pat : FStar_Syntax_Syntax.pat -> t) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2611 = translate_constant c  in Constant uu____2611
    | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
        let uu____2630 =
          FStar_List.map
            (fun uu____2651  ->
               match uu____2651 with
               | (p1,uu____2663) ->
                   let uu____2664 = translate_pat p1  in
                   (uu____2664, FStar_Pervasives_Native.None)) pats
           in
        iapp (mkConstruct cfv [] []) uu____2630
    | FStar_Syntax_Syntax.Pat_var bvar -> mkAccuVar bvar
    | FStar_Syntax_Syntax.Pat_wild bvar -> mkAccuVar bvar
    | FStar_Syntax_Syntax.Pat_dot_term (bvar,t) ->
        failwith "Pat_dot_term not implemented"

and (translate :
  FStar_TypeChecker_Env.env -> t Prims.list -> FStar_Syntax_Syntax.term -> t)
  =
  fun env  ->
    fun bs  ->
      fun e  ->
        debug
          (fun uu____2691  ->
             let uu____2692 =
               let uu____2693 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2693  in
             let uu____2694 =
               let uu____2695 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2695  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2692 uu____2694);
        debug
          (fun uu____2701  ->
             let uu____2702 =
               let uu____2703 = FStar_List.map (fun x  -> t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____2703  in
             FStar_Util.print1 "BS list: %s\n" uu____2702);
        (let uu____2708 =
           let uu____2709 = FStar_Syntax_Subst.compress e  in
           uu____2709.FStar_Syntax_Syntax.n  in
         match uu____2708 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2712,uu____2713) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  -> Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2755 = translate_constant c  in Constant uu____2755
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug
                (fun uu____2772  ->
                   let uu____2773 = FStar_Syntax_Print.tag_of_term t  in
                   let uu____2774 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2775 =
                     let uu____2776 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2776
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print3 "Term with univs: %s - %s\nUniv %s\n"
                     uu____2773 uu____2774 uu____2775);
              (let uu____2781 = translate env bs t  in
               let uu____2782 = FStar_List.map (translate_univ bs) us  in
               FStar_List.fold_left
                 (fun head1  ->
                    fun u  -> app head1 u FStar_Pervasives_Native.None)
                 uu____2781 uu____2782))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2790 =
               let uu____2791 = translate_univ bs u  in un_univ uu____2791
                in
             Type_t uu____2790
         | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
             (debug_term e; failwith "Tm_arrow: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_refine (db,tm) ->
             Refinement
               ((db, FStar_Pervasives_Native.None),
                 (Lam
                    (((fun y  -> translate env (y :: bs) tm)),
                      (Constant Unit), FStar_Pervasives_Native.None)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2832,uu____2833) ->
             translate env bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____2902) -> translate env bs e1
         | FStar_Syntax_Syntax.Tm_name x -> mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2908,uu____2909) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (x::[],body,uu____2930) ->
             (debug
                (fun uu____2964  ->
                   let uu____2965 = FStar_Syntax_Print.tag_of_term body  in
                   let uu____2966 = FStar_Syntax_Print.term_to_string body
                      in
                   FStar_Util.print2 "Tm_abs body : %s - %s\n" uu____2965
                     uu____2966);
              (let x1 = FStar_Pervasives_Native.fst x  in
               let uu____2968 =
                 let uu____2977 =
                   translate env bs x1.FStar_Syntax_Syntax.sort  in
                 ((fun y  -> translate env (y :: bs) body), uu____2977,
                   (FStar_Pervasives_Native.snd x))
                  in
               Lam uu____2968))
         | FStar_Syntax_Syntax.Tm_abs (x::xs,body,uu____2985) ->
             let rest =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_abs
                    (xs, body, FStar_Pervasives_Native.None))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             let tm =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_abs
                    ([x], rest, FStar_Pervasives_Native.None))
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                in
             translate env bs tm
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv env bs fvar1
         | FStar_Syntax_Syntax.Tm_app (e1,[]) ->
             failwith "Impossible: application with no arguments"
         | FStar_Syntax_Syntax.Tm_app (e1,arg::[]) ->
             (debug
                (fun uu____3107  ->
                   let uu____3108 = FStar_Syntax_Print.term_to_string e1  in
                   let uu____3109 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg)
                      in
                   FStar_Util.print2 "Application %s / %s\n" uu____3108
                     uu____3109);
              (let uu____3112 = translate env bs e1  in
               let uu____3113 =
                 translate env bs (FStar_Pervasives_Native.fst arg)  in
               app uu____3112 uu____3113 (FStar_Pervasives_Native.snd arg)))
         | FStar_Syntax_Syntax.Tm_app (head1,arg::args) ->
             (debug
                (fun uu____3160  ->
                   let uu____3161 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3162 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg)
                      in
                   FStar_Util.print2 "Application %s / %s (...more agrs)\n"
                     uu____3161 uu____3162);
              (let first =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange
                  in
               let tm =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (first, args))
                   FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                  in
               translate env bs tm))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | Construct (c,us,args) ->
                   (debug
                      (fun uu____3269  ->
                         let uu____3270 =
                           let uu____3271 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3292  ->
                                     match uu____3292 with
                                     | (x,q) ->
                                         let uu____3305 = t_to_string x  in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3305))
                              in
                           FStar_All.pipe_right uu____3271
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3270);
                    (let uu____3309 = pickBranch scrut1 branches  in
                     match uu____3309 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____3330 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate env uu____3330 branch1
                     | FStar_Pervasives_Native.None  ->
                         mkAccuMatch scrut1 case branches))
               | Constant c ->
                   let uu____3348 = pickBranch scrut1 branches  in
                   (match uu____3348 with
                    | FStar_Pervasives_Native.Some (branch1,[]) ->
                        translate env bs branch1
                    | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                        translate env (arg :: bs) branch1
                    | FStar_Pervasives_Native.None  ->
                        mkAccuMatch scrut1 case branches
                    | FStar_Pervasives_Native.Some (uu____3382,hd1::tl1) ->
                        failwith
                          "Impossible: Matching on constants cannot bind more than one variable")
               | uu____3395 -> mkAccuMatch scrut1 case branches  in
             let uu____3396 = translate env bs scrut  in case uu____3396
         | FStar_Syntax_Syntax.Tm_let ((false ,lbs),body) ->
             let bs' =
               FStar_List.fold_left
                 (fun bs'  ->
                    fun lb  ->
                      let b = translate_letbinding env bs lb  in b :: bs') bs
                 lbs
                in
             translate env bs' body
         | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) ->
             let uu____3442 = make_rec_env lbs bs  in
             translate env uu____3442 body)

and (readback_primops :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun n1  ->
      fun args  ->
        debug
          (fun uu____3457  -> FStar_Util.print1 "Readback primop %s\n" n1);
        (let args1 =
           FStar_List.map
             (fun uu____3468  ->
                match uu____3468 with | (e,uu____3474) -> translate env [] e)
             args
            in
         match (n1, args1) with
         | ("op_Minus",(Constant (Int i))::[]) ->
             let uu____3480 =
               let uu____3481 =
                 let uu____3482 = FStar_BigInt.minus_big_int i  in
                 Int uu____3482  in
               Constant uu____3481  in
             readback env uu____3480
         | ("op_Addition",(Constant (Int i1))::(Constant (Int i2))::[]) ->
             let uu____3487 =
               let uu____3488 =
                 let uu____3489 = FStar_BigInt.add_big_int i1 i2  in
                 Int uu____3489  in
               Constant uu____3488  in
             readback env uu____3487
         | ("op_Subtraction",(Constant (Int i1))::(Constant (Int i2))::[]) ->
             let uu____3494 =
               let uu____3495 =
                 let uu____3496 = FStar_BigInt.sub_big_int i1 i2  in
                 Int uu____3496  in
               Constant uu____3495  in
             readback env uu____3494
         | ("op_GreaterThan",(Constant (Int i1))::(Constant (Int i2))::[]) ->
             let uu____3501 =
               let uu____3502 =
                 let uu____3503 = FStar_BigInt.gt_big_int i1 i2  in
                 Bool uu____3503  in
               Constant uu____3502  in
             readback env uu____3501
         | ("equals",typ::t1::t2::[]) ->
             let uu____3509 =
               let uu____3510 =
                 let uu____3511 =
                   let uu____3512 = readback env t1  in
                   let uu____3513 = readback env t2  in
                   uu____3512 = uu____3513  in
                 Bool uu____3511  in
               Constant uu____3510  in
             readback env uu____3509
         | ("op_Negation",(Constant (Bool b))::[]) ->
             readback env (Constant (Bool (Prims.op_Negation b)))
         | ("l_and",(Constant (Bool b1))::(Constant (Bool b2))::[]) ->
             readback env (Constant (Bool (b1 && b2)))
         | ("l_or",(Constant (Bool b1))::(Constant (Bool b2))::[]) ->
             readback env (Constant (Bool (b1 || b2)))
         | ("b2t",(Constant (Bool b))::[]) ->
             readback env (Constant (Bool b))
         | uu____3528 -> failwith "Bad primitive op application")

and (readback : FStar_TypeChecker_Env.env -> t -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun x  ->
      debug
        (fun uu____3542  ->
           let uu____3543 = t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____3543);
      (match x with
       | Univ u -> failwith "Readback of universes should not occur"
       | Unknown  ->
           FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | Constant (Unit ) -> FStar_Syntax_Syntax.unit_const
       | Constant (Bool (true )) -> FStar_Syntax_Util.exp_true_bool
       | Constant (Bool (false )) -> FStar_Syntax_Util.exp_false_bool
       | Constant (Int i) ->
           let uu____3546 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____3546 FStar_Syntax_Util.exp_int
       | Constant (String (s,r)) ->
           FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, r)))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | Constant (Char c) -> FStar_Syntax_Util.exp_char c
       | Type_t u ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | Lam (f,t,q) ->
           let x1 =
             let uu____3560 = readback env t  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____3560
              in
           let body =
             let uu____3562 = f (mkAccuVar x1)  in readback env uu____3562
              in
           FStar_Syntax_Util.abs [(x1, q)] body FStar_Pervasives_Native.None
       | Construct (fv,us,args_t) ->
           let args =
             map_rev
               (fun uu____3609  ->
                  match uu____3609 with
                  | (x1,q) ->
                      let uu____3620 = readback env x1  in (uu____3620, q))
               args_t
              in
           let apply1 tm =
             match args with
             | [] -> tm
             | uu____3637 -> FStar_Syntax_Util.mk_app tm args  in
           let fv_lid =
             FStar_Syntax_Print.lid_to_string
               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              in
           if FStar_List.mem fv_lid primops
           then readback_primops env fv_lid args
           else
             (match us with
              | uu____3646::uu____3647 ->
                  let uu____3650 =
                    let uu____3653 =
                      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3653
                      (FStar_List.rev us)
                     in
                  apply1 uu____3650
              | [] ->
                  let uu____3654 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  apply1 uu____3654)
       | Accu (Var bv,[]) -> FStar_Syntax_Syntax.bv_to_name bv
       | Accu (Var bv,ts) ->
           let args =
             map_rev
               (fun uu____3701  ->
                  match uu____3701 with
                  | (x1,q) ->
                      let uu____3712 = readback env x1  in (uu____3712, q))
               ts
              in
           let uu____3713 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____3713 args
       | Accu (Match (scrut,cases,branches),ts) ->
           let args =
             map_rev
               (fun uu____3759  ->
                  match uu____3759 with
                  | (x1,q) ->
                      let uu____3770 = readback env x1  in (uu____3770, q))
               ts
              in
           let head1 =
             let scrut_new = readback env scrut  in
             let branches_new =
               FStar_List.map
                 (fun uu____3815  ->
                    match uu____3815 with
                    | (pat,when_clause,uu____3840) ->
                        let uu____3853 =
                          let uu____3854 =
                            let uu____3855 = translate_pat pat  in
                            cases uu____3855  in
                          readback env uu____3854  in
                        (pat, when_clause, uu____3853)) branches
                in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_match (scrut_new, branches_new))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           (match ts with
            | [] -> head1
            | uu____3876 -> FStar_Syntax_Util.mk_app head1 args)
       | Accu (Rec (lb,lbs,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____3959 = curry hd1 args1  in
                 app uu____3959 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
              in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef  in
           let uu____3961 = test_args ts args_no  in
           if uu____3961
           then
             let uu____3962 =
               let uu____3963 =
                 let uu____3964 = make_rec_env lbs bs  in
                 translate_letbinding env uu____3964 lb  in
               curry uu____3963 ts  in
             readback env uu____3962
           else
             (let head1 =
                let f =
                  match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inl bv -> FStar_Syntax_Syntax.bv_to_name bv
                  | FStar_Util.Inr fv -> failwith "Not yet implemented"  in
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((true, lbs), f))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              let args =
                map_rev
                  (fun uu____4001  ->
                     match uu____4001 with
                     | (x1,q) ->
                         let uu____4012 = readback env x1  in (uu____4012, q))
                  ts
                 in
              match ts with
              | [] -> head1
              | uu____4017 -> FStar_Syntax_Util.mk_app head1 args)
       | Refinement (b,r) ->
           let body =
             let uu____4027 = readback env r  in translate env [] uu____4027
              in
           (debug
              (fun uu____4033  ->
                 let uu____4034 = t_to_string body  in
                 FStar_Util.print1 "Translated refinement body: %s\n"
                   uu____4034);
            (let uu____4035 =
               let uu____4038 =
                 let uu____4039 =
                   let uu____4046 = readback env body  in
                   ((FStar_Pervasives_Native.fst b), uu____4046)  in
                 FStar_Syntax_Syntax.Tm_refine uu____4039  in
               FStar_Syntax_Syntax.mk uu____4038  in
             uu____4035 FStar_Pervasives_Native.None FStar_Range.dummyRange)))

let (normalize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  -> let uu____4056 = translate env [] e  in readback env uu____4056
  