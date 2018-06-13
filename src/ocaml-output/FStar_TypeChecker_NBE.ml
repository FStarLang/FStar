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
            let uu____70 = let uu____73 = f x  in uu____73 :: acc  in
            aux xs uu____70
         in
      aux l []
  
let rec drop : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p  ->
    fun l  ->
      match l with
      | [] -> []
      | x::xs ->
          let uu____107 = p x  in if uu____107 then x :: xs else drop p xs
  
let (debug : FStar_TypeChecker_Normalize.cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____126 =
        let uu____127 = FStar_TypeChecker_Normalize.cfg_env cfg  in
        FStar_TypeChecker_Env.debug uu____127 (FStar_Options.Other "NBE")  in
      if uu____126 then f () else ()
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____134 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____134
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____151 = FStar_Syntax_Print.sigelt_to_string_short v1  in
             FStar_Util.print2 "%s -> %%s\n" k uu____151) ()
  
type var = FStar_Syntax_Syntax.bv
type sort = Prims.int
type constant =
  | Unit 
  | Bool of Prims.bool 
  | Int of FStar_BigInt.t 
  | String of (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  
  | Char of FStar_Char.char 
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____182 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____189 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____203 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____221 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____248 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
type atom =
  | Var of var 
  | Match of
  (t,(t -> FStar_Syntax_Syntax.term) -> FStar_Syntax_Syntax.branch Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Rec of
  (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
  t Prims.list) FStar_Pervasives_Native.tuple3 
and t =
  | Lam of (t -> t,unit -> t,FStar_Syntax_Syntax.aqual)
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
  FStar_Pervasives_Native.tuple2 
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____381 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____407 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,(t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Rec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____467 -> false
  
let (__proj__Rec__item___0 :
  atom ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____523 -> false
  
let (__proj__Lam__item___0 :
  t ->
    (t -> t,unit -> t,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____583 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____641 -> false
  
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
    match projectee with | Constant _0 -> true | uu____697 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____711 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____725 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____738 -> false
  
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____749 -> false
  
let (__proj__Refinement__item___0 :
  t -> (FStar_Syntax_Syntax.binder,t) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
type args =
  (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____788) -> FStar_Util.format1 "\"%s\"" s
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam uu____798 -> "Lam"
    | Accu (a,l) ->
        let uu____825 =
          let uu____826 = atom_to_string a  in
          let uu____827 =
            let uu____828 =
              let uu____829 =
                let uu____830 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____830  in
              Prims.strcat uu____829 ")"  in
            Prims.strcat ") (" uu____828  in
          Prims.strcat uu____826 uu____827  in
        Prims.strcat "Accu (" uu____825
    | Construct (fv,us,l) ->
        let uu____862 =
          let uu____863 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____864 =
            let uu____865 =
              let uu____866 =
                let uu____867 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____867  in
              let uu____870 =
                let uu____871 =
                  let uu____872 =
                    let uu____873 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____873  in
                  Prims.strcat uu____872 ")"  in
                Prims.strcat "] (" uu____871  in
              Prims.strcat uu____866 uu____870  in
            Prims.strcat ") [" uu____865  in
          Prims.strcat uu____863 uu____864  in
        Prims.strcat "Construct (" uu____862
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____888 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____888
    | Type_t u ->
        let uu____890 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____890
    | Refinement ((b,uu____892),t) ->
        let uu____894 =
          let uu____895 = FStar_Syntax_Print.bv_to_string b  in
          let uu____896 =
            let uu____897 =
              let uu____898 = t_to_string t  in Prims.strcat uu____898 ")"
               in
            Prims.strcat ", " uu____897  in
          Prims.strcat uu____895 uu____896  in
        Prims.strcat "Refinement (" uu____894
    | Unknown  -> "Unknown"

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____901 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____901
    | Match (t,uu____903) ->
        let uu____920 = t_to_string t  in Prims.strcat "Match " uu____920
    | Rec (uu____921,uu____922,l) ->
        let uu____932 =
          let uu____933 =
            let uu____934 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____934  in
          Prims.strcat uu____933 ")"  in
        Prims.strcat "Rec (" uu____932

let (is_not_accu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____942,uu____943) -> false | uu____956 -> true
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
        -> t)
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts) 
let (mkAccuVar : var -> t) = fun v1  -> Accu ((Var v1), []) 
let (mkAccuMatch :
  t ->
    ((t -> FStar_Syntax_Syntax.term) -> FStar_Syntax_Syntax.branch Prims.list)
      -> t)
  = fun s  -> fun bs  -> Accu ((Match (s, bs)), []) 
let (mkAccuRec :
  FStar_Syntax_Syntax.letbinding ->
    FStar_Syntax_Syntax.letbinding Prims.list -> t Prims.list -> t)
  = fun b  -> fun bs  -> fun env  -> Accu ((Rec (b, bs, env)), []) 
let (isAccu : t -> Prims.bool) =
  fun trm  -> match trm with | Accu uu____1095 -> true | uu____1106 -> false 
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____1206 -> FStar_Util.Inl []
          | FStar_Syntax_Syntax.Pat_constant s ->
              let matches_const c s1 =
                match c with
                | Constant (Unit ) -> s1 = FStar_Const.Const_unit
                | Constant (Bool b) ->
                    (match s1 with
                     | FStar_Const.Const_bool p1 -> b = p1
                     | uu____1229 -> false)
                | Constant (Int i) ->
                    (match s1 with
                     | FStar_Const.Const_int
                         (p1,FStar_Pervasives_Native.None ) ->
                         let uu____1242 = FStar_BigInt.big_int_of_string p1
                            in
                         i = uu____1242
                     | uu____1243 -> false)
                | Constant (String (st,uu____1245)) ->
                    (match s1 with
                     | FStar_Const.Const_string (p1,uu____1247) -> st = p1
                     | uu____1248 -> false)
                | Constant (Char c1) ->
                    (match s1 with
                     | FStar_Const.Const_char p1 -> c1 = p1
                     | uu____1254 -> false)
                | uu____1255 -> false  in
              let uu____1256 = matches_const scrutinee s  in
              if uu____1256 then FStar_Util.Inl [] else FStar_Util.Inr false
          | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
              let rec matches_args out a p1 =
                match (a, p1) with
                | ([],[]) -> FStar_Util.Inl out
                | ((t,uu____1377)::rest_a,(p2,uu____1380)::rest_p) ->
                    let uu____1414 = matches_pat t p2  in
                    (match uu____1414 with
                     | FStar_Util.Inl s ->
                         matches_args (FStar_List.append out s) rest_a rest_p
                     | m -> m)
                | uu____1439 -> FStar_Util.Inr false  in
              (match scrutinee with
               | Construct (fv',_us,args_rev) ->
                   let uu____1483 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                   if uu____1483
                   then matches_args [] (FStar_List.rev args_rev) arg_pats
                   else FStar_Util.Inr false
               | uu____1497 -> FStar_Util.Inr true)
           in
        match branches1 with
        | [] -> failwith "Branch not found"
        | (p,_wopt,e)::branches2 ->
            let uu____1538 = matches_pat scrut1 p  in
            (match uu____1538 with
             | FStar_Util.Inl matches ->
                 FStar_Pervasives_Native.Some (e, matches)
             | FStar_Util.Inr (false ) ->
                 pickBranch_aux scrut1 branches2 branches0
             | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
         in
      pickBranch_aux scrut branches branches
  
let rec test_args :
  'Auu____1583 .
    (t,'Auu____1583) FStar_Pervasives_Native.tuple2 Prims.list ->
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
    let uu____1631 =
      let uu____1632 = FStar_Syntax_Subst.compress t  in
      uu____1632.FStar_Syntax_Syntax.n  in
    match uu____1631 with
    | FStar_Syntax_Syntax.Tm_delayed uu____1635 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____1658 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_name uu____1659 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_fvar uu____1660 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_constant uu____1661 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_type uu____1662 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_arrow uu____1663 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uvar uu____1676 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_refine uu____1689 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_unknown  -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1697) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1704) ->
        let uu____1725 = count_abstractions body  in
        (FStar_List.length xs) + uu____1725
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1752 =
          let uu____1753 = count_abstractions head1  in
          uu____1753 - (FStar_List.length args)  in
        max uu____1752 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____1812,uu____1813,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____1862,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1881) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1887,uu____1888) ->
        count_abstractions t1
    | uu____1929 -> (Prims.parse_int "0")
  
let (find_sigelt_in_gamma :
  FStar_TypeChecker_Normalize.cfg ->
    FStar_TypeChecker_Env.env ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lid  ->
        let mapper uu____1974 =
          match uu____1974 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____2057  ->
                         let uu____2058 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____2058);
                    FStar_Pervasives_Native.Some elt)
               | uu____2059 -> FStar_Pervasives_Native.None)
           in
        let uu____2074 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____2074 mapper
  
let (is_univ : t -> Prims.bool) =
  fun tm  -> match tm with | Univ uu____2118 -> true | uu____2119 -> false 
let (un_univ : t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with | Univ u -> u | uu____2126 -> failwith "Not a universe"
  
let (translate_univ : t Prims.list -> FStar_Syntax_Syntax.universe -> t) =
  fun bs  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar i ->
            let u' = FStar_List.nth bs i  in un_univ u'
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2151 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2151
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2155 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2155
        | FStar_Syntax_Syntax.U_name uu____2158 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_unif uu____2159 ->
            failwith "Unknown or unconstrained universe"
        | FStar_Syntax_Syntax.U_unknown  ->
            failwith "Unknown or unconstrained universe"
         in
      let uu____2168 = aux u  in Univ uu____2168
  
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
           | FStar_Util.Inl uu____2257 -> failwith "impossible"
           | FStar_Util.Inr name ->
               let uu____2261 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____2261
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
  
let rec (app :
  FStar_TypeChecker_Normalize.cfg -> t -> t -> FStar_Syntax_Syntax.aqual -> t)
  =
  fun cfg  ->
    fun f  ->
      fun x  ->
        fun q  ->
          debug cfg
            (fun uu____2369  ->
               let uu____2370 = t_to_string f  in
               let uu____2371 = t_to_string x  in
               FStar_Util.print2 "When creating app: %s applied to %s\n"
                 uu____2370 uu____2371);
          (match f with
           | Lam (f1,uu____2373,uu____2374) -> f1 x
           | Accu (a,ts) -> Accu (a, ((x, q) :: ts))
           | Construct (i,us,ts) ->
               (match x with
                | Univ u -> Construct (i, (u :: us), ts)
                | uu____2439 -> Construct (i, us, ((x, q) :: ts)))
           | Refinement (b,r) ->
               let uu____2454 =
                 let uu____2459 = app cfg r x q  in (b, uu____2459)  in
               Refinement uu____2454
           | Constant uu____2460 -> failwith "Ill-typed application"
           | Univ uu____2461 -> failwith "Ill-typed application"
           | Type_t uu____2462 -> failwith "Ill-typed application"
           | Unknown  -> failwith "Ill-typed application")

and (iapp :
  FStar_TypeChecker_Normalize.cfg ->
    t ->
      (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
        -> t)
  =
  fun cfg  ->
    fun f  ->
      fun args  ->
        match args with
        | [] -> f
        | uu____2476 ->
            let uu____2483 =
              let uu____2484 =
                let uu____2485 = FStar_List.hd args  in
                FStar_Pervasives_Native.fst uu____2485  in
              let uu____2494 =
                let uu____2495 = FStar_List.hd args  in
                FStar_Pervasives_Native.snd uu____2495  in
              app cfg f uu____2484 uu____2494  in
            let uu____2504 = FStar_List.tl args  in
            iapp cfg uu____2483 uu____2504

and (translate_fv :
  FStar_TypeChecker_Normalize.cfg ->
    t Prims.list -> FStar_Syntax_Syntax.fv -> t)
  =
  fun cfg  ->
    fun bs  ->
      fun fvar1  ->
        let debug1 = debug cfg  in
        let qninfo =
          let uu____2529 = FStar_TypeChecker_Normalize.cfg_env cfg  in
          let uu____2530 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2529 uu____2530  in
        let uu____2531 =
          FStar_TypeChecker_Normalize.should_unfold cfg
            (fun uu____2533  -> false) fvar1 qninfo
           in
        match uu____2531 with
        | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
            failwith "Not yet handled"
        | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
            failwith "Not yet handled"
        | FStar_TypeChecker_Normalize.Should_unfold_no  ->
            (debug1
               (fun uu____2539  ->
                  let uu____2540 = FStar_Syntax_Print.fv_to_string fvar1  in
                  FStar_Util.print1 "(1) Decided to not unfold %s\n"
                    uu____2540);
             mkConstruct fvar1 [] [])
        | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
            (match qninfo with
             | FStar_Pervasives_Native.Some
                 (FStar_Util.Inr
                  ({
                     FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                       ((is_rec,lbs),names1);
                     FStar_Syntax_Syntax.sigrng = uu____2548;
                     FStar_Syntax_Syntax.sigquals = uu____2549;
                     FStar_Syntax_Syntax.sigmeta = uu____2550;
                     FStar_Syntax_Syntax.sigattrs = uu____2551;_},_us_opt),_rng)
                 ->
                 let lbm = find_let lbs fvar1  in
                 (match lbm with
                  | FStar_Pervasives_Native.Some lb ->
                      if is_rec
                      then mkAccuRec lb [] []
                      else
                        (debug1
                           (fun uu____2620  ->
                              FStar_Util.print
                                "Translate fv: it's a Sig_let\n" []);
                         debug1
                           (fun uu____2628  ->
                              let uu____2629 =
                                let uu____2630 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                FStar_Syntax_Print.tag_of_term uu____2630  in
                              let uu____2631 =
                                let uu____2632 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                FStar_Syntax_Print.term_to_string uu____2632
                                 in
                              FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                uu____2629 uu____2631);
                         debug1
                           (fun uu____2640  ->
                              let uu____2641 =
                                let uu____2642 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                FStar_Syntax_Print.tag_of_term uu____2642  in
                              let uu____2643 =
                                let uu____2644 =
                                  FStar_Syntax_Subst.compress
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                FStar_Syntax_Print.term_to_string uu____2644
                                 in
                              FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                uu____2641 uu____2643);
                         (let uu____2645 =
                            FStar_TypeChecker_Normalize.is_prim_step cfg
                              fvar1
                             in
                          if uu____2645
                          then mkConstruct fvar1 [] []
                          else translate_letbinding cfg [] lb))
                  | FStar_Pervasives_Native.None  ->
                      failwith "Could not find mutually recursive definition")
             | uu____2651 ->
                 (debug1
                    (fun uu____2657  ->
                       let uu____2658 = FStar_Syntax_Print.fv_to_string fvar1
                          in
                       FStar_Util.print1 "(2) Decided to not unfold %s\n"
                         uu____2658);
                  mkConstruct fvar1 [] []))

and (translate_letbinding :
  FStar_TypeChecker_Normalize.cfg ->
    t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)
  =
  fun cfg  ->
    fun bs  ->
      fun lb  ->
        let debug1 = debug cfg  in
        let rec make_univ_abst us bs1 def =
          match us with
          | [] ->
              let translated_def = translate cfg bs1 def  in
              let translated_type =
                let uu____2702 =
                  let uu____2703 =
                    FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp
                     in
                  uu____2703.FStar_Syntax_Syntax.n  in
                match uu____2702 with
                | FStar_Syntax_Syntax.Tm_refine uu____2706 ->
                    let uu____2713 =
                      translate cfg bs1 lb.FStar_Syntax_Syntax.lbtyp  in
                    app cfg uu____2713 translated_def
                      FStar_Pervasives_Native.None
                | uu____2714 -> Constant Unit  in
              (debug1
                 (fun uu____2728  ->
                    let uu____2729 =
                      let uu____2730 =
                        FStar_Syntax_Subst.compress
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      uu____2730.FStar_Syntax_Syntax.n  in
                    match uu____2729 with
                    | FStar_Syntax_Syntax.Tm_refine uu____2733 ->
                        let readback_type = readback cfg translated_type  in
                        let uu____2741 = t_to_string translated_def  in
                        let uu____2742 =
                          FStar_Syntax_Print.term_to_string readback_type  in
                        FStar_Util.print2 "<<< Type of %s is %s\n" uu____2741
                          uu____2742
                    | uu____2743 -> ());
               translated_def)
          | u::us' ->
              Lam
                (((fun univ  -> make_univ_abst us' (univ :: bs1) def)),
                  ((fun uu____2757  -> Constant Unit)),
                  FStar_Pervasives_Native.None)
           in
        make_univ_abst lb.FStar_Syntax_Syntax.lbunivs bs
          lb.FStar_Syntax_Syntax.lbdef

and (translate_constant : FStar_Syntax_Syntax.sconst -> constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> Unit
    | FStar_Const.Const_bool b -> Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____2771 = FStar_BigInt.big_int_of_string s  in Int uu____2771
    | FStar_Const.Const_string (s,r) -> String (s, r)
    | FStar_Const.Const_char c1 -> Char c1
    | uu____2776 ->
        let uu____2777 =
          let uu____2778 =
            let uu____2779 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____2779 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____2778  in
        failwith uu____2777

and (translate_pat :
  FStar_TypeChecker_Normalize.cfg -> FStar_Syntax_Syntax.pat -> t) =
  fun cfg  ->
    fun p  ->
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          let uu____2783 = translate_constant c  in Constant uu____2783
      | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
          let uu____2802 =
            FStar_List.map
              (fun uu____2823  ->
                 match uu____2823 with
                 | (p1,uu____2835) ->
                     let uu____2836 = translate_pat cfg p1  in
                     (uu____2836, FStar_Pervasives_Native.None)) pats
             in
          iapp cfg (mkConstruct cfv [] []) uu____2802
      | FStar_Syntax_Syntax.Pat_var bvar -> mkAccuVar bvar
      | FStar_Syntax_Syntax.Pat_wild bvar -> mkAccuVar bvar
      | FStar_Syntax_Syntax.Pat_dot_term (bvar,t) ->
          failwith "Pat_dot_term not implemented"

and (translate :
  FStar_TypeChecker_Normalize.cfg ->
    t Prims.list -> FStar_Syntax_Syntax.term -> t)
  =
  fun cfg  ->
    fun bs  ->
      fun e  ->
        let debug1 = debug cfg  in
        debug1
          (fun uu____2871  ->
             let uu____2872 =
               let uu____2873 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____2873  in
             let uu____2874 =
               let uu____2875 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____2875  in
             FStar_Util.print2 "Term: %s - %s\n" uu____2872 uu____2874);
        debug1
          (fun uu____2881  ->
             let uu____2882 =
               let uu____2883 = FStar_List.map (fun x  -> t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____2883  in
             FStar_Util.print1 "BS list: %s\n" uu____2882);
        (let uu____2888 =
           let uu____2889 = FStar_Syntax_Subst.compress e  in
           uu____2889.FStar_Syntax_Syntax.n  in
         match uu____2888 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2892,uu____2893) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  -> Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____2931 = translate_constant c  in Constant uu____2931
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____2948  ->
                   let uu____2949 = FStar_Syntax_Print.tag_of_term t  in
                   let uu____2950 = FStar_Syntax_Print.term_to_string t  in
                   let uu____2951 =
                     let uu____2952 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____2952
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print3 "Term with univs: %s - %s\nUniv %s\n"
                     uu____2949 uu____2950 uu____2951);
              (let uu____2957 = translate cfg bs t  in
               FStar_List.fold_left
                 (fun head1  ->
                    fun u  ->
                      let uu____2963 = translate_univ bs u  in
                      app cfg head1 uu____2963 FStar_Pervasives_Native.None)
                 uu____2957 us))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2965 =
               let uu____2966 = translate_univ bs u  in un_univ uu____2966
                in
             Type_t uu____2965
         | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
             (debug_term e; failwith "Tm_arrow: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_refine (db,tm) ->
             Refinement
               ((db, FStar_Pervasives_Native.None),
                 (Lam
                    (((fun y  -> translate cfg (y :: bs) tm)),
                      ((fun uu____3001  -> Constant Unit)),
                      FStar_Pervasives_Native.None)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3003,uu____3004) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____3065) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_name x -> mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____3071,uu____3072) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (x::[],body,uu____3093) ->
             (debug1
                (fun uu____3127  ->
                   let uu____3128 = FStar_Syntax_Print.tag_of_term body  in
                   let uu____3129 = FStar_Syntax_Print.term_to_string body
                      in
                   FStar_Util.print2 "Tm_abs body : %s - %s\n" uu____3128
                     uu____3129);
              (let x1 = FStar_Pervasives_Native.fst x  in
               Lam
                 ((fun y  -> translate cfg (y :: bs) body),
                   (fun uu____3140  ->
                      translate cfg bs x1.FStar_Syntax_Syntax.sort),
                   (FStar_Pervasives_Native.snd x))))
         | FStar_Syntax_Syntax.Tm_abs (x::xs,body,uu____3144) ->
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
             translate cfg bs tm
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app (e1,[]) ->
             failwith "Impossible: application with no arguments"
         | FStar_Syntax_Syntax.Tm_app (e1,arg::[]) ->
             (debug1
                (fun uu____3266  ->
                   let uu____3267 = FStar_Syntax_Print.term_to_string e1  in
                   let uu____3268 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg)
                      in
                   FStar_Util.print2 "Application %s / %s\n" uu____3267
                     uu____3268);
              (let uu____3271 = translate cfg bs e1  in
               let uu____3272 =
                 translate cfg bs (FStar_Pervasives_Native.fst arg)  in
               app cfg uu____3271 uu____3272
                 (FStar_Pervasives_Native.snd arg)))
         | FStar_Syntax_Syntax.Tm_app (head1,arg::args) ->
             (debug1
                (fun uu____3319  ->
                   let uu____3320 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3321 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg)
                      in
                   FStar_Util.print2 "Application %s / %s (...more agrs)\n"
                     uu____3320 uu____3321);
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
               translate cfg bs tm))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | Construct (c,us,args) ->
                   (debug1
                      (fun uu____3440  ->
                         let uu____3441 =
                           let uu____3442 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3465  ->
                                     match uu____3465 with
                                     | (x,q) ->
                                         let uu____3478 = t_to_string x  in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3478))
                              in
                           FStar_All.pipe_right uu____3442
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3441);
                    (let uu____3482 = pickBranch scrut1 branches  in
                     match uu____3482 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____3503 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____3503 branch1
                     | FStar_Pervasives_Native.None  ->
                         mkAccuMatch scrut1 make_branches))
               | Constant c ->
                   let uu____3521 = pickBranch scrut1 branches  in
                   (match uu____3521 with
                    | FStar_Pervasives_Native.Some (branch1,[]) ->
                        translate cfg bs branch1
                    | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                        translate cfg (arg :: bs) branch1
                    | FStar_Pervasives_Native.None  ->
                        mkAccuMatch scrut1 make_branches
                    | FStar_Pervasives_Native.Some (uu____3555,hd1::tl1) ->
                        failwith
                          "Impossible: Matching on constants cannot bind more than one variable")
               | uu____3568 -> mkAccuMatch scrut1 make_branches
             
             and make_branches readback1 =
               let rec process_pattern bs1 p =
                 let uu____3601 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____3635 =
                         FStar_List.fold_left
                           (fun uu____3673  ->
                              fun uu____3674  ->
                                match (uu____3673, uu____3674) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3755 = process_pattern bs2 arg
                                       in
                                    (match uu____3755 with
                                     | (bs',arg') ->
                                         (bs2, ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3635 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____3844 =
                           let uu____3845 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3845  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3844
                          in
                       (((mkAccuVar x) :: bs1),
                         (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____3850 =
                           let uu____3851 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3851  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3850
                          in
                       (((mkAccuVar x) :: bs1),
                         (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____3861 =
                           let uu____3862 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____3862  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____3861
                          in
                       let uu____3863 =
                         let uu____3864 =
                           let uu____3871 =
                             let uu____3874 = translate cfg bs1 tm  in
                             readback1 uu____3874  in
                           (x, uu____3871)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____3864  in
                       (((mkAccuVar x) :: bs1), uu____3863)
                    in
                 match uu____3601 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___241_3894 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___241_3894.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____3913  ->
                    match uu____3913 with
                    | (pat,when_clause,e1) ->
                        let uu____3935 = process_pattern bs pat  in
                        (match uu____3935 with
                         | (bs',pat') ->
                             let uu____3948 =
                               let uu____3949 =
                                 let uu____3952 = translate cfg bs' e1  in
                                 readback1 uu____3952  in
                               (pat', when_clause, uu____3949)  in
                             FStar_Syntax_Util.branch uu____3948)) branches
              in let uu____3961 = translate cfg bs scrut  in case uu____3961
         | FStar_Syntax_Syntax.Tm_let ((false ,lbs),body) ->
             let bs' =
               FStar_List.fold_left
                 (fun bs'  ->
                    fun lb  ->
                      let b = translate_letbinding cfg bs lb  in b :: bs') bs
                 lbs
                in
             translate cfg bs' body
         | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) ->
             let uu____4007 = make_rec_env lbs bs  in
             translate cfg uu____4007 body)

and (readback :
  FStar_TypeChecker_Normalize.cfg -> t -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____4025  ->
           let uu____4026 = t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____4026);
      (match x with
       | Univ u -> failwith "Readback of universes should not occur"
       | Unknown  ->
           FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | Constant (Unit ) -> FStar_Syntax_Syntax.unit_const
       | Constant (Bool (true )) -> FStar_Syntax_Util.exp_true_bool
       | Constant (Bool (false )) -> FStar_Syntax_Util.exp_false_bool
       | Constant (Int i) ->
           let uu____4029 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____4029 FStar_Syntax_Util.exp_int
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
             let uu____4051 =
               let uu____4052 = t ()  in readback cfg uu____4052  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____4051
              in
           let body =
             let uu____4054 = f (mkAccuVar x1)  in readback cfg uu____4054
              in
           FStar_Syntax_Util.abs [(x1, q)] body FStar_Pervasives_Native.None
       | Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____4101  ->
                  match uu____4101 with
                  | (x1,q) ->
                      let uu____4112 = readback cfg x1  in (uu____4112, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____4131 -> FStar_Syntax_Util.mk_app tm args1  in
           let tm uu____4145 =
             match us with
             | uu____4148::uu____4149 ->
                 let uu____4152 =
                   let uu____4155 =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                       FStar_Pervasives_Native.None FStar_Range.dummyRange
                      in
                   FStar_Syntax_Syntax.mk_Tm_uinst uu____4155
                     (FStar_List.rev us)
                    in
                 apply uu____4152
             | [] ->
                 let uu____4156 =
                   FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 apply uu____4156
              in
           let uu____4159 = FStar_TypeChecker_Normalize.find_prim_step cfg fv
              in
           (match uu____4159 with
            | FStar_Pervasives_Native.Some prim_step when
                prim_step.FStar_TypeChecker_Normalize.strong_reduction_ok ->
                let l = FStar_List.length args1  in
                let uu____4168 =
                  if l = prim_step.FStar_TypeChecker_Normalize.arity
                  then (args1, [])
                  else
                    FStar_List.splitAt
                      prim_step.FStar_TypeChecker_Normalize.arity args1
                   in
                (match uu____4168 with
                 | (args_1,args_2) ->
                     let psc =
                       {
                         FStar_TypeChecker_Normalize.psc_range =
                           FStar_Range.dummyRange;
                         FStar_TypeChecker_Normalize.psc_subst =
                           (fun uu____4254  ->
                              if
                                prim_step.FStar_TypeChecker_Normalize.requires_binder_substitution
                              then
                                failwith
                                  "Cannot handle primops that require substitution"
                              else [])
                       }  in
                     let uu____4256 =
                       prim_step.FStar_TypeChecker_Normalize.interpretation
                         psc args_1
                        in
                     (match uu____4256 with
                      | FStar_Pervasives_Native.Some tm1 ->
                          FStar_Syntax_Util.mk_app tm1 args_2
                      | FStar_Pervasives_Native.None  -> tm ()))
            | uu____4260 -> tm ())
       | Accu (Var bv,[]) -> FStar_Syntax_Syntax.bv_to_name bv
       | Accu (Var bv,ts) ->
           let args =
             map_rev
               (fun uu____4307  ->
                  match uu____4307 with
                  | (x1,q) ->
                      let uu____4318 = readback cfg x1  in (uu____4318, q))
               ts
              in
           let uu____4319 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____4319 args
       | Accu (Match (scrut,make_branches),ts) ->
           let args =
             map_rev
               (fun uu____4372  ->
                  match uu____4372 with
                  | (x1,q) ->
                      let uu____4383 = readback cfg x1  in (uu____4383, q))
               ts
              in
           let head1 =
             let scrut_new = readback cfg scrut  in
             let branches_new = make_branches (readback cfg)  in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_match (scrut_new, branches_new))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           (match ts with
            | [] -> head1
            | uu____4413 -> FStar_Syntax_Util.mk_app head1 args)
       | Accu (Rec (lb,lbs,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app cfg hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____4500 = curry hd1 args1  in
                 app cfg uu____4500 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
              in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef  in
           let uu____4502 = test_args ts args_no  in
           if uu____4502
           then
             let uu____4503 =
               let uu____4504 =
                 let uu____4505 = make_rec_env lbs bs  in
                 translate_letbinding cfg uu____4505 lb  in
               curry uu____4504 ts  in
             readback cfg uu____4503
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
                  (fun uu____4550  ->
                     match uu____4550 with
                     | (x1,q) ->
                         let uu____4561 = readback cfg x1  in (uu____4561, q))
                  ts
                 in
              match ts with
              | [] -> head1
              | uu____4566 -> FStar_Syntax_Util.mk_app head1 args)
       | Refinement (b,r) ->
           let body =
             let uu____4576 = readback cfg r  in translate cfg [] uu____4576
              in
           (debug1
              (fun uu____4582  ->
                 let uu____4583 = t_to_string body  in
                 FStar_Util.print1 "Translated refinement body: %s\n"
                   uu____4583);
            (let uu____4584 =
               let uu____4591 =
                 let uu____4592 =
                   let uu____4599 = readback cfg body  in
                   ((FStar_Pervasives_Native.fst b), uu____4599)  in
                 FStar_Syntax_Syntax.Tm_refine uu____4592  in
               FStar_Syntax_Syntax.mk uu____4591  in
             uu____4584 FStar_Pervasives_Native.None FStar_Range.dummyRange)))

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____4629 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____4636 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____4652 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____4672 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____4685 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____4691 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___240_4696  ->
    match uu___240_4696 with
    | Primops  -> FStar_TypeChecker_Env.Primops
    | UnfoldUntil d -> FStar_TypeChecker_Env.UnfoldUntil d
    | UnfoldOnly lids -> FStar_TypeChecker_Env.UnfoldOnly lids
    | UnfoldAttr attr -> FStar_TypeChecker_Env.UnfoldAttr attr
    | UnfoldTac  -> FStar_TypeChecker_Env.UnfoldTac
    | Reify  -> FStar_TypeChecker_Env.Reify
  
let (normalize :
  step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg =
          let uu____4722 = FStar_List.map step_as_normalizer_step steps  in
          FStar_TypeChecker_Normalize.config uu____4722 env  in
        let uu____4725 = translate cfg [] e  in readback cfg uu____4725
  
let (normalize' :
  FStar_TypeChecker_Env.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg = FStar_TypeChecker_Normalize.config steps env  in
        let uu____4746 = translate cfg [] e  in readback cfg uu____4746
  