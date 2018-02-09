open Prims
let max: Prims.int -> Prims.int -> Prims.int =
  fun a  -> fun b  -> if a > b then a else b
let map_rev: 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____56 = let uu____59 = f x in uu____59 :: acc in
            aux xs uu____56 in
      aux l []
let rec drop: 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p  ->
    fun l  ->
      match l with
      | [] -> []
      | x::xs ->
          let uu____88 = p x in if uu____88 then x :: xs else drop p xs
let debug: (Prims.unit -> Prims.unit) -> Prims.unit =
  fun f  ->
    let uu____100 =
      FStar_Options.debug_at_level "Test" (FStar_Options.Other "NBE") in
    if uu____100 then f () else ()
let debug_term: FStar_Syntax_Syntax.term -> Prims.unit =
  fun t  ->
    let uu____105 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.print1 "%s\n" uu____105
let debug_sigmap: FStar_Syntax_Syntax.sigelt FStar_Util.smap -> Prims.unit =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____120 = FStar_Syntax_Print.sigelt_to_string_short v1 in
             FStar_Util.print2 "%s -> %%s\n" k uu____120) ()
type var = FStar_Syntax_Syntax.bv[@@deriving show]
type sort = Prims.int[@@deriving show]
type atom =
  | Var of var
  | Match of (t,t -> t) FStar_Pervasives_Native.tuple2
  | Rec of (FStar_Syntax_Syntax.letbinding,t Prims.list)
  FStar_Pervasives_Native.tuple2[@@deriving show]
and t =
  | Lam of (t -> t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
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
  | Unit
  | Bool of Prims.bool
  | Type_t of FStar_Syntax_Syntax.universe
  | Univ of FStar_Syntax_Syntax.universe[@@deriving show]
let uu___is_Var: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____207 -> false
let __proj__Var__item___0: atom -> var =
  fun projectee  -> match projectee with | Var _0 -> _0
let uu___is_Match: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____225 -> false
let __proj__Match__item___0:
  atom -> (t,t -> t) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Rec: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____261 -> false
let __proj__Rec__item___0:
  atom ->
    (FStar_Syntax_Syntax.letbinding,t Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Rec _0 -> _0
let uu___is_Lam: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____297 -> false
let __proj__Lam__item___0:
  t -> (t -> t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Lam _0 -> _0
let uu___is_Accu: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____337 -> false
let __proj__Accu__item___0:
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Accu _0 -> _0
let uu___is_Construct: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____393 -> false
let __proj__Construct__item___0:
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Construct _0 -> _0
let uu___is_Unit: t -> Prims.bool =
  fun projectee  -> match projectee with | Unit  -> true | uu____446 -> false
let uu___is_Bool: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____451 -> false
let __proj__Bool__item___0: t -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
let uu___is_Type_t: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____463 -> false
let __proj__Type_t__item___0: t -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Type_t _0 -> _0
let uu___is_Univ: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____475 -> false
let __proj__Univ__item___0: t -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
type head = t[@@deriving show]
type annot = t FStar_Pervasives_Native.option[@@deriving show]
let rec t_to_string: t -> Prims.string =
  fun x  ->
    match x with
    | Lam uu____490 -> "Lam"
    | Accu (a,l) ->
        let uu____511 =
          let uu____512 = atom_to_string a in
          let uu____513 =
            let uu____514 =
              let uu____515 =
                let uu____516 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l in
                FStar_String.concat "; " uu____516 in
              Prims.strcat uu____515 ")" in
            Prims.strcat ") (" uu____514 in
          Prims.strcat uu____512 uu____513 in
        Prims.strcat "Accu (" uu____511
    | Construct (fv,us,l) ->
        let uu____548 =
          let uu____549 = FStar_Syntax_Print.fv_to_string fv in
          let uu____550 =
            let uu____551 =
              let uu____552 =
                let uu____553 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us in
                FStar_String.concat "; " uu____553 in
              let uu____556 =
                let uu____557 =
                  let uu____558 =
                    let uu____559 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l in
                    FStar_String.concat "; " uu____559 in
                  Prims.strcat uu____558 ")" in
                Prims.strcat "] (" uu____557 in
              Prims.strcat uu____552 uu____556 in
            Prims.strcat ") [" uu____551 in
          Prims.strcat uu____549 uu____550 in
        Prims.strcat "Construct (" uu____548
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Univ u ->
        let uu____575 = FStar_Syntax_Print.univ_to_string u in
        Prims.strcat "Universe " uu____575
    | Type_t u ->
        let uu____577 = FStar_Syntax_Print.univ_to_string u in
        Prims.strcat "Type_t " uu____577
and atom_to_string: atom -> Prims.string =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____580 = FStar_Syntax_Print.bv_to_string v1 in
        Prims.strcat "Var " uu____580
    | Match (t,uu____582) ->
        let uu____587 = t_to_string t in Prims.strcat "Match " uu____587
    | Rec (uu____588,l) ->
        let uu____594 =
          let uu____595 =
            let uu____596 = FStar_List.map t_to_string l in
            FStar_String.concat "; " uu____596 in
          Prims.strcat uu____595 ")" in
        Prims.strcat "Rec (" uu____594
let is_not_accu: t -> Prims.bool =
  fun x  ->
    match x with | Accu (uu____602,uu____603) -> false | uu____616 -> true
let mkConstruct:
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list ->
      (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
        -> t
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts)
let mkAccuVar: var -> t = fun v1  -> Accu ((Var v1), [])
let mkAccuMatch: t -> (t -> t) -> t =
  fun s  -> fun c  -> Accu ((Match (s, c)), [])
let mkAccuRec: FStar_Syntax_Syntax.letbinding -> t Prims.list -> t =
  fun b  -> fun env  -> Accu ((Rec (b, env)), [])
let isAccu: t -> Prims.bool =
  fun trm  -> match trm with | Accu uu____711 -> true | uu____722 -> false
let rec pickBranch:
  t ->
    FStar_Syntax_Syntax.branch Prims.list ->
      (FStar_Syntax_Syntax.term,t Prims.list) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun scrut  ->
    fun branches  ->
      let rec matches_pat scrutinee p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_var bv -> FStar_Util.Inl [scrutinee]
        | FStar_Syntax_Syntax.Pat_wild bv -> FStar_Util.Inl [scrutinee]
        | FStar_Syntax_Syntax.Pat_dot_term uu____774 -> FStar_Util.Inl []
        | FStar_Syntax_Syntax.Pat_constant s ->
            failwith
              "Constant patterns are not yet supported; should be easy"
        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
            let rec matches_args out a p1 =
              match (a, p1) with
              | ([],[]) -> FStar_Util.Inl out
              | ((t,uu____893)::rest_a,(p2,uu____896)::rest_p) ->
                  let uu____930 = matches_pat t p2 in
                  (match uu____930 with
                   | FStar_Util.Inl s ->
                       matches_args (FStar_List.append out s) rest_a rest_p
                   | m -> m)
              | uu____955 -> FStar_Util.Inr false in
            (match scrutinee with
             | Construct (fv',_us,args_rev) ->
                 let uu____999 = FStar_Syntax_Syntax.fv_eq fv fv' in
                 if uu____999
                 then matches_args [] (FStar_List.rev args_rev) arg_pats
                 else FStar_Util.Inr false
             | uu____1013 -> FStar_Util.Inr true) in
      match branches with
      | [] -> failwith "Branch not found"
      | (p,_wopt,e)::branches1 ->
          let uu____1082 = matches_pat scrut p in
          (match uu____1082 with
           | FStar_Util.Inl matches ->
               FStar_Pervasives_Native.Some (e, matches)
           | FStar_Util.Inr (false ) -> pickBranch scrut branches1
           | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
let rec test_args:
  'Auu____1129 .
    (t,'Auu____1129) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int -> Prims.bool
  =
  fun ts  ->
    fun cnt  ->
      match ts with
      | [] -> cnt <= (Prims.parse_int "0")
      | t::ts1 ->
          (Prims.op_Negation (isAccu (FStar_Pervasives_Native.fst t))) &&
            (test_args ts1 (cnt - (Prims.parse_int "1")))
let rec count_abstractions: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    let uu____1173 =
      let uu____1174 = FStar_Syntax_Subst.compress t in
      uu____1174.FStar_Syntax_Syntax.n in
    match uu____1173 with
    | FStar_Syntax_Syntax.Tm_delayed uu____1177 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____1202 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_name uu____1203 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_fvar uu____1204 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_constant uu____1205 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_type uu____1206 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_arrow uu____1207 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_uvar uu____1220 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_refine uu____1237 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_unknown  -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1245) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1252) ->
        let uu____1273 = count_abstractions body in
        (FStar_List.length xs) + uu____1273
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1300 =
          let uu____1301 = count_abstractions head1 in
          uu____1301 - (FStar_List.length args) in
        max uu____1300 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____1360,uu____1361,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____1410,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1429) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1435,uu____1436) ->
        count_abstractions t1
let find_sigelt_in_gamma:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____1510 =
        match uu____1510 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                 FStar_Pervasives_Native.Some elt
             | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                 (debug
                    (fun uu____1595  ->
                       let uu____1596 = FStar_Syntax_Print.univs_to_string us in
                       FStar_Util.print1
                         "Universes in local declaration: %s\n" uu____1596);
                  FStar_Pervasives_Native.Some elt)
             | uu____1597 -> FStar_Pervasives_Native.None) in
      let uu____1612 = FStar_TypeChecker_Env.lookup_qname env lid in
      FStar_Util.bind_opt uu____1612 mapper
let translate_univ: t Prims.list -> FStar_Syntax_Syntax.universe -> t =
  fun bs  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar i ->
            let uu____1667 = FStar_List.nth bs i in
            (match uu____1667 with | Univ u3 -> u3)
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1670 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1670
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1674 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1674
        | FStar_Syntax_Syntax.U_name uu____1677 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_unif uu____1678 ->
            failwith "Unknown or unconstrained universe"
        | FStar_Syntax_Syntax.U_unknown  ->
            failwith "Unknown or unconstrained universe" in
      let uu____1687 = aux u in Univ uu____1687
let is_univ: t -> Prims.bool =
  fun tm  -> match tm with | Univ uu____1691 -> true | uu____1692 -> false
let un_univ: t -> FStar_Syntax_Syntax.universe =
  fun tm  ->
    match tm with | Univ u -> u | uu____1697 -> failwith "Not a universe"
let rec app: t -> t -> FStar_Syntax_Syntax.aqual -> t =
  fun f  ->
    fun x  ->
      fun q  ->
        debug
          (fun uu____1752  ->
             let uu____1753 = t_to_string f in
             let uu____1754 = t_to_string x in
             FStar_Util.print2 "When creating app: %s applied to %s\n"
               uu____1753 uu____1754);
        (match f with
         | Lam (f1,uu____1756) -> f1 x
         | Accu (a,ts) -> Accu (a, ((x, q) :: ts))
         | Construct (i,us,ts) ->
             (match x with
              | Univ u -> Construct (i, (u :: us), ts)
              | uu____1813 -> Construct (i, us, ((x, q) :: ts)))
         | Unit  -> failwith "Ill-typed application"
         | Bool uu____1826 -> failwith "Ill-typed application"
         | Univ uu____1827 -> failwith "Ill-typed application"
         | Type_t uu____1828 -> failwith "Ill-typed application")
and iapp:
  t ->
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
      -> t
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____1841 ->
          let uu____1848 =
            let uu____1849 =
              let uu____1850 = FStar_List.hd args in
              FStar_Pervasives_Native.fst uu____1850 in
            let uu____1859 =
              let uu____1860 = FStar_List.hd args in
              FStar_Pervasives_Native.snd uu____1860 in
            app f uu____1849 uu____1859 in
          let uu____1869 = FStar_List.tl args in iapp uu____1848 uu____1869
and translate_fv:
  FStar_TypeChecker_Env.env -> t Prims.list -> FStar_Syntax_Syntax.fv -> t =
  fun env  ->
    fun bs  ->
      fun fvar1  ->
        let find_in_sigtab env1 lid =
          FStar_Util.smap_try_find env1.FStar_TypeChecker_Env.sigtab
            (FStar_Ident.text_of_lid lid) in
        let uu____1896 =
          let uu____1901 =
            let uu____1906 =
              find_sigelt_in_gamma env
                (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____1909 =
              let uu____1914 =
                find_in_sigtab env
                  (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              [uu____1914] in
            uu____1906 :: uu____1909 in
          FStar_List.find FStar_Util.is_some uu____1901 in
        match uu____1896 with
        | FStar_Pervasives_Native.Some elt ->
            (match elt with
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,lb::[]),uu____1932);
                   FStar_Syntax_Syntax.sigrng = uu____1933;
                   FStar_Syntax_Syntax.sigquals = uu____1934;
                   FStar_Syntax_Syntax.sigmeta = uu____1935;
                   FStar_Syntax_Syntax.sigattrs = uu____1936;_}
                 ->
                 if is_rec
                 then mkAccuRec lb []
                 else
                   (debug
                      (fun uu____1957  ->
                         FStar_Util.print "Translate fv: it's a Sig_let\n" []);
                    debug
                      (fun uu____1965  ->
                         let uu____1966 =
                           let uu____1967 =
                             FStar_Syntax_Subst.compress
                               lb.FStar_Syntax_Syntax.lbtyp in
                           FStar_Syntax_Print.tag_of_term uu____1967 in
                         let uu____1968 =
                           let uu____1969 =
                             FStar_Syntax_Subst.compress
                               lb.FStar_Syntax_Syntax.lbtyp in
                           FStar_Syntax_Print.term_to_string uu____1969 in
                         FStar_Util.print2 "Type of lbdef: %s - %s\n"
                           uu____1966 uu____1968);
                    debug
                      (fun uu____1977  ->
                         let uu____1978 =
                           let uu____1979 =
                             FStar_Syntax_Subst.compress
                               lb.FStar_Syntax_Syntax.lbdef in
                           FStar_Syntax_Print.tag_of_term uu____1979 in
                         let uu____1980 =
                           let uu____1981 =
                             FStar_Syntax_Subst.compress
                               lb.FStar_Syntax_Syntax.lbdef in
                           FStar_Syntax_Print.term_to_string uu____1981 in
                         FStar_Util.print2 "Body of lbdef: %s - %s\n"
                           uu____1978 uu____1980);
                    translate_letbinding env [] lb)
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel =
                     FStar_Syntax_Syntax.Sig_datacon
                     (uu____1982,uu____1983,uu____1984,lid,uu____1986,[]);
                   FStar_Syntax_Syntax.sigrng = uu____1987;
                   FStar_Syntax_Syntax.sigquals = uu____1988;
                   FStar_Syntax_Syntax.sigmeta = uu____1989;
                   FStar_Syntax_Syntax.sigattrs = uu____1990;_}
                 ->
                 (debug
                    (fun uu____2002  ->
                       let uu____2003 = FStar_Syntax_Print.lid_to_string lid in
                       FStar_Util.print1
                         "Translate fv %s: it's a Sig_datacon\n" uu____2003);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.Some
                 {
                   FStar_Syntax_Syntax.sigel =
                     FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,univs1,bs1,ty,uu____2012,uu____2013);
                   FStar_Syntax_Syntax.sigrng = uu____2014;
                   FStar_Syntax_Syntax.sigquals = uu____2015;
                   FStar_Syntax_Syntax.sigmeta = uu____2016;
                   FStar_Syntax_Syntax.sigattrs = uu____2017;_}
                 ->
                 (debug
                    (fun uu____2035  ->
                       let uu____2036 = FStar_Syntax_Print.lid_to_string lid in
                       FStar_Util.print1
                         "Translate fv %s: it's a Sig_inductive_type\n"
                         uu____2036);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.None  ->
                 (debug
                    (fun uu____2044  ->
                       FStar_Util.print
                         "Translate fv: it's not in the environment\n" []);
                  mkConstruct fvar1 [] [])
             | FStar_Pervasives_Native.Some s ->
                 let uu____2050 =
                   let uu____2051 = FStar_Syntax_Print.sigelt_to_string s in
                   FStar_Util.format1 "Sig %s\n" uu____2051 in
                 FStar_All.pipe_right uu____2050 failwith)
        | FStar_Pervasives_Native.None  -> mkConstruct fvar1 [] []
and translate_letbinding:
  FStar_TypeChecker_Env.env ->
    t Prims.list -> FStar_Syntax_Syntax.letbinding -> t
  =
  fun env  ->
    fun bs  ->
      fun lb  ->
        let rec make_univ_abst us bs1 def =
          match us with
          | [] -> translate env bs1 def
          | u::us' ->
              Lam
                (((fun u1  -> make_univ_abst us' (u1 :: bs1) def)),
                  FStar_Pervasives_Native.None) in
        make_univ_abst lb.FStar_Syntax_Syntax.lbunivs bs
          lb.FStar_Syntax_Syntax.lbdef
and translate:
  FStar_TypeChecker_Env.env -> t Prims.list -> FStar_Syntax_Syntax.term -> t
  =
  fun env  ->
    fun bs  ->
      fun e  ->
        debug
          (fun uu____2103  ->
             let uu____2104 =
               let uu____2105 = FStar_Syntax_Subst.compress e in
               FStar_Syntax_Print.tag_of_term uu____2105 in
             let uu____2106 =
               let uu____2107 = FStar_Syntax_Subst.compress e in
               FStar_Syntax_Print.term_to_string uu____2107 in
             FStar_Util.print2 "Term: %s - %s\n" uu____2104 uu____2106);
        debug
          (fun uu____2113  ->
             let uu____2114 =
               let uu____2115 = FStar_List.map (fun x  -> t_to_string x) bs in
               FStar_String.concat ";; " uu____2115 in
             FStar_Util.print1 "BS list: %s\n" uu____2114);
        (let uu____2120 =
           let uu____2121 = FStar_Syntax_Subst.compress e in
           uu____2121.FStar_Syntax_Syntax.n in
         match uu____2120 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____2124,uu____2125) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             failwith "Tm_unknown: Impossible"
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) -> Unit
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Bool b
         | FStar_Syntax_Syntax.Tm_constant c ->
             let err =
               let uu____2169 =
                 let uu____2170 = FStar_Syntax_Print.const_to_string c in
                 Prims.strcat uu____2170 ": Not yet implemented" in
               Prims.strcat "Tm_constant " uu____2169 in
             (debug_term e; failwith err)
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug
                (fun uu____2188  ->
                   let uu____2189 = FStar_Syntax_Print.tag_of_term t in
                   let uu____2190 = FStar_Syntax_Print.term_to_string t in
                   let uu____2191 =
                     let uu____2192 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us in
                     FStar_All.pipe_right uu____2192
                       (FStar_String.concat ", ") in
                   FStar_Util.print3 "Term with univs: %s - %s\nUniv %s\n"
                     uu____2189 uu____2190 uu____2191);
              (let uu____2197 = translate env bs t in
               let uu____2198 = FStar_List.map (translate_univ bs) us in
               FStar_List.fold_left
                 (fun head1  ->
                    fun u  -> app head1 u FStar_Pervasives_Native.None)
                 uu____2197 uu____2198))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____2206 =
               let uu____2207 = translate_univ bs u in un_univ uu____2207 in
             Type_t uu____2206
         | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
             (debug_term e; failwith "Tm_arrow: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_refine uu____2227 ->
             (debug_term e; failwith "Tm_refine: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2236,uu____2237) ->
             translate env bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____2306) -> translate env bs e1
         | FStar_Syntax_Syntax.Tm_name x -> mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____2312,uu____2313) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (x::[],body,uu____2334) ->
             (debug
                (fun uu____2368  ->
                   let uu____2369 = FStar_Syntax_Print.tag_of_term body in
                   let uu____2370 = FStar_Syntax_Print.term_to_string body in
                   FStar_Util.print2 "Tm_abs body : %s - %s\n" uu____2369
                     uu____2370);
              Lam
                (((fun y  -> translate env (y :: bs) body)),
                  (FStar_Pervasives_Native.snd x)))
         | FStar_Syntax_Syntax.Tm_abs (x::xs,body,uu____2378) ->
             let rest =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_abs
                    (xs, body, FStar_Pervasives_Native.None))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange in
             let tm =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_abs
                    ([x], rest, FStar_Pervasives_Native.None))
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
             translate env bs tm
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv env bs fvar1
         | FStar_Syntax_Syntax.Tm_app (e1,[]) ->
             failwith "Impossible: application with no arguments"
         | FStar_Syntax_Syntax.Tm_app (e1,arg::[]) ->
             (debug
                (fun uu____2500  ->
                   let uu____2501 = FStar_Syntax_Print.term_to_string e1 in
                   let uu____2502 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg) in
                   FStar_Util.print2 "Application %s / %s\n" uu____2501
                     uu____2502);
              (let uu____2505 = translate env bs e1 in
               let uu____2506 =
                 translate env bs (FStar_Pervasives_Native.fst arg) in
               app uu____2505 uu____2506 (FStar_Pervasives_Native.snd arg)))
         | FStar_Syntax_Syntax.Tm_app (head1,arg::args) ->
             (debug
                (fun uu____2553  ->
                   let uu____2554 = FStar_Syntax_Print.term_to_string head1 in
                   let uu____2555 =
                     FStar_Syntax_Print.term_to_string
                       (FStar_Pervasives_Native.fst arg) in
                   FStar_Util.print2 "Application %s / %s (...more agrs)\n"
                     uu____2554 uu____2555);
              (let first =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               let tm =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (first, args))
                   FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
               translate env bs tm))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | Construct (c,us,args) ->
                   (debug
                      (fun uu____2662  ->
                         let uu____2663 =
                           let uu____2664 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____2685  ->
                                     match uu____2685 with
                                     | (x,q) ->
                                         let uu____2698 = t_to_string x in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____2698)) in
                           FStar_All.pipe_right uu____2664
                             (FStar_String.concat "; ") in
                         FStar_Util.print1 "Match args: %s\n" uu____2663);
                    (let uu____2702 = pickBranch scrut1 branches in
                     match uu____2702 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____2723 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1 in
                         translate env uu____2723 branch1
                     | FStar_Pervasives_Native.None  ->
                         mkAccuMatch scrut1 case))
               | uu____2740 -> mkAccuMatch scrut1 case in
             let uu____2741 = translate env bs scrut in case uu____2741
         | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
             let def = translate_letbinding env bs lb in
             translate env (def :: bs) body
         | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),body) ->
             let f = mkAccuRec lb bs in translate env (f :: bs) body
         | FStar_Syntax_Syntax.Tm_let uu____2772 ->
             failwith "Mutual recursion; not yet handled")
and readback: FStar_TypeChecker_Env.env -> t -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun x  ->
      debug
        (fun uu____2792  ->
           let uu____2793 = t_to_string x in
           FStar_Util.print1 "Readback: %s\n" uu____2793);
      (match x with
       | Unit  -> FStar_Syntax_Syntax.unit_const
       | Univ u -> failwith "Readback of universes should not occur"
       | Bool (true ) -> FStar_Syntax_Util.exp_true_bool
       | Bool (false ) -> FStar_Syntax_Util.exp_false_bool
       | Type_t u ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | Lam (f,q) ->
           let x1 =
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               FStar_Syntax_Syntax.tun in
           let body =
             let uu____2804 = f (mkAccuVar x1) in readback env uu____2804 in
           FStar_Syntax_Util.abs [(x1, q)] body FStar_Pervasives_Native.None
       | Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____2851  ->
                  match uu____2851 with
                  | (x1,q) ->
                      let uu____2862 = readback env x1 in (uu____2862, q))
               args in
           let apply1 tm =
             match args1 with
             | [] -> tm
             | uu____2879 -> FStar_Syntax_Util.mk_app tm args1 in
           (match us with
            | uu____2886::uu____2887 ->
                let uu____2890 =
                  let uu____2893 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____2893
                    (FStar_List.rev us) in
                apply1 uu____2890
            | [] ->
                let uu____2894 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                apply1 uu____2894)
       | Accu (Var bv,[]) -> FStar_Syntax_Syntax.bv_to_name bv
       | Accu (Var bv,ts) ->
           let args =
             map_rev
               (fun uu____2941  ->
                  match uu____2941 with
                  | (x1,q) ->
                      let uu____2952 = readback env x1 in (uu____2952, q)) ts in
           let uu____2953 = FStar_Syntax_Syntax.bv_to_name bv in
           FStar_Syntax_Util.mk_app uu____2953 args
       | Accu (Match (scrut,cases),ts) ->
           let args =
             map_rev
               (fun uu____2994  ->
                  match uu____2994 with
                  | (x1,q) ->
                      let uu____3005 = readback env x1 in (uu____3005, q)) ts in
           let head1 =
             let uu____3007 = cases scrut in readback env uu____3007 in
           (match ts with
            | [] -> head1
            | uu____3012 -> FStar_Syntax_Util.mk_app head1 args)
       | Accu (Rec (lb,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____3090 = curry hd1 args1 in
                 app uu____3090 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg) in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef in
           let uu____3092 = test_args ts args_no in
           if uu____3092
           then
             let uu____3093 =
               let uu____3094 =
                 translate_letbinding env ((mkAccuRec lb bs) :: bs) lb in
               curry uu____3094 ts in
             readback env uu____3093
           else
             (let head1 =
                let f =
                  match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inl bv -> FStar_Syntax_Syntax.bv_to_name bv
                  | FStar_Util.Inr fv -> failwith "Not yet implemented" in
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((true, [lb]), f))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange in
              let args =
                map_rev
                  (fun uu____3129  ->
                     match uu____3129 with
                     | (x1,q) ->
                         let uu____3140 = readback env x1 in (uu____3140, q))
                  ts in
              match ts with
              | [] -> head1
              | uu____3145 -> FStar_Syntax_Util.mk_app head1 args))
let normalize:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  -> let uu____3158 = translate env [] e in readback env uu____3158