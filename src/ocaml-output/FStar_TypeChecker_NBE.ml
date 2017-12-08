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
let debug_term: FStar_Syntax_Syntax.term -> Prims.unit =
  fun t  ->
    let uu____63 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.print1 "%s\n" uu____63
let debug_sigmap: FStar_Syntax_Syntax.sigelt FStar_Util.smap -> Prims.unit =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____78 = FStar_Syntax_Print.sigelt_to_string_short v1 in
             FStar_Util.print2 "%s -> %%s\n" k uu____78) ()
type var = FStar_Syntax_Syntax.bv[@@deriving show]
type sort = Prims.int[@@deriving show]
type atom =
  | Var of var
  | Type of FStar_Syntax_Syntax.universe
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
  (FStar_Syntax_Syntax.fv,(t,FStar_Syntax_Syntax.aqual)
                            FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2
  | Unit
  | Bool of Prims.bool[@@deriving show]
let uu___is_Var: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____157 -> false
let __proj__Var__item___0: atom -> var =
  fun projectee  -> match projectee with | Var _0 -> _0
let uu___is_Type: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Type _0 -> true | uu____169 -> false
let __proj__Type__item___0: atom -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Type _0 -> _0
let uu___is_Match: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____187 -> false
let __proj__Match__item___0:
  atom -> (t,t -> t) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Rec: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____223 -> false
let __proj__Rec__item___0:
  atom ->
    (FStar_Syntax_Syntax.letbinding,t Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Rec _0 -> _0
let uu___is_Lam: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____259 -> false
let __proj__Lam__item___0:
  t -> (t -> t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Lam _0 -> _0
let uu___is_Accu: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____299 -> false
let __proj__Accu__item___0:
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Accu _0 -> _0
let uu___is_Construct: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____351 -> false
let __proj__Construct__item___0:
  t ->
    (FStar_Syntax_Syntax.fv,(t,FStar_Syntax_Syntax.aqual)
                              FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Construct _0 -> _0
let uu___is_Unit: t -> Prims.bool =
  fun projectee  -> match projectee with | Unit  -> true | uu____392 -> false
let uu___is_Bool: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____397 -> false
let __proj__Bool__item___0: t -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
type head = t[@@deriving show]
type annot = t FStar_Pervasives_Native.option[@@deriving show]
let is_not_accu: t -> Prims.bool =
  fun x  ->
    match x with | Accu (uu____410,uu____411) -> false | uu____424 -> true
let mkConstruct:
  FStar_Syntax_Syntax.fv ->
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
      -> t
  = fun i  -> fun ts  -> Construct (i, ts)
let mkAccuVar: var -> t = fun v1  -> Accu ((Var v1), [])
let mkAccuMatch: t -> (t -> t) -> t =
  fun s  -> fun c  -> Accu ((Match (s, c)), [])
let mkAccuRec: FStar_Syntax_Syntax.letbinding -> t Prims.list -> t =
  fun b  -> fun env  -> Accu ((Rec (b, env)), [])
let mkAccTyp: FStar_Syntax_Syntax.universe -> t =
  fun u  -> Accu ((Type u), [])
let isAccu: t -> Prims.bool =
  fun trm  -> match trm with | Accu uu____523 -> true | uu____534 -> false
let rec pickBranch:
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.branch Prims.list -> FStar_Syntax_Syntax.term
  =
  fun c  ->
    fun branches  ->
      match branches with
      | [] -> failwith "Branch not found"
      | ({ FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (c',args);
           FStar_Syntax_Syntax.p = uu____547;_},uu____548,e)::bs
          when FStar_Syntax_Syntax.fv_eq c c' -> e
      | b::bs -> pickBranch c bs
let rec test_args:
  'Auu____618 .
    (t,'Auu____618) FStar_Pervasives_Native.tuple2 Prims.list ->
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
    let uu____662 =
      let uu____663 = FStar_Syntax_Subst.compress t in
      uu____663.FStar_Syntax_Syntax.n in
    match uu____662 with
    | FStar_Syntax_Syntax.Tm_delayed uu____666 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_uinst uu____691 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_bvar uu____698 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_name uu____699 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_fvar uu____700 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_constant uu____701 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_type uu____702 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_arrow uu____703 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_uvar uu____716 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_refine uu____733 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_unknown  -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____742) ->
        let uu____763 = count_abstractions body in
        (FStar_List.length xs) + uu____763
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____790 =
          let uu____791 = count_abstractions head1 in
          uu____791 - (FStar_List.length args) in
        max uu____790 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____850,uu____851,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____900,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____919) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____925,uu____926) ->
        count_abstractions t1
let find_sigelt_in_gamma:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____1000 =
        match uu____1000 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                 FStar_Pervasives_Native.Some elt
             | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                 FStar_Pervasives_Native.Some elt
             | uu____1080 -> FStar_Pervasives_Native.None) in
      let uu____1095 = FStar_TypeChecker_Env.lookup_qname env lid in
      FStar_Util.bind_opt uu____1095 mapper
let rec app: t -> t -> FStar_Syntax_Syntax.aqual -> t =
  fun f  ->
    fun x  ->
      fun q  ->
        match f with
        | Lam (f1,uu____1166) -> f1 x
        | Accu (a,ts) -> Accu (a, ((x, q) :: ts))
        | Construct (i,ts) -> Construct (i, ((x, q) :: ts))
        | Unit  -> failwith "Ill-typed application"
        | Bool uu____1219 -> failwith "Ill-typed application"
and iapp:
  t ->
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
      -> t
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____1232 ->
          let uu____1239 =
            let uu____1240 =
              let uu____1241 = FStar_List.hd args in
              FStar_Pervasives_Native.fst uu____1241 in
            let uu____1250 =
              let uu____1251 = FStar_List.hd args in
              FStar_Pervasives_Native.snd uu____1251 in
            app f uu____1240 uu____1250 in
          let uu____1260 = FStar_List.tl args in iapp uu____1239 uu____1260
and translate:
  FStar_TypeChecker_Env.env -> t Prims.list -> FStar_Syntax_Syntax.term -> t
  =
  fun env  ->
    fun bs  ->
      fun e  ->
        let uu____1276 =
          let uu____1277 = FStar_Syntax_Subst.compress e in
          uu____1277.FStar_Syntax_Syntax.n in
        match uu____1276 with
        | FStar_Syntax_Syntax.Tm_delayed (uu____1280,uu____1281) ->
            failwith "Tm_delayed: Impossible"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            failwith "Tm_unknown: Impossible"
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) -> Unit
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
            Bool b
        | FStar_Syntax_Syntax.Tm_constant c ->
            let err1 =
              let uu____1325 =
                let uu____1326 = FStar_Syntax_Print.const_to_string c in
                Prims.strcat uu____1326 ": Not yet implemented" in
              Prims.strcat "Tm_constant " uu____1325 in
            (debug_term e; failwith err1)
        | FStar_Syntax_Syntax.Tm_bvar db ->
            FStar_List.nth bs db.FStar_Syntax_Syntax.index
        | FStar_Syntax_Syntax.Tm_uinst (t,u::[]) ->
            let tr = translate env bs t in
            (match tr with
             | Lam uu____1338 ->
                 let x =
                   let uu____1352 =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       FStar_Syntax_Syntax.tun in
                   (uu____1352, FStar_Pervasives_Native.None) in
                 let t' =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ([x], t, FStar_Pervasives_Native.None))
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
                 let uu____1382 = translate env bs t' in
                 let uu____1383 =
                   let uu____1384 = FStar_Syntax_Subst.compress_univ u in
                   mkAccTyp uu____1384 in
                 app uu____1382 uu____1383 FStar_Pervasives_Native.None
             | uu____1385 ->
                 let uu____1386 =
                   let uu____1387 = FStar_Syntax_Subst.compress_univ u in
                   mkAccTyp uu____1387 in
                 app tr uu____1386 FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_uinst (t,uu____1389) ->
            (debug_term e; failwith "Not yet implemented Tm_uinst")
        | FStar_Syntax_Syntax.Tm_type u -> mkAccTyp u
        | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
            (debug_term e; failwith "Tm_arrow: Not yet implemented")
        | FStar_Syntax_Syntax.Tm_refine uu____1415 ->
            (debug_term e; failwith "Tm_refine: Not yet implemented")
        | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1424,uu____1425) ->
            translate env bs t
        | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
            (debug_term e; failwith "Tm_uvar: Not yet implemented")
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____1494) -> translate env bs e1
        | FStar_Syntax_Syntax.Tm_name x -> mkAccuVar x
        | FStar_Syntax_Syntax.Tm_abs (x::[],body,uu____1502) ->
            Lam
              (((fun y  -> translate env (y :: bs) body)),
                (FStar_Pervasives_Native.snd x))
        | FStar_Syntax_Syntax.Tm_abs (x::xs,body,uu____1536) ->
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
        | FStar_Syntax_Syntax.Tm_fvar fvar1 ->
            let find_in_sigtab1 env1 lid =
              FStar_Util.smap_try_find env1.FStar_TypeChecker_Env.sigtab
                (FStar_Ident.text_of_lid lid) in
            let uu____1611 =
              let uu____1616 =
                let uu____1621 =
                  find_sigelt_in_gamma env
                    (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                let uu____1624 =
                  let uu____1629 =
                    find_in_sigtab1 env
                      (fvar1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  [uu____1629] in
                uu____1621 :: uu____1624 in
              FStar_List.find FStar_Util.is_some uu____1616 in
            (match uu____1611 with
             | FStar_Pervasives_Native.Some elt ->
                 (match elt with
                  | FStar_Pervasives_Native.Some
                      {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,lb::[]),uu____1647);
                        FStar_Syntax_Syntax.sigrng = uu____1648;
                        FStar_Syntax_Syntax.sigquals = uu____1649;
                        FStar_Syntax_Syntax.sigmeta = uu____1650;
                        FStar_Syntax_Syntax.sigattrs = uu____1651;_}
                      ->
                      if is_rec
                      then mkAccuRec lb []
                      else translate env [] lb.FStar_Syntax_Syntax.lbdef
                  | FStar_Pervasives_Native.Some
                      {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_datacon
                          (uu____1669,uu____1670,uu____1671,uu____1672,uu____1673,[]);
                        FStar_Syntax_Syntax.sigrng = uu____1674;
                        FStar_Syntax_Syntax.sigquals = uu____1675;
                        FStar_Syntax_Syntax.sigmeta = uu____1676;
                        FStar_Syntax_Syntax.sigattrs = uu____1677;_}
                      -> mkConstruct fvar1 []
                  | FStar_Pervasives_Native.Some
                      {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,univs1,bs1,ty,uu____1692,uu____1693);
                        FStar_Syntax_Syntax.sigrng = uu____1694;
                        FStar_Syntax_Syntax.sigquals = uu____1695;
                        FStar_Syntax_Syntax.sigmeta = uu____1696;
                        FStar_Syntax_Syntax.sigattrs = uu____1697;_}
                      -> mkConstruct fvar1 []
                  | FStar_Pervasives_Native.None  -> mkConstruct fvar1 []
                  | FStar_Pervasives_Native.Some s ->
                      let uu____1719 =
                        let uu____1720 =
                          FStar_Syntax_Print.sigelt_to_string s in
                        FStar_Util.format1 "Sig %s" uu____1720 in
                      FStar_All.pipe_right uu____1719 failwith)
             | FStar_Pervasives_Native.None  -> mkConstruct fvar1 [])
        | FStar_Syntax_Syntax.Tm_app (e1,arg::[]) ->
            let uu____1759 = translate env bs e1 in
            let uu____1760 =
              translate env bs (FStar_Pervasives_Native.fst arg) in
            app uu____1759 uu____1760 (FStar_Pervasives_Native.snd arg)
        | FStar_Syntax_Syntax.Tm_app (head1,arg::args) ->
            let first =
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
                FStar_Pervasives_Native.None FStar_Range.dummyRange in
            let tm =
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_app (first, args))
                FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
            translate env bs tm
        | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
            let rec case scrut1 =
              match scrut1 with
              | Construct (c,args) ->
                  let branch1 =
                    let uu____1895 =
                      let uu____1898 =
                        map_rev
                          (fun uu____1908  ->
                             match uu____1908 with | (x,uu____1914) -> x)
                          args in
                      FStar_List.append uu____1898 bs in
                    let uu____1915 = pickBranch c branches in
                    translate env uu____1895 uu____1915 in
                  branch1
              | uu____1916 -> mkAccuMatch scrut1 case in
            let uu____1917 = translate env bs scrut in case uu____1917
        | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
            let def = translate env bs lb.FStar_Syntax_Syntax.lbdef in
            translate env (def :: bs) body
        | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),body) ->
            let f = mkAccuRec lb bs in translate env (f :: bs) body
and readback: FStar_TypeChecker_Env.env -> t -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun x  ->
      match x with
      | Unit  -> FStar_Syntax_Syntax.unit_const
      | Bool (true ) -> FStar_Syntax_Util.exp_true_bool
      | Bool (false ) -> FStar_Syntax_Util.exp_false_bool
      | Lam (f,q) ->
          let x1 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.tun in
          let body =
            let uu____1958 = f (mkAccuVar x1) in readback env uu____1958 in
          FStar_Syntax_Util.abs [(x1, q)] body FStar_Pervasives_Native.None
      | Construct (fv,args) ->
          let args1 =
            map_rev
              (fun uu____2000  ->
                 match uu____2000 with
                 | (x1,q) ->
                     let uu____2011 = readback env x1 in (uu____2011, q))
              args in
          (match args1 with
           | [] ->
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
           | h::hs ->
               (match (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.n
                with
                | FStar_Syntax_Syntax.Tm_type u ->
                    let uu____2033 =
                      let uu____2036 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_fvar fv)
                          FStar_Pervasives_Native.None FStar_Range.dummyRange in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____2036 [u] in
                    FStar_Syntax_Util.mk_app uu____2033 hs
                | uu____2037 ->
                    let uu____2038 =
                      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                        FStar_Pervasives_Native.None FStar_Range.dummyRange in
                    FStar_Syntax_Util.mk_app uu____2038 args1))
      | Accu (Var bv,[]) -> FStar_Syntax_Syntax.bv_to_name bv
      | Accu (Var bv,ts) ->
          let args =
            map_rev
              (fun uu____2085  ->
                 match uu____2085 with
                 | (x1,q) ->
                     let uu____2096 = readback env x1 in (uu____2096, q)) ts in
          let uu____2097 = FStar_Syntax_Syntax.bv_to_name bv in
          FStar_Syntax_Util.mk_app uu____2097 args
      | Accu (Type u,[]) ->
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
      | Accu (Type u,ts) ->
          let args =
            map_rev
              (fun uu____2144  ->
                 match uu____2144 with
                 | (x1,q) ->
                     let uu____2155 = readback env x1 in (uu____2155, q)) ts in
          let uu____2156 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
              FStar_Pervasives_Native.None FStar_Range.dummyRange in
          FStar_Syntax_Util.mk_app uu____2156 args
      | Accu (Match (scrut,cases),ts) ->
          let args =
            map_rev
              (fun uu____2197  ->
                 match uu____2197 with
                 | (x1,q) ->
                     let uu____2208 = readback env x1 in (uu____2208, q)) ts in
          let head1 = let uu____2210 = cases scrut in readback env uu____2210 in
          (match ts with
           | [] -> head1
           | uu____2215 -> FStar_Syntax_Util.mk_app head1 args)
      | Accu (Rec (lb,bs),ts) ->
          let rec curry hd1 args =
            match args with
            | [] -> hd1
            | arg::[] ->
                app hd1 (FStar_Pervasives_Native.fst arg)
                  (FStar_Pervasives_Native.snd arg)
            | arg::args1 ->
                let uu____2293 = curry hd1 args1 in
                app uu____2293 (FStar_Pervasives_Native.fst arg)
                  (FStar_Pervasives_Native.snd arg) in
          let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef in
          let uu____2295 = test_args ts args_no in
          if uu____2295
          then
            let uu____2296 =
              let uu____2297 =
                translate env ((mkAccuRec lb bs) :: bs)
                  lb.FStar_Syntax_Syntax.lbdef in
              curry uu____2297 ts in
            readback env uu____2296
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
                 (fun uu____2332  ->
                    match uu____2332 with
                    | (x1,q) ->
                        let uu____2343 = readback env x1 in (uu____2343, q))
                 ts in
             match ts with
             | [] -> head1
             | uu____2348 -> FStar_Syntax_Util.mk_app head1 args)
let normalize:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  -> let uu____2361 = translate env [] e in readback env uu____2361