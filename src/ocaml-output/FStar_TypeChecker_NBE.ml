open Prims
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
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
type var = FStar_Syntax_Syntax.bv[@@deriving show]
type sort = Prims.int[@@deriving show]
type atom =
  | Var of var
  | Sort of sort
  | Prod of (t,t) FStar_Pervasives_Native.tuple2
  | Match of (t,t -> t) FStar_Pervasives_Native.tuple2
  | Rec of (FStar_Syntax_Syntax.letbinding,t Prims.list)
  FStar_Pervasives_Native.tuple2[@@deriving show]
and t =
  | Lam of (t -> t)
  | Fix of (t -> t)
  | Accu of (atom,t Prims.list) FStar_Pervasives_Native.tuple2
  | Construct of (FStar_Syntax_Syntax.fv,t Prims.list)
  FStar_Pervasives_Native.tuple2
  | Unit
  | Bool of Prims.bool[@@deriving show]
let uu___is_Var: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____146 -> false
let __proj__Var__item___0: atom -> var =
  fun projectee  -> match projectee with | Var _0 -> _0
let uu___is_Sort: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____158 -> false
let __proj__Sort__item___0: atom -> sort =
  fun projectee  -> match projectee with | Sort _0 -> _0
let uu___is_Prod: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Prod _0 -> true | uu____174 -> false
let __proj__Prod__item___0: atom -> (t,t) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Prod _0 -> _0
let uu___is_Match: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____204 -> false
let __proj__Match__item___0:
  atom -> (t,t -> t) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Rec: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____240 -> false
let __proj__Rec__item___0:
  atom ->
    (FStar_Syntax_Syntax.letbinding,t Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Rec _0 -> _0
let uu___is_Lam: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____272 -> false
let __proj__Lam__item___0: t -> t -> t =
  fun projectee  -> match projectee with | Lam _0 -> _0
let uu___is_Fix: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Fix _0 -> true | uu____292 -> false
let __proj__Fix__item___0: t -> t -> t =
  fun projectee  -> match projectee with | Fix _0 -> _0
let uu___is_Accu: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____316 -> false
let __proj__Accu__item___0:
  t -> (atom,t Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Accu _0 -> _0
let uu___is_Construct: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____352 -> false
let __proj__Construct__item___0:
  t -> (FStar_Syntax_Syntax.fv,t Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Construct _0 -> _0
let uu___is_Unit: t -> Prims.bool =
  fun projectee  -> match projectee with | Unit  -> true | uu____381 -> false
let uu___is_Bool: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____386 -> false
let __proj__Bool__item___0: t -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
type head = t[@@deriving show]
type annot = t FStar_Pervasives_Native.option[@@deriving show]
let is_not_accu: t -> Prims.bool =
  fun x  ->
    match x with | Accu (uu____399,uu____400) -> false | uu____405 -> true
let mkConstruct: FStar_Syntax_Syntax.fv -> t Prims.list -> t =
  fun i  -> fun ts  -> Construct (i, ts)
let mkAccuVar: var -> t = fun v1  -> Accu ((Var v1), [])
let mkAccuMatch: t -> (t -> t) -> t =
  fun s  -> fun c  -> Accu ((Match (s, c)), [])
let mkAccuRec: FStar_Syntax_Syntax.letbinding -> t Prims.list -> t =
  fun b  -> fun env  -> Accu ((Rec (b, env)), [])
let isAccu: t -> Prims.bool =
  fun trm  -> match trm with | Accu uu____455 -> true | uu____462 -> false
let rec pickBranch:
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.branch Prims.list -> FStar_Syntax_Syntax.term
  =
  fun c  ->
    fun branches  ->
      match branches with
      | [] -> failwith "Branch not found"
      | ({ FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (c',args);
           FStar_Syntax_Syntax.p = uu____475;_},uu____476,e)::bs
          when FStar_Syntax_Syntax.fv_eq c c' -> e
      | b::bs -> pickBranch c bs
let rec test_args: t Prims.list -> Prims.int -> Prims.bool =
  fun ts  ->
    fun cnt  ->
      match ts with
      | [] -> cnt <= (Prims.parse_int "0")
      | t::ts1 ->
          (Prims.op_Negation (isAccu t)) &&
            (test_args ts1 (cnt - (Prims.parse_int "1")))
let rec count_abstractions: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    let uu____560 =
      let uu____561 = FStar_Syntax_Subst.compress t in
      uu____561.FStar_Syntax_Syntax.n in
    match uu____560 with
    | FStar_Syntax_Syntax.Tm_delayed uu____564 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_uinst uu____589 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_bvar uu____596 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_name uu____597 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_fvar uu____598 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_constant uu____599 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_type uu____600 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_arrow uu____601 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_uvar uu____614 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_refine uu____631 -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_unknown  -> Prims.parse_int "0"
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____640) ->
        let uu____661 = count_abstractions body in
        (FStar_List.length xs) + uu____661
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____688 =
          let uu____689 = count_abstractions head1 in
          uu____689 - (FStar_List.length args) in
        max uu____688 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____748,uu____749,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____798,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____817) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____823,uu____824) ->
        count_abstractions t1
let rec mkBranches:
  'Auu____871 'Auu____872 'Auu____873 'Auu____874 .
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,'Auu____874,
      'Auu____873) FStar_Pervasives_Native.tuple3 Prims.list ->
      (t -> 'Auu____872) ->
        (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,'Auu____871
                                                                   FStar_Pervasives_Native.option,
          'Auu____872) FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun branches  ->
    fun cont  ->
      match branches with
      | ({ FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (fv,pats);
           FStar_Syntax_Syntax.p = uu____922;_},uu____923,uu____924)::branches'
          ->
          let uu____962 =
            FStar_List.fold_right
              (fun p  ->
                 fun uu____998  ->
                   match uu____998 with
                   | (args,bs) ->
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun in
                       let uu____1046 =
                         let uu____1055 =
                           let uu____1062 =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_var x)
                               FStar_Range.dummyRange in
                           (uu____1062, (FStar_Pervasives_Native.snd p)) in
                         uu____1055 :: bs in
                       (((mkAccuVar x) :: args), uu____1046)) pats ([], []) in
          (match uu____962 with
           | (args,binders) ->
               let value = Construct (fv, args) in
               let pat =
                 FStar_Syntax_Syntax.withinfo
                   (FStar_Syntax_Syntax.Pat_cons (fv, binders))
                   FStar_Range.dummyRange in
               let branch1 =
                 let uu____1148 = cont value in
                 (pat, FStar_Pervasives_Native.None, uu____1148) in
               let uu____1153 = mkBranches branches' cont in branch1 ::
                 uu____1153)
      | uu____1176 -> failwith "Unexpected pattern"
let rec app: t -> t -> t =
  fun f  ->
    fun x  ->
      match f with
      | Lam f1 -> f1 x
      | Accu (a,ts) -> Accu (a, (x :: ts))
      | Construct (i,ts) -> Construct (i, (x :: ts))
      | Unit  -> failwith "Ill-typed application"
      | Bool uu____1238 -> failwith "Ill-typed application"
and iapp: t -> t Prims.list -> t =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____1243 ->
          let uu____1246 =
            let uu____1247 = FStar_List.hd args in app f uu____1247 in
          let uu____1248 = FStar_List.tl args in iapp uu____1246 uu____1248
and translate: t Prims.list -> FStar_Syntax_Syntax.term -> t =
  fun bs  ->
    fun e  ->
      let uu____1255 =
        let uu____1256 = FStar_Syntax_Subst.compress e in
        uu____1256.FStar_Syntax_Syntax.n in
      match uu____1255 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1259 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) -> Unit
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> Bool b
      | FStar_Syntax_Syntax.Tm_bvar db ->
          FStar_List.nth bs db.FStar_Syntax_Syntax.index
      | FStar_Syntax_Syntax.Tm_name x -> mkAccuVar x
      | FStar_Syntax_Syntax.Tm_abs (x::[],body,uu____1289) ->
          Lam ((fun y  -> translate (y :: bs) body))
      | FStar_Syntax_Syntax.Tm_fvar v1 -> mkConstruct v1 []
      | FStar_Syntax_Syntax.Tm_abs (x::xs,body,uu____1323) ->
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
          translate bs tm
      | FStar_Syntax_Syntax.Tm_app (e1,arg::[]) ->
          let uu____1418 = translate bs e1 in
          let uu____1419 = translate bs (FStar_Pervasives_Native.fst arg) in
          app uu____1418 uu____1419
      | FStar_Syntax_Syntax.Tm_app (head1,arg::args) ->
          let first =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
              FStar_Pervasives_Native.None FStar_Range.dummyRange in
          let tm =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (first, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
          translate bs tm
      | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
          let rec case scrut1 =
            match scrut1 with
            | Construct (c,args) ->
                let branch1 =
                  let uu____1544 = pickBranch c branches in
                  translate (FStar_List.append (FStar_List.rev args) bs)
                    uu____1544 in
                branch1
            | uu____1545 -> mkAccuMatch scrut1 case in
          let uu____1546 = translate bs scrut in case uu____1546
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let def = translate bs lb.FStar_Syntax_Syntax.lbdef in
          translate (def :: bs) body
      | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),body) ->
          let f = mkAccuRec lb bs in translate (f :: bs) body
      | uu____1577 -> (debug_term e; failwith "Not yet implemented")
and readback: t -> FStar_Syntax_Syntax.term =
  fun x  ->
    match x with
    | Unit  -> FStar_Syntax_Syntax.unit_const
    | Bool (true ) -> FStar_Syntax_Util.exp_true_bool
    | Bool (false ) -> FStar_Syntax_Util.exp_false_bool
    | Lam f ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.tun in
        let body = let uu____1585 = f (mkAccuVar x1) in readback uu____1585 in
        let uu____1586 =
          let uu____1587 = FStar_Syntax_Syntax.mk_binder x1 in [uu____1587] in
        FStar_Syntax_Util.abs uu____1586 body FStar_Pervasives_Native.None
    | Construct (fv,args) ->
        let args1 =
          FStar_List.map
            (fun x1  ->
               let uu____1600 = readback x1 in
               FStar_Syntax_Syntax.as_arg uu____1600) args in
        (match args1 with
         | [] ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
         | uu____1601 ->
             let uu____1604 =
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                 FStar_Pervasives_Native.None FStar_Range.dummyRange in
             FStar_Syntax_Util.mk_app uu____1604 args1)
    | Accu (Var bv,[]) -> FStar_Syntax_Syntax.bv_to_name bv
    | Accu (Var bv,ts) ->
        let args =
          map_rev
            (fun x1  ->
               let uu____1622 = readback x1 in
               FStar_Syntax_Syntax.as_arg uu____1622) ts in
        let uu____1623 = FStar_Syntax_Syntax.bv_to_name bv in
        FStar_Syntax_Util.mk_app uu____1623 args
    | Accu (Match (scrut,cases),ts) ->
        let args =
          map_rev
            (fun x1  ->
               let uu____1643 = readback x1 in
               FStar_Syntax_Syntax.as_arg uu____1643) ts in
        let head1 = let uu____1645 = cases scrut in readback uu____1645 in
        (match ts with
         | [] -> head1
         | uu____1646 -> FStar_Syntax_Util.mk_app head1 args)
    | Accu (Rec (lb,bs),ts) ->
        let rec curry hd1 args =
          match args with
          | [] -> hd1
          | arg::[] -> app hd1 arg
          | arg::args1 ->
              let uu____1676 = curry hd1 args1 in app uu____1676 arg in
        let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef in
        let uu____1678 = test_args ts args_no in
        if uu____1678
        then
          let uu____1679 =
            let uu____1680 =
              translate ((mkAccuRec lb bs) :: bs)
                lb.FStar_Syntax_Syntax.lbdef in
            curry uu____1680 ts in
          readback uu____1679
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
               (fun x1  ->
                  let uu____1702 = readback x1 in
                  FStar_Syntax_Syntax.as_arg uu____1702) ts in
           match ts with
           | [] -> head1
           | uu____1703 -> FStar_Syntax_Util.mk_app head1 args)
    | uu____1706 -> failwith "Not yet implemented"
let normalize: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  -> let uu____1710 = translate [] e in readback uu____1710