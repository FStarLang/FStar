open Prims
let map_rev: 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____53 = let uu____56 = f x in uu____56 :: acc in
            aux xs uu____53 in
      aux l []
let debug_term: FStar_Syntax_Syntax.term -> Prims.unit =
  fun t  ->
    let uu____61 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.print1 "%s\n" uu____61
type var = FStar_Syntax_Syntax.bv[@@deriving show]
type sort = Prims.int[@@deriving show]
type atom =
  | Var of var
  | Sort of sort
  | Prod of (t,t) FStar_Pervasives_Native.tuple2
  | Match of (FStar_Syntax_Syntax.branch Prims.list,t,t -> t)
  FStar_Pervasives_Native.tuple3
  | Fix of (t -> t,t,Prims.int) FStar_Pervasives_Native.tuple3[@@deriving
                                                                show]
and t =
  | Lam of (t -> t)
  | Accu of (atom,t Prims.list) FStar_Pervasives_Native.tuple2
  | Construct of (FStar_Syntax_Syntax.fv,t Prims.list)
  FStar_Pervasives_Native.tuple2
  | Unit
  | Bool of Prims.bool[@@deriving show]
let uu___is_Var: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____145 -> false
let __proj__Var__item___0: atom -> var =
  fun projectee  -> match projectee with | Var _0 -> _0
let uu___is_Sort: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____159 -> false
let __proj__Sort__item___0: atom -> sort =
  fun projectee  -> match projectee with | Sort _0 -> _0
let uu___is_Prod: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Prod _0 -> true | uu____177 -> false
let __proj__Prod__item___0: atom -> (t,t) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Prod _0 -> _0
let uu___is_Match: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____213 -> false
let __proj__Match__item___0:
  atom ->
    (FStar_Syntax_Syntax.branch Prims.list,t,t -> t)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Fix: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Fix _0 -> true | uu____265 -> false
let __proj__Fix__item___0:
  atom -> (t -> t,t,Prims.int) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | Fix _0 -> _0
let uu___is_Lam: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____305 -> false
let __proj__Lam__item___0: t -> t -> t =
  fun projectee  -> match projectee with | Lam _0 -> _0
let uu___is_Accu: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____332 -> false
let __proj__Accu__item___0:
  t -> (atom,t Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Accu _0 -> _0
let uu___is_Construct: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____370 -> false
let __proj__Construct__item___0:
  t -> (FStar_Syntax_Syntax.fv,t Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Construct _0 -> _0
let uu___is_Unit: t -> Prims.bool =
  fun projectee  -> match projectee with | Unit  -> true | uu____401 -> false
let uu___is_Bool: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____407 -> false
let __proj__Bool__item___0: t -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
type head = t[@@deriving show]
type annot = t FStar_Pervasives_Native.option[@@deriving show]
let app: t -> t -> t =
  fun f  ->
    fun x  ->
      match f with
      | Lam f1 -> f1 x
      | Accu (a,ts) -> Accu (a, (x :: ts))
      | Construct (i,ts) -> Construct (i, (x :: ts))
      | Unit  -> failwith "Ill-typed application"
      | Bool uu____445 -> failwith "Ill-typed application"
let mkConstruct: FStar_Syntax_Syntax.fv -> t Prims.list -> t =
  fun i  -> fun ts  -> Construct (i, ts)
let mkAccuVar: var -> t = fun v1  -> Accu ((Var v1), [])
let mkAccuMatch: FStar_Syntax_Syntax.branch Prims.list -> t -> (t -> t) -> t
  = fun b  -> fun s  -> fun c  -> Accu ((Match (b, s, c)), [])
let rec pickBranch:
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.branch Prims.list -> FStar_Syntax_Syntax.term
  =
  fun c  ->
    fun branches  ->
      match branches with
      | [] -> failwith "Branch not found"
      | ({ FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (c',args);
           FStar_Syntax_Syntax.p = uu____507;_},uu____508,e)::bs
          when FStar_Syntax_Syntax.fv_eq c c' -> e
      | b::bs -> pickBranch c bs
let rec mkBranches:
  'Auu____587 'Auu____588 'Auu____589 'Auu____590 .
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,'Auu____590,
      'Auu____589) FStar_Pervasives_Native.tuple3 Prims.list ->
      (t -> 'Auu____588) ->
        (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,'Auu____587
                                                                   FStar_Pervasives_Native.option,
          'Auu____588) FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun branches  ->
    fun cont  ->
      match branches with
      | ({ FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (fv,pats);
           FStar_Syntax_Syntax.p = uu____638;_},uu____639,uu____640)::branches'
          ->
          let uu____678 =
            FStar_List.fold_right
              (fun p  ->
                 fun uu____714  ->
                   match uu____714 with
                   | (args,bs) ->
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun in
                       let uu____762 =
                         let uu____771 =
                           let uu____778 =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_var x)
                               FStar_Range.dummyRange in
                           (uu____778, (FStar_Pervasives_Native.snd p)) in
                         uu____771 :: bs in
                       (((mkAccuVar x) :: args), uu____762)) pats ([], []) in
          (match uu____678 with
           | (args,binders) ->
               let value = Construct (fv, args) in
               let pat =
                 FStar_Syntax_Syntax.withinfo
                   (FStar_Syntax_Syntax.Pat_cons (fv, binders))
                   FStar_Range.dummyRange in
               let branch1 =
                 let uu____864 = cont value in
                 (pat, FStar_Pervasives_Native.None, uu____864) in
               let uu____869 = mkBranches branches' cont in branch1 ::
                 uu____869)
      | uu____892 -> failwith "Unexpected pattern"
let rec translate: t Prims.list -> FStar_Syntax_Syntax.term -> t =
  fun bs  ->
    fun e  ->
      let uu____929 =
        let uu____930 = FStar_Syntax_Subst.compress e in
        uu____930.FStar_Syntax_Syntax.n in
      match uu____929 with
      | FStar_Syntax_Syntax.Tm_delayed uu____933 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) -> Unit
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> Bool b
      | FStar_Syntax_Syntax.Tm_bvar db ->
          FStar_List.nth bs db.FStar_Syntax_Syntax.index
      | FStar_Syntax_Syntax.Tm_name x -> mkAccuVar x
      | FStar_Syntax_Syntax.Tm_abs (x::[],body,uu____963) ->
          Lam ((fun y  -> translate (y :: bs) body))
      | FStar_Syntax_Syntax.Tm_fvar v1 -> mkConstruct v1 []
      | FStar_Syntax_Syntax.Tm_abs (x::xs,body,uu____997) ->
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
          let uu____1092 = translate bs e1 in
          let uu____1093 = translate bs (FStar_Pervasives_Native.fst arg) in
          app uu____1092 uu____1093
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
                  let uu____1218 = pickBranch c branches in
                  translate (FStar_List.append (FStar_List.rev args) args)
                    uu____1218 in
                branch1
            | uu____1219 -> mkAccuMatch branches scrut1 case in
          let uu____1220 = translate bs scrut in case uu____1220
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let def = translate bs lb.FStar_Syntax_Syntax.lbdef in
          translate (def :: bs) body
      | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),body) ->
          failwith "Not yet implemented"
      | uu____1250 -> (debug_term e; failwith "Not yet implemented")
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
        let body = let uu____1258 = f (mkAccuVar x1) in readback uu____1258 in
        let uu____1259 =
          let uu____1260 = FStar_Syntax_Syntax.mk_binder x1 in [uu____1260] in
        FStar_Syntax_Util.abs uu____1259 body FStar_Pervasives_Native.None
    | Construct (fv,args) ->
        let args1 =
          FStar_List.map
            (fun x1  ->
               let uu____1273 = readback x1 in
               FStar_Syntax_Syntax.as_arg uu____1273) args in
        (match args1 with
         | [] ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
         | uu____1274 ->
             let uu____1277 =
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                 FStar_Pervasives_Native.None FStar_Range.dummyRange in
             FStar_Syntax_Util.mk_app uu____1277 args1)
    | Accu (Var bv,[]) -> FStar_Syntax_Syntax.bv_to_name bv
    | Accu (Var bv,ts) ->
        let args =
          map_rev
            (fun x1  ->
               let uu____1295 = readback x1 in
               FStar_Syntax_Syntax.as_arg uu____1295) ts in
        let uu____1296 = FStar_Syntax_Syntax.bv_to_name bv in
        FStar_Syntax_Util.mk_app uu____1296 args
    | Accu (Match (branches,scrut,cases),ts) ->
        let args =
          map_rev
            (fun x1  ->
               let uu____1321 = readback x1 in
               FStar_Syntax_Syntax.as_arg uu____1321) ts in
        let head1 = let uu____1323 = cases scrut in readback uu____1323 in
        (match ts with
         | [] -> head1
         | uu____1324 -> FStar_Syntax_Util.mk_app head1 args)
    | uu____1327 -> failwith "Not yet implemented"
and normalize: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  -> let uu____1329 = translate [] e in readback uu____1329