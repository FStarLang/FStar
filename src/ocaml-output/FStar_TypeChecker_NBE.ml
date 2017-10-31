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
  | Rec of (FStar_Syntax_Syntax.term,t Prims.list)
  FStar_Pervasives_Native.tuple2[@@deriving show]
and t =
  | Lam of (t -> t)
  | Accu of (atom,t Prims.list) FStar_Pervasives_Native.tuple2
  | Construct of (FStar_Syntax_Syntax.fv,t Prims.list)
  FStar_Pervasives_Native.tuple2
  | Unit
  | Bool of Prims.bool[@@deriving show]
let uu___is_Var: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____141 -> false
let __proj__Var__item___0: atom -> var =
  fun projectee  -> match projectee with | Var _0 -> _0
let uu___is_Sort: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____155 -> false
let __proj__Sort__item___0: atom -> sort =
  fun projectee  -> match projectee with | Sort _0 -> _0
let uu___is_Prod: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Prod _0 -> true | uu____173 -> false
let __proj__Prod__item___0: atom -> (t,t) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Prod _0 -> _0
let uu___is_Match: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____209 -> false
let __proj__Match__item___0:
  atom ->
    (FStar_Syntax_Syntax.branch Prims.list,t,t -> t)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Rec: atom -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____259 -> false
let __proj__Rec__item___0:
  atom ->
    (FStar_Syntax_Syntax.term,t Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Rec _0 -> _0
let uu___is_Lam: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____293 -> false
let __proj__Lam__item___0: t -> t -> t =
  fun projectee  -> match projectee with | Lam _0 -> _0
let uu___is_Accu: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____320 -> false
let __proj__Accu__item___0:
  t -> (atom,t Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Accu _0 -> _0
let uu___is_Construct: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____358 -> false
let __proj__Construct__item___0:
  t -> (FStar_Syntax_Syntax.fv,t Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Construct _0 -> _0
let uu___is_Unit: t -> Prims.bool =
  fun projectee  -> match projectee with | Unit  -> true | uu____389 -> false
let uu___is_Bool: t -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____395 -> false
let __proj__Bool__item___0: t -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
type head = t[@@deriving show]
type annot = t FStar_Pervasives_Native.option[@@deriving show]
let is_not_accu: t -> Prims.bool =
  fun x  ->
    match x with | Accu (uu____410,uu____411) -> false | uu____416 -> true
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
           FStar_Syntax_Syntax.p = uu____478;_},uu____479,e)::bs
          when FStar_Syntax_Syntax.fv_eq c c' -> e
      | b::bs -> pickBranch c bs
let rec mkBranches:
  'Auu____558 'Auu____559 'Auu____560 'Auu____561 .
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,'Auu____561,
      'Auu____560) FStar_Pervasives_Native.tuple3 Prims.list ->
      (t -> 'Auu____559) ->
        (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,'Auu____558
                                                                   FStar_Pervasives_Native.option,
          'Auu____559) FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun branches  ->
    fun cont  ->
      match branches with
      | ({ FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (fv,pats);
           FStar_Syntax_Syntax.p = uu____609;_},uu____610,uu____611)::branches'
          ->
          let uu____649 =
            FStar_List.fold_right
              (fun p  ->
                 fun uu____685  ->
                   match uu____685 with
                   | (args,bs) ->
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun in
                       let uu____733 =
                         let uu____742 =
                           let uu____749 =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_var x)
                               FStar_Range.dummyRange in
                           (uu____749, (FStar_Pervasives_Native.snd p)) in
                         uu____742 :: bs in
                       (((mkAccuVar x) :: args), uu____733)) pats ([], []) in
          (match uu____649 with
           | (args,binders) ->
               let value = Construct (fv, args) in
               let pat =
                 FStar_Syntax_Syntax.withinfo
                   (FStar_Syntax_Syntax.Pat_cons (fv, binders))
                   FStar_Range.dummyRange in
               let branch1 =
                 let uu____835 = cont value in
                 (pat, FStar_Pervasives_Native.None, uu____835) in
               let uu____840 = mkBranches branches' cont in branch1 ::
                 uu____840)
      | uu____863 -> failwith "Unexpected pattern"
let rec app: t -> t -> t =
  fun f  ->
    fun x  ->
      match f with
      | Lam f1 -> f1 x
      | Accu (a,ts) -> Accu (a, (x :: ts))
      | Construct (i,ts) -> Construct (i, (x :: ts))
      | Unit  -> failwith "Ill-typed application"
      | Bool uu____923 -> failwith "Ill-typed application"
and iapp: t -> t Prims.list -> t =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____928 ->
          let uu____931 =
            let uu____932 = FStar_List.hd args in app f uu____932 in
          let uu____933 = FStar_List.tl args in iapp uu____931 uu____933
and translate: t Prims.list -> FStar_Syntax_Syntax.term -> t =
  fun bs  ->
    fun e  ->
      let uu____940 =
        let uu____941 = FStar_Syntax_Subst.compress e in
        uu____941.FStar_Syntax_Syntax.n in
      match uu____940 with
      | FStar_Syntax_Syntax.Tm_delayed uu____944 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) -> Unit
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> Bool b
      | FStar_Syntax_Syntax.Tm_bvar db ->
          FStar_List.nth bs db.FStar_Syntax_Syntax.index
      | FStar_Syntax_Syntax.Tm_name x -> mkAccuVar x
      | FStar_Syntax_Syntax.Tm_abs (x::[],body,uu____974) ->
          Lam ((fun y  -> translate (y :: bs) body))
      | FStar_Syntax_Syntax.Tm_fvar v1 -> mkConstruct v1 []
      | FStar_Syntax_Syntax.Tm_abs (x::xs,body,uu____1008) ->
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
          let uu____1103 = translate bs e1 in
          let uu____1104 = translate bs (FStar_Pervasives_Native.fst arg) in
          app uu____1103 uu____1104
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
                  let uu____1229 = pickBranch c branches in
                  translate (FStar_List.append (FStar_List.rev args) bs)
                    uu____1229 in
                branch1
            | uu____1230 -> mkAccuMatch branches scrut1 case in
          let uu____1231 = translate bs scrut in case uu____1231
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let def = translate bs lb.FStar_Syntax_Syntax.lbdef in
          translate (def :: bs) body
      | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),body) ->
          let f = Accu ((Rec ((lb.FStar_Syntax_Syntax.lbdef), bs)), []) in
          translate (f :: bs) body
      | uu____1268 -> (debug_term e; failwith "Not yet implemented")
let rec readback: t -> FStar_Syntax_Syntax.term =
  fun x  ->
    match x with
    | Unit  -> FStar_Syntax_Syntax.unit_const
    | Bool (true ) -> FStar_Syntax_Util.exp_true_bool
    | Bool (false ) -> FStar_Syntax_Util.exp_false_bool
    | Lam f ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.tun in
        let body = let uu____1279 = f (mkAccuVar x1) in readback uu____1279 in
        let uu____1280 =
          let uu____1281 = FStar_Syntax_Syntax.mk_binder x1 in [uu____1281] in
        FStar_Syntax_Util.abs uu____1280 body FStar_Pervasives_Native.None
    | Construct (fv,args) ->
        let args1 =
          FStar_List.map
            (fun x1  ->
               let uu____1294 = readback x1 in
               FStar_Syntax_Syntax.as_arg uu____1294) args in
        (match args1 with
         | [] ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
               FStar_Pervasives_Native.None FStar_Range.dummyRange
         | uu____1295 ->
             let uu____1298 =
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                 FStar_Pervasives_Native.None FStar_Range.dummyRange in
             FStar_Syntax_Util.mk_app uu____1298 args1)
    | Accu (Var bv,[]) -> FStar_Syntax_Syntax.bv_to_name bv
    | Accu (Var bv,ts) ->
        let args =
          map_rev
            (fun x1  ->
               let uu____1316 = readback x1 in
               FStar_Syntax_Syntax.as_arg uu____1316) ts in
        let uu____1317 = FStar_Syntax_Syntax.bv_to_name bv in
        FStar_Syntax_Util.mk_app uu____1317 args
    | Accu (Match (branches,scrut,cases),ts) ->
        let args =
          map_rev
            (fun x1  ->
               let uu____1342 = readback x1 in
               FStar_Syntax_Syntax.as_arg uu____1342) ts in
        let head1 = let uu____1344 = cases scrut in readback uu____1344 in
        (match ts with
         | [] -> head1
         | uu____1345 -> FStar_Syntax_Util.mk_app head1 args)
    | Accu (Rec (f,bs),ts) ->
        let uu____1359 =
          let uu____1360 = FStar_Syntax_Subst.compress f in
          uu____1360.FStar_Syntax_Syntax.n in
        (match uu____1359 with
         | FStar_Syntax_Syntax.Tm_abs (args,uu____1364,uu____1365) ->
             let uu____1386 =
               ((FStar_List.length ts) = (FStar_List.length args)) &&
                 (let uu____1392 = FStar_List.map is_not_accu ts in
                  FStar_List.fold_right (fun x1  -> fun y  -> x1 && y)
                    uu____1392 true) in
             if uu____1386
             then
               let uu____1399 =
                 let uu____1400 =
                   translate ((Accu ((Rec (f, bs)), [])) :: bs) f in
                 iapp uu____1400 ts in
               readback uu____1399
             else
               failwith
                 "TODO: reading back a partially applied recursive function not yet implemented"
         | uu____1406 -> failwith "Recursive definition not a function")
    | uu____1407 -> failwith "Not yet implemented"
let normalize: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  -> let uu____1412 = translate [] e in readback uu____1412