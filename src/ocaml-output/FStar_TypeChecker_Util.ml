open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv Prims.option* FStar_Syntax_Syntax.lcomp)
let report:
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let _0_239 = FStar_TypeChecker_Env.get_range env in
      let _0_238 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.report _0_239 _0_238
let is_type: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____15 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
    match uu____15 with
    | FStar_Syntax_Syntax.Tm_type uu____16 -> true
    | uu____17 -> false
let t_binders:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    let _0_240 = FStar_TypeChecker_Env.all_binders env in
    FStar_All.pipe_right _0_240
      (FStar_List.filter
         (fun uu____29  ->
            match uu____29 with
            | (x,uu____33) -> is_type x.FStar_Syntax_Syntax.sort))
let new_uvar_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____43 =
          (FStar_Options.full_context_dependency ()) ||
            (let _0_241 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_241) in
        if uu____43
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let _0_242 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar _0_242 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  = fun env  -> fun k  -> Prims.fst (new_uvar_aux env k)
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___91_53  ->
    match uu___91_53 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____55);
        FStar_Syntax_Syntax.tk = uu____56;
        FStar_Syntax_Syntax.pos = uu____57;
        FStar_Syntax_Syntax.vars = uu____58;_} -> uv
    | uu____73 -> failwith "Impossible"
let new_implicit_var:
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term* (FStar_Syntax_Syntax.uvar*
            FStar_Range.range) Prims.list* FStar_TypeChecker_Env.guard_t)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          let uu____92 =
            FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid in
          match uu____92 with
          | Some (uu____105::(tm,uu____107)::[]) ->
              let t =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))))
                  None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____151 ->
              let uu____158 = new_uvar_aux env k in
              (match uu____158 with
               | (t,u) ->
                   let g =
                     let uu___111_170 = FStar_TypeChecker_Rel.trivial_guard in
                     let _0_245 =
                       let _0_244 =
                         let _0_243 = as_uvar u in
                         (reason, env, _0_243, t, k, r) in
                       [_0_244] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___111_170.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___111_170.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___111_170.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = _0_245
                     } in
                   let _0_248 =
                     let _0_247 = let _0_246 = as_uvar u in (_0_246, r) in
                     [_0_247] in
                   (t, _0_248, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____200 = Prims.op_Negation (FStar_Util.set_is_empty uvs) in
      if uu____200
      then
        let us =
          let _0_250 =
            let _0_249 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____211  ->
                 match uu____211 with
                 | (x,uu____219) -> FStar_Syntax_Print.uvar_to_string x)
              _0_249 in
          FStar_All.pipe_right _0_250 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let _0_252 =
            let _0_251 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us _0_251 in
          FStar_Errors.report r _0_252);
         FStar_Options.pop ())
      else ()
let force_sort':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____245 = FStar_ST.read s.FStar_Syntax_Syntax.tk in
    match uu____245 with
    | None  ->
        failwith
          (let _0_254 = FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos in
           let _0_253 = FStar_Syntax_Print.term_to_string s in
           FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
             _0_254 _0_253)
    | Some tk -> tk
let force_sort s =
  (FStar_Syntax_Syntax.mk (force_sort' s)) None s.FStar_Syntax_Syntax.pos
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.typ*
        Prims.bool)
  =
  fun env  ->
    fun uu____280  ->
      match uu____280 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____287;
          FStar_Syntax_Syntax.lbdef = e;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname in
          let t = FStar_Syntax_Subst.compress t in
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (if univ_vars <> []
                then
                  failwith
                    "Impossible: non-empty universe variables but the type is unknown"
                else ();
                (let r = FStar_TypeChecker_Env.get_range env in
                 let mk_binder scope a =
                   let uu____319 =
                     (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n in
                   match uu____319 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____322 = FStar_Syntax_Util.type_u () in
                       (match uu____322 with
                        | (k,uu____328) ->
                            let t =
                              let _0_255 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right _0_255 Prims.fst in
                            ((let uu___112_332 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___112_332.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___112_332.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), false))
                   | uu____333 -> (a, true) in
                 let rec aux must_check_ty vars e =
                   let e = FStar_Syntax_Subst.compress e in
                   match e.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e,uu____358) ->
                       aux must_check_ty vars e
                   | FStar_Syntax_Syntax.Tm_ascribed (e,t,uu____365) ->
                       (t, true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____392) ->
                       let uu____415 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____439  ->
                                 fun uu____440  ->
                                   match (uu____439, uu____440) with
                                   | ((scope,bs,must_check_ty),(a,imp)) ->
                                       let uu____482 =
                                         if must_check_ty
                                         then (a, true)
                                         else mk_binder scope a in
                                       (match uu____482 with
                                        | (tb,must_check_ty) ->
                                            let b = (tb, imp) in
                                            let bs = FStar_List.append bs [b] in
                                            let scope =
                                              FStar_List.append scope [b] in
                                            (scope, bs, must_check_ty)))
                              (vars, [], must_check_ty)) in
                       (match uu____415 with
                        | (scope,bs,must_check_ty) ->
                            let uu____543 = aux must_check_ty scope body in
                            (match uu____543 with
                             | (res,must_check_ty) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t ->
                                       let uu____560 =
                                         FStar_Options.ml_ish () in
                                       if uu____560
                                       then FStar_Syntax_Util.ml_comp t r
                                       else FStar_Syntax_Syntax.mk_Total t
                                   | FStar_Util.Inr c -> c in
                                 let t = FStar_Syntax_Util.arrow bs c in
                                 ((let uu____567 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____567
                                   then
                                     let _0_258 =
                                       FStar_Range.string_of_range r in
                                     let _0_257 =
                                       FStar_Syntax_Print.term_to_string t in
                                     let _0_256 =
                                       FStar_Util.string_of_bool
                                         must_check_ty in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       _0_258 _0_257 _0_256
                                   else ());
                                  ((FStar_Util.Inl t), must_check_ty))))
                   | uu____575 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let _0_260 =
                            FStar_Util.Inl
                              (let _0_259 =
                                 FStar_TypeChecker_Rel.new_uvar r vars
                                   FStar_Syntax_Util.ktype0 in
                               FStar_All.pipe_right _0_259 Prims.fst) in
                          (_0_260, false)) in
                 let uu____587 =
                   let _0_261 = t_binders env in aux false _0_261 e in
                 match uu____587 with
                 | (t,b) ->
                     let t =
                       match t with
                       | FStar_Util.Inr c ->
                           let uu____608 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____608
                           then FStar_Syntax_Util.comp_result c
                           else
                             Prims.raise
                               (FStar_Errors.Error
                                  (let _0_263 =
                                     let _0_262 =
                                       FStar_Syntax_Print.comp_to_string c in
                                     FStar_Util.format1
                                       "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                       _0_262 in
                                   (_0_263, rng)))
                       | FStar_Util.Inl t -> t in
                     ([], t, b)))
           | uu____618 ->
               let uu____619 = FStar_Syntax_Subst.open_univ_vars univ_vars t in
               (match uu____619 with | (univ_vars,t) -> (univ_vars, t, false)))
let pat_as_exps:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term
          Prims.list* FStar_Syntax_Syntax.pat)
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        let rec pat_as_arg_with_env allow_wc_dependence env p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let e =
                (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c))
                  None p.FStar_Syntax_Syntax.p in
              ([], [], [], env, e, p)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____702) ->
              let uu____707 = FStar_Syntax_Util.type_u () in
              (match uu____707 with
               | (k,uu____720) ->
                   let t = new_uvar env k in
                   let x =
                     let uu___113_723 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___113_723.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___113_723.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____724 =
                     let _0_264 = FStar_TypeChecker_Env.all_binders env in
                     FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p
                       _0_264 t in
                   (match uu____724 with
                    | (e,u) ->
                        let p =
                          let uu___114_741 = p in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___114_741.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___114_741.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env, e, p)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____748 = FStar_Syntax_Util.type_u () in
              (match uu____748 with
               | (t,uu____761) ->
                   let x =
                     let uu___115_763 = x in
                     let _0_265 = new_uvar env t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___115_763.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___115_763.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = _0_265
                     } in
                   let env =
                     if allow_wc_dependence
                     then FStar_TypeChecker_Env.push_bv env x
                     else env in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x))
                       None p.FStar_Syntax_Syntax.p in
                   ([x], [], [x], env, e, p))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____783 = FStar_Syntax_Util.type_u () in
              (match uu____783 with
               | (t,uu____796) ->
                   let x =
                     let uu___116_798 = x in
                     let _0_266 = new_uvar env t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___116_798.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___116_798.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = _0_266
                     } in
                   let env = FStar_TypeChecker_Env.push_bv env x in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x))
                       None p.FStar_Syntax_Syntax.p in
                   ([x], [x], [], env, e, p))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____828 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____884  ->
                        fun uu____885  ->
                          match (uu____884, uu____885) with
                          | ((b,a,w,env,args,pats),(p,imp)) ->
                              let uu____984 =
                                pat_as_arg_with_env allow_wc_dependence env p in
                              (match uu____984 with
                               | (b',a',w',env,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env,
                                     (arg :: args), ((pat, imp) :: pats))))
                     ([], [], [], env, [], [])) in
              (match uu____828 with
               | (b,a,w,env,args,pats) ->
                   let e =
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_meta
                           (let _0_269 =
                              (let _0_268 = FStar_Syntax_Syntax.fv_to_tm fv in
                               let _0_267 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app _0_268 _0_267)
                                None p.FStar_Syntax_Syntax.p in
                            (_0_269,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Data_app))))) None
                       p.FStar_Syntax_Syntax.p in
                   let _0_272 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let _0_271 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let _0_270 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (_0_272, _0_271, _0_270, env, e,
                     (let uu___117_1129 = p in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats)));
                        FStar_Syntax_Syntax.ty =
                          (uu___117_1129.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___117_1129.FStar_Syntax_Syntax.p)
                      })))
          | FStar_Syntax_Syntax.Pat_disj uu____1135 -> failwith "impossible" in
        let rec elaborate_pat env p =
          let maybe_dot inaccessible a r =
            if allow_implicits && inaccessible
            then
              FStar_Syntax_Syntax.withinfo
                (FStar_Syntax_Syntax.Pat_dot_term
                   (a, FStar_Syntax_Syntax.tun))
                FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r
            else
              FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a)
                FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r in
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let pats =
                FStar_List.map
                  (fun uu____1204  ->
                     match uu____1204 with
                     | (p,imp) ->
                         let _0_273 = elaborate_pat env p in (_0_273, imp))
                  pats in
              let uu____1221 =
                FStar_TypeChecker_Env.lookup_datacon env
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1221 with
               | (uu____1230,t) ->
                   let uu____1232 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1232 with
                    | (f,uu____1243) ->
                        let rec aux formals pats =
                          match (formals, pats) with
                          | ([],[]) -> []
                          | ([],uu____1318::uu____1319) ->
                              Prims.raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1354::uu____1355,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1395  ->
                                      match uu____1395 with
                                      | (t,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let _0_274 =
                                                   Some
                                                     (FStar_Syntax_Syntax.range_of_bv
                                                        t) in
                                                 FStar_Syntax_Syntax.new_bv
                                                   _0_274
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let _0_275 =
                                                 maybe_dot inaccessible a r in
                                               (_0_275, true)
                                           | uu____1420 ->
                                               Prims.raise
                                                 (FStar_Errors.Error
                                                    (let _0_277 =
                                                       let _0_276 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p in
                                                       FStar_Util.format1
                                                         "Insufficient pattern arguments (%s)"
                                                         _0_276 in
                                                     (_0_277,
                                                       (FStar_Ident.range_of_lid
                                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))))))
                          | (f::formals',(p,p_imp)::pats') ->
                              (match f with
                               | (uu____1472,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1473))
                                   when p_imp ->
                                   let _0_278 = aux formals' pats' in
                                   (p, true) :: _0_278
                               | (uu____1481,Some
                                  (FStar_Syntax_Syntax.Implicit
                                  inaccessible)) ->
                                   let a =
                                     FStar_Syntax_Syntax.new_bv
                                       (Some (p.FStar_Syntax_Syntax.p))
                                       FStar_Syntax_Syntax.tun in
                                   let p =
                                     maybe_dot inaccessible a
                                       (FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                   let _0_279 = aux formals' pats in
                                   (p, true) :: _0_279
                               | (uu____1498,imp) ->
                                   let _0_282 =
                                     let _0_280 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p, _0_280) in
                                   let _0_281 = aux formals' pats' in _0_282
                                     :: _0_281) in
                        let uu___118_1508 = p in
                        let _0_284 =
                          FStar_Syntax_Syntax.Pat_cons
                            (let _0_283 = aux f pats in (fv, _0_283)) in
                        {
                          FStar_Syntax_Syntax.v = _0_284;
                          FStar_Syntax_Syntax.ty =
                            (uu___118_1508.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___118_1508.FStar_Syntax_Syntax.p)
                        }))
          | uu____1516 -> p in
        let one_pat allow_wc_dependence env p =
          let p = elaborate_pat env p in
          let uu____1542 = pat_as_arg_with_env allow_wc_dependence env p in
          match uu____1542 with
          | (b,a,w,env,arg,p) ->
              let uu____1572 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1572 with
               | Some x ->
                   Prims.raise
                     (FStar_Errors.Error
                        (let _0_285 =
                           FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                         (_0_285, (p.FStar_Syntax_Syntax.p))))
               | uu____1593 -> (b, a, w, arg, p)) in
        let top_level_pat_as_args env p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_disj [] -> failwith "impossible"
          | FStar_Syntax_Syntax.Pat_disj (q::pats) ->
              let uu____1636 = one_pat false env q in
              (match uu____1636 with
               | (b,a,uu____1652,te,q) ->
                   let uu____1661 =
                     FStar_List.fold_right
                       (fun p  ->
                          fun uu____1677  ->
                            match uu____1677 with
                            | (w,args,pats) ->
                                let uu____1701 = one_pat false env p in
                                (match uu____1701 with
                                 | (b',a',w',arg,p) ->
                                     let uu____1727 =
                                       Prims.op_Negation
                                         (FStar_Util.multiset_equiv
                                            FStar_Syntax_Syntax.bv_eq a a') in
                                     if uu____1727
                                     then
                                       Prims.raise
                                         (FStar_Errors.Error
                                            (let _0_287 =
                                               FStar_TypeChecker_Err.disjunctive_pattern_vars
                                                 a a' in
                                             let _0_286 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             (_0_287, _0_286)))
                                     else
                                       (let _0_289 =
                                          let _0_288 =
                                            FStar_Syntax_Syntax.as_arg arg in
                                          _0_288 :: args in
                                        ((FStar_List.append w' w), _0_289, (p
                                          :: pats))))) pats ([], [], []) in
                   (match uu____1661 with
                    | (w,args,pats) ->
                        let _0_291 =
                          let _0_290 = FStar_Syntax_Syntax.as_arg te in
                          _0_290 :: args in
                        ((FStar_List.append b w), _0_291,
                          (let uu___119_1765 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_disj (q :: pats));
                             FStar_Syntax_Syntax.ty =
                               (uu___119_1765.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___119_1765.FStar_Syntax_Syntax.p)
                           }))))
          | uu____1766 ->
              let uu____1767 = one_pat true env p in
              (match uu____1767 with
               | (b,uu____1782,uu____1783,arg,p) ->
                   let _0_293 =
                     let _0_292 = FStar_Syntax_Syntax.as_arg arg in [_0_292] in
                   (b, _0_293, p)) in
        let uu____1794 = top_level_pat_as_args env p in
        match uu____1794 with
        | (b,args,p) ->
            let exps = FStar_All.pipe_right args (FStar_List.map Prims.fst) in
            (b, exps, p)
let decorate_pattern:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.pat
  =
  fun env  ->
    fun p  ->
      fun exps  ->
        let qq = p in
        let rec aux p e =
          let pkg q t =
            FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p in
          let e = FStar_Syntax_Util.unmeta e in
          match ((p.FStar_Syntax_Syntax.v), (e.FStar_Syntax_Syntax.n)) with
          | (uu____1865,FStar_Syntax_Syntax.Tm_uinst (e,uu____1867)) ->
              aux p e
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1872,FStar_Syntax_Syntax.Tm_constant uu____1873) ->
              let _0_294 = force_sort' e in
              pkg p.FStar_Syntax_Syntax.v _0_294
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 failwith
                   (let _0_296 = FStar_Syntax_Print.bv_to_string x in
                    let _0_295 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      _0_296 _0_295)
               else ();
               (let uu____1879 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____1879
                then
                  let _0_298 = FStar_Syntax_Print.bv_to_string x in
                  let _0_297 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" _0_298
                    _0_297
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x =
                  let uu___120_1883 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___120_1883.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___120_1883.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1887 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1887
                then
                  failwith
                    (let _0_300 = FStar_Syntax_Print.bv_to_string x in
                     let _0_299 = FStar_Syntax_Print.bv_to_string y in
                     FStar_Util.format2
                       "Expected pattern variable %s; got %s" _0_300 _0_299)
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x =
                  let uu___121_1891 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___121_1891.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___121_1891.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1893),uu____1894) ->
              let s = force_sort e in
              let x =
                let uu___122_1903 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___122_1903.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___122_1903.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1916 =
                  Prims.op_Negation (FStar_Syntax_Syntax.fv_eq fv fv') in
                if uu____1916
                then
                  failwith
                    (FStar_Util.format2
                       "Expected pattern constructor %s; got %s"
                       ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str)
                else ());
               (let _0_301 = force_sort' e in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) _0_301))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
                FStar_Syntax_Syntax.vars = _;_},args))
            |(FStar_Syntax_Syntax.Pat_cons
              (fv,argpats),FStar_Syntax_Syntax.Tm_app
              ({
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_);
                 FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
                 FStar_Syntax_Syntax.vars = _;_},args))
              ->
              ((let uu____1996 =
                  let _0_302 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right _0_302 Prims.op_Negation in
                if uu____1996
                then
                  failwith
                    (FStar_Util.format2
                       "Expected pattern constructor %s; got %s"
                       ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str)
                else ());
               (let fv = fv' in
                let rec match_args matched_pats args argpats =
                  match (args, argpats) with
                  | ([],[]) ->
                      let _0_303 = force_sort' e in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv, (FStar_List.rev matched_pats))) _0_303
                  | (arg::args,(argpat,uu____2096)::argpats) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2146) ->
                           let x =
                             let _0_304 = force_sort e in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p.FStar_Syntax_Syntax.p)) _0_304 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args
                             argpats
                       | ((e,imp),uu____2175) ->
                           let pat =
                             let _0_306 = aux argpat e in
                             let _0_305 = FStar_Syntax_Syntax.is_implicit imp in
                             (_0_306, _0_305) in
                           match_args (pat :: matched_pats) args argpats)
                  | uu____2192 ->
                      failwith
                        (let _0_308 = FStar_Syntax_Print.pat_to_string p in
                         let _0_307 = FStar_Syntax_Print.term_to_string e in
                         FStar_Util.format2
                           "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                           _0_308 _0_307) in
                match_args [] args argpats))
          | uu____2212 ->
              failwith
                (let _0_312 =
                   FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                 let _0_311 = FStar_Syntax_Print.pat_to_string qq in
                 let _0_310 =
                   let _0_309 =
                     FStar_All.pipe_right exps
                       (FStar_List.map FStar_Syntax_Print.term_to_string) in
                   FStar_All.pipe_right _0_309 (FStar_String.concat "\n\t") in
                 FStar_Util.format3
                   "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                   _0_312 _0_311 _0_310) in
        match ((p.FStar_Syntax_Syntax.v), exps) with
        | (FStar_Syntax_Syntax.Pat_disj ps,uu____2220) when
            (FStar_List.length ps) = (FStar_List.length exps) ->
            let ps = FStar_List.map2 aux ps exps in
            FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj ps)
              FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
              p.FStar_Syntax_Syntax.p
        | (uu____2236,e::[]) -> aux p e
        | uu____2239 -> failwith "Unexpected number of patterns"
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty) in
    let mk f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2276 =
      match uu____2276 with
      | (p,i) ->
          let uu____2286 = decorated_pattern_as_term p in
          (match uu____2286 with
           | (vars,te) ->
               let _0_314 =
                 let _0_313 = FStar_Syntax_Syntax.as_implicit i in
                 (te, _0_313) in
               (vars, _0_314)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____2305 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Pat_constant c ->
        let _0_315 = mk (FStar_Syntax_Syntax.Tm_constant c) in ([], _0_315)
    | FStar_Syntax_Syntax.Pat_wild x|FStar_Syntax_Syntax.Pat_var x ->
        let _0_316 = mk (FStar_Syntax_Syntax.Tm_name x) in ([x], _0_316)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2328 =
          let _0_317 = FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right _0_317 FStar_List.unzip in
        (match uu____2328 with
         | (vars,args) ->
             let vars = FStar_List.flatten vars in
             let _0_319 =
               mk
                 (FStar_Syntax_Syntax.Tm_app
                    (let _0_318 = FStar_Syntax_Syntax.fv_to_tm fv in
                     (_0_318, args))) in
             (vars, _0_319))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____2415)::[] -> wp
      | uu____2428 ->
          failwith
            (let _0_321 =
               let _0_320 =
                 FStar_List.map
                   (fun uu____2439  ->
                      match uu____2439 with
                      | (x,uu____2443) -> FStar_Syntax_Print.term_to_string x)
                   c.FStar_Syntax_Syntax.effect_args in
               FStar_All.pipe_right _0_320 (FStar_String.concat ", ") in
             FStar_Util.format2
               "Impossible: Got a computation %s with effect args [%s]"
               (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str _0_321) in
    let _0_322 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (_0_322, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
        -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2471 = destruct_comp c in
        match uu____2471 with
        | (u,uu____2476,wp) ->
            let _0_324 =
              let _0_323 =
                FStar_Syntax_Syntax.as_arg
                  (lift c.FStar_Syntax_Syntax.result_typ wp) in
              [_0_323] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = _0_324;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2487 =
          let _0_326 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let _0_325 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env _0_326 _0_325 in
        match uu____2487 with | (m,uu____2492,uu____2493) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2503 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2503
        then FStar_Syntax_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
let lift_and_destruct:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl* FStar_Syntax_Syntax.bv*
          FStar_Syntax_Syntax.term)* (FStar_Syntax_Syntax.universe*
          FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.typ)*
          (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.typ*
          FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c1 = FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1 in
        let c2 = FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2 in
        let uu____2528 =
          FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name
            c2.FStar_Syntax_Syntax.effect_name in
        match uu____2528 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c1 m lift1 in
            let m2 = lift_comp c2 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2558 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2558 with
             | (a,kwp) ->
                 let _0_328 = destruct_comp m1 in
                 let _0_327 = destruct_comp m2 in
                 ((md, a, kwp), _0_328, _0_327))
let is_pure_effect:
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l = FStar_TypeChecker_Env.norm_eff_name env l in
      FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid
let is_pure_or_ghost_effect:
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l = FStar_TypeChecker_Env.norm_eff_name env l in
      (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid)
let mk_comp_l:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags  ->
            FStar_Syntax_Syntax.mk_Comp
              (let _0_330 =
                 let _0_329 = FStar_Syntax_Syntax.as_arg wp in [_0_329] in
               {
                 FStar_Syntax_Syntax.comp_univs = [u_result];
                 FStar_Syntax_Syntax.effect_name = mname;
                 FStar_Syntax_Syntax.result_typ = result;
                 FStar_Syntax_Syntax.effect_args = _0_330;
                 FStar_Syntax_Syntax.flags = flags
               })
let mk_comp:
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname
let lax_mk_tot_or_comp_l:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags  ->
          if FStar_Ident.lid_equals mname FStar_Syntax_Const.effect_Tot_lid
          then FStar_Syntax_Syntax.mk_Total' result (Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
let subst_lcomp:
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun subst  ->
    fun lc  ->
      let uu___123_2654 = lc in
      let _0_332 =
        FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___123_2654.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = _0_332;
        FStar_Syntax_Syntax.cflags =
          (uu___123_2654.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2655  ->
             let _0_331 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst _0_331)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2659 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
    match uu____2659 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2660 -> true
    | uu____2668 -> false
let return_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun t  ->
      fun v  ->
        let c =
          let uu____2679 =
            let _0_333 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation _0_333 in
          if uu____2679
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_Util.must
                 (FStar_TypeChecker_Env.effect_decl_opt env
                    FStar_Syntax_Const.effect_PURE_lid) in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2684 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2684
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2686 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____2686 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let _0_339 =
                        (let _0_338 =
                           FStar_TypeChecker_Env.inst_effect_fun_with 
                             [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                         let _0_337 =
                           let _0_336 = FStar_Syntax_Syntax.as_arg t in
                           let _0_335 =
                             let _0_334 = FStar_Syntax_Syntax.as_arg v in
                             [_0_334] in
                           _0_336 :: _0_335 in
                         FStar_Syntax_Syntax.mk_Tm_app _0_338 _0_337)
                          (Some (k.FStar_Syntax_Syntax.n))
                          v.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env _0_339) in
             (mk_comp m) u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____2699 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____2699
         then
           let _0_342 = FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos in
           let _0_341 = FStar_Syntax_Print.term_to_string v in
           let _0_340 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" _0_342
             _0_341 _0_340
         else ());
        c
let bind:
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term Prims.option ->
        FStar_Syntax_Syntax.lcomp ->
          lcomp_with_binder -> FStar_Syntax_Syntax.lcomp
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____2716  ->
            match uu____2716 with
            | (b,lc2) ->
                let lc1 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc2 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc1 lc2 in
                ((let uu____2726 =
                    FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                  if uu____2726
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let _0_345 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let _0_344 = FStar_Syntax_Print.lcomp_to_string lc1 in
                    let _0_343 = FStar_Syntax_Print.lcomp_to_string lc2 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      _0_345 _0_344 bstr _0_343
                  else ());
                 (let bind_it uu____2734 =
                    let uu____2735 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____2735
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc2.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc2.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc1.FStar_Syntax_Syntax.comp () in
                       let c2 = lc2.FStar_Syntax_Syntax.comp () in
                       (let uu____2745 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Extreme in
                        if uu____2745
                        then
                          let _0_350 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let _0_349 = FStar_Syntax_Print.lcomp_to_string lc1 in
                          let _0_348 = FStar_Syntax_Print.comp_to_string c1 in
                          let _0_347 = FStar_Syntax_Print.lcomp_to_string lc2 in
                          let _0_346 = FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n" _0_350
                            _0_349 _0_348 _0_347 _0_346
                        else ());
                       (let try_simplify uu____2754 =
                          let aux uu____2763 =
                            let uu____2764 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____2764
                            then
                              match b with
                              | None  -> Some (c2, "trivial no binder")
                              | Some uu____2781 ->
                                  let uu____2782 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____2782
                                   then Some (c2, "trivial ml")
                                   else None)
                            else
                              (let uu____2800 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____2800
                               then Some (c2, "both ml")
                               else None) in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                Some
                                  (let _0_351 =
                                     FStar_Syntax_Subst.subst_comp
                                       [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                   (_0_351, reason))
                            | uu____2835 -> aux () in
                          let uu____2840 =
                            (FStar_Syntax_Util.is_total_comp c1) &&
                              (FStar_Syntax_Util.is_total_comp c2) in
                          if uu____2840
                          then subst_c2 "both total"
                          else
                            (let uu____2845 =
                               (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                 (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                             if uu____2845
                             then
                               Some
                                 (let _0_352 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2) in
                                  (_0_352, "both gtot"))
                             else
                               (match (e1opt, b) with
                                | (Some e,Some x) ->
                                    let uu____2861 =
                                      (FStar_Syntax_Util.is_total_comp c1) &&
                                        (Prims.op_Negation
                                           (FStar_Syntax_Syntax.is_null_bv x)) in
                                    if uu____2861
                                    then subst_c2 "substituted e"
                                    else aux ()
                                | uu____2866 -> aux ())) in
                        let uu____2871 = try_simplify () in
                        match uu____2871 with
                        | Some (c,reason) -> c
                        | None  ->
                            let uu____2881 = lift_and_destruct env c1 c2 in
                            (match uu____2881 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let _0_353 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [_0_353]
                                   | Some x ->
                                       let _0_354 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [_0_354] in
                                 let mk_lam wp =
                                   FStar_Syntax_Util.abs bs wp
                                     (Some
                                        (FStar_Util.Inr
                                           (FStar_Syntax_Const.effect_Tot_lid,
                                             [FStar_Syntax_Syntax.TOTAL]))) in
                                 let r1 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_constant
                                         (FStar_Const.Const_range r1))) None
                                     r1 in
                                 let wp_args =
                                   let _0_363 = FStar_Syntax_Syntax.as_arg r1 in
                                   let _0_362 =
                                     let _0_361 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let _0_360 =
                                       let _0_359 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let _0_358 =
                                         let _0_357 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let _0_356 =
                                           let _0_355 =
                                             FStar_Syntax_Syntax.as_arg
                                               (mk_lam wp2) in
                                           [_0_355] in
                                         _0_357 :: _0_356 in
                                       _0_359 :: _0_358 in
                                     _0_361 :: _0_360 in
                                   _0_363 :: _0_362 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   (let _0_364 =
                                      FStar_TypeChecker_Env.inst_effect_fun_with
                                        [u_t1; u_t2] env md
                                        md.FStar_Syntax_Syntax.bind_wp in
                                    FStar_Syntax_Syntax.mk_Tm_app _0_364
                                      wp_args) None
                                     t2.FStar_Syntax_Syntax.pos in
                                 let c = (mk_comp md) u_t2 t2 wp [] in c))) in
                  {
                    FStar_Syntax_Syntax.eff_name = joined_eff;
                    FStar_Syntax_Syntax.res_typ =
                      (lc2.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = [];
                    FStar_Syntax_Syntax.comp = bind_it
                  }))
let label:
  Prims.string ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax
  =
  fun reason  ->
    fun r  ->
      fun f  ->
        (FStar_Syntax_Syntax.mk
           (FStar_Syntax_Syntax.Tm_meta
              (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false)))))
          None f.FStar_Syntax_Syntax.pos
let label_opt:
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) Prims.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | None  -> f
          | Some reason ->
              let uu____2994 =
                let _0_365 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation _0_365 in
              if uu____2994
              then f
              else (let _0_366 = reason () in label _0_366 r f)
let label_guard:
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___124_3006 = g in
            let _0_367 =
              FStar_TypeChecker_Common.NonTrivial (label reason r f) in
            {
              FStar_TypeChecker_Env.guard_f = _0_367;
              FStar_TypeChecker_Env.deferred =
                (uu___124_3006.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___124_3006.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___124_3006.FStar_TypeChecker_Env.implicits)
            }
let weaken_guard:
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2 in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____3016 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3033 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3037 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3037
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____3044 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3044
                 then c
                 else
                   (let c =
                      FStar_TypeChecker_Normalize.unfold_effect_abbrev env c in
                    let uu____3049 = destruct_comp c in
                    match uu____3049 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c.FStar_Syntax_Syntax.effect_name in
                        let wp =
                          (let _0_374 =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [u_res_t] env md
                               md.FStar_Syntax_Syntax.assume_p in
                           let _0_373 =
                             let _0_372 = FStar_Syntax_Syntax.as_arg res_t in
                             let _0_371 =
                               let _0_370 = FStar_Syntax_Syntax.as_arg f in
                               let _0_369 =
                                 let _0_368 = FStar_Syntax_Syntax.as_arg wp in
                                 [_0_368] in
                               _0_370 :: _0_369 in
                             _0_372 :: _0_371 in
                           FStar_Syntax_Syntax.mk_Tm_app _0_374 _0_373) None
                            wp.FStar_Syntax_Syntax.pos in
                        (mk_comp md) u_res_t res_t wp
                          c.FStar_Syntax_Syntax.flags)) in
        let uu___125_3066 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___125_3066.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___125_3066.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___125_3066.FStar_Syntax_Syntax.cflags);
          FStar_Syntax_Syntax.comp = weaken
        }
let strengthen_precondition:
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp* FStar_TypeChecker_Env.guard_t)
  =
  fun reason  ->
    fun env  ->
      fun e  ->
        fun lc  ->
          fun g0  ->
            let uu____3093 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3093
            then (lc, g0)
            else
              ((let uu____3098 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3098
                then
                  let _0_376 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let _0_375 = FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    _0_376 _0_375
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___92_3104  ->
                          match uu___92_3104 with
                          | FStar_Syntax_Syntax.RETURN 
                            |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3106 -> [])) in
                let strengthen uu____3112 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g0 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3120 = FStar_TypeChecker_Rel.guard_form g0 in
                     match uu____3120 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c =
                           let uu____3127 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (Prims.op_Negation
                                  (FStar_Syntax_Util.is_partial_return c)) in
                           if uu____3127
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let _0_378 =
                                 let _0_377 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   _0_377 in
                               FStar_Syntax_Util.comp_set_flags _0_378
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3138 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3138
                           then
                             let _0_380 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let _0_379 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               _0_380 _0_379
                           else ());
                          (let c =
                             FStar_TypeChecker_Normalize.unfold_effect_abbrev
                               env c in
                           let uu____3141 = destruct_comp c in
                           match uu____3141 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c.FStar_Syntax_Syntax.effect_name in
                               let wp =
                                 (let _0_389 =
                                    FStar_TypeChecker_Env.inst_effect_fun_with
                                      [u_res_t] env md
                                      md.FStar_Syntax_Syntax.assert_p in
                                  let _0_388 =
                                    let _0_387 =
                                      FStar_Syntax_Syntax.as_arg res_t in
                                    let _0_386 =
                                      let _0_385 =
                                        let _0_382 =
                                          let _0_381 =
                                            FStar_TypeChecker_Env.get_range
                                              env in
                                          label_opt env reason _0_381 f in
                                        FStar_All.pipe_left
                                          FStar_Syntax_Syntax.as_arg _0_382 in
                                      let _0_384 =
                                        let _0_383 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [_0_383] in
                                      _0_385 :: _0_384 in
                                    _0_387 :: _0_386 in
                                  FStar_Syntax_Syntax.mk_Tm_app _0_389 _0_388)
                                   None wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3159 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3159
                                 then
                                   let _0_390 =
                                     FStar_Syntax_Print.term_to_string wp in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     _0_390
                                 else ());
                                (let c2 = (mk_comp md) u_res_t res_t wp flags in
                                 c2))))) in
                let _0_394 =
                  let uu___126_3162 = lc in
                  let _0_393 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let _0_392 =
                    let uu____3163 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let _0_391 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation _0_391) in
                    if uu____3163 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = _0_393;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___126_3162.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = _0_392;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (_0_394,
                  (let uu___127_3166 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___127_3166.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___127_3166.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___127_3166.FStar_TypeChecker_Env.implicits)
                   }))))
let add_equality_to_post_condition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun comp  ->
      fun res_t  ->
        let md_pure =
          FStar_TypeChecker_Env.get_effect_decl env
            FStar_Syntax_Const.effect_PURE_lid in
        let x = FStar_Syntax_Syntax.new_bv None res_t in
        let y = FStar_Syntax_Syntax.new_bv None res_t in
        let uu____3181 =
          let _0_396 = FStar_Syntax_Syntax.bv_to_name x in
          let _0_395 = FStar_Syntax_Syntax.bv_to_name y in (_0_396, _0_395) in
        match uu____3181 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              (let _0_401 =
                 FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                   md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
               let _0_400 =
                 let _0_399 = FStar_Syntax_Syntax.as_arg res_t in
                 let _0_398 =
                   let _0_397 = FStar_Syntax_Syntax.as_arg yexp in [_0_397] in
                 _0_399 :: _0_398 in
               FStar_Syntax_Syntax.mk_Tm_app _0_401 _0_400) None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              (let _0_409 =
                 FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                   md_pure md_pure.FStar_Syntax_Syntax.assume_p in
               let _0_408 =
                 let _0_407 = FStar_Syntax_Syntax.as_arg res_t in
                 let _0_406 =
                   let _0_405 =
                     let _0_402 =
                       FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                     FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_402 in
                   let _0_404 =
                     let _0_403 =
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                     [_0_403] in
                   _0_405 :: _0_404 in
                 _0_407 :: _0_406 in
               FStar_Syntax_Syntax.mk_Tm_app _0_409 _0_408) None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              (let _0_419 =
                 FStar_TypeChecker_Env.inst_effect_fun_with
                   [u_res_t; u_res_t] env md_pure
                   md_pure.FStar_Syntax_Syntax.close_wp in
               let _0_418 =
                 let _0_417 = FStar_Syntax_Syntax.as_arg res_t in
                 let _0_416 =
                   let _0_415 = FStar_Syntax_Syntax.as_arg res_t in
                   let _0_414 =
                     let _0_413 =
                       let _0_412 =
                         let _0_411 =
                           let _0_410 = FStar_Syntax_Syntax.mk_binder y in
                           [_0_410] in
                         FStar_Syntax_Util.abs _0_411 x_eq_y_yret
                           (Some
                              (FStar_Util.Inr
                                 (FStar_Syntax_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL]))) in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_412 in
                     [_0_413] in
                   _0_415 :: _0_414 in
                 _0_417 :: _0_416 in
               FStar_Syntax_Syntax.mk_Tm_app _0_419 _0_418) None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              (mk_comp md_pure) u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let _0_420 = FStar_TypeChecker_Env.get_range env in
              bind _0_420 env None (FStar_Syntax_Util.lcomp_of_comp comp)
                ((Some x), (FStar_Syntax_Util.lcomp_of_comp lc2)) in
            lc.FStar_Syntax_Syntax.comp ()
let ite:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.formula ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun guard  ->
      fun lcomp_then  ->
        fun lcomp_else  ->
          let joined_eff = join_lcomp env lcomp_then lcomp_else in
          let comp uu____3238 =
            let uu____3239 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3239
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3242 =
                 let _0_422 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let _0_421 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env _0_422 _0_421 in
               match uu____3242 with
               | ((md,uu____3256,uu____3257),(u_res_t,res_t,wp_then),
                  (uu____3261,uu____3262,wp_else)) ->
                   let ifthenelse md res_t g wp_t wp_e =
                     let _0_432 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     (let _0_431 =
                        FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                          env md md.FStar_Syntax_Syntax.if_then_else in
                      let _0_430 =
                        let _0_429 = FStar_Syntax_Syntax.as_arg res_t in
                        let _0_428 =
                          let _0_427 = FStar_Syntax_Syntax.as_arg g in
                          let _0_426 =
                            let _0_425 = FStar_Syntax_Syntax.as_arg wp_t in
                            let _0_424 =
                              let _0_423 = FStar_Syntax_Syntax.as_arg wp_e in
                              [_0_423] in
                            _0_425 :: _0_424 in
                          _0_427 :: _0_426 in
                        _0_429 :: _0_428 in
                      FStar_Syntax_Syntax.mk_Tm_app _0_431 _0_430) None
                       _0_432 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3298 =
                     let _0_433 = FStar_Options.split_cases () in
                     _0_433 > (Prims.parse_int "0") in
                   if uu____3298
                   then
                     let comp = (mk_comp md) u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp =
                        (let _0_438 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                         let _0_437 =
                           let _0_436 = FStar_Syntax_Syntax.as_arg res_t in
                           let _0_435 =
                             let _0_434 = FStar_Syntax_Syntax.as_arg wp in
                             [_0_434] in
                           _0_436 :: _0_435 in
                         FStar_Syntax_Syntax.mk_Tm_app _0_438 _0_437) None
                          wp.FStar_Syntax_Syntax.pos in
                      (mk_comp md) u_res_t res_t wp [])) in
          let _0_439 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = _0_439;
            FStar_Syntax_Syntax.res_typ =
              (lcomp_then.FStar_Syntax_Syntax.res_typ);
            FStar_Syntax_Syntax.cflags = [];
            FStar_Syntax_Syntax.comp = comp
          }
let fvar_const:
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun lid  ->
      let _0_441 =
        let _0_440 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid _0_440 in
      FStar_Syntax_Syntax.fvar _0_441 FStar_Syntax_Syntax.Delta_constant None
let bind_cases:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.formula* FStar_Syntax_Syntax.lcomp) Prims.list ->
        FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____3333  ->
                 match uu____3333 with
                 | (uu____3336,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3341 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3343 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3343
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t g wp_t wp_e =
               let _0_451 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               (let _0_450 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env md
                    md.FStar_Syntax_Syntax.if_then_else in
                let _0_449 =
                  let _0_448 = FStar_Syntax_Syntax.as_arg res_t in
                  let _0_447 =
                    let _0_446 = FStar_Syntax_Syntax.as_arg g in
                    let _0_445 =
                      let _0_444 = FStar_Syntax_Syntax.as_arg wp_t in
                      let _0_443 =
                        let _0_442 = FStar_Syntax_Syntax.as_arg wp_e in
                        [_0_442] in
                      _0_444 :: _0_443 in
                    _0_446 :: _0_445 in
                  _0_448 :: _0_447 in
                FStar_Syntax_Syntax.mk_Tm_app _0_450 _0_449) None _0_451 in
             let default_case =
               let post_k =
                 let _0_454 =
                   let _0_452 = FStar_Syntax_Syntax.null_binder res_t in
                   [_0_452] in
                 let _0_453 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow _0_454 _0_453 in
               let kwp =
                 let _0_457 =
                   let _0_455 = FStar_Syntax_Syntax.null_binder post_k in
                   [_0_455] in
                 let _0_456 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow _0_457 _0_456 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let _0_463 =
                   let _0_458 = FStar_Syntax_Syntax.mk_binder post in
                   [_0_458] in
                 let _0_462 =
                   let _0_461 =
                     let _0_459 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check _0_459 in
                   let _0_460 = fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left _0_461 _0_460 in
                 FStar_Syntax_Util.abs _0_463 _0_462
                   (Some
                      (FStar_Util.Inr
                         (FStar_Syntax_Const.effect_Tot_lid,
                           [FStar_Syntax_Syntax.TOTAL]))) in
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   FStar_Syntax_Const.effect_PURE_lid in
               (mk_comp md) u_res_t res_t wp [] in
             let comp =
               FStar_List.fold_right
                 (fun uu____3389  ->
                    fun celse  ->
                      match uu____3389 with
                      | (g,cthen) ->
                          let uu____3395 =
                            let _0_464 = cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env _0_464 celse in
                          (match uu____3395 with
                           | ((md,uu____3409,uu____3410),(uu____3411,uu____3412,wp_then),
                              (uu____3414,uu____3415,wp_else)) ->
                               let _0_465 =
                                 ifthenelse md res_t g wp_then wp_else in
                               (mk_comp md) u_res_t res_t _0_465 [])) lcases
                 default_case in
             let uu____3426 =
               let _0_466 = FStar_Options.split_cases () in
               _0_466 > (Prims.parse_int "0") in
             if uu____3426
             then add_equality_to_post_condition env comp res_t
             else
               (let comp =
                  FStar_TypeChecker_Normalize.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp.FStar_Syntax_Syntax.effect_name in
                let uu____3430 = destruct_comp comp in
                match uu____3430 with
                | (uu____3434,uu____3435,wp) ->
                    let wp =
                      (let _0_471 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.ite_wp in
                       let _0_470 =
                         let _0_469 = FStar_Syntax_Syntax.as_arg res_t in
                         let _0_468 =
                           let _0_467 = FStar_Syntax_Syntax.as_arg wp in
                           [_0_467] in
                         _0_469 :: _0_468 in
                       FStar_Syntax_Syntax.mk_Tm_app _0_471 _0_470) None
                        wp.FStar_Syntax_Syntax.pos in
                    (mk_comp md) u_res_t res_t wp [])) in
        {
          FStar_Syntax_Syntax.eff_name = eff;
          FStar_Syntax_Syntax.res_typ = res_t;
          FStar_Syntax_Syntax.cflags = [];
          FStar_Syntax_Syntax.comp = bind_cases
        }
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        let close uu____3460 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3464 = FStar_Syntax_Util.is_ml_comp c in
          if uu____3464
          then c
          else
            (let uu____3468 =
               env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
             if uu____3468
             then c
             else
               (let close_wp u_res md res_t bvs wp0 =
                  FStar_List.fold_right
                    (fun x  ->
                       fun wp  ->
                         let bs =
                           let _0_472 = FStar_Syntax_Syntax.mk_binder x in
                           [_0_472] in
                         let us =
                           let _0_474 =
                             let _0_473 =
                               env.FStar_TypeChecker_Env.universe_of env
                                 x.FStar_Syntax_Syntax.sort in
                             [_0_473] in
                           u_res :: _0_474 in
                         let wp =
                           FStar_Syntax_Util.abs bs wp
                             (Some
                                (FStar_Util.Inr
                                   (FStar_Syntax_Const.effect_Tot_lid,
                                     [FStar_Syntax_Syntax.TOTAL]))) in
                         (let _0_481 =
                            FStar_TypeChecker_Env.inst_effect_fun_with us env
                              md md.FStar_Syntax_Syntax.close_wp in
                          let _0_480 =
                            let _0_479 = FStar_Syntax_Syntax.as_arg res_t in
                            let _0_478 =
                              let _0_477 =
                                FStar_Syntax_Syntax.as_arg
                                  x.FStar_Syntax_Syntax.sort in
                              let _0_476 =
                                let _0_475 = FStar_Syntax_Syntax.as_arg wp in
                                [_0_475] in
                              _0_477 :: _0_476 in
                            _0_479 :: _0_478 in
                          FStar_Syntax_Syntax.mk_Tm_app _0_481 _0_480) None
                           wp0.FStar_Syntax_Syntax.pos) bvs wp0 in
                let c =
                  FStar_TypeChecker_Normalize.unfold_effect_abbrev env c in
                let uu____3517 = destruct_comp c in
                match uu____3517 with
                | (u_res_t,res_t,wp) ->
                    let md =
                      FStar_TypeChecker_Env.get_effect_decl env
                        c.FStar_Syntax_Syntax.effect_name in
                    let wp = close_wp u_res_t md res_t bvs wp in
                    (mk_comp md) u_res_t c.FStar_Syntax_Syntax.result_typ wp
                      c.FStar_Syntax_Syntax.flags)) in
        let uu___128_3528 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___128_3528.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___128_3528.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___128_3528.FStar_Syntax_Syntax.cflags);
          FStar_Syntax_Syntax.comp = close
        }
let maybe_assume_result_eq_pure_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let refine uu____3543 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3547 =
            (Prims.op_Negation
               (is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))
              || env.FStar_TypeChecker_Env.lax in
          if uu____3547
          then c
          else
            (let uu____3551 = FStar_Syntax_Util.is_partial_return c in
             if uu____3551
             then c
             else
               (let uu____3555 =
                  (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
                    (Prims.op_Negation
                       (FStar_TypeChecker_Env.lid_exists env
                          FStar_Syntax_Const.effect_GTot_lid)) in
                if uu____3555
                then
                  failwith
                    (let _0_483 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                     let _0_482 = FStar_Syntax_Print.term_to_string e in
                     FStar_Util.format2 "%s: %s\n" _0_483 _0_482)
                else
                  (let c =
                     FStar_TypeChecker_Normalize.unfold_effect_abbrev env c in
                   let t = c.FStar_Syntax_Syntax.result_typ in
                   let c = FStar_Syntax_Syntax.mk_Comp c in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (Some (t.FStar_Syntax_Syntax.pos)) t in
                   let xexp = FStar_Syntax_Syntax.bv_to_name x in
                   let ret =
                     let _0_485 =
                       let _0_484 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags _0_484
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       _0_485 in
                   let eq =
                     let _0_486 = env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 _0_486 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret
                       (FStar_TypeChecker_Common.NonTrivial eq) in
                   let c =
                     let _0_487 =
                       (bind e.FStar_Syntax_Syntax.pos env None
                          (FStar_Syntax_Util.lcomp_of_comp c)
                          ((Some x), eq_ret)).FStar_Syntax_Syntax.comp () in
                     FStar_Syntax_Util.comp_set_flags _0_487
                       (FStar_Syntax_Syntax.PARTIAL_RETURN ::
                       (FStar_Syntax_Util.comp_flags c)) in
                   c))) in
        let flags =
          let uu____3579 =
            ((Prims.op_Negation
                (FStar_Syntax_Util.is_function_typ
                   lc.FStar_Syntax_Syntax.res_typ))
               && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (Prims.op_Negation
                 (FStar_Syntax_Util.is_lcomp_partial_return lc)) in
          if uu____3579
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let uu___129_3582 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___129_3582.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___129_3582.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = refine
        }
let check_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp*
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____3601 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____3601 with
          | None  ->
              Prims.raise
                (FStar_Errors.Error
                   (let _0_489 =
                      FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                        env e c c' in
                    let _0_488 = FStar_TypeChecker_Env.get_range env in
                    (_0_489, _0_488)))
          | Some g -> (e, c', g)
let maybe_coerce_bool_to_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let uu____3626 =
            (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
          match uu____3626 with
          | FStar_Syntax_Syntax.Tm_type uu____3629 ->
              let uu____3630 =
                (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n in
              (match uu____3630 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.bool_lid
                   ->
                   let uu____3634 =
                     FStar_TypeChecker_Env.lookup_lid env
                       FStar_Syntax_Const.b2t_lid in
                   let b2t =
                     FStar_Syntax_Syntax.fvar
                       (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                          e.FStar_Syntax_Syntax.pos)
                       (FStar_Syntax_Syntax.Delta_defined_at_level
                          (Prims.parse_int "1")) None in
                   let lc =
                     let _0_492 =
                       let _0_491 =
                         let _0_490 =
                           FStar_Syntax_Syntax.mk_Total
                             FStar_Syntax_Util.ktype0 in
                         FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                           _0_490 in
                       (None, _0_491) in
                     bind e.FStar_Syntax_Syntax.pos env (Some e) lc _0_492 in
                   let e =
                     (let _0_494 =
                        let _0_493 = FStar_Syntax_Syntax.as_arg e in [_0_493] in
                      FStar_Syntax_Syntax.mk_Tm_app b2t _0_494)
                       (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                       e.FStar_Syntax_Syntax.pos in
                   (e, lc)
               | uu____3651 -> (e, lc))
          | uu____3652 -> (e, lc)
let weaken_result_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let gopt =
            if env.FStar_TypeChecker_Env.use_eq
            then
              let _0_495 =
                FStar_TypeChecker_Rel.try_teq env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (_0_495, false)
            else
              (let _0_496 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (_0_496, true)) in
          match gopt with
          | (None ,uu____3684) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___130_3687 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___130_3687.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___130_3687.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___130_3687.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard) ->
              let uu____3691 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____3691 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc =
                     let uu___131_3696 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___131_3696.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___131_3696.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___131_3696.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g =
                     let uu___132_3699 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___132_3699.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___132_3699.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___132_3699.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____3705 =
                     let uu____3706 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____3706
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____3711 =
                          (FStar_Syntax_Subst.compress f).FStar_Syntax_Syntax.n in
                        match uu____3711 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____3714,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____3716;
                                          FStar_Syntax_Syntax.pos =
                                            uu____3717;
                                          FStar_Syntax_Syntax.vars =
                                            uu____3718;_},uu____3719)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc =
                              let uu___133_3743 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___133_3743.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___133_3743.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___133_3743.FStar_Syntax_Syntax.comp)
                              } in
                            lc.FStar_Syntax_Syntax.comp ()
                        | uu____3744 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____3749 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____3749
                              then
                                let _0_500 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let _0_499 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let _0_498 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let _0_497 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  _0_500 _0_499 _0_498 _0_497
                              else ());
                             (let ct =
                                FStar_TypeChecker_Normalize.unfold_effect_abbrev
                                  env c in
                              let uu____3752 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____3752 with
                              | (a,kwp) ->
                                  let k =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (a, t)] kwp in
                                  let md =
                                    FStar_TypeChecker_Env.get_effect_decl env
                                      ct.FStar_Syntax_Syntax.effect_name in
                                  let x =
                                    FStar_Syntax_Syntax.new_bv
                                      (Some (t.FStar_Syntax_Syntax.pos)) t in
                                  let xexp = FStar_Syntax_Syntax.bv_to_name x in
                                  let uu____3763 = destruct_comp ct in
                                  (match uu____3763 with
                                   | (u_t,uu____3770,uu____3771) ->
                                       let wp =
                                         (let _0_505 =
                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                              [u_t] env md
                                              md.FStar_Syntax_Syntax.ret_wp in
                                          let _0_504 =
                                            let _0_503 =
                                              FStar_Syntax_Syntax.as_arg t in
                                            let _0_502 =
                                              let _0_501 =
                                                FStar_Syntax_Syntax.as_arg
                                                  xexp in
                                              [_0_501] in
                                            _0_503 :: _0_502 in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            _0_505 _0_504)
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let _0_506 =
                                           (mk_comp md) u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           _0_506 in
                                       let guard =
                                         if apply_guard
                                         then
                                           (let _0_508 =
                                              let _0_507 =
                                                FStar_Syntax_Syntax.as_arg
                                                  xexp in
                                              [_0_507] in
                                            FStar_Syntax_Syntax.mk_Tm_app f
                                              _0_508)
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f.FStar_Syntax_Syntax.pos
                                         else f in
                                       let uu____3792 =
                                         let _0_512 =
                                           FStar_All.pipe_left
                                             (fun _0_509  -> Some _0_509)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let _0_511 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let _0_510 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition _0_512
                                           _0_511 e cret _0_510 in
                                       (match uu____3792 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x =
                                              let uu___134_3807 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___134_3807.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___134_3807.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c =
                                              let _0_514 =
                                                let _0_513 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  _0_513 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) _0_514
                                                ((Some x), eq_ret) in
                                            let c =
                                              c.FStar_Syntax_Syntax.comp () in
                                            ((let uu____3816 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____3816
                                              then
                                                let _0_515 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  _0_515
                                              else ());
                                             c)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___93_3822  ->
                             match uu___93_3822 with
                             | FStar_Syntax_Syntax.RETURN 
                               |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____3824 -> [])) in
                   let lc =
                     let uu___135_3826 = lc in
                     let _0_516 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = _0_516;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g =
                     let uu___136_3828 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___136_3828.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___136_3828.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___136_3828.FStar_TypeChecker_Env.implicits)
                     } in
                   (e, lc, g))
let pure_or_ghost_pre_and_post:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ Prims.option* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv None res_t in
        let _0_519 =
          (let _0_518 =
             let _0_517 =
               FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name x) in
             [_0_517] in
           FStar_Syntax_Syntax.mk_Tm_app ens _0_518) None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x _0_519 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____3858 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____3858
      then (None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal _|FStar_Syntax_Syntax.Total _ ->
             failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____3882)::(ens,uu____3884)::uu____3885 ->
                    let _0_522 = Some (norm req) in
                    let _0_521 =
                      let _0_520 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm _0_520 in
                    (_0_522, _0_521)
                | uu____3908 ->
                    Prims.raise
                      (FStar_Errors.Error
                         (let _0_524 =
                            let _0_523 =
                              FStar_Syntax_Print.comp_to_string comp in
                            FStar_Util.format1
                              "Effect constructor is not fully applied; got %s"
                              _0_523 in
                          (_0_524, (comp.FStar_Syntax_Syntax.pos)))))
             else
               (let ct =
                  FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp in
                match ct.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____3923)::uu____3924 ->
                    let uu____3938 =
                      FStar_TypeChecker_Env.lookup_lid env
                        FStar_Syntax_Const.as_requires in
                    (match uu____3938 with
                     | (us_r,uu____3945) ->
                         let uu____3946 =
                           FStar_TypeChecker_Env.lookup_lid env
                             FStar_Syntax_Const.as_ensures in
                         (match uu____3946 with
                          | (us_e,uu____3953) ->
                              let r =
                                (ct.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let _0_525 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst _0_525 us_r in
                              let as_ens =
                                let _0_526 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst _0_526 us_e in
                              let req =
                                (let _0_529 =
                                   let _0_528 =
                                     let _0_527 =
                                       FStar_Syntax_Syntax.as_arg wp in
                                     [_0_527] in
                                   ((ct.FStar_Syntax_Syntax.result_typ),
                                     (Some FStar_Syntax_Syntax.imp_tag)) ::
                                     _0_528 in
                                 FStar_Syntax_Syntax.mk_Tm_app as_req _0_529)
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                (let _0_532 =
                                   let _0_531 =
                                     let _0_530 =
                                       FStar_Syntax_Syntax.as_arg wp in
                                     [_0_530] in
                                   ((ct.FStar_Syntax_Syntax.result_typ),
                                     (Some FStar_Syntax_Syntax.imp_tag)) ::
                                     _0_531 in
                                 FStar_Syntax_Syntax.mk_Tm_app as_ens _0_532)
                                  None
                                  (ct.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let _0_534 = Some (norm req) in
                              let _0_533 =
                                norm
                                  (mk_post_type
                                     ct.FStar_Syntax_Syntax.result_typ ens) in
                              (_0_534, _0_533)))
                | uu____3988 -> failwith "Impossible"))
let maybe_instantiate:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.typ*
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Rel.trivial_guard)
        else
          (let number_of_implicits t =
             let uu____4018 = FStar_Syntax_Util.arrow_formals t in
             match uu____4018 with
             | (formals,uu____4027) ->
                 let n_implicits =
                   let uu____4039 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4076  ->
                             match uu____4076 with
                             | (uu____4080,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality)))) in
                   match uu____4039 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t =
             let uu____4152 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4152 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t in
                 if n_available < n_expected
                 then
                   Prims.raise
                     (FStar_Errors.Error
                        (let _0_539 =
                           let _0_537 = FStar_Util.string_of_int n_expected in
                           let _0_536 = FStar_Syntax_Print.term_to_string e in
                           let _0_535 = FStar_Util.string_of_int n_available in
                           FStar_Util.format3
                             "Expected a term with %s implicit arguments, but %s has only %s"
                             _0_537 _0_536 _0_535 in
                         let _0_538 = FStar_TypeChecker_Env.get_range env in
                         (_0_539, _0_538)))
                 else Some (n_available - n_expected) in
           let decr_inst uu___94_4184 =
             match uu___94_4184 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4203 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____4203 with
                | (bs,c) ->
                    let rec aux subst inst_n bs =
                      match (inst_n, bs) with
                      | (Some _0_540,uu____4264) when
                          _0_540 = (Prims.parse_int "0") ->
                          ([], bs, subst,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____4286,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort in
                          let uu____4305 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t in
                          (match uu____4305 with
                           | (v,uu____4326,g) ->
                               let subst = (FStar_Syntax_Syntax.NT (x, v)) ::
                                 subst in
                               let uu____4336 =
                                 aux subst (decr_inst inst_n) rest in
                               (match uu____4336 with
                                | (args,bs,subst,g') ->
                                    let _0_541 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs, subst, _0_541)))
                      | (uu____4398,bs) ->
                          ([], bs, subst,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____4422 =
                      let _0_542 = inst_n_binders t in aux [] _0_542 bs in
                    (match uu____4422 with
                     | (args,bs,subst,guard) ->
                         (match (args, bs) with
                          | ([],uu____4472) -> (e, torig, guard)
                          | (uu____4488,[]) when
                              Prims.op_Negation
                                (FStar_Syntax_Util.is_total_comp c)
                              ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____4504 ->
                              let t =
                                match bs with
                                | [] -> FStar_Syntax_Util.comp_result c
                                | uu____4523 -> FStar_Syntax_Util.arrow bs c in
                              let t = FStar_Syntax_Subst.subst subst t in
                              let e =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e, t, guard))))
           | uu____4538 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs univs =
  let _0_545 =
    let _0_544 = FStar_Util.set_elements univs in
    FStar_All.pipe_right _0_544
      (FStar_List.map
         (fun u  ->
            let _0_543 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right _0_543 FStar_Util.string_of_int)) in
  FStar_All.pipe_right _0_545 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____4568 = FStar_Util.set_is_empty x in
      if uu____4568
      then []
      else
        (let s =
           let _0_547 =
             let _0_546 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x _0_546 in
           FStar_All.pipe_right _0_547 FStar_Util.set_elements in
         (let uu____4576 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____4576
          then
            let _0_548 =
              string_of_univs (FStar_TypeChecker_Env.univ_vars env) in
            FStar_Util.print1 "univ_vars in env: %s\n" _0_548
          else ());
         (let r = Some (FStar_TypeChecker_Env.get_range env) in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____4592 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____4592
                     then
                       let _0_552 =
                         let _0_549 = FStar_Unionfind.uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int _0_549 in
                       let _0_551 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let _0_550 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n" _0_552
                         _0_551 _0_550
                     else ());
                    FStar_Unionfind.change u
                      (Some (FStar_Syntax_Syntax.U_name u_name));
                    u_name)) in
          u_names))
let gather_free_univnames:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env in
      let tm_univnames = FStar_Syntax_Free.univnames t in
      let univnames =
        let _0_553 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right _0_553 FStar_Util.fifo_set_elements in
      univnames
let maybe_set_tk ts uu___95_4635 =
  match uu___95_4635 with
  | None  -> ts
  | Some t ->
      let t = FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange in
      let t = FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t in
      (FStar_ST.write (Prims.snd ts).FStar_Syntax_Syntax.tk
         (Some (t.FStar_Syntax_Syntax.n));
       ts)
let check_universe_generalization:
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____4676) -> generalized_univ_names
        | (uu____4680,[]) -> explicit_univ_names
        | uu____4684 ->
            Prims.raise
              (FStar_Errors.Error
                 (let _0_555 =
                    let _0_554 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "Generalized universe in a term containing explicit universe annotation : "
                      _0_554 in
                  (_0_555, (t.FStar_Syntax_Syntax.pos))))
let generalize_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta] env t0 in
      let univnames = gather_free_univnames env t in
      let univs = FStar_Syntax_Free.univs t in
      (let uu____4702 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____4702
       then
         let _0_556 = string_of_univs univs in
         FStar_Util.print1 "univs to gen : %s\n" _0_556
       else ());
      (let gen = gen_univs env univs in
       (let uu____4708 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____4708
        then
          let _0_557 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" _0_557
        else ());
       (let univs = check_universe_generalization univnames gen t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs t in
        let _0_558 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs, ts) _0_558))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list Prims.option
  =
  fun env  ->
    fun ecs  ->
      let uu____4741 =
        let _0_559 =
          FStar_Util.for_all
            (fun uu____4746  ->
               match uu____4746 with
               | (uu____4751,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation _0_559 in
      if uu____4741
      then None
      else
        (let norm c =
           (let uu____4774 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____4774
            then
              let _0_560 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                _0_560
            else ());
           (let c =
              let uu____4777 = FStar_TypeChecker_Env.should_verify env in
              if uu____4777
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____4780 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____4780
             then
               let _0_561 = FStar_Syntax_Print.comp_to_string c in
               FStar_Util.print1 "Normalized to:\n\t %s\n" _0_561
             else ());
            c) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let _0_562 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right _0_562 FStar_Util.set_elements in
         let uu____4848 =
           let _0_563 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____4937  ->
                     match uu____4937 with
                     | (e,c) ->
                         let t =
                           FStar_All.pipe_right
                             (FStar_Syntax_Util.comp_result c)
                             FStar_Syntax_Subst.compress in
                         let c = norm c in
                         let t = FStar_Syntax_Util.comp_result c in
                         let univs = FStar_Syntax_Free.univs t in
                         let uvt = FStar_Syntax_Free.uvars t in
                         let uvs = gen_uvars uvt in (univs, (uvs, e, c)))) in
           FStar_All.pipe_right _0_563 FStar_List.unzip in
         match uu____4848 with
         | (univs,uvars) ->
             let univs =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs in
             let gen_univs = gen_univs env univs in
             ((let uu____5066 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____5066
               then
                 FStar_All.pipe_right gen_univs
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.print1 "Generalizing uvar %s\n"
                           x.FStar_Ident.idText))
               else ());
              (let ecs =
                 FStar_All.pipe_right uvars
                   (FStar_List.map
                      (fun uu____5108  ->
                         match uu____5108 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____5165  ->
                                       match uu____5165 with
                                       | (u,k) ->
                                           let uu____5185 =
                                             FStar_Unionfind.find u in
                                           (match uu____5185 with
                                            | FStar_Syntax_Syntax.Fixed
                                              {
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_name
                                                  a;
                                                FStar_Syntax_Syntax.tk = _;
                                                FStar_Syntax_Syntax.pos = _;
                                                FStar_Syntax_Syntax.vars = _;_}
                                              |FStar_Syntax_Syntax.Fixed
                                              {
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_abs
                                                  (_,{
                                                       FStar_Syntax_Syntax.n
                                                         =
                                                         FStar_Syntax_Syntax.Tm_name
                                                         a;
                                                       FStar_Syntax_Syntax.tk
                                                         = _;
                                                       FStar_Syntax_Syntax.pos
                                                         = _;
                                                       FStar_Syntax_Syntax.vars
                                                         = _;_},_);
                                                FStar_Syntax_Syntax.tk = _;
                                                FStar_Syntax_Syntax.pos = _;
                                                FStar_Syntax_Syntax.vars = _;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Syntax_Syntax.Fixed
                                                uu____5223 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____5231 ->
                                                let k =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____5236 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k in
                                                (match uu____5236 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let _0_566 =
                                                         let _0_565 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_564  ->
                                                              Some _0_564)
                                                           _0_565 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         _0_566 kres in
                                                     let t =
                                                       let _0_568 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let _0_567 =
                                                         Some
                                                           (FStar_Util.Inl
                                                              (FStar_Syntax_Util.lcomp_of_comp
                                                                 (FStar_Syntax_Syntax.mk_Total
                                                                    kres))) in
                                                       FStar_Syntax_Util.abs
                                                         bs _0_568 _0_567 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____5274 =
                               match (tvars, gen_univs) with
                               | ([],[]) -> (e, c)
                               | ([],uu____5292) ->
                                   let c =
                                     FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm]
                                       env c in
                                   let e =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm]
                                       env e in
                                   (e, c)
                               | uu____5304 ->
                                   let uu____5312 = (e, c) in
                                   (match uu____5312 with
                                    | (e0,c0) ->
                                        let c =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm]
                                            env c in
                                        let e =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Zeta;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Iota;
                                            FStar_TypeChecker_Normalize.NoFullNorm]
                                            env e in
                                        let t =
                                          let uu____5324 =
                                            (FStar_Syntax_Subst.compress
                                               (FStar_Syntax_Util.comp_result
                                                  c)).FStar_Syntax_Syntax.n in
                                          match uu____5324 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____5339 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____5339 with
                                               | (bs,cod) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs) cod)
                                          | uu____5349 ->
                                              FStar_Syntax_Util.arrow tvars c in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e
                                            (Some
                                               (FStar_Util.Inl
                                                  (FStar_Syntax_Util.lcomp_of_comp
                                                     c))) in
                                        let _0_569 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', _0_569)) in
                             (match uu____5274 with
                              | (e,c) -> (gen_univs, e, c)))) in
               Some ecs)))
let generalize:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.lbname* FStar_Syntax_Syntax.term*
      FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.lbname* FStar_Syntax_Syntax.univ_name Prims.list*
        FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list
  =
  fun env  ->
    fun lecs  ->
      (let uu____5396 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____5396
       then
         let _0_571 =
           let _0_570 =
             FStar_List.map
               (fun uu____5401  ->
                  match uu____5401 with
                  | (lb,uu____5406,uu____5407) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right _0_570 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" _0_571
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____5416  ->
              match uu____5416 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____5431 =
           let _0_572 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____5450  ->
                     match uu____5450 with | (uu____5456,e,c) -> (e, c))) in
           gen env _0_572 in
         match uu____5431 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____5488  ->
                     match uu____5488 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____5532  ->
                  fun uu____5533  ->
                    match (uu____5532, uu____5533) with
                    | ((l,uu____5566,uu____5567),(us,e,c)) ->
                        ((let uu____5593 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____5593
                          then
                            let _0_576 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let _0_575 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let _0_574 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let _0_573 = FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n" _0_576
                              _0_575 _0_574 _0_573
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames  ->
            fun uu____5612  ->
              match uu____5612 with
              | (l,generalized_univs,t,c) ->
                  let _0_577 =
                    check_universe_generalization univnames generalized_univs
                      t in
                  (l, _0_577, t, c)) univnames_lecs generalized_lecs)
let check_and_ascribe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term* FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let env =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
          let check env t1 t2 =
            if env.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq env t1 t2
            else
              (let uu____5661 = FStar_TypeChecker_Rel.try_subtype env t1 t2 in
               match uu____5661 with
               | None  -> None
               | Some f ->
                   let _0_579 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left (fun _0_578  -> Some _0_578) _0_579) in
          let is_var e =
            let uu____5670 =
              (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n in
            match uu____5670 with
            | FStar_Syntax_Syntax.Tm_name uu____5671 -> true
            | uu____5672 -> false in
          let decorate e t =
            let e = FStar_Syntax_Subst.compress e in
            match e.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_name
                      (let uu___137_5694 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___137_5694.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___137_5694.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t2
                       }))) (Some (t2.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos
            | uu____5695 ->
                let uu___138_5696 = e in
                let _0_580 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_5696.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = _0_580;
                  FStar_Syntax_Syntax.pos =
                    (uu___138_5696.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___138_5696.FStar_Syntax_Syntax.vars)
                } in
          let env =
            let uu___139_5703 = env in
            let _0_581 =
              env.FStar_TypeChecker_Env.use_eq ||
                (env.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___139_5703.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___139_5703.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___139_5703.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___139_5703.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___139_5703.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___139_5703.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___139_5703.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___139_5703.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___139_5703.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___139_5703.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___139_5703.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___139_5703.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___139_5703.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___139_5703.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___139_5703.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = _0_581;
              FStar_TypeChecker_Env.is_iface =
                (uu___139_5703.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___139_5703.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___139_5703.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___139_5703.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___139_5703.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___139_5703.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___139_5703.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___139_5703.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____5704 = check env t1 t2 in
          match uu____5704 with
          | None  ->
              Prims.raise
                (FStar_Errors.Error
                   (let _0_583 =
                      FStar_TypeChecker_Err.expected_expression_of_type env
                        t2 e t1 in
                    let _0_582 = FStar_TypeChecker_Env.get_range env in
                    (_0_583, _0_582)))
          | Some g ->
              ((let uu____5712 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel") in
                if uu____5712
                then
                  let _0_584 = FStar_TypeChecker_Rel.guard_to_string env g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") _0_584
                else ());
               (let _0_585 = decorate e t2 in (_0_585, g)))
let check_top_level:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool* FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        let discharge g =
          FStar_TypeChecker_Rel.force_trivial_guard env g;
          FStar_Syntax_Util.is_pure_lcomp lc in
        let g = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
        let uu____5735 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____5735
        then
          let _0_587 = discharge g in
          let _0_586 = lc.FStar_Syntax_Syntax.comp () in (_0_587, _0_586)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c =
             let _0_590 =
               let _0_589 =
                 let _0_588 =
                   FStar_TypeChecker_Normalize.unfold_effect_abbrev env c in
                 FStar_All.pipe_right _0_588 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right _0_589
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right _0_590
               (FStar_TypeChecker_Normalize.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c.FStar_Syntax_Syntax.effect_name in
           let uu____5748 = destruct_comp c in
           match uu____5748 with
           | (u_t,t,wp) ->
               let vc =
                 let _0_596 = FStar_TypeChecker_Env.get_range env in
                 (let _0_595 =
                    FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                      md.FStar_Syntax_Syntax.trivial in
                  let _0_594 =
                    let _0_593 = FStar_Syntax_Syntax.as_arg t in
                    let _0_592 =
                      let _0_591 = FStar_Syntax_Syntax.as_arg wp in [_0_591] in
                    _0_593 :: _0_592 in
                  FStar_Syntax_Syntax.mk_Tm_app _0_595 _0_594)
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   _0_596 in
               ((let uu____5765 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____5765
                 then
                   let _0_597 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" _0_597
                 else ());
                (let g =
                   let _0_598 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g _0_598 in
                 let _0_600 = discharge g in
                 let _0_599 = FStar_Syntax_Syntax.mk_Comp c in
                 (_0_600, _0_599))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___96_5791 =
        match uu___96_5791 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____5797)::[] -> f fst
        | uu____5810 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let _0_602 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right _0_602
          (fun _0_601  -> FStar_TypeChecker_Common.NonTrivial _0_601) in
      let op_or_e e =
        let _0_604 = FStar_Syntax_Util.mk_neg (FStar_Syntax_Util.b2t e) in
        FStar_All.pipe_right _0_604
          (fun _0_603  -> FStar_TypeChecker_Common.NonTrivial _0_603) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_605  -> FStar_TypeChecker_Common.NonTrivial _0_605) in
      let op_or_t t =
        let _0_607 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right _0_607
          (fun _0_606  -> FStar_TypeChecker_Common.NonTrivial _0_606) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_608  -> FStar_TypeChecker_Common.NonTrivial _0_608) in
      let short_op_ite uu___97_5842 =
        match uu___97_5842 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____5848)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____5863)::[] ->
            let _0_610 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right _0_610
              (fun _0_609  -> FStar_TypeChecker_Common.NonTrivial _0_609)
        | uu____5886 -> failwith "Unexpected args to ITE" in
      let table =
        let _0_624 =
          let _0_611 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, _0_611) in
        let _0_623 =
          let _0_622 =
            let _0_612 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, _0_612) in
          let _0_621 =
            let _0_620 =
              let _0_613 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, _0_613) in
            let _0_619 =
              let _0_618 =
                let _0_614 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, _0_614) in
              let _0_617 =
                let _0_616 =
                  let _0_615 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, _0_615) in
                [_0_616; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              _0_618 :: _0_617 in
            _0_620 :: _0_619 in
          _0_622 :: _0_621 in
        _0_624 :: _0_623 in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____5939 =
            FStar_Util.find_map table
              (fun uu____5945  ->
                 match uu____5945 with
                 | (x,mk) ->
                     if FStar_Ident.lid_equals x lid
                     then Some (mk seen_args)
                     else None) in
          (match uu____5939 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____5960 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____5964 = (FStar_Syntax_Util.un_uinst l).FStar_Syntax_Syntax.n in
    match uu____5964 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____5966 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs =
        match bs with
        | (hd,uu____5984)::uu____5985 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____5991 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____5995,Some (FStar_Syntax_Syntax.Implicit uu____5996))::uu____5997
          -> bs
      | uu____6006 ->
          let uu____6007 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____6007 with
           | None  -> bs
           | Some t ->
               let uu____6010 =
                 (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
               (match uu____6010 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____6012) ->
                    let uu____6023 =
                      FStar_Util.prefix_until
                        (fun uu___98_6042  ->
                           match uu___98_6042 with
                           | (uu____6046,Some (FStar_Syntax_Syntax.Implicit
                              uu____6047)) -> false
                           | uu____6049 -> true) bs' in
                    (match uu____6023 with
                     | None  -> bs
                     | Some ([],uu____6067,uu____6068) -> bs
                     | Some (imps,uu____6105,uu____6106) ->
                         let uu____6143 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____6151  ->
                                   match uu____6151 with
                                   | (x,uu____6156) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____6143
                         then
                           let r = pos bs in
                           let imps =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____6179  ->
                                     match uu____6179 with
                                     | (x,i) ->
                                         let _0_625 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (_0_625, i))) in
                           FStar_List.append imps bs
                         else bs)
                | uu____6195 -> bs))
let maybe_lift:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun c1  ->
        fun c2  ->
          fun t  ->
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1 in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2 in
            if
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
            then e
            else
              (let _0_626 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               (FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_meta
                     (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)))))
                 _0_626 e.FStar_Syntax_Syntax.pos)
let maybe_monadic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c in
          let uu____6238 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____6238
          then e
          else
            (let _0_627 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))) _0_627
               e.FStar_Syntax_Syntax.pos)
let effect_repr_aux only_reifiable env c u_c =
  let uu____6280 =
    let _0_628 =
      FStar_TypeChecker_Env.norm_eff_name env
        (FStar_Syntax_Util.comp_effect_name c) in
    FStar_TypeChecker_Env.effect_decl_opt env _0_628 in
  match uu____6280 with
  | None  -> None
  | Some ed ->
      let uu____6288 =
        only_reifiable &&
          (Prims.op_Negation
             (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable))) in
      if uu____6288
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____6301 ->
             let c = FStar_TypeChecker_Normalize.unfold_effect_abbrev env c in
             let uu____6303 =
               let _0_629 = FStar_List.hd c.FStar_Syntax_Syntax.effect_args in
               ((c.FStar_Syntax_Syntax.result_typ), _0_629) in
             (match uu____6303 with
              | (res_typ,wp) ->
                  let repr =
                    FStar_TypeChecker_Env.inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  Some
                    (let _0_632 = FStar_TypeChecker_Env.get_range env in
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app
                           (let _0_631 =
                              let _0_630 = FStar_Syntax_Syntax.as_arg res_typ in
                              [_0_630; wp] in
                            (repr, _0_631)))) None _0_632)))
let effect_repr:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax Prims.option
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c
let reify_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          Prims.raise
            (FStar_Errors.Error
               (let _0_634 =
                  FStar_Util.format1 "Effect %s cannot be reified"
                    l.FStar_Ident.str in
                let _0_633 = FStar_TypeChecker_Env.get_range env in
                (_0_634, _0_633))) in
        let uu____6388 =
          let _0_635 = c.FStar_Syntax_Syntax.comp () in
          effect_repr_aux true env _0_635 u_c in
        match uu____6388 with
        | None  -> no_reify c.FStar_Syntax_Syntax.eff_name
        | Some tm -> tm
let d: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s
let mk_toplevel_definition:
  FStar_TypeChecker_Env.env_t ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt*
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____6416 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____6416
         then
           (d (FStar_Ident.text_of_lid lident);
            (let _0_636 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) _0_636))
         else ());
        (let fv =
           let _0_637 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident _0_637 None in
         let lbname = FStar_Util.Inr fv in
         let lb =
           (false,
             [{
                FStar_Syntax_Syntax.lbname = lbname;
                FStar_Syntax_Syntax.lbunivs = [];
                FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
                FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid;
                FStar_Syntax_Syntax.lbdef = def
              }]) in
         let sig_ctx =
           FStar_Syntax_Syntax.Sig_let
             (lb, FStar_Range.dummyRange, [lident],
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen], []) in
         let _0_638 =
           (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)) None
             FStar_Range.dummyRange in
         (sig_ctx, _0_638))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___99_6450 =
        match uu___99_6450 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____6451 -> false in
      let reducibility uu___100_6455 =
        match uu___100_6455 with
        | FStar_Syntax_Syntax.Abstract 
          |FStar_Syntax_Syntax.Irreducible 
           |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
            |FStar_Syntax_Syntax.Visible_default 
             |FStar_Syntax_Syntax.Inline_for_extraction 
            -> true
        | uu____6456 -> false in
      let assumption uu___101_6460 =
        match uu___101_6460 with
        | FStar_Syntax_Syntax.Assumption |FStar_Syntax_Syntax.New  -> true
        | uu____6461 -> false in
      let reification uu___102_6465 =
        match uu___102_6465 with
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            true
        | uu____6467 -> false in
      let inferred uu___103_6471 =
        match uu___103_6471 with
        | FStar_Syntax_Syntax.Discriminator _
          |FStar_Syntax_Syntax.Projector _
           |FStar_Syntax_Syntax.RecordType _
            |FStar_Syntax_Syntax.RecordConstructor _
             |FStar_Syntax_Syntax.ExceptionConstructor 
              |FStar_Syntax_Syntax.HasMaskedEffect 
               |FStar_Syntax_Syntax.Effect 
            -> true
        | uu____6476 -> false in
      let has_eq uu___104_6480 =
        match uu___104_6480 with
        | FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq  -> true
        | uu____6481 -> false in
      let quals_combo_ok quals q =
        match q with
        | FStar_Syntax_Syntax.Assumption  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                         (inferred x))
                        || (visibility x))
                       || (assumption x))
                      ||
                      (env.FStar_TypeChecker_Env.is_iface &&
                         (x = FStar_Syntax_Syntax.Inline_for_extraction))))
        | FStar_Syntax_Syntax.New  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (assumption x)))
        | FStar_Syntax_Syntax.Inline_for_extraction  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (visibility x))
                         || (reducibility x))
                        || (reification x))
                       || (inferred x))
                      ||
                      (env.FStar_TypeChecker_Env.is_iface &&
                         (x = FStar_Syntax_Syntax.Assumption))))
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
          |FStar_Syntax_Syntax.Visible_default 
           |FStar_Syntax_Syntax.Irreducible 
            |FStar_Syntax_Syntax.Abstract 
             |FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq 
            ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (x = FStar_Syntax_Syntax.Abstract))
                         || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                        || (has_eq x))
                       || (inferred x))
                      || (visibility x)))
        | FStar_Syntax_Syntax.TotalEffect  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (reification x)))
        | FStar_Syntax_Syntax.Logic  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) ||
                        (inferred x))
                       || (visibility x))
                      || (reducibility x)))
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____6506 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____6509 =
        let _0_639 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___105_6511  ->
                  match uu___105_6511 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____6512 -> false)) in
        FStar_All.pipe_right _0_639 Prims.op_Negation in
      if uu____6509
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          Prims.raise
            (FStar_Errors.Error
               (let _0_641 =
                  let _0_640 = FStar_Syntax_Print.quals_to_string quals in
                  FStar_Util.format2
                    "The qualifier list \"[%s]\" is not permissible for this element%s"
                    _0_640 msg in
                (_0_641, r))) in
        let err msg = err' (Prims.strcat ": " msg) in
        let err' uu____6529 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____6537 =
            Prims.op_Negation
              (FStar_All.pipe_right quals
                 (FStar_List.for_all (quals_combo_ok quals))) in
          if uu____6537 then err "ill-formed combination" else ());
         (match se with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____6541),uu____6542,uu____6543,uu____6544,uu____6545)
              ->
              ((let uu____6558 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____6558
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____6561 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____6561
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____6565 ->
              let uu____6573 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_Util.for_all
                        (fun x  ->
                           (((x = FStar_Syntax_Syntax.Abstract) ||
                               (inferred x))
                              || (visibility x))
                             || (has_eq x)))) in
              if uu____6573 then err' () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____6577 ->
              let uu____6584 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____6584 then err' () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____6587 ->
              let uu____6593 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_Util.for_all
                        (fun x  ->
                           (visibility x) ||
                             (x = FStar_Syntax_Syntax.Assumption)))) in
              if uu____6593 then err' () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____6597 ->
              let uu____6600 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_Util.for_all
                        (fun x  ->
                           (((x = FStar_Syntax_Syntax.TotalEffect) ||
                               (inferred x))
                              || (visibility x))
                             || (reification x)))) in
              if uu____6600 then err' () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____6604 ->
              let uu____6607 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_Util.for_all
                        (fun x  ->
                           (((x = FStar_Syntax_Syntax.TotalEffect) ||
                               (inferred x))
                              || (visibility x))
                             || (reification x)))) in
              if uu____6607 then err' () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6611 ->
              let uu____6621 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_Util.for_all
                        (fun x  -> (inferred x) || (visibility x)))) in
              if uu____6621 then err' () else ()
          | uu____6625 -> ()))
      else ()
let mk_discriminator_and_indexed_projectors:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      Prims.bool ->
        FStar_TypeChecker_Env.env ->
          FStar_Ident.lident ->
            FStar_Ident.lident ->
              FStar_Syntax_Syntax.univ_names ->
                FStar_Syntax_Syntax.binders ->
                  FStar_Syntax_Syntax.binders ->
                    FStar_Syntax_Syntax.binders ->
                      FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun fvq  ->
      fun refine_domain  ->
        fun env  ->
          fun tc  ->
            fun lid  ->
              fun uvs  ->
                fun inductive_tps  ->
                  fun indices  ->
                    fun fields  ->
                      let p = FStar_Ident.range_of_lid lid in
                      let pos q =
                        FStar_Syntax_Syntax.withinfo q
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee" (Some p) ptyp in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs in
                      let tps = inductive_tps in
                      let arg_typ =
                        let inst_tc =
                          (FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_uinst
                                (let _0_642 =
                                   FStar_Syntax_Syntax.fv_to_tm
                                     (FStar_Syntax_Syntax.lid_as_fv tc
                                        FStar_Syntax_Syntax.Delta_constant
                                        None) in
                                 (_0_642, inst_univs)))) None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____6707  ->
                                  match uu____6707 with
                                  | (x,imp) ->
                                      let _0_643 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (_0_643, imp))) in
                        (FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p in
                      let unrefined_arg_binder =
                        FStar_Syntax_Syntax.mk_binder (projectee arg_typ) in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let x =
                             FStar_Syntax_Syntax.new_bv (Some p) arg_typ in
                           let sort =
                             let disc_fvar =
                               FStar_Syntax_Syntax.fvar
                                 (FStar_Ident.set_lid_range disc_name p)
                                 FStar_Syntax_Syntax.Delta_equational None in
                             let _0_648 =
                               FStar_Syntax_Util.b2t
                                 ((let _0_647 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let _0_646 =
                                     let _0_645 =
                                       let _0_644 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg _0_644 in
                                     [_0_645] in
                                   FStar_Syntax_Syntax.mk_Tm_app _0_647
                                     _0_646) None p) in
                             FStar_Syntax_Util.refine x _0_648 in
                           FStar_Syntax_Syntax.mk_binder
                             (let uu___140_6733 = projectee arg_typ in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___140_6733.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___140_6733.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = sort
                              })) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let _0_649 =
                          FStar_List.map
                            (fun uu____6751  ->
                               match uu____6751 with
                               | (x,uu____6758) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append _0_649 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____6779  ->
                                match uu____6779 with
                                | (x,uu____6786) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let _0_650 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid _0_650)
                               ||
                               (FStar_Options.dont_gen_projectors
                                  (FStar_TypeChecker_Env.current_module env).FStar_Ident.str) in
                           let quals =
                             let _0_653 =
                               let _0_652 =
                                 let uu____6799 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____6799
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let _0_651 =
                                 FStar_List.filter
                                   (fun uu___106_6802  ->
                                      match uu___106_6802 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____6803 -> false) iquals in
                               FStar_List.append _0_652 _0_651 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) _0_653 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               FStar_Syntax_Syntax.mk_Total
                                 (FStar_Syntax_Syntax.fv_to_tm
                                    (FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Syntax_Const.bool_lid
                                       FStar_Syntax_Syntax.Delta_constant
                                       None)) in
                             let _0_654 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               _0_654 in
                           let decl =
                             FStar_Syntax_Syntax.Sig_declare_typ
                               (discriminator_name, uvs, t, quals,
                                 (FStar_Ident.range_of_lid discriminator_name)) in
                           (let uu____6817 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____6817
                            then
                              let _0_655 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n" _0_655
                            else ());
                           if only_decl
                           then [decl]
                           else
                             (let body =
                                if Prims.op_Negation refine_domain
                                then FStar_Syntax_Const.exp_true_bool
                                else
                                  (let arg_pats =
                                     FStar_All.pipe_right all_params
                                       (FStar_List.mapi
                                          (fun j  ->
                                             fun uu____6845  ->
                                               match uu____6845 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let _0_657 =
                                                       pos
                                                         (FStar_Syntax_Syntax.Pat_dot_term
                                                            (let _0_656 =
                                                               FStar_Syntax_Syntax.gen_bv
                                                                 (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                 None
                                                                 FStar_Syntax_Syntax.tun in
                                                             (_0_656,
                                                               FStar_Syntax_Syntax.tun))) in
                                                     (_0_657, b)
                                                   else
                                                     (let _0_658 =
                                                        pos
                                                          (FStar_Syntax_Syntax.Pat_wild
                                                             (FStar_Syntax_Syntax.gen_bv
                                                                (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                None
                                                                FStar_Syntax_Syntax.tun)) in
                                                      (_0_658, b)))) in
                                   let pat_true =
                                     let _0_660 =
                                       pos
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (let _0_659 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 lid
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some fvq) in
                                             (_0_659, arg_pats))) in
                                     (_0_660, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let _0_661 =
                                       pos
                                         (FStar_Syntax_Syntax.Pat_wild
                                            (FStar_Syntax_Syntax.new_bv None
                                               FStar_Syntax_Syntax.tun)) in
                                     (_0_661, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (Prims.fst unrefined_arg_binder) in
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_match
                                         (let _0_665 =
                                            let _0_664 =
                                              FStar_Syntax_Util.branch
                                                pat_true in
                                            let _0_663 =
                                              let _0_662 =
                                                FStar_Syntax_Util.branch
                                                  pat_false in
                                              [_0_662] in
                                            _0_664 :: _0_663 in
                                          (arg_exp, _0_665)))) None p) in
                              let dd =
                                let uu____6914 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____6914
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    FStar_Syntax_Syntax.Delta_equational
                                else FStar_Syntax_Syntax.Delta_equational in
                              let imp =
                                FStar_Syntax_Util.abs binders body None in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun in
                              let lb =
                                let _0_667 =
                                  FStar_Util.Inr
                                    (FStar_Syntax_Syntax.lid_as_fv
                                       discriminator_name dd None) in
                                let _0_666 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = _0_667;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = _0_666
                                } in
                              let impl =
                                FStar_Syntax_Syntax.Sig_let
                                  (let _0_670 =
                                     let _0_669 =
                                       let _0_668 =
                                         FStar_All.pipe_right
                                           lb.FStar_Syntax_Syntax.lbname
                                           FStar_Util.right in
                                       FStar_All.pipe_right _0_668
                                         (fun fv  ->
                                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                     [_0_669] in
                                   ((false, [lb]), p, _0_670, quals, [])) in
                              (let uu____6942 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____6942
                               then
                                 let _0_671 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   _0_671
                               else ());
                              [decl; impl])) in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder) in
                      let binders =
                        FStar_List.append imp_binders [arg_binder] in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder in
                      let subst =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6962  ->
                                  match uu____6962 with
                                  | (a,uu____6966) ->
                                      let uu____6967 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____6967 with
                                       | (field_name,uu____6971) ->
                                           let field_proj_tm =
                                             let _0_672 =
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 (FStar_Syntax_Syntax.lid_as_fv
                                                    field_name
                                                    FStar_Syntax_Syntax.Delta_equational
                                                    None) in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               _0_672 inst_univs in
                                           let proj =
                                             (FStar_Syntax_Syntax.mk_Tm_app
                                                field_proj_tm [arg]) None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let _0_693 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____6997  ->
                                    match uu____6997 with
                                    | (x,uu____7002) ->
                                        let p =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____7004 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____7004 with
                                         | (field_name,uu____7009) ->
                                             let t =
                                               let _0_674 =
                                                 let _0_673 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     (FStar_Syntax_Subst.subst
                                                        subst
                                                        x.FStar_Syntax_Syntax.sort) in
                                                 FStar_Syntax_Util.arrow
                                                   binders _0_673 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) _0_674 in
                                             let only_decl =
                                               ((let _0_675 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   _0_675)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (FStar_Options.dont_gen_projectors
                                                    (FStar_TypeChecker_Env.current_module
                                                       env).FStar_Ident.str) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let _0_676 =
                                                   FStar_List.filter
                                                     (fun uu___107_7021  ->
                                                        match uu___107_7021
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7022 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: _0_676
                                               else q in
                                             let quals =
                                               let iquals =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___108_7030  ->
                                                         match uu___108_7030
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                           
                                                           |FStar_Syntax_Syntax.Private
                                                            -> true
                                                         | uu____7031 ->
                                                             false)) in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals) in
                                             let decl =
                                               FStar_Syntax_Syntax.Sig_declare_typ
                                                 (field_name, uvs, t, quals,
                                                   (FStar_Ident.range_of_lid
                                                      field_name)) in
                                             ((let uu____7035 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____7035
                                               then
                                                 let _0_677 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   _0_677
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     None
                                                     FStar_Syntax_Syntax.tun in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j  ->
                                                           fun uu____7062  ->
                                                             match uu____7062
                                                             with
                                                             | (x,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let _0_678
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (_0_678,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let _0_680
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (let _0_679
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (_0_679,
                                                                    FStar_Syntax_Syntax.tun))) in
                                                                    (_0_680,
                                                                    b))
                                                                   else
                                                                    (let _0_681
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_wild
                                                                    (FStar_Syntax_Syntax.gen_bv
                                                                    (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun)) in
                                                                    (_0_681,
                                                                    b)))) in
                                                 let pat =
                                                   let _0_684 =
                                                     pos
                                                       (FStar_Syntax_Syntax.Pat_cons
                                                          (let _0_682 =
                                                             FStar_Syntax_Syntax.lid_as_fv
                                                               lid
                                                               FStar_Syntax_Syntax.Delta_constant
                                                               (Some fvq) in
                                                           (_0_682, arg_pats))) in
                                                   let _0_683 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (_0_684, None, _0_683) in
                                                 let body =
                                                   (FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_match
                                                         (let _0_686 =
                                                            let _0_685 =
                                                              FStar_Syntax_Util.branch
                                                                pat in
                                                            [_0_685] in
                                                          (arg_exp, _0_686))))
                                                     None p in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____7132 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____7132
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       FStar_Syntax_Syntax.Delta_equational
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun in
                                                 let lb =
                                                   let _0_688 =
                                                     FStar_Util.Inr
                                                       (FStar_Syntax_Syntax.lid_as_fv
                                                          field_name dd None) in
                                                   let _0_687 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = _0_688;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = _0_687
                                                   } in
                                                 let impl =
                                                   FStar_Syntax_Syntax.Sig_let
                                                     (let _0_691 =
                                                        let _0_690 =
                                                          let _0_689 =
                                                            FStar_All.pipe_right
                                                              lb.FStar_Syntax_Syntax.lbname
                                                              FStar_Util.right in
                                                          FStar_All.pipe_right
                                                            _0_689
                                                            (fun fv  ->
                                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                        [_0_690] in
                                                      ((false, [lb]), p,
                                                        _0_691, quals, [])) in
                                                 (let uu____7154 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____7154
                                                  then
                                                    let _0_692 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      _0_692
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right _0_693 FStar_List.flatten in
                      FStar_List.append discriminator_ses projectors_ses
let mk_data_operations:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun env  ->
      fun tcs  ->
        fun se  ->
          match se with
          | FStar_Syntax_Syntax.Sig_datacon
              (constr_lid,uvs,t,typ_lid,n_typars,quals,uu____7182,r) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____7188 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____7188 with
               | (univ_opening,uvs) ->
                   let t = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____7201 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____7201 with
                    | (formals,uu____7211) ->
                        let uu____7222 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se  ->
                                 let uu____7235 =
                                   let _0_694 =
                                     FStar_Util.must
                                       (FStar_Syntax_Util.lid_of_sigelt se) in
                                   FStar_Ident.lid_equals typ_lid _0_694 in
                                 if uu____7235
                                 then
                                   match se with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____7244,uvs',tps,typ0,uu____7248,constrs,uu____7250,uu____7251)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____7265 -> failwith "Impossible"
                                 else None) in
                          match tps_opt with
                          | Some x -> x
                          | None  ->
                              if
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Syntax_Const.exn_lid
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Unexpected data constructor", r)) in
                        (match uu____7222 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ0 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____7307 =
                               FStar_Syntax_Util.arrow_formals typ0 in
                             (match uu____7307 with
                              | (indices,uu____7317) ->
                                  let refine_domain =
                                    let uu____7329 =
                                      FStar_All.pipe_right quals
                                        (FStar_Util.for_some
                                           (fun uu___109_7331  ->
                                              match uu___109_7331 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____7332 -> true
                                              | uu____7337 -> false)) in
                                    if uu____7329
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___110_7344 =
                                      match uu___110_7344 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____7346,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____7353 -> None in
                                    let uu____7354 =
                                      FStar_Util.find_map quals
                                        filter_records in
                                    match uu____7354 with
                                    | None  -> FStar_Syntax_Syntax.Data_ctor
                                    | Some q -> q in
                                  let iquals =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals in
                                  let fields =
                                    let uu____7362 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____7362 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____7393  ->
                                               fun uu____7394  ->
                                                 match (uu____7393,
                                                         uu____7394)
                                                 with
                                                 | ((x,uu____7404),(x',uu____7406))
                                                     ->
                                                     FStar_Syntax_Syntax.NT
                                                       (let _0_695 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x' in
                                                        (x, _0_695))) imp_tps
                                            inductive_tps in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals fv_qual refine_domain env typ_lid
                                    constr_lid uvs inductive_tps indices
                                    fields))))
          | uu____7411 -> []