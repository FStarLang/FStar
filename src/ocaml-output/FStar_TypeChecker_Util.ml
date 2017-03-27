open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)
let report :
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let _0_262 = FStar_TypeChecker_Env.get_range env  in
      let _0_261 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.report _0_262 _0_261
  
let is_type : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____15 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
    match uu____15 with
    | FStar_Syntax_Syntax.Tm_type uu____16 -> true
    | uu____17 -> false
  
let t_binders :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    let _0_263 = FStar_TypeChecker_Env.all_binders env  in
    FStar_All.pipe_right _0_263
      (FStar_List.filter
         (fun uu____29  ->
            match uu____29 with
            | (x,uu____33) -> is_type x.FStar_Syntax_Syntax.sort))
  
let new_uvar_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____43 =
          (FStar_Options.full_context_dependency ()) ||
            (let _0_264 = FStar_TypeChecker_Env.current_module env  in
             FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_264)
           in
        if uu____43
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env  in
      let _0_265 = FStar_TypeChecker_Env.get_range env  in
      FStar_TypeChecker_Env.new_uvar _0_265 bs k
  
let new_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  = fun env  -> fun k  -> Prims.fst (new_uvar_aux env k) 
let as_uvar : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___92_53  ->
    match uu___92_53 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____55);
        FStar_Syntax_Syntax.tk = uu____56;
        FStar_Syntax_Syntax.pos = uu____57;
        FStar_Syntax_Syntax.vars = uu____58;_} -> uv
    | uu____73 -> failwith "Impossible"
  
let new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar *
            FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          let uu____92 =
            FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid  in
          match uu____92 with
          | Some (uu____105::(tm,uu____107)::[]) ->
              let t =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))))
                  None tm.FStar_Syntax_Syntax.pos
                 in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____151 ->
              let uu____158 = new_uvar_aux env k  in
              (match uu____158 with
               | (t,u) ->
                   let g =
                     let uu___112_170 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     let _0_268 =
                       let _0_267 =
                         let _0_266 = as_uvar u  in
                         (reason, env, _0_266, t, k, r)  in
                       [_0_267]  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___112_170.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___112_170.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___112_170.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = _0_268
                     }  in
                   let _0_271 =
                     let _0_270 = let _0_269 = as_uvar u  in (_0_269, r)  in
                     [_0_270]  in
                   (t, _0_271, g))
  
let check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____200 = Prims.op_Negation (FStar_Util.set_is_empty uvs)  in
      if uu____200
      then
        let us =
          let _0_273 =
            let _0_272 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun uu____211  ->
                 match uu____211 with
                 | (x,uu____219) -> FStar_Syntax_Print.uvar_to_string x)
              _0_272
             in
          FStar_All.pipe_right _0_273 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let _0_275 =
            let _0_274 = FStar_Syntax_Print.term_to_string t  in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us _0_274
             in
          FStar_Errors.report r _0_275);
         FStar_Options.pop ())
      else ()
  
let force_sort' :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____245 = FStar_ST.read s.FStar_Syntax_Syntax.tk  in
    match uu____245 with
    | None  ->
        failwith
          (let _0_277 = FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos
              in
           let _0_276 = FStar_Syntax_Print.term_to_string s  in
           FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
             _0_277 _0_276)
    | Some tk -> tk
  
let force_sort s =
  (FStar_Syntax_Syntax.mk (force_sort' s)) None s.FStar_Syntax_Syntax.pos 
let extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.typ *
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
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t = FStar_Syntax_Subst.compress t  in
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (if univ_vars <> []
                then
                  failwith
                    "Impossible: non-empty universe variables but the type is unknown"
                else ();
                (let r = FStar_TypeChecker_Env.get_range env  in
                 let mk_binder scope a =
                   let uu____319 =
                     (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                      in
                   match uu____319 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____322 = FStar_Syntax_Util.type_u ()  in
                       (match uu____322 with
                        | (k,uu____328) ->
                            let t =
                              let _0_278 =
                                FStar_TypeChecker_Env.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k
                                 in
                              FStar_All.pipe_right _0_278 Prims.fst  in
                            ((let uu___113_332 = a  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___113_332.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___113_332.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), false))
                   | uu____333 -> (a, true)  in
                 let rec aux must_check_ty vars e =
                   let e = FStar_Syntax_Subst.compress e  in
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
                                         else mk_binder scope a  in
                                       (match uu____482 with
                                        | (tb,must_check_ty) ->
                                            let b = (tb, imp)  in
                                            let bs = FStar_List.append bs [b]
                                               in
                                            let scope =
                                              FStar_List.append scope [b]  in
                                            (scope, bs, must_check_ty)))
                              (vars, [], must_check_ty))
                          in
                       (match uu____415 with
                        | (scope,bs,must_check_ty) ->
                            let uu____543 = aux must_check_ty scope body  in
                            (match uu____543 with
                             | (res,must_check_ty) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t ->
                                       let uu____560 =
                                         FStar_Options.ml_ish ()  in
                                       if uu____560
                                       then FStar_Syntax_Util.ml_comp t r
                                       else FStar_Syntax_Syntax.mk_Total t
                                   | FStar_Util.Inr c -> c  in
                                 let t = FStar_Syntax_Util.arrow bs c  in
                                 ((let uu____565 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High
                                      in
                                   if uu____565
                                   then
                                     let _0_281 =
                                       FStar_Range.string_of_range r  in
                                     let _0_280 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let _0_279 =
                                       FStar_Util.string_of_bool
                                         must_check_ty
                                        in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       _0_281 _0_280 _0_279
                                   else ());
                                  ((FStar_Util.Inl t), must_check_ty))))
                   | uu____569 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let _0_283 =
                            FStar_Util.Inl
                              (let _0_282 =
                                 FStar_TypeChecker_Env.new_uvar r vars
                                   FStar_Syntax_Util.ktype0
                                  in
                               FStar_All.pipe_right _0_282 Prims.fst)
                             in
                          (_0_283, false))
                    in
                 let uu____581 =
                   let _0_284 = t_binders env  in aux false _0_284 e  in
                 match uu____581 with
                 | (t,b) ->
                     let t =
                       match t with
                       | FStar_Util.Inr c ->
                           let uu____598 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                           if uu____598
                           then FStar_TypeChecker_Env.result_typ env c
                           else
                             Prims.raise
                               (FStar_Errors.Error
                                  (let _0_286 =
                                     let _0_285 =
                                       FStar_Syntax_Print.comp_to_string c
                                        in
                                     FStar_Util.format1
                                       "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                       _0_285
                                      in
                                   (_0_286, rng)))
                       | FStar_Util.Inl t -> t  in
                     ([], t, b)))
           | uu____602 ->
               let uu____603 = FStar_Syntax_Subst.open_univ_vars univ_vars t
                  in
               (match uu____603 with | (univ_vars,t) -> (univ_vars, t, false)))
  
let pat_as_exps :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term
          Prims.list * FStar_Syntax_Syntax.pat)
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        let rec pat_as_arg_with_env allow_wc_dependence env p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let e =
                (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c))
                  None p.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env, e, p)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____686) ->
              let uu____691 = FStar_Syntax_Util.type_u ()  in
              (match uu____691 with
               | (k,uu____704) ->
                   let t = new_uvar env k  in
                   let x =
                     let uu___114_707 = x  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___114_707.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___114_707.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     }  in
                   let uu____708 =
                     let _0_287 = FStar_TypeChecker_Env.all_binders env  in
                     FStar_TypeChecker_Env.new_uvar p.FStar_Syntax_Syntax.p
                       _0_287 t
                      in
                   (match uu____708 with
                    | (e,u) ->
                        let p =
                          let uu___115_725 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___115_725.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___115_725.FStar_Syntax_Syntax.p)
                          }  in
                        ([], [], [], env, e, p)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____732 = FStar_Syntax_Util.type_u ()  in
              (match uu____732 with
               | (t,uu____745) ->
                   let x =
                     let uu___116_747 = x  in
                     let _0_288 = new_uvar env t  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___116_747.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___116_747.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = _0_288
                     }  in
                   let env =
                     if allow_wc_dependence
                     then FStar_TypeChecker_Env.push_bv env x
                     else env  in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x))
                       None p.FStar_Syntax_Syntax.p
                      in
                   ([x], [], [x], env, e, p))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____767 = FStar_Syntax_Util.type_u ()  in
              (match uu____767 with
               | (t,uu____780) ->
                   let x =
                     let uu___117_782 = x  in
                     let _0_289 = new_uvar env t  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___117_782.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___117_782.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = _0_289
                     }  in
                   let env = FStar_TypeChecker_Env.push_bv env x  in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x))
                       None p.FStar_Syntax_Syntax.p
                      in
                   ([x], [x], [], env, e, p))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____812 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____868  ->
                        fun uu____869  ->
                          match (uu____868, uu____869) with
                          | ((b,a,w,env,args,pats),(p,imp)) ->
                              let uu____968 =
                                pat_as_arg_with_env allow_wc_dependence env p
                                 in
                              (match uu____968 with
                               | (b',a',w',env,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   ((b' :: b), (a' :: a), (w' :: w), env,
                                     (arg :: args), ((pat, imp) :: pats))))
                     ([], [], [], env, [], []))
                 in
              (match uu____812 with
               | (b,a,w,env,args,pats) ->
                   let e =
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_meta
                           (let _0_292 =
                              (let _0_291 = FStar_Syntax_Syntax.fv_to_tm fv
                                  in
                               let _0_290 =
                                 FStar_All.pipe_right args FStar_List.rev  in
                               FStar_Syntax_Syntax.mk_Tm_app _0_291 _0_290)
                                None p.FStar_Syntax_Syntax.p
                               in
                            (_0_292,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Data_app))))) None
                       p.FStar_Syntax_Syntax.p
                      in
                   let _0_295 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let _0_294 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let _0_293 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (_0_295, _0_294, _0_293, env, e,
                     (let uu___118_1113 = p  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats)));
                        FStar_Syntax_Syntax.ty =
                          (uu___118_1113.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___118_1113.FStar_Syntax_Syntax.p)
                      })))
          | FStar_Syntax_Syntax.Pat_disj uu____1119 -> failwith "impossible"
           in
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
                FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r
             in
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let pats =
                FStar_List.map
                  (fun uu____1188  ->
                     match uu____1188 with
                     | (p,imp) ->
                         let _0_296 = elaborate_pat env p  in (_0_296, imp))
                  pats
                 in
              let uu____1205 =
                FStar_TypeChecker_Env.lookup_datacon env
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              (match uu____1205 with
               | (uu____1214,t) ->
                   let uu____1216 = FStar_Syntax_Util.arrow_formals_comp t
                      in
                   (match uu____1216 with
                    | (f,uu____1225) ->
                        let rec aux formals pats =
                          match (formals, pats) with
                          | ([],[]) -> []
                          | ([],uu____1296::uu____1297) ->
                              Prims.raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1332::uu____1333,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1373  ->
                                      match uu____1373 with
                                      | (t,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let _0_297 =
                                                   Some
                                                     (FStar_Syntax_Syntax.range_of_bv
                                                        t)
                                                    in
                                                 FStar_Syntax_Syntax.new_bv
                                                   _0_297
                                                   FStar_Syntax_Syntax.tun
                                                  in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                  in
                                               let _0_298 =
                                                 maybe_dot inaccessible a r
                                                  in
                                               (_0_298, true)
                                           | uu____1398 ->
                                               Prims.raise
                                                 (FStar_Errors.Error
                                                    (let _0_300 =
                                                       let _0_299 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p
                                                          in
                                                       FStar_Util.format1
                                                         "Insufficient pattern arguments (%s)"
                                                         _0_299
                                                        in
                                                     (_0_300,
                                                       (FStar_Ident.range_of_lid
                                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))))))
                          | (f::formals',(p,p_imp)::pats') ->
                              (match f with
                               | (uu____1450,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1451))
                                   when p_imp ->
                                   let _0_301 = aux formals' pats'  in
                                   (p, true) :: _0_301
                               | (uu____1459,Some
                                  (FStar_Syntax_Syntax.Implicit
                                  inaccessible)) ->
                                   let a =
                                     FStar_Syntax_Syntax.new_bv
                                       (Some (p.FStar_Syntax_Syntax.p))
                                       FStar_Syntax_Syntax.tun
                                      in
                                   let p =
                                     maybe_dot inaccessible a
                                       (FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                      in
                                   let _0_302 = aux formals' pats  in
                                   (p, true) :: _0_302
                               | (uu____1476,imp) ->
                                   let _0_305 =
                                     let _0_303 =
                                       FStar_Syntax_Syntax.is_implicit imp
                                        in
                                     (p, _0_303)  in
                                   let _0_304 = aux formals' pats'  in _0_305
                                     :: _0_304)
                           in
                        let uu___119_1486 = p  in
                        let _0_307 =
                          FStar_Syntax_Syntax.Pat_cons
                            (let _0_306 = aux f pats  in (fv, _0_306))
                           in
                        {
                          FStar_Syntax_Syntax.v = _0_307;
                          FStar_Syntax_Syntax.ty =
                            (uu___119_1486.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___119_1486.FStar_Syntax_Syntax.p)
                        }))
          | uu____1494 -> p  in
        let one_pat allow_wc_dependence env p =
          let p = elaborate_pat env p  in
          let uu____1520 = pat_as_arg_with_env allow_wc_dependence env p  in
          match uu____1520 with
          | (b,a,w,env,arg,p) ->
              let uu____1550 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____1550 with
               | Some x ->
                   Prims.raise
                     (FStar_Errors.Error
                        (let _0_308 =
                           FStar_TypeChecker_Err.nonlinear_pattern_variable x
                            in
                         (_0_308, (p.FStar_Syntax_Syntax.p))))
               | uu____1571 -> (b, a, w, arg, p))
           in
        let top_level_pat_as_args env p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_disj [] -> failwith "impossible"
          | FStar_Syntax_Syntax.Pat_disj (q::pats) ->
              let uu____1614 = one_pat false env q  in
              (match uu____1614 with
               | (b,a,uu____1630,te,q) ->
                   let uu____1639 =
                     FStar_List.fold_right
                       (fun p  ->
                          fun uu____1655  ->
                            match uu____1655 with
                            | (w,args,pats) ->
                                let uu____1679 = one_pat false env p  in
                                (match uu____1679 with
                                 | (b',a',w',arg,p) ->
                                     let uu____1705 =
                                       Prims.op_Negation
                                         (FStar_Util.multiset_equiv
                                            FStar_Syntax_Syntax.bv_eq a a')
                                        in
                                     if uu____1705
                                     then
                                       Prims.raise
                                         (FStar_Errors.Error
                                            (let _0_310 =
                                               FStar_TypeChecker_Err.disjunctive_pattern_vars
                                                 a a'
                                                in
                                             let _0_309 =
                                               FStar_TypeChecker_Env.get_range
                                                 env
                                                in
                                             (_0_310, _0_309)))
                                     else
                                       (let _0_312 =
                                          let _0_311 =
                                            FStar_Syntax_Syntax.as_arg arg
                                             in
                                          _0_311 :: args  in
                                        ((FStar_List.append w' w), _0_312, (p
                                          :: pats))))) pats ([], [], [])
                      in
                   (match uu____1639 with
                    | (w,args,pats) ->
                        let _0_314 =
                          let _0_313 = FStar_Syntax_Syntax.as_arg te  in
                          _0_313 :: args  in
                        ((FStar_List.append b w), _0_314,
                          (let uu___120_1743 = p  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_disj (q :: pats));
                             FStar_Syntax_Syntax.ty =
                               (uu___120_1743.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___120_1743.FStar_Syntax_Syntax.p)
                           }))))
          | uu____1744 ->
              let uu____1745 = one_pat true env p  in
              (match uu____1745 with
               | (b,uu____1760,uu____1761,arg,p) ->
                   let _0_316 =
                     let _0_315 = FStar_Syntax_Syntax.as_arg arg  in [_0_315]
                      in
                   (b, _0_316, p))
           in
        let uu____1772 = top_level_pat_as_args env p  in
        match uu____1772 with
        | (b,args,p) ->
            let exps = FStar_All.pipe_right args (FStar_List.map Prims.fst)
               in
            (b, exps, p)
  
let decorate_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.pat
  =
  fun env  ->
    fun p  ->
      fun exps  ->
        let qq = p  in
        let rec aux p e =
          let pkg q t =
            FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p  in
          let e = FStar_Syntax_Util.unmeta e  in
          match ((p.FStar_Syntax_Syntax.v), (e.FStar_Syntax_Syntax.n)) with
          | (uu____1843,FStar_Syntax_Syntax.Tm_uinst (e,uu____1845)) ->
              aux p e
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1850,FStar_Syntax_Syntax.Tm_constant uu____1851) ->
              let _0_317 = force_sort' e  in
              pkg p.FStar_Syntax_Syntax.v _0_317
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 failwith
                   (let _0_319 = FStar_Syntax_Print.bv_to_string x  in
                    let _0_318 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      _0_319 _0_318)
               else ();
               (let uu____1857 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____1857
                then
                  let _0_321 = FStar_Syntax_Print.bv_to_string x  in
                  let _0_320 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" _0_321
                    _0_320
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x =
                  let uu___121_1861 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___121_1861.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___121_1861.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1865 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____1865
                then
                  failwith
                    (let _0_323 = FStar_Syntax_Print.bv_to_string x  in
                     let _0_322 = FStar_Syntax_Print.bv_to_string y  in
                     FStar_Util.format2
                       "Expected pattern variable %s; got %s" _0_323 _0_322)
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x =
                  let uu___122_1869 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___122_1869.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___122_1869.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1871),uu____1872) ->
              let s = force_sort e  in
              let x =
                let uu___123_1881 = x  in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___123_1881.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___123_1881.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                }  in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1894 =
                  Prims.op_Negation (FStar_Syntax_Syntax.fv_eq fv fv')  in
                if uu____1894
                then
                  failwith
                    (FStar_Util.format2
                       "Expected pattern constructor %s; got %s"
                       ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str)
                else ());
               (let _0_324 = force_sort' e  in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) _0_324))
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
              ((let uu____1974 =
                  let _0_325 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right _0_325 Prims.op_Negation  in
                if uu____1974
                then
                  failwith
                    (FStar_Util.format2
                       "Expected pattern constructor %s; got %s"
                       ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str)
                else ());
               (let fv = fv'  in
                let rec match_args matched_pats args argpats =
                  match (args, argpats) with
                  | ([],[]) ->
                      let _0_326 = force_sort' e  in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv, (FStar_List.rev matched_pats))) _0_326
                  | (arg::args,(argpat,uu____2074)::argpats) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2124) ->
                           let x =
                             let _0_327 = force_sort e  in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p.FStar_Syntax_Syntax.p)) _0_327
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args
                             argpats
                       | ((e,imp),uu____2153) ->
                           let pat =
                             let _0_329 = aux argpat e  in
                             let _0_328 = FStar_Syntax_Syntax.is_implicit imp
                                in
                             (_0_329, _0_328)  in
                           match_args (pat :: matched_pats) args argpats)
                  | uu____2170 ->
                      failwith
                        (let _0_331 = FStar_Syntax_Print.pat_to_string p  in
                         let _0_330 = FStar_Syntax_Print.term_to_string e  in
                         FStar_Util.format2
                           "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                           _0_331 _0_330)
                   in
                match_args [] args argpats))
          | uu____2190 ->
              failwith
                (let _0_335 =
                   FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                 let _0_334 = FStar_Syntax_Print.pat_to_string qq  in
                 let _0_333 =
                   let _0_332 =
                     FStar_All.pipe_right exps
                       (FStar_List.map FStar_Syntax_Print.term_to_string)
                      in
                   FStar_All.pipe_right _0_332 (FStar_String.concat "\n\t")
                    in
                 FStar_Util.format3
                   "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                   _0_335 _0_334 _0_333)
           in
        match ((p.FStar_Syntax_Syntax.v), exps) with
        | (FStar_Syntax_Syntax.Pat_disj ps,uu____2198) when
            (FStar_List.length ps) = (FStar_List.length exps) ->
            let ps = FStar_List.map2 aux ps exps  in
            FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj ps)
              FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
              p.FStar_Syntax_Syntax.p
        | (uu____2214,e::[]) -> aux p e
        | uu____2217 -> failwith "Unexpected number of patterns"
  
let rec decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty)  in
    let mk f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p  in
    let pat_as_arg uu____2254 =
      match uu____2254 with
      | (p,i) ->
          let uu____2264 = decorated_pattern_as_term p  in
          (match uu____2264 with
           | (vars,te) ->
               let _0_337 =
                 let _0_336 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, _0_336)  in
               (vars, _0_337))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____2283 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Pat_constant c ->
        let _0_338 = mk (FStar_Syntax_Syntax.Tm_constant c)  in ([], _0_338)
    | FStar_Syntax_Syntax.Pat_wild x|FStar_Syntax_Syntax.Pat_var x ->
        let _0_339 = mk (FStar_Syntax_Syntax.Tm_name x)  in ([x], _0_339)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2306 =
          let _0_340 = FStar_All.pipe_right pats (FStar_List.map pat_as_arg)
             in
          FStar_All.pipe_right _0_340 FStar_List.unzip  in
        (match uu____2306 with
         | (vars,args) ->
             let vars = FStar_List.flatten vars  in
             let _0_342 =
               mk
                 (FStar_Syntax_Syntax.Tm_app
                    (let _0_341 = FStar_Syntax_Syntax.fv_to_tm fv  in
                     (_0_341, args)))
                in
             (vars, _0_342))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let arrow_formals :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun k  ->
      let uu____2388 = FStar_Syntax_Util.arrow_formals_comp k  in
      match uu____2388 with
      | (bs,c) ->
          let _0_343 = FStar_TypeChecker_Env.result_typ env c  in
          (bs, _0_343)
  
let join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2416 =
          let _0_345 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let _0_344 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env _0_345 _0_344  in
        match uu____2416 with | (m,uu____2421,uu____2422) -> m
  
let lift_and_destruct :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        (FStar_TypeChecker_Env.normal_comp_typ *
          FStar_TypeChecker_Env.normal_comp_typ)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c1 = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c1  in
        let c2 = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c2  in
        let uu____2436 =
          FStar_TypeChecker_Env.join env c1.FStar_TypeChecker_Env.nct_name
            c2.FStar_TypeChecker_Env.nct_name
           in
        match uu____2436 with
        | (m,lift1,lift2) ->
            let _0_347 = lift1 c1  in
            let _0_346 = lift2 c2  in (_0_347, _0_346)
  
let force_teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let _0_348 = FStar_TypeChecker_Rel.teq env t1 t2  in
        FStar_TypeChecker_Rel.force_trivial_guard env _0_348
  
let join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.lcomp * FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc1  ->
      fun lc2  ->
        let uu____2469 =
          (FStar_Syntax_Util.is_total_lcomp lc1) &&
            (FStar_Syntax_Util.is_total_lcomp lc2)
           in
        if uu____2469
        then (lc1, lc2)
        else
          (let nct_of_lcomp lc =
             let _0_350 =
               FStar_Syntax_Syntax.as_arg
                 lc.FStar_Syntax_Syntax.lcomp_res_typ
                in
             let _0_349 = FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                in
             {
               FStar_TypeChecker_Env.nct_name =
                 (lc.FStar_Syntax_Syntax.lcomp_name);
               FStar_TypeChecker_Env.nct_univs =
                 (lc.FStar_Syntax_Syntax.lcomp_univs);
               FStar_TypeChecker_Env.nct_indices =
                 (lc.FStar_Syntax_Syntax.lcomp_indices);
               FStar_TypeChecker_Env.nct_result = _0_350;
               FStar_TypeChecker_Env.nct_wp = _0_349;
               FStar_TypeChecker_Env.nct_flags =
                 (lc.FStar_Syntax_Syntax.lcomp_cflags)
             }  in
           let lcomp_of_nct nct =
             {
               FStar_Syntax_Syntax.lcomp_name =
                 (nct.FStar_TypeChecker_Env.nct_name);
               FStar_Syntax_Syntax.lcomp_univs =
                 (nct.FStar_TypeChecker_Env.nct_univs);
               FStar_Syntax_Syntax.lcomp_indices =
                 (nct.FStar_TypeChecker_Env.nct_indices);
               FStar_Syntax_Syntax.lcomp_res_typ =
                 (Prims.fst nct.FStar_TypeChecker_Env.nct_result);
               FStar_Syntax_Syntax.lcomp_cflags =
                 (nct.FStar_TypeChecker_Env.nct_flags);
               FStar_Syntax_Syntax.lcomp_as_comp =
                 (fun uu____2483  ->
                    FStar_TypeChecker_Env.normal_comp_typ_as_comp env nct)
             }  in
           let uu____2484 =
             FStar_TypeChecker_Env.join env
               lc1.FStar_Syntax_Syntax.lcomp_name
               lc2.FStar_Syntax_Syntax.lcomp_name
              in
           match uu____2484 with
           | (uu____2490,lift1,lift2) ->
               let nct1 = lift1 (nct_of_lcomp lc1)  in
               let nct2 = lift2 (nct_of_lcomp lc2)  in
               ((let _0_354 =
                   FStar_List.tl nct1.FStar_TypeChecker_Env.nct_univs  in
                 let _0_353 =
                   FStar_List.tl nct2.FStar_TypeChecker_Env.nct_univs  in
                 FStar_List.iter2
                   (fun u  ->
                      fun v  ->
                        let _0_352 = FStar_Syntax_Util.type_at_u u  in
                        let _0_351 = FStar_Syntax_Util.type_at_u v  in
                        force_teq env _0_352 _0_351) _0_354 _0_353);
                FStar_List.iter2
                  (fun uu____2505  ->
                     fun uu____2506  ->
                       match (uu____2505, uu____2506) with
                       | ((i,uu____2516),(j,uu____2518)) -> force_teq env i j)
                  nct1.FStar_TypeChecker_Env.nct_indices
                  nct2.FStar_TypeChecker_Env.nct_indices;
                ((lcomp_of_nct nct1), (lcomp_of_nct nct2))))
  
let is_pure_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l = FStar_TypeChecker_Env.norm_eff_name env l  in
      FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid
  
let is_pure_or_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l = FStar_TypeChecker_Env.norm_eff_name env l  in
      (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid)
  
let mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universes ->
      FStar_Syntax_Syntax.arg Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  =
  fun mname  ->
    fun univs  ->
      fun indices  ->
        fun result  ->
          fun wp  ->
            fun flags  ->
              FStar_Syntax_Syntax.mk_Comp
                (let _0_359 =
                   let _0_358 =
                     let _0_357 = FStar_Syntax_Syntax.as_arg result  in
                     let _0_356 =
                       let _0_355 = FStar_Syntax_Syntax.as_arg wp  in
                       [_0_355]  in
                     _0_357 :: _0_356  in
                   FStar_List.append indices _0_358  in
                 {
                   FStar_Syntax_Syntax.comp_typ_name = mname;
                   FStar_Syntax_Syntax.comp_univs = univs;
                   FStar_Syntax_Syntax.effect_args = _0_359;
                   FStar_Syntax_Syntax.flags = flags
                 })
  
let mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universes ->
      FStar_Syntax_Syntax.arg Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let subst_lcomp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun subst  ->
    fun lc  ->
      let uu___124_2582 = lc  in
      let _0_361 =
        FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.lcomp_res_typ
         in
      {
        FStar_Syntax_Syntax.lcomp_name =
          (uu___124_2582.FStar_Syntax_Syntax.lcomp_name);
        FStar_Syntax_Syntax.lcomp_univs =
          (uu___124_2582.FStar_Syntax_Syntax.lcomp_univs);
        FStar_Syntax_Syntax.lcomp_indices =
          (uu___124_2582.FStar_Syntax_Syntax.lcomp_indices);
        FStar_Syntax_Syntax.lcomp_res_typ = _0_361;
        FStar_Syntax_Syntax.lcomp_cflags =
          (uu___124_2582.FStar_Syntax_Syntax.lcomp_cflags);
        FStar_Syntax_Syntax.lcomp_as_comp =
          (fun uu____2583  ->
             let _0_360 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
             FStar_Syntax_Subst.subst_comp subst _0_360)
      }
  
let is_function : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2587 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
       in
    match uu____2587 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2588 -> true
    | uu____2596 -> false
  
let return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun t  ->
      fun v  ->
        let c =
          let uu____2607 =
            let _0_362 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid
               in
            FStar_All.pipe_left Prims.op_Negation _0_362  in
          if uu____2607
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_Util.must
                 (FStar_TypeChecker_Env.effect_decl_opt env
                    FStar_Syntax_Const.effect_PURE_lid)
                in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t  in
             let wp =
               let uu____2612 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                  in
               if uu____2612
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2614 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid
                     in
                  match uu____2614 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp
                         in
                      let _0_368 =
                        (let _0_367 =
                           FStar_TypeChecker_Env.inst_effect_fun_with 
                             [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                            in
                         let _0_366 =
                           let _0_365 = FStar_Syntax_Syntax.as_arg t  in
                           let _0_364 =
                             let _0_363 = FStar_Syntax_Syntax.as_arg v  in
                             [_0_363]  in
                           _0_365 :: _0_364  in
                         FStar_Syntax_Syntax.mk_Tm_app _0_367 _0_366)
                          (Some (k.FStar_Syntax_Syntax.n))
                          v.FStar_Syntax_Syntax.pos
                         in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env _0_368)
                in
             (mk_comp m) [u_t] [] t wp [FStar_Syntax_Syntax.RETURN])
           in
        (let uu____2627 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return")
            in
         if uu____2627
         then
           let _0_371 = FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos
              in
           let _0_370 = FStar_Syntax_Print.term_to_string v  in
           let _0_369 = FStar_TypeChecker_Normalize.comp_to_string env c  in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" _0_371
             _0_370 _0_369
         else ());
        c
  
let bind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.lcomp ->
        lcomp_with_binder -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun e1opt  ->
      fun lc1  ->
        fun uu____2641  ->
          match uu____2641 with
          | (b,lc2) ->
              let lc1 =
                FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
              let lc2 =
                FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
              ((let uu____2650 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                if uu____2650
                then
                  let bstr =
                    match b with
                    | None  -> "none"
                    | Some x -> FStar_Syntax_Print.bv_to_string x  in
                  let _0_374 =
                    match e1opt with
                    | None  -> "None"
                    | Some e -> FStar_Syntax_Print.term_to_string e  in
                  let _0_373 = FStar_Syntax_Print.lcomp_to_string lc1  in
                  let _0_372 = FStar_Syntax_Print.lcomp_to_string lc2  in
                  FStar_Util.print4
                    "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                    _0_374 _0_373 bstr _0_372
                else ());
               (let uu____2655 = join_lcomp env lc1 lc2  in
                match uu____2655 with
                | (lc1,lc2) ->
                    let bind_it uu____2663 =
                      let c1 = lc1.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                      let c2 = lc2.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                      (let uu____2671 =
                         FStar_TypeChecker_Env.debug env
                           FStar_Options.Extreme
                          in
                       if uu____2671
                       then
                         let _0_379 =
                           match b with
                           | None  -> "none"
                           | Some x -> FStar_Syntax_Print.bv_to_string x  in
                         let _0_378 = FStar_Syntax_Print.lcomp_to_string lc1
                            in
                         let _0_377 = FStar_Syntax_Print.comp_to_string c1
                            in
                         let _0_376 = FStar_Syntax_Print.lcomp_to_string lc2
                            in
                         let _0_375 = FStar_Syntax_Print.comp_to_string c2
                            in
                         FStar_Util.print5
                           "b=%s,Evaluated %s to %s\n And %s to %s\n" _0_379
                           _0_378 _0_377 _0_376 _0_375
                       else ());
                      (let try_simplify uu____2680 =
                         let aux uu____2689 =
                           let uu____2690 =
                             FStar_Syntax_Util.is_trivial_wp c1  in
                           if uu____2690
                           then
                             match b with
                             | None  -> Some (c2, "trivial no binder")
                             | Some uu____2707 ->
                                 let uu____2708 =
                                   FStar_Syntax_Util.is_ml_comp c2  in
                                 (if uu____2708
                                  then Some (c2, "trivial ml")
                                  else None)
                           else
                             (let uu____2726 =
                                (FStar_Syntax_Util.is_ml_comp c1) &&
                                  (FStar_Syntax_Util.is_ml_comp c2)
                                 in
                              if uu____2726
                              then Some (c2, "both ml")
                              else None)
                            in
                         let subst_c2 reason =
                           match (e1opt, b) with
                           | (Some e,Some x) ->
                               Some
                                 (let _0_380 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2
                                     in
                                  (_0_380, reason))
                           | uu____2761 -> aux ()  in
                         let uu____2766 =
                           (FStar_Syntax_Util.is_total_comp c1) &&
                             (FStar_Syntax_Util.is_total_comp c2)
                            in
                         if uu____2766
                         then subst_c2 "both total"
                         else
                           (let uu____2771 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                               in
                            if uu____2771
                            then
                              Some
                                (let _0_381 =
                                   FStar_Syntax_Syntax.mk_GTotal
                                     (FStar_TypeChecker_Env.result_typ env c2)
                                    in
                                 (_0_381, "both gtot"))
                            else
                              (match (e1opt, b) with
                               | (Some e,Some x) ->
                                   let uu____2787 =
                                     (FStar_Syntax_Util.is_total_comp c1) &&
                                       (Prims.op_Negation
                                          (FStar_Syntax_Syntax.is_null_bv x))
                                      in
                                   if uu____2787
                                   then subst_c2 "substituted e"
                                   else aux ()
                               | uu____2792 -> aux ()))
                          in
                       let uu____2797 = try_simplify ()  in
                       match uu____2797 with
                       | Some (c,reason) -> c
                       | None  ->
                           let nct1 =
                             FStar_TypeChecker_Env.comp_as_normal_comp_typ
                               env c1
                              in
                           let nct2 =
                             FStar_TypeChecker_Env.comp_as_normal_comp_typ
                               env c2
                              in
                           let md =
                             FStar_TypeChecker_Env.get_effect_decl env
                               nct1.FStar_TypeChecker_Env.nct_name
                              in
                           let t1 =
                             Prims.fst nct1.FStar_TypeChecker_Env.nct_result
                              in
                           let t2 =
                             Prims.fst nct2.FStar_TypeChecker_Env.nct_result
                              in
                           let mk_lam wp =
                             let bs =
                               match b with
                               | None  ->
                                   let _0_382 =
                                     FStar_Syntax_Syntax.null_binder
                                       (Prims.fst
                                          nct1.FStar_TypeChecker_Env.nct_result)
                                      in
                                   [_0_382]
                               | Some x ->
                                   let _0_383 =
                                     FStar_Syntax_Syntax.mk_binder x  in
                                   [_0_383]
                                in
                             FStar_Syntax_Util.abs bs wp
                               (Some
                                  (FStar_Util.Inr
                                     (FStar_Syntax_Const.effect_Tot_lid,
                                       [FStar_Syntax_Syntax.TOTAL])))
                              in
                           let bind_inst =
                             let _0_386 =
                               let _0_385 =
                                 let _0_384 =
                                   FStar_List.hd
                                     nct2.FStar_TypeChecker_Env.nct_univs
                                    in
                                 [_0_384]  in
                               FStar_List.append
                                 nct1.FStar_TypeChecker_Env.nct_univs _0_385
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               _0_386 env md md.FStar_Syntax_Syntax.bind_wp
                              in
                           let bind_args =
                             let _0_391 =
                               let _0_390 =
                                 let _0_389 =
                                   let _0_388 =
                                     let _0_387 =
                                       FStar_Syntax_Syntax.as_arg
                                         (mk_lam
                                            (Prims.fst
                                               nct2.FStar_TypeChecker_Env.nct_wp))
                                        in
                                     [_0_387]  in
                                   (nct1.FStar_TypeChecker_Env.nct_wp) ::
                                     _0_388
                                    in
                                 (nct2.FStar_TypeChecker_Env.nct_result) ::
                                   _0_389
                                  in
                               (nct1.FStar_TypeChecker_Env.nct_result) ::
                                 _0_390
                                in
                             FStar_List.append
                               nct1.FStar_TypeChecker_Env.nct_indices _0_391
                              in
                           let wp =
                             (FStar_Syntax_Syntax.mk_Tm_app bind_inst
                                bind_args) None t2.FStar_Syntax_Syntax.pos
                              in
                           let nct =
                             let uu___125_2860 = nct2  in
                             let _0_392 = FStar_Syntax_Syntax.as_arg wp  in
                             {
                               FStar_TypeChecker_Env.nct_name =
                                 (uu___125_2860.FStar_TypeChecker_Env.nct_name);
                               FStar_TypeChecker_Env.nct_univs =
                                 (uu___125_2860.FStar_TypeChecker_Env.nct_univs);
                               FStar_TypeChecker_Env.nct_indices =
                                 (uu___125_2860.FStar_TypeChecker_Env.nct_indices);
                               FStar_TypeChecker_Env.nct_result =
                                 (uu___125_2860.FStar_TypeChecker_Env.nct_result);
                               FStar_TypeChecker_Env.nct_wp = _0_392;
                               FStar_TypeChecker_Env.nct_flags =
                                 (uu___125_2860.FStar_TypeChecker_Env.nct_flags)
                             }  in
                           FStar_TypeChecker_Env.normal_comp_typ_as_comp env
                             nct)
                       in
                    let uu____2861 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2861
                    then lc2
                    else
                      (let uu___126_2863 = lc2  in
                       {
                         FStar_Syntax_Syntax.lcomp_name =
                           (uu___126_2863.FStar_Syntax_Syntax.lcomp_name);
                         FStar_Syntax_Syntax.lcomp_univs =
                           (uu___126_2863.FStar_Syntax_Syntax.lcomp_univs);
                         FStar_Syntax_Syntax.lcomp_indices =
                           (uu___126_2863.FStar_Syntax_Syntax.lcomp_indices);
                         FStar_Syntax_Syntax.lcomp_res_typ =
                           (uu___126_2863.FStar_Syntax_Syntax.lcomp_res_typ);
                         FStar_Syntax_Syntax.lcomp_cflags =
                           (uu___126_2863.FStar_Syntax_Syntax.lcomp_cflags);
                         FStar_Syntax_Syntax.lcomp_as_comp = bind_it
                       })))
  
let label :
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
  
let label_opt :
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
              let uu____2907 =
                let _0_393 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation _0_393  in
              if uu____2907
              then f
              else (let _0_394 = reason ()  in label _0_394 r f)
  
let label_guard :
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
            let uu___127_2919 = g  in
            let _0_395 =
              FStar_TypeChecker_Common.NonTrivial (label reason r f)  in
            {
              FStar_TypeChecker_Env.guard_f = _0_395;
              FStar_TypeChecker_Env.deferred =
                (uu___127_2919.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___127_2919.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___127_2919.FStar_TypeChecker_Env.implicits)
            }
  
let weaken_guard :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2  in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____2929 -> g2
  
let weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____2946 =
          let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          match f with
          | FStar_TypeChecker_Common.Trivial  -> c
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2953 = FStar_Syntax_Util.is_ml_comp c  in
              if uu____2953
              then c
              else
                (let nct =
                   FStar_TypeChecker_Env.comp_as_normal_comp_typ env c  in
                 let md =
                   FStar_TypeChecker_Env.get_effect_decl env
                     nct.FStar_TypeChecker_Env.nct_name
                    in
                 let wp =
                   let _0_401 =
                     (FStar_All.pipe_right nct.FStar_TypeChecker_Env.nct_wp
                        Prims.fst).FStar_Syntax_Syntax.pos
                      in
                   (let _0_400 =
                      FStar_TypeChecker_Env.inst_effect_fun_with
                        nct.FStar_TypeChecker_Env.nct_univs env md
                        md.FStar_Syntax_Syntax.assume_p
                       in
                    let _0_399 =
                      let _0_398 =
                        let _0_397 =
                          let _0_396 = FStar_Syntax_Syntax.as_arg f  in
                          [_0_396; nct.FStar_TypeChecker_Env.nct_wp]  in
                        (nct.FStar_TypeChecker_Env.nct_result) :: _0_397  in
                      FStar_List.append nct.FStar_TypeChecker_Env.nct_indices
                        _0_398
                       in
                    FStar_Syntax_Syntax.mk_Tm_app _0_400 _0_399) None _0_401
                    in
                 let _0_403 =
                   let uu___128_2974 = nct  in
                   let _0_402 = FStar_Syntax_Syntax.as_arg wp  in
                   {
                     FStar_TypeChecker_Env.nct_name =
                       (uu___128_2974.FStar_TypeChecker_Env.nct_name);
                     FStar_TypeChecker_Env.nct_univs =
                       (uu___128_2974.FStar_TypeChecker_Env.nct_univs);
                     FStar_TypeChecker_Env.nct_indices =
                       (uu___128_2974.FStar_TypeChecker_Env.nct_indices);
                     FStar_TypeChecker_Env.nct_result =
                       (uu___128_2974.FStar_TypeChecker_Env.nct_result);
                     FStar_TypeChecker_Env.nct_wp = _0_402;
                     FStar_TypeChecker_Env.nct_flags =
                       (uu___128_2974.FStar_TypeChecker_Env.nct_flags)
                   }  in
                 FStar_TypeChecker_Env.normal_comp_typ_as_comp env _0_403)
           in
        let uu____2975 =
          env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
        if uu____2975
        then lc
        else
          (let uu___129_2977 = lc  in
           {
             FStar_Syntax_Syntax.lcomp_name =
               (uu___129_2977.FStar_Syntax_Syntax.lcomp_name);
             FStar_Syntax_Syntax.lcomp_univs =
               (uu___129_2977.FStar_Syntax_Syntax.lcomp_univs);
             FStar_Syntax_Syntax.lcomp_indices =
               (uu___129_2977.FStar_Syntax_Syntax.lcomp_indices);
             FStar_Syntax_Syntax.lcomp_res_typ =
               (uu___129_2977.FStar_Syntax_Syntax.lcomp_res_typ);
             FStar_Syntax_Syntax.lcomp_cflags =
               (uu___129_2977.FStar_Syntax_Syntax.lcomp_cflags);
             FStar_Syntax_Syntax.lcomp_as_comp = weaken
           })
  
let strengthen_precondition :
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t)
  =
  fun reason  ->
    fun env  ->
      fun e  ->
        fun lc  ->
          fun g0  ->
            let uu____3004 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____3004
            then (lc, g0)
            else
              ((let uu____3009 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme
                   in
                if uu____3009
                then
                  let _0_405 =
                    FStar_TypeChecker_Normalize.term_to_string env e  in
                  let _0_404 = FStar_TypeChecker_Rel.guard_to_string env g0
                     in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    _0_405 _0_404
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.lcomp_cflags
                    (FStar_List.collect
                       (fun uu___93_3015  ->
                          match uu___93_3015 with
                          | FStar_Syntax_Syntax.RETURN 
                            |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3017 -> []))
                   in
                let strengthen uu____3023 =
                  let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                  let g0 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                  let uu____3028 = FStar_TypeChecker_Rel.guard_form g0  in
                  match uu____3028 with
                  | FStar_TypeChecker_Common.Trivial  -> c
                  | FStar_TypeChecker_Common.NonTrivial f ->
                      let c =
                        let uu____3035 =
                          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                            (Prims.op_Negation
                               (FStar_Syntax_Util.is_partial_return c))
                           in
                        if uu____3035
                        then
                          let x =
                            let _0_406 =
                              FStar_TypeChecker_Env.result_typ env c  in
                            FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                              None _0_406
                             in
                          let xret =
                            let _0_408 =
                              let _0_407 = FStar_Syntax_Syntax.bv_to_name x
                                 in
                              return_value env x.FStar_Syntax_Syntax.sort
                                _0_407
                               in
                            FStar_Syntax_Util.comp_set_flags _0_408
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             in
                          let lc =
                            let _0_411 =
                              FStar_TypeChecker_Env.lcomp_of_comp env c  in
                            let _0_410 =
                              let _0_409 =
                                FStar_TypeChecker_Env.lcomp_of_comp env xret
                                 in
                              ((Some x), _0_409)  in
                            bind env (Some e) _0_411 _0_410  in
                          lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                        else c  in
                      ((let uu____3046 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            FStar_Options.Extreme
                           in
                        if uu____3046
                        then
                          let _0_413 =
                            FStar_TypeChecker_Normalize.term_to_string env e
                             in
                          let _0_412 =
                            FStar_TypeChecker_Normalize.term_to_string env f
                             in
                          FStar_Util.print2
                            "-------------Strengthening pre-condition of term %s with guard %s\n"
                            _0_413 _0_412
                        else ());
                       (let nct =
                          FStar_TypeChecker_Env.comp_as_normal_comp_typ env c
                           in
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            nct.FStar_TypeChecker_Env.nct_name
                           in
                        let wp =
                          let _0_421 =
                            (FStar_All.pipe_right
                               nct.FStar_TypeChecker_Env.nct_wp Prims.fst).FStar_Syntax_Syntax.pos
                             in
                          (let _0_420 =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               nct.FStar_TypeChecker_Env.nct_univs env md
                               md.FStar_Syntax_Syntax.assert_p
                              in
                           let _0_419 =
                             let _0_418 =
                               let _0_417 =
                                 let _0_416 =
                                   let _0_415 =
                                     let _0_414 =
                                       FStar_TypeChecker_Env.get_range env
                                        in
                                     label_opt env reason _0_414 f  in
                                   FStar_All.pipe_left
                                     FStar_Syntax_Syntax.as_arg _0_415
                                    in
                                 [_0_416; nct.FStar_TypeChecker_Env.nct_wp]
                                  in
                               (nct.FStar_TypeChecker_Env.nct_result) ::
                                 _0_417
                                in
                             FStar_List.append
                               nct.FStar_TypeChecker_Env.nct_indices _0_418
                              in
                           FStar_Syntax_Syntax.mk_Tm_app _0_420 _0_419) None
                            _0_421
                           in
                        (let uu____3066 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             FStar_Options.Extreme
                            in
                         if uu____3066
                         then
                           let _0_422 = FStar_Syntax_Print.term_to_string wp
                              in
                           FStar_Util.print1
                             "-------------Strengthened pre-condition is %s\n"
                             _0_422
                         else ());
                        (let c2 =
                           let _0_424 =
                             let uu___130_3069 = nct  in
                             let _0_423 = FStar_Syntax_Syntax.as_arg wp  in
                             {
                               FStar_TypeChecker_Env.nct_name =
                                 (uu___130_3069.FStar_TypeChecker_Env.nct_name);
                               FStar_TypeChecker_Env.nct_univs =
                                 (uu___130_3069.FStar_TypeChecker_Env.nct_univs);
                               FStar_TypeChecker_Env.nct_indices =
                                 (uu___130_3069.FStar_TypeChecker_Env.nct_indices);
                               FStar_TypeChecker_Env.nct_result =
                                 (uu___130_3069.FStar_TypeChecker_Env.nct_result);
                               FStar_TypeChecker_Env.nct_wp = _0_423;
                               FStar_TypeChecker_Env.nct_flags =
                                 (uu___130_3069.FStar_TypeChecker_Env.nct_flags)
                             }  in
                           FStar_TypeChecker_Env.normal_comp_typ_as_comp env
                             _0_424
                            in
                         c2)))
                   in
                let flags =
                  let uu____3072 =
                    (FStar_Syntax_Util.is_pure_lcomp lc) &&
                      (let _0_425 =
                         FStar_Syntax_Util.is_function_typ
                           lc.FStar_Syntax_Syntax.lcomp_res_typ
                          in
                       FStar_All.pipe_left Prims.op_Negation _0_425)
                     in
                  if uu____3072 then flags else []  in
                let lc =
                  let uu___131_3076 = lc  in
                  {
                    FStar_Syntax_Syntax.lcomp_name =
                      (uu___131_3076.FStar_Syntax_Syntax.lcomp_name);
                    FStar_Syntax_Syntax.lcomp_univs =
                      (uu___131_3076.FStar_Syntax_Syntax.lcomp_univs);
                    FStar_Syntax_Syntax.lcomp_indices =
                      (uu___131_3076.FStar_Syntax_Syntax.lcomp_indices);
                    FStar_Syntax_Syntax.lcomp_res_typ =
                      (uu___131_3076.FStar_Syntax_Syntax.lcomp_res_typ);
                    FStar_Syntax_Syntax.lcomp_cflags = flags;
                    FStar_Syntax_Syntax.lcomp_as_comp =
                      (uu___131_3076.FStar_Syntax_Syntax.lcomp_as_comp)
                  }  in
                let _0_426 =
                  let uu____3077 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3077
                  then lc
                  else
                    (let uu___132_3079 = lc  in
                     {
                       FStar_Syntax_Syntax.lcomp_name =
                         (uu___132_3079.FStar_Syntax_Syntax.lcomp_name);
                       FStar_Syntax_Syntax.lcomp_univs =
                         (uu___132_3079.FStar_Syntax_Syntax.lcomp_univs);
                       FStar_Syntax_Syntax.lcomp_indices =
                         (uu___132_3079.FStar_Syntax_Syntax.lcomp_indices);
                       FStar_Syntax_Syntax.lcomp_res_typ =
                         (uu___132_3079.FStar_Syntax_Syntax.lcomp_res_typ);
                       FStar_Syntax_Syntax.lcomp_cflags =
                         (uu___132_3079.FStar_Syntax_Syntax.lcomp_cflags);
                       FStar_Syntax_Syntax.lcomp_as_comp = strengthen
                     })
                   in
                (_0_426,
                  (let uu___133_3080 = g0  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___133_3080.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___133_3080.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___133_3080.FStar_TypeChecker_Env.implicits)
                   }))))
  
let add_equality_to_post_condition :
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
            FStar_Syntax_Const.effect_PURE_lid
           in
        let x = FStar_Syntax_Syntax.new_bv None res_t  in
        let y = FStar_Syntax_Syntax.new_bv None res_t  in
        let uu____3095 =
          let _0_428 = FStar_Syntax_Syntax.bv_to_name x  in
          let _0_427 = FStar_Syntax_Syntax.bv_to_name y  in (_0_428, _0_427)
           in
        match uu____3095 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t  in
            let yret =
              (let _0_433 =
                 FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                   md_pure md_pure.FStar_Syntax_Syntax.ret_wp
                  in
               let _0_432 =
                 let _0_431 = FStar_Syntax_Syntax.as_arg res_t  in
                 let _0_430 =
                   let _0_429 = FStar_Syntax_Syntax.as_arg yexp  in [_0_429]
                    in
                 _0_431 :: _0_430  in
               FStar_Syntax_Syntax.mk_Tm_app _0_433 _0_432) None
                res_t.FStar_Syntax_Syntax.pos
               in
            let x_eq_y_yret =
              (let _0_441 =
                 FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                   md_pure md_pure.FStar_Syntax_Syntax.assume_p
                  in
               let _0_440 =
                 let _0_439 = FStar_Syntax_Syntax.as_arg res_t  in
                 let _0_438 =
                   let _0_437 =
                     let _0_434 =
                       FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp  in
                     FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_434
                      in
                   let _0_436 =
                     let _0_435 =
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret
                        in
                     [_0_435]  in
                   _0_437 :: _0_436  in
                 _0_439 :: _0_438  in
               FStar_Syntax_Syntax.mk_Tm_app _0_441 _0_440) None
                res_t.FStar_Syntax_Syntax.pos
               in
            let forall_y_x_eq_y_yret =
              (let _0_451 =
                 FStar_TypeChecker_Env.inst_effect_fun_with
                   [u_res_t; u_res_t] env md_pure
                   md_pure.FStar_Syntax_Syntax.close_wp
                  in
               let _0_450 =
                 let _0_449 = FStar_Syntax_Syntax.as_arg res_t  in
                 let _0_448 =
                   let _0_447 = FStar_Syntax_Syntax.as_arg res_t  in
                   let _0_446 =
                     let _0_445 =
                       let _0_444 =
                         let _0_443 =
                           let _0_442 = FStar_Syntax_Syntax.mk_binder y  in
                           [_0_442]  in
                         FStar_Syntax_Util.abs _0_443 x_eq_y_yret
                           (Some
                              (FStar_Util.Inr
                                 (FStar_Syntax_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL])))
                          in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_444
                        in
                     [_0_445]  in
                   _0_447 :: _0_446  in
                 _0_449 :: _0_448  in
               FStar_Syntax_Syntax.mk_Tm_app _0_451 _0_450) None
                res_t.FStar_Syntax_Syntax.pos
               in
            let lc2 =
              (mk_comp md_pure) [u_res_t] [] res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN]
               in
            let lc =
              let _0_454 = FStar_TypeChecker_Env.lcomp_of_comp env comp  in
              let _0_453 =
                let _0_452 = FStar_TypeChecker_Env.lcomp_of_comp env lc2  in
                ((Some x), _0_452)  in
              bind env None _0_454 _0_453  in
            lc.FStar_Syntax_Syntax.lcomp_as_comp ()
  
let fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun lid  ->
      let _0_456 =
        let _0_455 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid _0_455  in
      FStar_Syntax_Syntax.fvar _0_456 FStar_Syntax_Syntax.Delta_constant None
  
let bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.formula * FStar_Syntax_Syntax.lcomp) Prims.list ->
        FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let uu____3157 =
          let _0_459 =
            let _0_458 =
              let _0_457 = FStar_Syntax_Syntax.mk_Total res_t  in
              FStar_TypeChecker_Env.lcomp_of_comp env _0_457  in
            (_0_458, [])  in
          FStar_List.fold_right
            (fun uu____3170  ->
               fun uu____3171  ->
                 match (uu____3170, uu____3171) with
                 | ((formula,lc),(out,lcases)) ->
                     let uu____3208 = join_lcomp env lc out  in
                     (match uu____3208 with
                      | (lc,_out) -> (lc, ((formula, lc) :: lcases)))) lcases
            _0_459
           in
        match uu____3157 with
        | (lc,lcases) ->
            let bind_cases uu____3241 =
              let if_then_else guard cthen celse =
                let uu____3252 = lift_and_destruct env cthen celse  in
                match uu____3252 with
                | (nct_then,nct_else) ->
                    let md =
                      FStar_TypeChecker_Env.get_effect_decl env
                        nct_then.FStar_TypeChecker_Env.nct_name
                       in
                    let wp =
                      let _0_466 =
                        FStar_Range.union_ranges
                          (Prims.fst nct_then.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                          (Prims.fst nct_else.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                         in
                      (let _0_465 =
                         FStar_TypeChecker_Env.inst_effect_fun_with
                           nct_then.FStar_TypeChecker_Env.nct_univs env md
                           md.FStar_Syntax_Syntax.if_then_else
                          in
                       let _0_464 =
                         let _0_463 =
                           let _0_462 = FStar_Syntax_Syntax.as_arg res_t  in
                           let _0_461 =
                             let _0_460 = FStar_Syntax_Syntax.as_arg guard
                                in
                             [_0_460;
                             nct_then.FStar_TypeChecker_Env.nct_wp;
                             nct_else.FStar_TypeChecker_Env.nct_wp]  in
                           _0_462 :: _0_461  in
                         FStar_List.append
                           nct_then.FStar_TypeChecker_Env.nct_indices _0_463
                          in
                       FStar_Syntax_Syntax.mk_Tm_app _0_465 _0_464) None
                        _0_466
                       in
                    (mk_comp md) nct_then.FStar_TypeChecker_Env.nct_univs
                      nct_then.FStar_TypeChecker_Env.nct_indices res_t wp []
                 in
              let default_case =
                let post_k =
                  let _0_469 =
                    let _0_467 = FStar_Syntax_Syntax.null_binder res_t  in
                    [_0_467]  in
                  let _0_468 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
                  FStar_Syntax_Util.arrow _0_469 _0_468  in
                let kwp =
                  let _0_472 =
                    let _0_470 = FStar_Syntax_Syntax.null_binder post_k  in
                    [_0_470]  in
                  let _0_471 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
                  FStar_Syntax_Util.arrow _0_472 _0_471  in
                let post = FStar_Syntax_Syntax.new_bv None post_k  in
                let wp =
                  let _0_478 =
                    let _0_473 = FStar_Syntax_Syntax.mk_binder post  in
                    [_0_473]  in
                  let _0_477 =
                    let _0_476 =
                      let _0_474 = FStar_TypeChecker_Env.get_range env  in
                      label FStar_TypeChecker_Err.exhaustiveness_check _0_474
                       in
                    let _0_475 = fvar_const env FStar_Syntax_Const.false_lid
                       in
                    FStar_All.pipe_left _0_476 _0_475  in
                  FStar_Syntax_Util.abs _0_478 _0_477
                    (Some
                       (FStar_Util.Inr
                          (FStar_Syntax_Const.effect_Tot_lid,
                            [FStar_Syntax_Syntax.TOTAL])))
                   in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    FStar_Syntax_Const.effect_PURE_lid
                   in
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                (mk_comp md) [u_res_t] [] res_t wp []  in
              let comp =
                FStar_List.fold_right
                  (fun uu____3292  ->
                     fun celse  ->
                       match uu____3292 with
                       | (g,cthen) ->
                           let _0_479 =
                             cthen.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                           if_then_else g _0_479 celse) lcases default_case
                 in
              let uu____3298 =
                let _0_480 = FStar_Options.split_cases ()  in
                _0_480 > (Prims.parse_int "0")  in
              if uu____3298
              then add_equality_to_post_condition env comp res_t
              else
                (let nct =
                   FStar_TypeChecker_Env.comp_as_normal_comp_typ env comp  in
                 let md =
                   FStar_TypeChecker_Env.get_effect_decl env
                     nct.FStar_TypeChecker_Env.nct_name
                    in
                 let share_post_wp =
                   (let _0_481 =
                      FStar_TypeChecker_Env.inst_effect_fun_with
                        nct.FStar_TypeChecker_Env.nct_univs env md
                        md.FStar_Syntax_Syntax.ite_wp
                       in
                    FStar_Syntax_Syntax.mk_Tm_app _0_481
                      (FStar_List.append
                         nct.FStar_TypeChecker_Env.nct_indices
                         [nct.FStar_TypeChecker_Env.nct_result;
                         nct.FStar_TypeChecker_Env.nct_wp])) None
                     (Prims.fst nct.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                    in
                 (mk_comp md) nct.FStar_TypeChecker_Env.nct_univs
                   nct.FStar_TypeChecker_Env.nct_indices
                   (Prims.fst nct.FStar_TypeChecker_Env.nct_result)
                   share_post_wp [])
               in
            let uu____3319 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
            if uu____3319
            then lc
            else
              (let uu___134_3321 = lc  in
               {
                 FStar_Syntax_Syntax.lcomp_name =
                   (uu___134_3321.FStar_Syntax_Syntax.lcomp_name);
                 FStar_Syntax_Syntax.lcomp_univs =
                   (uu___134_3321.FStar_Syntax_Syntax.lcomp_univs);
                 FStar_Syntax_Syntax.lcomp_indices =
                   (uu___134_3321.FStar_Syntax_Syntax.lcomp_indices);
                 FStar_Syntax_Syntax.lcomp_res_typ =
                   (uu___134_3321.FStar_Syntax_Syntax.lcomp_res_typ);
                 FStar_Syntax_Syntax.lcomp_cflags =
                   (uu___134_3321.FStar_Syntax_Syntax.lcomp_cflags);
                 FStar_Syntax_Syntax.lcomp_as_comp = bind_cases
               })
  
let close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        let close uu____3338 =
          let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          let uu____3342 = FStar_Syntax_Util.is_ml_comp c  in
          if uu____3342
          then c
          else
            (let nct = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c
                in
             let md =
               FStar_TypeChecker_Env.get_effect_decl env
                 nct.FStar_TypeChecker_Env.nct_name
                in
             let r =
               (Prims.fst nct.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                in
             let closed_wp =
               FStar_List.fold_right
                 (fun x  ->
                    fun wp  ->
                      let us =
                        let _0_483 =
                          let _0_482 =
                            env.FStar_TypeChecker_Env.universe_of env
                              x.FStar_Syntax_Syntax.sort
                             in
                          [_0_482]  in
                        FStar_List.append nct.FStar_TypeChecker_Env.nct_univs
                          _0_483
                         in
                      let wp =
                        let _0_485 =
                          let _0_484 = FStar_Syntax_Syntax.mk_binder x  in
                          [_0_484]  in
                        FStar_Syntax_Util.abs _0_485 wp
                          (Some
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])))
                         in
                      (let _0_492 =
                         FStar_TypeChecker_Env.inst_effect_fun_with us env md
                           md.FStar_Syntax_Syntax.close_wp
                          in
                       let _0_491 =
                         let _0_490 =
                           let _0_489 =
                             let _0_488 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let _0_487 =
                               let _0_486 = FStar_Syntax_Syntax.as_arg wp  in
                               [_0_486]  in
                             _0_488 :: _0_487  in
                           (nct.FStar_TypeChecker_Env.nct_result) :: _0_489
                            in
                         FStar_List.append
                           nct.FStar_TypeChecker_Env.nct_indices _0_490
                          in
                       FStar_Syntax_Syntax.mk_Tm_app _0_492 _0_491) None r)
                 bvs (Prims.fst nct.FStar_TypeChecker_Env.nct_wp)
                in
             (mk_comp md) nct.FStar_TypeChecker_Env.nct_univs
               nct.FStar_TypeChecker_Env.nct_indices
               (Prims.fst nct.FStar_TypeChecker_Env.nct_result) closed_wp
               nct.FStar_TypeChecker_Env.nct_flags)
           in
        let uu____3380 =
          env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
        if uu____3380
        then lc
        else
          (let uu___135_3382 = lc  in
           {
             FStar_Syntax_Syntax.lcomp_name =
               (uu___135_3382.FStar_Syntax_Syntax.lcomp_name);
             FStar_Syntax_Syntax.lcomp_univs =
               (uu___135_3382.FStar_Syntax_Syntax.lcomp_univs);
             FStar_Syntax_Syntax.lcomp_indices =
               (uu___135_3382.FStar_Syntax_Syntax.lcomp_indices);
             FStar_Syntax_Syntax.lcomp_res_typ =
               (uu___135_3382.FStar_Syntax_Syntax.lcomp_res_typ);
             FStar_Syntax_Syntax.lcomp_cflags =
               (uu___135_3382.FStar_Syntax_Syntax.lcomp_cflags);
             FStar_Syntax_Syntax.lcomp_as_comp = close
           })
  
let maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let refine uu____3397 =
          let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          let uu____3401 =
            (Prims.op_Negation
               (is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.lcomp_name))
              || env.FStar_TypeChecker_Env.lax
             in
          if uu____3401
          then c
          else
            (let uu____3405 = FStar_Syntax_Util.is_partial_return c  in
             if uu____3405
             then c
             else
               (let uu____3409 =
                  (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
                    (Prims.op_Negation
                       (FStar_TypeChecker_Env.lid_exists env
                          FStar_Syntax_Const.effect_GTot_lid))
                   in
                if uu____3409
                then
                  failwith
                    (let _0_494 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let _0_493 = FStar_Syntax_Print.term_to_string e  in
                     FStar_Util.format2 "%s: %s\n" _0_494 _0_493)
                else
                  (let nct =
                     FStar_TypeChecker_Env.comp_as_normal_comp_typ env c  in
                   let t = Prims.fst nct.FStar_TypeChecker_Env.nct_result  in
                   let c =
                     FStar_TypeChecker_Env.normal_comp_typ_as_comp env nct
                      in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (Some (t.FStar_Syntax_Syntax.pos)) t
                      in
                   let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                   let ret =
                     let _0_496 =
                       let _0_495 = return_value env t xexp  in
                       FStar_Syntax_Util.comp_set_flags _0_495
                         [FStar_Syntax_Syntax.PARTIAL_RETURN]
                        in
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.lcomp_of_comp env) _0_496
                      in
                   let eq =
                     let _0_497 = env.FStar_TypeChecker_Env.universe_of env t
                        in
                     FStar_Syntax_Util.mk_eq2 _0_497 t xexp e  in
                   let eq_ret =
                     weaken_precondition env ret
                       (FStar_TypeChecker_Common.NonTrivial eq)
                      in
                   let bind_lc =
                     let _0_498 = FStar_TypeChecker_Env.lcomp_of_comp env c
                        in
                     bind env None _0_498 ((Some x), eq_ret)  in
                   let _0_499 = bind_lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                      in
                   FStar_Syntax_Util.comp_set_flags _0_499
                     (FStar_Syntax_Syntax.PARTIAL_RETURN ::
                     (FStar_Syntax_Util.comp_flags c)))))
           in
        let flags =
          let uu____3431 =
            ((Prims.op_Negation
                (FStar_Syntax_Util.is_function_typ
                   lc.FStar_Syntax_Syntax.lcomp_res_typ))
               && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (Prims.op_Negation
                 (FStar_Syntax_Util.is_lcomp_partial_return lc))
             in
          if uu____3431
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.lcomp_cflags)
          else lc.FStar_Syntax_Syntax.lcomp_cflags  in
        let uu___136_3434 = lc  in
        {
          FStar_Syntax_Syntax.lcomp_name =
            (uu___136_3434.FStar_Syntax_Syntax.lcomp_name);
          FStar_Syntax_Syntax.lcomp_univs =
            (uu___136_3434.FStar_Syntax_Syntax.lcomp_univs);
          FStar_Syntax_Syntax.lcomp_indices =
            (uu___136_3434.FStar_Syntax_Syntax.lcomp_indices);
          FStar_Syntax_Syntax.lcomp_res_typ =
            (uu___136_3434.FStar_Syntax_Syntax.lcomp_res_typ);
          FStar_Syntax_Syntax.lcomp_cflags = flags;
          FStar_Syntax_Syntax.lcomp_as_comp = refine
        }
  
let check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____3453 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____3453 with
          | None  ->
              Prims.raise
                (FStar_Errors.Error
                   (let _0_501 =
                      FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                        env e c c'
                       in
                    let _0_500 = FStar_TypeChecker_Env.get_range env  in
                    (_0_501, _0_500)))
          | Some g -> (e, c', g)
  
let maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let uu____3478 =
            (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
          match uu____3478 with
          | FStar_Syntax_Syntax.Tm_type uu____3481 ->
              let uu____3482 =
                (FStar_Syntax_Subst.compress
                   lc.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n
                 in
              (match uu____3482 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.bool_lid
                   ->
                   let uu____3486 =
                     FStar_TypeChecker_Env.lookup_lid env
                       FStar_Syntax_Const.b2t_lid
                      in
                   let b2t =
                     FStar_Syntax_Syntax.fvar
                       (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                          e.FStar_Syntax_Syntax.pos)
                       (FStar_Syntax_Syntax.Delta_defined_at_level
                          (Prims.parse_int "1")) None
                      in
                   let lc =
                     let _0_504 =
                       let _0_503 =
                         let _0_502 =
                           FStar_Syntax_Syntax.mk_Total
                             FStar_Syntax_Util.ktype0
                            in
                         FStar_TypeChecker_Env.lcomp_of_comp env _0_502  in
                       (None, _0_503)  in
                     bind env (Some e) lc _0_504  in
                   let e =
                     (let _0_506 =
                        let _0_505 = FStar_Syntax_Syntax.as_arg e  in
                        [_0_505]  in
                      FStar_Syntax_Syntax.mk_Tm_app b2t _0_506)
                       (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                       e.FStar_Syntax_Syntax.pos
                      in
                   (e, lc)
               | uu____3501 -> (e, lc))
          | uu____3502 -> (e, lc)
  
let weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let gopt =
            if env.FStar_TypeChecker_Env.use_eq
            then
              let _0_507 =
                FStar_TypeChecker_Rel.try_teq env
                  lc.FStar_Syntax_Syntax.lcomp_res_typ t
                 in
              (_0_507, false)
            else
              (let _0_508 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.lcomp_res_typ t
                  in
               (_0_508, true))
             in
          match gopt with
          | (None ,uu____3534) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.lcomp_res_typ t;
               (e,
                 ((let uu___137_3537 = lc  in
                   {
                     FStar_Syntax_Syntax.lcomp_name =
                       (uu___137_3537.FStar_Syntax_Syntax.lcomp_name);
                     FStar_Syntax_Syntax.lcomp_univs =
                       (uu___137_3537.FStar_Syntax_Syntax.lcomp_univs);
                     FStar_Syntax_Syntax.lcomp_indices =
                       (uu___137_3537.FStar_Syntax_Syntax.lcomp_indices);
                     FStar_Syntax_Syntax.lcomp_res_typ = t;
                     FStar_Syntax_Syntax.lcomp_cflags =
                       (uu___137_3537.FStar_Syntax_Syntax.lcomp_cflags);
                     FStar_Syntax_Syntax.lcomp_as_comp =
                       (uu___137_3537.FStar_Syntax_Syntax.lcomp_as_comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard) ->
              let uu____3541 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____3541 with
               | FStar_TypeChecker_Common.Trivial  ->
                   (e,
                     (let uu___138_3545 = lc  in
                      {
                        FStar_Syntax_Syntax.lcomp_name =
                          (uu___138_3545.FStar_Syntax_Syntax.lcomp_name);
                        FStar_Syntax_Syntax.lcomp_univs =
                          (uu___138_3545.FStar_Syntax_Syntax.lcomp_univs);
                        FStar_Syntax_Syntax.lcomp_indices =
                          (uu___138_3545.FStar_Syntax_Syntax.lcomp_indices);
                        FStar_Syntax_Syntax.lcomp_res_typ = t;
                        FStar_Syntax_Syntax.lcomp_cflags =
                          (uu___138_3545.FStar_Syntax_Syntax.lcomp_cflags);
                        FStar_Syntax_Syntax.lcomp_as_comp =
                          (uu___138_3545.FStar_Syntax_Syntax.lcomp_as_comp)
                      }), g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g =
                     let uu___139_3548 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___139_3548.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___139_3548.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___139_3548.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____3554 =
                     let uu____3555 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____3555
                     then lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                     else
                       (let f =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f
                           in
                        let uu____3560 =
                          (FStar_Syntax_Subst.compress f).FStar_Syntax_Syntax.n
                           in
                        match uu____3560 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____3563,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____3565;
                                          FStar_Syntax_Syntax.pos =
                                            uu____3566;
                                          FStar_Syntax_Syntax.vars =
                                            uu____3567;_},uu____3568)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc =
                              let uu___140_3592 = lc  in
                              {
                                FStar_Syntax_Syntax.lcomp_name =
                                  (uu___140_3592.FStar_Syntax_Syntax.lcomp_name);
                                FStar_Syntax_Syntax.lcomp_univs =
                                  (uu___140_3592.FStar_Syntax_Syntax.lcomp_univs);
                                FStar_Syntax_Syntax.lcomp_indices =
                                  (uu___140_3592.FStar_Syntax_Syntax.lcomp_indices);
                                FStar_Syntax_Syntax.lcomp_res_typ = t;
                                FStar_Syntax_Syntax.lcomp_cflags =
                                  (uu___140_3592.FStar_Syntax_Syntax.lcomp_cflags);
                                FStar_Syntax_Syntax.lcomp_as_comp =
                                  (uu___140_3592.FStar_Syntax_Syntax.lcomp_as_comp)
                              }  in
                            lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                        | uu____3593 ->
                            let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                               in
                            ((let uu____3598 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____3598
                              then
                                let _0_512 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.lcomp_res_typ
                                   in
                                let _0_511 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let _0_510 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let _0_509 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  _0_512 _0_511 _0_510 _0_509
                              else ());
                             (let nct =
                                FStar_TypeChecker_Env.comp_as_normal_comp_typ
                                  env c
                                 in
                              let md =
                                FStar_TypeChecker_Env.get_effect_decl env
                                  nct.FStar_TypeChecker_Env.nct_name
                                 in
                              let x =
                                FStar_Syntax_Syntax.new_bv
                                  (Some (t.FStar_Syntax_Syntax.pos)) t
                                 in
                              let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                              let wp =
                                (let _0_518 =
                                   FStar_TypeChecker_Env.inst_effect_fun_with
                                     nct.FStar_TypeChecker_Env.nct_univs env
                                     md md.FStar_Syntax_Syntax.ret_wp
                                    in
                                 let _0_517 =
                                   let _0_516 =
                                     let _0_515 =
                                       FStar_Syntax_Syntax.as_arg t  in
                                     let _0_514 =
                                       let _0_513 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [_0_513]  in
                                     _0_515 :: _0_514  in
                                   FStar_List.append
                                     nct.FStar_TypeChecker_Env.nct_indices
                                     _0_516
                                    in
                                 FStar_Syntax_Syntax.mk_Tm_app _0_518 _0_517)
                                  None xexp.FStar_Syntax_Syntax.pos
                                 in
                              let cret =
                                let _0_519 =
                                  (mk_comp md)
                                    nct.FStar_TypeChecker_Env.nct_univs
                                    nct.FStar_TypeChecker_Env.nct_indices t
                                    wp [FStar_Syntax_Syntax.RETURN]
                                   in
                                FStar_TypeChecker_Env.lcomp_of_comp env
                                  _0_519
                                 in
                              let guard =
                                if apply_guard
                                then
                                  (let _0_521 =
                                     let _0_520 =
                                       FStar_Syntax_Syntax.as_arg xexp  in
                                     [_0_520]  in
                                   FStar_Syntax_Syntax.mk_Tm_app f _0_521)
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    f.FStar_Syntax_Syntax.pos
                                else f  in
                              let uu____3626 =
                                let _0_525 =
                                  FStar_All.pipe_left
                                    (fun _0_522  -> Some _0_522)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env
                                       lc.FStar_Syntax_Syntax.lcomp_res_typ t)
                                   in
                                let _0_524 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let _0_523 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition _0_525 _0_524 e cret
                                  _0_523
                                 in
                              match uu____3626 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x =
                                    let uu___141_3641 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___141_3641.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___141_3641.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.lcomp_res_typ)
                                    }  in
                                  let c =
                                    let _0_527 =
                                      let _0_526 =
                                        FStar_TypeChecker_Env.normal_comp_typ_as_comp
                                          env nct
                                         in
                                      FStar_TypeChecker_Env.lcomp_of_comp env
                                        _0_526
                                       in
                                    bind env (Some e) _0_527
                                      ((Some x), eq_ret)
                                     in
                                  let c =
                                    c.FStar_Syntax_Syntax.lcomp_as_comp ()
                                     in
                                  ((let uu____3648 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____3648
                                    then
                                      let _0_528 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" _0_528
                                    else ());
                                   c))))
                      in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.lcomp_cflags
                       (FStar_List.collect
                          (fun uu___94_3654  ->
                             match uu___94_3654 with
                             | FStar_Syntax_Syntax.RETURN 
                               |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____3656 -> []))
                      in
                   let lc =
                     let uu___142_3658 = lc  in
                     {
                       FStar_Syntax_Syntax.lcomp_name =
                         (uu___142_3658.FStar_Syntax_Syntax.lcomp_name);
                       FStar_Syntax_Syntax.lcomp_univs =
                         (uu___142_3658.FStar_Syntax_Syntax.lcomp_univs);
                       FStar_Syntax_Syntax.lcomp_indices =
                         (uu___142_3658.FStar_Syntax_Syntax.lcomp_indices);
                       FStar_Syntax_Syntax.lcomp_res_typ = t;
                       FStar_Syntax_Syntax.lcomp_cflags = flags;
                       FStar_Syntax_Syntax.lcomp_as_comp = strengthen
                     }  in
                   let g =
                     let uu___143_3660 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___143_3660.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___143_3660.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___143_3660.FStar_TypeChecker_Env.implicits)
                     }  in
                   (e, lc, g))
  
let pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv None res_t  in
        let _0_531 =
          (let _0_530 =
             let _0_529 =
               FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name x)
                in
             [_0_529]  in
           FStar_Syntax_Syntax.mk_Tm_app ens _0_530) None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x _0_531  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____3690 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____3690
      then
        let _0_532 = FStar_TypeChecker_Env.result_typ env comp  in
        (None, _0_532)
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal _|FStar_Syntax_Syntax.Total _ ->
             failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (res,uu____3712)::(req,uu____3714)::(ens,uu____3716)::uu____3717
                    ->
                    let _0_535 = Some (norm req)  in
                    let _0_534 =
                      let _0_533 = mk_post_type res ens  in
                      FStar_All.pipe_left norm _0_533  in
                    (_0_535, _0_534)
                | uu____3748 ->
                    Prims.raise
                      (FStar_Errors.Error
                         (let _0_537 =
                            let _0_536 =
                              FStar_Syntax_Print.comp_to_string comp  in
                            FStar_Util.format1
                              "Effect constructor is not fully applied; got %s"
                              _0_536
                             in
                          (_0_537, (comp.FStar_Syntax_Syntax.pos)))))
             else
               (let nct =
                  FStar_TypeChecker_Env.comp_as_normal_comp_typ env comp  in
                let res_t = Prims.fst nct.FStar_TypeChecker_Env.nct_result
                   in
                let wp = Prims.fst nct.FStar_TypeChecker_Env.nct_wp  in
                let uu____3769 =
                  FStar_TypeChecker_Env.lookup_lid env
                    FStar_Syntax_Const.as_requires
                   in
                match uu____3769 with
                | (us_r,uu____3776) ->
                    let uu____3777 =
                      FStar_TypeChecker_Env.lookup_lid env
                        FStar_Syntax_Const.as_ensures
                       in
                    (match uu____3777 with
                     | (us_e,uu____3784) ->
                         let r = res_t.FStar_Syntax_Syntax.pos  in
                         let as_req =
                           let _0_538 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Syntax_Const.as_requires r)
                               FStar_Syntax_Syntax.Delta_equational None
                              in
                           FStar_Syntax_Syntax.mk_Tm_uinst _0_538 us_r  in
                         let as_ens =
                           let _0_539 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Syntax_Const.as_ensures r)
                               FStar_Syntax_Syntax.Delta_equational None
                              in
                           FStar_Syntax_Syntax.mk_Tm_uinst _0_539 us_e  in
                         let req =
                           (let _0_542 =
                              let _0_541 =
                                let _0_540 = FStar_Syntax_Syntax.as_arg wp
                                   in
                                [_0_540]  in
                              (res_t, (Some FStar_Syntax_Syntax.imp_tag)) ::
                                _0_541
                               in
                            FStar_Syntax_Syntax.mk_Tm_app as_req _0_542)
                             (Some
                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                             r
                            in
                         let ens =
                           (let _0_545 =
                              let _0_544 =
                                let _0_543 = FStar_Syntax_Syntax.as_arg wp
                                   in
                                [_0_543]  in
                              (res_t, (Some FStar_Syntax_Syntax.imp_tag)) ::
                                _0_544
                               in
                            FStar_Syntax_Syntax.mk_Tm_app as_ens _0_545) None
                             r
                            in
                         let _0_547 = Some (norm req)  in
                         let _0_546 = norm (mk_post_type res_t ens)  in
                         (_0_547, _0_546))))
  
let maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
          FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.subst_t)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Rel.trivial_guard, [])
        else
          (let number_of_implicits t =
             let uu____3847 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____3847 with
             | (formals,uu____3854) ->
                 let n_implicits =
                   let uu____3862 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____3899  ->
                             match uu____3899 with
                             | (uu____3903,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____3862 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t =
             let uu____3975 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____3975 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t  in
                 if n_available < n_expected
                 then
                   Prims.raise
                     (FStar_Errors.Error
                        (let _0_552 =
                           let _0_550 = FStar_Util.string_of_int n_expected
                              in
                           let _0_549 = FStar_Syntax_Print.term_to_string e
                              in
                           let _0_548 = FStar_Util.string_of_int n_available
                              in
                           FStar_Util.format3
                             "Expected a term with %s implicit arguments, but %s has only %s"
                             _0_550 _0_549 _0_548
                            in
                         let _0_551 = FStar_TypeChecker_Env.get_range env  in
                         (_0_552, _0_551)))
                 else Some (n_available - n_expected)
              in
           let decr_inst uu___95_4007 =
             match uu___95_4007 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1"))  in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4027 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____4027 with
                | (bs,c) ->
                    let rec aux subst inst_n bs =
                      match (inst_n, bs) with
                      | (Some _0_553,uu____4089) when
                          _0_553 = (Prims.parse_int "0") ->
                          ([], bs, subst,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____4111,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____4130 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t
                             in
                          (match uu____4130 with
                           | (v,uu____4151,g) ->
                               let subst = (FStar_Syntax_Syntax.NT (x, v)) ::
                                 subst  in
                               let uu____4161 =
                                 aux subst (decr_inst inst_n) rest  in
                               (match uu____4161 with
                                | (args,bs,subst,g') ->
                                    let _0_554 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs, subst, _0_554)))
                      | (uu____4223,bs) ->
                          ([], bs, subst,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____4247 =
                      let _0_555 = inst_n_binders t  in aux [] _0_555 bs  in
                    (match uu____4247 with
                     | (args,bs,subst,guard) ->
                         (match (args, bs) with
                          | ([],uu____4299) -> (e, torig, guard, [])
                          | (uu____4316,[]) when
                              Prims.op_Negation
                                (FStar_Syntax_Util.is_total_comp c)
                              ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard,
                                [])
                          | uu____4333 ->
                              let t =
                                match bs with
                                | [] ->
                                    FStar_TypeChecker_Env.result_typ env c
                                | uu____4348 -> FStar_Syntax_Util.arrow bs c
                                 in
                              let t = FStar_Syntax_Subst.subst subst t  in
                              let e =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e, t, guard, subst))))
           | uu____4364 -> (e, t, FStar_TypeChecker_Rel.trivial_guard, []))
  
let string_of_univs univs =
  let _0_558 =
    let _0_557 = FStar_Util.set_elements univs  in
    FStar_All.pipe_right _0_557
      (FStar_List.map
         (fun u  ->
            let _0_556 = FStar_Unionfind.uvar_id u  in
            FStar_All.pipe_right _0_556 FStar_Util.string_of_int))
     in
  FStar_All.pipe_right _0_558 (FStar_String.concat ", ") 
let gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____4395 = FStar_Util.set_is_empty x  in
      if uu____4395
      then []
      else
        (let s =
           let _0_560 =
             let _0_559 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x _0_559  in
           FStar_All.pipe_right _0_560 FStar_Util.set_elements  in
         (let uu____4403 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____4403
          then
            let _0_561 =
              string_of_univs (FStar_TypeChecker_Env.univ_vars env)  in
            FStar_Util.print1 "univ_vars in env: %s\n" _0_561
          else ());
         (let r = Some (FStar_TypeChecker_Env.get_range env)  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____4419 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____4419
                     then
                       let _0_565 =
                         let _0_562 = FStar_Unionfind.uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int _0_562
                          in
                       let _0_564 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let _0_563 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n" _0_565
                         _0_564 _0_563
                     else ());
                    FStar_Unionfind.change u
                      (Some (FStar_Syntax_Syntax.U_name u_name));
                    u_name))
             in
          u_names))
  
let gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env  in
      let tm_univnames = FStar_Syntax_Free.univnames t  in
      let univnames =
        let _0_566 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right _0_566 FStar_Util.fifo_set_elements  in
      univnames
  
let maybe_set_tk ts uu___96_4462 =
  match uu___96_4462 with
  | None  -> ts
  | Some t ->
      let t = FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange  in
      let t = FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t  in
      (FStar_ST.write (Prims.snd ts).FStar_Syntax_Syntax.tk
         (Some (t.FStar_Syntax_Syntax.n));
       ts)
  
let check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____4503) -> generalized_univ_names
        | (uu____4507,[]) -> explicit_univ_names
        | uu____4511 ->
            Prims.raise
              (FStar_Errors.Error
                 (let _0_568 =
                    let _0_567 = FStar_Syntax_Print.term_to_string t  in
                    Prims.strcat
                      "Generalized universe in a term containing explicit universe annotation : "
                      _0_567
                     in
                  (_0_568, (t.FStar_Syntax_Syntax.pos))))
  
let generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta] env t0
         in
      let univnames = gather_free_univnames env t  in
      let univs = FStar_Syntax_Free.univs t  in
      (let uu____4529 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____4529
       then
         let _0_569 = string_of_univs univs  in
         FStar_Util.print1 "univs to gen : %s\n" _0_569
       else ());
      (let gen = gen_univs env univs  in
       (let uu____4535 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____4535
        then
          let _0_570 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.print1 "After generalization: %s\n" _0_570
        else ());
       (let univs = check_universe_generalization univnames gen t0  in
        let ts = FStar_Syntax_Subst.close_univ_vars univs t  in
        let _0_571 = FStar_ST.read t0.FStar_Syntax_Syntax.tk  in
        maybe_set_tk (univs, ts) _0_571))
  
let gen :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list Prims.option
  =
  fun env  ->
    fun ecs  ->
      let uu____4568 =
        let _0_572 =
          FStar_Util.for_all
            (fun uu____4573  ->
               match uu____4573 with
               | (uu____4578,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs
           in
        FStar_All.pipe_left Prims.op_Negation _0_572  in
      if uu____4568
      then None
      else
        (let norm c =
           (let uu____4601 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
            if uu____4601
            then
              let _0_573 = FStar_Syntax_Print.comp_to_string c  in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                _0_573
            else ());
           (let c =
              let uu____4604 = FStar_TypeChecker_Env.should_verify env  in
              if uu____4604
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
               in
            (let uu____4607 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____4607
             then
               let _0_574 = FStar_Syntax_Print.comp_to_string c  in
               FStar_Util.print1 "Normalized to:\n\t %s\n" _0_574
             else ());
            c)
            in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
         let gen_uvars uvs =
           let _0_575 = FStar_Util.set_difference uvs env_uvars  in
           FStar_All.pipe_right _0_575 FStar_Util.set_elements  in
         let uu____4675 =
           let _0_577 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____4762  ->
                     match uu____4762 with
                     | (e,c) ->
                         let c = norm c  in
                         let t =
                           let _0_576 =
                             FStar_TypeChecker_Env.result_typ env c  in
                           FStar_All.pipe_right _0_576
                             FStar_Syntax_Subst.compress
                            in
                         let univs = FStar_Syntax_Free.univs t  in
                         let uvt = FStar_Syntax_Free.uvars t  in
                         let uvs = gen_uvars uvt  in (univs, (uvs, e, c))))
              in
           FStar_All.pipe_right _0_577 FStar_List.unzip  in
         match uu____4675 with
         | (univs,uvars) ->
             let univs =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs
                in
             let gen_univs = gen_univs env univs  in
             ((let uu____4880 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____4880
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
                      (fun uu____4922  ->
                         match uu____4922 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____4979  ->
                                       match uu____4979 with
                                       | (u,k) ->
                                           let uu____4999 =
                                             FStar_Unionfind.find u  in
                                           (match uu____4999 with
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
                                                uu____5037 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____5045 ->
                                                let k =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k
                                                   in
                                                let uu____5050 =
                                                  FStar_Syntax_Util.arrow_formals_comp
                                                    k
                                                   in
                                                (match uu____5050 with
                                                 | (bs,cres) ->
                                                     let kres =
                                                       FStar_TypeChecker_Env.result_typ
                                                         env cres
                                                        in
                                                     let a =
                                                       let _0_580 =
                                                         let _0_579 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env
                                                            in
                                                         FStar_All.pipe_left
                                                           (fun _0_578  ->
                                                              Some _0_578)
                                                           _0_579
                                                          in
                                                       FStar_Syntax_Syntax.new_bv
                                                         _0_580 kres
                                                        in
                                                     let t =
                                                       let _0_583 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a
                                                          in
                                                       let _0_582 =
                                                         Some
                                                           (FStar_Util.Inl
                                                              (let _0_581 =
                                                                 FStar_Syntax_Syntax.mk_Total
                                                                   kres
                                                                  in
                                                               FStar_TypeChecker_Env.lcomp_of_comp
                                                                 env _0_581))
                                                          in
                                                       FStar_Syntax_Util.abs
                                                         bs _0_583 _0_582
                                                        in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag)))))))
                                in
                             let uu____5083 =
                               match (tvars, gen_univs) with
                               | ([],[]) -> (e, c)
                               | ([],uu____5101) ->
                                   let c =
                                     FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm]
                                       env c
                                      in
                                   let e =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm]
                                       env e
                                      in
                                   (e, c)
                               | uu____5113 ->
                                   let uu____5121 = (e, c)  in
                                   (match uu____5121 with
                                    | (e0,c0) ->
                                        let c =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm]
                                            env c
                                           in
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
                                            env e
                                           in
                                        let t =
                                          let uu____5131 =
                                            (FStar_Syntax_Subst.compress
                                               (FStar_TypeChecker_Env.result_typ
                                                  env c)).FStar_Syntax_Syntax.n
                                             in
                                          match uu____5131 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____5144 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____5144 with
                                               | (bs,cod) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs) cod)
                                          | uu____5152 ->
                                              FStar_Syntax_Util.arrow tvars c
                                           in
                                        let e' =
                                          let _0_584 =
                                            Some
                                              (FStar_Util.Inl
                                                 (FStar_TypeChecker_Env.lcomp_of_comp
                                                    env c))
                                             in
                                          FStar_Syntax_Util.abs tvars e
                                            _0_584
                                           in
                                        let _0_585 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', _0_585))
                                in
                             (match uu____5083 with
                              | (e,c) -> (gen_univs, e, c))))
                  in
               Some ecs)))
  
let generalize :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_name Prims.list
        * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list
  =
  fun env  ->
    fun lecs  ->
      (let uu____5199 = FStar_TypeChecker_Env.debug env FStar_Options.Low  in
       if uu____5199
       then
         let _0_587 =
           let _0_586 =
             FStar_List.map
               (fun uu____5204  ->
                  match uu____5204 with
                  | (lb,uu____5209,uu____5210) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs
              in
           FStar_All.pipe_right _0_586 (FStar_String.concat ", ")  in
         FStar_Util.print1 "Generalizing: %s\n" _0_587
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____5219  ->
              match uu____5219 with | (l,t,c) -> gather_free_univnames env t)
           lecs
          in
       let generalized_lecs =
         let uu____5234 =
           let _0_588 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____5253  ->
                     match uu____5253 with | (uu____5259,e,c) -> (e, c)))
              in
           gen env _0_588  in
         match uu____5234 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____5291  ->
                     match uu____5291 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____5331  ->
                  fun uu____5332  ->
                    match (uu____5331, uu____5332) with
                    | ((l,uu____5359,uu____5360),(us,e,c)) ->
                        ((let uu____5380 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium
                             in
                          if uu____5380
                          then
                            let _0_592 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos
                               in
                            let _0_591 =
                              FStar_Syntax_Print.lbname_to_string l  in
                            let _0_590 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_TypeChecker_Env.result_typ env c)
                               in
                            let _0_589 = FStar_Syntax_Print.term_to_string e
                               in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n" _0_592
                              _0_591 _0_590 _0_589
                          else ());
                         (l, us, e, c))) lecs ecs
          in
       FStar_List.map2
         (fun univnames  ->
            fun uu____5397  ->
              match uu____5397 with
              | (l,generalized_univs,t,c) ->
                  let _0_593 =
                    check_universe_generalization univnames generalized_univs
                      t
                     in
                  (l, _0_593, t, c)) univnames_lecs generalized_lecs)
  
let check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let env =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check env t1 t2 =
            if env.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq env t1 t2
            else
              (let uu____5446 = FStar_TypeChecker_Rel.try_subtype env t1 t2
                  in
               match uu____5446 with
               | None  -> None
               | Some f ->
                   let _0_595 = FStar_TypeChecker_Rel.apply_guard f e  in
                   FStar_All.pipe_left (fun _0_594  -> Some _0_594) _0_595)
             in
          let is_var e =
            let uu____5455 =
              (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n  in
            match uu____5455 with
            | FStar_Syntax_Syntax.Tm_name uu____5456 -> true
            | uu____5457 -> false  in
          let decorate e t =
            let e = FStar_Syntax_Subst.compress e  in
            match e.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_name
                      (let uu___144_5479 = x  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___144_5479.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___144_5479.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t2
                       }))) (Some (t2.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos
            | uu____5480 ->
                let uu___145_5481 = e  in
                let _0_596 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n))  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___145_5481.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = _0_596;
                  FStar_Syntax_Syntax.pos =
                    (uu___145_5481.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___145_5481.FStar_Syntax_Syntax.vars)
                }
             in
          let env =
            let uu___146_5488 = env  in
            let _0_597 =
              env.FStar_TypeChecker_Env.use_eq ||
                (env.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_5488.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_5488.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_5488.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_5488.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_5488.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_5488.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_5488.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_5488.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_5488.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_5488.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_5488.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_5488.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_5488.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___146_5488.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_5488.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = _0_597;
              FStar_TypeChecker_Env.is_iface =
                (uu___146_5488.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_5488.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_5488.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_5488.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___146_5488.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_5488.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_5488.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___146_5488.FStar_TypeChecker_Env.qname_and_index)
            }  in
          let uu____5489 = check env t1 t2  in
          match uu____5489 with
          | None  ->
              Prims.raise
                (FStar_Errors.Error
                   (let _0_599 =
                      FStar_TypeChecker_Err.expected_expression_of_type env
                        t2 e t1
                       in
                    let _0_598 = FStar_TypeChecker_Env.get_range env  in
                    (_0_599, _0_598)))
          | Some g ->
              ((let uu____5497 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5497
                then
                  let _0_600 = FStar_TypeChecker_Rel.guard_to_string env g
                     in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") _0_600
                else ());
               (let _0_601 = decorate e t2  in (_0_601, g)))
  
let check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        let discharge g =
          FStar_TypeChecker_Rel.force_trivial_guard env g;
          FStar_Syntax_Util.is_pure_lcomp lc  in
        let g = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
        let uu____5520 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____5520
        then
          let _0_603 = discharge g  in
          let _0_602 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          (_0_603, _0_602)
        else
          (let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
           let steps = [FStar_TypeChecker_Normalize.Beta]  in
           let c =
             let _0_606 =
               let _0_605 =
                 let _0_604 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right _0_604 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right _0_605
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right _0_606
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let nct =
             let _0_607 = FStar_Syntax_Syntax.mk_Comp c  in
             FStar_TypeChecker_Env.comp_as_normal_comp_typ env _0_607  in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               nct.FStar_TypeChecker_Env.nct_name
              in
           let vc =
             let _0_609 = FStar_TypeChecker_Env.get_range env  in
             (let _0_608 =
                FStar_TypeChecker_Env.inst_effect_fun_with
                  nct.FStar_TypeChecker_Env.nct_univs env md
                  md.FStar_Syntax_Syntax.trivial
                 in
              FStar_Syntax_Syntax.mk_Tm_app _0_608
                (FStar_List.append nct.FStar_TypeChecker_Env.nct_indices
                   [nct.FStar_TypeChecker_Env.nct_result;
                   nct.FStar_TypeChecker_Env.nct_wp]))
               (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _0_609
              in
           (let uu____5546 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____5546
            then
              let _0_610 = FStar_Syntax_Print.term_to_string vc  in
              FStar_Util.print1 "top-level VC: %s\n" _0_610
            else ());
           (let g =
              let _0_611 =
                FStar_All.pipe_left
                  FStar_TypeChecker_Rel.guard_of_guard_formula
                  (FStar_TypeChecker_Common.NonTrivial vc)
                 in
              FStar_TypeChecker_Rel.conj_guard g _0_611  in
            let _0_613 = discharge g  in
            let _0_612 = FStar_Syntax_Syntax.mk_Comp c  in (_0_613, _0_612)))
  
let short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___97_5572 =
        match uu___97_5572 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____5578)::[] -> f fst
        | uu____5591 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let _0_615 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right _0_615
          (fun _0_614  -> FStar_TypeChecker_Common.NonTrivial _0_614)
         in
      let op_or_e e =
        let _0_617 = FStar_Syntax_Util.mk_neg (FStar_Syntax_Util.b2t e)  in
        FStar_All.pipe_right _0_617
          (fun _0_616  -> FStar_TypeChecker_Common.NonTrivial _0_616)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_618  -> FStar_TypeChecker_Common.NonTrivial _0_618)
         in
      let op_or_t t =
        let _0_620 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right _0_620
          (fun _0_619  -> FStar_TypeChecker_Common.NonTrivial _0_619)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_621  -> FStar_TypeChecker_Common.NonTrivial _0_621)
         in
      let short_op_ite uu___98_5623 =
        match uu___98_5623 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____5629)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____5644)::[] ->
            let _0_623 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right _0_623
              (fun _0_622  -> FStar_TypeChecker_Common.NonTrivial _0_622)
        | uu____5667 -> failwith "Unexpected args to ITE"  in
      let table =
        let _0_637 =
          let _0_624 = short_bin_op op_and_e  in
          (FStar_Syntax_Const.op_And, _0_624)  in
        let _0_636 =
          let _0_635 =
            let _0_625 = short_bin_op op_or_e  in
            (FStar_Syntax_Const.op_Or, _0_625)  in
          let _0_634 =
            let _0_633 =
              let _0_626 = short_bin_op op_and_t  in
              (FStar_Syntax_Const.and_lid, _0_626)  in
            let _0_632 =
              let _0_631 =
                let _0_627 = short_bin_op op_or_t  in
                (FStar_Syntax_Const.or_lid, _0_627)  in
              let _0_630 =
                let _0_629 =
                  let _0_628 = short_bin_op op_imp_t  in
                  (FStar_Syntax_Const.imp_lid, _0_628)  in
                [_0_629; (FStar_Syntax_Const.ite_lid, short_op_ite)]  in
              _0_631 :: _0_630  in
            _0_633 :: _0_632  in
          _0_635 :: _0_634  in
        _0_637 :: _0_636  in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____5720 =
            FStar_Util.find_map table
              (fun uu____5726  ->
                 match uu____5726 with
                 | (x,mk) ->
                     if FStar_Ident.lid_equals x lid
                     then Some (mk seen_args)
                     else None)
             in
          (match uu____5720 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____5741 -> FStar_TypeChecker_Common.Trivial
  
let short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____5745 = (FStar_Syntax_Util.un_uinst l).FStar_Syntax_Syntax.n  in
    match uu____5745 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____5747 -> false
  
let maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs =
        match bs with
        | (hd,uu____5765)::uu____5766 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____5772 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____5776,Some (FStar_Syntax_Syntax.Implicit uu____5777))::uu____5778
          -> bs
      | uu____5787 ->
          let uu____5788 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____5788 with
           | None  -> bs
           | Some t ->
               let uu____5791 =
                 (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
               (match uu____5791 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____5793) ->
                    let uu____5804 =
                      FStar_Util.prefix_until
                        (fun uu___99_5823  ->
                           match uu___99_5823 with
                           | (uu____5827,Some (FStar_Syntax_Syntax.Implicit
                              uu____5828)) -> false
                           | uu____5830 -> true) bs'
                       in
                    (match uu____5804 with
                     | None  -> bs
                     | Some ([],uu____5848,uu____5849) -> bs
                     | Some (imps,uu____5886,uu____5887) ->
                         let uu____5924 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____5932  ->
                                   match uu____5932 with
                                   | (x,uu____5937) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____5924
                         then
                           let r = pos bs  in
                           let imps =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____5960  ->
                                     match uu____5960 with
                                     | (x,i) ->
                                         let _0_638 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (_0_638, i)))
                              in
                           FStar_List.append imps bs
                         else bs)
                | uu____5976 -> bs))
  
let maybe_lift :
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
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1  in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2  in
            if
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
            then e
            else
              (let _0_639 = FStar_ST.read e.FStar_Syntax_Syntax.tk  in
               (FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_meta
                     (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)))))
                 _0_639 e.FStar_Syntax_Syntax.pos)
  
let maybe_monadic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c  in
          let uu____6019 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)
             in
          if uu____6019
          then e
          else
            (let _0_640 = FStar_ST.read e.FStar_Syntax_Syntax.tk  in
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))) _0_640
               e.FStar_Syntax_Syntax.pos)
  
let effect_repr_aux only_reifiable env c =
  let uu____6056 =
    let _0_641 =
      FStar_TypeChecker_Env.norm_eff_name env
        (FStar_Syntax_Util.comp_effect_name c)
       in
    FStar_TypeChecker_Env.effect_decl_opt env _0_641  in
  match uu____6056 with
  | None  -> None
  | Some ed ->
      let uu____6064 =
        only_reifiable &&
          (Prims.op_Negation
             (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)))
         in
      if uu____6064
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____6077 ->
             let nct = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c
                in
             let repr =
               FStar_TypeChecker_Env.inst_effect_fun_with
                 nct.FStar_TypeChecker_Env.nct_univs env ed
                 ([], (ed.FStar_Syntax_Syntax.repr))
                in
             Some
               (let _0_642 = FStar_TypeChecker_Env.get_range env  in
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_app
                     (repr,
                       (FStar_List.append
                          nct.FStar_TypeChecker_Env.nct_indices
                          [nct.FStar_TypeChecker_Env.nct_result;
                          nct.FStar_TypeChecker_Env.nct_wp]))) None _0_642))
  
let effect_repr :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  = fun env  -> fun c  -> effect_repr_aux false env c 
let reify_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun lc  ->
      let uu____6114 =
        let _0_643 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
        effect_repr_aux true env _0_643  in
      match uu____6114 with
      | None  ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_645 =
                  FStar_Util.format1 "Effect %s cannot be reified"
                    (lc.FStar_Syntax_Syntax.lcomp_name).FStar_Ident.str
                   in
                let _0_644 = FStar_TypeChecker_Env.get_range env  in
                (_0_645, _0_644)))
      | Some tm -> tm
  
let d : Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s 
let mk_toplevel_definition :
  FStar_TypeChecker_Env.env_t ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt *
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____6142 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____6142
         then
           (d (FStar_Ident.text_of_lid lident);
            (let _0_646 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) _0_646))
         else ());
        (let fv =
           let _0_647 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident _0_647 None  in
         let lbname = FStar_Util.Inr fv  in
         let lb =
           (false,
             [{
                FStar_Syntax_Syntax.lbname = lbname;
                FStar_Syntax_Syntax.lbunivs = [];
                FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
                FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid;
                FStar_Syntax_Syntax.lbdef = def
              }])
            in
         let sig_ctx =
           FStar_Syntax_Syntax.Sig_let
             (lb, FStar_Range.dummyRange, [lident],
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen], [])
            in
         let _0_648 =
           (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)) None
             FStar_Range.dummyRange
            in
         (sig_ctx, _0_648))
  
let check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___100_6176 =
        match uu___100_6176 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____6177 -> false  in
      let reducibility uu___101_6181 =
        match uu___101_6181 with
        | FStar_Syntax_Syntax.Abstract 
          |FStar_Syntax_Syntax.Irreducible 
           |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
            |FStar_Syntax_Syntax.Visible_default 
             |FStar_Syntax_Syntax.Inline_for_extraction 
            -> true
        | uu____6182 -> false  in
      let assumption uu___102_6186 =
        match uu___102_6186 with
        | FStar_Syntax_Syntax.Assumption |FStar_Syntax_Syntax.New  -> true
        | uu____6187 -> false  in
      let reification uu___103_6191 =
        match uu___103_6191 with
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            true
        | uu____6193 -> false  in
      let inferred uu___104_6197 =
        match uu___104_6197 with
        | FStar_Syntax_Syntax.Discriminator _
          |FStar_Syntax_Syntax.Projector _
           |FStar_Syntax_Syntax.RecordType _
            |FStar_Syntax_Syntax.RecordConstructor _
             |FStar_Syntax_Syntax.ExceptionConstructor 
              |FStar_Syntax_Syntax.HasMaskedEffect 
               |FStar_Syntax_Syntax.Effect 
            -> true
        | uu____6202 -> false  in
      let has_eq uu___105_6206 =
        match uu___105_6206 with
        | FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq  -> true
        | uu____6207 -> false  in
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
        | uu____6232 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____6235 =
        let _0_649 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___106_6237  ->
                  match uu___106_6237 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____6238 -> false))
           in
        FStar_All.pipe_right _0_649 Prims.op_Negation  in
      if uu____6235
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          Prims.raise
            (FStar_Errors.Error
               (let _0_651 =
                  let _0_650 = FStar_Syntax_Print.quals_to_string quals  in
                  FStar_Util.format2
                    "The qualifier list \"[%s]\" is not permissible for this element%s"
                    _0_650 msg
                   in
                (_0_651, r)))
           in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err' uu____6255 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____6263 =
            Prims.op_Negation
              (FStar_All.pipe_right quals
                 (FStar_List.for_all (quals_combo_ok quals)))
             in
          if uu____6263 then err "ill-formed combination" else ());
         (match se with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____6267),uu____6268,uu____6269,uu____6270,uu____6271)
              ->
              ((let uu____6284 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____6284
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____6287 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____6287
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____6291 ->
              let uu____6299 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_Util.for_all
                        (fun x  ->
                           (((x = FStar_Syntax_Syntax.Abstract) ||
                               (inferred x))
                              || (visibility x))
                             || (has_eq x))))
                 in
              if uu____6299 then err' () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____6303 ->
              let uu____6310 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____6310 then err' () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____6313 ->
              let uu____6319 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_Util.for_all
                        (fun x  ->
                           (visibility x) ||
                             (x = FStar_Syntax_Syntax.Assumption))))
                 in
              if uu____6319 then err' () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____6323 ->
              let uu____6326 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_Util.for_all
                        (fun x  ->
                           (((x = FStar_Syntax_Syntax.TotalEffect) ||
                               (inferred x))
                              || (visibility x))
                             || (reification x))))
                 in
              if uu____6326 then err' () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____6330 ->
              let uu____6333 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_Util.for_all
                        (fun x  ->
                           (((x = FStar_Syntax_Syntax.TotalEffect) ||
                               (inferred x))
                              || (visibility x))
                             || (reification x))))
                 in
              if uu____6333 then err' () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6337 ->
              let uu____6347 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_Util.for_all
                        (fun x  -> (inferred x) || (visibility x))))
                 in
              if uu____6347 then err' () else ()
          | uu____6351 -> ()))
      else ()
  
let mk_discriminator_and_indexed_projectors :
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
                      let p = FStar_Ident.range_of_lid lid  in
                      let pos q =
                        FStar_Syntax_Syntax.withinfo q
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p
                         in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee" (Some p) ptyp
                         in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs
                         in
                      let tps = inductive_tps  in
                      let arg_typ =
                        let inst_tc =
                          (FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_uinst
                                (let _0_652 =
                                   FStar_Syntax_Syntax.fv_to_tm
                                     (FStar_Syntax_Syntax.lid_as_fv tc
                                        FStar_Syntax_Syntax.Delta_constant
                                        None)
                                    in
                                 (_0_652, inst_univs)))) None p
                           in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____6433  ->
                                  match uu____6433 with
                                  | (x,imp) ->
                                      let _0_653 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (_0_653, imp)))
                           in
                        (FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p
                         in
                      let unrefined_arg_binder =
                        FStar_Syntax_Syntax.mk_binder (projectee arg_typ)  in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let x =
                             FStar_Syntax_Syntax.new_bv (Some p) arg_typ  in
                           let sort =
                             let disc_fvar =
                               FStar_Syntax_Syntax.fvar
                                 (FStar_Ident.set_lid_range disc_name p)
                                 FStar_Syntax_Syntax.Delta_equational None
                                in
                             let _0_658 =
                               FStar_Syntax_Util.b2t
                                 ((let _0_657 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let _0_656 =
                                     let _0_655 =
                                       let _0_654 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg _0_654
                                        in
                                     [_0_655]  in
                                   FStar_Syntax_Syntax.mk_Tm_app _0_657
                                     _0_656) None p)
                                in
                             FStar_Syntax_Util.refine x _0_658  in
                           FStar_Syntax_Syntax.mk_binder
                             (let uu___147_6459 = projectee arg_typ  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___147_6459.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___147_6459.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = sort
                              }))
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let _0_659 =
                          FStar_List.map
                            (fun uu____6477  ->
                               match uu____6477 with
                               | (x,uu____6484) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps
                           in
                        FStar_List.append _0_659 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____6505  ->
                                match uu____6505 with
                                | (x,uu____6512) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag))))
                         in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let no_decl = false  in
                           let only_decl =
                             (let _0_660 =
                                FStar_TypeChecker_Env.current_module env  in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid _0_660)
                               ||
                               (FStar_Options.dont_gen_projectors
                                  (FStar_TypeChecker_Env.current_module env).FStar_Ident.str)
                              in
                           let quals =
                             let _0_663 =
                               let _0_662 =
                                 let uu____6525 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit)
                                    in
                                 if uu____6525
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else []  in
                               let _0_661 =
                                 FStar_List.filter
                                   (fun uu___107_6528  ->
                                      match uu___107_6528 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____6529 -> false) iquals
                                  in
                               FStar_List.append _0_662 _0_661  in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) _0_663
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               FStar_Syntax_Syntax.mk_Total
                                 (FStar_Syntax_Syntax.fv_to_tm
                                    (FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Syntax_Const.bool_lid
                                       FStar_Syntax_Syntax.Delta_constant
                                       None))
                                in
                             let _0_664 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               _0_664
                              in
                           let decl =
                             FStar_Syntax_Syntax.Sig_declare_typ
                               (discriminator_name, uvs, t, quals,
                                 (FStar_Ident.range_of_lid discriminator_name))
                              in
                           (let uu____6543 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____6543
                            then
                              let _0_665 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n" _0_665
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
                                             fun uu____6571  ->
                                               match uu____6571 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let _0_667 =
                                                       pos
                                                         (FStar_Syntax_Syntax.Pat_dot_term
                                                            (let _0_666 =
                                                               FStar_Syntax_Syntax.gen_bv
                                                                 (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                 None
                                                                 FStar_Syntax_Syntax.tun
                                                                in
                                                             (_0_666,
                                                               FStar_Syntax_Syntax.tun)))
                                                        in
                                                     (_0_667, b)
                                                   else
                                                     (let _0_668 =
                                                        pos
                                                          (FStar_Syntax_Syntax.Pat_wild
                                                             (FStar_Syntax_Syntax.gen_bv
                                                                (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                None
                                                                FStar_Syntax_Syntax.tun))
                                                         in
                                                      (_0_668, b))))
                                      in
                                   let pat_true =
                                     let _0_670 =
                                       pos
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (let _0_669 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 lid
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some fvq)
                                                in
                                             (_0_669, arg_pats)))
                                        in
                                     (_0_670, None,
                                       FStar_Syntax_Const.exp_true_bool)
                                      in
                                   let pat_false =
                                     let _0_671 =
                                       pos
                                         (FStar_Syntax_Syntax.Pat_wild
                                            (FStar_Syntax_Syntax.new_bv None
                                               FStar_Syntax_Syntax.tun))
                                        in
                                     (_0_671, None,
                                       FStar_Syntax_Const.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (Prims.fst unrefined_arg_binder)
                                      in
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_match
                                         (let _0_675 =
                                            let _0_674 =
                                              FStar_Syntax_Util.branch
                                                pat_true
                                               in
                                            let _0_673 =
                                              let _0_672 =
                                                FStar_Syntax_Util.branch
                                                  pat_false
                                                 in
                                              [_0_672]  in
                                            _0_674 :: _0_673  in
                                          (arg_exp, _0_675)))) None p)
                                 in
                              let dd =
                                let uu____6640 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____6640
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    FStar_Syntax_Syntax.Delta_equational
                                else FStar_Syntax_Syntax.Delta_equational  in
                              let imp =
                                FStar_Syntax_Util.abs binders body None  in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun  in
                              let lb =
                                let _0_677 =
                                  FStar_Util.Inr
                                    (FStar_Syntax_Syntax.lid_as_fv
                                       discriminator_name dd None)
                                   in
                                let _0_676 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = _0_677;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = _0_676
                                }  in
                              let impl =
                                FStar_Syntax_Syntax.Sig_let
                                  (let _0_680 =
                                     let _0_679 =
                                       let _0_678 =
                                         FStar_All.pipe_right
                                           lb.FStar_Syntax_Syntax.lbname
                                           FStar_Util.right
                                          in
                                       FStar_All.pipe_right _0_678
                                         (fun fv  ->
                                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                        in
                                     [_0_679]  in
                                   ((false, [lb]), p, _0_680, quals, []))
                                 in
                              (let uu____6668 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____6668
                               then
                                 let _0_681 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   _0_681
                               else ());
                              [decl; impl]))
                         in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder)
                         in
                      let binders =
                        FStar_List.append imp_binders [arg_binder]  in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder
                         in
                      let subst =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6688  ->
                                  match uu____6688 with
                                  | (a,uu____6692) ->
                                      let uu____6693 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____6693 with
                                       | (field_name,uu____6697) ->
                                           let field_proj_tm =
                                             let _0_682 =
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 (FStar_Syntax_Syntax.lid_as_fv
                                                    field_name
                                                    FStar_Syntax_Syntax.Delta_equational
                                                    None)
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               _0_682 inst_univs
                                              in
                                           let proj =
                                             (FStar_Syntax_Syntax.mk_Tm_app
                                                field_proj_tm [arg]) None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let _0_703 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____6723  ->
                                    match uu____6723 with
                                    | (x,uu____6728) ->
                                        let p =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____6730 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____6730 with
                                         | (field_name,uu____6735) ->
                                             let t =
                                               let _0_684 =
                                                 let _0_683 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     (FStar_Syntax_Subst.subst
                                                        subst
                                                        x.FStar_Syntax_Syntax.sort)
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders _0_683
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) _0_684
                                                in
                                             let only_decl =
                                               ((let _0_685 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env
                                                    in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   _0_685)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (FStar_Options.dont_gen_projectors
                                                    (FStar_TypeChecker_Env.current_module
                                                       env).FStar_Ident.str)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let _0_686 =
                                                   FStar_List.filter
                                                     (fun uu___108_6747  ->
                                                        match uu___108_6747
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____6748 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: _0_686
                                               else q  in
                                             let quals =
                                               let iquals =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___109_6756  ->
                                                         match uu___109_6756
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                           
                                                           |FStar_Syntax_Syntax.Private
                                                            -> true
                                                         | uu____6757 ->
                                                             false))
                                                  in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals)
                                                in
                                             let decl =
                                               FStar_Syntax_Syntax.Sig_declare_typ
                                                 (field_name, uvs, t, quals,
                                                   (FStar_Ident.range_of_lid
                                                      field_name))
                                                in
                                             ((let uu____6761 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____6761
                                               then
                                                 let _0_687 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   _0_687
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     None
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j  ->
                                                           fun uu____6788  ->
                                                             match uu____6788
                                                             with
                                                             | (x,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp
                                                                    in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let _0_688
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (_0_688,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let _0_690
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (let _0_689
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (_0_689,
                                                                    FStar_Syntax_Syntax.tun)))
                                                                     in
                                                                    (_0_690,
                                                                    b))
                                                                   else
                                                                    (let _0_691
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_wild
                                                                    (FStar_Syntax_Syntax.gen_bv
                                                                    (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun))
                                                                     in
                                                                    (_0_691,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let _0_694 =
                                                     pos
                                                       (FStar_Syntax_Syntax.Pat_cons
                                                          (let _0_692 =
                                                             FStar_Syntax_Syntax.lid_as_fv
                                                               lid
                                                               FStar_Syntax_Syntax.Delta_constant
                                                               (Some fvq)
                                                              in
                                                           (_0_692, arg_pats)))
                                                      in
                                                   let _0_693 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (_0_694, None, _0_693)  in
                                                 let body =
                                                   (FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_match
                                                         (let _0_696 =
                                                            let _0_695 =
                                                              FStar_Syntax_Util.branch
                                                                pat
                                                               in
                                                            [_0_695]  in
                                                          (arg_exp, _0_696))))
                                                     None p
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None
                                                    in
                                                 let dd =
                                                   let uu____6858 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____6858
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       FStar_Syntax_Syntax.Delta_equational
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational
                                                    in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let lb =
                                                   let _0_698 =
                                                     FStar_Util.Inr
                                                       (FStar_Syntax_Syntax.lid_as_fv
                                                          field_name dd None)
                                                      in
                                                   let _0_697 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = _0_698;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = _0_697
                                                   }  in
                                                 let impl =
                                                   FStar_Syntax_Syntax.Sig_let
                                                     (let _0_701 =
                                                        let _0_700 =
                                                          let _0_699 =
                                                            FStar_All.pipe_right
                                                              lb.FStar_Syntax_Syntax.lbname
                                                              FStar_Util.right
                                                             in
                                                          FStar_All.pipe_right
                                                            _0_699
                                                            (fun fv  ->
                                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                           in
                                                        [_0_700]  in
                                                      ((false, [lb]), p,
                                                        _0_701, quals, []))
                                                    in
                                                 (let uu____6880 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____6880
                                                  then
                                                    let _0_702 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      _0_702
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right _0_703 FStar_List.flatten  in
                      FStar_List.append discriminator_ses projectors_ses
  
let mk_data_operations :
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
              (constr_lid,uvs,t,typ_lid,n_typars,quals,uu____6908,r) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____6914 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____6914 with
               | (univ_opening,uvs) ->
                   let t = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____6927 = FStar_Syntax_Util.arrow_formals_comp t
                      in
                   (match uu____6927 with
                    | (formals,uu____6935) ->
                        let uu____6942 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se  ->
                                 let uu____6955 =
                                   let _0_704 =
                                     FStar_Util.must
                                       (FStar_Syntax_Util.lid_of_sigelt se)
                                      in
                                   FStar_Ident.lid_equals typ_lid _0_704  in
                                 if uu____6955
                                 then
                                   match se with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____6964,uvs',tps,typ0,uu____6968,constrs,uu____6970,uu____6971)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____6985 -> failwith "Impossible"
                                 else None)
                             in
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
                                     ("Unexpected data constructor", r))
                           in
                        (match uu____6942 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ0 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____7027 =
                               FStar_Syntax_Util.arrow_formals_comp typ0  in
                             (match uu____7027 with
                              | (indices,uu____7035) ->
                                  let refine_domain =
                                    let uu____7043 =
                                      FStar_All.pipe_right quals
                                        (FStar_Util.for_some
                                           (fun uu___110_7045  ->
                                              match uu___110_7045 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____7046 -> true
                                              | uu____7051 -> false))
                                       in
                                    if uu____7043
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___111_7058 =
                                      match uu___111_7058 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____7060,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____7067 -> None  in
                                    let uu____7068 =
                                      FStar_Util.find_map quals
                                        filter_records
                                       in
                                    match uu____7068 with
                                    | None  -> FStar_Syntax_Syntax.Data_ctor
                                    | Some q -> q  in
                                  let iquals =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals  in
                                  let fields =
                                    let uu____7076 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____7076 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____7107  ->
                                               fun uu____7108  ->
                                                 match (uu____7107,
                                                         uu____7108)
                                                 with
                                                 | ((x,uu____7118),(x',uu____7120))
                                                     ->
                                                     FStar_Syntax_Syntax.NT
                                                       (let _0_705 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x'
                                                           in
                                                        (x, _0_705))) imp_tps
                                            inductive_tps
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals fv_qual refine_domain env typ_lid
                                    constr_lid uvs inductive_tps indices
                                    fields))))
          | uu____7125 -> []
  
let destruct_comp_term :
  FStar_Syntax_Syntax.term ->
    (FStar_Ident.lid * FStar_Syntax_Syntax.universes)
  =
  fun m  ->
    let uu____7131 = (FStar_Syntax_Subst.compress m).FStar_Syntax_Syntax.n
       in
    match uu____7131 with
    | FStar_Syntax_Syntax.Tm_uinst
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
           FStar_Syntax_Syntax.tk = uu____7135;
           FStar_Syntax_Syntax.pos = uu____7136;
           FStar_Syntax_Syntax.vars = uu____7137;_},univs)
        -> let _0_706 = FStar_Syntax_Syntax.lid_of_fv fv  in (_0_706, univs)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let _0_707 = FStar_Syntax_Syntax.lid_of_fv fv  in (_0_707, [])
    | uu____7145 -> failwith "Impossible"
  
let mlift_of_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_TypeChecker_Env.normal_comp_typ ->
        FStar_TypeChecker_Env.normal_comp_typ
  =
  fun env  ->
    fun sub  ->
      let mlift nct =
        let fail uu____7162 =
          let _0_708 =
            FStar_Util.format2
              "Invalid application of mlift, effect names differ : %s vs %s"
              (FStar_Ident.text_of_lid nct.FStar_TypeChecker_Env.nct_name)
              (FStar_Ident.text_of_lid
                 (sub.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name)
             in
          FStar_All.pipe_left failwith _0_708  in
        let sigma =
          let skeleton =
            let _0_710 =
              (FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_arrow
                    (let _0_709 =
                       FStar_Syntax_Syntax.mk_Total
                         FStar_TypeChecker_Common.t_unit
                        in
                     ((sub.FStar_Syntax_Syntax.sub_eff_binders), _0_709))))
                None FStar_Range.dummyRange
               in
            ((sub.FStar_Syntax_Syntax.sub_eff_univs), _0_710)  in
          let uu____7184 = FStar_TypeChecker_Env.inst_tscheme skeleton  in
          match uu____7184 with
          | (univ_meta_vars,skel) ->
              let uu____7190 =
                FStar_List.fold_right
                  (fun univ  ->
                     fun uu____7198  ->
                       match uu____7198 with
                       | (out,i) ->
                           (((FStar_Syntax_Syntax.UN (i, univ)) :: out),
                             (i + (Prims.parse_int "1")))) univ_meta_vars
                  ([],
                    (FStar_List.length
                       sub.FStar_Syntax_Syntax.sub_eff_binders))
                 in
              (match uu____7190 with
               | (univ_meta_vars_subst,uu____7217) ->
                   let uu____7220 =
                     maybe_instantiate env FStar_Syntax_Syntax.tun skel  in
                   (match uu____7220 with
                    | (_term,_typ,_guard,index_meta_var_subst) ->
                        FStar_List.append univ_meta_vars_subst
                          index_meta_var_subst))
           in
        let formal_source =
          let _0_711 =
            FStar_Syntax_Syntax.mk_Comp
              sub.FStar_Syntax_Syntax.sub_eff_source
             in
          FStar_Syntax_Subst.subst_comp sigma _0_711  in
        let actual_source_no_wp =
          let ct =
            {
              FStar_Syntax_Syntax.comp_typ_name =
                (nct.FStar_TypeChecker_Env.nct_name);
              FStar_Syntax_Syntax.comp_univs =
                (nct.FStar_TypeChecker_Env.nct_univs);
              FStar_Syntax_Syntax.effect_args =
                (FStar_List.append nct.FStar_TypeChecker_Env.nct_indices
                   [nct.FStar_TypeChecker_Env.nct_result]);
              FStar_Syntax_Syntax.flags =
                (nct.FStar_TypeChecker_Env.nct_flags)
            }  in
          FStar_Syntax_Syntax.mk_Comp ct  in
        (let uu____7238 =
           FStar_TypeChecker_Rel.sub_comp
             (let uu___148_7240 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___148_7240.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___148_7240.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___148_7240.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___148_7240.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___148_7240.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___148_7240.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___148_7240.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___148_7240.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___148_7240.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___148_7240.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___148_7240.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___148_7240.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs =
                  (uu___148_7240.FStar_TypeChecker_Env.letrecs);
                FStar_TypeChecker_Env.top_level =
                  (uu___148_7240.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___148_7240.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq = true;
                FStar_TypeChecker_Env.is_iface =
                  (uu___148_7240.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___148_7240.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___148_7240.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___148_7240.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.type_of =
                  (uu___148_7240.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___148_7240.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___148_7240.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qname_and_index =
                  (uu___148_7240.FStar_TypeChecker_Env.qname_and_index)
              }) formal_source actual_source_no_wp
            in
         match uu____7238 with
         | None  -> fail ()
         | Some g -> FStar_TypeChecker_Rel.force_trivial_guard env g);
        (let target_nct =
           let target_wp =
             (let _0_713 =
                let _0_712 =
                  FStar_Util.must sub.FStar_Syntax_Syntax.sub_eff_lift_wp  in
                FStar_Syntax_Subst.subst sigma _0_712  in
              FStar_Syntax_Syntax.mk_Tm_app _0_713
                [nct.FStar_TypeChecker_Env.nct_wp]) None
               FStar_Range.dummyRange
              in
           let target_comp_no_wp =
             let _0_715 =
               let _0_714 =
                 FStar_Syntax_Syntax.mk_Comp
                   sub.FStar_Syntax_Syntax.sub_eff_target
                  in
               FStar_Syntax_Subst.subst_comp sigma _0_714  in
             FStar_All.pipe_right _0_715 FStar_Syntax_Util.comp_to_comp_typ
              in
           let target_comp_typ =
             let uu___149_7252 = target_comp_no_wp  in
             let _0_718 =
               let _0_717 =
                 let _0_716 = FStar_Syntax_Syntax.as_arg target_wp  in
                 [_0_716]  in
               FStar_List.append
                 target_comp_no_wp.FStar_Syntax_Syntax.effect_args _0_717
                in
             {
               FStar_Syntax_Syntax.comp_typ_name =
                 (uu___149_7252.FStar_Syntax_Syntax.comp_typ_name);
               FStar_Syntax_Syntax.comp_univs =
                 (uu___149_7252.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_args = _0_718;
               FStar_Syntax_Syntax.flags =
                 (uu___149_7252.FStar_Syntax_Syntax.flags)
             }  in
           let _0_719 = FStar_Syntax_Syntax.mk_Comp target_comp_typ  in
           FStar_TypeChecker_Env.comp_as_normal_comp_typ env _0_719  in
         target_nct)
         in
      mlift
  
let extend_effect_lattice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun sub_eff  ->
      let compose_edges e1 e2 =
        {
          FStar_TypeChecker_Env.msource = (e1.FStar_TypeChecker_Env.msource);
          FStar_TypeChecker_Env.mtarget = (e2.FStar_TypeChecker_Env.mtarget);
          FStar_TypeChecker_Env.mlift =
            (fun nct  ->
               e2.FStar_TypeChecker_Env.mlift
                 (e1.FStar_TypeChecker_Env.mlift nct))
        }  in
      let edge =
        let _0_720 = mlift_of_sub_eff env sub_eff  in
        {
          FStar_TypeChecker_Env.msource =
            ((sub_eff.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name);
          FStar_TypeChecker_Env.mtarget =
            ((sub_eff.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.comp_typ_name);
          FStar_TypeChecker_Env.mlift = _0_720
        }  in
      let id_edge l =
        {
          FStar_TypeChecker_Env.msource = l;
          FStar_TypeChecker_Env.mtarget = l;
          FStar_TypeChecker_Env.mlift = (fun nct  -> nct)
        }  in
      let print_mlift l =
        let arg =
          let _0_721 = FStar_Ident.lid_of_path ["ARG"] FStar_Range.dummyRange
             in
          FStar_Syntax_Syntax.lid_as_fv _0_721
            FStar_Syntax_Syntax.Delta_constant None
           in
        let wp =
          let _0_722 = FStar_Ident.lid_of_path ["WP"] FStar_Range.dummyRange
             in
          FStar_Syntax_Syntax.lid_as_fv _0_722
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Print.term_to_string (l arg wp)  in
      let order = edge ::
        ((env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.order)  in
      let ms =
        FStar_All.pipe_right
          (env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.decls
          (FStar_List.map (fun e  -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order uu____7318 =
        match uu____7318 with
        | (i,j) ->
            if FStar_Ident.lid_equals i j
            then
              FStar_All.pipe_right (id_edge i) (fun _0_723  -> Some _0_723)
            else
              FStar_All.pipe_right order
                (FStar_Util.find_opt
                   (fun e  ->
                      (FStar_Ident.lid_equals e.FStar_TypeChecker_Env.msource
                         i)
                        &&
                        (FStar_Ident.lid_equals
                           e.FStar_TypeChecker_Env.mtarget j)))
         in
      let order =
        FStar_All.pipe_right ms
          (FStar_List.fold_left
             (fun order  ->
                fun k  ->
                  let _0_727 =
                    FStar_All.pipe_right ms
                      (FStar_List.collect
                         (fun i  ->
                            if FStar_Ident.lid_equals i k
                            then []
                            else
                              FStar_All.pipe_right ms
                                (FStar_List.collect
                                   (fun j  ->
                                      if FStar_Ident.lid_equals j k
                                      then []
                                      else
                                        (let uu____7349 =
                                           let _0_725 =
                                             find_edge order (i, k)  in
                                           let _0_724 =
                                             find_edge order (k, j)  in
                                           (_0_725, _0_724)  in
                                         match uu____7349 with
                                         | (Some e1,Some e2) ->
                                             let _0_726 = compose_edges e1 e2
                                                in
                                             [_0_726]
                                         | uu____7361 -> [])))))
                     in
                  FStar_List.append order _0_727) order)
         in
      let order =
        FStar_Util.remove_dups
          (fun e1  ->
             fun e2  ->
               (FStar_Ident.lid_equals e1.FStar_TypeChecker_Env.msource
                  e2.FStar_TypeChecker_Env.msource)
                 &&
                 (FStar_Ident.lid_equals e1.FStar_TypeChecker_Env.mtarget
                    e2.FStar_TypeChecker_Env.mtarget)) order
         in
      FStar_All.pipe_right order
        (FStar_List.iter
           (fun edge  ->
              let uu____7373 =
                (FStar_Ident.lid_equals edge.FStar_TypeChecker_Env.msource
                   FStar_Syntax_Const.effect_DIV_lid)
                  &&
                  (let _0_728 =
                     FStar_TypeChecker_Env.lookup_effect_quals env
                       edge.FStar_TypeChecker_Env.mtarget
                      in
                   FStar_All.pipe_right _0_728
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____7373
              then
                Prims.raise
                  (FStar_Errors.Error
                     (let _0_730 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge.FStar_TypeChecker_Env.mtarget).FStar_Ident.str
                         in
                      let _0_729 = FStar_TypeChecker_Env.get_range env  in
                      (_0_730, _0_729)))
              else ()));
      (let joins =
         FStar_All.pipe_right ms
           (FStar_List.collect
              (fun i  ->
                 FStar_All.pipe_right ms
                   (FStar_List.collect
                      (fun j  ->
                         let join_opt =
                           FStar_All.pipe_right ms
                             (FStar_List.fold_left
                                (fun bopt  ->
                                   fun k  ->
                                     let uu____7429 =
                                       let _0_732 = find_edge order (i, k)
                                          in
                                       let _0_731 = find_edge order (j, k)
                                          in
                                       (_0_732, _0_731)  in
                                     match uu____7429 with
                                     | (Some ik,Some jk) ->
                                         (match bopt with
                                          | None  -> Some (k, ik, jk)
                                          | Some (ub,uu____7455,uu____7456)
                                              ->
                                              let uu____7460 =
                                                (FStar_Util.is_some
                                                   (find_edge order (k, ub)))
                                                  &&
                                                  (Prims.op_Negation
                                                     (FStar_Util.is_some
                                                        (find_edge order
                                                           (ub, k))))
                                                 in
                                              if uu____7460
                                              then Some (k, ik, jk)
                                              else bopt)
                                     | uu____7469 -> bopt) None)
                            in
                         match join_opt with
                         | None  -> []
                         | Some (k,e1,e2) ->
                             [(i, j, k, (e1.FStar_TypeChecker_Env.mlift),
                                (e2.FStar_TypeChecker_Env.mlift))]))))
          in
       let effects =
         let uu___150_7512 = env.FStar_TypeChecker_Env.effects  in
         {
           FStar_TypeChecker_Env.decls =
             (uu___150_7512.FStar_TypeChecker_Env.decls);
           FStar_TypeChecker_Env.order = order;
           FStar_TypeChecker_Env.joins = joins
         }  in
       let uu___151_7513 = env  in
       {
         FStar_TypeChecker_Env.solver =
           (uu___151_7513.FStar_TypeChecker_Env.solver);
         FStar_TypeChecker_Env.range =
           (uu___151_7513.FStar_TypeChecker_Env.range);
         FStar_TypeChecker_Env.curmodule =
           (uu___151_7513.FStar_TypeChecker_Env.curmodule);
         FStar_TypeChecker_Env.gamma =
           (uu___151_7513.FStar_TypeChecker_Env.gamma);
         FStar_TypeChecker_Env.gamma_cache =
           (uu___151_7513.FStar_TypeChecker_Env.gamma_cache);
         FStar_TypeChecker_Env.modules =
           (uu___151_7513.FStar_TypeChecker_Env.modules);
         FStar_TypeChecker_Env.expected_typ =
           (uu___151_7513.FStar_TypeChecker_Env.expected_typ);
         FStar_TypeChecker_Env.sigtab =
           (uu___151_7513.FStar_TypeChecker_Env.sigtab);
         FStar_TypeChecker_Env.is_pattern =
           (uu___151_7513.FStar_TypeChecker_Env.is_pattern);
         FStar_TypeChecker_Env.instantiate_imp =
           (uu___151_7513.FStar_TypeChecker_Env.instantiate_imp);
         FStar_TypeChecker_Env.effects = effects;
         FStar_TypeChecker_Env.generalize =
           (uu___151_7513.FStar_TypeChecker_Env.generalize);
         FStar_TypeChecker_Env.letrecs =
           (uu___151_7513.FStar_TypeChecker_Env.letrecs);
         FStar_TypeChecker_Env.top_level =
           (uu___151_7513.FStar_TypeChecker_Env.top_level);
         FStar_TypeChecker_Env.check_uvars =
           (uu___151_7513.FStar_TypeChecker_Env.check_uvars);
         FStar_TypeChecker_Env.use_eq =
           (uu___151_7513.FStar_TypeChecker_Env.use_eq);
         FStar_TypeChecker_Env.is_iface =
           (uu___151_7513.FStar_TypeChecker_Env.is_iface);
         FStar_TypeChecker_Env.admit =
           (uu___151_7513.FStar_TypeChecker_Env.admit);
         FStar_TypeChecker_Env.lax =
           (uu___151_7513.FStar_TypeChecker_Env.lax);
         FStar_TypeChecker_Env.lax_universes =
           (uu___151_7513.FStar_TypeChecker_Env.lax_universes);
         FStar_TypeChecker_Env.type_of =
           (uu___151_7513.FStar_TypeChecker_Env.type_of);
         FStar_TypeChecker_Env.universe_of =
           (uu___151_7513.FStar_TypeChecker_Env.universe_of);
         FStar_TypeChecker_Env.use_bv_sorts =
           (uu___151_7513.FStar_TypeChecker_Env.use_bv_sorts);
         FStar_TypeChecker_Env.qname_and_index =
           (uu___151_7513.FStar_TypeChecker_Env.qname_and_index)
       })
  
let build_lattice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____7521) ->
          let uu___152_7522 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___152_7522.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___152_7522.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___152_7522.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___152_7522.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___152_7522.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___152_7522.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___152_7522.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___152_7522.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___152_7522.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___152_7522.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (let uu___153_7523 = env.FStar_TypeChecker_Env.effects  in
               {
                 FStar_TypeChecker_Env.decls = (ne ::
                   ((env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.decls));
                 FStar_TypeChecker_Env.order =
                   (uu___153_7523.FStar_TypeChecker_Env.order);
                 FStar_TypeChecker_Env.joins =
                   (uu___153_7523.FStar_TypeChecker_Env.joins)
               });
            FStar_TypeChecker_Env.generalize =
              (uu___152_7522.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___152_7522.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___152_7522.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___152_7522.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___152_7522.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___152_7522.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___152_7522.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___152_7522.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___152_7522.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___152_7522.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___152_7522.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___152_7522.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___152_7522.FStar_TypeChecker_Env.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect (sub,uu____7525) ->
          extend_effect_lattice env sub
      | uu____7526 -> env
  