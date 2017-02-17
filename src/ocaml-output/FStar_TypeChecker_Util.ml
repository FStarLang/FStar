open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv Prims.option* FStar_Syntax_Syntax.lcomp)
let report:
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let uu____12 = FStar_TypeChecker_Env.get_range env in
      let uu____13 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.report uu____12 uu____13
let is_type: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____17 =
      let uu____18 = FStar_Syntax_Subst.compress t in
      uu____18.FStar_Syntax_Syntax.n in
    match uu____17 with
    | FStar_Syntax_Syntax.Tm_type uu____21 -> true
    | uu____22 -> false
let t_binders:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    let uu____29 = FStar_TypeChecker_Env.all_binders env in
    FStar_All.pipe_right uu____29
      (FStar_List.filter
         (fun uu____35  ->
            match uu____35 with
            | (x,uu____39) -> is_type x.FStar_Syntax_Syntax.sort))
let new_uvar_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____49 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____50 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____50) in
        match uu____49 with
        | true  -> FStar_TypeChecker_Env.all_binders env
        | uu____51 -> t_binders env in
      let uu____52 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____52 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun k  -> let uu____59 = new_uvar_aux env k in Prims.fst uu____59
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___91_64  ->
    match uu___91_64 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____66);
        FStar_Syntax_Syntax.tk = uu____67;
        FStar_Syntax_Syntax.pos = uu____68;
        FStar_Syntax_Syntax.vars = uu____69;_} -> uv
    | uu____84 -> failwith "Impossible"
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
          let uu____103 =
            FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid in
          match uu____103 with
          | Some (uu____116::(tm,uu____118)::[]) ->
              let t =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))))
                  None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____162 ->
              let uu____169 = new_uvar_aux env k in
              (match uu____169 with
               | (t,u) ->
                   let g =
                     let uu___111_181 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____182 =
                       let uu____190 =
                         let uu____197 = as_uvar u in
                         (reason, env, uu____197, t, k, r) in
                       [uu____190] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___111_181.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___111_181.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___111_181.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____182
                     } in
                   let uu____210 =
                     let uu____214 =
                       let uu____217 = as_uvar u in (uu____217, r) in
                     [uu____214] in
                   (t, uu____210, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____235 =
        let uu____236 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____236 in
      match uu____235 with
      | true  ->
          let us =
            let uu____240 =
              let uu____242 = FStar_Util.set_elements uvs in
              FStar_List.map
                (fun uu____258  ->
                   match uu____258 with
                   | (x,uu____266) -> FStar_Syntax_Print.uvar_to_string x)
                uu____242 in
            FStar_All.pipe_right uu____240 (FStar_String.concat ", ") in
          (FStar_Options.push ();
           FStar_Options.set_option "hide_uvar_nums"
             (FStar_Options.Bool false);
           FStar_Options.set_option "print_implicits"
             (FStar_Options.Bool true);
           (let uu____283 =
              let uu____284 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____284 in
            FStar_Errors.report r uu____283);
           FStar_Options.pop ())
      | uu____285 -> ()
let force_sort':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____293 = FStar_ST.read s.FStar_Syntax_Syntax.tk in
    match uu____293 with
    | None  ->
        let uu____298 =
          let uu____299 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos in
          let uu____300 = FStar_Syntax_Print.term_to_string s in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____299 uu____300 in
        failwith uu____298
    | Some tk -> tk
let force_sort s =
  let uu____315 =
    let uu____318 = force_sort' s in FStar_Syntax_Syntax.mk uu____318 in
  uu____315 None s.FStar_Syntax_Syntax.pos
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.typ*
        Prims.bool)
  =
  fun env  ->
    fun uu____335  ->
      match uu____335 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____342;
          FStar_Syntax_Syntax.lbdef = e;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname in
          let t = FStar_Syntax_Subst.compress t in
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               ((match univ_vars <> [] with
                 | true  ->
                     failwith
                       "Impossible: non-empty universe variables but the type is unknown"
                 | uu____363 -> ());
                (let r = FStar_TypeChecker_Env.get_range env in
                 let mk_binder scope a =
                   let uu____374 =
                     let uu____375 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____375.FStar_Syntax_Syntax.n in
                   match uu____374 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____380 = FStar_Syntax_Util.type_u () in
                       (match uu____380 with
                        | (k,uu____386) ->
                            let t =
                              let uu____388 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____388 Prims.fst in
                            ((let uu___112_393 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___112_393.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___112_393.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), false))
                   | uu____394 -> (a, true) in
                 let rec aux must_check_ty vars e =
                   let e = FStar_Syntax_Subst.compress e in
                   match e.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e,uu____419) ->
                       aux must_check_ty vars e
                   | FStar_Syntax_Syntax.Tm_ascribed (e,t,uu____426) ->
                       (t, true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____453) ->
                       let uu____476 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____500  ->
                                 fun uu____501  ->
                                   match (uu____500, uu____501) with
                                   | ((scope,bs,must_check_ty),(a,imp)) ->
                                       let uu____543 =
                                         match must_check_ty with
                                         | true  -> (a, true)
                                         | uu____548 -> mk_binder scope a in
                                       (match uu____543 with
                                        | (tb,must_check_ty) ->
                                            let b = (tb, imp) in
                                            let bs = FStar_List.append bs [b] in
                                            let scope =
                                              FStar_List.append scope [b] in
                                            (scope, bs, must_check_ty)))
                              (vars, [], must_check_ty)) in
                       (match uu____476 with
                        | (scope,bs,must_check_ty) ->
                            let uu____604 = aux must_check_ty scope body in
                            (match uu____604 with
                             | (res,must_check_ty) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t ->
                                       let uu____621 =
                                         FStar_Options.ml_ish () in
                                       (match uu____621 with
                                        | true  ->
                                            FStar_Syntax_Util.ml_comp t r
                                        | uu____622 ->
                                            FStar_Syntax_Syntax.mk_Total t)
                                   | FStar_Util.Inr c -> c in
                                 let t = FStar_Syntax_Util.arrow bs c in
                                 ((let uu____628 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   match uu____628 with
                                   | true  ->
                                       let uu____629 =
                                         FStar_Range.string_of_range r in
                                       let uu____630 =
                                         FStar_Syntax_Print.term_to_string t in
                                       let uu____631 =
                                         FStar_Util.string_of_bool
                                           must_check_ty in
                                       FStar_Util.print3
                                         "(%s) Using type %s .... must check = %s\n"
                                         uu____629 uu____630 uu____631
                                   | uu____632 -> ());
                                  ((FStar_Util.Inl t), must_check_ty))))
                   | uu____639 ->
                       (match must_check_ty with
                        | true  ->
                            ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                        | uu____646 ->
                            let uu____647 =
                              let uu____650 =
                                let uu____651 =
                                  FStar_TypeChecker_Rel.new_uvar r vars
                                    FStar_Syntax_Util.ktype0 in
                                FStar_All.pipe_right uu____651 Prims.fst in
                              FStar_Util.Inl uu____650 in
                            (uu____647, false)) in
                 let uu____658 =
                   let uu____663 = t_binders env in aux false uu____663 e in
                 match uu____658 with
                 | (t,b) ->
                     let t =
                       match t with
                       | FStar_Util.Inr c ->
                           let uu____680 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           (match uu____680 with
                            | true  -> FStar_Syntax_Util.comp_result c
                            | uu____683 ->
                                let uu____684 =
                                  let uu____685 =
                                    let uu____688 =
                                      let uu____689 =
                                        FStar_Syntax_Print.comp_to_string c in
                                      FStar_Util.format1
                                        "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                        uu____689 in
                                    (uu____688, rng) in
                                  FStar_Errors.Error uu____685 in
                                Prims.raise uu____684)
                       | FStar_Util.Inl t -> t in
                     ([], t, b)))
           | uu____696 ->
               let uu____697 = FStar_Syntax_Subst.open_univ_vars univ_vars t in
               (match uu____697 with | (univ_vars,t) -> (univ_vars, t, false)))
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____780) ->
              let uu____785 = FStar_Syntax_Util.type_u () in
              (match uu____785 with
               | (k,uu____798) ->
                   let t = new_uvar env k in
                   let x =
                     let uu___113_801 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___113_801.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___113_801.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____802 =
                     let uu____805 = FStar_TypeChecker_Env.all_binders env in
                     FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p
                       uu____805 t in
                   (match uu____802 with
                    | (e,u) ->
                        let p =
                          let uu___114_820 = p in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___114_820.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___114_820.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env, e, p)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____827 = FStar_Syntax_Util.type_u () in
              (match uu____827 with
               | (t,uu____840) ->
                   let x =
                     let uu___115_842 = x in
                     let uu____843 = new_uvar env t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___115_842.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___115_842.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____843
                     } in
                   let env =
                     match allow_wc_dependence with
                     | true  -> FStar_TypeChecker_Env.push_bv env x
                     | uu____847 -> env in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x))
                       None p.FStar_Syntax_Syntax.p in
                   ([x], [], [x], env, e, p))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____865 = FStar_Syntax_Util.type_u () in
              (match uu____865 with
               | (t,uu____878) ->
                   let x =
                     let uu___116_880 = x in
                     let uu____881 = new_uvar env t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___116_880.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___116_880.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____881
                     } in
                   let env = FStar_TypeChecker_Env.push_bv env x in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x))
                       None p.FStar_Syntax_Syntax.p in
                   ([x], [x], [], env, e, p))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____913 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____969  ->
                        fun uu____970  ->
                          match (uu____969, uu____970) with
                          | ((b,a,w,env,args,pats),(p,imp)) ->
                              let uu____1069 =
                                pat_as_arg_with_env allow_wc_dependence env p in
                              (match uu____1069 with
                               | (b',a',w',env,te,pat) ->
                                   let arg =
                                     match imp with
                                     | true  -> FStar_Syntax_Syntax.iarg te
                                     | uu____1108 ->
                                         FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env,
                                     (arg :: args), ((pat, imp) :: pats))))
                     ([], [], [], env, [], [])) in
              (match uu____913 with
               | (b,a,w,env,args,pats) ->
                   let e =
                     let uu____1177 =
                       let uu____1180 =
                         let uu____1181 =
                           let uu____1186 =
                             let uu____1189 =
                               let uu____1190 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1191 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1190
                                 uu____1191 in
                             uu____1189 None p.FStar_Syntax_Syntax.p in
                           (uu____1186,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1181 in
                       FStar_Syntax_Syntax.mk uu____1180 in
                     uu____1177 None p.FStar_Syntax_Syntax.p in
                   let uu____1208 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1214 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1220 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1208, uu____1214, uu____1220, env, e,
                     (let uu___117_1233 = p in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats)));
                        FStar_Syntax_Syntax.ty =
                          (uu___117_1233.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___117_1233.FStar_Syntax_Syntax.p)
                      })))
          | FStar_Syntax_Syntax.Pat_disj uu____1239 -> failwith "impossible" in
        let rec elaborate_pat env p =
          let maybe_dot inaccessible a r =
            match allow_implicits && inaccessible with
            | true  ->
                FStar_Syntax_Syntax.withinfo
                  (FStar_Syntax_Syntax.Pat_dot_term
                     (a, FStar_Syntax_Syntax.tun))
                  FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r
            | uu____1279 ->
                FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a)
                  FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r in
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let pats =
                FStar_List.map
                  (fun uu____1308  ->
                     match uu____1308 with
                     | (p,imp) ->
                         let uu____1323 = elaborate_pat env p in
                         (uu____1323, imp)) pats in
              let uu____1328 =
                FStar_TypeChecker_Env.lookup_datacon env
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1328 with
               | (uu____1337,t) ->
                   let uu____1339 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1339 with
                    | (f,uu____1350) ->
                        let rec aux formals pats =
                          match (formals, pats) with
                          | ([],[]) -> []
                          | ([],uu____1425::uu____1426) ->
                              Prims.raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1461::uu____1462,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1502  ->
                                      match uu____1502 with
                                      | (t,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1520 =
                                                   let uu____1522 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t in
                                                   Some uu____1522 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1520
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1528 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1528, true)
                                           | uu____1533 ->
                                               let uu____1535 =
                                                 let uu____1536 =
                                                   let uu____1539 =
                                                     let uu____1540 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1540 in
                                                   (uu____1539,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1536 in
                                               Prims.raise uu____1535)))
                          | (f::formals',(p,p_imp)::pats') ->
                              (match f with
                               | (uu____1591,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1592))
                                   when p_imp ->
                                   let uu____1594 = aux formals' pats' in
                                   (p, true) :: uu____1594
                               | (uu____1606,Some
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
                                   let uu____1617 = aux formals' pats in
                                   (p, true) :: uu____1617
                               | (uu____1629,imp) ->
                                   let uu____1633 =
                                     let uu____1638 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p, uu____1638) in
                                   let uu____1641 = aux formals' pats' in
                                   uu____1633 :: uu____1641) in
                        let uu___118_1651 = p in
                        let uu____1654 =
                          let uu____1655 =
                            let uu____1663 = aux f pats in (fv, uu____1663) in
                          FStar_Syntax_Syntax.Pat_cons uu____1655 in
                        {
                          FStar_Syntax_Syntax.v = uu____1654;
                          FStar_Syntax_Syntax.ty =
                            (uu___118_1651.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___118_1651.FStar_Syntax_Syntax.p)
                        }))
          | uu____1674 -> p in
        let one_pat allow_wc_dependence env p =
          let p = elaborate_pat env p in
          let uu____1700 = pat_as_arg_with_env allow_wc_dependence env p in
          match uu____1700 with
          | (b,a,w,env,arg,p) ->
              let uu____1730 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1730 with
               | Some x ->
                   let uu____1743 =
                     let uu____1744 =
                       let uu____1747 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1747, (p.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1744 in
                   Prims.raise uu____1743
               | uu____1756 -> (b, a, w, arg, p)) in
        let top_level_pat_as_args env p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_disj [] -> failwith "impossible"
          | FStar_Syntax_Syntax.Pat_disj (q::pats) ->
              let uu____1799 = one_pat false env q in
              (match uu____1799 with
               | (b,a,uu____1815,te,q) ->
                   let uu____1824 =
                     FStar_List.fold_right
                       (fun p  ->
                          fun uu____1840  ->
                            match uu____1840 with
                            | (w,args,pats) ->
                                let uu____1864 = one_pat false env p in
                                (match uu____1864 with
                                 | (b',a',w',arg,p) ->
                                     let uu____1890 =
                                       let uu____1891 =
                                         FStar_Util.multiset_equiv
                                           FStar_Syntax_Syntax.bv_eq a a' in
                                       Prims.op_Negation uu____1891 in
                                     (match uu____1890 with
                                      | true  ->
                                          let uu____1898 =
                                            let uu____1899 =
                                              let uu____1902 =
                                                FStar_TypeChecker_Err.disjunctive_pattern_vars
                                                  a a' in
                                              let uu____1903 =
                                                FStar_TypeChecker_Env.get_range
                                                  env in
                                              (uu____1902, uu____1903) in
                                            FStar_Errors.Error uu____1899 in
                                          Prims.raise uu____1898
                                      | uu____1910 ->
                                          let uu____1911 =
                                            let uu____1913 =
                                              FStar_Syntax_Syntax.as_arg arg in
                                            uu____1913 :: args in
                                          ((FStar_List.append w' w),
                                            uu____1911, (p :: pats))))) pats
                       ([], [], []) in
                   (match uu____1824 with
                    | (w,args,pats) ->
                        let uu____1934 =
                          let uu____1936 = FStar_Syntax_Syntax.as_arg te in
                          uu____1936 :: args in
                        ((FStar_List.append b w), uu____1934,
                          (let uu___119_1941 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_disj (q :: pats));
                             FStar_Syntax_Syntax.ty =
                               (uu___119_1941.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___119_1941.FStar_Syntax_Syntax.p)
                           }))))
          | uu____1942 ->
              let uu____1943 = one_pat true env p in
              (match uu____1943 with
               | (b,uu____1958,uu____1959,arg,p) ->
                   let uu____1968 =
                     let uu____1970 = FStar_Syntax_Syntax.as_arg arg in
                     [uu____1970] in
                   (b, uu____1968, p)) in
        let uu____1973 = top_level_pat_as_args env p in
        match uu____1973 with
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
          | (uu____2044,FStar_Syntax_Syntax.Tm_uinst (e,uu____2046)) ->
              aux p e
          | (FStar_Syntax_Syntax.Pat_constant
             uu____2051,FStar_Syntax_Syntax.Tm_constant uu____2052) ->
              let uu____2053 = force_sort' e in
              pkg p.FStar_Syntax_Syntax.v uu____2053
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              ((match Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y) with
                | true  ->
                    let uu____2057 =
                      let uu____2058 = FStar_Syntax_Print.bv_to_string x in
                      let uu____2059 = FStar_Syntax_Print.bv_to_string y in
                      FStar_Util.format2
                        "Expected pattern variable %s; got %s" uu____2058
                        uu____2059 in
                    failwith uu____2057
                | uu____2060 -> ());
               (let uu____2062 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                match uu____2062 with
                | true  ->
                    let uu____2063 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2064 =
                      FStar_TypeChecker_Normalize.term_to_string env
                        y.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2
                      "Pattern variable %s introduced at type %s\n"
                      uu____2063 uu____2064
                | uu____2065 -> ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x =
                  let uu___120_2068 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___120_2068.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___120_2068.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2072 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                match uu____2072 with
                | true  ->
                    let uu____2073 =
                      let uu____2074 = FStar_Syntax_Print.bv_to_string x in
                      let uu____2075 = FStar_Syntax_Print.bv_to_string y in
                      FStar_Util.format2
                        "Expected pattern variable %s; got %s" uu____2074
                        uu____2075 in
                    failwith uu____2073
                | uu____2076 -> ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x =
                  let uu___121_2079 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___121_2079.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___121_2079.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2081),uu____2082) ->
              let s = force_sort e in
              let x =
                let uu___122_2091 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___122_2091.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___122_2091.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2104 =
                  let uu____2105 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2105 in
                match uu____2104 with
                | true  ->
                    let uu____2106 =
                      FStar_Util.format2
                        "Expected pattern constructor %s; got %s"
                        ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                        ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                    failwith uu____2106
                | uu____2115 -> ());
               (let uu____2116 = force_sort' e in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____2116))
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
              ((let uu____2187 =
                  let uu____2188 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2188 Prims.op_Negation in
                match uu____2187 with
                | true  ->
                    let uu____2189 =
                      FStar_Util.format2
                        "Expected pattern constructor %s; got %s"
                        ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                        ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                    failwith uu____2189
                | uu____2198 -> ());
               (let fv = fv' in
                let rec match_args matched_pats args argpats =
                  match (args, argpats) with
                  | ([],[]) ->
                      let uu____2277 = force_sort' e in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv, (FStar_List.rev matched_pats))) uu____2277
                  | (arg::args,(argpat,uu____2290)::argpats) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2340) ->
                           let x =
                             let uu____2356 = force_sort e in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p.FStar_Syntax_Syntax.p)) uu____2356 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args
                             argpats
                       | ((e,imp),uu____2370) ->
                           let pat =
                             let uu____2385 = aux argpat e in
                             let uu____2386 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2385, uu____2386) in
                           match_args (pat :: matched_pats) args argpats)
                  | uu____2389 ->
                      let uu____2403 =
                        let uu____2404 = FStar_Syntax_Print.pat_to_string p in
                        let uu____2405 = FStar_Syntax_Print.term_to_string e in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2404 uu____2405 in
                      failwith uu____2403 in
                match_args [] args argpats))
          | uu____2412 ->
              let uu____2415 =
                let uu____2416 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2417 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2418 =
                  let uu____2419 =
                    FStar_All.pipe_right exps
                      (FStar_List.map FStar_Syntax_Print.term_to_string) in
                  FStar_All.pipe_right uu____2419
                    (FStar_String.concat "\n\t") in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2416 uu____2417 uu____2418 in
              failwith uu____2415 in
        match ((p.FStar_Syntax_Syntax.v), exps) with
        | (FStar_Syntax_Syntax.Pat_disj ps,uu____2426) when
            (FStar_List.length ps) = (FStar_List.length exps) ->
            let ps = FStar_List.map2 aux ps exps in
            FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj ps)
              FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
              p.FStar_Syntax_Syntax.p
        | (uu____2442,e::[]) -> aux p e
        | uu____2445 -> failwith "Unexpected number of patterns"
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty) in
    let mk f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2482 =
      match uu____2482 with
      | (p,i) ->
          let uu____2492 = decorated_pattern_as_term p in
          (match uu____2492 with
           | (vars,te) ->
               let uu____2505 =
                 let uu____2508 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2508) in
               (vars, uu____2505)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____2515 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2523 = mk (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2523)
    | FStar_Syntax_Syntax.Pat_wild x|FStar_Syntax_Syntax.Pat_var x ->
        let uu____2526 = mk (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2526)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2540 =
          let uu____2548 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2548 FStar_List.unzip in
        (match uu____2540 with
         | (vars,args) ->
             let vars = FStar_List.flatten vars in
             let uu____2606 =
               let uu____2607 =
                 let uu____2608 =
                   let uu____2618 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2618, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2608 in
               mk uu____2607 in
             (vars, uu____2606))
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
      | (wp,uu____2647)::[] -> wp
      | uu____2660 ->
          let uu____2666 =
            let uu____2667 =
              let uu____2668 =
                FStar_List.map
                  (fun uu____2672  ->
                     match uu____2672 with
                     | (x,uu____2676) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2668 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2667 in
          failwith uu____2666 in
    let uu____2680 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2680, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2694 = destruct_comp c in
        match uu____2694 with
        | (u,uu____2699,wp) ->
            let uu____2701 =
              let uu____2707 =
                let uu____2708 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2708 in
              [uu____2707] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2701;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2718 =
          let uu____2722 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2723 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2722 uu____2723 in
        match uu____2718 with | (m,uu____2725,uu____2726) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2736 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        match uu____2736 with
        | true  -> FStar_Syntax_Const.effect_Tot_lid
        | uu____2737 ->
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
        let uu____2761 =
          FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name
            c2.FStar_Syntax_Syntax.effect_name in
        match uu____2761 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c1 m lift1 in
            let m2 = lift_comp c2 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2783 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2783 with
             | (a,kwp) ->
                 let uu____2800 = destruct_comp m1 in
                 let uu____2804 = destruct_comp m2 in
                 ((md, a, kwp), uu____2800, uu____2804))
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
            let uu____2852 =
              let uu____2853 =
                let uu____2859 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2859] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2853;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2852
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
          match FStar_Ident.lid_equals mname
                  FStar_Syntax_Const.effect_Tot_lid
          with
          | true  -> FStar_Syntax_Syntax.mk_Total' result (Some u_result)
          | uu____2888 ->
              mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
let subst_lcomp:
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun subst  ->
    fun lc  ->
      let uu___123_2895 = lc in
      let uu____2896 =
        FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___123_2895.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2896;
        FStar_Syntax_Syntax.cflags =
          (uu___123_2895.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2899  ->
             let uu____2900 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst uu____2900)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2904 =
      let uu____2905 = FStar_Syntax_Subst.compress t in
      uu____2905.FStar_Syntax_Syntax.n in
    match uu____2904 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2908 -> true
    | uu____2916 -> false
let return_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun t  ->
      fun v  ->
        let c =
          let uu____2927 =
            let uu____2928 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____2928 in
          match uu____2927 with
          | true  -> FStar_Syntax_Syntax.mk_Total t
          | uu____2929 ->
              let m =
                let uu____2931 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    FStar_Syntax_Const.effect_PURE_lid in
                FStar_Util.must uu____2931 in
              let u_t = env.FStar_TypeChecker_Env.universe_of env t in
              let wp =
                let uu____2935 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
                match uu____2935 with
                | true  -> FStar_Syntax_Syntax.tun
                | uu____2936 ->
                    let uu____2937 =
                      FStar_TypeChecker_Env.wp_signature env
                        FStar_Syntax_Const.effect_PURE_lid in
                    (match uu____2937 with
                     | (a,kwp) ->
                         let k =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (a, t)] kwp in
                         let uu____2943 =
                           let uu____2944 =
                             let uu____2945 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                             let uu____2946 =
                               let uu____2947 = FStar_Syntax_Syntax.as_arg t in
                               let uu____2948 =
                                 let uu____2950 =
                                   FStar_Syntax_Syntax.as_arg v in
                                 [uu____2950] in
                               uu____2947 :: uu____2948 in
                             FStar_Syntax_Syntax.mk_Tm_app uu____2945
                               uu____2946 in
                           uu____2944 (Some (k.FStar_Syntax_Syntax.n))
                             v.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env uu____2943) in
              (mk_comp m) u_t t wp [FStar_Syntax_Syntax.RETURN] in
        (let uu____2956 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         match uu____2956 with
         | true  ->
             let uu____2957 =
               FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos in
             let uu____2958 = FStar_Syntax_Print.term_to_string v in
             let uu____2959 =
               FStar_TypeChecker_Normalize.comp_to_string env c in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2957 uu____2958 uu____2959
         | uu____2960 -> ());
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
          fun uu____2976  ->
            match uu____2976 with
            | (b,lc2) ->
                let lc1 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc2 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc1 lc2 in
                ((let uu____2986 =
                    FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                  match uu____2986 with
                  | true  ->
                      let bstr =
                        match b with
                        | None  -> "none"
                        | Some x -> FStar_Syntax_Print.bv_to_string x in
                      let uu____2989 =
                        match e1opt with
                        | None  -> "None"
                        | Some e -> FStar_Syntax_Print.term_to_string e in
                      let uu____2991 = FStar_Syntax_Print.lcomp_to_string lc1 in
                      let uu____2992 = FStar_Syntax_Print.lcomp_to_string lc2 in
                      FStar_Util.print4
                        "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                        uu____2989 uu____2991 bstr uu____2992
                  | uu____2993 -> ());
                 (let bind_it uu____2997 =
                    let uu____2998 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    match uu____2998 with
                    | true  ->
                        let u_t =
                          env.FStar_TypeChecker_Env.universe_of env
                            lc2.FStar_Syntax_Syntax.res_typ in
                        lax_mk_tot_or_comp_l joined_eff u_t
                          lc2.FStar_Syntax_Syntax.res_typ []
                    | uu____3000 ->
                        let c1 = lc1.FStar_Syntax_Syntax.comp () in
                        let c2 = lc2.FStar_Syntax_Syntax.comp () in
                        ((let uu____3008 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Extreme in
                          match uu____3008 with
                          | true  ->
                              let uu____3009 =
                                match b with
                                | None  -> "none"
                                | Some x -> FStar_Syntax_Print.bv_to_string x in
                              let uu____3011 =
                                FStar_Syntax_Print.lcomp_to_string lc1 in
                              let uu____3012 =
                                FStar_Syntax_Print.comp_to_string c1 in
                              let uu____3013 =
                                FStar_Syntax_Print.lcomp_to_string lc2 in
                              let uu____3014 =
                                FStar_Syntax_Print.comp_to_string c2 in
                              FStar_Util.print5
                                "b=%s,Evaluated %s to %s\n And %s to %s\n"
                                uu____3009 uu____3011 uu____3012 uu____3013
                                uu____3014
                          | uu____3015 -> ());
                         (let try_simplify uu____3022 =
                            let aux uu____3031 =
                              let uu____3032 =
                                FStar_Syntax_Util.is_trivial_wp c1 in
                              match uu____3032 with
                              | true  ->
                                  (match b with
                                   | None  -> Some (c2, "trivial no binder")
                                   | Some uu____3049 ->
                                       let uu____3050 =
                                         FStar_Syntax_Util.is_ml_comp c2 in
                                       (match uu____3050 with
                                        | true  -> Some (c2, "trivial ml")
                                        | uu____3062 -> None))
                              | uu____3067 ->
                                  let uu____3068 =
                                    (FStar_Syntax_Util.is_ml_comp c1) &&
                                      (FStar_Syntax_Util.is_ml_comp c2) in
                                  (match uu____3068 with
                                   | true  -> Some (c2, "both ml")
                                   | uu____3080 -> None) in
                            let subst_c2 reason =
                              match (e1opt, b) with
                              | (Some e,Some x) ->
                                  let uu____3101 =
                                    let uu____3104 =
                                      FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                    (uu____3104, reason) in
                                  Some uu____3101
                              | uu____3107 -> aux () in
                            let uu____3112 =
                              (FStar_Syntax_Util.is_total_comp c1) &&
                                (FStar_Syntax_Util.is_total_comp c2) in
                            match uu____3112 with
                            | true  -> subst_c2 "both total"
                            | uu____3116 ->
                                let uu____3117 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                (match uu____3117 with
                                 | true  ->
                                     let uu____3121 =
                                       let uu____3124 =
                                         FStar_Syntax_Syntax.mk_GTotal
                                           (FStar_Syntax_Util.comp_result c2) in
                                       (uu____3124, "both gtot") in
                                     Some uu____3121
                                 | uu____3127 ->
                                     (match (e1opt, b) with
                                      | (Some e,Some x) ->
                                          let uu____3137 =
                                            (FStar_Syntax_Util.is_total_comp
                                               c1)
                                              &&
                                              (let uu____3138 =
                                                 FStar_Syntax_Syntax.is_null_bv
                                                   x in
                                               Prims.op_Negation uu____3138) in
                                          (match uu____3137 with
                                           | true  ->
                                               subst_c2 "substituted e"
                                           | uu____3142 -> aux ())
                                      | uu____3143 -> aux ())) in
                          let uu____3148 = try_simplify () in
                          match uu____3148 with
                          | Some (c,reason) -> c
                          | None  ->
                              let uu____3158 = lift_and_destruct env c1 c2 in
                              (match uu____3158 with
                               | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                   let bs =
                                     match b with
                                     | None  ->
                                         let uu____3192 =
                                           FStar_Syntax_Syntax.null_binder t1 in
                                         [uu____3192]
                                     | Some x ->
                                         let uu____3194 =
                                           FStar_Syntax_Syntax.mk_binder x in
                                         [uu____3194] in
                                   let mk_lam wp =
                                     FStar_Syntax_Util.abs bs wp
                                       (Some
                                          (FStar_Util.Inr
                                             (FStar_Syntax_Const.effect_Tot_lid,
                                               [FStar_Syntax_Syntax.TOTAL]))) in
                                   let r1 =
                                     (FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_constant
                                           (FStar_Const.Const_range r1)))
                                       None r1 in
                                   let wp_args =
                                     let uu____3221 =
                                       FStar_Syntax_Syntax.as_arg r1 in
                                     let uu____3222 =
                                       let uu____3224 =
                                         FStar_Syntax_Syntax.as_arg t1 in
                                       let uu____3225 =
                                         let uu____3227 =
                                           FStar_Syntax_Syntax.as_arg t2 in
                                         let uu____3228 =
                                           let uu____3230 =
                                             FStar_Syntax_Syntax.as_arg wp1 in
                                           let uu____3231 =
                                             let uu____3233 =
                                               let uu____3234 = mk_lam wp2 in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____3234 in
                                             [uu____3233] in
                                           uu____3230 :: uu____3231 in
                                         uu____3227 :: uu____3228 in
                                       uu____3224 :: uu____3225 in
                                     uu____3221 :: uu____3222 in
                                   let k =
                                     FStar_Syntax_Subst.subst
                                       [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                   let wp =
                                     let uu____3239 =
                                       let uu____3240 =
                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                           [u_t1; u_t2] env md
                                           md.FStar_Syntax_Syntax.bind_wp in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____3240 wp_args in
                                     uu____3239 None
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
              let uu____3289 =
                let uu____3290 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3290 in
              (match uu____3289 with
               | true  -> f
               | uu____3291 ->
                   let uu____3292 = reason () in label uu____3292 r f)
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
            let uu___124_3303 = g in
            let uu____3304 =
              let uu____3305 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3305 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3304;
              FStar_TypeChecker_Env.deferred =
                (uu___124_3303.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___124_3303.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___124_3303.FStar_TypeChecker_Env.implicits)
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
      | uu____3315 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3332 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3336 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          match uu____3336 with
          | true  -> c
          | uu____3339 ->
              (match f with
               | FStar_TypeChecker_Common.Trivial  -> c
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let uu____3343 = FStar_Syntax_Util.is_ml_comp c in
                   (match uu____3343 with
                    | true  -> c
                    | uu____3346 ->
                        let c =
                          FStar_TypeChecker_Normalize.unfold_effect_abbrev
                            env c in
                        let uu____3348 = destruct_comp c in
                        (match uu____3348 with
                         | (u_res_t,res_t,wp) ->
                             let md =
                               FStar_TypeChecker_Env.get_effect_decl env
                                 c.FStar_Syntax_Syntax.effect_name in
                             let wp =
                               let uu____3361 =
                                 let uu____3362 =
                                   FStar_TypeChecker_Env.inst_effect_fun_with
                                     [u_res_t] env md
                                     md.FStar_Syntax_Syntax.assume_p in
                                 let uu____3363 =
                                   let uu____3364 =
                                     FStar_Syntax_Syntax.as_arg res_t in
                                   let uu____3365 =
                                     let uu____3367 =
                                       FStar_Syntax_Syntax.as_arg f in
                                     let uu____3368 =
                                       let uu____3370 =
                                         FStar_Syntax_Syntax.as_arg wp in
                                       [uu____3370] in
                                     uu____3367 :: uu____3368 in
                                   uu____3364 :: uu____3365 in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____3362
                                   uu____3363 in
                               uu____3361 None wp.FStar_Syntax_Syntax.pos in
                             (mk_comp md) u_res_t res_t wp
                               c.FStar_Syntax_Syntax.flags))) in
        let uu___125_3375 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___125_3375.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___125_3375.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___125_3375.FStar_Syntax_Syntax.cflags);
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
            let uu____3402 = FStar_TypeChecker_Rel.is_trivial g0 in
            match uu____3402 with
            | true  -> (lc, g0)
            | uu____3405 ->
                ((let uu____3407 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      FStar_Options.Extreme in
                  match uu____3407 with
                  | true  ->
                      let uu____3408 =
                        FStar_TypeChecker_Normalize.term_to_string env e in
                      let uu____3409 =
                        FStar_TypeChecker_Rel.guard_to_string env g0 in
                      FStar_Util.print2
                        "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                        uu____3408 uu____3409
                  | uu____3410 -> ());
                 (let flags =
                    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                      (FStar_List.collect
                         (fun uu___92_3415  ->
                            match uu___92_3415 with
                            | FStar_Syntax_Syntax.RETURN 
                              |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                [FStar_Syntax_Syntax.PARTIAL_RETURN]
                            | uu____3417 -> [])) in
                  let strengthen uu____3423 =
                    let c = lc.FStar_Syntax_Syntax.comp () in
                    match env.FStar_TypeChecker_Env.lax with
                    | true  -> c
                    | uu____3429 ->
                        let g0 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                        let uu____3431 = FStar_TypeChecker_Rel.guard_form g0 in
                        (match uu____3431 with
                         | FStar_TypeChecker_Common.Trivial  -> c
                         | FStar_TypeChecker_Common.NonTrivial f ->
                             let c =
                               let uu____3438 =
                                 (FStar_Syntax_Util.is_pure_or_ghost_comp c)
                                   &&
                                   (let uu____3439 =
                                      FStar_Syntax_Util.is_partial_return c in
                                    Prims.op_Negation uu____3439) in
                               match uu____3438 with
                               | true  ->
                                   let x =
                                     FStar_Syntax_Syntax.gen_bv
                                       "strengthen_pre_x" None
                                       (FStar_Syntax_Util.comp_result c) in
                                   let xret =
                                     let uu____3446 =
                                       let uu____3447 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       return_value env
                                         x.FStar_Syntax_Syntax.sort
                                         uu____3447 in
                                     FStar_Syntax_Util.comp_set_flags
                                       uu____3446
                                       [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                                   let lc =
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (Some e)
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       ((Some x),
                                         (FStar_Syntax_Util.lcomp_of_comp
                                            xret)) in
                                   lc.FStar_Syntax_Syntax.comp ()
                               | uu____3450 -> c in
                             ((let uu____3452 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme in
                               match uu____3452 with
                               | true  ->
                                   let uu____3453 =
                                     FStar_TypeChecker_Normalize.term_to_string
                                       env e in
                                   let uu____3454 =
                                     FStar_TypeChecker_Normalize.term_to_string
                                       env f in
                                   FStar_Util.print2
                                     "-------------Strengthening pre-condition of term %s with guard %s\n"
                                     uu____3453 uu____3454
                               | uu____3455 -> ());
                              (let c =
                                 FStar_TypeChecker_Normalize.unfold_effect_abbrev
                                   env c in
                               let uu____3457 = destruct_comp c in
                               match uu____3457 with
                               | (u_res_t,res_t,wp) ->
                                   let md =
                                     FStar_TypeChecker_Env.get_effect_decl
                                       env c.FStar_Syntax_Syntax.effect_name in
                                   let wp =
                                     let uu____3470 =
                                       let uu____3471 =
                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                           [u_res_t] env md
                                           md.FStar_Syntax_Syntax.assert_p in
                                       let uu____3472 =
                                         let uu____3473 =
                                           FStar_Syntax_Syntax.as_arg res_t in
                                         let uu____3474 =
                                           let uu____3476 =
                                             let uu____3477 =
                                               let uu____3478 =
                                                 FStar_TypeChecker_Env.get_range
                                                   env in
                                               label_opt env reason
                                                 uu____3478 f in
                                             FStar_All.pipe_left
                                               FStar_Syntax_Syntax.as_arg
                                               uu____3477 in
                                           let uu____3479 =
                                             let uu____3481 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____3481] in
                                           uu____3476 :: uu____3479 in
                                         uu____3473 :: uu____3474 in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____3471 uu____3472 in
                                     uu____3470 None
                                       wp.FStar_Syntax_Syntax.pos in
                                   ((let uu____3487 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme in
                                     match uu____3487 with
                                     | true  ->
                                         let uu____3488 =
                                           FStar_Syntax_Print.term_to_string
                                             wp in
                                         FStar_Util.print1
                                           "-------------Strengthened pre-condition is %s\n"
                                           uu____3488
                                     | uu____3489 -> ());
                                    (let c2 =
                                       (mk_comp md) u_res_t res_t wp flags in
                                     c2))))) in
                  let uu____3491 =
                    let uu___126_3492 = lc in
                    let uu____3493 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc.FStar_Syntax_Syntax.eff_name in
                    let uu____3494 =
                      let uu____3496 =
                        (FStar_Syntax_Util.is_pure_lcomp lc) &&
                          (let uu____3497 =
                             FStar_Syntax_Util.is_function_typ
                               lc.FStar_Syntax_Syntax.res_typ in
                           FStar_All.pipe_left Prims.op_Negation uu____3497) in
                      match uu____3496 with
                      | true  -> flags
                      | uu____3499 -> [] in
                    {
                      FStar_Syntax_Syntax.eff_name = uu____3493;
                      FStar_Syntax_Syntax.res_typ =
                        (uu___126_3492.FStar_Syntax_Syntax.res_typ);
                      FStar_Syntax_Syntax.cflags = uu____3494;
                      FStar_Syntax_Syntax.comp = strengthen
                    } in
                  (uu____3491,
                    (let uu___127_3500 = g0 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___127_3500.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___127_3500.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___127_3500.FStar_TypeChecker_Env.implicits)
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
        let uu____3515 =
          let uu____3518 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3519 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3518, uu____3519) in
        match uu____3515 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3528 =
                let uu____3529 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3530 =
                  let uu____3531 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3532 =
                    let uu____3534 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3534] in
                  uu____3531 :: uu____3532 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3529 uu____3530 in
              uu____3528 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3542 =
                let uu____3543 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3544 =
                  let uu____3545 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3546 =
                    let uu____3548 =
                      let uu____3549 =
                        FStar_Syntax_Util.mk_eq res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3549 in
                    let uu____3550 =
                      let uu____3552 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3552] in
                    uu____3548 :: uu____3550 in
                  uu____3545 :: uu____3546 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3543 uu____3544 in
              uu____3542 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3560 =
                let uu____3561 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3562 =
                  let uu____3563 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3564 =
                    let uu____3566 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3567 =
                      let uu____3569 =
                        let uu____3570 =
                          let uu____3571 =
                            let uu____3575 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3575] in
                          FStar_Syntax_Util.abs uu____3571 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3570 in
                      [uu____3569] in
                    uu____3566 :: uu____3567 in
                  uu____3563 :: uu____3564 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3561 uu____3562 in
              uu____3560 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              (mk_comp md_pure) u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3591 = FStar_TypeChecker_Env.get_range env in
              bind uu____3591 env None (FStar_Syntax_Util.lcomp_of_comp comp)
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
          let comp uu____3609 =
            let uu____3610 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            match uu____3610 with
            | true  ->
                let u_t =
                  env.FStar_TypeChecker_Env.universe_of env
                    lcomp_then.FStar_Syntax_Syntax.res_typ in
                lax_mk_tot_or_comp_l joined_eff u_t
                  lcomp_then.FStar_Syntax_Syntax.res_typ []
            | uu____3612 ->
                let uu____3613 =
                  let uu____3626 = lcomp_then.FStar_Syntax_Syntax.comp () in
                  let uu____3627 = lcomp_else.FStar_Syntax_Syntax.comp () in
                  lift_and_destruct env uu____3626 uu____3627 in
                (match uu____3613 with
                 | ((md,uu____3629,uu____3630),(u_res_t,res_t,wp_then),
                    (uu____3634,uu____3635,wp_else)) ->
                     let ifthenelse md res_t g wp_t wp_e =
                       let uu____3664 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos in
                       let uu____3665 =
                         let uu____3666 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md
                             md.FStar_Syntax_Syntax.if_then_else in
                         let uu____3667 =
                           let uu____3668 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____3669 =
                             let uu____3671 = FStar_Syntax_Syntax.as_arg g in
                             let uu____3672 =
                               let uu____3674 =
                                 FStar_Syntax_Syntax.as_arg wp_t in
                               let uu____3675 =
                                 let uu____3677 =
                                   FStar_Syntax_Syntax.as_arg wp_e in
                                 [uu____3677] in
                               uu____3674 :: uu____3675 in
                             uu____3671 :: uu____3672 in
                           uu____3668 :: uu____3669 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3666 uu____3667 in
                       uu____3665 None uu____3664 in
                     let wp = ifthenelse md res_t guard wp_then wp_else in
                     let uu____3685 =
                       let uu____3686 = FStar_Options.split_cases () in
                       uu____3686 > (Prims.parse_int "0") in
                     (match uu____3685 with
                      | true  ->
                          let comp = (mk_comp md) u_res_t res_t wp [] in
                          add_equality_to_post_condition env comp res_t
                      | uu____3688 ->
                          let wp =
                            let uu____3692 =
                              let uu____3693 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp in
                              let uu____3694 =
                                let uu____3695 =
                                  FStar_Syntax_Syntax.as_arg res_t in
                                let uu____3696 =
                                  let uu____3698 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3698] in
                                uu____3695 :: uu____3696 in
                              FStar_Syntax_Syntax.mk_Tm_app uu____3693
                                uu____3694 in
                            uu____3692 None wp.FStar_Syntax_Syntax.pos in
                          (mk_comp md) u_res_t res_t wp [])) in
          let uu____3703 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3703;
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
      let uu____3710 =
        let uu____3711 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3711 in
      FStar_Syntax_Syntax.fvar uu____3710 FStar_Syntax_Syntax.Delta_constant
        None
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
               fun uu____3731  ->
                 match uu____3731 with
                 | (uu____3734,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3739 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3741 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          match uu____3741 with
          | true  -> lax_mk_tot_or_comp_l eff u_res_t res_t []
          | uu____3742 ->
              let ifthenelse md res_t g wp_t wp_e =
                let uu____3761 =
                  FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                    wp_e.FStar_Syntax_Syntax.pos in
                let uu____3762 =
                  let uu____3763 =
                    FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                      md md.FStar_Syntax_Syntax.if_then_else in
                  let uu____3764 =
                    let uu____3765 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3766 =
                      let uu____3768 = FStar_Syntax_Syntax.as_arg g in
                      let uu____3769 =
                        let uu____3771 = FStar_Syntax_Syntax.as_arg wp_t in
                        let uu____3772 =
                          let uu____3774 = FStar_Syntax_Syntax.as_arg wp_e in
                          [uu____3774] in
                        uu____3771 :: uu____3772 in
                      uu____3768 :: uu____3769 in
                    uu____3765 :: uu____3766 in
                  FStar_Syntax_Syntax.mk_Tm_app uu____3763 uu____3764 in
                uu____3762 None uu____3761 in
              let default_case =
                let post_k =
                  let uu____3783 =
                    let uu____3787 = FStar_Syntax_Syntax.null_binder res_t in
                    [uu____3787] in
                  let uu____3788 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                  FStar_Syntax_Util.arrow uu____3783 uu____3788 in
                let kwp =
                  let uu____3794 =
                    let uu____3798 = FStar_Syntax_Syntax.null_binder post_k in
                    [uu____3798] in
                  let uu____3799 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                  FStar_Syntax_Util.arrow uu____3794 uu____3799 in
                let post = FStar_Syntax_Syntax.new_bv None post_k in
                let wp =
                  let uu____3804 =
                    let uu____3808 = FStar_Syntax_Syntax.mk_binder post in
                    [uu____3808] in
                  let uu____3809 =
                    let uu____3810 =
                      let uu____3813 = FStar_TypeChecker_Env.get_range env in
                      label FStar_TypeChecker_Err.exhaustiveness_check
                        uu____3813 in
                    let uu____3814 =
                      fvar_const env FStar_Syntax_Const.false_lid in
                    FStar_All.pipe_left uu____3810 uu____3814 in
                  FStar_Syntax_Util.abs uu____3804 uu____3809
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
                  (fun uu____3828  ->
                     fun celse  ->
                       match uu____3828 with
                       | (g,cthen) ->
                           let uu____3834 =
                             let uu____3847 =
                               cthen.FStar_Syntax_Syntax.comp () in
                             lift_and_destruct env uu____3847 celse in
                           (match uu____3834 with
                            | ((md,uu____3849,uu____3850),(uu____3851,uu____3852,wp_then),
                               (uu____3854,uu____3855,wp_else)) ->
                                let uu____3866 =
                                  ifthenelse md res_t g wp_then wp_else in
                                (mk_comp md) u_res_t res_t uu____3866 []))
                  lcases default_case in
              let uu____3867 =
                let uu____3868 = FStar_Options.split_cases () in
                uu____3868 > (Prims.parse_int "0") in
              (match uu____3867 with
               | true  -> add_equality_to_post_condition env comp res_t
               | uu____3869 ->
                   let comp =
                     FStar_TypeChecker_Normalize.comp_to_comp_typ env comp in
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       comp.FStar_Syntax_Syntax.effect_name in
                   let uu____3872 = destruct_comp comp in
                   (match uu____3872 with
                    | (uu____3876,uu____3877,wp) ->
                        let wp =
                          let uu____3882 =
                            let uu____3883 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.ite_wp in
                            let uu____3884 =
                              let uu____3885 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3886 =
                                let uu____3888 =
                                  FStar_Syntax_Syntax.as_arg wp in
                                [uu____3888] in
                              uu____3885 :: uu____3886 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3883
                              uu____3884 in
                          uu____3882 None wp.FStar_Syntax_Syntax.pos in
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
        let close uu____3909 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3913 = FStar_Syntax_Util.is_ml_comp c in
          match uu____3913 with
          | true  -> c
          | uu____3916 ->
              let uu____3917 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
              (match uu____3917 with
               | true  -> c
               | uu____3920 ->
                   let close_wp u_res md res_t bvs wp0 =
                     FStar_List.fold_right
                       (fun x  ->
                          fun wp  ->
                            let bs =
                              let uu____3949 =
                                FStar_Syntax_Syntax.mk_binder x in
                              [uu____3949] in
                            let us =
                              let uu____3952 =
                                let uu____3954 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    x.FStar_Syntax_Syntax.sort in
                                [uu____3954] in
                              u_res :: uu____3952 in
                            let wp =
                              FStar_Syntax_Util.abs bs wp
                                (Some
                                   (FStar_Util.Inr
                                      (FStar_Syntax_Const.effect_Tot_lid,
                                        [FStar_Syntax_Syntax.TOTAL]))) in
                            let uu____3965 =
                              let uu____3966 =
                                FStar_TypeChecker_Env.inst_effect_fun_with us
                                  env md md.FStar_Syntax_Syntax.close_wp in
                              let uu____3967 =
                                let uu____3968 =
                                  FStar_Syntax_Syntax.as_arg res_t in
                                let uu____3969 =
                                  let uu____3971 =
                                    FStar_Syntax_Syntax.as_arg
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____3972 =
                                    let uu____3974 =
                                      FStar_Syntax_Syntax.as_arg wp in
                                    [uu____3974] in
                                  uu____3971 :: uu____3972 in
                                uu____3968 :: uu____3969 in
                              FStar_Syntax_Syntax.mk_Tm_app uu____3966
                                uu____3967 in
                            uu____3965 None wp0.FStar_Syntax_Syntax.pos) bvs
                       wp0 in
                   let c =
                     FStar_TypeChecker_Normalize.unfold_effect_abbrev env c in
                   let uu____3980 = destruct_comp c in
                   (match uu____3980 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c.FStar_Syntax_Syntax.effect_name in
                        let wp = close_wp u_res_t md res_t bvs wp in
                        (mk_comp md) u_res_t c.FStar_Syntax_Syntax.result_typ
                          wp c.FStar_Syntax_Syntax.flags)) in
        let uu___128_3991 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___128_3991.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___128_3991.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___128_3991.FStar_Syntax_Syntax.cflags);
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
        let refine uu____4006 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4010 =
            (let uu____4011 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4011) || env.FStar_TypeChecker_Env.lax in
          match uu____4010 with
          | true  -> c
          | uu____4014 ->
              let uu____4015 = FStar_Syntax_Util.is_partial_return c in
              (match uu____4015 with
               | true  -> c
               | uu____4018 ->
                   let uu____4019 =
                     (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
                       (let uu____4020 =
                          FStar_TypeChecker_Env.lid_exists env
                            FStar_Syntax_Const.effect_GTot_lid in
                        Prims.op_Negation uu____4020) in
                   (match uu____4019 with
                    | true  ->
                        let uu____4023 =
                          let uu____4024 =
                            FStar_Range.string_of_range
                              e.FStar_Syntax_Syntax.pos in
                          let uu____4025 =
                            FStar_Syntax_Print.term_to_string e in
                          FStar_Util.format2 "%s: %s\n" uu____4024 uu____4025 in
                        failwith uu____4023
                    | uu____4028 ->
                        let c =
                          FStar_TypeChecker_Normalize.unfold_effect_abbrev
                            env c in
                        let t = c.FStar_Syntax_Syntax.result_typ in
                        let c = FStar_Syntax_Syntax.mk_Comp c in
                        let x =
                          FStar_Syntax_Syntax.new_bv
                            (Some (t.FStar_Syntax_Syntax.pos)) t in
                        let xexp = FStar_Syntax_Syntax.bv_to_name x in
                        let ret =
                          let uu____4037 =
                            let uu____4040 = return_value env t xexp in
                            FStar_Syntax_Util.comp_set_flags uu____4040
                              [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                            uu____4037 in
                        let eq = FStar_Syntax_Util.mk_eq t t xexp e in
                        let eq_ret =
                          weaken_precondition env ret
                            (FStar_TypeChecker_Common.NonTrivial eq) in
                        let c =
                          let uu____4054 =
                            let uu____4055 =
                              let uu____4060 =
                                bind e.FStar_Syntax_Syntax.pos env None
                                  (FStar_Syntax_Util.lcomp_of_comp c)
                                  ((Some x), eq_ret) in
                              uu____4060.FStar_Syntax_Syntax.comp in
                            uu____4055 () in
                          FStar_Syntax_Util.comp_set_flags uu____4054
                            (FStar_Syntax_Syntax.PARTIAL_RETURN ::
                            (FStar_Syntax_Util.comp_flags c)) in
                        c)) in
        let flags =
          let uu____4064 =
            ((let uu____4065 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4065) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4066 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4066) in
          match uu____4064 with
          | true  -> FStar_Syntax_Syntax.PARTIAL_RETURN ::
              (lc.FStar_Syntax_Syntax.cflags)
          | uu____4068 -> lc.FStar_Syntax_Syntax.cflags in
        let uu___129_4069 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___129_4069.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___129_4069.FStar_Syntax_Syntax.res_typ);
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
          let uu____4088 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4088 with
          | None  ->
              let uu____4093 =
                let uu____4094 =
                  let uu____4097 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4098 = FStar_TypeChecker_Env.get_range env in
                  (uu____4097, uu____4098) in
                FStar_Errors.Error uu____4094 in
              Prims.raise uu____4093
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
          let uu____4119 =
            let uu____4120 = FStar_Syntax_Subst.compress t in
            uu____4120.FStar_Syntax_Syntax.n in
          match uu____4119 with
          | FStar_Syntax_Syntax.Tm_type uu____4125 ->
              let uu____4126 =
                let uu____4127 =
                  FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
                uu____4127.FStar_Syntax_Syntax.n in
              (match uu____4126 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.bool_lid
                   ->
                   let uu____4133 =
                     FStar_TypeChecker_Env.lookup_lid env
                       FStar_Syntax_Const.b2t_lid in
                   let b2t =
                     FStar_Syntax_Syntax.fvar
                       (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                          e.FStar_Syntax_Syntax.pos)
                       (FStar_Syntax_Syntax.Delta_defined_at_level
                          (Prims.parse_int "1")) None in
                   let lc =
                     let uu____4138 =
                       let uu____4139 =
                         let uu____4140 =
                           FStar_Syntax_Syntax.mk_Total
                             FStar_Syntax_Util.ktype0 in
                         FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                           uu____4140 in
                       (None, uu____4139) in
                     bind e.FStar_Syntax_Syntax.pos env (Some e) lc
                       uu____4138 in
                   let e =
                     let uu____4149 =
                       let uu____4150 =
                         let uu____4151 = FStar_Syntax_Syntax.as_arg e in
                         [uu____4151] in
                       FStar_Syntax_Syntax.mk_Tm_app b2t uu____4150 in
                     uu____4149
                       (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                       e.FStar_Syntax_Syntax.pos in
                   (e, lc)
               | uu____4158 -> (e, lc))
          | uu____4159 -> (e, lc)
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
            match env.FStar_TypeChecker_Env.use_eq with
            | true  ->
                let uu____4185 =
                  FStar_TypeChecker_Rel.try_teq env
                    lc.FStar_Syntax_Syntax.res_typ t in
                (uu____4185, false)
            | uu____4188 ->
                let uu____4189 =
                  FStar_TypeChecker_Rel.try_subtype env
                    lc.FStar_Syntax_Syntax.res_typ t in
                (uu____4189, true) in
          match gopt with
          | (None ,uu____4195) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___130_4198 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___130_4198.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___130_4198.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___130_4198.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard) ->
              let uu____4202 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4202 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc =
                     let uu___131_4207 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___131_4207.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___131_4207.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___131_4207.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g =
                     let uu___132_4210 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___132_4210.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___132_4210.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___132_4210.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4216 =
                     let uu____4217 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     match uu____4217 with
                     | true  -> lc.FStar_Syntax_Syntax.comp ()
                     | uu____4220 ->
                         let f =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.Eager_unfolding;
                             FStar_TypeChecker_Normalize.Simplify] env f in
                         let uu____4222 =
                           let uu____4223 = FStar_Syntax_Subst.compress f in
                           uu____4223.FStar_Syntax_Syntax.n in
                         (match uu____4222 with
                          | FStar_Syntax_Syntax.Tm_abs
                              (uu____4228,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4230;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4231;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4232;_},uu____4233)
                              when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.true_lid
                              ->
                              let lc =
                                let uu___133_4257 = lc in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___133_4257.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___133_4257.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___133_4257.FStar_Syntax_Syntax.comp)
                                } in
                              lc.FStar_Syntax_Syntax.comp ()
                          | uu____4258 ->
                              let c = lc.FStar_Syntax_Syntax.comp () in
                              ((let uu____4263 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    FStar_Options.Extreme in
                                match uu____4263 with
                                | true  ->
                                    let uu____4264 =
                                      FStar_TypeChecker_Normalize.term_to_string
                                        env lc.FStar_Syntax_Syntax.res_typ in
                                    let uu____4265 =
                                      FStar_TypeChecker_Normalize.term_to_string
                                        env t in
                                    let uu____4266 =
                                      FStar_TypeChecker_Normalize.comp_to_string
                                        env c in
                                    let uu____4267 =
                                      FStar_TypeChecker_Normalize.term_to_string
                                        env f in
                                    FStar_Util.print4
                                      "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                      uu____4264 uu____4265 uu____4266
                                      uu____4267
                                | uu____4268 -> ());
                               (let ct =
                                  FStar_TypeChecker_Normalize.unfold_effect_abbrev
                                    env c in
                                let uu____4270 =
                                  FStar_TypeChecker_Env.wp_signature env
                                    FStar_Syntax_Const.effect_PURE_lid in
                                match uu____4270 with
                                | (a,kwp) ->
                                    let k =
                                      FStar_Syntax_Subst.subst
                                        [FStar_Syntax_Syntax.NT (a, t)] kwp in
                                    let md =
                                      FStar_TypeChecker_Env.get_effect_decl
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name in
                                    let x =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (t.FStar_Syntax_Syntax.pos)) t in
                                    let xexp =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____4281 = destruct_comp ct in
                                    (match uu____4281 with
                                     | (u_t,uu____4288,uu____4289) ->
                                         let wp =
                                           let uu____4293 =
                                             let uu____4294 =
                                               FStar_TypeChecker_Env.inst_effect_fun_with
                                                 [u_t] env md
                                                 md.FStar_Syntax_Syntax.ret_wp in
                                             let uu____4295 =
                                               let uu____4296 =
                                                 FStar_Syntax_Syntax.as_arg t in
                                               let uu____4297 =
                                                 let uu____4299 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     xexp in
                                                 [uu____4299] in
                                               uu____4296 :: uu____4297 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____4294 uu____4295 in
                                           uu____4293
                                             (Some (k.FStar_Syntax_Syntax.n))
                                             xexp.FStar_Syntax_Syntax.pos in
                                         let cret =
                                           let uu____4305 =
                                             (mk_comp md) u_t t wp
                                               [FStar_Syntax_Syntax.RETURN] in
                                           FStar_All.pipe_left
                                             FStar_Syntax_Util.lcomp_of_comp
                                             uu____4305 in
                                         let guard =
                                           match apply_guard with
                                           | true  ->
                                               let uu____4315 =
                                                 let uu____4316 =
                                                   let uu____4317 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       xexp in
                                                   [uu____4317] in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   f uu____4316 in
                                               uu____4315
                                                 (Some
                                                    (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                                 f.FStar_Syntax_Syntax.pos
                                           | uu____4322 -> f in
                                         let uu____4323 =
                                           let uu____4326 =
                                             FStar_All.pipe_left
                                               (fun _0_28  -> Some _0_28)
                                               (FStar_TypeChecker_Err.subtyping_failed
                                                  env
                                                  lc.FStar_Syntax_Syntax.res_typ
                                                  t) in
                                           let uu____4337 =
                                             FStar_TypeChecker_Env.set_range
                                               env e.FStar_Syntax_Syntax.pos in
                                           let uu____4338 =
                                             FStar_All.pipe_left
                                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                               (FStar_TypeChecker_Common.NonTrivial
                                                  guard) in
                                           strengthen_precondition uu____4326
                                             uu____4337 e cret uu____4338 in
                                         (match uu____4323 with
                                          | (eq_ret,_trivial_so_ok_to_discard)
                                              ->
                                              let x =
                                                let uu___134_4344 = x in
                                                {
                                                  FStar_Syntax_Syntax.ppname
                                                    =
                                                    (uu___134_4344.FStar_Syntax_Syntax.ppname);
                                                  FStar_Syntax_Syntax.index =
                                                    (uu___134_4344.FStar_Syntax_Syntax.index);
                                                  FStar_Syntax_Syntax.sort =
                                                    (lc.FStar_Syntax_Syntax.res_typ)
                                                } in
                                              let c =
                                                let uu____4346 =
                                                  let uu____4347 =
                                                    FStar_Syntax_Syntax.mk_Comp
                                                      ct in
                                                  FStar_All.pipe_left
                                                    FStar_Syntax_Util.lcomp_of_comp
                                                    uu____4347 in
                                                bind
                                                  e.FStar_Syntax_Syntax.pos
                                                  env (Some e) uu____4346
                                                  ((Some x), eq_ret) in
                                              let c =
                                                c.FStar_Syntax_Syntax.comp () in
                                              ((let uu____4357 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    FStar_Options.Extreme in
                                                match uu____4357 with
                                                | true  ->
                                                    let uu____4358 =
                                                      FStar_TypeChecker_Normalize.comp_to_string
                                                        env c in
                                                    FStar_Util.print1
                                                      "Strengthened to %s\n"
                                                      uu____4358
                                                | uu____4359 -> ());
                                               c)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___93_4364  ->
                             match uu___93_4364 with
                             | FStar_Syntax_Syntax.RETURN 
                               |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4366 -> [])) in
                   let lc =
                     let uu___135_4368 = lc in
                     let uu____4369 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4369;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g =
                     let uu___136_4371 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___136_4371.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___136_4371.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___136_4371.FStar_TypeChecker_Env.implicits)
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
        let uu____4391 =
          let uu____4392 =
            let uu____4393 =
              let uu____4394 =
                let uu____4395 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4395 in
              [uu____4394] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4393 in
          uu____4392 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4391 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4404 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      match uu____4404 with
      | true  -> (None, (FStar_Syntax_Util.comp_result comp))
      | uu____4411 ->
          (match comp.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.GTotal _|FStar_Syntax_Syntax.Total _ ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Comp ct ->
               (match (FStar_Ident.lid_equals
                         ct.FStar_Syntax_Syntax.effect_name
                         FStar_Syntax_Const.effect_Pure_lid)
                        ||
                        (FStar_Ident.lid_equals
                           ct.FStar_Syntax_Syntax.effect_name
                           FStar_Syntax_Const.effect_Ghost_lid)
                with
                | true  ->
                    (match ct.FStar_Syntax_Syntax.effect_args with
                     | (req,uu____4428)::(ens,uu____4430)::uu____4431 ->
                         let uu____4453 =
                           let uu____4455 = norm req in Some uu____4455 in
                         let uu____4456 =
                           let uu____4457 =
                             mk_post_type ct.FStar_Syntax_Syntax.result_typ
                               ens in
                           FStar_All.pipe_left norm uu____4457 in
                         (uu____4453, uu____4456)
                     | uu____4459 ->
                         let uu____4465 =
                           let uu____4466 =
                             let uu____4469 =
                               let uu____4470 =
                                 FStar_Syntax_Print.comp_to_string comp in
                               FStar_Util.format1
                                 "Effect constructor is not fully applied; got %s"
                                 uu____4470 in
                             (uu____4469, (comp.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____4466 in
                         Prims.raise uu____4465)
                | uu____4474 ->
                    let ct =
                      FStar_TypeChecker_Normalize.unfold_effect_abbrev env
                        comp in
                    (match ct.FStar_Syntax_Syntax.effect_args with
                     | (wp,uu____4480)::uu____4481 ->
                         let uu____4495 =
                           FStar_TypeChecker_Env.lookup_lid env
                             FStar_Syntax_Const.as_requires in
                         (match uu____4495 with
                          | (us_r,uu____4502) ->
                              let uu____4503 =
                                FStar_TypeChecker_Env.lookup_lid env
                                  FStar_Syntax_Const.as_ensures in
                              (match uu____4503 with
                               | (us_e,uu____4510) ->
                                   let r =
                                     (ct.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                                   let as_req =
                                     let uu____4513 =
                                       FStar_Syntax_Syntax.fvar
                                         (FStar_Ident.set_lid_range
                                            FStar_Syntax_Const.as_requires r)
                                         FStar_Syntax_Syntax.Delta_equational
                                         None in
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       uu____4513 us_r in
                                   let as_ens =
                                     let uu____4515 =
                                       FStar_Syntax_Syntax.fvar
                                         (FStar_Ident.set_lid_range
                                            FStar_Syntax_Const.as_ensures r)
                                         FStar_Syntax_Syntax.Delta_equational
                                         None in
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       uu____4515 us_e in
                                   let req =
                                     let uu____4519 =
                                       let uu____4520 =
                                         let uu____4521 =
                                           let uu____4528 =
                                             FStar_Syntax_Syntax.as_arg wp in
                                           [uu____4528] in
                                         ((ct.FStar_Syntax_Syntax.result_typ),
                                           (Some FStar_Syntax_Syntax.imp_tag))
                                           :: uu____4521 in
                                       FStar_Syntax_Syntax.mk_Tm_app as_req
                                         uu____4520 in
                                     uu____4519
                                       (Some
                                          (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                       (ct.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                                   let ens =
                                     let uu____4544 =
                                       let uu____4545 =
                                         let uu____4546 =
                                           let uu____4553 =
                                             FStar_Syntax_Syntax.as_arg wp in
                                           [uu____4553] in
                                         ((ct.FStar_Syntax_Syntax.result_typ),
                                           (Some FStar_Syntax_Syntax.imp_tag))
                                           :: uu____4546 in
                                       FStar_Syntax_Syntax.mk_Tm_app as_ens
                                         uu____4545 in
                                     uu____4544 None
                                       (ct.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                                   let uu____4566 =
                                     let uu____4568 = norm req in
                                     Some uu____4568 in
                                   let uu____4569 =
                                     let uu____4570 =
                                       mk_post_type
                                         ct.FStar_Syntax_Syntax.result_typ
                                         ens in
                                     norm uu____4570 in
                                   (uu____4566, uu____4569)))
                     | uu____4572 -> failwith "Impossible")))
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
        match Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        with
        | true  -> (e, torig, FStar_TypeChecker_Rel.trivial_guard)
        | uu____4597 ->
            let number_of_implicits t =
              let uu____4602 = FStar_Syntax_Util.arrow_formals t in
              match uu____4602 with
              | (formals,uu____4611) ->
                  let n_implicits =
                    let uu____4623 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____4660  ->
                              match uu____4660 with
                              | (uu____4664,imp) ->
                                  (imp = None) ||
                                    (imp =
                                       (Some FStar_Syntax_Syntax.Equality)))) in
                    match uu____4623 with
                    | None  -> FStar_List.length formals
                    | Some (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits in
                  n_implicits in
            let inst_n_binders t =
              let uu____4736 = FStar_TypeChecker_Env.expected_typ env in
              match uu____4736 with
              | None  -> None
              | Some expected_t ->
                  let n_expected = number_of_implicits expected_t in
                  let n_available = number_of_implicits t in
                  (match n_available < n_expected with
                   | true  ->
                       let uu____4750 =
                         let uu____4751 =
                           let uu____4754 =
                             let uu____4755 =
                               FStar_Util.string_of_int n_expected in
                             let uu____4759 =
                               FStar_Syntax_Print.term_to_string e in
                             let uu____4760 =
                               FStar_Util.string_of_int n_available in
                             FStar_Util.format3
                               "Expected a term with %s implicit arguments, but %s has only %s"
                               uu____4755 uu____4759 uu____4760 in
                           let uu____4764 =
                             FStar_TypeChecker_Env.get_range env in
                           (uu____4754, uu____4764) in
                         FStar_Errors.Error uu____4751 in
                       Prims.raise uu____4750
                   | uu____4766 -> Some (n_available - n_expected)) in
            let decr_inst uu___94_4777 =
              match uu___94_4777 with
              | None  -> None
              | Some i -> Some (i - (Prims.parse_int "1")) in
            (match torig.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____4796 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____4796 with
                  | (bs,c) ->
                      let rec aux subst inst_n bs =
                        match (inst_n, bs) with
                        | (Some _0_29,uu____4857) when
                            _0_29 = (Prims.parse_int "0") ->
                            ([], bs, subst,
                              FStar_TypeChecker_Rel.trivial_guard)
                        | (uu____4879,(x,Some (FStar_Syntax_Syntax.Implicit
                                       dot))::rest)
                            ->
                            let t =
                              FStar_Syntax_Subst.subst subst
                                x.FStar_Syntax_Syntax.sort in
                            let uu____4898 =
                              new_implicit_var
                                "Instantiation of implicit argument"
                                e.FStar_Syntax_Syntax.pos env t in
                            (match uu____4898 with
                             | (v,uu____4919,g) ->
                                 let subst = (FStar_Syntax_Syntax.NT (x, v))
                                   :: subst in
                                 let uu____4929 =
                                   aux subst (decr_inst inst_n) rest in
                                 (match uu____4929 with
                                  | (args,bs,subst,g') ->
                                      let uu____4978 =
                                        FStar_TypeChecker_Rel.conj_guard g g' in
                                      (((v,
                                          (Some
                                             (FStar_Syntax_Syntax.Implicit
                                                dot))) :: args), bs, subst,
                                        uu____4978)))
                        | (uu____4992,bs) ->
                            ([], bs, subst,
                              FStar_TypeChecker_Rel.trivial_guard) in
                      let uu____5016 =
                        let uu____5030 = inst_n_binders t in
                        aux [] uu____5030 bs in
                      (match uu____5016 with
                       | (args,bs,subst,guard) ->
                           (match (args, bs) with
                            | ([],uu____5068) -> (e, torig, guard)
                            | (uu____5084,[]) when
                                let uu____5100 =
                                  FStar_Syntax_Util.is_total_comp c in
                                Prims.op_Negation uu____5100 ->
                                (e, torig,
                                  FStar_TypeChecker_Rel.trivial_guard)
                            | uu____5101 ->
                                let t =
                                  match bs with
                                  | [] -> FStar_Syntax_Util.comp_result c
                                  | uu____5120 ->
                                      FStar_Syntax_Util.arrow bs c in
                                let t = FStar_Syntax_Subst.subst subst t in
                                let e =
                                  (FStar_Syntax_Syntax.mk_Tm_app e args)
                                    (Some (t.FStar_Syntax_Syntax.n))
                                    e.FStar_Syntax_Syntax.pos in
                                (e, t, guard))))
             | uu____5135 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs univs =
  let uu____5147 =
    let uu____5149 = FStar_Util.set_elements univs in
    FStar_All.pipe_right uu____5149
      (FStar_List.map
         (fun u  ->
            let uu____5159 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____5159 FStar_Util.string_of_int)) in
  FStar_All.pipe_right uu____5147 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5171 = FStar_Util.set_is_empty x in
      match uu____5171 with
      | true  -> []
      | uu____5173 ->
          let s =
            let uu____5176 =
              let uu____5178 = FStar_TypeChecker_Env.univ_vars env in
              FStar_Util.set_difference x uu____5178 in
            FStar_All.pipe_right uu____5176 FStar_Util.set_elements in
          ((let uu____5183 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Gen") in
            match uu____5183 with
            | true  ->
                let uu____5184 =
                  let uu____5185 = FStar_TypeChecker_Env.univ_vars env in
                  string_of_univs uu____5185 in
                FStar_Util.print1 "univ_vars in env: %s\n" uu____5184
            | uu____5190 -> ());
           (let r =
              let uu____5193 = FStar_TypeChecker_Env.get_range env in
              Some uu____5193 in
            let u_names =
              FStar_All.pipe_right s
                (FStar_List.map
                   (fun u  ->
                      let u_name = FStar_Syntax_Syntax.new_univ_name r in
                      (let uu____5205 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Gen") in
                       match uu____5205 with
                       | true  ->
                           let uu____5206 =
                             let uu____5207 = FStar_Unionfind.uvar_id u in
                             FStar_All.pipe_left FStar_Util.string_of_int
                               uu____5207 in
                           let uu____5209 =
                             FStar_Syntax_Print.univ_to_string
                               (FStar_Syntax_Syntax.U_unif u) in
                           let uu____5210 =
                             FStar_Syntax_Print.univ_to_string
                               (FStar_Syntax_Syntax.U_name u_name) in
                           FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                             uu____5206 uu____5209 uu____5210
                       | uu____5211 -> ());
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
        let uu____5228 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5228 FStar_Util.fifo_set_elements in
      univnames
let maybe_set_tk ts uu___95_5255 =
  match uu___95_5255 with
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
        | ([],uu____5296) -> generalized_univ_names
        | (uu____5300,[]) -> explicit_univ_names
        | uu____5304 ->
            let uu____5309 =
              let uu____5310 =
                let uu____5313 =
                  let uu____5314 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5314 in
                (uu____5313, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5310 in
            Prims.raise uu____5309
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
      (let uu____5328 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       match uu____5328 with
       | true  ->
           let uu____5329 = string_of_univs univs in
           FStar_Util.print1 "univs to gen : %s\n" uu____5329
       | uu____5331 -> ());
      (let gen = gen_univs env univs in
       (let uu____5335 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        match uu____5335 with
        | true  ->
            let uu____5336 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.print1 "After generalization: %s\n" uu____5336
        | uu____5337 -> ());
       (let univs = check_universe_generalization univnames gen t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs t in
        let uu____5341 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs, ts) uu____5341))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list Prims.option
  =
  fun env  ->
    fun ecs  ->
      let uu____5371 =
        let uu____5372 =
          FStar_Util.for_all
            (fun uu____5377  ->
               match uu____5377 with
               | (uu____5382,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5372 in
      match uu____5371 with
      | true  -> None
      | uu____5399 ->
          let norm c =
            (let uu____5405 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             match uu____5405 with
             | true  ->
                 let uu____5406 = FStar_Syntax_Print.comp_to_string c in
                 FStar_Util.print1
                   "Normalizing before generalizing:\n\t %s\n" uu____5406
             | uu____5407 -> ());
            (let c =
               let uu____5409 = FStar_TypeChecker_Env.should_verify env in
               match uu____5409 with
               | true  ->
                   FStar_TypeChecker_Normalize.normalize_comp
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.NoFullNorm] env c
               | uu____5410 ->
                   FStar_TypeChecker_Normalize.normalize_comp
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.NoFullNorm] env c in
             (let uu____5412 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              match uu____5412 with
              | true  ->
                  let uu____5413 = FStar_Syntax_Print.comp_to_string c in
                  FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5413
              | uu____5414 -> ());
             c) in
          let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
          let gen_uvars uvs =
            let uu____5447 = FStar_Util.set_difference uvs env_uvars in
            FStar_All.pipe_right uu____5447 FStar_Util.set_elements in
          let uu____5491 =
            let uu____5509 =
              FStar_All.pipe_right ecs
                (FStar_List.map
                   (fun uu____5564  ->
                      match uu____5564 with
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
            FStar_All.pipe_right uu____5509 FStar_List.unzip in
          (match uu____5491 with
           | (univs,uvars) ->
               let univs =
                 FStar_List.fold_left FStar_Util.set_union
                   FStar_Syntax_Syntax.no_universe_uvars univs in
               let gen_univs = gen_univs env univs in
               ((let uu____5726 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 match uu____5726 with
                 | true  ->
                     FStar_All.pipe_right gen_univs
                       (FStar_List.iter
                          (fun x  ->
                             FStar_Util.print1 "Generalizing uvar %s\n"
                               x.FStar_Ident.idText))
                 | uu____5729 -> ());
                (let ecs =
                   FStar_All.pipe_right uvars
                     (FStar_List.map
                        (fun uu____5768  ->
                           match uu____5768 with
                           | (uvs,e,c) ->
                               let tvars =
                                 FStar_All.pipe_right uvs
                                   (FStar_List.map
                                      (fun uu____5825  ->
                                         match uu____5825 with
                                         | (u,k) ->
                                             let uu____5845 =
                                               FStar_Unionfind.find u in
                                             (match uu____5845 with
                                              | FStar_Syntax_Syntax.Fixed
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk = _;
                                                  FStar_Syntax_Syntax.pos = _;
                                                  FStar_Syntax_Syntax.vars =
                                                    _;_}
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
                                                  FStar_Syntax_Syntax.vars =
                                                    _;_}
                                                  ->
                                                  (a,
                                                    (Some
                                                       FStar_Syntax_Syntax.imp_tag))
                                              | FStar_Syntax_Syntax.Fixed
                                                  uu____5883 ->
                                                  failwith
                                                    "Unexpected instantiation of mutually recursive uvar"
                                              | uu____5891 ->
                                                  let k =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Beta]
                                                      env k in
                                                  let uu____5896 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      k in
                                                  (match uu____5896 with
                                                   | (bs,kres) ->
                                                       let a =
                                                         let uu____5920 =
                                                           let uu____5922 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env in
                                                           FStar_All.pipe_left
                                                             (fun _0_30  ->
                                                                Some _0_30)
                                                             uu____5922 in
                                                         FStar_Syntax_Syntax.new_bv
                                                           uu____5920 kres in
                                                       let t =
                                                         let uu____5925 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             a in
                                                         let uu____5926 =
                                                           let uu____5933 =
                                                             let uu____5939 =
                                                               let uu____5940
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_Total
                                                                   kres in
                                                               FStar_Syntax_Util.lcomp_of_comp
                                                                 uu____5940 in
                                                             FStar_Util.Inl
                                                               uu____5939 in
                                                           Some uu____5933 in
                                                         FStar_Syntax_Util.abs
                                                           bs uu____5925
                                                           uu____5926 in
                                                       (FStar_Syntax_Util.set_uvar
                                                          u t;
                                                        (a,
                                                          (Some
                                                             FStar_Syntax_Syntax.imp_tag))))))) in
                               let uu____5955 =
                                 match (tvars, gen_univs) with
                                 | ([],[]) -> (e, c)
                                 | ([],uu____5973) ->
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
                                 | uu____5985 ->
                                     let uu____5993 = (e, c) in
                                     (match uu____5993 with
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
                                            let uu____6005 =
                                              let uu____6006 =
                                                FStar_Syntax_Subst.compress
                                                  (FStar_Syntax_Util.comp_result
                                                     c) in
                                              uu____6006.FStar_Syntax_Syntax.n in
                                            match uu____6005 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,cod) ->
                                                let uu____6023 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs cod in
                                                (match uu____6023 with
                                                 | (bs,cod) ->
                                                     FStar_Syntax_Util.arrow
                                                       (FStar_List.append
                                                          tvars bs) cod)
                                            | uu____6033 ->
                                                FStar_Syntax_Util.arrow tvars
                                                  c in
                                          let e' =
                                            FStar_Syntax_Util.abs tvars e
                                              (Some
                                                 (FStar_Util.Inl
                                                    (FStar_Syntax_Util.lcomp_of_comp
                                                       c))) in
                                          let uu____6043 =
                                            FStar_Syntax_Syntax.mk_Total t in
                                          (e', uu____6043)) in
                               (match uu____5955 with
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
      (let uu____6081 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       match uu____6081 with
       | true  ->
           let uu____6082 =
             let uu____6083 =
               FStar_List.map
                 (fun uu____6088  ->
                    match uu____6088 with
                    | (lb,uu____6093,uu____6094) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____6083 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____6082
       | uu____6096 -> ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6104  ->
              match uu____6104 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6119 =
           let uu____6126 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6142  ->
                     match uu____6142 with | (uu____6148,e,c) -> (e, c))) in
           gen env uu____6126 in
         match uu____6119 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6180  ->
                     match uu____6180 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6224  ->
                  fun uu____6225  ->
                    match (uu____6224, uu____6225) with
                    | ((l,uu____6258,uu____6259),(us,e,c)) ->
                        ((let uu____6285 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          match uu____6285 with
                          | true  ->
                              let uu____6286 =
                                FStar_Range.string_of_range
                                  e.FStar_Syntax_Syntax.pos in
                              let uu____6287 =
                                FStar_Syntax_Print.lbname_to_string l in
                              let uu____6288 =
                                FStar_Syntax_Print.term_to_string
                                  (FStar_Syntax_Util.comp_result c) in
                              let uu____6289 =
                                FStar_Syntax_Print.term_to_string e in
                              FStar_Util.print4
                                "(%s) Generalized %s at type %s\n%s\n"
                                uu____6286 uu____6287 uu____6288 uu____6289
                          | uu____6290 -> ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames  ->
            fun uu____6308  ->
              match uu____6308 with
              | (l,generalized_univs,t,c) ->
                  let uu____6326 =
                    check_universe_generalization univnames generalized_univs
                      t in
                  (l, uu____6326, t, c)) univnames_lecs generalized_lecs)
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
            match env.FStar_TypeChecker_Env.use_eq with
            | true  -> FStar_TypeChecker_Rel.try_teq env t1 t2
            | uu____6358 ->
                let uu____6359 = FStar_TypeChecker_Rel.try_subtype env t1 t2 in
                (match uu____6359 with
                 | None  -> None
                 | Some f ->
                     let uu____6363 = FStar_TypeChecker_Rel.apply_guard f e in
                     FStar_All.pipe_left (fun _0_31  -> Some _0_31)
                       uu____6363) in
          let is_var e =
            let uu____6369 =
              let uu____6370 = FStar_Syntax_Subst.compress e in
              uu____6370.FStar_Syntax_Syntax.n in
            match uu____6369 with
            | FStar_Syntax_Syntax.Tm_name uu____6373 -> true
            | uu____6374 -> false in
          let decorate e t =
            let e = FStar_Syntax_Subst.compress e in
            match e.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_name
                      (let uu___137_6396 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___137_6396.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___137_6396.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t2
                       }))) (Some (t2.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos
            | uu____6397 ->
                let uu___138_6398 = e in
                let uu____6399 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___138_6398.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6399;
                  FStar_Syntax_Syntax.pos =
                    (uu___138_6398.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___138_6398.FStar_Syntax_Syntax.vars)
                } in
          let env =
            let uu___139_6408 = env in
            let uu____6409 =
              env.FStar_TypeChecker_Env.use_eq ||
                (env.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___139_6408.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___139_6408.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___139_6408.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___139_6408.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___139_6408.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___139_6408.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___139_6408.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___139_6408.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___139_6408.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___139_6408.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___139_6408.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___139_6408.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___139_6408.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___139_6408.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___139_6408.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6409;
              FStar_TypeChecker_Env.is_iface =
                (uu___139_6408.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___139_6408.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___139_6408.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___139_6408.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___139_6408.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___139_6408.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___139_6408.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___139_6408.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____6410 = check env t1 t2 in
          match uu____6410 with
          | None  ->
              let uu____6414 =
                let uu____6415 =
                  let uu____6418 =
                    FStar_TypeChecker_Err.expected_expression_of_type env t2
                      e t1 in
                  let uu____6419 = FStar_TypeChecker_Env.get_range env in
                  (uu____6418, uu____6419) in
                FStar_Errors.Error uu____6415 in
              Prims.raise uu____6414
          | Some g ->
              ((let uu____6424 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel") in
                match uu____6424 with
                | true  ->
                    let uu____6425 =
                      FStar_TypeChecker_Rel.guard_to_string env g in
                    FStar_All.pipe_left
                      (FStar_Util.print1 "Applied guard is %s\n") uu____6425
                | uu____6426 -> ());
               (let uu____6427 = decorate e t2 in (uu____6427, g)))
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
        let uu____6451 = FStar_Syntax_Util.is_total_lcomp lc in
        match uu____6451 with
        | true  ->
            let uu____6454 = discharge g in
            let uu____6455 = lc.FStar_Syntax_Syntax.comp () in
            (uu____6454, uu____6455)
        | uu____6460 ->
            let c = lc.FStar_Syntax_Syntax.comp () in
            let steps = [FStar_TypeChecker_Normalize.Beta] in
            let c =
              let uu____6467 =
                let uu____6468 =
                  let uu____6469 =
                    FStar_TypeChecker_Normalize.unfold_effect_abbrev env c in
                  FStar_All.pipe_right uu____6469 FStar_Syntax_Syntax.mk_Comp in
                FStar_All.pipe_right uu____6468
                  (FStar_TypeChecker_Normalize.normalize_comp steps env) in
              FStar_All.pipe_right uu____6467
                (FStar_TypeChecker_Normalize.comp_to_comp_typ env) in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c.FStar_Syntax_Syntax.effect_name in
            let uu____6471 = destruct_comp c in
            (match uu____6471 with
             | (u_t,t,wp) ->
                 let vc =
                   let uu____6483 = FStar_TypeChecker_Env.get_range env in
                   let uu____6484 =
                     let uu____6485 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env
                         md md.FStar_Syntax_Syntax.trivial in
                     let uu____6486 =
                       let uu____6487 = FStar_Syntax_Syntax.as_arg t in
                       let uu____6488 =
                         let uu____6490 = FStar_Syntax_Syntax.as_arg wp in
                         [uu____6490] in
                       uu____6487 :: uu____6488 in
                     FStar_Syntax_Syntax.mk_Tm_app uu____6485 uu____6486 in
                   uu____6484
                     (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                     uu____6483 in
                 ((let uu____6496 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Simplification") in
                   match uu____6496 with
                   | true  ->
                       let uu____6497 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.print1 "top-level VC: %s\n" uu____6497
                   | uu____6498 -> ());
                  (let g =
                     let uu____6500 =
                       FStar_All.pipe_left
                         FStar_TypeChecker_Rel.guard_of_guard_formula
                         (FStar_TypeChecker_Common.NonTrivial vc) in
                     FStar_TypeChecker_Rel.conj_guard g uu____6500 in
                   let uu____6501 = discharge g in
                   let uu____6502 = FStar_Syntax_Syntax.mk_Comp c in
                   (uu____6501, uu____6502))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___96_6526 =
        match uu___96_6526 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____6532)::[] -> f fst
        | uu____6545 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6550 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6550
          (fun _0_32  -> FStar_TypeChecker_Common.NonTrivial _0_32) in
      let op_or_e e =
        let uu____6559 =
          let uu____6562 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6562 in
        FStar_All.pipe_right uu____6559
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34) in
      let op_or_t t =
        let uu____6573 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6573
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36) in
      let short_op_ite uu___97_6587 =
        match uu___97_6587 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6593)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6608)::[] ->
            let uu____6629 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6629
              (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37)
        | uu____6634 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6641 =
          let uu____6646 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____6646) in
        let uu____6651 =
          let uu____6657 =
            let uu____6662 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____6662) in
          let uu____6667 =
            let uu____6673 =
              let uu____6678 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____6678) in
            let uu____6683 =
              let uu____6689 =
                let uu____6694 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____6694) in
              let uu____6699 =
                let uu____6705 =
                  let uu____6710 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____6710) in
                [uu____6705; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____6689 :: uu____6699 in
            uu____6673 :: uu____6683 in
          uu____6657 :: uu____6667 in
        uu____6641 :: uu____6651 in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____6751 =
            FStar_Util.find_map table
              (fun uu____6757  ->
                 match uu____6757 with
                 | (x,mk) ->
                     (match FStar_Ident.lid_equals x lid with
                      | true  ->
                          let uu____6770 = mk seen_args in Some uu____6770
                      | uu____6771 -> None)) in
          (match uu____6751 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____6773 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6777 =
      let uu____6778 = FStar_Syntax_Util.un_uinst l in
      uu____6778.FStar_Syntax_Syntax.n in
    match uu____6777 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____6782 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs =
        match bs with
        | (hd,uu____6800)::uu____6801 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____6807 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____6811,Some (FStar_Syntax_Syntax.Implicit uu____6812))::uu____6813
          -> bs
      | uu____6822 ->
          let uu____6823 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____6823 with
           | None  -> bs
           | Some t ->
               let uu____6826 =
                 let uu____6827 = FStar_Syntax_Subst.compress t in
                 uu____6827.FStar_Syntax_Syntax.n in
               (match uu____6826 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____6831) ->
                    let uu____6842 =
                      FStar_Util.prefix_until
                        (fun uu___98_6861  ->
                           match uu___98_6861 with
                           | (uu____6865,Some (FStar_Syntax_Syntax.Implicit
                              uu____6866)) -> false
                           | uu____6868 -> true) bs' in
                    (match uu____6842 with
                     | None  -> bs
                     | Some ([],uu____6886,uu____6887) -> bs
                     | Some (imps,uu____6924,uu____6925) ->
                         let uu____6962 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____6970  ->
                                   match uu____6970 with
                                   | (x,uu____6975) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         (match uu____6962 with
                          | true  ->
                              let r = pos bs in
                              let imps =
                                FStar_All.pipe_right imps
                                  (FStar_List.map
                                     (fun uu____6998  ->
                                        match uu____6998 with
                                        | (x,i) ->
                                            let uu____7009 =
                                              FStar_Syntax_Syntax.set_range_of_bv
                                                x r in
                                            (uu____7009, i))) in
                              FStar_List.append imps bs
                          | uu____7014 -> bs))
                | uu____7015 -> bs))
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
            match ((FStar_Ident.lid_equals m1 m2) ||
                     ((FStar_Syntax_Util.is_pure_effect c1) &&
                        (FStar_Syntax_Util.is_ghost_effect c2)))
                    ||
                    ((FStar_Syntax_Util.is_pure_effect c2) &&
                       (FStar_Syntax_Util.is_ghost_effect c1))
            with
            | true  -> e
            | uu____7033 ->
                let uu____7034 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_meta
                      (e,
                        (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)))))
                  uu____7034 e.FStar_Syntax_Syntax.pos
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
          let uu____7060 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          match uu____7060 with
          | true  -> e
          | uu____7061 ->
              let uu____7062 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
              (FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))))
                uu____7062 e.FStar_Syntax_Syntax.pos
let effect_repr_aux only_reifiable env c u_c =
  let uu____7104 =
    let uu____7106 =
      FStar_TypeChecker_Env.norm_eff_name env
        (FStar_Syntax_Util.comp_effect_name c) in
    FStar_TypeChecker_Env.effect_decl_opt env uu____7106 in
  match uu____7104 with
  | None  -> None
  | Some ed ->
      let uu____7113 =
        only_reifiable &&
          (let uu____7114 =
             FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____7114) in
      (match uu____7113 with
       | true  -> None
       | uu____7121 ->
           (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> None
            | uu____7127 ->
                let c =
                  FStar_TypeChecker_Normalize.unfold_effect_abbrev env c in
                let uu____7129 =
                  let uu____7138 =
                    FStar_List.hd c.FStar_Syntax_Syntax.effect_args in
                  ((c.FStar_Syntax_Syntax.result_typ), uu____7138) in
                (match uu____7129 with
                 | (res_typ,wp) ->
                     let repr =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_c] env
                         ed ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____7172 =
                       let uu____7175 = FStar_TypeChecker_Env.get_range env in
                       let uu____7176 =
                         let uu____7179 =
                           let uu____7180 =
                             let uu____7190 =
                               let uu____7192 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____7192; wp] in
                             (repr, uu____7190) in
                           FStar_Syntax_Syntax.Tm_app uu____7180 in
                         FStar_Syntax_Syntax.mk uu____7179 in
                       uu____7176 None uu____7175 in
                     Some uu____7172)))
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
          let uu____7236 =
            let uu____7237 =
              let uu____7240 =
                FStar_Util.format1 "Effect %s cannot be reified"
                  l.FStar_Ident.str in
              let uu____7241 = FStar_TypeChecker_Env.get_range env in
              (uu____7240, uu____7241) in
            FStar_Errors.Error uu____7237 in
          Prims.raise uu____7236 in
        let uu____7242 =
          let uu____7246 = c.FStar_Syntax_Syntax.comp () in
          effect_repr_aux true env uu____7246 u_c in
        match uu____7242 with
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
        (let uu____7273 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         match uu____7273 with
         | true  ->
             (d (FStar_Ident.text_of_lid lident);
              (let uu____7275 = FStar_Syntax_Print.term_to_string def in
               FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
                 (FStar_Ident.text_of_lid lident) uu____7275))
         | uu____7276 -> ());
        (let fv =
           let uu____7278 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7278 None in
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
         let uu____7286 =
           (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)) None
             FStar_Range.dummyRange in
         (sig_ctx, uu____7286))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___99_7308 =
        match uu___99_7308 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7309 -> false in
      let reducibility uu___100_7313 =
        match uu___100_7313 with
        | FStar_Syntax_Syntax.Abstract 
          |FStar_Syntax_Syntax.Irreducible 
           |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
            |FStar_Syntax_Syntax.Visible_default 
             |FStar_Syntax_Syntax.Inline_for_extraction 
            -> true
        | uu____7314 -> false in
      let assumption uu___101_7318 =
        match uu___101_7318 with
        | FStar_Syntax_Syntax.Assumption |FStar_Syntax_Syntax.New  -> true
        | uu____7319 -> false in
      let reification uu___102_7323 =
        match uu___102_7323 with
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            true
        | uu____7325 -> false in
      let inferred uu___103_7329 =
        match uu___103_7329 with
        | FStar_Syntax_Syntax.Discriminator _
          |FStar_Syntax_Syntax.Projector _
           |FStar_Syntax_Syntax.RecordType _
            |FStar_Syntax_Syntax.RecordConstructor _
             |FStar_Syntax_Syntax.ExceptionConstructor 
              |FStar_Syntax_Syntax.HasMaskedEffect 
               |FStar_Syntax_Syntax.Effect 
            -> true
        | uu____7334 -> false in
      let has_eq uu___104_7338 =
        match uu___104_7338 with
        | FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7339 -> false in
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
        | uu____7364 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7367 =
        let uu____7368 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___105_7370  ->
                  match uu___105_7370 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7371 -> false)) in
        FStar_All.pipe_right uu____7368 Prims.op_Negation in
      match uu____7367 with
      | true  ->
          let r = FStar_Syntax_Util.range_of_sigelt se in
          let no_dup_quals =
            FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
          let err' msg =
            let uu____7381 =
              let uu____7382 =
                let uu____7385 =
                  let uu____7386 = FStar_Syntax_Print.quals_to_string quals in
                  FStar_Util.format2
                    "The qualifier list \"[%s]\" is not permissible for this element%s"
                    uu____7386 msg in
                (uu____7385, r) in
              FStar_Errors.Error uu____7382 in
            Prims.raise uu____7381 in
          let err msg = err' (Prims.strcat ": " msg) in
          let err' uu____7394 = err' "" in
          ((match (FStar_List.length quals) <>
                    (FStar_List.length no_dup_quals)
            with
            | true  -> err "duplicate qualifiers"
            | uu____7400 -> ());
           (let uu____7402 =
              let uu____7403 =
                FStar_All.pipe_right quals
                  (FStar_List.for_all (quals_combo_ok quals)) in
              Prims.op_Negation uu____7403 in
            match uu____7402 with
            | true  -> err "ill-formed combination"
            | uu____7405 -> ());
           (match se with
            | FStar_Syntax_Syntax.Sig_let
                ((is_rec,uu____7407),uu____7408,uu____7409,uu____7410,uu____7411)
                ->
                ((let uu____7424 =
                    is_rec &&
                      (FStar_All.pipe_right quals
                         (FStar_List.contains
                            FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                  match uu____7424 with
                  | true  ->
                      err "recursive definitions cannot be marked inline"
                  | uu____7426 -> ());
                 (let uu____7427 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_some
                         (fun x  -> (assumption x) || (has_eq x))) in
                  match uu____7427 with
                  | true  ->
                      err
                        "definitions cannot be assumed or marked with equality qualifiers"
                  | uu____7430 -> ()))
            | FStar_Syntax_Syntax.Sig_bundle uu____7431 ->
                let uu____7439 =
                  let uu____7440 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_all
                         (fun x  ->
                            (((x = FStar_Syntax_Syntax.Abstract) ||
                                (inferred x))
                               || (visibility x))
                              || (has_eq x))) in
                  Prims.op_Negation uu____7440 in
                (match uu____7439 with | true  -> err' () | uu____7443 -> ())
            | FStar_Syntax_Syntax.Sig_declare_typ uu____7444 ->
                let uu____7451 =
                  FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
                (match uu____7451 with | true  -> err' () | uu____7453 -> ())
            | FStar_Syntax_Syntax.Sig_assume uu____7454 ->
                let uu____7460 =
                  let uu____7461 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_all
                         (fun x  ->
                            (visibility x) ||
                              (x = FStar_Syntax_Syntax.Assumption))) in
                  Prims.op_Negation uu____7461 in
                (match uu____7460 with | true  -> err' () | uu____7464 -> ())
            | FStar_Syntax_Syntax.Sig_new_effect uu____7465 ->
                let uu____7468 =
                  let uu____7469 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_all
                         (fun x  ->
                            (((x = FStar_Syntax_Syntax.TotalEffect) ||
                                (inferred x))
                               || (visibility x))
                              || (reification x))) in
                  Prims.op_Negation uu____7469 in
                (match uu____7468 with | true  -> err' () | uu____7472 -> ())
            | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7473 ->
                let uu____7476 =
                  let uu____7477 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_all
                         (fun x  ->
                            (((x = FStar_Syntax_Syntax.TotalEffect) ||
                                (inferred x))
                               || (visibility x))
                              || (reification x))) in
                  Prims.op_Negation uu____7477 in
                (match uu____7476 with | true  -> err' () | uu____7480 -> ())
            | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7481 ->
                let uu____7491 =
                  let uu____7492 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_all
                         (fun x  -> (inferred x) || (visibility x))) in
                  Prims.op_Negation uu____7492 in
                (match uu____7491 with | true  -> err' () | uu____7495 -> ())
            | uu____7496 -> ()))
      | uu____7497 -> ()
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
                          let uu____7553 =
                            let uu____7556 =
                              let uu____7557 =
                                let uu____7562 =
                                  let uu____7563 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7563 in
                                (uu____7562, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7557 in
                            FStar_Syntax_Syntax.mk uu____7556 in
                          uu____7553 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7589  ->
                                  match uu____7589 with
                                  | (x,imp) ->
                                      let uu____7596 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7596, imp))) in
                        (FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p in
                      let unrefined_arg_binder =
                        let uu____7602 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7602 in
                      let arg_binder =
                        match Prims.op_Negation refine_domain with
                        | true  -> unrefined_arg_binder
                        | uu____7604 ->
                            let disc_name =
                              FStar_Syntax_Util.mk_discriminator lid in
                            let x =
                              FStar_Syntax_Syntax.new_bv (Some p) arg_typ in
                            let sort =
                              let disc_fvar =
                                FStar_Syntax_Syntax.fvar
                                  (FStar_Ident.set_lid_range disc_name p)
                                  FStar_Syntax_Syntax.Delta_equational None in
                              let uu____7611 =
                                let uu____7612 =
                                  let uu____7613 =
                                    let uu____7614 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst
                                        disc_fvar inst_univs in
                                    let uu____7615 =
                                      let uu____7616 =
                                        let uu____7617 =
                                          FStar_Syntax_Syntax.bv_to_name x in
                                        FStar_All.pipe_left
                                          FStar_Syntax_Syntax.as_arg
                                          uu____7617 in
                                      [uu____7616] in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7614
                                      uu____7615 in
                                  uu____7613 None p in
                                FStar_Syntax_Util.b2t uu____7612 in
                              FStar_Syntax_Util.refine x uu____7611 in
                            let uu____7622 =
                              let uu___140_7623 = projectee arg_typ in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___140_7623.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___140_7623.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = sort
                              } in
                            FStar_Syntax_Syntax.mk_binder uu____7622 in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7633 =
                          FStar_List.map
                            (fun uu____7643  ->
                               match uu____7643 with
                               | (x,uu____7650) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7633 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7674  ->
                                match uu____7674 with
                                | (x,uu____7681) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        match fvq <> FStar_Syntax_Syntax.Data_ctor with
                        | true  -> []
                        | uu____7686 ->
                            let discriminator_name =
                              FStar_Syntax_Util.mk_discriminator lid in
                            let no_decl = false in
                            let only_decl =
                              (let uu____7690 =
                                 FStar_TypeChecker_Env.current_module env in
                               FStar_Ident.lid_equals
                                 FStar_Syntax_Const.prims_lid uu____7690)
                                ||
                                (let uu____7691 =
                                   let uu____7692 =
                                     FStar_TypeChecker_Env.current_module env in
                                   uu____7692.FStar_Ident.str in
                                 FStar_Options.dont_gen_projectors uu____7691) in
                            let quals =
                              let uu____7695 =
                                let uu____7697 =
                                  let uu____7699 =
                                    only_decl &&
                                      ((FStar_All.pipe_left Prims.op_Negation
                                          env.FStar_TypeChecker_Env.is_iface)
                                         || env.FStar_TypeChecker_Env.admit) in
                                  match uu____7699 with
                                  | true  -> [FStar_Syntax_Syntax.Assumption]
                                  | uu____7701 -> [] in
                                let uu____7702 =
                                  FStar_List.filter
                                    (fun uu___106_7704  ->
                                       match uu___106_7704 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           Prims.op_Negation only_decl
                                       | FStar_Syntax_Syntax.Private  -> true
                                       | uu____7705 -> false) iquals in
                                FStar_List.append uu____7697 uu____7702 in
                              FStar_List.append
                                ((FStar_Syntax_Syntax.Discriminator lid) ::
                                (match only_decl with
                                 | true  -> [FStar_Syntax_Syntax.Logic]
                                 | uu____7707 -> [])) uu____7695 in
                            let binders =
                              FStar_List.append imp_binders
                                [unrefined_arg_binder] in
                            let t =
                              let bool_typ =
                                let uu____7718 =
                                  let uu____7719 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      FStar_Syntax_Const.bool_lid
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7719 in
                                FStar_Syntax_Syntax.mk_Total uu____7718 in
                              let uu____7720 =
                                FStar_Syntax_Util.arrow binders bool_typ in
                              FStar_All.pipe_left
                                (FStar_Syntax_Subst.close_univ_vars uvs)
                                uu____7720 in
                            let decl =
                              FStar_Syntax_Syntax.Sig_declare_typ
                                (discriminator_name, uvs, t, quals,
                                  (FStar_Ident.range_of_lid
                                     discriminator_name)) in
                            ((let uu____7724 =
                                FStar_TypeChecker_Env.debug env
                                  (FStar_Options.Other "LogTypes") in
                              match uu____7724 with
                              | true  ->
                                  let uu____7725 =
                                    FStar_Syntax_Print.sigelt_to_string decl in
                                  FStar_Util.print1
                                    "Declaration of a discriminator %s\n"
                                    uu____7725
                              | uu____7726 -> ());
                             (match only_decl with
                              | true  -> [decl]
                              | uu____7728 ->
                                  let body =
                                    match Prims.op_Negation refine_domain
                                    with
                                    | true  ->
                                        FStar_Syntax_Const.exp_true_bool
                                    | uu____7730 ->
                                        let arg_pats =
                                          FStar_All.pipe_right all_params
                                            (FStar_List.mapi
                                               (fun j  ->
                                                  fun uu____7753  ->
                                                    match uu____7753 with
                                                    | (x,imp) ->
                                                        let b =
                                                          FStar_Syntax_Syntax.is_implicit
                                                            imp in
                                                        (match b &&
                                                                 (j < ntps)
                                                         with
                                                         | true  ->
                                                             let uu____7769 =
                                                               let uu____7772
                                                                 =
                                                                 let uu____7773
                                                                   =
                                                                   let uu____7778
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                   (uu____7778,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                 FStar_Syntax_Syntax.Pat_dot_term
                                                                   uu____7773 in
                                                               pos uu____7772 in
                                                             (uu____7769, b)
                                                         | uu____7781 ->
                                                             let uu____7782 =
                                                               let uu____7785
                                                                 =
                                                                 let uu____7786
                                                                   =
                                                                   FStar_Syntax_Syntax.gen_bv
                                                                    (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                 FStar_Syntax_Syntax.Pat_wild
                                                                   uu____7786 in
                                                               pos uu____7785 in
                                                             (uu____7782, b)))) in
                                        let pat_true =
                                          let uu____7798 =
                                            let uu____7801 =
                                              let uu____7802 =
                                                let uu____7810 =
                                                  FStar_Syntax_Syntax.lid_as_fv
                                                    lid
                                                    FStar_Syntax_Syntax.Delta_constant
                                                    (Some fvq) in
                                                (uu____7810, arg_pats) in
                                              FStar_Syntax_Syntax.Pat_cons
                                                uu____7802 in
                                            pos uu____7801 in
                                          (uu____7798, None,
                                            FStar_Syntax_Const.exp_true_bool) in
                                        let pat_false =
                                          let uu____7832 =
                                            let uu____7835 =
                                              let uu____7836 =
                                                FStar_Syntax_Syntax.new_bv
                                                  None
                                                  FStar_Syntax_Syntax.tun in
                                              FStar_Syntax_Syntax.Pat_wild
                                                uu____7836 in
                                            pos uu____7835 in
                                          (uu____7832, None,
                                            FStar_Syntax_Const.exp_false_bool) in
                                        let arg_exp =
                                          FStar_Syntax_Syntax.bv_to_name
                                            (Prims.fst unrefined_arg_binder) in
                                        let uu____7845 =
                                          let uu____7848 =
                                            let uu____7849 =
                                              let uu____7865 =
                                                let uu____7867 =
                                                  FStar_Syntax_Util.branch
                                                    pat_true in
                                                let uu____7868 =
                                                  let uu____7870 =
                                                    FStar_Syntax_Util.branch
                                                      pat_false in
                                                  [uu____7870] in
                                                uu____7867 :: uu____7868 in
                                              (arg_exp, uu____7865) in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____7849 in
                                          FStar_Syntax_Syntax.mk uu____7848 in
                                        uu____7845 None p in
                                  let dd =
                                    let uu____7881 =
                                      FStar_All.pipe_right quals
                                        (FStar_List.contains
                                           FStar_Syntax_Syntax.Abstract) in
                                    match uu____7881 with
                                    | true  ->
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                    | uu____7883 ->
                                        FStar_Syntax_Syntax.Delta_equational in
                                  let imp =
                                    FStar_Syntax_Util.abs binders body None in
                                  let lbtyp =
                                    match no_decl with
                                    | true  -> t
                                    | uu____7891 -> FStar_Syntax_Syntax.tun in
                                  let lb =
                                    let uu____7893 =
                                      let uu____7896 =
                                        FStar_Syntax_Syntax.lid_as_fv
                                          discriminator_name dd None in
                                      FStar_Util.Inr uu____7896 in
                                    let uu____7897 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        imp in
                                    {
                                      FStar_Syntax_Syntax.lbname = uu____7893;
                                      FStar_Syntax_Syntax.lbunivs = uvs;
                                      FStar_Syntax_Syntax.lbtyp = lbtyp;
                                      FStar_Syntax_Syntax.lbeff =
                                        FStar_Syntax_Const.effect_Tot_lid;
                                      FStar_Syntax_Syntax.lbdef = uu____7897
                                    } in
                                  let impl =
                                    let uu____7901 =
                                      let uu____7910 =
                                        let uu____7912 =
                                          let uu____7913 =
                                            FStar_All.pipe_right
                                              lb.FStar_Syntax_Syntax.lbname
                                              FStar_Util.right in
                                          FStar_All.pipe_right uu____7913
                                            (fun fv  ->
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                        [uu____7912] in
                                      ((false, [lb]), p, uu____7910, quals,
                                        []) in
                                    FStar_Syntax_Syntax.Sig_let uu____7901 in
                                  ((let uu____7929 =
                                      FStar_TypeChecker_Env.debug env
                                        (FStar_Options.Other "LogTypes") in
                                    match uu____7929 with
                                    | true  ->
                                        let uu____7930 =
                                          FStar_Syntax_Print.sigelt_to_string
                                            impl in
                                        FStar_Util.print1
                                          "Implementation of a discriminator %s\n"
                                          uu____7930
                                    | uu____7931 -> ());
                                   [decl; impl]))) in
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
                                fun uu____7950  ->
                                  match uu____7950 with
                                  | (a,uu____7954) ->
                                      let uu____7955 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____7955 with
                                       | (field_name,uu____7959) ->
                                           let field_proj_tm =
                                             let uu____7961 =
                                               let uu____7962 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7962 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7961 inst_univs in
                                           let proj =
                                             (FStar_Syntax_Syntax.mk_Tm_app
                                                field_proj_tm [arg]) None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____7978 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7987  ->
                                    match uu____7987 with
                                    | (x,uu____7992) ->
                                        let p =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____7994 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____7994 with
                                         | (field_name,uu____7999) ->
                                             let t =
                                               let uu____8001 =
                                                 let uu____8002 =
                                                   let uu____8005 =
                                                     FStar_Syntax_Subst.subst
                                                       subst
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8005 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8002 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8001 in
                                             let only_decl =
                                               ((let uu____8007 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____8007)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____8008 =
                                                    let uu____8009 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8009.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8008) in
                                             let no_decl = false in
                                             let quals q =
                                               match only_decl with
                                               | true  ->
                                                   let uu____8019 =
                                                     FStar_List.filter
                                                       (fun uu___107_8021  ->
                                                          match uu___107_8021
                                                          with
                                                          | FStar_Syntax_Syntax.Abstract
                                                               -> false
                                                          | uu____8022 ->
                                                              true) q in
                                                   FStar_Syntax_Syntax.Assumption
                                                     :: uu____8019
                                               | uu____8023 -> q in
                                             let quals =
                                               let iquals =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___108_8030  ->
                                                         match uu___108_8030
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                           
                                                           |FStar_Syntax_Syntax.Private
                                                            -> true
                                                         | uu____8031 ->
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
                                             ((let uu____8035 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               match uu____8035 with
                                               | true  ->
                                                   let uu____8036 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       decl in
                                                   FStar_Util.print1
                                                     "Declaration of a projector %s\n"
                                                     uu____8036
                                               | uu____8037 -> ());
                                              (match only_decl with
                                               | true  -> [decl]
                                               | uu____8039 ->
                                                   let projection =
                                                     FStar_Syntax_Syntax.gen_bv
                                                       (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                       None
                                                       FStar_Syntax_Syntax.tun in
                                                   let arg_pats =
                                                     FStar_All.pipe_right
                                                       all_params
                                                       (FStar_List.mapi
                                                          (fun j  ->
                                                             fun uu____8063 
                                                               ->
                                                               match uu____8063
                                                               with
                                                               | (x,imp) ->
                                                                   let b =
                                                                    FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                   (match 
                                                                    (i + ntps)
                                                                    = j
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    let uu____8079
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                    (uu____8079,
                                                                    b)
                                                                    | 
                                                                    uu____8084
                                                                    ->
                                                                    (match 
                                                                    b &&
                                                                    (j < ntps)
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    let uu____8091
                                                                    =
                                                                    let uu____8094
                                                                    =
                                                                    let uu____8095
                                                                    =
                                                                    let uu____8100
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8100,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8095 in
                                                                    pos
                                                                    uu____8094 in
                                                                    (uu____8091,
                                                                    b)
                                                                    | 
                                                                    uu____8103
                                                                    ->
                                                                    let uu____8104
                                                                    =
                                                                    let uu____8107
                                                                    =
                                                                    let uu____8108
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8108 in
                                                                    pos
                                                                    uu____8107 in
                                                                    (uu____8104,
                                                                    b))))) in
                                                   let pat =
                                                     let uu____8120 =
                                                       let uu____8123 =
                                                         let uu____8124 =
                                                           let uu____8132 =
                                                             FStar_Syntax_Syntax.lid_as_fv
                                                               lid
                                                               FStar_Syntax_Syntax.Delta_constant
                                                               (Some fvq) in
                                                           (uu____8132,
                                                             arg_pats) in
                                                         FStar_Syntax_Syntax.Pat_cons
                                                           uu____8124 in
                                                       pos uu____8123 in
                                                     let uu____8138 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         projection in
                                                     (uu____8120, None,
                                                       uu____8138) in
                                                   let body =
                                                     let uu____8149 =
                                                       let uu____8152 =
                                                         let uu____8153 =
                                                           let uu____8169 =
                                                             let uu____8171 =
                                                               FStar_Syntax_Util.branch
                                                                 pat in
                                                             [uu____8171] in
                                                           (arg_exp,
                                                             uu____8169) in
                                                         FStar_Syntax_Syntax.Tm_match
                                                           uu____8153 in
                                                       FStar_Syntax_Syntax.mk
                                                         uu____8152 in
                                                     uu____8149 None p in
                                                   let imp =
                                                     FStar_Syntax_Util.abs
                                                       binders body None in
                                                   let dd =
                                                     let uu____8188 =
                                                       FStar_All.pipe_right
                                                         quals
                                                         (FStar_List.contains
                                                            FStar_Syntax_Syntax.Abstract) in
                                                     match uu____8188 with
                                                     | true  ->
                                                         FStar_Syntax_Syntax.Delta_abstract
                                                           FStar_Syntax_Syntax.Delta_equational
                                                     | uu____8190 ->
                                                         FStar_Syntax_Syntax.Delta_equational in
                                                   let lbtyp =
                                                     match no_decl with
                                                     | true  -> t
                                                     | uu____8192 ->
                                                         FStar_Syntax_Syntax.tun in
                                                   let lb =
                                                     let uu____8194 =
                                                       let uu____8197 =
                                                         FStar_Syntax_Syntax.lid_as_fv
                                                           field_name dd None in
                                                       FStar_Util.Inr
                                                         uu____8197 in
                                                     let uu____8198 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         uvs imp in
                                                     {
                                                       FStar_Syntax_Syntax.lbname
                                                         = uu____8194;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = lbtyp;
                                                       FStar_Syntax_Syntax.lbeff
                                                         =
                                                         FStar_Syntax_Const.effect_Tot_lid;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____8198
                                                     } in
                                                   let impl =
                                                     let uu____8202 =
                                                       let uu____8211 =
                                                         let uu____8213 =
                                                           let uu____8214 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8214
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8213] in
                                                       ((false, [lb]), p,
                                                         uu____8211, quals,
                                                         []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8202 in
                                                   ((let uu____8230 =
                                                       FStar_TypeChecker_Env.debug
                                                         env
                                                         (FStar_Options.Other
                                                            "LogTypes") in
                                                     match uu____8230 with
                                                     | true  ->
                                                         let uu____8231 =
                                                           FStar_Syntax_Print.sigelt_to_string
                                                             impl in
                                                         FStar_Util.print1
                                                           "Implementation of a projector %s\n"
                                                           uu____8231
                                                     | uu____8232 -> ());
                                                    (match no_decl with
                                                     | true  -> [impl]
                                                     | uu____8234 ->
                                                         [decl; impl]))))))) in
                        FStar_All.pipe_right uu____7978 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,quals,uu____8262,r) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8268 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8268 with
               | (univ_opening,uvs) ->
                   let t = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8281 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____8281 with
                    | (formals,uu____8291) ->
                        let uu____8302 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se  ->
                                 let uu____8315 =
                                   let uu____8316 =
                                     let uu____8317 =
                                       FStar_Syntax_Util.lid_of_sigelt se in
                                     FStar_Util.must uu____8317 in
                                   FStar_Ident.lid_equals typ_lid uu____8316 in
                                 match uu____8315 with
                                 | true  ->
                                     (match se with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____8327,uvs',tps,typ0,uu____8331,constrs,uu____8333,uu____8334)
                                          ->
                                          Some
                                            (tps, typ0,
                                              ((FStar_List.length constrs) >
                                                 (Prims.parse_int "1")))
                                      | uu____8348 -> failwith "Impossible")
                                 | uu____8353 -> None) in
                          match tps_opt with
                          | Some x -> x
                          | None  ->
                              (match FStar_Ident.lid_equals typ_lid
                                       FStar_Syntax_Const.exn_lid
                               with
                               | true  ->
                                   ([], FStar_Syntax_Util.ktype0, true)
                               | uu____8380 ->
                                   Prims.raise
                                     (FStar_Errors.Error
                                        ("Unexpected data constructor", r))) in
                        (match uu____8302 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ0 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8390 =
                               FStar_Syntax_Util.arrow_formals typ0 in
                             (match uu____8390 with
                              | (indices,uu____8400) ->
                                  let refine_domain =
                                    let uu____8412 =
                                      FStar_All.pipe_right quals
                                        (FStar_Util.for_some
                                           (fun uu___109_8414  ->
                                              match uu___109_8414 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8415 -> true
                                              | uu____8420 -> false)) in
                                    match uu____8412 with
                                    | true  -> false
                                    | uu____8421 -> should_refine in
                                  let fv_qual =
                                    let filter_records uu___110_8427 =
                                      match uu___110_8427 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8429,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8436 -> None in
                                    let uu____8437 =
                                      FStar_Util.find_map quals
                                        filter_records in
                                    match uu____8437 with
                                    | None  -> FStar_Syntax_Syntax.Data_ctor
                                    | Some q -> q in
                                  let iquals =
                                    match FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            iquals
                                    with
                                    | true  -> FStar_Syntax_Syntax.Private ::
                                        iquals
                                    | uu____8443 -> iquals in
                                  let fields =
                                    let uu____8445 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8445 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8476  ->
                                               fun uu____8477  ->
                                                 match (uu____8476,
                                                         uu____8477)
                                                 with
                                                 | ((x,uu____8487),(x',uu____8489))
                                                     ->
                                                     let uu____8494 =
                                                       let uu____8499 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8499) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8494) imp_tps
                                            inductive_tps in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals fv_qual refine_domain env typ_lid
                                    constr_lid uvs inductive_tps indices
                                    fields))))
          | uu____8500 -> []