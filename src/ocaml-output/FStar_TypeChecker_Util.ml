open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)
let report :
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let uu____12 = FStar_TypeChecker_Env.get_range env  in
      let uu____13 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.report uu____12 uu____13
  
let is_type : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____17 =
      let uu____18 = FStar_Syntax_Subst.compress t  in
      uu____18.FStar_Syntax_Syntax.n  in
    match uu____17 with
    | FStar_Syntax_Syntax.Tm_type uu____21 -> true
    | uu____22 -> false
  
let t_binders :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    let uu____29 = FStar_TypeChecker_Env.all_binders env  in
    FStar_All.pipe_right uu____29
      (FStar_List.filter
         (fun uu____35  ->
            match uu____35 with
            | (x,uu____39) -> is_type x.FStar_Syntax_Syntax.sort))
  
let new_uvar_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____49 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____50 = FStar_TypeChecker_Env.current_module env  in
             FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____50)
           in
        if uu____49
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env  in
      let uu____52 = FStar_TypeChecker_Env.get_range env  in
      FStar_TypeChecker_Env.new_uvar uu____52 bs k
  
let new_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun k  -> let uu____59 = new_uvar_aux env k  in Prims.fst uu____59
  
let as_uvar : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___92_64  ->
    match uu___92_64 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____66);
        FStar_Syntax_Syntax.tk = uu____67;
        FStar_Syntax_Syntax.pos = uu____68;
        FStar_Syntax_Syntax.vars = uu____69;_} -> uv
    | uu____84 -> failwith "Impossible"
  
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
          let uu____103 =
            FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid  in
          match uu____103 with
          | Some (uu____116::(tm,uu____118)::[]) ->
              let t =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))))
                  None tm.FStar_Syntax_Syntax.pos
                 in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____162 ->
              let uu____169 = new_uvar_aux env k  in
              (match uu____169 with
               | (t,u) ->
                   let g =
                     let uu___112_181 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     let uu____182 =
                       let uu____190 =
                         let uu____197 = as_uvar u  in
                         (reason, env, uu____197, t, k, r)  in
                       [uu____190]  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___112_181.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___112_181.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___112_181.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____182
                     }  in
                   let uu____210 =
                     let uu____214 =
                       let uu____217 = as_uvar u  in (uu____217, r)  in
                     [uu____214]  in
                   (t, uu____210, g))
  
let check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____235 =
        let uu____236 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____236  in
      if uu____235
      then
        let us =
          let uu____240 =
            let uu____242 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun uu____258  ->
                 match uu____258 with
                 | (x,uu____266) -> FStar_Syntax_Print.uvar_to_string x)
              uu____242
             in
          FStar_All.pipe_right uu____240 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____283 =
            let uu____284 = FStar_Syntax_Print.term_to_string t  in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____284
             in
          FStar_Errors.report r uu____283);
         FStar_Options.pop ())
      else ()
  
let force_sort' :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____293 = FStar_ST.read s.FStar_Syntax_Syntax.tk  in
    match uu____293 with
    | None  ->
        let uu____298 =
          let uu____299 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos  in
          let uu____300 = FStar_Syntax_Print.term_to_string s  in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____299 uu____300
           in
        failwith uu____298
    | Some tk -> tk
  
let force_sort s =
  let uu____315 =
    let uu____318 = force_sort' s  in FStar_Syntax_Syntax.mk uu____318  in
  uu____315 None s.FStar_Syntax_Syntax.pos 
let extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.typ *
        Prims.bool)
  =
  fun env  ->
    fun uu____335  ->
      match uu____335 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____342;
          FStar_Syntax_Syntax.lbdef = e;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (if univ_vars1 <> []
                then
                  failwith
                    "Impossible: non-empty universe variables but the type is unknown"
                else ();
                (let r = FStar_TypeChecker_Env.get_range env  in
                 let mk_binder1 scope a =
                   let uu____374 =
                     let uu____375 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort
                        in
                     uu____375.FStar_Syntax_Syntax.n  in
                   match uu____374 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____380 = FStar_Syntax_Util.type_u ()  in
                       (match uu____380 with
                        | (k,uu____386) ->
                            let t2 =
                              let uu____388 =
                                FStar_TypeChecker_Env.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k
                                 in
                              FStar_All.pipe_right uu____388 Prims.fst  in
                            ((let uu___113_393 = a  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___113_393.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___113_393.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____394 -> (a, true)  in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1  in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____419) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____426) ->
                       (t2, true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____453) ->
                       let uu____476 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____500  ->
                                 fun uu____501  ->
                                   match (uu____500, uu____501) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____543 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a  in
                                       (match uu____543 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp)  in
                                            let bs2 =
                                              FStar_List.append bs1 [b]  in
                                            let scope1 =
                                              FStar_List.append scope [b]  in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty))
                          in
                       (match uu____476 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____604 = aux must_check_ty1 scope body  in
                            (match uu____604 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____621 =
                                         FStar_Options.ml_ish ()  in
                                       if uu____621
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c  in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c  in
                                 ((let uu____626 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High
                                      in
                                   if uu____626
                                   then
                                     let uu____627 =
                                       FStar_Range.string_of_range r  in
                                     let uu____628 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____629 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2
                                        in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____627 uu____628 uu____629
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____633 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____641 =
                            let uu____644 =
                              let uu____645 =
                                FStar_TypeChecker_Env.new_uvar r vars
                                  FStar_Syntax_Util.ktype0
                                 in
                              FStar_All.pipe_right uu____645 Prims.fst  in
                            FStar_Util.Inl uu____644  in
                          (uu____641, false))
                    in
                 let uu____652 =
                   let uu____657 = t_binders env  in aux false uu____657 e
                    in
                 match uu____652 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____670 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                           if uu____670
                           then FStar_TypeChecker_Env.result_typ env c
                           else
                             (let uu____672 =
                                let uu____673 =
                                  let uu____676 =
                                    let uu____677 =
                                      FStar_Syntax_Print.comp_to_string c  in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____677
                                     in
                                  (uu____676, rng)  in
                                FStar_Errors.Error uu____673  in
                              Prims.raise uu____672)
                       | FStar_Util.Inl t3 -> t3  in
                     ([], t3, b)))
           | uu____680 ->
               let uu____681 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____681 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
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
        let rec pat_as_arg_with_env allow_wc_dependence env1 p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let e =
                (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c))
                  None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____764) ->
              let uu____769 = FStar_Syntax_Util.type_u ()  in
              (match uu____769 with
               | (k,uu____782) ->
                   let t = new_uvar env1 k  in
                   let x1 =
                     let uu___114_785 = x  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___114_785.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___114_785.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     }  in
                   let uu____786 =
                     let uu____789 = FStar_TypeChecker_Env.all_binders env1
                        in
                     FStar_TypeChecker_Env.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____789 t
                      in
                   (match uu____786 with
                    | (e,u) ->
                        let p2 =
                          let uu___115_804 = p1  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___115_804.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___115_804.FStar_Syntax_Syntax.p)
                          }  in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____811 = FStar_Syntax_Util.type_u ()  in
              (match uu____811 with
               | (t,uu____824) ->
                   let x1 =
                     let uu___116_826 = x  in
                     let uu____827 = new_uvar env1 t  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___116_826.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___116_826.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____827
                     }  in
                   let env2 =
                     if allow_wc_dependence
                     then FStar_TypeChecker_Env.push_bv env1 x1
                     else env1  in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____849 = FStar_Syntax_Util.type_u ()  in
              (match uu____849 with
               | (t,uu____862) ->
                   let x1 =
                     let uu___117_864 = x  in
                     let uu____865 = new_uvar env1 t  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___117_864.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___117_864.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____865
                     }  in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____897 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____953  ->
                        fun uu____954  ->
                          match (uu____953, uu____954) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1053 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2
                                 in
                              (match uu____1053 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], []))
                 in
              (match uu____897 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1161 =
                       let uu____1164 =
                         let uu____1165 =
                           let uu____1170 =
                             let uu____1173 =
                               let uu____1174 =
                                 FStar_Syntax_Syntax.fv_to_tm fv  in
                               let uu____1175 =
                                 FStar_All.pipe_right args FStar_List.rev  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1174
                                 uu____1175
                                in
                             uu____1173 None p1.FStar_Syntax_Syntax.p  in
                           (uu____1170,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app))
                            in
                         FStar_Syntax_Syntax.Tm_meta uu____1165  in
                       FStar_Syntax_Syntax.mk uu____1164  in
                     uu____1161 None p1.FStar_Syntax_Syntax.p  in
                   let uu____1192 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____1198 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____1204 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____1192, uu____1198, uu____1204, env2, e,
                     (let uu___118_1217 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___118_1217.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___118_1217.FStar_Syntax_Syntax.p)
                      })))
          | FStar_Syntax_Syntax.Pat_disj uu____1223 -> failwith "impossible"
           in
        let rec elaborate_pat env1 p1 =
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
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let pats1 =
                FStar_List.map
                  (fun uu____1292  ->
                     match uu____1292 with
                     | (p2,imp) ->
                         let uu____1307 = elaborate_pat env1 p2  in
                         (uu____1307, imp)) pats
                 in
              let uu____1312 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              (match uu____1312 with
               | (uu____1321,t) ->
                   let uu____1323 = FStar_Syntax_Util.arrow_formals_comp t
                      in
                   (match uu____1323 with
                    | (f,uu____1332) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1403::uu____1404) ->
                              Prims.raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1439::uu____1440,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1480  ->
                                      match uu____1480 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1498 =
                                                   let uu____1500 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1
                                                      in
                                                   Some uu____1500  in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1498
                                                   FStar_Syntax_Syntax.tun
                                                  in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                  in
                                               let uu____1506 =
                                                 maybe_dot inaccessible a r
                                                  in
                                               (uu____1506, true)
                                           | uu____1511 ->
                                               let uu____1513 =
                                                 let uu____1514 =
                                                   let uu____1517 =
                                                     let uu____1518 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1518
                                                      in
                                                   (uu____1517,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                                                    in
                                                 FStar_Errors.Error
                                                   uu____1514
                                                  in
                                               Prims.raise uu____1513)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1569,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1570))
                                   when p_imp ->
                                   let uu____1572 = aux formals' pats'  in
                                   (p2, true) :: uu____1572
                               | (uu____1584,Some
                                  (FStar_Syntax_Syntax.Implicit
                                  inaccessible)) ->
                                   let a =
                                     FStar_Syntax_Syntax.new_bv
                                       (Some (p2.FStar_Syntax_Syntax.p))
                                       FStar_Syntax_Syntax.tun
                                      in
                                   let p3 =
                                     maybe_dot inaccessible a
                                       (FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                      in
                                   let uu____1595 = aux formals' pats2  in
                                   (p3, true) :: uu____1595
                               | (uu____1607,imp) ->
                                   let uu____1611 =
                                     let uu____1616 =
                                       FStar_Syntax_Syntax.is_implicit imp
                                        in
                                     (p2, uu____1616)  in
                                   let uu____1619 = aux formals' pats'  in
                                   uu____1611 :: uu____1619)
                           in
                        let uu___119_1629 = p1  in
                        let uu____1632 =
                          let uu____1633 =
                            let uu____1641 = aux f pats1  in (fv, uu____1641)
                             in
                          FStar_Syntax_Syntax.Pat_cons uu____1633  in
                        {
                          FStar_Syntax_Syntax.v = uu____1632;
                          FStar_Syntax_Syntax.ty =
                            (uu___119_1629.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___119_1629.FStar_Syntax_Syntax.p)
                        }))
          | uu____1652 -> p1  in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____1678 = pat_as_arg_with_env allow_wc_dependence env1 p2
             in
          match uu____1678 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1708 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____1708 with
               | Some x ->
                   let uu____1721 =
                     let uu____1722 =
                       let uu____1725 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x
                          in
                       (uu____1725, (p3.FStar_Syntax_Syntax.p))  in
                     FStar_Errors.Error uu____1722  in
                   Prims.raise uu____1721
               | uu____1734 -> (b, a, w, arg, p3))
           in
        let top_level_pat_as_args env1 p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_disj [] -> failwith "impossible"
          | FStar_Syntax_Syntax.Pat_disj (q::pats) ->
              let uu____1777 = one_pat false env1 q  in
              (match uu____1777 with
               | (b,a,uu____1793,te,q1) ->
                   let uu____1802 =
                     FStar_List.fold_right
                       (fun p2  ->
                          fun uu____1818  ->
                            match uu____1818 with
                            | (w,args,pats1) ->
                                let uu____1842 = one_pat false env1 p2  in
                                (match uu____1842 with
                                 | (b',a',w',arg,p3) ->
                                     let uu____1868 =
                                       let uu____1869 =
                                         FStar_Util.multiset_equiv
                                           FStar_Syntax_Syntax.bv_eq a a'
                                          in
                                       Prims.op_Negation uu____1869  in
                                     if uu____1868
                                     then
                                       let uu____1876 =
                                         let uu____1877 =
                                           let uu____1880 =
                                             FStar_TypeChecker_Err.disjunctive_pattern_vars
                                               a a'
                                              in
                                           let uu____1881 =
                                             FStar_TypeChecker_Env.get_range
                                               env1
                                              in
                                           (uu____1880, uu____1881)  in
                                         FStar_Errors.Error uu____1877  in
                                       Prims.raise uu____1876
                                     else
                                       (let uu____1889 =
                                          let uu____1891 =
                                            FStar_Syntax_Syntax.as_arg arg
                                             in
                                          uu____1891 :: args  in
                                        ((FStar_List.append w' w),
                                          uu____1889, (p3 :: pats1))))) pats
                       ([], [], [])
                      in
                   (match uu____1802 with
                    | (w,args,pats1) ->
                        let uu____1912 =
                          let uu____1914 = FStar_Syntax_Syntax.as_arg te  in
                          uu____1914 :: args  in
                        ((FStar_List.append b w), uu____1912,
                          (let uu___120_1919 = p1  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_disj (q1 :: pats1));
                             FStar_Syntax_Syntax.ty =
                               (uu___120_1919.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___120_1919.FStar_Syntax_Syntax.p)
                           }))))
          | uu____1920 ->
              let uu____1921 = one_pat true env1 p1  in
              (match uu____1921 with
               | (b,uu____1936,uu____1937,arg,p2) ->
                   let uu____1946 =
                     let uu____1948 = FStar_Syntax_Syntax.as_arg arg  in
                     [uu____1948]  in
                   (b, uu____1946, p2))
           in
        let uu____1951 = top_level_pat_as_args env p  in
        match uu____1951 with
        | (b,args,p1) ->
            let exps = FStar_All.pipe_right args (FStar_List.map Prims.fst)
               in
            (b, exps, p1)
  
let decorate_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.pat
  =
  fun env  ->
    fun p  ->
      fun exps  ->
        let qq = p  in
        let rec aux p1 e =
          let pkg q t =
            FStar_Syntax_Syntax.withinfo q t p1.FStar_Syntax_Syntax.p  in
          let e1 = FStar_Syntax_Util.unmeta e  in
          match ((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n)) with
          | (uu____2022,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2024)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____2029,FStar_Syntax_Syntax.Tm_constant uu____2030) ->
              let uu____2031 = force_sort' e1  in
              pkg p1.FStar_Syntax_Syntax.v uu____2031
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2035 =
                    let uu____2036 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2037 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2036 uu____2037
                     in
                  failwith uu____2035)
               else ();
               (let uu____2040 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____2040
                then
                  let uu____2041 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____2042 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2041
                    uu____2042
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___121_2046 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___121_2046.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___121_2046.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2050 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____2050
                then
                  let uu____2051 =
                    let uu____2052 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2053 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2052 uu____2053
                     in
                  failwith uu____2051
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___122_2057 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___122_2057.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___122_2057.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2059),uu____2060) ->
              let s = force_sort e1  in
              let x1 =
                let uu___123_2069 = x  in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___123_2069.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___123_2069.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                }  in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2082 =
                  let uu____2083 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____2083  in
                if uu____2082
                then
                  let uu____2084 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2084
                else ());
               (let uu____2094 = force_sort' e1  in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____2094))
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
              ((let uu____2165 =
                  let uu____2166 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____2166 Prims.op_Negation  in
                if uu____2165
                then
                  let uu____2167 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2167
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2255 = force_sort' e1  in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2255
                  | (arg::args2,(argpat,uu____2268)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2318) ->
                           let x =
                             let uu____2334 = force_sort e2  in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2334
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2348) ->
                           let pat =
                             let uu____2363 = aux argpat e2  in
                             let uu____2364 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____2363, uu____2364)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2367 ->
                      let uu____2381 =
                        let uu____2382 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____2383 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2382 uu____2383
                         in
                      failwith uu____2381
                   in
                match_args [] args argpats))
          | uu____2390 ->
              let uu____2393 =
                let uu____2394 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____2395 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____2396 =
                  let uu____2397 =
                    FStar_All.pipe_right exps
                      (FStar_List.map FStar_Syntax_Print.term_to_string)
                     in
                  FStar_All.pipe_right uu____2397
                    (FStar_String.concat "\n\t")
                   in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2394 uu____2395 uu____2396
                 in
              failwith uu____2393
           in
        match ((p.FStar_Syntax_Syntax.v), exps) with
        | (FStar_Syntax_Syntax.Pat_disj ps,uu____2404) when
            (FStar_List.length ps) = (FStar_List.length exps) ->
            let ps1 = FStar_List.map2 aux ps exps  in
            FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj ps1)
              FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
              p.FStar_Syntax_Syntax.p
        | (uu____2420,e::[]) -> aux p e
        | uu____2423 -> failwith "Unexpected number of patterns"
  
let rec decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty)  in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p  in
    let pat_as_arg uu____2460 =
      match uu____2460 with
      | (p,i) ->
          let uu____2470 = decorated_pattern_as_term p  in
          (match uu____2470 with
           | (vars,te) ->
               let uu____2483 =
                 let uu____2486 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____2486)  in
               (vars, uu____2483))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____2493 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2501 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____2501)
    | FStar_Syntax_Syntax.Pat_wild x|FStar_Syntax_Syntax.Pat_var x ->
        let uu____2504 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____2504)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2518 =
          let uu____2526 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____2526 FStar_List.unzip  in
        (match uu____2518 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____2584 =
               let uu____2585 =
                 let uu____2586 =
                   let uu____2596 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____2596, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____2586  in
               mk1 uu____2585  in
             (vars1, uu____2584))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let arrow_formals :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun k  ->
      let uu____2620 = FStar_Syntax_Util.arrow_formals_comp k  in
      match uu____2620 with
      | (bs,c) ->
          let uu____2636 = FStar_TypeChecker_Env.result_typ env c  in
          (bs, uu____2636)
  
let join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2649 =
          let uu____2653 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____2654 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____2653 uu____2654  in
        match uu____2649 with | (m,uu____2656,uu____2657) -> m
  
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
        let c11 = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c1  in
        let c21 = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c2  in
        let uu____2671 =
          FStar_TypeChecker_Env.join env c11.FStar_TypeChecker_Env.nct_name
            c21.FStar_TypeChecker_Env.nct_name
           in
        match uu____2671 with
        | (m,lift1,lift2) ->
            let uu____2680 = lift1 env c11  in
            let uu____2683 = lift2 env c21  in (uu____2680, uu____2683)
  
let force_teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____2695 = FStar_TypeChecker_Rel.teq env t1 t2  in
        FStar_TypeChecker_Rel.force_trivial_guard env uu____2695
  
let join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.lcomp * FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc1  ->
      fun lc2  ->
        let uu____2707 =
          (FStar_Syntax_Util.is_total_lcomp lc1) &&
            (FStar_Syntax_Util.is_total_lcomp lc2)
           in
        if uu____2707
        then (lc1, lc2)
        else
          (let nct_of_lcomp lc =
             let uu____2715 =
               FStar_Syntax_Syntax.as_arg
                 lc.FStar_Syntax_Syntax.lcomp_res_typ
                in
             let uu____2716 =
               FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun  in
             {
               FStar_TypeChecker_Env.nct_name =
                 (lc.FStar_Syntax_Syntax.lcomp_name);
               FStar_TypeChecker_Env.nct_univs =
                 (lc.FStar_Syntax_Syntax.lcomp_univs);
               FStar_TypeChecker_Env.nct_indices =
                 (lc.FStar_Syntax_Syntax.lcomp_indices);
               FStar_TypeChecker_Env.nct_result = uu____2715;
               FStar_TypeChecker_Env.nct_wp = uu____2716;
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
                 (fun uu____2723  ->
                    FStar_TypeChecker_Env.normal_comp_typ_as_comp env nct)
             }  in
           let uu____2724 =
             FStar_TypeChecker_Env.join env
               lc1.FStar_Syntax_Syntax.lcomp_name
               lc2.FStar_Syntax_Syntax.lcomp_name
              in
           match uu____2724 with
           | (uu____2730,lift1,lift2) ->
               let nct1 =
                 let uu____2734 = nct_of_lcomp lc1  in lift1 env uu____2734
                  in
               let nct2 =
                 let uu____2738 = nct_of_lcomp lc2  in lift2 env uu____2738
                  in
               ((let uu____2742 =
                   FStar_List.tl nct1.FStar_TypeChecker_Env.nct_univs  in
                 let uu____2744 =
                   FStar_List.tl nct2.FStar_TypeChecker_Env.nct_univs  in
                 FStar_List.iter2
                   (fun u  ->
                      fun v1  ->
                        let uu____2748 = FStar_Syntax_Util.type_at_u u  in
                        let uu____2749 = FStar_Syntax_Util.type_at_u v1  in
                        force_teq env uu____2748 uu____2749) uu____2742
                   uu____2744);
                FStar_List.iter2
                  (fun uu____2755  ->
                     fun uu____2756  ->
                       match (uu____2755, uu____2756) with
                       | ((i,uu____2766),(j,uu____2768)) -> force_teq env i j)
                  nct1.FStar_TypeChecker_Env.nct_indices
                  nct2.FStar_TypeChecker_Env.nct_indices;
                ((lcomp_of_nct nct1), (lcomp_of_nct nct2))))
  
let is_pure_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid
  
let is_pure_or_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GHOST_lid)
  
let mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universes ->
      FStar_Syntax_Syntax.arg Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  =
  fun mname  ->
    fun univs1  ->
      fun indices  ->
        fun result  ->
          fun wp  ->
            fun flags  ->
              let uu____2809 =
                let uu____2810 =
                  let uu____2816 =
                    let uu____2818 = FStar_Syntax_Syntax.as_arg result  in
                    let uu____2819 =
                      let uu____2821 = FStar_Syntax_Syntax.as_arg wp  in
                      [uu____2821]  in
                    uu____2818 :: uu____2819  in
                  FStar_List.append indices uu____2816  in
                {
                  FStar_Syntax_Syntax.comp_typ_name = mname;
                  FStar_Syntax_Syntax.comp_univs = univs1;
                  FStar_Syntax_Syntax.effect_args = uu____2810;
                  FStar_Syntax_Syntax.flags = flags
                }  in
              FStar_Syntax_Syntax.mk_Comp uu____2809
  
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
  fun subst1  ->
    fun lc  ->
      let uu___124_2845 = lc  in
      let uu____2846 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.lcomp_res_typ
         in
      {
        FStar_Syntax_Syntax.lcomp_name =
          (uu___124_2845.FStar_Syntax_Syntax.lcomp_name);
        FStar_Syntax_Syntax.lcomp_univs =
          (uu___124_2845.FStar_Syntax_Syntax.lcomp_univs);
        FStar_Syntax_Syntax.lcomp_indices =
          (uu___124_2845.FStar_Syntax_Syntax.lcomp_indices);
        FStar_Syntax_Syntax.lcomp_res_typ = uu____2846;
        FStar_Syntax_Syntax.lcomp_cflags =
          (uu___124_2845.FStar_Syntax_Syntax.lcomp_cflags);
        FStar_Syntax_Syntax.lcomp_as_comp =
          (fun uu____2849  ->
             let uu____2850 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
             FStar_Syntax_Subst.subst_comp subst1 uu____2850)
      }
  
let is_function : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2854 =
      let uu____2855 = FStar_Syntax_Subst.compress t  in
      uu____2855.FStar_Syntax_Syntax.n  in
    match uu____2854 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2858 -> true
    | uu____2866 -> false
  
let return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun t  ->
      fun v1  ->
        let c =
          let uu____2877 =
            let uu____2878 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid
               in
            FStar_All.pipe_left Prims.op_Negation uu____2878  in
          if uu____2877
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               let uu____2881 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   FStar_Syntax_Const.effect_PURE_lid
                  in
               FStar_Util.must uu____2881  in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t  in
             let wp =
               let uu____2885 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                  in
               if uu____2885
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2887 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid
                     in
                  match uu____2887 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp
                         in
                      let uu____2893 =
                        let uu____2894 =
                          let uu____2895 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                             in
                          let uu____2896 =
                            let uu____2897 = FStar_Syntax_Syntax.as_arg t  in
                            let uu____2898 =
                              let uu____2900 = FStar_Syntax_Syntax.as_arg v1
                                 in
                              [uu____2900]  in
                            uu____2897 :: uu____2898  in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2895 uu____2896
                           in
                        uu____2894 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos
                         in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2893)
                in
             (mk_comp m) [u_t] [] t wp [FStar_Syntax_Syntax.RETURN])
           in
        (let uu____2906 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return")
            in
         if uu____2906
         then
           let uu____2907 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
           let uu____2908 = FStar_Syntax_Print.term_to_string v1  in
           let uu____2909 = FStar_TypeChecker_Normalize.comp_to_string env c
              in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2907
             uu____2908 uu____2909
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
        fun uu____2923  ->
          match uu____2923 with
          | (b,lc2) ->
              let lc11 =
                FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
              let lc21 =
                FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
              ((let uu____2932 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                if uu____2932
                then
                  let bstr =
                    match b with
                    | None  -> "none"
                    | Some x -> FStar_Syntax_Print.bv_to_string x  in
                  let uu____2935 =
                    match e1opt with
                    | None  -> "None"
                    | Some e -> FStar_Syntax_Print.term_to_string e  in
                  let uu____2937 = FStar_Syntax_Print.lcomp_to_string lc11
                     in
                  let uu____2938 = FStar_Syntax_Print.lcomp_to_string lc21
                     in
                  FStar_Util.print4
                    "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                    uu____2935 uu____2937 bstr uu____2938
                else ());
               (let uu____2940 = join_lcomp env lc11 lc21  in
                match uu____2940 with
                | (lc12,lc22) ->
                    let bind_it uu____2948 =
                      let c1 = lc12.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                      let c2 = lc22.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                      (let uu____2956 =
                         FStar_TypeChecker_Env.debug env
                           FStar_Options.Extreme
                          in
                       if uu____2956
                       then
                         let uu____2957 =
                           match b with
                           | None  -> "none"
                           | Some x -> FStar_Syntax_Print.bv_to_string x  in
                         let uu____2959 =
                           FStar_Syntax_Print.lcomp_to_string lc12  in
                         let uu____2960 =
                           FStar_Syntax_Print.comp_to_string c1  in
                         let uu____2961 =
                           FStar_Syntax_Print.lcomp_to_string lc22  in
                         let uu____2962 =
                           FStar_Syntax_Print.comp_to_string c2  in
                         FStar_Util.print5
                           "b=%s,Evaluated %s to %s\n And %s to %s\n"
                           uu____2957 uu____2959 uu____2960 uu____2961
                           uu____2962
                       else ());
                      (let try_simplify uu____2970 =
                         let aux uu____2979 =
                           let uu____2980 =
                             FStar_Syntax_Util.is_trivial_wp c1  in
                           if uu____2980
                           then
                             match b with
                             | None  -> Some (c2, "trivial no binder")
                             | Some uu____2997 ->
                                 let uu____2998 =
                                   FStar_Syntax_Util.is_ml_comp c2  in
                                 (if uu____2998
                                  then Some (c2, "trivial ml")
                                  else None)
                           else
                             (let uu____3016 =
                                (FStar_Syntax_Util.is_ml_comp c1) &&
                                  (FStar_Syntax_Util.is_ml_comp c2)
                                 in
                              if uu____3016
                              then Some (c2, "both ml")
                              else None)
                            in
                         let subst_c2 reason =
                           match (e1opt, b) with
                           | (Some e,Some x) ->
                               let uu____3049 =
                                 let uu____3052 =
                                   FStar_Syntax_Subst.subst_comp
                                     [FStar_Syntax_Syntax.NT (x, e)] c2
                                    in
                                 (uu____3052, reason)  in
                               Some uu____3049
                           | uu____3055 -> aux ()  in
                         let uu____3060 =
                           (FStar_Syntax_Util.is_total_comp c1) &&
                             (FStar_Syntax_Util.is_total_comp c2)
                            in
                         if uu____3060
                         then subst_c2 "both total"
                         else
                           (let uu____3065 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                               in
                            if uu____3065
                            then
                              let uu____3069 =
                                let uu____3072 =
                                  let uu____3073 =
                                    FStar_TypeChecker_Env.result_typ env c2
                                     in
                                  FStar_Syntax_Syntax.mk_GTotal uu____3073
                                   in
                                (uu____3072, "both gtot")  in
                              Some uu____3069
                            else
                              (match (e1opt, b) with
                               | (Some e,Some x) ->
                                   let uu____3086 =
                                     (FStar_Syntax_Util.is_total_comp c1) &&
                                       (let uu____3087 =
                                          FStar_Syntax_Syntax.is_null_bv x
                                           in
                                        Prims.op_Negation uu____3087)
                                      in
                                   if uu____3086
                                   then subst_c2 "substituted e"
                                   else aux ()
                               | uu____3092 -> aux ()))
                          in
                       let uu____3097 = try_simplify ()  in
                       match uu____3097 with
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
                                   let uu____3127 =
                                     FStar_Syntax_Syntax.null_binder
                                       (Prims.fst
                                          nct1.FStar_TypeChecker_Env.nct_result)
                                      in
                                   [uu____3127]
                               | Some x ->
                                   let uu____3131 =
                                     FStar_Syntax_Syntax.mk_binder x  in
                                   [uu____3131]
                                in
                             FStar_Syntax_Util.abs bs wp
                               (Some
                                  (FStar_Util.Inr
                                     (FStar_Syntax_Const.effect_Tot_lid,
                                       [FStar_Syntax_Syntax.TOTAL])))
                              in
                           let bind_inst =
                             let uu____3142 =
                               let uu____3143 =
                                 let uu____3145 =
                                   FStar_List.hd
                                     nct2.FStar_TypeChecker_Env.nct_univs
                                    in
                                 [uu____3145]  in
                               FStar_List.append
                                 nct1.FStar_TypeChecker_Env.nct_univs
                                 uu____3143
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               uu____3142 env md
                               md.FStar_Syntax_Syntax.bind_wp
                              in
                           let bind_args =
                             let uu____3152 =
                               let uu____3158 =
                                 let uu____3160 =
                                   let uu____3162 =
                                     let uu____3164 =
                                       let uu____3165 =
                                         mk_lam
                                           (Prims.fst
                                              nct2.FStar_TypeChecker_Env.nct_wp)
                                          in
                                       FStar_Syntax_Syntax.as_arg uu____3165
                                        in
                                     [uu____3164]  in
                                   (nct1.FStar_TypeChecker_Env.nct_wp) ::
                                     uu____3162
                                    in
                                 (nct2.FStar_TypeChecker_Env.nct_result) ::
                                   uu____3160
                                  in
                               (nct1.FStar_TypeChecker_Env.nct_result) ::
                                 uu____3158
                                in
                             FStar_List.append
                               nct1.FStar_TypeChecker_Env.nct_indices
                               uu____3152
                              in
                           let wp =
                             (FStar_Syntax_Syntax.mk_Tm_app bind_inst
                                bind_args) None t2.FStar_Syntax_Syntax.pos
                              in
                           let nct =
                             let uu___125_3180 = nct2  in
                             let uu____3181 = FStar_Syntax_Syntax.as_arg wp
                                in
                             {
                               FStar_TypeChecker_Env.nct_name =
                                 (uu___125_3180.FStar_TypeChecker_Env.nct_name);
                               FStar_TypeChecker_Env.nct_univs =
                                 (uu___125_3180.FStar_TypeChecker_Env.nct_univs);
                               FStar_TypeChecker_Env.nct_indices =
                                 (uu___125_3180.FStar_TypeChecker_Env.nct_indices);
                               FStar_TypeChecker_Env.nct_result =
                                 (uu___125_3180.FStar_TypeChecker_Env.nct_result);
                               FStar_TypeChecker_Env.nct_wp = uu____3181;
                               FStar_TypeChecker_Env.nct_flags =
                                 (uu___125_3180.FStar_TypeChecker_Env.nct_flags)
                             }  in
                           FStar_TypeChecker_Env.normal_comp_typ_as_comp env
                             nct)
                       in
                    let uu____3182 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3182
                    then lc22
                    else
                      (let uu___126_3184 = lc22  in
                       {
                         FStar_Syntax_Syntax.lcomp_name =
                           (uu___126_3184.FStar_Syntax_Syntax.lcomp_name);
                         FStar_Syntax_Syntax.lcomp_univs =
                           (uu___126_3184.FStar_Syntax_Syntax.lcomp_univs);
                         FStar_Syntax_Syntax.lcomp_indices =
                           (uu___126_3184.FStar_Syntax_Syntax.lcomp_indices);
                         FStar_Syntax_Syntax.lcomp_res_typ =
                           (uu___126_3184.FStar_Syntax_Syntax.lcomp_res_typ);
                         FStar_Syntax_Syntax.lcomp_cflags =
                           (uu___126_3184.FStar_Syntax_Syntax.lcomp_cflags);
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
          | Some reason1 ->
              let uu____3228 =
                let uu____3229 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____3229  in
              if uu____3228
              then f
              else (let uu____3231 = reason1 ()  in label uu____3231 r f)
  
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
            let uu___127_3242 = g  in
            let uu____3243 =
              let uu____3244 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____3244  in
            {
              FStar_TypeChecker_Env.guard_f = uu____3243;
              FStar_TypeChecker_Env.deferred =
                (uu___127_3242.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___127_3242.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___127_3242.FStar_TypeChecker_Env.implicits)
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
      | uu____3254 -> g2
  
let weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3271 =
          let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          match f with
          | FStar_TypeChecker_Common.Trivial  -> c
          | FStar_TypeChecker_Common.NonTrivial f1 ->
              let uu____3278 = FStar_Syntax_Util.is_ml_comp c  in
              if uu____3278
              then c
              else
                (let nct =
                   FStar_TypeChecker_Env.comp_as_normal_comp_typ env c  in
                 let md =
                   FStar_TypeChecker_Env.get_effect_decl env
                     nct.FStar_TypeChecker_Env.nct_name
                    in
                 let wp =
                   let uu____3287 =
                     let uu____3288 =
                       FStar_All.pipe_right nct.FStar_TypeChecker_Env.nct_wp
                         Prims.fst
                        in
                     uu____3288.FStar_Syntax_Syntax.pos  in
                   let uu____3295 =
                     let uu____3296 =
                       FStar_TypeChecker_Env.inst_effect_fun_with
                         nct.FStar_TypeChecker_Env.nct_univs env md
                         md.FStar_Syntax_Syntax.assume_p
                        in
                     let uu____3297 =
                       let uu____3298 =
                         let uu____3304 =
                           let uu____3306 = FStar_Syntax_Syntax.as_arg f1  in
                           [uu____3306; nct.FStar_TypeChecker_Env.nct_wp]  in
                         (nct.FStar_TypeChecker_Env.nct_result) :: uu____3304
                          in
                       FStar_List.append
                         nct.FStar_TypeChecker_Env.nct_indices uu____3298
                        in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3296 uu____3297  in
                   uu____3295 None uu____3287  in
                 let uu____3315 =
                   let uu___128_3316 = nct  in
                   let uu____3317 = FStar_Syntax_Syntax.as_arg wp  in
                   {
                     FStar_TypeChecker_Env.nct_name =
                       (uu___128_3316.FStar_TypeChecker_Env.nct_name);
                     FStar_TypeChecker_Env.nct_univs =
                       (uu___128_3316.FStar_TypeChecker_Env.nct_univs);
                     FStar_TypeChecker_Env.nct_indices =
                       (uu___128_3316.FStar_TypeChecker_Env.nct_indices);
                     FStar_TypeChecker_Env.nct_result =
                       (uu___128_3316.FStar_TypeChecker_Env.nct_result);
                     FStar_TypeChecker_Env.nct_wp = uu____3317;
                     FStar_TypeChecker_Env.nct_flags =
                       (uu___128_3316.FStar_TypeChecker_Env.nct_flags)
                   }  in
                 FStar_TypeChecker_Env.normal_comp_typ_as_comp env uu____3315)
           in
        let uu____3318 =
          env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
        if uu____3318
        then lc
        else
          (let uu___129_3320 = lc  in
           {
             FStar_Syntax_Syntax.lcomp_name =
               (uu___129_3320.FStar_Syntax_Syntax.lcomp_name);
             FStar_Syntax_Syntax.lcomp_univs =
               (uu___129_3320.FStar_Syntax_Syntax.lcomp_univs);
             FStar_Syntax_Syntax.lcomp_indices =
               (uu___129_3320.FStar_Syntax_Syntax.lcomp_indices);
             FStar_Syntax_Syntax.lcomp_res_typ =
               (uu___129_3320.FStar_Syntax_Syntax.lcomp_res_typ);
             FStar_Syntax_Syntax.lcomp_cflags =
               (uu___129_3320.FStar_Syntax_Syntax.lcomp_cflags);
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
            let uu____3347 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____3347
            then (lc, g0)
            else
              ((let uu____3352 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme
                   in
                if uu____3352
                then
                  let uu____3353 =
                    FStar_TypeChecker_Normalize.term_to_string env e  in
                  let uu____3354 =
                    FStar_TypeChecker_Rel.guard_to_string env g0  in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3353 uu____3354
                else ());
               (let strengthen uu____3361 =
                  let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                  let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                  let uu____3366 = FStar_TypeChecker_Rel.guard_form g01  in
                  match uu____3366 with
                  | FStar_TypeChecker_Common.Trivial  -> c
                  | FStar_TypeChecker_Common.NonTrivial f ->
                      let c1 =
                        let uu____3373 =
                          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                            (let uu____3374 =
                               FStar_Syntax_Util.is_partial_return c  in
                             Prims.op_Negation uu____3374)
                           in
                        if uu____3373
                        then
                          let x =
                            let uu____3378 =
                              FStar_TypeChecker_Env.result_typ env c  in
                            FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                              None uu____3378
                             in
                          let xret =
                            let uu____3382 =
                              let uu____3383 =
                                FStar_Syntax_Syntax.bv_to_name x  in
                              return_value env x.FStar_Syntax_Syntax.sort
                                uu____3383
                               in
                            FStar_Syntax_Util.comp_set_flags uu____3382
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             in
                          let lc1 =
                            let uu____3385 =
                              FStar_TypeChecker_Env.lcomp_of_comp env c  in
                            let uu____3386 =
                              let uu____3387 =
                                FStar_TypeChecker_Env.lcomp_of_comp env xret
                                 in
                              ((Some x), uu____3387)  in
                            bind env (Some e) uu____3385 uu____3386  in
                          lc1.FStar_Syntax_Syntax.lcomp_as_comp ()
                        else c  in
                      let ct = FStar_TypeChecker_Env.comp_to_comp_typ env c1
                         in
                      if
                        (FStar_Ident.lid_equals
                           ct.FStar_Syntax_Syntax.comp_typ_name
                           FStar_Syntax_Const.effect_Tot_lid)
                          ||
                          (FStar_Ident.lid_equals
                             ct.FStar_Syntax_Syntax.comp_typ_name
                             FStar_Syntax_Const.effect_GTot_lid)
                      then c1
                      else
                        ((let uu____3395 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____3395
                          then
                            let uu____3396 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e
                               in
                            let uu____3397 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____3396 uu____3397
                          else ());
                         (let nct =
                            FStar_TypeChecker_Env.comp_as_normal_comp_typ env
                              c1
                             in
                          let md =
                            FStar_TypeChecker_Env.get_effect_decl env
                              nct.FStar_TypeChecker_Env.nct_name
                             in
                          let wp =
                            let uu____3404 =
                              let uu____3405 =
                                FStar_All.pipe_right
                                  nct.FStar_TypeChecker_Env.nct_wp Prims.fst
                                 in
                              uu____3405.FStar_Syntax_Syntax.pos  in
                            let uu____3412 =
                              let uu____3413 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  nct.FStar_TypeChecker_Env.nct_univs env md
                                  md.FStar_Syntax_Syntax.assert_p
                                 in
                              let uu____3414 =
                                let uu____3415 =
                                  let uu____3421 =
                                    let uu____3423 =
                                      let uu____3424 =
                                        let uu____3425 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        label_opt env reason uu____3425 f  in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Syntax.as_arg uu____3424
                                       in
                                    [uu____3423;
                                    nct.FStar_TypeChecker_Env.nct_wp]  in
                                  (nct.FStar_TypeChecker_Env.nct_result) ::
                                    uu____3421
                                   in
                                FStar_List.append
                                  nct.FStar_TypeChecker_Env.nct_indices
                                  uu____3415
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app uu____3413
                                uu____3414
                               in
                            uu____3412 None uu____3404  in
                          (let uu____3435 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme
                              in
                           if uu____3435
                           then
                             let uu____3436 =
                               FStar_Syntax_Print.term_to_string wp  in
                             FStar_Util.print1
                               "-------------Strengthened pre-condition is %s\n"
                               uu____3436
                           else ());
                          (let c2 =
                             let uu____3439 =
                               let uu___130_3440 = nct  in
                               let uu____3441 = FStar_Syntax_Syntax.as_arg wp
                                  in
                               {
                                 FStar_TypeChecker_Env.nct_name =
                                   (uu___130_3440.FStar_TypeChecker_Env.nct_name);
                                 FStar_TypeChecker_Env.nct_univs =
                                   (uu___130_3440.FStar_TypeChecker_Env.nct_univs);
                                 FStar_TypeChecker_Env.nct_indices =
                                   (uu___130_3440.FStar_TypeChecker_Env.nct_indices);
                                 FStar_TypeChecker_Env.nct_result =
                                   (uu___130_3440.FStar_TypeChecker_Env.nct_result);
                                 FStar_TypeChecker_Env.nct_wp = uu____3441;
                                 FStar_TypeChecker_Env.nct_flags =
                                   (uu___130_3440.FStar_TypeChecker_Env.nct_flags)
                               }  in
                             FStar_TypeChecker_Env.normal_comp_typ_as_comp
                               env uu____3439
                              in
                           c2)))
                   in
                let flags =
                  let uu____3444 =
                    (FStar_Syntax_Util.is_pure_lcomp lc) &&
                      (let uu____3445 =
                         FStar_Syntax_Util.is_function_typ
                           lc.FStar_Syntax_Syntax.lcomp_res_typ
                          in
                       FStar_All.pipe_left Prims.op_Negation uu____3445)
                     in
                  if uu____3444
                  then
                    FStar_All.pipe_right lc.FStar_Syntax_Syntax.lcomp_cflags
                      (FStar_List.collect
                         (fun uu___93_3449  ->
                            match uu___93_3449 with
                            | FStar_Syntax_Syntax.RETURN 
                              |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                [FStar_Syntax_Syntax.PARTIAL_RETURN]
                            | uu____3451 -> []))
                  else []  in
                let lc1 =
                  let uu___131_3454 = lc  in
                  {
                    FStar_Syntax_Syntax.lcomp_name =
                      (uu___131_3454.FStar_Syntax_Syntax.lcomp_name);
                    FStar_Syntax_Syntax.lcomp_univs =
                      (uu___131_3454.FStar_Syntax_Syntax.lcomp_univs);
                    FStar_Syntax_Syntax.lcomp_indices =
                      (uu___131_3454.FStar_Syntax_Syntax.lcomp_indices);
                    FStar_Syntax_Syntax.lcomp_res_typ =
                      (uu___131_3454.FStar_Syntax_Syntax.lcomp_res_typ);
                    FStar_Syntax_Syntax.lcomp_cflags = flags;
                    FStar_Syntax_Syntax.lcomp_as_comp =
                      (uu___131_3454.FStar_Syntax_Syntax.lcomp_as_comp)
                  }  in
                let lc2 =
                  let uu____3456 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3456
                  then lc1
                  else
                    (let uu___132_3458 = lc1  in
                     {
                       FStar_Syntax_Syntax.lcomp_name =
                         (uu___132_3458.FStar_Syntax_Syntax.lcomp_name);
                       FStar_Syntax_Syntax.lcomp_univs =
                         (uu___132_3458.FStar_Syntax_Syntax.lcomp_univs);
                       FStar_Syntax_Syntax.lcomp_indices =
                         (uu___132_3458.FStar_Syntax_Syntax.lcomp_indices);
                       FStar_Syntax_Syntax.lcomp_res_typ =
                         (uu___132_3458.FStar_Syntax_Syntax.lcomp_res_typ);
                       FStar_Syntax_Syntax.lcomp_cflags =
                         (uu___132_3458.FStar_Syntax_Syntax.lcomp_cflags);
                       FStar_Syntax_Syntax.lcomp_as_comp = strengthen
                     })
                   in
                (lc2,
                  (let uu___133_3459 = g0  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___133_3459.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___133_3459.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___133_3459.FStar_TypeChecker_Env.implicits)
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
        let uu____3474 =
          let uu____3477 = FStar_Syntax_Syntax.bv_to_name x  in
          let uu____3478 = FStar_Syntax_Syntax.bv_to_name y  in
          (uu____3477, uu____3478)  in
        match uu____3474 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t  in
            let yret =
              let uu____3487 =
                let uu____3488 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____3489 =
                  let uu____3490 = FStar_Syntax_Syntax.as_arg res_t  in
                  let uu____3491 =
                    let uu____3493 = FStar_Syntax_Syntax.as_arg yexp  in
                    [uu____3493]  in
                  uu____3490 :: uu____3491  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3488 uu____3489  in
              uu____3487 None res_t.FStar_Syntax_Syntax.pos  in
            let x_eq_y_yret =
              let uu____3501 =
                let uu____3502 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p
                   in
                let uu____3503 =
                  let uu____3504 = FStar_Syntax_Syntax.as_arg res_t  in
                  let uu____3505 =
                    let uu____3507 =
                      let uu____3508 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp  in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3508
                       in
                    let uu____3509 =
                      let uu____3511 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret
                         in
                      [uu____3511]  in
                    uu____3507 :: uu____3509  in
                  uu____3504 :: uu____3505  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3502 uu____3503  in
              uu____3501 None res_t.FStar_Syntax_Syntax.pos  in
            let forall_y_x_eq_y_yret =
              let uu____3519 =
                let uu____3520 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp
                   in
                let uu____3521 =
                  let uu____3522 = FStar_Syntax_Syntax.as_arg res_t  in
                  let uu____3523 =
                    let uu____3525 = FStar_Syntax_Syntax.as_arg res_t  in
                    let uu____3526 =
                      let uu____3528 =
                        let uu____3529 =
                          let uu____3530 =
                            let uu____3534 = FStar_Syntax_Syntax.mk_binder y
                               in
                            [uu____3534]  in
                          FStar_Syntax_Util.abs uu____3530 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL])))
                           in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3529
                         in
                      [uu____3528]  in
                    uu____3525 :: uu____3526  in
                  uu____3522 :: uu____3523  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3520 uu____3521  in
              uu____3519 None res_t.FStar_Syntax_Syntax.pos  in
            let lc2 =
              (mk_comp md_pure) [u_res_t] [] res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN]
               in
            let lc =
              let uu____3550 = FStar_TypeChecker_Env.lcomp_of_comp env comp
                 in
              let uu____3551 =
                let uu____3552 = FStar_TypeChecker_Env.lcomp_of_comp env lc2
                   in
                ((Some x), uu____3552)  in
              bind env None uu____3550 uu____3551  in
            lc.FStar_Syntax_Syntax.lcomp_as_comp ()
  
let fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun lid  ->
      let uu____3560 =
        let uu____3561 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____3561  in
      FStar_Syntax_Syntax.fvar uu____3560 FStar_Syntax_Syntax.Delta_constant
        None
  
let bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.formula * FStar_Syntax_Syntax.lcomp) Prims.list ->
        FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let uu____3577 =
          let uu____3583 =
            let uu____3589 =
              let uu____3590 = FStar_Syntax_Syntax.mk_Total res_t  in
              FStar_TypeChecker_Env.lcomp_of_comp env uu____3590  in
            (uu____3589, [])  in
          FStar_List.fold_right
            (fun uu____3603  ->
               fun uu____3604  ->
                 match (uu____3603, uu____3604) with
                 | ((formula,lc),(out,lcases1)) ->
                     let uu____3641 = join_lcomp env lc out  in
                     (match uu____3641 with
                      | (lc1,_out) -> (lc1, ((formula, lc1) :: lcases1))))
            lcases uu____3583
           in
        match uu____3577 with
        | (lc,lcases1) ->
            let bind_cases uu____3669 =
              let if_then_else1 guard cthen celse =
                let uu____3680 = lift_and_destruct env cthen celse  in
                match uu____3680 with
                | (nct_then,nct_else) ->
                    let md =
                      FStar_TypeChecker_Env.get_effect_decl env
                        nct_then.FStar_TypeChecker_Env.nct_name
                       in
                    let wp =
                      let uu____3689 =
                        FStar_Range.union_ranges
                          (Prims.fst nct_then.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                          (Prims.fst nct_else.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                         in
                      let uu____3694 =
                        let uu____3695 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            nct_then.FStar_TypeChecker_Env.nct_univs env md
                            md.FStar_Syntax_Syntax.if_then_else
                           in
                        let uu____3696 =
                          let uu____3697 =
                            let uu____3703 = FStar_Syntax_Syntax.as_arg res_t
                               in
                            let uu____3704 =
                              let uu____3706 =
                                FStar_Syntax_Syntax.as_arg guard  in
                              [uu____3706;
                              nct_then.FStar_TypeChecker_Env.nct_wp;
                              nct_else.FStar_TypeChecker_Env.nct_wp]  in
                            uu____3703 :: uu____3704  in
                          FStar_List.append
                            nct_then.FStar_TypeChecker_Env.nct_indices
                            uu____3697
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3695 uu____3696
                         in
                      uu____3694 None uu____3689  in
                    (mk_comp md) nct_then.FStar_TypeChecker_Env.nct_univs
                      nct_then.FStar_TypeChecker_Env.nct_indices res_t wp []
                 in
              let default_case =
                let post_k =
                  let uu____3717 =
                    let uu____3718 = FStar_Syntax_Syntax.null_binder res_t
                       in
                    [uu____3718]  in
                  let uu____3719 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
                  FStar_Syntax_Util.arrow uu____3717 uu____3719  in
                let kwp =
                  let uu____3721 =
                    let uu____3722 = FStar_Syntax_Syntax.null_binder post_k
                       in
                    [uu____3722]  in
                  let uu____3723 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
                  FStar_Syntax_Util.arrow uu____3721 uu____3723  in
                let post = FStar_Syntax_Syntax.new_bv None post_k  in
                let wp =
                  let uu____3726 =
                    let uu____3730 = FStar_Syntax_Syntax.mk_binder post  in
                    [uu____3730]  in
                  let uu____3731 =
                    let uu____3732 =
                      let uu____3735 = FStar_TypeChecker_Env.get_range env
                         in
                      label FStar_TypeChecker_Err.exhaustiveness_check
                        uu____3735
                       in
                    let uu____3736 =
                      fvar_const env FStar_Syntax_Const.false_lid  in
                    FStar_All.pipe_left uu____3732 uu____3736  in
                  FStar_Syntax_Util.abs uu____3726 uu____3731
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
                  (fun uu____3751  ->
                     fun celse  ->
                       match uu____3751 with
                       | (g,cthen) ->
                           let uu____3757 =
                             cthen.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                           if_then_else1 g uu____3757 celse) lcases1
                  default_case
                 in
              let uu____3758 =
                let uu____3759 = FStar_Options.split_cases ()  in
                uu____3759 > (Prims.parse_int "0")  in
              if uu____3758
              then add_equality_to_post_condition env comp res_t
              else
                (let nct =
                   FStar_TypeChecker_Env.comp_as_normal_comp_typ env comp  in
                 let md =
                   FStar_TypeChecker_Env.get_effect_decl env
                     nct.FStar_TypeChecker_Env.nct_name
                    in
                 let share_post_wp =
                   let uu____3768 =
                     let uu____3769 =
                       FStar_TypeChecker_Env.inst_effect_fun_with
                         nct.FStar_TypeChecker_Env.nct_univs env md
                         md.FStar_Syntax_Syntax.ite_wp
                        in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3769
                       (FStar_List.append
                          nct.FStar_TypeChecker_Env.nct_indices
                          [nct.FStar_TypeChecker_Env.nct_result;
                          nct.FStar_TypeChecker_Env.nct_wp])
                      in
                   uu____3768 None
                     (Prims.fst nct.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                    in
                 (mk_comp md) nct.FStar_TypeChecker_Env.nct_univs
                   nct.FStar_TypeChecker_Env.nct_indices
                   (Prims.fst nct.FStar_TypeChecker_Env.nct_result)
                   share_post_wp [])
               in
            let uu____3782 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
            if uu____3782
            then lc
            else
              (let uu___134_3784 = lc  in
               {
                 FStar_Syntax_Syntax.lcomp_name =
                   (uu___134_3784.FStar_Syntax_Syntax.lcomp_name);
                 FStar_Syntax_Syntax.lcomp_univs =
                   (uu___134_3784.FStar_Syntax_Syntax.lcomp_univs);
                 FStar_Syntax_Syntax.lcomp_indices =
                   (uu___134_3784.FStar_Syntax_Syntax.lcomp_indices);
                 FStar_Syntax_Syntax.lcomp_res_typ =
                   (uu___134_3784.FStar_Syntax_Syntax.lcomp_res_typ);
                 FStar_Syntax_Syntax.lcomp_cflags =
                   (uu___134_3784.FStar_Syntax_Syntax.lcomp_cflags);
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
        let close1 uu____3801 =
          let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          let uu____3805 = FStar_Syntax_Util.is_ml_comp c  in
          if uu____3805
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
                        let uu____3821 =
                          let uu____3823 =
                            env.FStar_TypeChecker_Env.universe_of env
                              x.FStar_Syntax_Syntax.sort
                             in
                          [uu____3823]  in
                        FStar_List.append nct.FStar_TypeChecker_Env.nct_univs
                          uu____3821
                         in
                      let wp1 =
                        let uu____3825 =
                          let uu____3829 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3829]  in
                        FStar_Syntax_Util.abs uu____3825 wp
                          (Some
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])))
                         in
                      let uu____3839 =
                        let uu____3840 =
                          FStar_TypeChecker_Env.inst_effect_fun_with us env
                            md md.FStar_Syntax_Syntax.close_wp
                           in
                        let uu____3841 =
                          let uu____3842 =
                            let uu____3848 =
                              let uu____3850 =
                                FStar_Syntax_Syntax.as_arg
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____3851 =
                                let uu____3853 =
                                  FStar_Syntax_Syntax.as_arg wp1  in
                                [uu____3853]  in
                              uu____3850 :: uu____3851  in
                            (nct.FStar_TypeChecker_Env.nct_result) ::
                              uu____3848
                             in
                          FStar_List.append
                            nct.FStar_TypeChecker_Env.nct_indices uu____3842
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3840 uu____3841
                         in
                      uu____3839 None r) bvs
                 (Prims.fst nct.FStar_TypeChecker_Env.nct_wp)
                in
             (mk_comp md) nct.FStar_TypeChecker_Env.nct_univs
               nct.FStar_TypeChecker_Env.nct_indices
               (Prims.fst nct.FStar_TypeChecker_Env.nct_result) closed_wp
               nct.FStar_TypeChecker_Env.nct_flags)
           in
        let uu____3866 =
          env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
        if uu____3866
        then lc
        else
          (let uu___135_3868 = lc  in
           {
             FStar_Syntax_Syntax.lcomp_name =
               (uu___135_3868.FStar_Syntax_Syntax.lcomp_name);
             FStar_Syntax_Syntax.lcomp_univs =
               (uu___135_3868.FStar_Syntax_Syntax.lcomp_univs);
             FStar_Syntax_Syntax.lcomp_indices =
               (uu___135_3868.FStar_Syntax_Syntax.lcomp_indices);
             FStar_Syntax_Syntax.lcomp_res_typ =
               (uu___135_3868.FStar_Syntax_Syntax.lcomp_res_typ);
             FStar_Syntax_Syntax.lcomp_cflags =
               (uu___135_3868.FStar_Syntax_Syntax.lcomp_cflags);
             FStar_Syntax_Syntax.lcomp_as_comp = close1
           })
  
let maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let refine1 uu____3883 =
          let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          let uu____3887 =
            (let uu____3888 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.lcomp_name
                in
             Prims.op_Negation uu____3888) || env.FStar_TypeChecker_Env.lax
             in
          if uu____3887
          then c
          else
            (let uu____3892 = FStar_Syntax_Util.is_partial_return c  in
             if uu____3892
             then c
             else
               (let uu____3896 =
                  (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
                    (let uu____3897 =
                       FStar_TypeChecker_Env.lid_exists env
                         FStar_Syntax_Const.effect_GTot_lid
                        in
                     Prims.op_Negation uu____3897)
                   in
                if uu____3896
                then
                  let uu____3900 =
                    let uu____3901 =
                      FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                       in
                    let uu____3902 = FStar_Syntax_Print.term_to_string e  in
                    FStar_Util.format2 "%s: %s\n" uu____3901 uu____3902  in
                  failwith uu____3900
                else
                  (let nct =
                     FStar_TypeChecker_Env.comp_as_normal_comp_typ env c  in
                   let t = Prims.fst nct.FStar_TypeChecker_Env.nct_result  in
                   let c1 =
                     FStar_TypeChecker_Env.normal_comp_typ_as_comp env nct
                      in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (Some (t.FStar_Syntax_Syntax.pos)) t
                      in
                   let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                   let ret1 =
                     let uu____3916 =
                       let uu____3917 = return_value env t xexp  in
                       FStar_Syntax_Util.comp_set_flags uu____3917
                         [FStar_Syntax_Syntax.PARTIAL_RETURN]
                        in
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.lcomp_of_comp env) uu____3916
                      in
                   let eq1 =
                     let uu____3919 =
                       env.FStar_TypeChecker_Env.universe_of env t  in
                     FStar_Syntax_Util.mk_eq2 uu____3919 t xexp e  in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1)
                      in
                   let bind_lc =
                     let uu____3922 =
                       FStar_TypeChecker_Env.lcomp_of_comp env c1  in
                     bind env None uu____3922 ((Some x), eq_ret)  in
                   let uu____3924 =
                     bind_lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                   FStar_Syntax_Util.comp_set_flags uu____3924
                     (FStar_Syntax_Syntax.PARTIAL_RETURN ::
                     (FStar_Syntax_Util.comp_flags c1)))))
           in
        let flags =
          let uu____3927 =
            ((let uu____3928 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.lcomp_res_typ
                 in
              Prims.op_Negation uu____3928) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____3929 = FStar_Syntax_Util.is_lcomp_partial_return lc
                  in
               Prims.op_Negation uu____3929)
             in
          if uu____3927
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.lcomp_cflags)
          else lc.FStar_Syntax_Syntax.lcomp_cflags  in
        let uu___136_3932 = lc  in
        {
          FStar_Syntax_Syntax.lcomp_name =
            (uu___136_3932.FStar_Syntax_Syntax.lcomp_name);
          FStar_Syntax_Syntax.lcomp_univs =
            (uu___136_3932.FStar_Syntax_Syntax.lcomp_univs);
          FStar_Syntax_Syntax.lcomp_indices =
            (uu___136_3932.FStar_Syntax_Syntax.lcomp_indices);
          FStar_Syntax_Syntax.lcomp_res_typ =
            (uu___136_3932.FStar_Syntax_Syntax.lcomp_res_typ);
          FStar_Syntax_Syntax.lcomp_cflags = flags;
          FStar_Syntax_Syntax.lcomp_as_comp = refine1
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
          let uu____3951 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____3951 with
          | None  ->
              let uu____3956 =
                let uu____3957 =
                  let uu____3960 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c'
                     in
                  let uu____3961 = FStar_TypeChecker_Env.get_range env  in
                  (uu____3960, uu____3961)  in
                FStar_Errors.Error uu____3957  in
              Prims.raise uu____3956
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
          let uu____3982 =
            let uu____3983 = FStar_Syntax_Subst.compress t  in
            uu____3983.FStar_Syntax_Syntax.n  in
          match uu____3982 with
          | FStar_Syntax_Syntax.Tm_type uu____3988 ->
              let uu____3989 =
                let uu____3990 =
                  FStar_Syntax_Subst.compress
                    lc.FStar_Syntax_Syntax.lcomp_res_typ
                   in
                uu____3990.FStar_Syntax_Syntax.n  in
              (match uu____3989 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.bool_lid
                   ->
                   let uu____3996 =
                     FStar_TypeChecker_Env.lookup_lid env
                       FStar_Syntax_Const.b2t_lid
                      in
                   let b2t1 =
                     FStar_Syntax_Syntax.fvar
                       (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                          e.FStar_Syntax_Syntax.pos)
                       (FStar_Syntax_Syntax.Delta_defined_at_level
                          (Prims.parse_int "1")) None
                      in
                   let lc1 =
                     let uu____4001 =
                       let uu____4002 =
                         let uu____4003 =
                           FStar_Syntax_Syntax.mk_Total
                             FStar_Syntax_Util.ktype0
                            in
                         FStar_TypeChecker_Env.lcomp_of_comp env uu____4003
                          in
                       (None, uu____4002)  in
                     bind env (Some e) lc uu____4001  in
                   let e1 =
                     let uu____4008 =
                       let uu____4009 =
                         let uu____4010 = FStar_Syntax_Syntax.as_arg e  in
                         [uu____4010]  in
                       FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4009  in
                     uu____4008
                       (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                       e.FStar_Syntax_Syntax.pos
                      in
                   (e1, lc1)
               | uu____4017 -> (e, lc))
          | uu____4018 -> (e, lc)
  
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
              let uu____4044 =
                FStar_TypeChecker_Rel.try_teq env
                  lc.FStar_Syntax_Syntax.lcomp_res_typ t
                 in
              (uu____4044, false)
            else
              (let uu____4048 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.lcomp_res_typ t
                  in
               (uu____4048, true))
             in
          match gopt with
          | (None ,uu____4054) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.lcomp_res_typ t;
               (e,
                 ((let uu___137_4057 = lc  in
                   {
                     FStar_Syntax_Syntax.lcomp_name =
                       (uu___137_4057.FStar_Syntax_Syntax.lcomp_name);
                     FStar_Syntax_Syntax.lcomp_univs =
                       (uu___137_4057.FStar_Syntax_Syntax.lcomp_univs);
                     FStar_Syntax_Syntax.lcomp_indices =
                       (uu___137_4057.FStar_Syntax_Syntax.lcomp_indices);
                     FStar_Syntax_Syntax.lcomp_res_typ = t;
                     FStar_Syntax_Syntax.lcomp_cflags =
                       (uu___137_4057.FStar_Syntax_Syntax.lcomp_cflags);
                     FStar_Syntax_Syntax.lcomp_as_comp =
                       (uu___137_4057.FStar_Syntax_Syntax.lcomp_as_comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4061 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____4061 with
               | FStar_TypeChecker_Common.Trivial  ->
                   (e,
                     (let uu___138_4065 = lc  in
                      {
                        FStar_Syntax_Syntax.lcomp_name =
                          (uu___138_4065.FStar_Syntax_Syntax.lcomp_name);
                        FStar_Syntax_Syntax.lcomp_univs =
                          (uu___138_4065.FStar_Syntax_Syntax.lcomp_univs);
                        FStar_Syntax_Syntax.lcomp_indices =
                          (uu___138_4065.FStar_Syntax_Syntax.lcomp_indices);
                        FStar_Syntax_Syntax.lcomp_res_typ = t;
                        FStar_Syntax_Syntax.lcomp_cflags =
                          (uu___138_4065.FStar_Syntax_Syntax.lcomp_cflags);
                        FStar_Syntax_Syntax.lcomp_as_comp =
                          (uu___138_4065.FStar_Syntax_Syntax.lcomp_as_comp)
                      }), g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___139_4068 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___139_4068.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___139_4068.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___139_4068.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____4074 =
                     let uu____4075 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____4075
                     then lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f
                           in
                        let uu____4080 =
                          let uu____4081 = FStar_Syntax_Subst.compress f1  in
                          uu____4081.FStar_Syntax_Syntax.n  in
                        match uu____4080 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4086,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4088;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4089;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4090;_},uu____4091)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___140_4115 = lc  in
                              {
                                FStar_Syntax_Syntax.lcomp_name =
                                  (uu___140_4115.FStar_Syntax_Syntax.lcomp_name);
                                FStar_Syntax_Syntax.lcomp_univs =
                                  (uu___140_4115.FStar_Syntax_Syntax.lcomp_univs);
                                FStar_Syntax_Syntax.lcomp_indices =
                                  (uu___140_4115.FStar_Syntax_Syntax.lcomp_indices);
                                FStar_Syntax_Syntax.lcomp_res_typ = t;
                                FStar_Syntax_Syntax.lcomp_cflags =
                                  (uu___140_4115.FStar_Syntax_Syntax.lcomp_cflags);
                                FStar_Syntax_Syntax.lcomp_as_comp =
                                  (uu___140_4115.FStar_Syntax_Syntax.lcomp_as_comp)
                              }  in
                            lc1.FStar_Syntax_Syntax.lcomp_as_comp ()
                        | uu____4116 ->
                            let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                               in
                            ((let uu____4121 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____4121
                              then
                                let uu____4122 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.lcomp_res_typ
                                   in
                                let uu____4123 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____4124 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____4125 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4122 uu____4123 uu____4124 uu____4125
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
                                let uu____4134 =
                                  let uu____4135 =
                                    FStar_TypeChecker_Env.inst_effect_fun_with
                                      nct.FStar_TypeChecker_Env.nct_univs env
                                      md md.FStar_Syntax_Syntax.ret_wp
                                     in
                                  let uu____4136 =
                                    let uu____4137 =
                                      let uu____4143 =
                                        FStar_Syntax_Syntax.as_arg t  in
                                      let uu____4144 =
                                        let uu____4146 =
                                          FStar_Syntax_Syntax.as_arg xexp  in
                                        [uu____4146]  in
                                      uu____4143 :: uu____4144  in
                                    FStar_List.append
                                      nct.FStar_TypeChecker_Env.nct_indices
                                      uu____4137
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app uu____4135
                                    uu____4136
                                   in
                                uu____4134 None xexp.FStar_Syntax_Syntax.pos
                                 in
                              let cret =
                                let uu____4156 =
                                  (mk_comp md)
                                    nct.FStar_TypeChecker_Env.nct_univs
                                    nct.FStar_TypeChecker_Env.nct_indices t
                                    wp [FStar_Syntax_Syntax.RETURN]
                                   in
                                FStar_TypeChecker_Env.lcomp_of_comp env
                                  uu____4156
                                 in
                              let guard =
                                if apply_guard1
                                then
                                  let uu____4162 =
                                    let uu____4163 =
                                      let uu____4164 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____4164]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____4163
                                     in
                                  uu____4162
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____4170 =
                                let uu____4173 =
                                  FStar_All.pipe_left
                                    (fun _0_28  -> Some _0_28)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env
                                       lc.FStar_Syntax_Syntax.lcomp_res_typ t)
                                   in
                                let uu____4184 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____4185 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____4173 uu____4184
                                  e cret uu____4185
                                 in
                              match uu____4170 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___141_4191 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___141_4191.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___141_4191.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.lcomp_res_typ)
                                    }  in
                                  let c1 =
                                    let uu____4193 =
                                      let uu____4194 =
                                        FStar_TypeChecker_Env.normal_comp_typ_as_comp
                                          env nct
                                         in
                                      FStar_TypeChecker_Env.lcomp_of_comp env
                                        uu____4194
                                       in
                                    bind env (Some e) uu____4193
                                      ((Some x1), eq_ret)
                                     in
                                  let c2 =
                                    c1.FStar_Syntax_Syntax.lcomp_as_comp ()
                                     in
                                  ((let uu____4200 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____4200
                                    then
                                      let uu____4201 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____4201
                                    else ());
                                   c2))))
                      in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.lcomp_cflags
                       (FStar_List.collect
                          (fun uu___94_4207  ->
                             match uu___94_4207 with
                             | FStar_Syntax_Syntax.RETURN 
                               |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4209 -> []))
                      in
                   let lc1 =
                     let uu___142_4211 = lc  in
                     {
                       FStar_Syntax_Syntax.lcomp_name =
                         (uu___142_4211.FStar_Syntax_Syntax.lcomp_name);
                       FStar_Syntax_Syntax.lcomp_univs =
                         (uu___142_4211.FStar_Syntax_Syntax.lcomp_univs);
                       FStar_Syntax_Syntax.lcomp_indices =
                         (uu___142_4211.FStar_Syntax_Syntax.lcomp_indices);
                       FStar_Syntax_Syntax.lcomp_res_typ = t;
                       FStar_Syntax_Syntax.lcomp_cflags = flags;
                       FStar_Syntax_Syntax.lcomp_as_comp = strengthen
                     }  in
                   let g2 =
                     let uu___143_4213 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___143_4213.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___143_4213.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___143_4213.FStar_TypeChecker_Env.implicits)
                     }  in
                   (e, lc1, g2))
  
let pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv None res_t  in
        let uu____4233 =
          let uu____4234 =
            let uu____4235 =
              let uu____4236 =
                let uu____4237 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____4237  in
              [uu____4236]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4235  in
          uu____4234 None res_t.FStar_Syntax_Syntax.pos  in
        FStar_Syntax_Util.refine x uu____4233  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____4246 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____4246
      then
        let uu____4250 = FStar_TypeChecker_Env.result_typ env comp  in
        (None, uu____4250)
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
                | (res,uu____4269)::(req,uu____4271)::(ens,uu____4273)::uu____4274
                    ->
                    let uu____4304 =
                      let uu____4306 = norm req  in Some uu____4306  in
                    let uu____4307 =
                      let uu____4308 = mk_post_type res ens  in
                      FStar_All.pipe_left norm uu____4308  in
                    (uu____4304, uu____4307)
                | uu____4310 ->
                    let uu____4316 =
                      let uu____4317 =
                        let uu____4320 =
                          let uu____4321 =
                            FStar_Syntax_Print.comp_to_string comp  in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4321
                           in
                        (uu____4320, (comp.FStar_Syntax_Syntax.pos))  in
                      FStar_Errors.Error uu____4317  in
                    Prims.raise uu____4316)
             else
               (let nct =
                  FStar_TypeChecker_Env.comp_as_normal_comp_typ env comp  in
                let res_t = Prims.fst nct.FStar_TypeChecker_Env.nct_result
                   in
                let wp = Prims.fst nct.FStar_TypeChecker_Env.nct_wp  in
                let uu____4337 =
                  FStar_TypeChecker_Env.lookup_lid env
                    FStar_Syntax_Const.as_requires
                   in
                match uu____4337 with
                | (us_r,uu____4344) ->
                    let uu____4345 =
                      FStar_TypeChecker_Env.lookup_lid env
                        FStar_Syntax_Const.as_ensures
                       in
                    (match uu____4345 with
                     | (us_e,uu____4352) ->
                         let r = res_t.FStar_Syntax_Syntax.pos  in
                         let as_req =
                           let uu____4355 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Syntax_Const.as_requires r)
                               FStar_Syntax_Syntax.Delta_equational None
                              in
                           FStar_Syntax_Syntax.mk_Tm_uinst uu____4355 us_r
                            in
                         let as_ens =
                           let uu____4357 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Syntax_Const.as_ensures r)
                               FStar_Syntax_Syntax.Delta_equational None
                              in
                           FStar_Syntax_Syntax.mk_Tm_uinst uu____4357 us_e
                            in
                         let req =
                           let uu____4361 =
                             let uu____4362 =
                               let uu____4363 =
                                 let uu____4370 =
                                   FStar_Syntax_Syntax.as_arg wp  in
                                 [uu____4370]  in
                               (res_t, (Some FStar_Syntax_Syntax.imp_tag)) ::
                                 uu____4363
                                in
                             FStar_Syntax_Syntax.mk_Tm_app as_req uu____4362
                              in
                           uu____4361
                             (Some
                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                             r
                            in
                         let ens =
                           let uu____4386 =
                             let uu____4387 =
                               let uu____4388 =
                                 let uu____4395 =
                                   FStar_Syntax_Syntax.as_arg wp  in
                                 [uu____4395]  in
                               (res_t, (Some FStar_Syntax_Syntax.imp_tag)) ::
                                 uu____4388
                                in
                             FStar_Syntax_Syntax.mk_Tm_app as_ens uu____4387
                              in
                           uu____4386 None r  in
                         let uu____4408 =
                           let uu____4410 = norm req  in Some uu____4410  in
                         let uu____4411 =
                           let uu____4412 = mk_post_type res_t ens  in
                           norm uu____4412  in
                         (uu____4408, uu____4411))))
  
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
          (let number_of_implicits t1 =
             let uu____4442 = FStar_Syntax_Util.arrow_formals_comp t1  in
             match uu____4442 with
             | (formals,uu____4449) ->
                 let n_implicits =
                   let uu____4457 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4494  ->
                             match uu____4494 with
                             | (uu____4498,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____4457 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____4570 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____4570 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____4584 =
                     let uu____4585 =
                       let uu____4588 =
                         let uu____4589 = FStar_Util.string_of_int n_expected
                            in
                         let uu____4593 = FStar_Syntax_Print.term_to_string e
                            in
                         let uu____4594 =
                           FStar_Util.string_of_int n_available  in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4589 uu____4593 uu____4594
                          in
                       let uu____4598 = FStar_TypeChecker_Env.get_range env
                          in
                       (uu____4588, uu____4598)  in
                     FStar_Errors.Error uu____4585  in
                   Prims.raise uu____4584
                 else Some (n_available - n_expected)
              in
           let decr_inst uu___95_4611 =
             match uu___95_4611 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1"))  in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4631 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____4631 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_29,uu____4693) when
                          _0_29 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____4715,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____4734 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____4734 with
                           | (v1,uu____4755,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____4765 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____4765 with
                                | (args,bs3,subst3,g') ->
                                    let uu____4814 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____4814)))
                      | (uu____4828,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____4852 =
                      let uu____4866 = inst_n_binders t  in
                      aux [] uu____4866 bs1  in
                    (match uu____4852 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____4906) -> (e, torig, guard, [])
                          | (uu____4923,[]) when
                              let uu____4939 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____4939 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard,
                                [])
                          | uu____4941 ->
                              let t1 =
                                match bs2 with
                                | [] ->
                                    FStar_TypeChecker_Env.result_typ env c1
                                | uu____4956 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard, subst1))))
           | uu____4972 -> (e, t, FStar_TypeChecker_Rel.trivial_guard, []))
  
let string_of_univs univs1 =
  let uu____4985 =
    let uu____4987 = FStar_Util.set_elements univs1  in
    FStar_All.pipe_right uu____4987
      (FStar_List.map
         (fun u  ->
            let uu____4997 = FStar_Unionfind.uvar_id u  in
            FStar_All.pipe_right uu____4997 FStar_Util.string_of_int))
     in
  FStar_All.pipe_right uu____4985 (FStar_String.concat ", ") 
let gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5009 = FStar_Util.set_is_empty x  in
      if uu____5009
      then []
      else
        (let s =
           let uu____5014 =
             let uu____5016 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____5016  in
           FStar_All.pipe_right uu____5014 FStar_Util.set_elements  in
         (let uu____5021 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____5021
          then
            let uu____5022 =
              let uu____5023 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____5023  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5022
          else ());
         (let r =
            let uu____5031 = FStar_TypeChecker_Env.get_range env  in
            Some uu____5031  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____5043 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____5043
                     then
                       let uu____5044 =
                         let uu____5045 = FStar_Unionfind.uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5045
                          in
                       let uu____5047 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____5048 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5044 uu____5047 uu____5048
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
      let univnames1 =
        let uu____5066 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____5066 FStar_Util.fifo_set_elements  in
      univnames1
  
let maybe_set_tk ts uu___96_5093 =
  match uu___96_5093 with
  | None  -> ts
  | Some t ->
      let t1 = FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange  in
      let t2 = FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t1  in
      (FStar_ST.write (Prims.snd ts).FStar_Syntax_Syntax.tk
         (Some (t2.FStar_Syntax_Syntax.n));
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
        | ([],uu____5134) -> generalized_univ_names
        | (uu____5138,[]) -> explicit_univ_names
        | uu____5142 ->
            let uu____5147 =
              let uu____5148 =
                let uu____5151 =
                  let uu____5152 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5152
                   in
                (uu____5151, (t.FStar_Syntax_Syntax.pos))  in
              FStar_Errors.Error uu____5148  in
            Prims.raise uu____5147
  
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
      let univnames1 = gather_free_univnames env t  in
      let univs1 = FStar_Syntax_Free.univs t  in
      (let uu____5166 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____5166
       then
         let uu____5167 = string_of_univs univs1  in
         FStar_Util.print1 "univs to gen : %s\n" uu____5167
       else ());
      (let gen1 = gen_univs env univs1  in
       (let uu____5173 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____5173
        then
          let uu____5174 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.print1 "After generalization: %s\n" uu____5174
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0  in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t  in
        let uu____5179 = FStar_ST.read t0.FStar_Syntax_Syntax.tk  in
        maybe_set_tk (univs2, ts) uu____5179))
  
let gen :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list Prims.option
  =
  fun env  ->
    fun ecs  ->
      let uu____5209 =
        let uu____5210 =
          FStar_Util.for_all
            (fun uu____5215  ->
               match uu____5215 with
               | (uu____5220,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs
           in
        FStar_All.pipe_left Prims.op_Negation uu____5210  in
      if uu____5209
      then None
      else
        (let norm c =
           (let uu____5243 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
            if uu____5243
            then
              let uu____5244 = FStar_Syntax_Print.comp_to_string c  in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5244
            else ());
           (let c1 =
              let uu____5247 = FStar_TypeChecker_Env.should_verify env  in
              if uu____5247
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
            (let uu____5250 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____5250
             then
               let uu____5251 = FStar_Syntax_Print.comp_to_string c1  in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5251
             else ());
            c1)
            in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
         let gen_uvars uvs =
           let uu____5285 = FStar_Util.set_difference uvs env_uvars  in
           FStar_All.pipe_right uu____5285 FStar_Util.set_elements  in
         let uu____5329 =
           let uu____5347 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5400  ->
                     match uu____5400 with
                     | (e,c) ->
                         let c1 = norm c  in
                         let t =
                           let uu____5422 =
                             FStar_TypeChecker_Env.result_typ env c1  in
                           FStar_All.pipe_right uu____5422
                             FStar_Syntax_Subst.compress
                            in
                         let univs1 = FStar_Syntax_Free.univs t  in
                         let uvt = FStar_Syntax_Free.uvars t  in
                         let uvs = gen_uvars uvt  in (univs1, (uvs, e, c1))))
              in
           FStar_All.pipe_right uu____5347 FStar_List.unzip  in
         match uu____5329 with
         | (univs1,uvars1) ->
             let univs2 =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs1
                in
             let gen_univs1 = gen_univs env univs2  in
             ((let uu____5552 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____5552
               then
                 FStar_All.pipe_right gen_univs1
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.print1 "Generalizing uvar %s\n"
                           x.FStar_Ident.idText))
               else ());
              (let ecs1 =
                 FStar_All.pipe_right uvars1
                   (FStar_List.map
                      (fun uu____5594  ->
                         match uu____5594 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____5651  ->
                                       match uu____5651 with
                                       | (u,k) ->
                                           let uu____5671 =
                                             FStar_Unionfind.find u  in
                                           (match uu____5671 with
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
                                                uu____5709 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____5717 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k
                                                   in
                                                let uu____5722 =
                                                  FStar_Syntax_Util.arrow_formals_comp
                                                    k1
                                                   in
                                                (match uu____5722 with
                                                 | (bs,cres) ->
                                                     let kres =
                                                       FStar_TypeChecker_Env.result_typ
                                                         env cres
                                                        in
                                                     let a =
                                                       let uu____5741 =
                                                         let uu____5743 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env
                                                            in
                                                         FStar_All.pipe_left
                                                           (fun _0_30  ->
                                                              Some _0_30)
                                                           uu____5743
                                                          in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____5741 kres
                                                        in
                                                     let t =
                                                       let uu____5746 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a
                                                          in
                                                       let uu____5747 =
                                                         let uu____5754 =
                                                           let uu____5760 =
                                                             let uu____5761 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres
                                                                in
                                                             FStar_TypeChecker_Env.lcomp_of_comp
                                                               env uu____5761
                                                              in
                                                           FStar_Util.Inl
                                                             uu____5760
                                                            in
                                                         Some uu____5754  in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____5746
                                                         uu____5747
                                                        in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag)))))))
                                in
                             let uu____5774 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | ([],uu____5792) ->
                                   let c1 =
                                     FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm]
                                       env c
                                      in
                                   let e1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm]
                                       env e
                                      in
                                   (e1, c1)
                               | uu____5804 ->
                                   let uu____5812 = (e, c)  in
                                   (match uu____5812 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm]
                                            env c
                                           in
                                        let e1 =
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
                                          let uu____5822 =
                                            let uu____5823 =
                                              let uu____5826 =
                                                FStar_TypeChecker_Env.result_typ
                                                  env c1
                                                 in
                                              FStar_Syntax_Subst.compress
                                                uu____5826
                                               in
                                            uu____5823.FStar_Syntax_Syntax.n
                                             in
                                          match uu____5822 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____5839 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____5839 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____5847 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1
                                           in
                                        let e' =
                                          let uu____5849 =
                                            let uu____5856 =
                                              let uu____5862 =
                                                FStar_TypeChecker_Env.lcomp_of_comp
                                                  env c1
                                                 in
                                              FStar_Util.Inl uu____5862  in
                                            Some uu____5856  in
                                          FStar_Syntax_Util.abs tvars e1
                                            uu____5849
                                           in
                                        let uu____5871 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____5871))
                                in
                             (match uu____5774 with
                              | (e1,c1) -> (gen_univs1, e1, c1))))
                  in
               Some ecs1)))
  
let generalize :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_name Prims.list
        * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list
  =
  fun env  ->
    fun lecs  ->
      (let uu____5909 = FStar_TypeChecker_Env.debug env FStar_Options.Low  in
       if uu____5909
       then
         let uu____5910 =
           let uu____5911 =
             FStar_List.map
               (fun uu____5916  ->
                  match uu____5916 with
                  | (lb,uu____5921,uu____5922) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs
              in
           FStar_All.pipe_right uu____5911 (FStar_String.concat ", ")  in
         FStar_Util.print1 "Generalizing: %s\n" uu____5910
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____5932  ->
              match uu____5932 with | (l,t,c) -> gather_free_univnames env t)
           lecs
          in
       let generalized_lecs =
         let uu____5947 =
           let uu____5954 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____5970  ->
                     match uu____5970 with | (uu____5976,e,c) -> (e, c)))
              in
           gen env uu____5954  in
         match uu____5947 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6008  ->
                     match uu____6008 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6048  ->
                  fun uu____6049  ->
                    match (uu____6048, uu____6049) with
                    | ((l,uu____6076,uu____6077),(us,e,c)) ->
                        ((let uu____6097 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium
                             in
                          if uu____6097
                          then
                            let uu____6098 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____6099 =
                              FStar_Syntax_Print.lbname_to_string l  in
                            let uu____6100 =
                              let uu____6101 =
                                FStar_TypeChecker_Env.result_typ env c  in
                              FStar_Syntax_Print.term_to_string uu____6101
                               in
                            let uu____6102 =
                              FStar_Syntax_Print.term_to_string e  in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6098 uu____6099 uu____6100 uu____6102
                          else ());
                         (l, us, e, c))) lecs ecs
          in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6119  ->
              match uu____6119 with
              | (l,generalized_univs,t,c) ->
                  let uu____6137 =
                    check_universe_generalization univnames1
                      generalized_univs t
                     in
                  (l, uu____6137, t, c)) univnames_lecs generalized_lecs)
  
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
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq env2 t11 t21
            else
              (let uu____6170 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21  in
               match uu____6170 with
               | None  -> None
               | Some f ->
                   let uu____6174 = FStar_TypeChecker_Rel.apply_guard f e  in
                   FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____6174)
             in
          let is_var e1 =
            let uu____6180 =
              let uu____6181 = FStar_Syntax_Subst.compress e1  in
              uu____6181.FStar_Syntax_Syntax.n  in
            match uu____6180 with
            | FStar_Syntax_Syntax.Tm_name uu____6184 -> true
            | uu____6185 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_name
                      (let uu___144_6207 = x  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___144_6207.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___144_6207.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t2
                       }))) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6208 ->
                let uu___145_6209 = e2  in
                let uu____6210 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n))  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___145_6209.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6210;
                  FStar_Syntax_Syntax.pos =
                    (uu___145_6209.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___145_6209.FStar_Syntax_Syntax.vars)
                }
             in
          let env2 =
            let uu___146_6219 = env1  in
            let uu____6220 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_6219.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_6219.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_6219.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_6219.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_6219.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_6219.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_6219.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_6219.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_6219.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_6219.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_6219.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_6219.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_6219.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___146_6219.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_6219.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6220;
              FStar_TypeChecker_Env.is_iface =
                (uu___146_6219.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_6219.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_6219.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_6219.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___146_6219.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_6219.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_6219.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___146_6219.FStar_TypeChecker_Env.qname_and_index)
            }  in
          let uu____6221 = check env2 t1 t2  in
          match uu____6221 with
          | None  ->
              let uu____6225 =
                let uu____6226 =
                  let uu____6229 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1
                     in
                  let uu____6230 = FStar_TypeChecker_Env.get_range env2  in
                  (uu____6229, uu____6230)  in
                FStar_Errors.Error uu____6226  in
              Prims.raise uu____6225
          | Some g ->
              ((let uu____6235 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____6235
                then
                  let uu____6236 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6236
                else ());
               (let uu____6238 = decorate e t2  in (uu____6238, g)))
  
let check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        let discharge g1 =
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          FStar_Syntax_Util.is_pure_lcomp lc  in
        let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
        let uu____6262 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____6262
        then
          let uu____6265 = discharge g1  in
          let uu____6266 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          (uu____6265, uu____6266)
        else
          (let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
           let steps = [FStar_TypeChecker_Normalize.Beta]  in
           let c1 =
             let uu____6278 =
               let uu____6279 =
                 let uu____6280 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____6280 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____6279
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____6278
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let nct =
             let uu____6282 = FStar_Syntax_Syntax.mk_Comp c1  in
             FStar_TypeChecker_Env.comp_as_normal_comp_typ env uu____6282  in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               nct.FStar_TypeChecker_Env.nct_name
              in
           let vc =
             let uu____6287 = FStar_TypeChecker_Env.get_range env  in
             let uu____6288 =
               let uu____6289 =
                 FStar_TypeChecker_Env.inst_effect_fun_with
                   nct.FStar_TypeChecker_Env.nct_univs env md
                   md.FStar_Syntax_Syntax.trivial
                  in
               FStar_Syntax_Syntax.mk_Tm_app uu____6289
                 (FStar_List.append nct.FStar_TypeChecker_Env.nct_indices
                    [nct.FStar_TypeChecker_Env.nct_result;
                    nct.FStar_TypeChecker_Env.nct_wp])
                in
             uu____6288
               (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
               uu____6287
              in
           (let uu____6299 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____6299
            then
              let uu____6300 = FStar_Syntax_Print.term_to_string vc  in
              FStar_Util.print1 "top-level VC: %s\n" uu____6300
            else ());
           (let g2 =
              let uu____6303 =
                FStar_All.pipe_left
                  FStar_TypeChecker_Rel.guard_of_guard_formula
                  (FStar_TypeChecker_Common.NonTrivial vc)
                 in
              FStar_TypeChecker_Rel.conj_guard g1 uu____6303  in
            let uu____6304 = discharge g2  in
            let uu____6305 = FStar_Syntax_Syntax.mk_Comp c1  in
            (uu____6304, uu____6305)))
  
let short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___97_6329 =
        match uu___97_6329 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6335)::[] -> f fst1
        | uu____6348 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____6353 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____6353
          (fun _0_32  -> FStar_TypeChecker_Common.NonTrivial _0_32)
         in
      let op_or_e e =
        let uu____6362 =
          let uu____6365 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____6365  in
        FStar_All.pipe_right uu____6362
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34)
         in
      let op_or_t t =
        let uu____6376 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____6376
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36)
         in
      let short_op_ite uu___98_6390 =
        match uu___98_6390 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6396)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6411)::[] ->
            let uu____6432 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____6432
              (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37)
        | uu____6437 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____6444 =
          let uu____6449 = short_bin_op op_and_e  in
          (FStar_Syntax_Const.op_And, uu____6449)  in
        let uu____6454 =
          let uu____6460 =
            let uu____6465 = short_bin_op op_or_e  in
            (FStar_Syntax_Const.op_Or, uu____6465)  in
          let uu____6470 =
            let uu____6476 =
              let uu____6481 = short_bin_op op_and_t  in
              (FStar_Syntax_Const.and_lid, uu____6481)  in
            let uu____6486 =
              let uu____6492 =
                let uu____6497 = short_bin_op op_or_t  in
                (FStar_Syntax_Const.or_lid, uu____6497)  in
              let uu____6502 =
                let uu____6508 =
                  let uu____6513 = short_bin_op op_imp_t  in
                  (FStar_Syntax_Const.imp_lid, uu____6513)  in
                [uu____6508; (FStar_Syntax_Const.ite_lid, short_op_ite)]  in
              uu____6492 :: uu____6502  in
            uu____6476 :: uu____6486  in
          uu____6460 :: uu____6470  in
        uu____6444 :: uu____6454  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____6554 =
            FStar_Util.find_map table
              (fun uu____6560  ->
                 match uu____6560 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____6573 = mk1 seen_args  in Some uu____6573
                     else None)
             in
          (match uu____6554 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____6576 -> FStar_TypeChecker_Common.Trivial
  
let short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6580 =
      let uu____6581 = FStar_Syntax_Util.un_uinst l  in
      uu____6581.FStar_Syntax_Syntax.n  in
    match uu____6580 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____6585 -> false
  
let maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____6603)::uu____6604 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____6610 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____6614,Some (FStar_Syntax_Syntax.Implicit uu____6615))::uu____6616
          -> bs
      | uu____6625 ->
          let uu____6626 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____6626 with
           | None  -> bs
           | Some t ->
               let uu____6629 =
                 let uu____6630 = FStar_Syntax_Subst.compress t  in
                 uu____6630.FStar_Syntax_Syntax.n  in
               (match uu____6629 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____6634) ->
                    let uu____6645 =
                      FStar_Util.prefix_until
                        (fun uu___99_6664  ->
                           match uu___99_6664 with
                           | (uu____6668,Some (FStar_Syntax_Syntax.Implicit
                              uu____6669)) -> false
                           | uu____6671 -> true) bs'
                       in
                    (match uu____6645 with
                     | None  -> bs
                     | Some ([],uu____6689,uu____6690) -> bs
                     | Some (imps,uu____6727,uu____6728) ->
                         let uu____6765 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____6773  ->
                                   match uu____6773 with
                                   | (x,uu____6778) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____6765
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____6801  ->
                                     match uu____6801 with
                                     | (x,i) ->
                                         let uu____6812 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____6812, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____6818 -> bs))
  
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
              (let uu____6837 = FStar_ST.read e.FStar_Syntax_Syntax.tk  in
               (FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_meta
                     (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)))))
                 uu____6837 e.FStar_Syntax_Syntax.pos)
  
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
          let uu____6863 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)
             in
          if uu____6863
          then e
          else
            (let uu____6865 = FStar_ST.read e.FStar_Syntax_Syntax.tk  in
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))))
               uu____6865 e.FStar_Syntax_Syntax.pos)
  
let effect_repr_aux only_reifiable env c =
  let uu____6902 =
    let uu____6904 =
      FStar_TypeChecker_Env.norm_eff_name env
        (FStar_Syntax_Util.comp_effect_name c)
       in
    FStar_TypeChecker_Env.effect_decl_opt env uu____6904  in
  match uu____6902 with
  | None  -> None
  | Some ed ->
      let uu____6911 =
        only_reifiable &&
          (let uu____6912 =
             FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
              in
           Prims.op_Negation uu____6912)
         in
      if uu____6911
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____6925 ->
             let nct = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c
                in
             let repr =
               FStar_TypeChecker_Env.inst_effect_fun_with
                 nct.FStar_TypeChecker_Env.nct_univs env ed
                 ([], (ed.FStar_Syntax_Syntax.repr))
                in
             let uu____6929 =
               let uu____6932 = FStar_TypeChecker_Env.get_range env  in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app
                    (repr,
                      (FStar_List.append
                         nct.FStar_TypeChecker_Env.nct_indices
                         [nct.FStar_TypeChecker_Env.nct_result;
                         nct.FStar_TypeChecker_Env.nct_wp]))) None uu____6932
                in
             Some uu____6929)
  
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
      let uu____6962 =
        let uu____6966 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
        effect_repr_aux true env uu____6966  in
      match uu____6962 with
      | None  ->
          let uu____6971 =
            let uu____6972 =
              let uu____6975 =
                FStar_Util.format1 "Effect %s cannot be reified"
                  (lc.FStar_Syntax_Syntax.lcomp_name).FStar_Ident.str
                 in
              let uu____6976 = FStar_TypeChecker_Env.get_range env  in
              (uu____6975, uu____6976)  in
            FStar_Errors.Error uu____6972  in
          Prims.raise uu____6971
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
        (let uu____6999 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____6999
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7001 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7001))
         else ());
        (let fv =
           let uu____7004 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7004 None  in
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
         let uu____7012 =
           (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)) None
             FStar_Range.dummyRange
            in
         (sig_ctx, uu____7012))
  
let check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___100_7034 =
        match uu___100_7034 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7035 -> false  in
      let reducibility uu___101_7039 =
        match uu___101_7039 with
        | FStar_Syntax_Syntax.Abstract 
          |FStar_Syntax_Syntax.Irreducible 
           |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
            |FStar_Syntax_Syntax.Visible_default 
             |FStar_Syntax_Syntax.Inline_for_extraction 
            -> true
        | uu____7040 -> false  in
      let assumption uu___102_7044 =
        match uu___102_7044 with
        | FStar_Syntax_Syntax.Assumption |FStar_Syntax_Syntax.New  -> true
        | uu____7045 -> false  in
      let reification uu___103_7049 =
        match uu___103_7049 with
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            true
        | uu____7051 -> false  in
      let inferred uu___104_7055 =
        match uu___104_7055 with
        | FStar_Syntax_Syntax.Discriminator _
          |FStar_Syntax_Syntax.Projector _
           |FStar_Syntax_Syntax.RecordType _
            |FStar_Syntax_Syntax.RecordConstructor _
             |FStar_Syntax_Syntax.ExceptionConstructor 
              |FStar_Syntax_Syntax.HasMaskedEffect 
               |FStar_Syntax_Syntax.Effect 
            -> true
        | uu____7060 -> false  in
      let has_eq uu___105_7064 =
        match uu___105_7064 with
        | FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7065 -> false  in
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
        | uu____7090 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____7093 =
        let uu____7094 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___106_7096  ->
                  match uu___106_7096 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7097 -> false))
           in
        FStar_All.pipe_right uu____7094 Prims.op_Negation  in
      if uu____7093
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____7107 =
            let uu____7108 =
              let uu____7111 =
                let uu____7112 = FStar_Syntax_Print.quals_to_string quals  in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7112 msg
                 in
              (uu____7111, r)  in
            FStar_Errors.Error uu____7108  in
          Prims.raise uu____7107  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____7120 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____7128 =
            let uu____7129 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____7129  in
          if uu____7128 then err "ill-formed combination" else ());
         (match se with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7133),uu____7134,uu____7135,uu____7136,uu____7137)
              ->
              ((let uu____7150 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____7150
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____7153 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____7153
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7157 ->
              let uu____7165 =
                let uu____7166 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____7166  in
              if uu____7165 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7170 ->
              let uu____7177 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____7177 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7180 ->
              let uu____7186 =
                let uu____7187 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____7187  in
              if uu____7186 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7191 ->
              let uu____7194 =
                let uu____7195 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____7195  in
              if uu____7194 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7199 ->
              let uu____7202 =
                let uu____7203 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____7203  in
              if uu____7202 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7207 ->
              let uu____7217 =
                let uu____7218 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____7218  in
              if uu____7217 then err'1 () else ()
          | uu____7222 -> ()))
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
                          let uu____7279 =
                            let uu____7282 =
                              let uu____7283 =
                                let uu____7288 =
                                  let uu____7289 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7289  in
                                (uu____7288, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____7283  in
                            FStar_Syntax_Syntax.mk uu____7282  in
                          uu____7279 None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7315  ->
                                  match uu____7315 with
                                  | (x,imp) ->
                                      let uu____7322 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____7322, imp)))
                           in
                        (FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p
                         in
                      let unrefined_arg_binder =
                        let uu____7328 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____7328  in
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
                             let uu____7337 =
                               let uu____7338 =
                                 let uu____7339 =
                                   let uu____7340 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____7341 =
                                     let uu____7342 =
                                       let uu____7343 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7343
                                        in
                                     [uu____7342]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7340
                                     uu____7341
                                    in
                                 uu____7339 None p  in
                               FStar_Syntax_Util.b2t uu____7338  in
                             FStar_Syntax_Util.refine x uu____7337  in
                           let uu____7348 =
                             let uu___147_7349 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___147_7349.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___147_7349.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____7348)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____7359 =
                          FStar_List.map
                            (fun uu____7369  ->
                               match uu____7369 with
                               | (x,uu____7376) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps
                           in
                        FStar_List.append uu____7359 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7400  ->
                                match uu____7400 with
                                | (x,uu____7407) ->
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
                             (let uu____7416 =
                                FStar_TypeChecker_Env.current_module env  in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7416)
                               ||
                               (let uu____7417 =
                                  let uu____7418 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____7418.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____7417)
                              in
                           let quals =
                             let uu____7421 =
                               let uu____7423 =
                                 let uu____7425 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit)
                                    in
                                 if uu____7425
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else []  in
                               let uu____7428 =
                                 FStar_List.filter
                                   (fun uu___107_7430  ->
                                      match uu___107_7430 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7431 -> false) iquals
                                  in
                               FStar_List.append uu____7423 uu____7428  in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7421
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____7444 =
                                 let uu____7445 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7445  in
                               FStar_Syntax_Syntax.mk_Total uu____7444  in
                             let uu____7446 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7446
                              in
                           let decl =
                             FStar_Syntax_Syntax.Sig_declare_typ
                               (discriminator_name, uvs, t, quals,
                                 (FStar_Ident.range_of_lid discriminator_name))
                              in
                           (let uu____7450 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____7450
                            then
                              let uu____7451 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7451
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
                                             fun uu____7479  ->
                                               match uu____7479 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7495 =
                                                       let uu____7498 =
                                                         let uu____7499 =
                                                           let uu____7504 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____7504,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7499
                                                          in
                                                       pos uu____7498  in
                                                     (uu____7495, b)
                                                   else
                                                     (let uu____7508 =
                                                        let uu____7511 =
                                                          let uu____7512 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7512
                                                           in
                                                        pos uu____7511  in
                                                      (uu____7508, b))))
                                      in
                                   let pat_true =
                                     let uu____7524 =
                                       let uu____7527 =
                                         let uu____7528 =
                                           let uu____7536 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq)
                                              in
                                           (uu____7536, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7528
                                          in
                                       pos uu____7527  in
                                     (uu____7524, None,
                                       FStar_Syntax_Const.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____7558 =
                                       let uu____7561 =
                                         let uu____7562 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7562
                                          in
                                       pos uu____7561  in
                                     (uu____7558, None,
                                       FStar_Syntax_Const.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (Prims.fst unrefined_arg_binder)
                                      in
                                   let uu____7571 =
                                     let uu____7574 =
                                       let uu____7575 =
                                         let uu____7591 =
                                           let uu____7593 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____7594 =
                                             let uu____7596 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____7596]  in
                                           uu____7593 :: uu____7594  in
                                         (arg_exp, uu____7591)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7575
                                        in
                                     FStar_Syntax_Syntax.mk uu____7574  in
                                   uu____7571 None p)
                                 in
                              let dd =
                                let uu____7607 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____7607
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
                                let uu____7619 =
                                  let uu____7622 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None
                                     in
                                  FStar_Util.Inr uu____7622  in
                                let uu____7623 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7619;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7623
                                }  in
                              let impl =
                                let uu____7627 =
                                  let uu____7636 =
                                    let uu____7638 =
                                      let uu____7639 =
                                        FStar_All.pipe_right
                                          lb.FStar_Syntax_Syntax.lbname
                                          FStar_Util.right
                                         in
                                      FStar_All.pipe_right uu____7639
                                        (fun fv  ->
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                       in
                                    [uu____7638]  in
                                  ((false, [lb]), p, uu____7636, quals, [])
                                   in
                                FStar_Syntax_Syntax.Sig_let uu____7627  in
                              (let uu____7655 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____7655
                               then
                                 let uu____7656 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7656
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
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7676  ->
                                  match uu____7676 with
                                  | (a,uu____7680) ->
                                      let uu____7681 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____7681 with
                                       | (field_name,uu____7685) ->
                                           let field_proj_tm =
                                             let uu____7687 =
                                               let uu____7688 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7688
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7687 inst_univs
                                              in
                                           let proj =
                                             (FStar_Syntax_Syntax.mk_Tm_app
                                                field_proj_tm [arg]) None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____7704 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7713  ->
                                    match uu____7713 with
                                    | (x,uu____7718) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____7720 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____7720 with
                                         | (field_name,uu____7725) ->
                                             let t =
                                               let uu____7727 =
                                                 let uu____7728 =
                                                   let uu____7729 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7729
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7728
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7727
                                                in
                                             let only_decl =
                                               ((let uu____7731 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env
                                                    in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____7731)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____7732 =
                                                    let uu____7733 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____7733.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7732)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7743 =
                                                   FStar_List.filter
                                                     (fun uu___108_7745  ->
                                                        match uu___108_7745
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7746 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7743
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___109_7754  ->
                                                         match uu___109_7754
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                           
                                                           |FStar_Syntax_Syntax.Private
                                                            -> true
                                                         | uu____7755 ->
                                                             false))
                                                  in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1)
                                                in
                                             let decl =
                                               FStar_Syntax_Syntax.Sig_declare_typ
                                                 (field_name, uvs, t, quals1,
                                                   (FStar_Ident.range_of_lid
                                                      field_name))
                                                in
                                             ((let uu____7759 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____7759
                                               then
                                                 let uu____7760 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7760
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
                                                           fun uu____7787  ->
                                                             match uu____7787
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp
                                                                    in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____7803
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____7803,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____7815
                                                                    =
                                                                    let uu____7818
                                                                    =
                                                                    let uu____7819
                                                                    =
                                                                    let uu____7824
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____7824,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7819
                                                                     in
                                                                    pos
                                                                    uu____7818
                                                                     in
                                                                    (uu____7815,
                                                                    b))
                                                                   else
                                                                    (let uu____7828
                                                                    =
                                                                    let uu____7831
                                                                    =
                                                                    let uu____7832
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7832
                                                                     in
                                                                    pos
                                                                    uu____7831
                                                                     in
                                                                    (uu____7828,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____7844 =
                                                     let uu____7847 =
                                                       let uu____7848 =
                                                         let uu____7856 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq)
                                                            in
                                                         (uu____7856,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____7848
                                                        in
                                                     pos uu____7847  in
                                                   let uu____7862 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____7844, None,
                                                     uu____7862)
                                                    in
                                                 let body =
                                                   let uu____7873 =
                                                     let uu____7876 =
                                                       let uu____7877 =
                                                         let uu____7893 =
                                                           let uu____7895 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____7895]  in
                                                         (arg_exp,
                                                           uu____7893)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____7877
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____7876
                                                      in
                                                   uu____7873 None p1  in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None
                                                    in
                                                 let dd =
                                                   let uu____7912 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____7912
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
                                                   let uu____7918 =
                                                     let uu____7921 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____7921
                                                      in
                                                   let uu____7922 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____7918;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____7922
                                                   }  in
                                                 let impl =
                                                   let uu____7926 =
                                                     let uu____7935 =
                                                       let uu____7937 =
                                                         let uu____7938 =
                                                           FStar_All.pipe_right
                                                             lb.FStar_Syntax_Syntax.lbname
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____7938
                                                           (fun fv  ->
                                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                          in
                                                       [uu____7937]  in
                                                     ((false, [lb]), p1,
                                                       uu____7935, quals1,
                                                       [])
                                                      in
                                                   FStar_Syntax_Syntax.Sig_let
                                                     uu____7926
                                                    in
                                                 (let uu____7954 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____7954
                                                  then
                                                    let uu____7955 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____7955
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____7704 FStar_List.flatten
                         in
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
              (constr_lid,uvs,t,typ_lid,n_typars,quals,uu____7986,r) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____7992 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____7992 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____8005 = FStar_Syntax_Util.arrow_formals_comp t1
                      in
                   (match uu____8005 with
                    | (formals,uu____8013) ->
                        let uu____8020 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8033 =
                                   let uu____8034 =
                                     let uu____8035 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____8035  in
                                   FStar_Ident.lid_equals typ_lid uu____8034
                                    in
                                 if uu____8033
                                 then
                                   match se1 with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8045,uvs',tps,typ0,uu____8049,constrs,uu____8051,uu____8052)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8066 -> failwith "Impossible"
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
                        (match uu____8020 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____8108 =
                               FStar_Syntax_Util.arrow_formals_comp typ01  in
                             (match uu____8108 with
                              | (indices,uu____8116) ->
                                  let refine_domain =
                                    let uu____8124 =
                                      FStar_All.pipe_right quals
                                        (FStar_Util.for_some
                                           (fun uu___110_8126  ->
                                              match uu___110_8126 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8127 -> true
                                              | uu____8132 -> false))
                                       in
                                    if uu____8124
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___111_8139 =
                                      match uu___111_8139 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8141,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8148 -> None  in
                                    let uu____8149 =
                                      FStar_Util.find_map quals
                                        filter_records
                                       in
                                    match uu____8149 with
                                    | None  -> FStar_Syntax_Syntax.Data_ctor
                                    | Some q -> q  in
                                  let iquals1 =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals  in
                                  let fields =
                                    let uu____8157 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____8157 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8188  ->
                                               fun uu____8189  ->
                                                 match (uu____8188,
                                                         uu____8189)
                                                 with
                                                 | ((x,uu____8199),(x',uu____8201))
                                                     ->
                                                     let uu____8206 =
                                                       let uu____8211 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____8211)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8206) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8212 -> []
  
let destruct_comp_term :
  FStar_Syntax_Syntax.term ->
    (FStar_Ident.lid * FStar_Syntax_Syntax.universes)
  =
  fun m  ->
    let uu____8218 =
      let uu____8219 = FStar_Syntax_Subst.compress m  in
      uu____8219.FStar_Syntax_Syntax.n  in
    match uu____8218 with
    | FStar_Syntax_Syntax.Tm_uinst
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
           FStar_Syntax_Syntax.tk = uu____8225;
           FStar_Syntax_Syntax.pos = uu____8226;
           FStar_Syntax_Syntax.vars = uu____8227;_},univs1)
        ->
        let uu____8233 = FStar_Syntax_Syntax.lid_of_fv fv  in
        (uu____8233, univs1)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8235 = FStar_Syntax_Syntax.lid_of_fv fv  in
        (uu____8235, [])
    | uu____8237 -> failwith "Impossible"
  
let mlift_of_sub_eff :
  FStar_Syntax_Syntax.sub_eff ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.normal_comp_typ ->
        FStar_TypeChecker_Env.normal_comp_typ
  =
  fun sub1  ->
    let mlift env nct =
      let fail uu____8255 =
        let uu____8256 =
          FStar_Util.format2
            "Invalid application of mlift, effect names differ : %s vs %s"
            (FStar_Ident.text_of_lid nct.FStar_TypeChecker_Env.nct_name)
            (FStar_Ident.text_of_lid
               (sub1.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name)
           in
        FStar_All.pipe_left failwith uu____8256  in
      let sigma =
        let skeleton =
          let uu____8264 =
            let uu____8267 =
              let uu____8270 =
                let uu____8271 =
                  let uu____8279 =
                    FStar_Syntax_Syntax.mk_Total
                      FStar_TypeChecker_Common.t_unit
                     in
                  ((sub1.FStar_Syntax_Syntax.sub_eff_binders), uu____8279)
                   in
                FStar_Syntax_Syntax.Tm_arrow uu____8271  in
              FStar_Syntax_Syntax.mk uu____8270  in
            uu____8267 None FStar_Range.dummyRange  in
          ((sub1.FStar_Syntax_Syntax.sub_eff_univs), uu____8264)  in
        let uu____8290 = FStar_TypeChecker_Env.inst_tscheme skeleton  in
        match uu____8290 with
        | (univ_meta_vars,skel) ->
            let uu____8296 =
              FStar_List.fold_right
                (fun univ  ->
                   fun uu____8304  ->
                     match uu____8304 with
                     | (out,i) ->
                         (((FStar_Syntax_Syntax.UN (i, univ)) :: out),
                           (i + (Prims.parse_int "1")))) univ_meta_vars
                ([],
                  (FStar_List.length sub1.FStar_Syntax_Syntax.sub_eff_binders))
               in
            (match uu____8296 with
             | (univ_meta_vars_subst,uu____8323) ->
                 let uu____8326 =
                   maybe_instantiate env FStar_Syntax_Syntax.tun skel  in
                 (match uu____8326 with
                  | (_term,_typ,_guard,index_meta_var_subst) ->
                      FStar_List.append univ_meta_vars_subst
                        index_meta_var_subst))
         in
      (let dummy_wp = FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun  in
       let formal_source =
         let ct =
           let uu___148_8340 = sub1.FStar_Syntax_Syntax.sub_eff_source  in
           {
             FStar_Syntax_Syntax.comp_typ_name =
               (uu___148_8340.FStar_Syntax_Syntax.comp_typ_name);
             FStar_Syntax_Syntax.comp_univs =
               (uu___148_8340.FStar_Syntax_Syntax.comp_univs);
             FStar_Syntax_Syntax.effect_args =
               (FStar_List.append
                  (sub1.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.effect_args
                  [dummy_wp]);
             FStar_Syntax_Syntax.flags =
               (uu___148_8340.FStar_Syntax_Syntax.flags)
           }  in
         let uu____8345 = FStar_Syntax_Syntax.mk_Comp ct  in
         FStar_Syntax_Subst.subst_comp sigma uu____8345  in
       let actual_source =
         let ct =
           {
             FStar_Syntax_Syntax.comp_typ_name =
               (nct.FStar_TypeChecker_Env.nct_name);
             FStar_Syntax_Syntax.comp_univs =
               (nct.FStar_TypeChecker_Env.nct_univs);
             FStar_Syntax_Syntax.effect_args =
               (FStar_List.append nct.FStar_TypeChecker_Env.nct_indices
                  [nct.FStar_TypeChecker_Env.nct_result; dummy_wp]);
             FStar_Syntax_Syntax.flags =
               (nct.FStar_TypeChecker_Env.nct_flags)
           }  in
         FStar_Syntax_Syntax.mk_Comp ct  in
       let uu____8352 =
         FStar_TypeChecker_Rel.sub_comp
           (let uu___149_8354 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___149_8354.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___149_8354.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___149_8354.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___149_8354.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___149_8354.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___149_8354.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___149_8354.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___149_8354.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___149_8354.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___149_8354.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___149_8354.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___149_8354.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___149_8354.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___149_8354.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___149_8354.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = true;
              FStar_TypeChecker_Env.is_iface =
                (uu___149_8354.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___149_8354.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___149_8354.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___149_8354.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___149_8354.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___149_8354.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___149_8354.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___149_8354.FStar_TypeChecker_Env.qname_and_index)
            }) formal_source actual_source
          in
       match uu____8352 with
       | None  -> fail ()
       | Some g -> FStar_TypeChecker_Rel.force_trivial_guard env g);
      (let target_nct =
         let target_wp =
           let uu____8360 =
             let uu____8361 =
               let uu____8362 =
                 FStar_Util.must sub1.FStar_Syntax_Syntax.sub_eff_lift_wp  in
               FStar_Syntax_Subst.subst sigma uu____8362  in
             FStar_Syntax_Syntax.mk_Tm_app uu____8361
               [nct.FStar_TypeChecker_Env.nct_wp]
              in
           uu____8360 None FStar_Range.dummyRange  in
         let target_comp_no_wp =
           let uu____8368 =
             let uu____8369 =
               FStar_Syntax_Syntax.mk_Comp
                 sub1.FStar_Syntax_Syntax.sub_eff_target
                in
             FStar_Syntax_Subst.subst_comp sigma uu____8369  in
           FStar_All.pipe_right uu____8368 FStar_Syntax_Util.comp_to_comp_typ
            in
         let target_comp_typ =
           let uu___150_8371 = target_comp_no_wp  in
           let uu____8372 =
             let uu____8378 =
               let uu____8384 = FStar_Syntax_Syntax.as_arg target_wp  in
               [uu____8384]  in
             FStar_List.append
               target_comp_no_wp.FStar_Syntax_Syntax.effect_args uu____8378
              in
           {
             FStar_Syntax_Syntax.comp_typ_name =
               (uu___150_8371.FStar_Syntax_Syntax.comp_typ_name);
             FStar_Syntax_Syntax.comp_univs =
               (uu___150_8371.FStar_Syntax_Syntax.comp_univs);
             FStar_Syntax_Syntax.effect_args = uu____8372;
             FStar_Syntax_Syntax.flags =
               (uu___150_8371.FStar_Syntax_Syntax.flags)
           }  in
         let uu____8389 = FStar_Syntax_Syntax.mk_Comp target_comp_typ  in
         FStar_TypeChecker_Env.comp_as_normal_comp_typ env uu____8389  in
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
            (fun env1  ->
               fun nct  ->
                 let uu____8405 = e1.FStar_TypeChecker_Env.mlift env1 nct  in
                 e2.FStar_TypeChecker_Env.mlift env1 uu____8405)
        }  in
      let edge =
        let uu____8407 = mlift_of_sub_eff sub_eff  in
        {
          FStar_TypeChecker_Env.msource =
            ((sub_eff.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name);
          FStar_TypeChecker_Env.mtarget =
            ((sub_eff.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.comp_typ_name);
          FStar_TypeChecker_Env.mlift = uu____8407
        }  in
      let id_edge l =
        {
          FStar_TypeChecker_Env.msource = l;
          FStar_TypeChecker_Env.mtarget = l;
          FStar_TypeChecker_Env.mlift = (fun uu____8418  -> fun nct  -> nct)
        }  in
      let print_mlift l =
        let arg =
          let uu____8435 =
            FStar_Ident.lid_of_path ["ARG"] FStar_Range.dummyRange  in
          FStar_Syntax_Syntax.lid_as_fv uu____8435
            FStar_Syntax_Syntax.Delta_constant None
           in
        let wp =
          let uu____8437 =
            FStar_Ident.lid_of_path ["WP"] FStar_Range.dummyRange  in
          FStar_Syntax_Syntax.lid_as_fv uu____8437
            FStar_Syntax_Syntax.Delta_constant None
           in
        let uu____8438 = l arg wp  in
        FStar_Syntax_Print.term_to_string uu____8438  in
      let order = edge ::
        ((env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.order)  in
      let ms =
        FStar_All.pipe_right
          (env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.decls
          (FStar_List.map (fun e  -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order1 uu____8456 =
        match uu____8456 with
        | (i,j) ->
            if FStar_Ident.lid_equals i j
            then FStar_All.pipe_right (id_edge i) (fun _0_38  -> Some _0_38)
            else
              FStar_All.pipe_right order1
                (FStar_Util.find_opt
                   (fun e  ->
                      (FStar_Ident.lid_equals e.FStar_TypeChecker_Env.msource
                         i)
                        &&
                        (FStar_Ident.lid_equals
                           e.FStar_TypeChecker_Env.mtarget j)))
         in
      let order1 =
        FStar_All.pipe_right ms
          (FStar_List.fold_left
             (fun order1  ->
                fun k  ->
                  let uu____8477 =
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
                                        (let uu____8489 =
                                           let uu____8494 =
                                             find_edge order1 (i, k)  in
                                           let uu____8496 =
                                             find_edge order1 (k, j)  in
                                           (uu____8494, uu____8496)  in
                                         match uu____8489 with
                                         | (Some e1,Some e2) ->
                                             let uu____8505 =
                                               compose_edges e1 e2  in
                                             [uu____8505]
                                         | uu____8506 -> [])))))
                     in
                  FStar_List.append order1 uu____8477) order)
         in
      let order2 =
        FStar_Util.remove_dups
          (fun e1  ->
             fun e2  ->
               (FStar_Ident.lid_equals e1.FStar_TypeChecker_Env.msource
                  e2.FStar_TypeChecker_Env.msource)
                 &&
                 (FStar_Ident.lid_equals e1.FStar_TypeChecker_Env.mtarget
                    e2.FStar_TypeChecker_Env.mtarget)) order1
         in
      FStar_All.pipe_right order2
        (FStar_List.iter
           (fun edge1  ->
              let uu____8518 =
                (FStar_Ident.lid_equals edge1.FStar_TypeChecker_Env.msource
                   FStar_Syntax_Const.effect_DIV_lid)
                  &&
                  (let uu____8519 =
                     FStar_TypeChecker_Env.lookup_effect_quals env
                       edge1.FStar_TypeChecker_Env.mtarget
                      in
                   FStar_All.pipe_right uu____8519
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____8518
              then
                let uu____8522 =
                  let uu____8523 =
                    let uu____8526 =
                      FStar_Util.format1
                        "Divergent computations cannot be included in an effect %s marked 'total'"
                        (edge1.FStar_TypeChecker_Env.mtarget).FStar_Ident.str
                       in
                    let uu____8527 = FStar_TypeChecker_Env.get_range env  in
                    (uu____8526, uu____8527)  in
                  FStar_Errors.Error uu____8523  in
                Prims.raise uu____8522
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
                                     let uu____8622 =
                                       let uu____8627 =
                                         find_edge order2 (i, k)  in
                                       let uu____8629 =
                                         find_edge order2 (j, k)  in
                                       (uu____8627, uu____8629)  in
                                     match uu____8622 with
                                     | (Some ik,Some jk) ->
                                         (match bopt with
                                          | None  -> Some (k, ik, jk)
                                          | Some (ub,uu____8652,uu____8653)
                                              ->
                                              let uu____8657 =
                                                (let uu____8658 =
                                                   find_edge order2 (k, ub)
                                                    in
                                                 FStar_Util.is_some
                                                   uu____8658)
                                                  &&
                                                  (let uu____8660 =
                                                     let uu____8661 =
                                                       find_edge order2
                                                         (ub, k)
                                                        in
                                                     FStar_Util.is_some
                                                       uu____8661
                                                      in
                                                   Prims.op_Negation
                                                     uu____8660)
                                                 in
                                              if uu____8657
                                              then Some (k, ik, jk)
                                              else bopt)
                                     | uu____8671 -> bopt) None)
                            in
                         match join_opt with
                         | None  -> []
                         | Some (k,e1,e2) ->
                             [(i, j, k, (e1.FStar_TypeChecker_Env.mlift),
                                (e2.FStar_TypeChecker_Env.mlift))]))))
          in
       let effects =
         let uu___151_8750 = env.FStar_TypeChecker_Env.effects  in
         {
           FStar_TypeChecker_Env.decls =
             (uu___151_8750.FStar_TypeChecker_Env.decls);
           FStar_TypeChecker_Env.order = order2;
           FStar_TypeChecker_Env.joins = joins
         }  in
       let uu___152_8751 = env  in
       {
         FStar_TypeChecker_Env.solver =
           (uu___152_8751.FStar_TypeChecker_Env.solver);
         FStar_TypeChecker_Env.range =
           (uu___152_8751.FStar_TypeChecker_Env.range);
         FStar_TypeChecker_Env.curmodule =
           (uu___152_8751.FStar_TypeChecker_Env.curmodule);
         FStar_TypeChecker_Env.gamma =
           (uu___152_8751.FStar_TypeChecker_Env.gamma);
         FStar_TypeChecker_Env.gamma_cache =
           (uu___152_8751.FStar_TypeChecker_Env.gamma_cache);
         FStar_TypeChecker_Env.modules =
           (uu___152_8751.FStar_TypeChecker_Env.modules);
         FStar_TypeChecker_Env.expected_typ =
           (uu___152_8751.FStar_TypeChecker_Env.expected_typ);
         FStar_TypeChecker_Env.sigtab =
           (uu___152_8751.FStar_TypeChecker_Env.sigtab);
         FStar_TypeChecker_Env.is_pattern =
           (uu___152_8751.FStar_TypeChecker_Env.is_pattern);
         FStar_TypeChecker_Env.instantiate_imp =
           (uu___152_8751.FStar_TypeChecker_Env.instantiate_imp);
         FStar_TypeChecker_Env.effects = effects;
         FStar_TypeChecker_Env.generalize =
           (uu___152_8751.FStar_TypeChecker_Env.generalize);
         FStar_TypeChecker_Env.letrecs =
           (uu___152_8751.FStar_TypeChecker_Env.letrecs);
         FStar_TypeChecker_Env.top_level =
           (uu___152_8751.FStar_TypeChecker_Env.top_level);
         FStar_TypeChecker_Env.check_uvars =
           (uu___152_8751.FStar_TypeChecker_Env.check_uvars);
         FStar_TypeChecker_Env.use_eq =
           (uu___152_8751.FStar_TypeChecker_Env.use_eq);
         FStar_TypeChecker_Env.is_iface =
           (uu___152_8751.FStar_TypeChecker_Env.is_iface);
         FStar_TypeChecker_Env.admit =
           (uu___152_8751.FStar_TypeChecker_Env.admit);
         FStar_TypeChecker_Env.lax =
           (uu___152_8751.FStar_TypeChecker_Env.lax);
         FStar_TypeChecker_Env.lax_universes =
           (uu___152_8751.FStar_TypeChecker_Env.lax_universes);
         FStar_TypeChecker_Env.type_of =
           (uu___152_8751.FStar_TypeChecker_Env.type_of);
         FStar_TypeChecker_Env.universe_of =
           (uu___152_8751.FStar_TypeChecker_Env.universe_of);
         FStar_TypeChecker_Env.use_bv_sorts =
           (uu___152_8751.FStar_TypeChecker_Env.use_bv_sorts);
         FStar_TypeChecker_Env.qname_and_index =
           (uu___152_8751.FStar_TypeChecker_Env.qname_and_index)
       })
  
let build_lattice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____8759) ->
          let uu___153_8760 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___153_8760.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___153_8760.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___153_8760.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___153_8760.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___153_8760.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___153_8760.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___153_8760.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___153_8760.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___153_8760.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___153_8760.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (let uu___154_8761 = env.FStar_TypeChecker_Env.effects  in
               {
                 FStar_TypeChecker_Env.decls = (ne ::
                   ((env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.decls));
                 FStar_TypeChecker_Env.order =
                   (uu___154_8761.FStar_TypeChecker_Env.order);
                 FStar_TypeChecker_Env.joins =
                   (uu___154_8761.FStar_TypeChecker_Env.joins)
               });
            FStar_TypeChecker_Env.generalize =
              (uu___153_8760.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___153_8760.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___153_8760.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___153_8760.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___153_8760.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___153_8760.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___153_8760.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___153_8760.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___153_8760.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___153_8760.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___153_8760.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___153_8760.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___153_8760.FStar_TypeChecker_Env.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect (sub1,uu____8763) ->
          extend_effect_lattice env sub1
      | uu____8764 -> env
  