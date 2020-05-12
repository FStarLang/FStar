open Prims
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____13 = FStar_Syntax_Util.head_and_args t  in
    match uu____13 with
    | (head,_args) ->
        let uu____57 =
          let uu____58 = FStar_Syntax_Subst.compress head  in
          uu____58.FStar_Syntax_Syntax.n  in
        (match uu____57 with
         | FStar_Syntax_Syntax.Tm_uvar uu____62 -> true
         | uu____76 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____84 = FStar_Syntax_Util.head_and_args t  in
    match uu____84 with
    | (head,_args) ->
        let uu____127 =
          let uu____128 = FStar_Syntax_Subst.compress head  in
          uu____128.FStar_Syntax_Syntax.n  in
        (match uu____127 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____132) -> u
         | uu____149 -> failwith "Not a flex-uvar")
  
type goal_type =
  | FlexRigid of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | FlexFlex of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.ctx_uvar)
  
  | Can_be_split_into of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term
  * FStar_Syntax_Syntax.ctx_uvar) 
  | Imp of FStar_Syntax_Syntax.ctx_uvar 
let (uu___is_FlexRigid : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | FlexRigid _0 -> true | uu____199 -> false
  
let (__proj__FlexRigid__item___0 :
  goal_type -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | FlexRigid _0 -> _0 
let (uu___is_FlexFlex : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | FlexFlex _0 -> true | uu____234 -> false
  
let (__proj__FlexFlex__item___0 :
  goal_type -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.ctx_uvar))
  = fun projectee  -> match projectee with | FlexFlex _0 -> _0 
let (uu___is_Can_be_split_into : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Can_be_split_into _0 -> true | uu____271 -> false
  
let (__proj__Can_be_split_into__item___0 :
  goal_type ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.ctx_uvar))
  = fun projectee  -> match projectee with | Can_be_split_into _0 -> _0 
let (uu___is_Imp : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp _0 -> true | uu____308 -> false
  
let (__proj__Imp__item___0 : goal_type -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  -> match projectee with | Imp _0 -> _0 
type goal_dep =
  {
  goal_dep_id: Prims.int ;
  goal_type: goal_type ;
  goal_imp: FStar_TypeChecker_Common.implicit ;
  assignees: FStar_Syntax_Syntax.ctx_uvar FStar_Util.set ;
  goal_dep_uvars: FStar_Syntax_Syntax.ctx_uvar FStar_Util.set ;
  dependences: goal_dep Prims.list FStar_ST.ref ;
  visited: Prims.int FStar_ST.ref }
let (__proj__Mkgoal_dep__item__goal_dep_id : goal_dep -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> goal_dep_id
  
let (__proj__Mkgoal_dep__item__goal_type : goal_dep -> goal_type) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> goal_type1
  
let (__proj__Mkgoal_dep__item__goal_imp :
  goal_dep -> FStar_TypeChecker_Common.implicit) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> goal_imp
  
let (__proj__Mkgoal_dep__item__assignees :
  goal_dep -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> assignees
  
let (__proj__Mkgoal_dep__item__goal_dep_uvars :
  goal_dep -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> goal_dep_uvars
  
let (__proj__Mkgoal_dep__item__dependences :
  goal_dep -> goal_dep Prims.list FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> dependences
  
let (__proj__Mkgoal_dep__item__visited : goal_dep -> Prims.int FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> visited
  
type goal_deps = goal_dep Prims.list
let (print_uvar_set :
  FStar_Syntax_Syntax.ctx_uvar FStar_Util.set -> Prims.string) =
  fun s  ->
    let uu____648 =
      let uu____652 = FStar_Util.set_elements s  in
      FStar_All.pipe_right uu____652
        (FStar_List.map
           (fun u  ->
              let uu____664 =
                let uu____666 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____666  in
              Prims.op_Hat "?" uu____664))
       in
    FStar_All.pipe_right uu____648 (FStar_String.concat "; ")
  
let (print_goal_dep : goal_dep -> Prims.string) =
  fun gd  ->
    let uu____683 = FStar_Util.string_of_int gd.goal_dep_id  in
    let uu____685 = print_uvar_set gd.assignees  in
    let uu____687 =
      let uu____689 =
        let uu____693 = FStar_ST.op_Bang gd.dependences  in
        FStar_List.map (fun gd1  -> FStar_Util.string_of_int gd1.goal_dep_id)
          uu____693
         in
      FStar_All.pipe_right uu____689 (FStar_String.concat "; ")  in
    let uu____727 =
      FStar_Syntax_Print.ctx_uvar_to_string
        (gd.goal_imp).FStar_TypeChecker_Common.imp_uvar
       in
    FStar_Util.format4 "%s:{assignees=[%s], dependences=[%s]}\n\t%s\n"
      uu____683 uu____685 uu____687 uu____727
  
let (find_user_tac_for_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun u  ->
      match u.FStar_Syntax_Syntax.ctx_uvar_meta with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
          a) ->
          let hooks =
            FStar_TypeChecker_Env.lookup_attr env
              FStar_Parser_Const.resolve_implicits_attr_string
             in
          FStar_All.pipe_right hooks
            (FStar_Util.try_find
               (fun hook  ->
                  FStar_All.pipe_right hook.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some (FStar_Syntax_Util.attr_eq a))))
      | uu____760 -> FStar_Pervasives_Native.None
  
let (should_defer_uvar_to_user_tac :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun env  ->
    fun u  ->
      if Prims.op_Negation env.FStar_TypeChecker_Env.enable_defer_to_tac
      then false
      else
        (let uu____780 = find_user_tac_for_uvar env u  in
         FStar_Option.isSome uu____780)
  
let (sort_goals :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.implicits -> FStar_TypeChecker_Common.implicits)
  =
  fun env  ->
    fun imps  ->
      let goal_dep_id = FStar_Util.mk_ref Prims.int_zero  in
      let uu____800 = (Prims.int_zero, Prims.int_one, (Prims.of_int (2)))  in
      match uu____800 with
      | (mark_unset,mark_inprogress,mark_finished) ->
          let empty_uv_set = FStar_Syntax_Free.new_uv_set ()  in
          let imp_as_goal_dep imp =
            FStar_Util.incr goal_dep_id;
            (match ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ).FStar_Syntax_Syntax.n
             with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____834;
                         FStar_Syntax_Syntax.vars = uu____835;_},uu____836);
                    FStar_Syntax_Syntax.pos = uu____837;
                    FStar_Syntax_Syntax.vars = uu____838;_},uu____839::
                  (lhs,uu____841)::(rhs,uu____843)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid
                 ->
                 let flex_lhs = is_flex lhs  in
                 let flex_rhs = is_flex rhs  in
                 let uu____922 =
                   if flex_lhs && flex_rhs
                   then
                     let uu____944 =
                       let uu____949 = flex_uvar_head lhs  in
                       let uu____950 = flex_uvar_head rhs  in
                       (uu____949, uu____950)  in
                     match uu____944 with
                     | (lhs1,rhs1) ->
                         let assignees =
                           let uu____966 =
                             FStar_Util.set_add lhs1 empty_uv_set  in
                           FStar_Util.set_add rhs1 uu____966  in
                         ((FlexFlex (lhs1, rhs1)), assignees, assignees)
                   else
                     if flex_lhs
                     then
                       (let lhs1 = flex_uvar_head lhs  in
                        let assignees = FStar_Util.set_add lhs1 empty_uv_set
                           in
                        let dep_uvars = FStar_Syntax_Free.uvars rhs  in
                        ((FlexRigid (lhs1, rhs)), assignees, dep_uvars))
                     else
                       if flex_rhs
                       then
                         (let rhs1 = flex_uvar_head rhs  in
                          let assignees =
                            FStar_Util.set_add rhs1 empty_uv_set  in
                          let dep_uvars = FStar_Syntax_Free.uvars lhs  in
                          ((FlexRigid (rhs1, lhs)), assignees, dep_uvars))
                       else
                         failwith
                           "Impossible: deferred goals must be flex on one at least one side"
                    in
                 (match uu____922 with
                  | (goal_type1,assignees,dep_uvars) ->
                      let uu____1045 = FStar_ST.op_Bang goal_dep_id  in
                      let uu____1068 = FStar_Util.mk_ref []  in
                      let uu____1075 = FStar_Util.mk_ref mark_unset  in
                      {
                        goal_dep_id = uu____1045;
                        goal_type = goal_type1;
                        goal_imp = imp;
                        assignees;
                        goal_dep_uvars = dep_uvars;
                        dependences = uu____1068;
                        visited = uu____1075
                      })
             | uu____1080 ->
                 let imp_goal uu____1086 =
                   (let uu____1088 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "ResolveImplicitsHook")
                       in
                    if uu____1088
                    then
                      let uu____1093 =
                        FStar_Syntax_Print.term_to_string
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Util.print1 "Goal is a generic implicit: %s\n"
                        uu____1093
                    else ());
                   (let uu____1098 = FStar_ST.op_Bang goal_dep_id  in
                    let uu____1121 = FStar_Util.mk_ref []  in
                    let uu____1128 = FStar_Util.mk_ref mark_unset  in
                    {
                      goal_dep_id = uu____1098;
                      goal_type =
                        (Imp (imp.FStar_TypeChecker_Common.imp_uvar));
                      goal_imp = imp;
                      assignees = empty_uv_set;
                      goal_dep_uvars = empty_uv_set;
                      dependences = uu____1121;
                      visited = uu____1128
                    })
                    in
                 let uu____1133 =
                   FStar_Syntax_Util.un_squash
                     (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                    in
                 (match uu____1133 with
                  | FStar_Pervasives_Native.None  -> imp_goal ()
                  | FStar_Pervasives_Native.Some t ->
                      let uu____1145 = FStar_Syntax_Util.head_and_args t  in
                      (match uu____1145 with
                       | (head,args) ->
                           let uu____1188 =
                             let uu____1203 =
                               let uu____1204 =
                                 FStar_Syntax_Util.un_uinst head  in
                               uu____1204.FStar_Syntax_Syntax.n  in
                             (uu____1203, args)  in
                           (match uu____1188 with
                            | (FStar_Syntax_Syntax.Tm_fvar
                               fv,(outer,uu____1219)::(inner,uu____1221)::
                               (frame,uu____1223)::[]) when
                                (let uu____1292 =
                                   FStar_Ident.lid_of_str
                                     "Steel.Memory.Tactics.can_be_split_into"
                                    in
                                 FStar_Syntax_Syntax.fv_eq_lid fv uu____1292)
                                  && (is_flex frame)
                                ->
                                let imp_uvar = flex_uvar_head frame  in
                                let uu____1295 = FStar_ST.op_Bang goal_dep_id
                                   in
                                let uu____1318 =
                                  FStar_Util.set_add imp_uvar empty_uv_set
                                   in
                                let uu____1321 =
                                  let uu____1324 =
                                    FStar_Syntax_Free.uvars outer  in
                                  let uu____1327 =
                                    FStar_Syntax_Free.uvars inner  in
                                  FStar_Util.set_union uu____1324 uu____1327
                                   in
                                let uu____1330 = FStar_Util.mk_ref []  in
                                let uu____1337 = FStar_Util.mk_ref mark_unset
                                   in
                                {
                                  goal_dep_id = uu____1295;
                                  goal_type =
                                    (Can_be_split_into
                                       (outer, inner, imp_uvar));
                                  goal_imp = imp;
                                  assignees = uu____1318;
                                  goal_dep_uvars = uu____1321;
                                  dependences = uu____1330;
                                  visited = uu____1337
                                }
                            | uu____1342 -> imp_goal ()))))
             in
          let goal_deps1 = FStar_List.map imp_as_goal_dep imps  in
          let uu____1360 =
            FStar_List.partition
              (fun gd  ->
                 match gd.goal_type with
                 | Imp uu____1373 -> false
                 | uu____1375 -> true) goal_deps1
             in
          (match uu____1360 with
           | (goal_deps2,rest) ->
               let fill_deps gds =
                 let in_deps deps gd =
                   FStar_Util.for_some
                     (fun d  -> d.goal_dep_id = gd.goal_dep_id) deps
                    in
                 let fill_deps_of_goal gd =
                   let dependent_uvars = gd.goal_dep_uvars  in
                   let current_deps = FStar_ST.op_Bang gd.dependences  in
                   let changed = FStar_Util.mk_ref false  in
                   let deps =
                     FStar_List.filter
                       (fun other_gd  ->
                          let res =
                            if gd.goal_dep_id = other_gd.goal_dep_id
                            then false
                            else
                              (let uu____1474 = in_deps current_deps other_gd
                                  in
                               if uu____1474
                               then false
                               else
                                 (match other_gd.goal_type with
                                  | FlexFlex uu____1482 ->
                                      let uu____1487 =
                                        FStar_ST.op_Bang other_gd.dependences
                                         in
                                      (match uu____1487 with
                                       | [] -> false
                                       | deps ->
                                           let eligible =
                                             let uu____1520 = in_deps deps gd
                                                in
                                             Prims.op_Negation uu____1520  in
                                           if eligible
                                           then
                                             let uu____1524 =
                                               let uu____1526 =
                                                 FStar_Util.set_intersect
                                                   dependent_uvars
                                                   other_gd.assignees
                                                  in
                                               FStar_Util.set_is_empty
                                                 uu____1526
                                                in
                                             Prims.op_Negation uu____1524
                                           else false)
                                  | uu____1532 ->
                                      let uu____1533 =
                                        let uu____1535 =
                                          FStar_Util.set_intersect
                                            dependent_uvars
                                            other_gd.assignees
                                           in
                                        FStar_Util.set_is_empty uu____1535
                                         in
                                      Prims.op_Negation uu____1533))
                             in
                          if res
                          then FStar_ST.op_Colon_Equals changed true
                          else ();
                          res) gds
                      in
                   (let uu____1565 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "ResolveImplicitsHook")
                       in
                    if uu____1565
                    then
                      let uu____1570 = print_goal_dep gd  in
                      let uu____1572 = print_uvar_set dependent_uvars  in
                      let uu____1574 =
                        let uu____1576 =
                          FStar_List.map
                            (fun x  -> FStar_Util.string_of_int x.goal_dep_id)
                            deps
                           in
                        FStar_All.pipe_right uu____1576
                          (FStar_String.concat "; ")
                         in
                      FStar_Util.print3
                        "Deps for goal %s, dep uvars = %s ... [%s]\n"
                        uu____1570 uu____1572 uu____1574
                    else ());
                   (let uu____1592 =
                      let uu____1595 = FStar_ST.op_Bang gd.dependences  in
                      FStar_List.append deps uu____1595  in
                    FStar_ST.op_Colon_Equals gd.dependences uu____1592);
                   FStar_ST.op_Bang changed  in
                 let rec aux uu____1670 =
                   let changed =
                     FStar_List.fold_right
                       (fun gd  ->
                          fun changed  ->
                            let changed' = fill_deps_of_goal gd  in
                            changed || changed') gds false
                      in
                   if changed then aux () else ()  in
                 aux ()  in
               let topological_sort gds =
                 let out = FStar_Util.mk_ref []  in
                 let has_cycle = FStar_Util.mk_ref false  in
                 let rec visit cycle gd =
                   let uu____1728 =
                     let uu____1730 = FStar_ST.op_Bang gd.visited  in
                     uu____1730 = mark_finished  in
                   if uu____1728
                   then ()
                   else
                     (let uu____1757 =
                        let uu____1759 = FStar_ST.op_Bang gd.visited  in
                        uu____1759 = mark_inprogress  in
                      if uu____1757
                      then
                        ((let uu____1785 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ResolveImplicitsHook")
                             in
                          if uu____1785
                          then
                            let uu____1790 =
                              let uu____1792 =
                                FStar_List.map print_goal_dep (gd :: cycle)
                                 in
                              FStar_All.pipe_right uu____1792
                                (FStar_String.concat ", ")
                               in
                            FStar_Util.print1 "Cycle:\n%s\n" uu____1790
                          else ());
                         FStar_ST.op_Colon_Equals has_cycle true)
                      else
                        (FStar_ST.op_Colon_Equals gd.visited mark_inprogress;
                         (let uu____1852 = FStar_ST.op_Bang gd.dependences
                             in
                          FStar_List.iter (visit (gd :: cycle)) uu____1852);
                         FStar_ST.op_Colon_Equals gd.visited mark_finished;
                         (let uu____1900 =
                            let uu____1903 = FStar_ST.op_Bang out  in gd ::
                              uu____1903
                             in
                          FStar_ST.op_Colon_Equals out uu____1900)))
                    in
                 FStar_List.iter (visit []) gds;
                 (let uu____1953 = FStar_ST.op_Bang has_cycle  in
                  if uu____1953
                  then FStar_Pervasives_Native.None
                  else
                    (let uu____1985 = FStar_ST.op_Bang out  in
                     FStar_Pervasives_Native.Some uu____1985))
                  in
               (fill_deps goal_deps2;
                (let uu____2015 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "ResolveImplicitsHook")
                    in
                 if uu____2015
                 then
                   (FStar_Util.print_string
                      "<<<<<<<<<<<<Goals before sorting>>>>>>>>>>>>>>>\n";
                    FStar_List.iter
                      (fun gd  ->
                         let uu____2025 = print_goal_dep gd  in
                         FStar_Util.print_string uu____2025) goal_deps2)
                 else ());
                (let goal_deps3 =
                   let uu____2032 = topological_sort goal_deps2  in
                   match uu____2032 with
                   | FStar_Pervasives_Native.None  -> goal_deps2
                   | FStar_Pervasives_Native.Some sorted ->
                       FStar_List.rev sorted
                    in
                 (let uu____2047 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "ResolveImplicitsHook")
                     in
                  if uu____2047
                  then
                    (FStar_Util.print_string
                       "<<<<<<<<<<<<Goals after sorting>>>>>>>>>>>>>>>\n";
                     FStar_List.iter
                       (fun gd  ->
                          let uu____2057 = print_goal_dep gd  in
                          FStar_Util.print_string uu____2057) goal_deps3)
                  else ());
                 FStar_List.map (fun gd  -> gd.goal_imp)
                   (FStar_List.append goal_deps3 rest))))
  
let (solve_goals_with_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.implicits ->
        FStar_Syntax_Syntax.sigelt -> unit)
  =
  fun env  ->
    fun g  ->
      fun imps  ->
        fun tac  ->
          let deferred_goals = sort_goals env imps  in
          let guard =
            let uu___212_2086 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___212_2086.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac = [];
              FStar_TypeChecker_Common.deferred =
                (uu___212_2086.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___212_2086.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = imps
            }  in
          let resolve_tac =
            match tac.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let (uu____2093,lid::[]) ->
                let qn = FStar_TypeChecker_Env.lookup_qname env lid  in
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv lid
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero) FStar_Pervasives_Native.None
                   in
                let dd =
                  let uu____2101 =
                    FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn  in
                  match uu____2101 with
                  | FStar_Pervasives_Native.Some dd -> dd
                  | FStar_Pervasives_Native.None  -> failwith "Expected a dd"
                   in
                let term =
                  let uu____2107 =
                    FStar_Syntax_Syntax.lid_as_fv lid dd
                      FStar_Pervasives_Native.None
                     in
                  FStar_Syntax_Syntax.fv_to_tm uu____2107  in
                term
            | uu____2108 -> failwith "Resolve_tac not found"  in
          let env1 =
            let uu___229_2111 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___229_2111.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___229_2111.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___229_2111.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___229_2111.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___229_2111.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___229_2111.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___229_2111.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___229_2111.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___229_2111.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___229_2111.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___229_2111.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___229_2111.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___229_2111.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___229_2111.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___229_2111.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___229_2111.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___229_2111.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___229_2111.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___229_2111.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___229_2111.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___229_2111.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___229_2111.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___229_2111.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___229_2111.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___229_2111.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___229_2111.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___229_2111.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___229_2111.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___229_2111.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___229_2111.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___229_2111.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___229_2111.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___229_2111.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___229_2111.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___229_2111.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___229_2111.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___229_2111.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___229_2111.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___229_2111.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___229_2111.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___229_2111.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___229_2111.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___229_2111.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___229_2111.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___229_2111.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___229_2111.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac = false
            }  in
          env1.FStar_TypeChecker_Env.try_solve_implicits_hook env1
            resolve_tac deferred_goals
  
let (solve_deferred_to_tactic_goals :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let deferred = g.FStar_TypeChecker_Common.deferred_to_tac  in
      match deferred with
      | [] -> g
      | uu____2130 ->
          let prob_as_implicit uu____2145 =
            match uu____2145 with
            | (reason,prob) ->
                (match prob with
                 | FStar_TypeChecker_Common.TProb tp when
                     tp.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let env1 =
                       let uu___243_2167 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___243_2167.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___243_2167.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___243_2167.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           ((tp.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___243_2167.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___243_2167.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___243_2167.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___243_2167.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___243_2167.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___243_2167.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___243_2167.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___243_2167.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___243_2167.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___243_2167.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___243_2167.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___243_2167.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___243_2167.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___243_2167.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___243_2167.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___243_2167.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___243_2167.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___243_2167.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___243_2167.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___243_2167.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___243_2167.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___243_2167.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___243_2167.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___243_2167.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___243_2167.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___243_2167.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___243_2167.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___243_2167.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___243_2167.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___243_2167.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___243_2167.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___243_2167.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___243_2167.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___243_2167.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___243_2167.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___243_2167.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___243_2167.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___243_2167.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___243_2167.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___243_2167.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___243_2167.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___243_2167.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___243_2167.FStar_TypeChecker_Env.enable_defer_to_tac)
                       }  in
                     let env_lax =
                       let uu___246_2169 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___246_2169.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___246_2169.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___246_2169.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___246_2169.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___246_2169.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___246_2169.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___246_2169.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___246_2169.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___246_2169.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___246_2169.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___246_2169.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___246_2169.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___246_2169.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___246_2169.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___246_2169.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___246_2169.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___246_2169.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (uu___246_2169.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___246_2169.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___246_2169.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___246_2169.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___246_2169.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___246_2169.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___246_2169.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___246_2169.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___246_2169.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___246_2169.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___246_2169.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___246_2169.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___246_2169.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___246_2169.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___246_2169.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___246_2169.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___246_2169.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___246_2169.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___246_2169.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___246_2169.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___246_2169.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___246_2169.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___246_2169.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___246_2169.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___246_2169.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___246_2169.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___246_2169.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (uu___246_2169.FStar_TypeChecker_Env.enable_defer_to_tac)
                       }  in
                     let uu____2172 =
                       let uu____2179 =
                         is_flex tp.FStar_TypeChecker_Common.lhs  in
                       if uu____2179
                       then
                         env1.FStar_TypeChecker_Env.type_of env_lax
                           tp.FStar_TypeChecker_Common.lhs
                       else
                         env1.FStar_TypeChecker_Env.type_of env_lax
                           tp.FStar_TypeChecker_Common.rhs
                        in
                     (match uu____2172 with
                      | (uu____2194,t_eq,uu____2196) ->
                          let goal_ty =
                            let uu____2198 =
                              env1.FStar_TypeChecker_Env.universe_of env_lax
                                t_eq
                               in
                            FStar_Syntax_Util.mk_eq2 uu____2198 t_eq
                              tp.FStar_TypeChecker_Common.lhs
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          let uu____2199 =
                            FStar_TypeChecker_Env.new_implicit_var_aux reason
                              (tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos
                              env1 goal_ty FStar_Syntax_Syntax.Strict
                              FStar_Pervasives_Native.None
                             in
                          (match uu____2199 with
                           | (goal,ctx_uvar,uu____2218) ->
                               let imp =
                                 let uu____2232 =
                                   let uu____2233 = FStar_List.hd ctx_uvar
                                      in
                                   FStar_Pervasives_Native.fst uu____2233  in
                                 {
                                   FStar_TypeChecker_Common.imp_reason = "";
                                   FStar_TypeChecker_Common.imp_uvar =
                                     uu____2232;
                                   FStar_TypeChecker_Common.imp_tm = goal;
                                   FStar_TypeChecker_Common.imp_range =
                                     ((tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos)
                                 }  in
                               let sigelt =
                                 let uu____2246 =
                                   is_flex tp.FStar_TypeChecker_Common.lhs
                                    in
                                 if uu____2246
                                 then
                                   let uu____2251 =
                                     flex_uvar_head
                                       tp.FStar_TypeChecker_Common.lhs
                                      in
                                   find_user_tac_for_uvar env1 uu____2251
                                 else
                                   (let uu____2254 =
                                      is_flex tp.FStar_TypeChecker_Common.rhs
                                       in
                                    if uu____2254
                                    then
                                      let uu____2259 =
                                        flex_uvar_head
                                          tp.FStar_TypeChecker_Common.rhs
                                         in
                                      find_user_tac_for_uvar env1 uu____2259
                                    else FStar_Pervasives_Native.None)
                                  in
                               (match sigelt with
                                | FStar_Pervasives_Native.None  ->
                                    failwith
                                      "Impossible: No tactic associated with deferred problem"
                                | FStar_Pervasives_Native.Some se ->
                                    (imp, se))))
                 | uu____2272 ->
                     failwith "Unexpected problem deferred to tactic")
             in
          let eqs =
            FStar_List.map prob_as_implicit
              g.FStar_TypeChecker_Common.deferred_to_tac
             in
          let uu____2294 =
            FStar_List.fold_right
              (fun imp  ->
                 fun uu____2326  ->
                   match uu____2326 with
                   | (more,imps) ->
                       let uu____2369 =
                         FStar_Syntax_Unionfind.find
                           (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       (match uu____2369 with
                        | FStar_Pervasives_Native.Some uu____2384 ->
                            (more, (imp :: imps))
                        | FStar_Pervasives_Native.None  ->
                            let se =
                              find_user_tac_for_uvar env
                                imp.FStar_TypeChecker_Common.imp_uvar
                               in
                            (match se with
                             | FStar_Pervasives_Native.None  ->
                                 (more, (imp :: imps))
                             | FStar_Pervasives_Native.Some se1 ->
                                 let imp1 =
                                   match (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_meta
                                   with
                                   | FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                       a) ->
                                       let reason =
                                         let uu____2423 =
                                           FStar_Syntax_Print.term_to_string
                                             a
                                            in
                                         FStar_Util.format2 "%s::%s"
                                           uu____2423
                                           imp.FStar_TypeChecker_Common.imp_reason
                                          in
                                       let uu___283_2426 = imp  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           = reason;
                                         FStar_TypeChecker_Common.imp_uvar =
                                           (uu___283_2426.FStar_TypeChecker_Common.imp_uvar);
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___283_2426.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___283_2426.FStar_TypeChecker_Common.imp_range)
                                       }
                                   | uu____2427 -> imp  in
                                 (((imp1, se1) :: more), imps))))
              g.FStar_TypeChecker_Common.implicits ([], [])
             in
          (match uu____2294 with
           | (more,imps) ->
               let bucketize is =
                 let map = FStar_Util.smap_create (Prims.of_int (17))  in
                 FStar_List.iter
                   (fun uu____2523  ->
                      match uu____2523 with
                      | (i,s) ->
                          let uu____2530 = FStar_Syntax_Util.lid_of_sigelt s
                             in
                          (match uu____2530 with
                           | FStar_Pervasives_Native.None  ->
                               failwith "Unexpected: tactic without a name"
                           | FStar_Pervasives_Native.Some l ->
                               let lstr = FStar_Ident.string_of_lid l  in
                               let uu____2537 =
                                 FStar_Util.smap_try_find map lstr  in
                               (match uu____2537 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Util.smap_add map lstr ([i], s)
                                | FStar_Pervasives_Native.Some (is1,s1) ->
                                    (FStar_Util.smap_remove map lstr;
                                     FStar_Util.smap_add map lstr
                                       ((i :: is1), s1))))) is;
                 FStar_Util.smap_fold map
                   (fun uu____2584  -> fun is1  -> fun out  -> is1 :: out) []
                  in
               let buckets = bucketize (FStar_List.append eqs more)  in
               (FStar_List.iter
                  (fun uu____2625  ->
                     match uu____2625 with
                     | (imps1,sigel) ->
                         solve_goals_with_tac env g imps1 sigel) buckets;
                (let uu___315_2632 = g  in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___315_2632.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac = [];
                   FStar_TypeChecker_Common.deferred =
                     (uu___315_2632.FStar_TypeChecker_Common.deferred);
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___315_2632.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits = imps
                 })))
  