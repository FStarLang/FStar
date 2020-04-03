open Prims
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____13 = FStar_Syntax_Util.head_and_args t  in
    match uu____13 with
    | (head1,_args) ->
        let uu____57 =
          let uu____58 = FStar_Syntax_Subst.compress head1  in
          uu____58.FStar_Syntax_Syntax.n  in
        (match uu____57 with
         | FStar_Syntax_Syntax.Tm_uvar uu____62 -> true
         | uu____76 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____84 = FStar_Syntax_Util.head_and_args t  in
    match uu____84 with
    | (head1,_args) ->
        let uu____127 =
          let uu____128 = FStar_Syntax_Subst.compress head1  in
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
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> goal_dep_id
  
let (__proj__Mkgoal_dep__item__goal_type : goal_dep -> goal_type) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> goal_type
  
let (__proj__Mkgoal_dep__item__goal_imp :
  goal_dep -> FStar_TypeChecker_Common.implicit) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> goal_imp
  
let (__proj__Mkgoal_dep__item__assignees :
  goal_dep -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> assignees
  
let (__proj__Mkgoal_dep__item__goal_dep_uvars :
  goal_dep -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> goal_dep_uvars
  
let (__proj__Mkgoal_dep__item__dependences :
  goal_dep -> goal_dep Prims.list FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> dependences
  
let (__proj__Mkgoal_dep__item__visited : goal_dep -> Prims.int FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> visited
  
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
  
let (sort_goals :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.implicits ->
      FStar_TypeChecker_Common.implicits ->
        FStar_TypeChecker_Common.implicits)
  =
  fun env  ->
    fun eqs  ->
      fun rest  ->
        let goal_dep_id = FStar_Util.mk_ref Prims.int_zero  in
        let uu____752 = (Prims.int_zero, Prims.int_one, (Prims.of_int (2)))
           in
        match uu____752 with
        | (mark_unset,mark_inprogress,mark_finished) ->
            let empty_uv_set = FStar_Syntax_Free.new_uv_set ()  in
            let eq_as_goal_dep eq1 =
              let uu____784 =
                match ((eq1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ).FStar_Syntax_Syntax.n
                with
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_fvar fv;
                            FStar_Syntax_Syntax.pos = uu____806;
                            FStar_Syntax_Syntax.vars = uu____807;_},uu____808);
                       FStar_Syntax_Syntax.pos = uu____809;
                       FStar_Syntax_Syntax.vars = uu____810;_},uu____811::
                     (lhs,uu____813)::(rhs,uu____815)::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq2_lid
                    ->
                    let flex_lhs = is_flex lhs  in
                    let flex_rhs = is_flex rhs  in
                    if flex_lhs && flex_rhs
                    then
                      let uu____905 =
                        let uu____910 = flex_uvar_head lhs  in
                        let uu____911 = flex_uvar_head rhs  in
                        (uu____910, uu____911)  in
                      (match uu____905 with
                       | (lhs1,rhs1) ->
                           let assignees =
                             let uu____927 =
                               FStar_Util.set_add lhs1 empty_uv_set  in
                             FStar_Util.set_add rhs1 uu____927  in
                           ((FlexFlex (lhs1, rhs1)), assignees, assignees))
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
                | uu____995 -> failwith "Not an eq"  in
              match uu____784 with
              | (goal_type,assignees,dep_uvars) ->
                  (FStar_Util.incr goal_dep_id;
                   (let uu____1019 = FStar_ST.op_Bang goal_dep_id  in
                    let uu____1042 = FStar_Util.mk_ref []  in
                    let uu____1049 = FStar_Util.mk_ref mark_unset  in
                    {
                      goal_dep_id = uu____1019;
                      goal_type;
                      goal_imp = eq1;
                      assignees;
                      goal_dep_uvars = dep_uvars;
                      dependences = uu____1042;
                      visited = uu____1049
                    }))
               in
            let imp_as_goal_dep i =
              FStar_Util.incr goal_dep_id;
              (let imp_goal uu____1066 =
                 (let uu____1068 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "ResolveImplicitsHook")
                     in
                  if uu____1068
                  then
                    let uu____1073 =
                      FStar_Syntax_Print.term_to_string
                        (i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                       in
                    FStar_Util.print1 "Discarding goal as imp: %s\n"
                      uu____1073
                  else ());
                 (let uu____1078 = FStar_ST.op_Bang goal_dep_id  in
                  let uu____1101 = FStar_Util.mk_ref []  in
                  let uu____1108 = FStar_Util.mk_ref mark_unset  in
                  {
                    goal_dep_id = uu____1078;
                    goal_type = (Imp (i.FStar_TypeChecker_Common.imp_uvar));
                    goal_imp = i;
                    assignees = empty_uv_set;
                    goal_dep_uvars = empty_uv_set;
                    dependences = uu____1101;
                    visited = uu____1108
                  })
                  in
               let uu____1113 =
                 FStar_Syntax_Util.un_squash
                   (i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               match uu____1113 with
               | FStar_Pervasives_Native.None  -> imp_goal ()
               | FStar_Pervasives_Native.Some t ->
                   let uu____1125 = FStar_Syntax_Util.head_and_args t  in
                   (match uu____1125 with
                    | (head1,args) ->
                        let uu____1168 =
                          let uu____1183 =
                            let uu____1184 = FStar_Syntax_Util.un_uinst head1
                               in
                            uu____1184.FStar_Syntax_Syntax.n  in
                          (uu____1183, args)  in
                        (match uu____1168 with
                         | (FStar_Syntax_Syntax.Tm_fvar
                            fv,(outer,uu____1199)::(inner,uu____1201)::
                            (frame,uu____1203)::[]) when
                             (let uu____1272 =
                                FStar_Ident.lid_of_str
                                  "Steel.Memory.Tactics.can_be_split_into"
                                 in
                              FStar_Syntax_Syntax.fv_eq_lid fv uu____1272) &&
                               (is_flex frame)
                             ->
                             let imp_uvar = flex_uvar_head frame  in
                             let uu____1275 = FStar_ST.op_Bang goal_dep_id
                                in
                             let uu____1298 =
                               FStar_Util.set_add imp_uvar empty_uv_set  in
                             let uu____1301 =
                               let uu____1304 = FStar_Syntax_Free.uvars outer
                                  in
                               let uu____1307 = FStar_Syntax_Free.uvars inner
                                  in
                               FStar_Util.set_union uu____1304 uu____1307  in
                             let uu____1310 = FStar_Util.mk_ref []  in
                             let uu____1317 = FStar_Util.mk_ref mark_unset
                                in
                             {
                               goal_dep_id = uu____1275;
                               goal_type =
                                 (Can_be_split_into (outer, inner, imp_uvar));
                               goal_imp = i;
                               assignees = uu____1298;
                               goal_dep_uvars = uu____1301;
                               dependences = uu____1310;
                               visited = uu____1317
                             }
                         | uu____1322 -> imp_goal ())))
               in
            let goal_deps =
              let uu____1340 = FStar_List.map eq_as_goal_dep eqs  in
              let uu____1343 = FStar_List.map imp_as_goal_dep rest  in
              FStar_List.append uu____1340 uu____1343  in
            let uu____1346 =
              FStar_List.partition
                (fun gd  ->
                   match gd.goal_type with
                   | Imp uu____1359 -> false
                   | uu____1361 -> true) goal_deps
               in
            (match uu____1346 with
             | (goal_deps1,rest1) ->
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
                                (let uu____1460 =
                                   in_deps current_deps other_gd  in
                                 if uu____1460
                                 then false
                                 else
                                   (match other_gd.goal_type with
                                    | FlexFlex uu____1468 ->
                                        let uu____1473 =
                                          FStar_ST.op_Bang
                                            other_gd.dependences
                                           in
                                        (match uu____1473 with
                                         | [] -> false
                                         | deps ->
                                             let eligible =
                                               let uu____1506 =
                                                 in_deps deps gd  in
                                               Prims.op_Negation uu____1506
                                                in
                                             if eligible
                                             then
                                               let uu____1510 =
                                                 let uu____1512 =
                                                   FStar_Util.set_intersect
                                                     dependent_uvars
                                                     other_gd.assignees
                                                    in
                                                 FStar_Util.set_is_empty
                                                   uu____1512
                                                  in
                                               Prims.op_Negation uu____1510
                                             else false)
                                    | uu____1518 ->
                                        let uu____1519 =
                                          let uu____1521 =
                                            FStar_Util.set_intersect
                                              dependent_uvars
                                              other_gd.assignees
                                             in
                                          FStar_Util.set_is_empty uu____1521
                                           in
                                        Prims.op_Negation uu____1519))
                               in
                            if res
                            then FStar_ST.op_Colon_Equals changed true
                            else ();
                            res) gds
                        in
                     (let uu____1551 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ResolveImplicitsHook")
                         in
                      if uu____1551
                      then
                        let uu____1556 = print_goal_dep gd  in
                        let uu____1558 = print_uvar_set dependent_uvars  in
                        let uu____1560 =
                          let uu____1562 =
                            FStar_List.map
                              (fun x  ->
                                 FStar_Util.string_of_int x.goal_dep_id) deps
                             in
                          FStar_All.pipe_right uu____1562
                            (FStar_String.concat "; ")
                           in
                        FStar_Util.print3
                          "Deps for goal %s, dep uvars = %s ... [%s]\n"
                          uu____1556 uu____1558 uu____1560
                      else ());
                     (let uu____1578 =
                        let uu____1581 = FStar_ST.op_Bang gd.dependences  in
                        FStar_List.append deps uu____1581  in
                      FStar_ST.op_Colon_Equals gd.dependences uu____1578);
                     FStar_ST.op_Bang changed  in
                   let rec aux uu____1656 =
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
                     let uu____1714 =
                       let uu____1716 = FStar_ST.op_Bang gd.visited  in
                       uu____1716 = mark_finished  in
                     if uu____1714
                     then ()
                     else
                       (let uu____1743 =
                          let uu____1745 = FStar_ST.op_Bang gd.visited  in
                          uu____1745 = mark_inprogress  in
                        if uu____1743
                        then
                          ((let uu____1771 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ResolveImplicitsHook")
                               in
                            if uu____1771
                            then
                              let uu____1776 =
                                let uu____1778 =
                                  FStar_List.map print_goal_dep (gd :: cycle)
                                   in
                                FStar_All.pipe_right uu____1778
                                  (FStar_String.concat ", ")
                                 in
                              FStar_Util.print1 "Cycle:\n%s\n" uu____1776
                            else ());
                           FStar_ST.op_Colon_Equals has_cycle true)
                        else
                          (FStar_ST.op_Colon_Equals gd.visited
                             mark_inprogress;
                           (let uu____1838 = FStar_ST.op_Bang gd.dependences
                               in
                            FStar_List.iter (visit (gd :: cycle)) uu____1838);
                           FStar_ST.op_Colon_Equals gd.visited mark_finished;
                           (let uu____1886 =
                              let uu____1889 = FStar_ST.op_Bang out  in gd ::
                                uu____1889
                               in
                            FStar_ST.op_Colon_Equals out uu____1886)))
                      in
                   FStar_List.iter (visit []) gds;
                   (let uu____1939 = FStar_ST.op_Bang has_cycle  in
                    if uu____1939
                    then FStar_Pervasives_Native.None
                    else
                      (let uu____1971 = FStar_ST.op_Bang out  in
                       FStar_Pervasives_Native.Some uu____1971))
                    in
                 (fill_deps goal_deps1;
                  (let uu____2001 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ResolveImplicitsHook")
                      in
                   if uu____2001
                   then
                     (FStar_Util.print_string
                        "<<<<<<<<<<<<Goals before sorting>>>>>>>>>>>>>>>\n";
                      FStar_List.iter
                        (fun gd  ->
                           let uu____2011 = print_goal_dep gd  in
                           FStar_Util.print_string uu____2011) goal_deps1)
                   else ());
                  (let goal_deps2 =
                     let uu____2018 = topological_sort goal_deps1  in
                     match uu____2018 with
                     | FStar_Pervasives_Native.None  -> goal_deps1
                     | FStar_Pervasives_Native.Some sorted1 ->
                         FStar_List.rev sorted1
                      in
                   (let uu____2033 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "ResolveImplicitsHook")
                       in
                    if uu____2033
                    then
                      (FStar_Util.print_string
                         "<<<<<<<<<<<<Goals after sorting>>>>>>>>>>>>>>>\n";
                       FStar_List.iter
                         (fun gd  ->
                            let uu____2043 = print_goal_dep gd  in
                            FStar_Util.print_string uu____2043) goal_deps2)
                    else ());
                   FStar_List.map (fun gd  -> gd.goal_imp)
                     (FStar_List.append goal_deps2 rest1))))
  