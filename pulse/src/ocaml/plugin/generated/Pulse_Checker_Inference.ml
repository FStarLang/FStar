open Prims
let rec (gen_uvars :
  Pulse_Syntax.term ->
    ((Pulse_Syntax.term Prims.list * Pulse_Syntax.comp), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t_head ->
    match t_head with
    | Pulse_Syntax.Tm_Arrow
        ({ Pulse_Syntax.binder_ty = t; Pulse_Syntax.binder_ppname = uu___;_},
         FStar_Pervasives_Native.Some (Pulse_Syntax.Implicit), c_rest)
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
             (Prims.of_int (19)) (Prims.of_int (13)) (Prims.of_int (19))
             (Prims.of_int (23)))
          (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
             (Prims.of_int (19)) (Prims.of_int (26)) (Prims.of_int (28))
             (Prims.of_int (27))) (Obj.magic (Pulse_Syntax.gen_uvar t))
          (fun uu___1 ->
             (fun uv ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (20)) (Prims.of_int (17))
                        (Prims.of_int (20)) (Prims.of_int (41)))
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (21)) (Prims.of_int (4))
                        (Prims.of_int (28)) (Prims.of_int (27)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           Pulse_Syntax_Naming.open_comp_with c_rest uv))
                     (fun uu___1 ->
                        (fun c_rest1 ->
                           match c_rest1 with
                           | Pulse_Syntax.C_ST c ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 -> ([uv], c_rest1))))
                           | Pulse_Syntax.C_STAtomic (uu___1, c) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> ([uv], c_rest1))))
                           | Pulse_Syntax.C_STGhost (uu___1, c) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> ([uv], c_rest1))))
                           | Pulse_Syntax.C_Tot t1 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Inference.fst"
                                          (Prims.of_int (27))
                                          (Prims.of_int (30))
                                          (Prims.of_int (27))
                                          (Prims.of_int (41)))
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Inference.fst"
                                          (Prims.of_int (26))
                                          (Prims.of_int (16))
                                          (Prims.of_int (28))
                                          (Prims.of_int (27)))
                                       (Obj.magic (gen_uvars t1))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               match uu___1 with
                                               | (uv_rest, comp_typ) ->
                                                   ((uv :: uv_rest),
                                                     comp_typ)))))) uu___1)))
               uu___1)
    | uu___ ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
             (Prims.of_int (31)) (Prims.of_int (10)) (Prims.of_int (32))
             (Prims.of_int (60)))
          (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
             (Prims.of_int (31)) (Prims.of_int (3)) (Prims.of_int (32))
             (Prims.of_int (60)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                   (Prims.of_int (32)) (Prims.of_int (34))
                   (Prims.of_int (32)) (Prims.of_int (59)))
                (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                   (Prims.of_int (19)) (Prims.of_int (590))
                   (Prims.of_int (31)))
                (Obj.magic (Pulse_Syntax_Printer.term_to_string t_head))
                (fun uu___1 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        Prims.strcat "gen_uvars: unexpected t_head: "
                          (Prims.strcat uu___1 "")))))
          (fun uu___1 -> FStar_Tactics_Derived.fail uu___1)
let rec (check_valid_solution :
  Pulse_Syntax.term ->
    Pulse_Syntax.term ->
      (Pulse_Syntax.term * Pulse_Syntax.term) Prims.list ->
        ((Pulse_Syntax.term * Pulse_Syntax.term) Prims.list, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun t1 ->
           fun t2 ->
             fun uv_sols ->
               match uv_sols with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> [(t1, t2)])))
               | (t1', t2')::tl ->
                   Obj.magic
                     (Obj.repr
                        (if Pulse_Syntax.eq_tm t1 t1'
                         then
                           Obj.repr
                             (if Pulse_Syntax.eq_tm t2 t2'
                              then
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___ -> uv_sols)
                              else
                                FStar_Tactics_Derived.fail
                                  "check_valid_solution failed")
                         else
                           Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (43)) (Prims.of_int (21))
                                   (Prims.of_int (43)) (Prims.of_int (52)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (43)) (Prims.of_int (9))
                                   (Prims.of_int (43)) (Prims.of_int (52)))
                                (Obj.magic (check_valid_solution t1 t2 tl))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> (t1', t2') :: uu___1))))))
          uu___2 uu___1 uu___
let (is_reveal_uvar :
  Pulse_Syntax.term ->
    (Pulse_Syntax.universe * Pulse_Syntax.term * Pulse_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match t with
    | Pulse_Syntax.Tm_PureApp
        (Pulse_Syntax.Tm_PureApp
         (Pulse_Syntax.Tm_UInst (l, u::[]), FStar_Pervasives_Native.Some
          (Pulse_Syntax.Implicit), ty),
         FStar_Pervasives_Native.None, Pulse_Syntax.Tm_UVar n)
        ->
        if l.Pulse_Syntax.fv_name = Pulse_Reflection_Util.reveal_lid
        then FStar_Pervasives_Native.Some (u, ty, (Pulse_Syntax.Tm_UVar n))
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let (is_reveal : Pulse_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = Pulse_Syntax.leftmost_head_and_args t in
    match uu___ with
    | (hd, uu___1) ->
        (match hd with
         | Pulse_Syntax.Tm_UInst (l, uu___2::[]) ->
             l.Pulse_Syntax.fv_name = Pulse_Reflection_Util.reveal_lid
         | uu___2 -> false)
let rec (match_typ :
  Pulse_Syntax.term ->
    Pulse_Syntax.term ->
      (Pulse_Syntax.term * Pulse_Syntax.term) Prims.list ->
        ((Pulse_Syntax.term * Pulse_Syntax.term) Prims.list, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun t1 ->
           fun t2 ->
             fun uv_sols ->
               match ((is_reveal_uvar t1), (is_reveal t2)) with
               | (FStar_Pervasives_Native.Some (u, ty, t), false) ->
                   Obj.magic
                     (Obj.repr
                        (check_valid_solution t
                           (Pulse_Typing.mk_hide u ty t2) uv_sols))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (match (t1, t2) with
                         | (Pulse_Syntax.Tm_UVar n, uu___1) ->
                             Obj.repr (check_valid_solution t1 t2 uv_sols)
                         | (uu___1, Pulse_Syntax.Tm_UVar uu___2) ->
                             Obj.repr
                               (FStar_Tactics_Derived.fail
                                  "match_typ: t2 is a uvar")
                         | (Pulse_Syntax.Tm_PureApp (head1, arg_qual1, arg1),
                            Pulse_Syntax.Tm_PureApp (head2, arg_qual2, arg2))
                             ->
                             Obj.repr
                               (if arg_qual1 = arg_qual2
                                then
                                  Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Inference.fst"
                                          (Prims.of_int (73))
                                          (Prims.of_int (25))
                                          (Prims.of_int (73))
                                          (Prims.of_int (54)))
                                       (FStar_Range.mk_range
                                          "Pulse.Checker.Inference.fst"
                                          (Prims.of_int (74))
                                          (Prims.of_int (11))
                                          (Prims.of_int (74))
                                          (Prims.of_int (38)))
                                       (Obj.magic
                                          (match_typ head1 head2 uv_sols))
                                       (fun uu___1 ->
                                          (fun uv_sols1 ->
                                             Obj.magic
                                               (match_typ arg1 arg2 uv_sols1))
                                            uu___1))
                                else
                                  Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> uv_sols)))
                         | (Pulse_Syntax.Tm_Pure t11, Pulse_Syntax.Tm_Pure
                            t21) -> Obj.repr (match_typ t11 t21 uv_sols)
                         | (uu___1, uu___2) ->
                             Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> uv_sols))))) uu___2 uu___1
          uu___
let rec (atomic_vprop_has_uvar : Pulse_Syntax.term -> Prims.bool) =
  fun t ->
    match t with
    | Pulse_Syntax.Tm_UVar uu___ -> true
    | Pulse_Syntax.Tm_PureApp (head, uu___, arg) ->
        (atomic_vprop_has_uvar head) || (atomic_vprop_has_uvar arg)
    | Pulse_Syntax.Tm_Pure arg -> atomic_vprop_has_uvar arg
    | Pulse_Syntax.Tm_Emp -> false
    | uu___ -> false
let rec (atomic_vprops_may_match :
  Pulse_Syntax.term -> Pulse_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      if
        (FStar_Pervasives_Native.uu___is_Some (is_reveal_uvar t1)) &&
          (Prims.op_Negation (is_reveal t2))
      then true
      else
        (match (t1, t2) with
         | (Pulse_Syntax.Tm_UVar uu___1, uu___2) -> true
         | (Pulse_Syntax.Tm_PureApp (head1, q1, arg1),
            Pulse_Syntax.Tm_PureApp (head2, q2, arg2)) ->
             ((atomic_vprops_may_match head1 head2) && (q1 = q2)) &&
               (atomic_vprops_may_match arg1 arg2)
         | (Pulse_Syntax.Tm_Pure x, Pulse_Syntax.Tm_Pure y) ->
             atomic_vprops_may_match x y
         | (uu___1, uu___2) -> Pulse_Syntax.eq_tm t1 t2)
let (infer_one_atomic_vprop :
  Pulse_Syntax.term ->
    Pulse_Syntax.term Prims.list ->
      (Pulse_Syntax.term * Pulse_Syntax.term) Prims.list ->
        ((Pulse_Syntax.term * Pulse_Syntax.term) Prims.list, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun t ->
           fun ctxt ->
             fun uv_sols ->
               if atomic_vprop_has_uvar t
               then
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                            (Prims.of_int (109)) (Prims.of_int (24))
                            (Prims.of_int (109)) (Prims.of_int (95)))
                         (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                            (Prims.of_int (113)) (Prims.of_int (4))
                            (Prims.of_int (123)) (Prims.of_int (16)))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               FStar_List_Tot_Base.filter
                                 (fun ctxt_vp ->
                                    atomic_vprops_may_match t ctxt_vp) ctxt))
                         (fun uu___ ->
                            (fun matching_ctxt ->
                               if
                                 (FStar_List_Tot_Base.length matching_ctxt) =
                                   Prims.int_one
                               then
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Inference.fst"
                                            (Prims.of_int (119))
                                            (Prims.of_int (20))
                                            (Prims.of_int (119))
                                            (Prims.of_int (67)))
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Inference.fst"
                                            (Prims.of_int (119))
                                            (Prims.of_int (10))
                                            (Prims.of_int (119))
                                            (Prims.of_int (17)))
                                         (Obj.magic
                                            (match_typ t
                                               (FStar_List_Tot_Base.hd
                                                  matching_ctxt) uv_sols))
                                         (fun uv_sols1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___ -> uv_sols1))))
                               else
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 -> uv_sols)))) uu___)))
               else
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 -> uv_sols)))) uu___2 uu___1 uu___
let (union_ranges :
  Pulse_Syntax.range ->
    Pulse_Syntax.range ->
      (Pulse_Syntax.range, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun r0 ->
         fun r1 ->
           Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> r0)))
        uu___1 uu___
let (with_range :
  Pulse_Syntax.st_term' -> Pulse_Syntax.range -> Pulse_Syntax.st_term) =
  fun t -> fun r -> { Pulse_Syntax.term1 = t; Pulse_Syntax.range = r }
let rec (rebuild_head :
  Pulse_Syntax.term ->
    Pulse_Syntax.term Prims.list ->
      (Pulse_Syntax.term * Pulse_Syntax.term) Prims.list ->
        Pulse_Syntax.range ->
          (Pulse_Syntax.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun head ->
    fun uvs ->
      fun uv_sols ->
        fun r ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
               (Prims.of_int (132)) (Prims.of_int (15)) (Prims.of_int (132))
               (Prims.of_int (18)))
            (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
               (Prims.of_int (131)) (Prims.of_int (46)) (Prims.of_int (142))
               (Prims.of_int (40)))
            (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> uvs))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | hd::tl ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "Pulse.Checker.Inference.fst"
                              (Prims.of_int (133)) (Prims.of_int (13))
                              (Prims.of_int (133)) (Prims.of_int (63)))
                           (FStar_Range.mk_range
                              "Pulse.Checker.Inference.fst"
                              (Prims.of_int (134)) (Prims.of_int (2))
                              (Prims.of_int (142)) (Prims.of_int (40)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 FStar_List_Tot_Base.find
                                   (fun uu___2 ->
                                      match uu___2 with
                                      | (t1, uu___3) ->
                                          Pulse_Syntax.eq_tm t1 hd) uv_sols))
                           (fun uu___1 ->
                              (fun ropt ->
                                 match ropt with
                                 | FStar_Pervasives_Native.None ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Derived.fail
                                             "inference failed in building head"))
                                 | FStar_Pervasives_Native.Some (uu___1, t2)
                                     ->
                                     Obj.magic
                                       (Obj.repr
                                          (match tl with
                                           | [] ->
                                               Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       with_range
                                                         (Pulse_Syntax.Tm_STApp
                                                            {
                                                              Pulse_Syntax.head
                                                                = head;
                                                              Pulse_Syntax.arg_qual
                                                                =
                                                                (FStar_Pervasives_Native.Some
                                                                   Pulse_Syntax.Implicit);
                                                              Pulse_Syntax.arg
                                                                = t2
                                                            }) r))
                                           | uu___2 ->
                                               Obj.repr
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Inference.fst"
                                                       (Prims.of_int (141))
                                                       (Prims.of_int (21))
                                                       (Prims.of_int (141))
                                                       (Prims.of_int (55)))
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Inference.fst"
                                                       (Prims.of_int (142))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (142))
                                                       (Prims.of_int (40)))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          Pulse_Syntax.Tm_PureApp
                                                            (head,
                                                              (FStar_Pervasives_Native.Some
                                                                 Pulse_Syntax.Implicit),
                                                              t2)))
                                                    (fun uu___3 ->
                                                       (fun app_node ->
                                                          Obj.magic
                                                            (rebuild_head
                                                               app_node tl
                                                               uv_sols r))
                                                         uu___3))))) uu___1)))
                 uu___)
let (try_inst_uvs_in_goal :
  Pulse_Syntax.term ->
    Pulse_Syntax.vprop ->
      ((Pulse_Syntax.term * Pulse_Syntax.term) Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun ctxt ->
    fun goal ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
           (Prims.of_int (147)) (Prims.of_int (18)) (Prims.of_int (147))
           (Prims.of_int (20)))
        (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
           (Prims.of_int (147)) (Prims.of_int (23)) (Prims.of_int (157))
           (Prims.of_int (11)))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> []))
        (fun uu___ ->
           (fun uv_sols ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                      (Prims.of_int (148)) (Prims.of_int (20))
                      (Prims.of_int (148)) (Prims.of_int (38)))
                   (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                      (Prims.of_int (148)) (Prims.of_int (41))
                      (Prims.of_int (157)) (Prims.of_int (11)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Checker_Framing.vprop_as_list goal))
                   (fun uu___ ->
                      (fun goal_list ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Inference.fst"
                                 (Prims.of_int (149)) (Prims.of_int (20))
                                 (Prims.of_int (149)) (Prims.of_int (38)))
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Inference.fst"
                                 (Prims.of_int (149)) (Prims.of_int (41))
                                 (Prims.of_int (157)) (Prims.of_int (11)))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ ->
                                    Pulse_Checker_Framing.vprop_as_list ctxt))
                              (fun uu___ ->
                                 (fun ctxt_list ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Inference.fst"
                                            (Prims.of_int (151))
                                            (Prims.of_int (6))
                                            (Prims.of_int (155))
                                            (Prims.of_int (17)))
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Inference.fst"
                                            (Prims.of_int (150))
                                            (Prims.of_int (8))
                                            (Prims.of_int (150))
                                            (Prims.of_int (15)))
                                         (Obj.magic
                                            (FStar_Tactics_Util.fold_left
                                               (fun uv_sols1 ->
                                                  fun goal_vprop ->
                                                    infer_one_atomic_vprop
                                                      goal_vprop ctxt_list
                                                      uv_sols1) uv_sols
                                               goal_list))
                                         (fun uv_sols1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___ -> uv_sols1))))
                                   uu___))) uu___))) uu___)
let (print_solutions :
  (Pulse_Syntax.term * Pulse_Syntax.term) Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun l ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
         (Prims.of_int (162)) (Prims.of_int (6)) (Prims.of_int (167))
         (Prims.of_int (10)))
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
         (Prims.of_int (161)) (Prims.of_int (4)) (Prims.of_int (167))
         (Prims.of_int (10)))
      (Obj.magic
         (FStar_Tactics_Util.map
            (fun uu___ ->
               match uu___ with
               | (u, t) ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (166)) (Prims.of_int (23))
                        (Prims.of_int (166)) (Prims.of_int (43)))
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (164)) (Prims.of_int (10))
                        (Prims.of_int (166)) (Prims.of_int (43)))
                     (Obj.magic (Pulse_Syntax_Printer.term_to_string t))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (164)) (Prims.of_int (10))
                                   (Prims.of_int (166)) (Prims.of_int (43)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (164)) (Prims.of_int (10))
                                   (Prims.of_int (166)) (Prims.of_int (43)))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Inference.fst"
                                         (Prims.of_int (165))
                                         (Prims.of_int (23))
                                         (Prims.of_int (165))
                                         (Prims.of_int (43)))
                                      (FStar_Range.mk_range
                                         "FStar.Printf.fst"
                                         (Prims.of_int (121))
                                         (Prims.of_int (8))
                                         (Prims.of_int (123))
                                         (Prims.of_int (44)))
                                      (Obj.magic
                                         (Pulse_Syntax_Printer.term_to_string
                                            u))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 ->
                                              fun x ->
                                                Prims.strcat
                                                  (Prims.strcat ""
                                                     (Prims.strcat uu___2
                                                        " := "))
                                                  (Prims.strcat x "")))))
                                (fun uu___2 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> uu___2 uu___1)))) uu___1))
            l))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_String.concat "\n" uu___))
let (infer :
  Pulse_Syntax.term ->
    Pulse_Syntax.term ->
      Pulse_Syntax.term ->
        Pulse_Syntax.range ->
          (Pulse_Syntax.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun head ->
    fun t_head ->
      fun ctxt_pre ->
        fun r ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
               (Prims.of_int (176)) (Prims.of_int (16)) (Prims.of_int (182))
               (Prims.of_int (46)))
            (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
               (Prims.of_int (174)) (Prims.of_int (19)) (Prims.of_int (200))
               (Prims.of_int (5)))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                     (Prims.of_int (177)) (Prims.of_int (20))
                     (Prims.of_int (177)) (Prims.of_int (36)))
                  (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                     (Prims.of_int (176)) (Prims.of_int (16))
                     (Prims.of_int (182)) (Prims.of_int (46)))
                  (Obj.magic (gen_uvars t_head))
                  (fun uu___ ->
                     match uu___ with
                     | (uvs, comp) ->
                         (match comp with
                          | Pulse_Syntax.C_ST st_comp ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   (uvs, (st_comp.Pulse_Syntax.pre)))
                          | Pulse_Syntax.C_STAtomic (uu___1, st_comp) ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   (uvs, (st_comp.Pulse_Syntax.pre)))
                          | Pulse_Syntax.C_STGhost (uu___1, st_comp) ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   (uvs, (st_comp.Pulse_Syntax.pre)))
                          | uu___1 ->
                              FStar_Tactics_Derived.fail
                                "infer:unexpected comp type"))))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | (uvs, pre) ->
                      if (FStar_List_Tot_Base.length uvs) = Prims.int_zero
                      then
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Derived.fail
                                "Inference did not find anything to infer"))
                      else
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (195)) (Prims.of_int (18))
                                   (Prims.of_int (195)) (Prims.of_int (51)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (195)) (Prims.of_int (54))
                                   (Prims.of_int (199)) (Prims.of_int (8)))
                                (Obj.magic
                                   (try_inst_uvs_in_goal ctxt_pre pre))
                                (fun uu___2 ->
                                   (fun uv_sols ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Inference.fst"
                                              (Prims.of_int (197))
                                              (Prims.of_int (15))
                                              (Prims.of_int (197))
                                              (Prims.of_int (46)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Inference.fst"
                                              (Prims.of_int (197))
                                              (Prims.of_int (8))
                                              (Prims.of_int (197))
                                              (Prims.of_int (12)))
                                           (Obj.magic
                                              (rebuild_head head uvs uv_sols
                                                 r))
                                           (fun head1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 -> head1))))
                                     uu___2)))) uu___)
let (find_solution :
  (Pulse_Syntax.term * Pulse_Syntax.term) Prims.list ->
    Prims.int -> Pulse_Syntax.term FStar_Pervasives_Native.option)
  =
  fun sol ->
    fun uv ->
      let r =
        FStar_List_Tot_Base.find
          (fun uu___ ->
             match uu___ with
             | (u, t) ->
                 (match u with
                  | Pulse_Syntax.Tm_UVar u1 -> u1 = uv
                  | uu___1 -> false)) sol in
      match r with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu___, t) ->
          FStar_Pervasives_Native.Some t
let rec (apply_solution :
  (Pulse_Syntax.term * Pulse_Syntax.term) Prims.list ->
    Pulse_Syntax.term -> Pulse_Syntax.term)
  =
  fun sol ->
    fun t ->
      match t with
      | Pulse_Syntax.Tm_BVar uu___ -> t
      | Pulse_Syntax.Tm_Var uu___ -> t
      | Pulse_Syntax.Tm_FVar uu___ -> t
      | Pulse_Syntax.Tm_UInst (uu___, uu___1) -> t
      | Pulse_Syntax.Tm_Constant uu___ -> t
      | Pulse_Syntax.Tm_Emp -> t
      | Pulse_Syntax.Tm_VProp -> t
      | Pulse_Syntax.Tm_Inames -> t
      | Pulse_Syntax.Tm_EmpInames -> t
      | Pulse_Syntax.Tm_Type uu___ -> t
      | Pulse_Syntax.Tm_Unknown -> t
      | Pulse_Syntax.Tm_UVar uv ->
          (match find_solution sol uv with
           | FStar_Pervasives_Native.None -> t
           | FStar_Pervasives_Native.Some t1 -> t1)
      | Pulse_Syntax.Tm_Refine (b, t1) ->
          Pulse_Syntax.Tm_Refine
            ((apply_solution_binder sol b), (apply_solution sol t1))
      | Pulse_Syntax.Tm_PureApp (head, q, arg) ->
          Pulse_Syntax.Tm_PureApp
            ((apply_solution sol head), q, (apply_solution sol arg))
      | Pulse_Syntax.Tm_Let (t1, e1, e2) ->
          Pulse_Syntax.Tm_Let
            ((apply_solution sol t1), (apply_solution sol e1),
              (apply_solution sol e2))
      | Pulse_Syntax.Tm_Pure p -> Pulse_Syntax.Tm_Pure (apply_solution sol p)
      | Pulse_Syntax.Tm_Star (l, r) ->
          Pulse_Syntax.Tm_Star
            ((apply_solution sol l), (apply_solution sol r))
      | Pulse_Syntax.Tm_ExistsSL (u, t1, body, se) ->
          Pulse_Syntax.Tm_ExistsSL
            (u, (apply_solution sol t1), (apply_solution sol body), se)
      | Pulse_Syntax.Tm_ForallSL (u, t1, body) ->
          Pulse_Syntax.Tm_ForallSL
            (u, (apply_solution sol t1), (apply_solution sol body))
      | Pulse_Syntax.Tm_Arrow (b, q, body) ->
          Pulse_Syntax.Tm_Arrow
            ((apply_solution_binder sol b), q,
              (apply_solution_comp sol body))
      | Pulse_Syntax.Tm_FStar t1 -> Pulse_Syntax.Tm_FStar t1
and (apply_solution_binder :
  (Pulse_Syntax.term * Pulse_Syntax.term) Prims.list ->
    Pulse_Syntax.binder -> Pulse_Syntax.binder)
  =
  fun sol ->
    fun b ->
      {
        Pulse_Syntax.binder_ty =
          (apply_solution sol b.Pulse_Syntax.binder_ty);
        Pulse_Syntax.binder_ppname = (b.Pulse_Syntax.binder_ppname)
      }
and (apply_solution_comp :
  (Pulse_Syntax.term * Pulse_Syntax.term) Prims.list ->
    Pulse_Syntax.comp -> Pulse_Syntax.comp)
  =
  fun sol ->
    fun c ->
      match c with
      | Pulse_Syntax.C_Tot t -> Pulse_Syntax.C_Tot (apply_solution sol t)
      | uu___ -> c
let rec (contains_uvar : Pulse_Syntax.term -> Prims.bool) =
  fun t ->
    match t with
    | Pulse_Syntax.Tm_BVar uu___ -> false
    | Pulse_Syntax.Tm_Var uu___ -> false
    | Pulse_Syntax.Tm_FVar uu___ -> false
    | Pulse_Syntax.Tm_UInst (uu___, uu___1) -> false
    | Pulse_Syntax.Tm_Constant uu___ -> false
    | Pulse_Syntax.Tm_Emp -> false
    | Pulse_Syntax.Tm_VProp -> false
    | Pulse_Syntax.Tm_Inames -> false
    | Pulse_Syntax.Tm_EmpInames -> false
    | Pulse_Syntax.Tm_Type uu___ -> false
    | Pulse_Syntax.Tm_Unknown -> false
    | Pulse_Syntax.Tm_UVar uu___ -> true
    | Pulse_Syntax.Tm_Refine (b, t1) ->
        (contains_uvar_binder b) || (contains_uvar t1)
    | Pulse_Syntax.Tm_PureApp (head, q, arg) ->
        (contains_uvar head) || (contains_uvar arg)
    | Pulse_Syntax.Tm_Let (t1, e1, e2) ->
        ((contains_uvar t1) || (contains_uvar e1)) || (contains_uvar e2)
    | Pulse_Syntax.Tm_Pure p -> contains_uvar p
    | Pulse_Syntax.Tm_Star (l, r) -> (contains_uvar l) || (contains_uvar r)
    | Pulse_Syntax.Tm_ExistsSL (u, t1, body, se) ->
        (contains_uvar t1) || (contains_uvar body)
    | Pulse_Syntax.Tm_ForallSL (u, t1, body) ->
        (contains_uvar t1) || (contains_uvar body)
    | Pulse_Syntax.Tm_Arrow (b, q, body) ->
        (contains_uvar_binder b) || (contains_uvar_comp body)
    | Pulse_Syntax.Tm_FStar t1 -> false
and (contains_uvar_binder : Pulse_Syntax.binder -> Prims.bool) =
  fun b -> contains_uvar b.Pulse_Syntax.binder_ty
and (contains_uvar_comp : Pulse_Syntax.comp -> Prims.bool) =
  fun c ->
    match c with | Pulse_Syntax.C_Tot t -> contains_uvar t | uu___ -> true
let (try_unify :
  Pulse_Syntax.term ->
    Pulse_Syntax.term ->
      ((Pulse_Syntax.term * Pulse_Syntax.term) Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  = fun l -> fun r -> match_typ l r []