open Prims
type uvar_id = Prims.nat
let (uvar_id_to_string : uvar_id -> Prims.string) =
  fun n -> Prims.strcat "?u_" (Prims.strcat (Prims.string_of_int n) "")
let (embedded_uvar_lid : Prims.string Prims.list) =
  ["__pulse_embedded_uvar__"]
let (is_uvar :
  Pulse_Syntax_Base.term -> uvar_id FStar_Pervasives_Native.option) =
  fun t ->
    match Pulse_Syntax_Pure.is_fvar t with
    | FStar_Pervasives_Native.Some (l, u::[]) ->
        if l = embedded_uvar_lid
        then
          (match FStar_Reflection_Builtins.inspect_universe u with
           | FStar_Reflection_Data.Uv_BVar n ->
               FStar_Pervasives_Native.Some n
           | uu___ -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let (wrap_nat_to_uvar : Prims.nat -> Pulse_Syntax_Base.term) =
  fun n ->
    Pulse_Syntax_Base.Tm_FStar
      ((FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_UInst
             ((FStar_Reflection_Builtins.pack_fv embedded_uvar_lid),
               [FStar_Reflection_Builtins.pack_universe
                  (FStar_Reflection_Data.Uv_BVar n)]))), FStar_Range.range_0)
let (gen_uvar :
  unit ->
    ((uvar_id * Pulse_Syntax_Base.term), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst" (Prims.of_int (38))
         (Prims.of_int (10)) (Prims.of_int (38)) (Prims.of_int (20)))
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst" (Prims.of_int (40))
         (Prims.of_int (2)) (Prims.of_int (40)) (Prims.of_int (23)))
      (Obj.magic (FStar_Tactics_Builtins.fresh ()))
      (fun n ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> (n, (wrap_nat_to_uvar n))))
let rec (gen_uvars :
  Pulse_Syntax_Base.term ->
    ((uvar_id Prims.list * Pulse_Syntax_Base.comp), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t_head ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst" (Prims.of_int (43))
         (Prims.of_int (13)) (Prims.of_int (43)) (Prims.of_int (28)))
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst" (Prims.of_int (44))
         (Prims.of_int (2)) (Prims.of_int (59)) (Prims.of_int (60)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> Pulse_Syntax_Pure.is_arrow t_head))
      (fun uu___ ->
         (fun ropt ->
            match ropt with
            | FStar_Pervasives_Native.Some
                (uu___, FStar_Pervasives_Native.Some
                 (Pulse_Syntax_Base.Implicit), c_rest)
                ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (46)) (Prims.of_int (16))
                        (Prims.of_int (46)) (Prims.of_int (27)))
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (45)) (Prims.of_int (39))
                        (Prims.of_int (56)) (Prims.of_int (3)))
                     (Obj.magic (gen_uvar ()))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           match uu___1 with
                           | (n, tm) ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Inference.fst"
                                       (Prims.of_int (47))
                                       (Prims.of_int (17))
                                       (Prims.of_int (47))
                                       (Prims.of_int (41)))
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Inference.fst"
                                       (Prims.of_int (48)) (Prims.of_int (4))
                                       (Prims.of_int (55))
                                       (Prims.of_int (25)))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          Pulse_Syntax_Naming.open_comp_with
                                            c_rest tm))
                                    (fun uu___2 ->
                                       (fun c_rest1 ->
                                          match c_rest1 with
                                          | Pulse_Syntax_Base.C_ST c ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         ([n], c_rest1))))
                                          | Pulse_Syntax_Base.C_STAtomic
                                              (uu___2, c) ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         ([n], c_rest1))))
                                          | Pulse_Syntax_Base.C_STGhost
                                              (uu___2, c) ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         ([n], c_rest1))))
                                          | Pulse_Syntax_Base.C_Tot t ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Inference.fst"
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (29))
                                                         (Prims.of_int (54))
                                                         (Prims.of_int (40)))
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Inference.fst"
                                                         (Prims.of_int (53))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (55))
                                                         (Prims.of_int (25)))
                                                      (Obj.magic
                                                         (gen_uvars t))
                                                      (fun uu___2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 ->
                                                              match uu___2
                                                              with
                                                              | (n_rest,
                                                                 comp_typ) ->
                                                                  ((n ::
                                                                    n_rest),
                                                                    comp_typ))))))
                                         uu___2))) uu___1))
            | uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (58)) (Prims.of_int (10))
                        (Prims.of_int (59)) (Prims.of_int (60)))
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (58)) (Prims.of_int (3))
                        (Prims.of_int (59)) (Prims.of_int (60)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "Pulse.Checker.Inference.fst"
                              (Prims.of_int (59)) (Prims.of_int (34))
                              (Prims.of_int (59)) (Prims.of_int (59)))
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))
                           (Obj.magic
                              (Pulse_Syntax_Printer.term_to_string t_head))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   Prims.strcat
                                     "gen_uvars: unexpected t_head: "
                                     (Prims.strcat uu___1 "")))))
                     (fun uu___1 -> FStar_Tactics_Derived.fail uu___1)))
           uu___)
let rec (check_valid_solution :
  uvar_id ->
    Pulse_Syntax_Base.term ->
      (uvar_id * Pulse_Syntax_Base.term) Prims.list ->
        ((uvar_id * Pulse_Syntax_Base.term) Prims.list, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun n ->
           fun t ->
             fun uv_sols ->
               match uv_sols with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> [(n, t)])))
               | (n', t')::tl ->
                   Obj.magic
                     (Obj.repr
                        (if n = n'
                         then
                           Obj.repr
                             (if Pulse_Syntax_Base.eq_tm t t'
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
                                   (Prims.of_int (70)) (Prims.of_int (19))
                                   (Prims.of_int (70)) (Prims.of_int (48)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (70)) (Prims.of_int (9))
                                   (Prims.of_int (70)) (Prims.of_int (48)))
                                (Obj.magic (check_valid_solution n t tl))
                                (fun uu___1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> (n', t') :: uu___1))))))
          uu___2 uu___1 uu___
let (uvar_index : Pulse_Syntax_Base.term -> uvar_id) =
  fun t -> FStar_Pervasives_Native.__proj__Some__item__v (is_uvar t)
let (is_reveal_uvar :
  Pulse_Syntax_Base.term ->
    (Pulse_Syntax_Base.universe * Pulse_Syntax_Base.term *
      Pulse_Syntax_Base.term) FStar_Pervasives_Native.option)
  =
  fun t ->
    match Pulse_Syntax_Pure.is_pure_app t with
    | FStar_Pervasives_Native.Some (hd, FStar_Pervasives_Native.None, arg) ->
        (match Pulse_Syntax_Pure.is_pure_app hd with
         | FStar_Pervasives_Native.Some
             (hd1, FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Implicit),
              ty)
             ->
             if FStar_Pervasives_Native.uu___is_Some (is_uvar arg)
             then
               (match Pulse_Syntax_Pure.is_fvar hd1 with
                | FStar_Pervasives_Native.Some (l, u::[]) ->
                    if l = Pulse_Reflection_Util.reveal_lid
                    then FStar_Pervasives_Native.Some (u, ty, arg)
                    else FStar_Pervasives_Native.None
                | uu___ -> FStar_Pervasives_Native.None)
             else FStar_Pervasives_Native.None
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (is_reveal : Pulse_Syntax_Base.term -> Prims.bool) =
  fun t ->
    match Pulse_Syntax_Pure.leftmost_head t with
    | FStar_Pervasives_Native.Some hd ->
        (match Pulse_Syntax_Pure.is_fvar hd with
         | FStar_Pervasives_Native.Some (l, uu___::[]) ->
             l = Pulse_Reflection_Util.reveal_lid
         | uu___ -> false)
    | uu___ -> false
let rec (match_typ :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      (uvar_id * Pulse_Syntax_Base.term) Prims.list ->
        ((uvar_id * Pulse_Syntax_Base.term) Prims.list, unit)
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
                        (check_valid_solution (uvar_index t)
                           (Pulse_Typing.mk_hide u ty t2) uv_sols))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (if FStar_Pervasives_Native.uu___is_Some (is_uvar t1)
                         then
                           Obj.repr
                             (check_valid_solution (uvar_index t1) t2 uv_sols)
                         else
                           Obj.repr
                             (if
                                FStar_Pervasives_Native.uu___is_Some
                                  (is_uvar t2)
                              then
                                Obj.repr
                                  (FStar_Tactics_Derived.fail
                                     "match_typ: t2 is a uvar")
                              else
                                Obj.repr
                                  (match (t1, t2) with
                                   | (Pulse_Syntax_Base.Tm_Pure t11,
                                      Pulse_Syntax_Base.Tm_Pure t21) ->
                                       Obj.repr (match_typ t11 t21 uv_sols)
                                   | (uu___3, uu___4) ->
                                       Obj.repr
                                         (match ((Pulse_Syntax_Pure.is_pure_app
                                                    t1),
                                                  (Pulse_Syntax_Pure.is_pure_app
                                                     t2))
                                          with
                                          | (FStar_Pervasives_Native.Some
                                             (head1, arg_qual1, arg1),
                                             FStar_Pervasives_Native.Some
                                             (head2, arg_qual2, arg2)) ->
                                              Obj.repr
                                                (if arg_qual1 = arg_qual2
                                                 then
                                                   Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Inference.fst"
                                                           (Prims.of_int (118))
                                                           (Prims.of_int (32))
                                                           (Prims.of_int (118))
                                                           (Prims.of_int (61)))
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Inference.fst"
                                                           (Prims.of_int (119))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (119))
                                                           (Prims.of_int (45)))
                                                        (Obj.magic
                                                           (match_typ head1
                                                              head2 uv_sols))
                                                        (fun uu___5 ->
                                                           (fun uv_sols1 ->
                                                              Obj.magic
                                                                (match_typ
                                                                   arg1 arg2
                                                                   uv_sols1))
                                                             uu___5))
                                                 else
                                                   Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___6 ->
                                                           uv_sols)))
                                          | (uu___5, uu___6) ->
                                              Obj.repr
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___7 -> uv_sols))))))))
          uu___2 uu___1 uu___
let rec (atomic_vprop_has_uvar : Pulse_Syntax_Base.term -> Prims.bool) =
  fun t ->
    if FStar_Pervasives_Native.uu___is_Some (is_uvar t)
    then true
    else
      (match t with
       | Pulse_Syntax_Base.Tm_Pure arg -> atomic_vprop_has_uvar arg
       | Pulse_Syntax_Base.Tm_Emp -> false
       | uu___1 ->
           (match Pulse_Syntax_Pure.is_pure_app t with
            | FStar_Pervasives_Native.Some (head, uu___2, arg) ->
                (atomic_vprop_has_uvar head) || (atomic_vprop_has_uvar arg)
            | uu___2 -> false))
let rec (atomic_vprops_may_match :
  Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      if
        (FStar_Pervasives_Native.uu___is_Some (is_reveal_uvar t1)) &&
          (Prims.op_Negation (is_reveal t2))
      then true
      else
        if FStar_Pervasives_Native.uu___is_Some (is_uvar t1)
        then true
        else
          (match (t1, t2) with
           | (Pulse_Syntax_Base.Tm_Pure x, Pulse_Syntax_Base.Tm_Pure y) ->
               atomic_vprops_may_match x y
           | (uu___2, uu___3) ->
               (match ((Pulse_Syntax_Pure.is_pure_app t1),
                        (Pulse_Syntax_Pure.is_pure_app t2))
                with
                | (FStar_Pervasives_Native.Some (head1, q1, arg1),
                   FStar_Pervasives_Native.Some (head2, q2, arg2)) ->
                    ((atomic_vprops_may_match head1 head2) && (q1 = q2)) &&
                      (atomic_vprops_may_match arg1 arg2)
                | (uu___4, uu___5) -> Pulse_Syntax_Base.eq_tm t1 t2))
let (infer_one_atomic_vprop :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term Prims.list ->
      (uvar_id * Pulse_Syntax_Base.term) Prims.list ->
        ((uvar_id * Pulse_Syntax_Base.term) Prims.list, unit)
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
                            (Prims.of_int (158)) (Prims.of_int (24))
                            (Prims.of_int (158)) (Prims.of_int (95)))
                         (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                            (Prims.of_int (162)) (Prims.of_int (4))
                            (Prims.of_int (172)) (Prims.of_int (16)))
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
                                            (Prims.of_int (168))
                                            (Prims.of_int (20))
                                            (Prims.of_int (168))
                                            (Prims.of_int (67)))
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Inference.fst"
                                            (Prims.of_int (169))
                                            (Prims.of_int (6))
                                            (Prims.of_int (171))
                                            (Prims.of_int (13)))
                                         (Obj.magic
                                            (match_typ t
                                               (FStar_List_Tot_Base.hd
                                                  matching_ctxt) uv_sols))
                                         (fun uu___ ->
                                            (fun uv_sols1 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Inference.fst"
                                                       (Prims.of_int (169))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (170))
                                                       (Prims.of_int (43)))
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Inference.fst"
                                                       (Prims.of_int (168))
                                                       (Prims.of_int (10))
                                                       (Prims.of_int (168))
                                                       (Prims.of_int (17)))
                                                    (Obj.magic
                                                       (FStar_Tactics_Builtins.print
                                                          (Prims.strcat
                                                             "post matching, uv_sols has "
                                                             (Prims.strcat
                                                                (Prims.string_of_int
                                                                   (FStar_List_Tot_Base.length
                                                                    uv_sols1))
                                                                " solutions\n"))))
                                                    (fun uu___ ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___1 ->
                                                            uv_sols1))))
                                              uu___)))
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
  Pulse_Syntax_Base.range ->
    Pulse_Syntax_Base.range ->
      (Pulse_Syntax_Base.range, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun r0 ->
         fun r1 ->
           Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> r0)))
        uu___1 uu___
let (with_range :
  Pulse_Syntax_Base.st_term' ->
    Pulse_Syntax_Base.range -> Pulse_Syntax_Base.st_term)
  =
  fun t ->
    fun r -> { Pulse_Syntax_Base.term1 = t; Pulse_Syntax_Base.range = r }
let rec (rebuild_head :
  Pulse_Syntax_Base.term ->
    uvar_id Prims.list ->
      (uvar_id * Pulse_Syntax_Base.term) Prims.list ->
        Pulse_Syntax_Base.range ->
          (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun head ->
    fun uvs ->
      fun uv_sols ->
        fun r ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
               (Prims.of_int (181)) (Prims.of_int (15)) (Prims.of_int (181))
               (Prims.of_int (18)))
            (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
               (Prims.of_int (180)) (Prims.of_int (46)) (Prims.of_int (194))
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
                              (Prims.of_int (182)) (Prims.of_int (13))
                              (Prims.of_int (182)) (Prims.of_int (59)))
                           (FStar_Range.mk_range
                              "Pulse.Checker.Inference.fst"
                              (Prims.of_int (183)) (Prims.of_int (2))
                              (Prims.of_int (194)) (Prims.of_int (40)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 FStar_List_Tot_Base.find
                                   (fun uu___2 ->
                                      match uu___2 with
                                      | (n1, uu___3) -> hd = n1) uv_sols))
                           (fun uu___1 ->
                              (fun ropt ->
                                 match ropt with
                                 | FStar_Pervasives_Native.None ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Derived.fail
                                             (Prims.strcat
                                                "inference failed in building head, no solution for "
                                                (Prims.strcat
                                                   (Prims.string_of_int hd)
                                                   "\n"))))
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
                                                         (Pulse_Syntax_Base.Tm_STApp
                                                            {
                                                              Pulse_Syntax_Base.head
                                                                = head;
                                                              Pulse_Syntax_Base.arg_qual
                                                                =
                                                                (FStar_Pervasives_Native.Some
                                                                   Pulse_Syntax_Base.Implicit);
                                                              Pulse_Syntax_Base.arg
                                                                = t2
                                                            }) r))
                                           | uu___2 ->
                                               Obj.repr
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Inference.fst"
                                                       (Prims.of_int (193))
                                                       (Prims.of_int (21))
                                                       (Prims.of_int (193))
                                                       (Prims.of_int (55)))
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Inference.fst"
                                                       (Prims.of_int (194))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (194))
                                                       (Prims.of_int (40)))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          Pulse_Syntax_Pure.tm_pureapp
                                                            head
                                                            (FStar_Pervasives_Native.Some
                                                               Pulse_Syntax_Base.Implicit)
                                                            t2))
                                                    (fun uu___3 ->
                                                       (fun app_node ->
                                                          Obj.magic
                                                            (rebuild_head
                                                               app_node tl
                                                               uv_sols r))
                                                         uu___3))))) uu___1)))
                 uu___)
let (try_inst_uvs_in_goal :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.vprop ->
      ((uvar_id * Pulse_Syntax_Base.term) Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun ctxt ->
    fun goal ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
           (Prims.of_int (199)) (Prims.of_int (18)) (Prims.of_int (199))
           (Prims.of_int (20)))
        (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
           (Prims.of_int (199)) (Prims.of_int (23)) (Prims.of_int (209))
           (Prims.of_int (11)))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> []))
        (fun uu___ ->
           (fun uv_sols ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                      (Prims.of_int (200)) (Prims.of_int (20))
                      (Prims.of_int (200)) (Prims.of_int (38)))
                   (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                      (Prims.of_int (200)) (Prims.of_int (41))
                      (Prims.of_int (209)) (Prims.of_int (11)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> Pulse_Checker_Framing.vprop_as_list goal))
                   (fun uu___ ->
                      (fun goal_list ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Inference.fst"
                                 (Prims.of_int (201)) (Prims.of_int (20))
                                 (Prims.of_int (201)) (Prims.of_int (38)))
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Inference.fst"
                                 (Prims.of_int (201)) (Prims.of_int (41))
                                 (Prims.of_int (209)) (Prims.of_int (11)))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ ->
                                    Pulse_Checker_Framing.vprop_as_list ctxt))
                              (fun uu___ ->
                                 (fun ctxt_list ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Inference.fst"
                                            (Prims.of_int (203))
                                            (Prims.of_int (6))
                                            (Prims.of_int (207))
                                            (Prims.of_int (17)))
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Inference.fst"
                                            (Prims.of_int (202))
                                            (Prims.of_int (8))
                                            (Prims.of_int (202))
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
  (uvar_id * Pulse_Syntax_Base.term) Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun l ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
         (Prims.of_int (214)) (Prims.of_int (6)) (Prims.of_int (219))
         (Prims.of_int (10)))
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
         (Prims.of_int (213)) (Prims.of_int (4)) (Prims.of_int (219))
         (Prims.of_int (10)))
      (Obj.magic
         (FStar_Tactics_Util.map
            (fun uu___ ->
               match uu___ with
               | (u, t) ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (218)) (Prims.of_int (23))
                        (Prims.of_int (218)) (Prims.of_int (43)))
                     (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                        (Prims.of_int (19)) (Prims.of_int (590))
                        (Prims.of_int (31)))
                     (Obj.magic (Pulse_Syntax_Printer.term_to_string t))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             Prims.strcat
                               (Prims.strcat ""
                                  (Prims.strcat (Prims.string_of_int u)
                                     " := ")) (Prims.strcat uu___1 "")))) l))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_String.concat "\n" uu___))
let (infer :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.range ->
          (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun head ->
    fun t_head ->
      fun ctxt_pre ->
        fun r ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
               (Prims.of_int (228)) (Prims.of_int (16)) (Prims.of_int (234))
               (Prims.of_int (46)))
            (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
               (Prims.of_int (226)) (Prims.of_int (19)) (Prims.of_int (251))
               (Prims.of_int (5)))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                     (Prims.of_int (229)) (Prims.of_int (20))
                     (Prims.of_int (229)) (Prims.of_int (36)))
                  (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                     (Prims.of_int (228)) (Prims.of_int (16))
                     (Prims.of_int (234)) (Prims.of_int (46)))
                  (Obj.magic (gen_uvars t_head))
                  (fun uu___ ->
                     match uu___ with
                     | (uvs, comp) ->
                         (match comp with
                          | Pulse_Syntax_Base.C_ST st_comp ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   (uvs, (st_comp.Pulse_Syntax_Base.pre)))
                          | Pulse_Syntax_Base.C_STAtomic (uu___1, st_comp) ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   (uvs, (st_comp.Pulse_Syntax_Base.pre)))
                          | Pulse_Syntax_Base.C_STGhost (uu___1, st_comp) ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   (uvs, (st_comp.Pulse_Syntax_Base.pre)))
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
                                   (Prims.of_int (246)) (Prims.of_int (18))
                                   (Prims.of_int (246)) (Prims.of_int (51)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (246)) (Prims.of_int (54))
                                   (Prims.of_int (250)) (Prims.of_int (8)))
                                (Obj.magic
                                   (try_inst_uvs_in_goal ctxt_pre pre))
                                (fun uu___2 ->
                                   (fun uv_sols ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Inference.fst"
                                              (Prims.of_int (248))
                                              (Prims.of_int (15))
                                              (Prims.of_int (248))
                                              (Prims.of_int (46)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Inference.fst"
                                              (Prims.of_int (248))
                                              (Prims.of_int (8))
                                              (Prims.of_int (248))
                                              (Prims.of_int (12)))
                                           (Obj.magic
                                              (rebuild_head head uvs uv_sols
                                                 r))
                                           (fun head1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 -> head1))))
                                     uu___2)))) uu___)
let (find_solution :
  (uvar_id * Pulse_Syntax_Base.term) Prims.list ->
    uvar_id -> Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun sol ->
    fun t ->
      let r =
        FStar_List_Tot_Base.find
          (fun uu___ -> match uu___ with | (u, uu___1) -> u = t) sol in
      match r with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu___, t1) ->
          FStar_Pervasives_Native.Some t1
let (solutions_to_string :
  (uvar_id * Pulse_Syntax_Base.term) Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun sol -> print_solutions sol
let rec (apply_solution :
  (uvar_id * Pulse_Syntax_Base.term) Prims.list ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  =
  fun sol ->
    fun t ->
      match t with
      | Pulse_Syntax_Base.Tm_Emp -> t
      | Pulse_Syntax_Base.Tm_VProp -> t
      | Pulse_Syntax_Base.Tm_Inames -> t
      | Pulse_Syntax_Base.Tm_EmpInames -> t
      | Pulse_Syntax_Base.Tm_Unknown -> t
      | Pulse_Syntax_Base.Tm_FStar (uu___, uu___1) ->
          if FStar_Pervasives_Native.uu___is_Some (is_uvar t)
          then
            let n = uvar_index t in
            (match find_solution sol n with
             | FStar_Pervasives_Native.None -> t
             | FStar_Pervasives_Native.Some t1 -> t1)
          else
            (match Pulse_Syntax_Pure.is_pure_app t with
             | FStar_Pervasives_Native.Some (head, q, arg) ->
                 Pulse_Syntax_Pure.tm_pureapp (apply_solution sol head) q
                   (apply_solution sol arg)
             | uu___3 -> t)
      | Pulse_Syntax_Base.Tm_Pure p ->
          Pulse_Syntax_Base.Tm_Pure (apply_solution sol p)
      | Pulse_Syntax_Base.Tm_Star (l, r) ->
          Pulse_Syntax_Base.Tm_Star
            ((apply_solution sol l), (apply_solution sol r))
      | Pulse_Syntax_Base.Tm_ExistsSL (u, t1, body, se) ->
          Pulse_Syntax_Base.Tm_ExistsSL
            (u, (apply_solution sol t1), (apply_solution sol body), se)
      | Pulse_Syntax_Base.Tm_ForallSL (u, t1, body) ->
          Pulse_Syntax_Base.Tm_ForallSL
            (u, (apply_solution sol t1), (apply_solution sol body))
let rec (contains_uvar : Pulse_Syntax_Base.term -> Prims.bool) =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_Emp -> false
    | Pulse_Syntax_Base.Tm_VProp -> false
    | Pulse_Syntax_Base.Tm_Inames -> false
    | Pulse_Syntax_Base.Tm_EmpInames -> false
    | Pulse_Syntax_Base.Tm_Unknown -> false
    | Pulse_Syntax_Base.Tm_Pure p -> contains_uvar p
    | Pulse_Syntax_Base.Tm_Star (l, r) ->
        (contains_uvar l) || (contains_uvar r)
    | Pulse_Syntax_Base.Tm_ExistsSL (u, t1, body, se) ->
        (contains_uvar t1) || (contains_uvar body)
    | Pulse_Syntax_Base.Tm_ForallSL (u, t1, body) ->
        (contains_uvar t1) || (contains_uvar body)
    | Pulse_Syntax_Base.Tm_FStar (uu___, uu___1) ->
        (FStar_Pervasives_Native.uu___is_Some (is_uvar t)) ||
          ((match Pulse_Syntax_Pure.is_pure_app t with
            | FStar_Pervasives_Native.Some (head, uu___2, arg) ->
                (contains_uvar head) || (contains_uvar arg)
            | uu___2 -> false))
let (try_unify :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term ->
      ((uvar_id * Pulse_Syntax_Base.term) Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  = fun l -> fun r -> match_typ l r []