open Prims
type uvar_id = Prims.nat
type uvar = (uvar_id * Pulse_Syntax_Base.ppname)
let (uvar_eq : uvar -> uvar -> Prims.bool) =
  fun u1 ->
    fun u2 ->
      (FStar_Pervasives_Native.fst u1) = (FStar_Pervasives_Native.fst u2)
type solution = (uvar * Pulse_Syntax_Base.term) Prims.list
let (uvar_to_string :
  uvar -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    match uu___ with
    | (num, pp) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
             (Prims.of_int (22)) (Prims.of_int (2)) (Prims.of_int (22))
             (Prims.of_int (54)))
          (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
             (Prims.of_int (22)) (Prims.of_int (2)) (Prims.of_int (22))
             (Prims.of_int (54)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                   (Prims.of_int (22)) (Prims.of_int (32))
                   (Prims.of_int (22)) (Prims.of_int (50)))
                (FStar_Range.mk_range "FStar.Printf.fst" (Prims.of_int (121))
                   (Prims.of_int (8)) (Prims.of_int (123))
                   (Prims.of_int (44)))
                (Obj.magic
                   (FStar_Tactics_Builtins.unseal pp.Pulse_Syntax_Base.name))
                (fun uu___1 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        fun x ->
                          Prims.strcat
                            (Prims.strcat "?" (Prims.strcat uu___1 "_"))
                            (Prims.strcat (Prims.string_of_int x) "")))))
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> uu___1 num))
let (range_of_uvar : uvar -> Pulse_Syntax_Base.range) =
  fun u -> (FStar_Pervasives_Native.snd u).Pulse_Syntax_Base.range
let (embedded_uvar_prefix : Prims.string) = "__pulse_embedded_uvar__"
let (is_uvar_r :
  FStar_Reflection_Types.term -> uvar FStar_Pervasives_Native.option) =
  fun t ->
    match FStar_Reflection_Builtins.inspect_ln t with
    | FStar_Reflection_Data.Tv_UInst (fv, u::[]) ->
        (match FStar_Reflection_Builtins.inspect_fv fv with
         | prefix::name::[] ->
             if prefix = embedded_uvar_prefix
             then
               (match FStar_Reflection_Builtins.inspect_universe u with
                | FStar_Reflection_Data.Uv_BVar n ->
                    FStar_Pervasives_Native.Some
                      (n,
                        (Pulse_Syntax_Base.mk_ppname (FStar_Sealed.seal name)
                           (FStar_Reflection_Builtins.range_of_term t)))
                | uu___ -> FStar_Pervasives_Native.None)
             else FStar_Pervasives_Native.None
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (is_uvar : Pulse_Syntax_Base.term -> uvar FStar_Pervasives_Native.option)
  =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_FStar (r, uu___) -> is_uvar_r r
    | uu___ -> FStar_Pervasives_Native.None
let (wrap_nat_to_uvar :
  Prims.string ->
    Pulse_Syntax_Base.range -> Prims.nat -> Pulse_Syntax_Base.term)
  =
  fun name ->
    fun r ->
      fun n ->
        let tm =
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_UInst
               ((FStar_Reflection_Builtins.pack_fv
                   [embedded_uvar_prefix; name]),
                 [FStar_Reflection_Builtins.pack_universe
                    (FStar_Reflection_Data.Uv_BVar n)])) in
        let tm1 = tm in Pulse_Syntax_Base.Tm_FStar (tm1, r)
let (gen_uvar :
  Pulse_Syntax_Base.ppname ->
    ((uvar * Pulse_Syntax_Base.term), unit) FStar_Tactics_Effect.tac_repr)
  =
  fun name ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst" (Prims.of_int (53))
         (Prims.of_int (10)) (Prims.of_int (53)) (Prims.of_int (20)))
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst" (Prims.of_int (54))
         (Prims.of_int (18)) (Prims.of_int (56)) (Prims.of_int (45)))
      (Obj.magic (FStar_Tactics_Builtins.fresh ()))
      (fun uu___ ->
         (fun n ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                    (Prims.of_int (55)) (Prims.of_int (11))
                    (Prims.of_int (55)) (Prims.of_int (29)))
                 (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                    (Prims.of_int (56)) (Prims.of_int (2))
                    (Prims.of_int (56)) (Prims.of_int (45)))
                 (Obj.magic
                    (FStar_Tactics_Builtins.unseal
                       name.Pulse_Syntax_Base.name))
                 (fun nm ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         ((n, name),
                           (wrap_nat_to_uvar nm name.Pulse_Syntax_Base.range
                              n)))))) uu___)
let rec (gen_uvars :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      ((uvar Prims.list * Pulse_Syntax_Base.comp), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t_head ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
           (Prims.of_int (59)) (Prims.of_int (13)) (Prims.of_int (59))
           (Prims.of_int (28)))
        (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
           (Prims.of_int (60)) (Prims.of_int (2)) (Prims.of_int (75))
           (Prims.of_int (60)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Pulse_Syntax_Pure.is_arrow t_head))
        (fun uu___ ->
           (fun ropt ->
              match ropt with
              | FStar_Pervasives_Native.Some
                  (b, FStar_Pervasives_Native.Some
                   (Pulse_Syntax_Base.Implicit), c_rest)
                  ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                          (Prims.of_int (62)) (Prims.of_int (16))
                          (Prims.of_int (62)) (Prims.of_int (40)))
                       (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                          (Prims.of_int (61)) (Prims.of_int (39))
                          (Prims.of_int (72)) (Prims.of_int (3)))
                       (Obj.magic
                          (gen_uvar b.Pulse_Syntax_Base.binder_ppname))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | (n, tm) ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Inference.fst"
                                         (Prims.of_int (63))
                                         (Prims.of_int (17))
                                         (Prims.of_int (63))
                                         (Prims.of_int (41)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Inference.fst"
                                         (Prims.of_int (64))
                                         (Prims.of_int (4))
                                         (Prims.of_int (71))
                                         (Prims.of_int (25)))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            Pulse_Syntax_Naming.open_comp_with
                                              c_rest tm))
                                      (fun uu___1 ->
                                         (fun c_rest1 ->
                                            match c_rest1 with
                                            | Pulse_Syntax_Base.C_ST c ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           ([n], c_rest1))))
                                            | Pulse_Syntax_Base.C_STAtomic
                                                (uu___1, c) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           ([n], c_rest1))))
                                            | Pulse_Syntax_Base.C_STGhost
                                                (uu___1, c) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           ([n], c_rest1))))
                                            | Pulse_Syntax_Base.C_Tot t ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Inference.fst"
                                                           (Prims.of_int (70))
                                                           (Prims.of_int (29))
                                                           (Prims.of_int (70))
                                                           (Prims.of_int (42)))
                                                        (FStar_Range.mk_range
                                                           "Pulse.Checker.Inference.fst"
                                                           (Prims.of_int (69))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (71))
                                                           (Prims.of_int (25)))
                                                        (Obj.magic
                                                           (gen_uvars g t))
                                                        (fun uu___1 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                match uu___1
                                                                with
                                                                | (n_rest,
                                                                   comp_typ)
                                                                    ->
                                                                    ((n ::
                                                                    n_rest),
                                                                    comp_typ))))))
                                           uu___1))) uu___))
              | uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                          (Prims.of_int (74)) (Prims.of_int (15))
                          (Prims.of_int (75)) (Prims.of_int (60)))
                       (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                          (Prims.of_int (74)) (Prims.of_int (3))
                          (Prims.of_int (75)) (Prims.of_int (60)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "Pulse.Checker.Inference.fst"
                                (Prims.of_int (75)) (Prims.of_int (34))
                                (Prims.of_int (75)) (Prims.of_int (59)))
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
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (Pulse_Typing_Env.fail g
                                  FStar_Pervasives_Native.None uu___1))
                            uu___1))) uu___)
let rec (check_valid_solution :
  Pulse_Typing_Env.env ->
    uvar ->
      Pulse_Syntax_Base.term ->
        solution -> (solution, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun n ->
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
                            (if uvar_eq n n'
                             then
                               Obj.repr
                                 (if Pulse_Syntax_Base.eq_tm t t'
                                  then
                                    Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___ -> uv_sols))
                                  else
                                    Obj.repr
                                      (Pulse_Typing_Env.fail g
                                         FStar_Pervasives_Native.None
                                         "check_valid_solution failed"))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Inference.fst"
                                       (Prims.of_int (86))
                                       (Prims.of_int (19))
                                       (Prims.of_int (86))
                                       (Prims.of_int (50)))
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Inference.fst"
                                       (Prims.of_int (86)) (Prims.of_int (9))
                                       (Prims.of_int (86))
                                       (Prims.of_int (50)))
                                    (Obj.magic
                                       (check_valid_solution g n t tl))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 -> (n', t') :: uu___1))))))
            uu___3 uu___2 uu___1 uu___
let (uvar_index : Pulse_Syntax_Base.term -> uvar) =
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
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        solution -> (solution, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun t1 ->
               fun t2 ->
                 fun uv_sols ->
                   match ((is_reveal_uvar t1), (is_reveal t2)) with
                   | (FStar_Pervasives_Native.Some (u, ty, t), false) ->
                       Obj.magic
                         (Obj.repr
                            (check_valid_solution g (uvar_index t)
                               (Pulse_Typing.mk_hide u ty t2) uv_sols))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (if
                               FStar_Pervasives_Native.uu___is_Some
                                 (is_uvar t1)
                             then
                               Obj.repr
                                 (check_valid_solution g (uvar_index t1) t2
                                    uv_sols)
                             else
                               Obj.repr
                                 (if
                                    FStar_Pervasives_Native.uu___is_Some
                                      (is_uvar t2)
                                  then
                                    Obj.repr
                                      (Pulse_Typing_Env.fail g
                                         FStar_Pervasives_Native.None
                                         "match_typ: t2 is a uvar")
                                  else
                                    Obj.repr
                                      (match (t1, t2) with
                                       | (Pulse_Syntax_Base.Tm_Pure t11,
                                          Pulse_Syntax_Base.Tm_Pure t21) ->
                                           Obj.repr
                                             (match_typ g t11 t21 uv_sols)
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
                                                               (Prims.of_int (134))
                                                               (Prims.of_int (32))
                                                               (Prims.of_int (134))
                                                               (Prims.of_int (63)))
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Inference.fst"
                                                               (Prims.of_int (135))
                                                               (Prims.of_int (18))
                                                               (Prims.of_int (135))
                                                               (Prims.of_int (47)))
                                                            (Obj.magic
                                                               (match_typ g
                                                                  head1 head2
                                                                  uv_sols))
                                                            (fun uu___5 ->
                                                               (fun uv_sols1
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    match_typ
                                                                    g arg1
                                                                    arg2
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
            uu___3 uu___2 uu___1 uu___
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
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term Prims.list ->
        solution -> (solution, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun g ->
             fun t ->
               fun ctxt ->
                 fun uv_sols ->
                   if atomic_vprop_has_uvar t
                   then
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "Pulse.Checker.Inference.fst"
                                (Prims.of_int (174)) (Prims.of_int (24))
                                (Prims.of_int (174)) (Prims.of_int (95)))
                             (FStar_Range.mk_range
                                "Pulse.Checker.Inference.fst"
                                (Prims.of_int (178)) (Prims.of_int (4))
                                (Prims.of_int (188)) (Prims.of_int (16)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   FStar_List_Tot_Base.filter
                                     (fun ctxt_vp ->
                                        atomic_vprops_may_match t ctxt_vp)
                                     ctxt))
                             (fun uu___ ->
                                (fun matching_ctxt ->
                                   if
                                     (FStar_List_Tot_Base.length
                                        matching_ctxt)
                                       = Prims.int_one
                                   then
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Inference.fst"
                                                (Prims.of_int (184))
                                                (Prims.of_int (20))
                                                (Prims.of_int (184))
                                                (Prims.of_int (69)))
                                             (FStar_Range.mk_range
                                                "Pulse.Checker.Inference.fst"
                                                (Prims.of_int (184))
                                                (Prims.of_int (10))
                                                (Prims.of_int (184))
                                                (Prims.of_int (17)))
                                             (Obj.magic
                                                (match_typ g t
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
                             (fun uu___1 -> uv_sols)))) uu___3 uu___2 uu___1
            uu___
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
    fun r -> { Pulse_Syntax_Base.term1 = t; Pulse_Syntax_Base.range1 = r }
let rec (rebuild_head :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      uvar Prims.list ->
        solution ->
          Pulse_Syntax_Base.range ->
            (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun head ->
      fun uvs ->
        fun uv_sols ->
          fun r ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                 (Prims.of_int (197)) (Prims.of_int (15))
                 (Prims.of_int (197)) (Prims.of_int (18)))
              (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                 (Prims.of_int (196)) (Prims.of_int (46))
                 (Prims.of_int (211)) (Prims.of_int (42)))
              (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> uvs))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | hd::tl ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "Pulse.Checker.Inference.fst"
                                (Prims.of_int (198)) (Prims.of_int (13))
                                (Prims.of_int (198)) (Prims.of_int (65)))
                             (FStar_Range.mk_range
                                "Pulse.Checker.Inference.fst"
                                (Prims.of_int (199)) (Prims.of_int (2))
                                (Prims.of_int (211)) (Prims.of_int (42)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   FStar_List_Tot_Base.find
                                     (fun uu___2 ->
                                        match uu___2 with
                                        | (n1, uu___3) -> uvar_eq hd n1)
                                     uv_sols))
                             (fun uu___1 ->
                                (fun ropt ->
                                   match ropt with
                                   | FStar_Pervasives_Native.None ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Inference.fst"
                                                  (Prims.of_int (202))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (204))
                                                  (Prims.of_int (34)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Inference.fst"
                                                  (Prims.of_int (201))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (204))
                                                  (Prims.of_int (34)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Inference.fst"
                                                        (Prims.of_int (204))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (204))
                                                        (Prims.of_int (33)))
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (590))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (590))
                                                        (Prims.of_int (31)))
                                                     (Obj.magic
                                                        (uvar_to_string hd))
                                                     (fun uu___1 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             Prims.strcat
                                                               "inference failed in building head, no solution for "
                                                               (Prims.strcat
                                                                  uu___1 "\n")))))
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     Obj.magic
                                                       (Pulse_Typing_Env.fail
                                                          g
                                                          (FStar_Pervasives_Native.Some
                                                             r) uu___1))
                                                    uu___1)))
                                   | FStar_Pervasives_Native.Some
                                       (uu___1, t2) ->
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
                                                         (Prims.of_int (210))
                                                         (Prims.of_int (21))
                                                         (Prims.of_int (210))
                                                         (Prims.of_int (55)))
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Inference.fst"
                                                         (Prims.of_int (211))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (211))
                                                         (Prims.of_int (42)))
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
                                                              (rebuild_head g
                                                                 app_node tl
                                                                 uv_sols r))
                                                           uu___3))))) uu___1)))
                   uu___)
let (print_solutions :
  solution -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun l ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
         (Prims.of_int (217)) (Prims.of_int (6)) (Prims.of_int (222))
         (Prims.of_int (10)))
      (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
         (Prims.of_int (216)) (Prims.of_int (4)) (Prims.of_int (222))
         (Prims.of_int (10)))
      (Obj.magic
         (FStar_Tactics_Util.map
            (fun uu___ ->
               match uu___ with
               | (u, t) ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (221)) (Prims.of_int (23))
                        (Prims.of_int (221)) (Prims.of_int (43)))
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (219)) (Prims.of_int (10))
                        (Prims.of_int (221)) (Prims.of_int (43)))
                     (Obj.magic (Pulse_Syntax_Printer.term_to_string t))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (219)) (Prims.of_int (10))
                                   (Prims.of_int (221)) (Prims.of_int (43)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (219)) (Prims.of_int (10))
                                   (Prims.of_int (221)) (Prims.of_int (43)))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Inference.fst"
                                         (Prims.of_int (220))
                                         (Prims.of_int (23))
                                         (Prims.of_int (220))
                                         (Prims.of_int (41)))
                                      (FStar_Range.mk_range
                                         "FStar.Printf.fst"
                                         (Prims.of_int (121))
                                         (Prims.of_int (8))
                                         (Prims.of_int (123))
                                         (Prims.of_int (44)))
                                      (Obj.magic (uvar_to_string u))
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
let (find_solution :
  solution -> uvar -> Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun sol ->
    fun t ->
      let r =
        FStar_List_Tot_Base.find
          (fun uu___ -> match uu___ with | (u, uu___1) -> uvar_eq u t) sol in
      match r with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu___, t1) ->
          FStar_Pervasives_Native.Some t1
let (try_inst_uvs_in_goal :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.vprop ->
        (solution, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun goal ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
             (Prims.of_int (236)) (Prims.of_int (18)) (Prims.of_int (236))
             (Prims.of_int (20)))
          (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
             (Prims.of_int (236)) (Prims.of_int (23)) (Prims.of_int (247))
             (Prims.of_int (8)))
          (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> []))
          (fun uu___ ->
             (fun uv_sols ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (237)) (Prims.of_int (20))
                        (Prims.of_int (237)) (Prims.of_int (38)))
                     (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                        (Prims.of_int (237)) (Prims.of_int (41))
                        (Prims.of_int (247)) (Prims.of_int (8)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           Pulse_Checker_VPropEquiv.vprop_as_list goal))
                     (fun uu___ ->
                        (fun goal_list ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (238)) (Prims.of_int (20))
                                   (Prims.of_int (238)) (Prims.of_int (38)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Inference.fst"
                                   (Prims.of_int (238)) (Prims.of_int (41))
                                   (Prims.of_int (247)) (Prims.of_int (8)))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      Pulse_Checker_VPropEquiv.vprop_as_list
                                        ctxt))
                                (fun uu___ ->
                                   (fun ctxt_list ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Inference.fst"
                                              (Prims.of_int (240))
                                              (Prims.of_int (6))
                                              (Prims.of_int (244))
                                              (Prims.of_int (17)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Inference.fst"
                                              (Prims.of_int (239))
                                              (Prims.of_int (8))
                                              (Prims.of_int (239))
                                              (Prims.of_int (15)))
                                           (Obj.magic
                                              (FStar_Tactics_Util.fold_left
                                                 (fun uv_sols1 ->
                                                    fun goal_vprop ->
                                                      infer_one_atomic_vprop
                                                        g goal_vprop
                                                        ctxt_list uv_sols1)
                                                 uv_sols goal_list))
                                           (fun uv_sols1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___ -> uv_sols1))))
                                     uu___))) uu___))) uu___)
let (infer :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.range ->
            (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun head ->
      fun t_head ->
        fun ctxt_pre ->
          fun r ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                 (Prims.of_int (258)) (Prims.of_int (10))
                 (Prims.of_int (258)) (Prims.of_int (34)))
              (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                 (Prims.of_int (258)) (Prims.of_int (37))
                 (Prims.of_int (282)) (Prims.of_int (5)))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Pulse_Typing_Env.push_context g "infer" r))
              (fun uu___ ->
                 (fun g1 ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                            (Prims.of_int (259)) (Prims.of_int (16))
                            (Prims.of_int (265)) (Prims.of_int (55)))
                         (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                            (Prims.of_int (258)) (Prims.of_int (37))
                            (Prims.of_int (282)) (Prims.of_int (5)))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Inference.fst"
                                  (Prims.of_int (260)) (Prims.of_int (20))
                                  (Prims.of_int (260)) (Prims.of_int (38)))
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Inference.fst"
                                  (Prims.of_int (259)) (Prims.of_int (16))
                                  (Prims.of_int (265)) (Prims.of_int (55)))
                               (Obj.magic (gen_uvars g1 t_head))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     match uu___ with
                                     | (uvs, comp) ->
                                         (match comp with
                                          | Pulse_Syntax_Base.C_ST st_comp ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___1 ->
                                                         (uvs,
                                                           (st_comp.Pulse_Syntax_Base.pre)))))
                                          | Pulse_Syntax_Base.C_STAtomic
                                              (uu___1, st_comp) ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         (uvs,
                                                           (st_comp.Pulse_Syntax_Base.pre)))))
                                          | Pulse_Syntax_Base.C_STGhost
                                              (uu___1, st_comp) ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         (uvs,
                                                           (st_comp.Pulse_Syntax_Base.pre)))))
                                          | uu___1 ->
                                              Obj.magic
                                                (Obj.repr
                                                   (Pulse_Typing_Env.fail g1
                                                      (FStar_Pervasives_Native.Some
                                                         r)
                                                      "infer:unexpected comp type"))))
                                    uu___)))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | (uvs, pre) ->
                                   if
                                     (FStar_List_Tot_Base.length uvs) =
                                       Prims.int_zero
                                   then
                                     Obj.magic
                                       (Pulse_Typing_Env.fail g1
                                          (FStar_Pervasives_Native.Some r)
                                          "Inference did not find anything to infer")
                                   else
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Inference.fst"
                                             (Prims.of_int (277))
                                             (Prims.of_int (18))
                                             (Prims.of_int (277))
                                             (Prims.of_int (53)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Inference.fst"
                                             (Prims.of_int (277))
                                             (Prims.of_int (56))
                                             (Prims.of_int (281))
                                             (Prims.of_int (8)))
                                          (Obj.magic
                                             (try_inst_uvs_in_goal g1
                                                ctxt_pre pre))
                                          (fun uu___2 ->
                                             (fun uv_sols ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Inference.fst"
                                                        (Prims.of_int (279))
                                                        (Prims.of_int (15))
                                                        (Prims.of_int (279))
                                                        (Prims.of_int (48)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Inference.fst"
                                                        (Prims.of_int (279))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (279))
                                                        (Prims.of_int (12)))
                                                     (Obj.magic
                                                        (rebuild_head g1 head
                                                           uvs uv_sols r))
                                                     (fun head1 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             head1)))) uu___2)))
                              uu___))) uu___)
let (solutions_to_string :
  solution -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun sol -> print_solutions sol
let rec (apply_sol :
  solution -> FStar_Reflection_Types.term -> FStar_Reflection_Types.term) =
  fun sol ->
    fun t ->
      match is_uvar_r t with
      | FStar_Pervasives_Native.None ->
          (match FStar_Reflection_Builtins.inspect_ln t with
           | FStar_Reflection_Data.Tv_App (hd, (arg, q)) ->
               let hd1 = apply_sol sol hd in
               let arg1 = apply_sol sol arg in
               FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_App (hd1, (arg1, q)))
           | uu___ -> t)
      | FStar_Pervasives_Native.Some n ->
          (match find_solution sol n with
           | FStar_Pervasives_Native.None -> t
           | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Tm_FStar
               (t1, uu___)) -> t1
           | FStar_Pervasives_Native.Some t1 ->
               Pulse_Elaborate_Pure.elab_term t1)
let rec (apply_solution :
  solution -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term) =
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
      | Pulse_Syntax_Base.Tm_ExistsSL (u, b, body) ->
          Pulse_Syntax_Base.Tm_ExistsSL
            (u,
              {
                Pulse_Syntax_Base.binder_ty =
                  (apply_solution sol b.Pulse_Syntax_Base.binder_ty);
                Pulse_Syntax_Base.binder_ppname =
                  (b.Pulse_Syntax_Base.binder_ppname)
              }, (apply_solution sol body))
      | Pulse_Syntax_Base.Tm_ForallSL (u, b, body) ->
          Pulse_Syntax_Base.Tm_ForallSL
            (u,
              {
                Pulse_Syntax_Base.binder_ty =
                  (apply_solution sol b.Pulse_Syntax_Base.binder_ty);
                Pulse_Syntax_Base.binder_ppname =
                  (b.Pulse_Syntax_Base.binder_ppname)
              }, (apply_solution sol body))
let rec (contains_uvar_r : FStar_Reflection_Types.term -> Prims.bool) =
  fun t ->
    (FStar_Pervasives_Native.uu___is_Some (is_uvar_r t)) ||
      (match FStar_Reflection_Builtins.inspect_ln t with
       | FStar_Reflection_Data.Tv_App (hd, (arg, uu___)) ->
           (contains_uvar_r hd) || (contains_uvar_r arg)
       | uu___ -> false)
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
    | Pulse_Syntax_Base.Tm_ExistsSL (u, t1, body) ->
        (contains_uvar t1.Pulse_Syntax_Base.binder_ty) ||
          (contains_uvar body)
    | Pulse_Syntax_Base.Tm_ForallSL (u, t1, body) ->
        (contains_uvar t1.Pulse_Syntax_Base.binder_ty) ||
          (contains_uvar body)
    | Pulse_Syntax_Base.Tm_FStar (t1, uu___) -> contains_uvar_r t1
let (try_unify :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (solution, unit) FStar_Tactics_Effect.tac_repr)
  = fun g -> fun l -> fun r -> match_typ g l r []
let (is_eq2 :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term * FStar_Reflection_Types.term)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = FStar_Reflection_Derived.collect_app_ln t in
    match uu___ with
    | (head, args) ->
        (match ((FStar_Reflection_Builtins.inspect_ln head), args) with
         | (FStar_Reflection_Data.Tv_FVar fv,
            uu___1::(a1, uu___2)::(a2, uu___3)::[]) ->
             let l = FStar_Reflection_Builtins.inspect_fv fv in
             if
               (l = ["Pulse"; "Steel"; "Wrapper"; "eq2_prop"]) ||
                 (l = ["Prims"; "eq2"])
             then FStar_Pervasives_Native.Some (a1, a2)
             else FStar_Pervasives_Native.None
         | (FStar_Reflection_Data.Tv_UInst (fv, uu___1),
            uu___2::(a1, uu___3)::(a2, uu___4)::[]) ->
             let l = FStar_Reflection_Builtins.inspect_fv fv in
             if
               (l = ["Pulse"; "Steel"; "Wrapper"; "eq2_prop"]) ||
                 (l = ["Prims"; "eq2"])
             then FStar_Pervasives_Native.Some (a1, a2)
             else FStar_Pervasives_Native.None
         | uu___1 -> FStar_Pervasives_Native.None)
let (try_solve_pure_equalities :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term -> (solution, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun p ->
           let rec aux sol t =
             FStar_Tactics_Effect.tac_bind
               (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                  (Prims.of_int (395)) (Prims.of_int (12))
                  (Prims.of_int (395)) (Prims.of_int (27)))
               (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                  (Prims.of_int (395)) (Prims.of_int (30))
                  (Prims.of_int (412)) (Prims.of_int (16)))
               (FStar_Tactics_Effect.lift_div_tac
                  (fun uu___ -> apply_sol sol t))
               (fun uu___ ->
                  (fun t1 ->
                     Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                             (Prims.of_int (396)) (Prims.of_int (12))
                             (Prims.of_int (396)) (Prims.of_int (33)))
                          (FStar_Range.mk_range "Pulse.Checker.Inference.fst"
                             (Prims.of_int (396)) (Prims.of_int (36))
                             (Prims.of_int (412)) (Prims.of_int (16)))
                          (Obj.magic
                             (FStar_Reflection_Formula.term_as_formula' t1))
                          (fun uu___ ->
                             (fun f ->
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Inference.fst"
                                        (Prims.of_int (398))
                                        (Prims.of_int (6))
                                        (Prims.of_int (404))
                                        (Prims.of_int (14)))
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Inference.fst"
                                        (Prims.of_int (396))
                                        (Prims.of_int (8))
                                        (Prims.of_int (396))
                                        (Prims.of_int (9)))
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           fun uu___1 ->
                                             fun uu___ ->
                                               (fun uu___ ->
                                                  fun t0 ->
                                                    fun t11 ->
                                                      if
                                                        (contains_uvar_r t0)
                                                          ||
                                                          (contains_uvar_r
                                                             t11)
                                                      then
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Inference.fst"
                                                                   (Prims.of_int (402))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (402))
                                                                   (Prims.of_int (87)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Inference.fst"
                                                                   (Prims.of_int (402))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (402))
                                                                   (Prims.of_int (93)))
                                                                (Obj.magic
                                                                   (try_unify
                                                                    g
                                                                    (Pulse_Syntax_Base.Tm_FStar
                                                                    (t0,
                                                                    FStar_Range.range_0))
                                                                    (Pulse_Syntax_Base.Tm_FStar
                                                                    (t11,
                                                                    FStar_Range.range_0))))
                                                                (fun uu___1
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___1
                                                                    sol))))
                                                      else
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___2
                                                                   -> sol))))
                                                 uu___2 uu___1 uu___))
                                     (fun uu___ ->
                                        (fun handle_eq ->
                                           match f with
                                           | FStar_Reflection_Formula.Comp
                                               (FStar_Reflection_Formula.Eq
                                                uu___, t0, t11)
                                               ->
                                               Obj.magic
                                                 (Obj.repr (handle_eq t0 t11))
                                           | FStar_Reflection_Formula.And
                                               (t0, t11) ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Inference.fst"
                                                          (Prims.of_int (408))
                                                          (Prims.of_int (23))
                                                          (Prims.of_int (408))
                                                          (Prims.of_int (35)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Checker.Inference.fst"
                                                          (Prims.of_int (408))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (408))
                                                          (Prims.of_int (38)))
                                                       (Obj.magic
                                                          (aux sol t0))
                                                       (fun uu___ ->
                                                          (fun uu___ ->
                                                             Obj.magic
                                                               (aux uu___ t11))
                                                            uu___)))
                                           | uu___ ->
                                               Obj.magic
                                                 (Obj.repr
                                                    (match is_eq2 t1 with
                                                     | FStar_Pervasives_Native.Some
                                                         (t0, t11) ->
                                                         Obj.repr
                                                           (handle_eq t0 t11)
                                                     | uu___1 ->
                                                         Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 sol)))))
                                          uu___))) uu___))) uu___) in
           match p with
           | Pulse_Syntax_Base.Tm_FStar (t, r) ->
               Obj.magic (Obj.repr (aux [] t))
           | uu___ -> Obj.magic (Obj.repr [])) uu___1 uu___