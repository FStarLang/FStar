open Prims
let rec first :
  'a 'b .
    ('a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun l ->
           match l with
           | [] ->
               Obj.magic (Obj.repr (FStar_Tactics_Derived.fail "no cands"))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Derived.or_else (fun uu___ -> f x)
                       (fun uu___ -> first f xs)))) uu___1 uu___
let rec (tcresolve' :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun seen ->
    fun fuel ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
           (Prims.of_int (43)) (Prims.of_int (4)) (Prims.of_int (44))
           (Prims.of_int (26)))
        (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
           (Prims.of_int (45)) (Prims.of_int (4)) (Prims.of_int (50))
           (Prims.of_int (137)))
        (if fuel <= Prims.int_zero
         then FStar_Tactics_Derived.fail "out of fuel"
         else FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                      (Prims.of_int (45)) (Prims.of_int (4))
                      (Prims.of_int (45)) (Prims.of_int (42)))
                   (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                      (Prims.of_int (45)) (Prims.of_int (43))
                      (Prims.of_int (46)) (Prims.of_int (26)))
                   (Obj.magic
                      (FStar_Tactics_Derived.debug
                         (Prims.strcat "fuel = " (Prims.string_of_int fuel))))
                   (fun uu___1 ->
                      (fun uu___1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (46)) (Prims.of_int (12))
                                 (Prims.of_int (46)) (Prims.of_int (23)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (47)) (Prims.of_int (4))
                                 (Prims.of_int (50)) (Prims.of_int (137)))
                              (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                              (fun uu___2 ->
                                 (fun g ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (47))
                                            (Prims.of_int (4))
                                            (Prims.of_int (48))
                                            (Prims.of_int (17)))
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (48))
                                            (Prims.of_int (18))
                                            (Prims.of_int (49))
                                            (Prims.of_int (27)))
                                         (if
                                            FStar_List_Tot_Base.existsb
                                              (FStar_Reflection_Builtins.term_eq
                                                 g) seen
                                          then
                                            FStar_Tactics_Derived.fail "loop"
                                          else
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 -> ()))
                                         (fun uu___2 ->
                                            (fun uu___2 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (49))
                                                       (Prims.of_int (15))
                                                       (Prims.of_int (49))
                                                       (Prims.of_int (24)))
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (50))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (50))
                                                       (Prims.of_int (137)))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 -> g ::
                                                          seen))
                                                    (fun uu___3 ->
                                                       (fun seen1 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Derived.or_else
                                                               (local seen1
                                                                  fuel)
                                                               (fun uu___3 ->
                                                                  FStar_Tactics_Derived.or_else
                                                                    (
                                                                    global
                                                                    seen1
                                                                    fuel)
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (135)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (135)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (134)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    g))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "could not solve constraint: "
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    uu___5)))))
                                                         uu___3))) uu___2)))
                                   uu___2))) uu___1))) uu___)
and (local :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun seen ->
    fun fuel ->
      fun uu___ ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
             (Prims.of_int (52)) (Prims.of_int (13)) (Prims.of_int (52))
             (Prims.of_int (40)))
          (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
             (Prims.of_int (53)) (Prims.of_int (4)) (Prims.of_int (53))
             (Prims.of_int (74)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (52)) (Prims.of_int (28))
                   (Prims.of_int (52)) (Prims.of_int (40)))
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (52)) (Prims.of_int (13))
                   (Prims.of_int (52)) (Prims.of_int (40)))
                (Obj.magic (FStar_Tactics_Derived.cur_env ()))
                (fun uu___1 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        FStar_Reflection_Builtins.binders_of_env uu___1))))
          (fun uu___1 ->
             (fun bs ->
                Obj.magic
                  (first
                     (fun b ->
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Range.mk_range
                             "FStar.Tactics.Typeclasses.fst"
                             (Prims.of_int (53)) (Prims.of_int (38))
                             (Prims.of_int (53)) (Prims.of_int (70)))
                          (FStar_Range.mk_range
                             "FStar.Tactics.Typeclasses.fst"
                             (Prims.of_int (53)) (Prims.of_int (20))
                             (Prims.of_int (53)) (Prims.of_int (70)))
                          (Obj.magic
                             (FStar_Tactics_Builtins.pack
                                (FStar_Reflection_Data.Tv_Var
                                   (FStar_Reflection_Derived.bv_of_binder b))))
                          (fun uu___1 ->
                             (fun uu___1 ->
                                Obj.magic (trywith seen fuel uu___1)) uu___1))
                     bs)) uu___1)
and (global :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun seen ->
    fun fuel ->
      fun uu___ ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
             (Prims.of_int (55)) (Prims.of_int (16)) (Prims.of_int (55))
             (Prims.of_int (54)))
          (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
             (Prims.of_int (56)) (Prims.of_int (4)) (Prims.of_int (56))
             (Prims.of_int (65)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (55)) (Prims.of_int (42))
                   (Prims.of_int (55)) (Prims.of_int (54)))
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (55)) (Prims.of_int (16))
                   (Prims.of_int (55)) (Prims.of_int (54)))
                (Obj.magic (FStar_Tactics_Derived.cur_env ()))
                (fun uu___1 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        FStar_Reflection_Builtins.lookup_attr
                          (FStar_Reflection_Builtins.pack_ln
                             (FStar_Reflection_Data.Tv_FVar
                                (FStar_Reflection_Builtins.pack_fv
                                   ["FStar";
                                   "Tactics";
                                   "Typeclasses";
                                   "tcinstance"]))) uu___1))))
          (fun uu___1 ->
             (fun cands ->
                Obj.magic
                  (first
                     (fun fv ->
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Range.mk_range
                             "FStar.Tactics.Typeclasses.fst"
                             (Prims.of_int (56)) (Prims.of_int (39))
                             (Prims.of_int (56)) (Prims.of_int (58)))
                          (FStar_Range.mk_range
                             "FStar.Tactics.Typeclasses.fst"
                             (Prims.of_int (56)) (Prims.of_int (21))
                             (Prims.of_int (56)) (Prims.of_int (58)))
                          (Obj.magic
                             (FStar_Tactics_Builtins.pack
                                (FStar_Reflection_Data.Tv_FVar fv)))
                          (fun uu___1 ->
                             (fun uu___1 ->
                                Obj.magic (trywith seen fuel uu___1)) uu___1))
                     cands)) uu___1)
and (trywith :
  FStar_Reflection_Types.term Prims.list ->
    Prims.int ->
      FStar_Reflection_Types.term ->
        (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun seen ->
    fun fuel ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
             (Prims.of_int (58)) (Prims.of_int (4)) (Prims.of_int (58))
             (Prims.of_int (70)))
          (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
             (Prims.of_int (59)) (Prims.of_int (4)) (Prims.of_int (59))
             (Prims.of_int (73)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (58)) (Prims.of_int (10))
                   (Prims.of_int (58)) (Prims.of_int (70)))
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (58)) (Prims.of_int (4)) (Prims.of_int (58))
                   (Prims.of_int (70)))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (58)) (Prims.of_int (53))
                         (Prims.of_int (58)) (Prims.of_int (69)))
                      (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                         (Prims.of_int (19)) (Prims.of_int (590))
                         (Prims.of_int (31)))
                      (Obj.magic (FStar_Tactics_Builtins.term_to_string t))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              Prims.strcat
                                "Trying to apply hypothesis/instance: " uu___))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic (FStar_Tactics_Derived.debug uu___)) uu___)))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Derived.seq
                     (fun uu___1 -> FStar_Tactics_Derived.apply_noinst t)
                     (fun uu___1 -> tcresolve' seen (fuel - Prims.int_one))))
               uu___)
let rec (maybe_intros : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
         (Prims.of_int (62)) (Prims.of_int (10)) (Prims.of_int (62))
         (Prims.of_int (21)))
      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
         (Prims.of_int (63)) (Prims.of_int (2)) (Prims.of_int (67))
         (Prims.of_int (11))) (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
      (fun uu___1 ->
         (fun g ->
            match FStar_Reflection_Builtins.inspect_ln g with
            | FStar_Reflection_Data.Tv_Arrow (uu___1, uu___2) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                           (Prims.of_int (65)) (Prims.of_int (4))
                           (Prims.of_int (65)) (Prims.of_int (21)))
                        (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                           (Prims.of_int (66)) (Prims.of_int (4))
                           (Prims.of_int (66)) (Prims.of_int (19)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (65)) (Prims.of_int (11))
                                 (Prims.of_int (65)) (Prims.of_int (21)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (65)) (Prims.of_int (4))
                                 (Prims.of_int (65)) (Prims.of_int (21)))
                              (Obj.magic (FStar_Tactics_Builtins.intro ()))
                              (fun uu___3 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___4 -> ()))))
                        (fun uu___3 ->
                           (fun uu___3 -> Obj.magic (maybe_intros ())) uu___3)))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
           uu___1)
let (tcresolve : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
         (Prims.of_int (74)) (Prims.of_int (4)) (Prims.of_int (74))
         (Prims.of_int (19)))
      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
         (Prims.of_int (75)) (Prims.of_int (4)) (Prims.of_int (78))
         (Prims.of_int (18))) (Obj.magic (maybe_intros ()))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Derived.try_with
                 (fun uu___2 ->
                    match () with | () -> tcresolve' [] (Prims.of_int (16)))
                 (fun uu___2 ->
                    (fun uu___2 ->
                       match uu___2 with
                       | FStar_Tactics_Common.TacticFailure s ->
                           Obj.magic
                             (FStar_Tactics_Derived.fail
                                (Prims.strcat "Typeclass resolution failed: "
                                   s))
                       | e -> Obj.magic (FStar_Tactics_Effect.raise e))
                      uu___2))) uu___1)
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.Typeclasses.tcresolve"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
             (FStar_Tactics_Native.from_tactic_1 tcresolve)
             FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
             psc ncb args)
let solve : 'a . 'a -> 'a = fun ev -> ev
let rec (mk_abs :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun body ->
           match bs with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> body)))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (89)) (Prims.of_int (20))
                          (Prims.of_int (89)) (Prims.of_int (47)))
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (89)) (Prims.of_int (15))
                          (Prims.of_int (89)) (Prims.of_int (47)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (89)) (Prims.of_int (30))
                                (Prims.of_int (89)) (Prims.of_int (46)))
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (89)) (Prims.of_int (20))
                                (Prims.of_int (89)) (Prims.of_int (47)))
                             (Obj.magic (mk_abs bs1 body))
                             (fun uu___ ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     FStar_Reflection_Data.Tv_Abs (b, uu___)))))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic (FStar_Tactics_Builtins.pack uu___))
                            uu___)))) uu___1 uu___
let rec last : 'a . 'a Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun l ->
       match l with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Derived.fail "last: empty list"))
       | x::[] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x)))
       | uu___::xs -> Obj.magic (Obj.repr (last xs))) uu___
let (filter_no_method_binders :
  FStar_Reflection_Types.binders -> FStar_Reflection_Types.binders) =
  fun bs ->
    let has_no_method_attr b =
      let attrs =
        (FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.binder_attrs in
      let is_no_method t =
        match FStar_Reflection_Builtins.inspect_ln t with
        | FStar_Reflection_Data.Tv_FVar fv ->
            let n =
              FStar_Reflection_Derived.flatten_name
                (FStar_Reflection_Builtins.inspect_fv fv) in
            n = "FStar.Tactics.Typeclasses.no_method"
        | uu___ -> false in
      FStar_List_Tot_Base.existsb is_no_method attrs in
    FStar_List_Tot_Base.filter
      (fun b -> Prims.op_Negation (has_no_method_attr b)) bs
let (mk_class :
  Prims.string ->
    (FStar_Reflection_Data.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
         (Prims.of_int (116)) (Prims.of_int (13)) (Prims.of_int (116))
         (Prims.of_int (26)))
      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
         (Prims.of_int (116)) (Prims.of_int (29)) (Prims.of_int (117))
         (Prims.of_int (41)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_Builtins.explode_qn nm))
      (fun uu___ ->
         (fun ns ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                    (Prims.of_int (117)) (Prims.of_int (12))
                    (Prims.of_int (117)) (Prims.of_int (38)))
                 (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                    (Prims.of_int (118)) (Prims.of_int (4))
                    (Prims.of_int (206)) (Prims.of_int (35)))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (117)) (Prims.of_int (23))
                          (Prims.of_int (117)) (Prims.of_int (35)))
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (117)) (Prims.of_int (12))
                          (Prims.of_int (117)) (Prims.of_int (38)))
                       (Obj.magic (FStar_Tactics_Builtins.top_env ()))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Reflection_Builtins.lookup_typ uu___ ns))))
                 (fun uu___ ->
                    (fun r ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (118)) (Prims.of_int (4))
                               (Prims.of_int (118)) (Prims.of_int (19)))
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (118)) (Prims.of_int (20))
                               (Prims.of_int (119)) (Prims.of_int (22)))
                            (Obj.magic
                               (FStar_Tactics_Derived.guard
                                  (FStar_Pervasives_Native.uu___is_Some r)))
                            (fun uu___ ->
                               (fun uu___ ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Typeclasses.fst"
                                          (Prims.of_int (119))
                                          (Prims.of_int (18))
                                          (Prims.of_int (119))
                                          (Prims.of_int (19)))
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Typeclasses.fst"
                                          (Prims.of_int (118))
                                          (Prims.of_int (20))
                                          (Prims.of_int (119))
                                          (Prims.of_int (22)))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> r))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             match uu___1 with
                                             | FStar_Pervasives_Native.Some
                                                 se ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Typeclasses.fst"
                                                         (Prims.of_int (120))
                                                         (Prims.of_int (23))
                                                         (Prims.of_int (120))
                                                         (Prims.of_int (122)))
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Typeclasses.fst"
                                                         (Prims.of_int (120))
                                                         (Prims.of_int (125))
                                                         (Prims.of_int (121))
                                                         (Prims.of_int (33)))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___2 ->
                                                            FStar_List_Tot_Base.filter
                                                              (fun uu___3 ->
                                                                 match uu___3
                                                                 with
                                                                 | FStar_Reflection_Data.Inline_for_extraction
                                                                    -> true
                                                                 | FStar_Reflection_Data.NoExtract
                                                                    -> true
                                                                 | uu___4 ->
                                                                    false)
                                                              (FStar_Reflection_Builtins.sigelt_quals
                                                                 se)))
                                                      (fun uu___2 ->
                                                         (fun to_propagate ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (30)))
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (35)))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    FStar_Reflection_Builtins.inspect_sigelt
                                                                    se))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun sv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (28)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.guard
                                                                    (FStar_Reflection_Data.uu___is_Sg_Inductive
                                                                    sv)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    sv))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Sg_Inductive
                                                                    (name,
                                                                    us,
                                                                    params,
                                                                    ty,
                                                                    ctors) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (29)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (last
                                                                    name))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    ctor_name
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (33)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.guard
                                                                    ((FStar_List_Tot_Base.length
                                                                    ctors) =
                                                                    Prims.int_one)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ctors))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (c_name,
                                                                    ty1)::[]
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (131))
                                                                    (Prims.of_int (38)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_SyntaxHelpers.collect_arr_bs
                                                                    ty1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (bs, cod)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (28)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Reflection_Builtins.inspect_comp
                                                                    cod))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun r1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (26)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.guard
                                                                    (FStar_Reflection_Data.uu___is_C_Total
                                                                    r1)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (23)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (133))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (134))
                                                                    (Prims.of_int (26)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    r1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.C_Total
                                                                    cod1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "__proj__Mk"
                                                                    (Prims.strcat
                                                                    ctor_name
                                                                    "__item__")))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun base
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun b ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (43)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.name_of_binder
                                                                    b))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun s ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (49)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.cur_module
                                                                    ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun ns1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Reflection_Builtins.pack_fv
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ns1 
                                                                    [s])))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun sfv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (43)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.fresh_bv_named
                                                                    "d"))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun dbv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcresolve"]))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun tcr
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (19)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Reflection_Builtins.pack_binder
                                                                    {
                                                                    FStar_Reflection_Data.binder_bv
                                                                    = dbv;
                                                                    FStar_Reflection_Data.binder_qual
                                                                    =
                                                                    (FStar_Reflection_Data.Q_Meta
                                                                    tcr);
                                                                    FStar_Reflection_Data.binder_attrs
                                                                    = [];
                                                                    FStar_Reflection_Data.binder_sort
                                                                    = cod1
                                                                    }))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    tcdict ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (66)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (60)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.cur_module
                                                                    ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___9
                                                                    [
                                                                    Prims.strcat
                                                                    base s]))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    proj_name
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (20)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    proj_name))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun proj
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (20)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (62)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (159))
                                                                    (Prims.of_int (59)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.top_env
                                                                    ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Reflection_Builtins.lookup_typ
                                                                    uu___9
                                                                    proj_name))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "mk_class: proj not found?"))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (match 
                                                                    FStar_Reflection_Builtins.inspect_sigelt
                                                                    se1
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Sg_Let
                                                                    (uu___10,
                                                                    lbs) ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (57)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_SyntaxHelpers.lookup_lb_view
                                                                    lbs
                                                                    proj_name))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Reflection_Data.lb_fv
                                                                    = uu___13;
                                                                    FStar_Reflection_Data.lb_us
                                                                    = uu___14;
                                                                    FStar_Reflection_Data.lb_typ
                                                                    = typ;
                                                                    FStar_Reflection_Data.lb_def
                                                                    = uu___15;_}
                                                                    -> typ)))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "mk_class: proj not Sg_Let?"))))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    proj_ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (20)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (59)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_SyntaxHelpers.collect_arr_bs
                                                                    proj_ty))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    cod2) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (87)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (90)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_List_Tot_Base.splitAt
                                                                    (FStar_List_Tot_Base.length
                                                                    params)
                                                                    bs1))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (ps, bs2)
                                                                    ->
                                                                    (match bs2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "mk_class: impossible, no binders"))
                                                                    | 
                                                                    b1::bs'
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (28)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (FStar_Reflection_Builtins.inspect_binder
                                                                    b1).FStar_Reflection_Data.binder_bv))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun bv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (177))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (25)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Reflection_Builtins.pack_binder
                                                                    {
                                                                    FStar_Reflection_Data.binder_bv
                                                                    = bv;
                                                                    FStar_Reflection_Data.binder_qual
                                                                    =
                                                                    (FStar_Reflection_Data.Q_Meta
                                                                    tcr);
                                                                    FStar_Reflection_Data.binder_attrs
                                                                    = [];
                                                                    FStar_Reflection_Data.binder_sort
                                                                    =
                                                                    ((FStar_Reflection_Builtins.inspect_binder
                                                                    b1).FStar_Reflection_Data.binder_sort)
                                                                    }))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun b11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_SyntaxHelpers.mk_arr_curried
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ps (b11
                                                                    :: bs'))
                                                                    cod2))
                                                                    uu___11)))
                                                                    uu___11)))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun ty2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (46)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun b1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Reflection_Derived.binder_set_qual
                                                                    FStar_Reflection_Data.Q_Implicit
                                                                    b1)))
                                                                    uu___9)
                                                                    params))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___9
                                                                    [tcdict]))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun bs1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (67)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (68)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.binder_to_term
                                                                    tcdict))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    [uu___9]))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Reflection_Derived.mk_e_app
                                                                    proj
                                                                    uu___9))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (mk_abs
                                                                    bs1
                                                                    uu___9))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    (fun def
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Reflection_Builtins.set_sigelt_attrs
                                                                    (FStar_Reflection_Builtins.inspect_binder
                                                                    b).FStar_Reflection_Data.binder_attrs
                                                                    (FStar_Reflection_Builtins.set_sigelt_quals
                                                                    to_propagate
                                                                    (FStar_Reflection_Builtins.pack_sigelt
                                                                    (FStar_Reflection_Data.Sg_Let
                                                                    (false,
                                                                    [
                                                                    FStar_Reflection_Builtins.pack_lb
                                                                    {
                                                                    FStar_Reflection_Data.lb_fv
                                                                    = sfv;
                                                                    FStar_Reflection_Data.lb_us
                                                                    = us;
                                                                    FStar_Reflection_Data.lb_typ
                                                                    = ty2;
                                                                    FStar_Reflection_Data.lb_def
                                                                    = def
                                                                    }]))))))))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9))
                                                                    (filter_no_method_binders
                                                                    bs)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                           uu___2))) uu___1)))
                                 uu___))) uu___))) uu___)
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.Typeclasses.mk_class"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
             (FStar_Tactics_Native.from_tactic_1 mk_class)
             FStar_Syntax_Embeddings.e_string
             (FStar_Syntax_Embeddings.e_list
                FStar_Reflection_Embeddings.e_sigelt) psc ncb args)