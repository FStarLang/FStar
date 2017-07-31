open Prims
let revert_squash s x = ()
let l_revert: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.revert
    (fun uu___56_58  ->
       FStar_Tactics_Builtins.apply
         (FStar_Tactics_Derived.quote_lid
            ["FStar"; "Tactics"; "Logic"; "revert_squash"]))
let rec l_revert_all:
  FStar_Reflection_Data.binders -> Prims.unit FStar_Tactics_Effect.tactic =
  fun bs  ->
    match bs with
    | [] -> FStar_Tactics_Effect.return ()
    | uu____79::tl1 ->
        FStar_Tactics_Effect.bind l_revert
          (fun uu___57_91  -> l_revert_all tl1)
let fa_intro_lem f = ()
let forall_intro: FStar_Reflection_Types.binder FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
    (fun g  ->
       match FStar_Reflection_Formula.term_as_formula g with
       | FStar_Reflection_Formula.Forall (uu____179,uu____180) ->
           FStar_Tactics_Effect.bind
             (FStar_Tactics_Builtins.apply
                (FStar_Tactics_Derived.quote_lid
                   ["FStar"; "Tactics"; "Logic"; "fa_intro_lem"]))
             (fun uu___58_194  -> FStar_Tactics_Builtins.intro)
       | uu____195 -> FStar_Tactics_Derived.fail "not a forall")
let forall_intros:
  FStar_Reflection_Types.binder Prims.list FStar_Tactics_Effect.tactic =
  FStar_Tactics_Derived.repeat1 forall_intro
let split_lem sa sb = ()
let split: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
    (fun g  ->
       match FStar_Reflection_Formula.term_as_formula g with
       | FStar_Reflection_Formula.And (uu____267,uu____268) ->
           FStar_Tactics_Builtins.apply
             (FStar_Tactics_Derived.quote_lid
                ["FStar"; "Tactics"; "Logic"; "split_lem"])
       | uu____277 -> FStar_Tactics_Derived.fail "not a conjunction")
let imp_intro_lem f = ()
let implies_intro: FStar_Reflection_Types.binder FStar_Tactics_Effect.tactic
  =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
    (fun g  ->
       match FStar_Reflection_Formula.term_as_formula g with
       | FStar_Reflection_Formula.Implies (uu____357,uu____358) ->
           FStar_Tactics_Effect.bind
             (FStar_Tactics_Builtins.apply
                (FStar_Tactics_Derived.quote_lid
                   ["FStar"; "Tactics"; "Logic"; "imp_intro_lem"]))
             (fun uu___59_374  ->
                FStar_Tactics_Effect.bind FStar_Tactics_Builtins.intro
                  (fun b  -> FStar_Tactics_Effect.return b))
       | uu____383 -> FStar_Tactics_Derived.fail "not an implication")
let implies_intros:
  FStar_Reflection_Types.binder Prims.list FStar_Tactics_Effect.tactic =
  FStar_Tactics_Derived.repeat1 implies_intro
let rec visit:
  Prims.unit FStar_Tactics_Effect.tactic ->
    Prims.unit -> (Prims.unit,Prims.unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun callback  ->
    fun uu____434  ->
      FStar_Tactics_Derived.focus
        (FStar_Tactics_Derived.or_else callback
           (FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
              (fun g  ->
                 match FStar_Reflection_Formula.term_as_formula g with
                 | FStar_Reflection_Formula.Forall (b,phi) ->
                     FStar_Tactics_Effect.bind forall_intros
                       (fun binders  ->
                          FStar_Tactics_Builtins.seq (visit callback)
                            (l_revert_all binders))
                 | FStar_Reflection_Formula.And (p,q) ->
                     FStar_Tactics_Builtins.seq split
                       (FStar_Tactics_Effect.bind (visit callback)
                          (fun uu___60_530  -> FStar_Tactics_Effect.return ()))
                 | FStar_Reflection_Formula.Implies (p,q) ->
                     FStar_Tactics_Effect.bind implies_intro
                       (fun uu___61_544  ->
                          FStar_Tactics_Builtins.seq (visit callback)
                            l_revert)
                 | uu____557 ->
                     FStar_Tactics_Derived.or_else
                       FStar_Tactics_Builtins.trivial
                       (FStar_Tactics_Builtins.smt)))) ()
let rec simplify_eq_implication:
  Prims.unit -> (Prims.unit,Prims.unit) FStar_Tactics_Effect._dm4f_TAC_repr =
  fun u  ->
    FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_env
      (fun e  ->
         FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
           (fun g  ->
              FStar_Tactics_Effect.bind
                (FStar_Tactics_Derived.destruct_equality_implication g)
                (fun r  ->
                   match r with
                   | FStar_Pervasives_Native.None  ->
                       FStar_Tactics_Derived.fail
                         "Not an equality implication"
                   | FStar_Pervasives_Native.Some (uu____639,rhs) ->
                       FStar_Tactics_Effect.bind implies_intro
                         (fun eq_h  ->
                            FStar_Tactics_Effect.bind
                              (FStar_Tactics_Builtins.rewrite eq_h)
                              (fun uu___63_662  ->
                                 FStar_Tactics_Effect.bind
                                   FStar_Tactics_Builtins.clear
                                   (fun uu___62_666  ->
                                      visit simplify_eq_implication)))))) ()
let rewrite_all_equalities:
  Prims.unit ->
    (Prims.unit,(Prims.unit FStar_Tactics_Effect.__result,Obj.t)
                  Prims.l_Forall)
      FStar_Tactics_Effect._dm4f_TAC_repr
  = visit simplify_eq_implication
let rec unfold_definition_and_simplify_eq':
  FStar_Reflection_Types.term ->
    Prims.unit -> (Prims.unit,Prims.unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun tm  ->
    fun u  ->
      FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
        (fun g  ->
           match FStar_Reflection_Formula.term_as_formula g with
           | FStar_Reflection_Formula.App (hd1,arg) ->
               if FStar_Reflection_Basic.term_eq hd1 tm
               then FStar_Tactics_Builtins.trivial
               else FStar_Tactics_Effect.return ()
           | uu____752 ->
               FStar_Tactics_Effect.bind
                 (FStar_Tactics_Derived.destruct_equality_implication g)
                 (fun r  ->
                    match r with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Tactics_Derived.fail
                          "Not an equality implication"
                    | FStar_Pervasives_Native.Some (uu____774,rhs) ->
                        FStar_Tactics_Effect.bind implies_intro
                          (fun eq_h  ->
                             FStar_Tactics_Effect.bind
                               (FStar_Tactics_Builtins.rewrite eq_h)
                               (fun uu___65_797  ->
                                  FStar_Tactics_Effect.bind
                                    FStar_Tactics_Builtins.clear
                                    (fun uu___64_801  ->
                                       visit
                                         (unfold_definition_and_simplify_eq'
                                            tm)))))) ()
let unfold_definition_and_simplify_eq:
  FStar_Reflection_Types.term FStar_Tactics_Effect.tactic ->
    Prims.unit FStar_Tactics_Effect.tactic
  =
  fun tm  ->
    FStar_Tactics_Effect.bind tm
      (fun tm'  -> unfold_definition_and_simplify_eq' tm')
let vbind sq f = ()
let unsquash:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term FStar_Tactics_Effect.tactic
  =
  fun t  ->
    FStar_Tactics_Effect.bind
      (FStar_Tactics_Derived.quote_lid ["FStar"; "Tactics"; "Logic"; "vbind"])
      (fun v  ->
         FStar_Tactics_Effect.bind
           (FStar_Tactics_Builtins.apply
              (FStar_Tactics_Effect.return
                 (FStar_Reflection_Syntax.mk_app v [t])))
           (fun uu___66_922  ->
              FStar_Tactics_Effect.bind FStar_Tactics_Builtins.intro
                (fun b  ->
                   FStar_Tactics_Effect.return
                     (FStar_Reflection_Basic.pack
                        (FStar_Reflection_Data.Tv_Var b)))))
let squash_intro: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.apply
    (FStar_Tactics_Derived.quote_lid ["FStar"; "Squash"; "return_squash"])
let or_ind o l r = ()
let cases_or:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic =
  fun o  ->
    FStar_Tactics_Effect.bind
      (FStar_Tactics_Derived.quote_lid
         ["FStar"; "Tactics"; "Logic"; "or_ind"])
      (fun oi  ->
         FStar_Tactics_Builtins.apply
           (FStar_Tactics_Effect.return
              (FStar_Reflection_Syntax.mk_app oi [o])))
(*let bool_ind:
  Prims.bool ->
    Prims.unit ->
      ((Prims.bool,Prims.unit,Prims.unit) Prims.eq2,Obj.t) Prims.l_imp
        Prims.squash ->
        ((Prims.bool,Prims.unit,Prims.unit) Prims.eq2,Obj.t) Prims.l_imp
          Prims.squash -> Prims.unit
  = fun b  -> fun phi  -> fun l  -> fun r  -> ()
let cases_bool:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic =
  fun b  ->
    FStar_Tactics_Effect.bind
      (FStar_Tactics_Derived.quote_lid
         ["FStar"; "Tactics"; "Logic"; "bool_ind"])
      (fun bi  ->
         FStar_Tactics_Builtins.seq
           (FStar_Tactics_Builtins.apply
              (FStar_Tactics_Effect.return
                 (FStar_Reflection_Syntax.mk_app bi [b])))
           (FStar_Tactics_Effect.bind
              (FStar_Tactics_Builtins.trytac
                 (FStar_Tactics_Effect.bind implies_intro
                    (fun b1  ->
                       FStar_Tactics_Effect.bind
                         (FStar_Tactics_Builtins.rewrite b1)
                         (fun uu___67_1159  -> FStar_Tactics_Builtins.clear))))
              (fun uu___68_1163  -> FStar_Tactics_Derived.idtac)))
let or_intro_1 uu____1193 = ()
let or_intro_2 uu____1223 = ()
let left: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.apply
    (FStar_Tactics_Derived.quote_lid
       ["FStar"; "Tactics"; "Logic"; "or_intro_1"])
let right: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.apply
    (FStar_Tactics_Derived.quote_lid
       ["FStar"; "Tactics"; "Logic"; "or_intro_2"])
let __and_elim p_and_q f = ()
let and_elim:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic =
  fun t  ->
    FStar_Tactics_Effect.bind
      (FStar_Tactics_Derived.quote_lid
         ["FStar"; "Tactics"; "Logic"; "__and_elim"])
      (fun ae  ->
         FStar_Tactics_Builtins.apply
           (FStar_Tactics_Effect.return
              (FStar_Reflection_Syntax.mk_app ae [t])))*)
