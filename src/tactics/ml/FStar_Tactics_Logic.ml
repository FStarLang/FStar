open Prims
let revert_squash s x = ()
let l_revert: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.revert
    (fun uu___56_56  ->
       FStar_Tactics_Builtins.apply
         (fun uu____59  ->
            fun s  -> FStar_Tactics_Effect.Success ((Obj.magic ()), s)))
let rec l_revert_all:
  FStar_Reflection_Syntax.binders -> Prims.unit FStar_Tactics_Effect.tactic =
  fun bs  ->
    match bs with
    | [] -> FStar_Tactics_Effect.return ()
    | uu____90::tl1 ->
        FStar_Tactics_Effect.bind l_revert
          (fun uu___57_101  -> l_revert_all tl1)
let fa_intro_lem f = ()
let forall_intro: FStar_Reflection_Types.binder FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
    (fun g  ->
       match FStar_Reflection_Formula.term_as_formula g with
       | FStar_Reflection_Formula.Forall (uu____185,uu____186) ->
           FStar_Tactics_Effect.bind
             (FStar_Tactics_Builtins.apply
                (fun uu____193  ->
                   fun s  -> FStar_Tactics_Effect.Success ((Obj.magic ()), s)))
             (fun uu___58_211  -> FStar_Tactics_Builtins.intro)
       | uu____212 -> FStar_Tactics_Derived.fail "not a forall")
let forall_intros:
  FStar_Reflection_Types.binder Prims.list FStar_Tactics_Effect.tactic =
  FStar_Tactics_Derived.repeat1 forall_intro
let split_lem sa sb = ()
let split: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
    (fun g  ->
       match FStar_Reflection_Formula.term_as_formula g with
       | FStar_Reflection_Formula.And (uu____282,uu____283) ->
           FStar_Tactics_Builtins.apply
             (fun uu____286  ->
                fun s  -> FStar_Tactics_Effect.Success ((Obj.magic ()), s))
       | uu____301 -> FStar_Tactics_Derived.fail "not a conjunction")
let imp_intro_lem f = ()
let implies_intro: FStar_Reflection_Types.binder FStar_Tactics_Effect.tactic
  =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
    (fun g  ->
       match FStar_Reflection_Formula.term_as_formula g with
       | FStar_Reflection_Formula.Implies (uu____379,uu____380) ->
           FStar_Tactics_Effect.bind
             (FStar_Tactics_Builtins.apply
                (fun uu____387  ->
                   fun s  -> FStar_Tactics_Effect.Success ((Obj.magic ()), s)))
             (fun uu___59_404  ->
                FStar_Tactics_Effect.bind FStar_Tactics_Builtins.intro
                  (fun b  -> FStar_Tactics_Effect.return b))
       | uu____412 -> FStar_Tactics_Derived.fail "not an implication")
let implies_intros:
  FStar_Reflection_Types.binder Prims.list FStar_Tactics_Effect.tactic =
  FStar_Tactics_Derived.repeat1 implies_intro
let rec visit:
  Prims.unit FStar_Tactics_Effect.tactic ->
    Prims.unit -> (Prims.unit,Prims.unit) FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun callback  ->
    fun uu____460  ->
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
                          (fun uu___60_553  -> FStar_Tactics_Effect.return ()))
                 | FStar_Reflection_Formula.Implies (p,q) ->
                     FStar_Tactics_Effect.bind implies_intro
                       (fun uu___61_566  ->
                          FStar_Tactics_Builtins.seq (visit callback)
                            l_revert)
                 | uu____579 ->
                     FStar_Tactics_Derived.or_else
                       FStar_Tactics_Builtins.trivial
                       (FStar_Tactics_Builtins.smt ())))) ()
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
                   | None  ->
                       FStar_Tactics_Derived.fail
                         "Not an equality implication"
                   | Some (uu____655,rhs) ->
                       FStar_Tactics_Effect.bind implies_intro
                         (fun eq_h  ->
                            FStar_Tactics_Effect.bind
                              (FStar_Tactics_Builtins.rewrite eq_h)
                              (fun uu___63_676  ->
                                 FStar_Tactics_Effect.bind
                                   FStar_Tactics_Builtins.clear
                                   (fun uu___62_679  ->
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
               if FStar_Reflection_Syntax.term_eq hd1 tm
               then FStar_Tactics_Builtins.trivial
               else FStar_Tactics_Effect.return ()
           | uu____756 ->
               FStar_Tactics_Effect.bind
                 (FStar_Tactics_Derived.destruct_equality_implication g)
                 (fun r  ->
                    match r with
                    | None  ->
                        FStar_Tactics_Derived.fail
                          "Not an equality implication"
                    | Some (uu____777,rhs) ->
                        FStar_Tactics_Effect.bind implies_intro
                          (fun eq_h  ->
                             FStar_Tactics_Effect.bind
                               (FStar_Tactics_Builtins.rewrite eq_h)
                               (fun uu___65_798  ->
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
      (fun uu____899  ->
         fun s  -> FStar_Tactics_Effect.Success ((Obj.magic ()), s))
      (fun v  ->
         FStar_Tactics_Effect.bind
           (FStar_Tactics_Builtins.apply
              (FStar_Tactics_Effect.return
                 (FStar_Reflection_Syntax.mk_app v [t])))
           (fun uu___66_933  ->
              FStar_Tactics_Effect.bind FStar_Tactics_Builtins.intro
                (fun b  ->
                   FStar_Tactics_Effect.return
                     (FStar_Reflection_Syntax.pack
                        (FStar_Reflection_Data.Tv_Var b)))))
let or_ind o l r = ()
let cases_or:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic =
  fun o  ->
    FStar_Tactics_Effect.bind
      (fun uu____1025  ->
         fun s  -> FStar_Tactics_Effect.Success ((Obj.magic ()), s))
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
      (fun uu____1128  ->
         fun s  -> FStar_Tactics_Effect.Success ((Obj.magic ()), s))
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
                         (fun uu___67_1182  -> FStar_Tactics_Builtins.clear))))
              (fun uu___68_1185  -> FStar_Tactics_Derived.idtac)))
let or_intro_1 uu____1215 = ()
let or_intro_2 uu____1245 = ()
let left: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.apply
    (fun uu____1255  ->
       fun s  -> FStar_Tactics_Effect.Success ((Obj.magic ()), s))
let right: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.apply
    (fun uu____1274  ->
       fun s  -> FStar_Tactics_Effect.Success ((Obj.magic ()), s))
let __and_elim p_and_q f = ()
let and_elim:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic =
  fun t  ->
    FStar_Tactics_Effect.bind
      (fun uu____1358  ->
         fun s  -> FStar_Tactics_Effect.Success ((Obj.magic ()), s))
      (fun ae  ->
         FStar_Tactics_Builtins.apply
           (FStar_Tactics_Effect.return
              (FStar_Reflection_Syntax.mk_app ae [t])))
*)
