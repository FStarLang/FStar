open Prims
let revert_squash:
  'Aa 'Ab . ('Aa,'Ab) Prims.l_Forall Prims.squash -> 'Aa -> 'Ab Prims.squash
  = fun s  -> fun x  -> ()
let l_revert: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.revert
    (fun uu___58_64  ->
       FStar_Tactics_Builtins.apply
         (FStar_Tactics_Derived.quote_lid
            ["FStar"; "Tactics"; "Logic"; "revert_squash"]))
let rec l_revert_all:
  FStar_Reflection_Types.binders -> Prims.unit FStar_Tactics_Effect.tactic =
  fun bs  ->
    match bs with
    | [] -> FStar_Tactics_Effect.return ()
    | uu____77::tl1 ->
        FStar_Tactics_Effect.bind l_revert
          (fun uu___59_82  -> l_revert_all tl1)
let fa_intro_lem:
  'Aa 'Ab .
    ('Aa -> 'Ab Prims.squash) -> ('Aa,'Ab) Prims.l_Forall Prims.squash
  = fun f  -> ()
let forall_intro: FStar_Reflection_Types.binder FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
    (fun g  ->
       match FStar_Reflection_Formula.term_as_formula g with
       | FStar_Reflection_Formula.Forall (uu____166,uu____167) ->
           FStar_Tactics_Effect.bind
             (FStar_Tactics_Builtins.apply
                (FStar_Tactics_Derived.quote_lid
                   ["FStar"; "Tactics"; "Logic"; "fa_intro_lem"]))
             (fun uu___60_169  -> FStar_Tactics_Builtins.intro)
       | uu____170 -> FStar_Tactics_Derived.fail "not a forall")
let forall_intros:
  FStar_Reflection_Types.binder Prims.list FStar_Tactics_Effect.tactic =
  FStar_Tactics_Derived.repeat1 forall_intro
let split_lem:
  'Aa 'Ab .
    'Aa Prims.squash ->
      'Ab Prims.squash -> ('Aa,'Ab) Prims.l_and Prims.squash
  = fun sa  -> fun sb  -> ()
let split: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
    (fun g  ->
       match FStar_Reflection_Formula.term_as_formula g with
       | FStar_Reflection_Formula.And (uu____241,uu____242) ->
           FStar_Tactics_Builtins.apply
             (FStar_Tactics_Derived.quote_lid
                ["FStar"; "Tactics"; "Logic"; "split_lem"])
       | uu____243 -> FStar_Tactics_Derived.fail "not a conjunction")
let imp_intro_lem:
  'Aa 'Ab . ('Aa -> 'Ab Prims.squash) -> ('Aa,'Ab) Prims.l_imp Prims.squash =
  fun f  -> ()
let implies_intro: FStar_Reflection_Types.binder FStar_Tactics_Effect.tactic
  =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
    (fun g  ->
       match FStar_Reflection_Formula.term_as_formula g with
       | FStar_Reflection_Formula.Implies (uu____317,uu____318) ->
           FStar_Tactics_Effect.bind
             (FStar_Tactics_Builtins.apply
                (FStar_Tactics_Derived.quote_lid
                   ["FStar"; "Tactics"; "Logic"; "imp_intro_lem"]))
             (fun uu___61_320  ->
                FStar_Tactics_Effect.bind FStar_Tactics_Builtins.intro
                  (fun b  -> FStar_Tactics_Effect.return b))
       | uu____323 -> FStar_Tactics_Derived.fail "not an implication")
let implies_intros:
  FStar_Reflection_Types.binder Prims.list FStar_Tactics_Effect.tactic =
  FStar_Tactics_Derived.repeat1 implies_intro
let rec visit:
  Prims.unit FStar_Tactics_Effect.tactic ->
    Prims.unit ->
      (Prims.unit,(Prims.unit FStar_Tactics_Effect.__result,Obj.t)
                    Prims.l_Forall)
        FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun callback  ->
    fun uu____379  ->
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
                          (fun uu___62_439  -> FStar_Tactics_Effect.return ()))
                 | FStar_Reflection_Formula.Implies (p,q) ->
                     FStar_Tactics_Effect.bind implies_intro
                       (fun uu___63_443  ->
                          FStar_Tactics_Builtins.seq (visit callback)
                            l_revert)
                 | uu____450 ->
                     FStar_Tactics_Derived.or_else
                       FStar_Tactics_Builtins.trivial
                       FStar_Tactics_Builtins.smt))) ()
let rec simplify_eq_implication:
  Prims.unit ->
    (Prims.unit,(Prims.unit FStar_Tactics_Effect.__result,Obj.t)
                  Prims.l_Forall)
      FStar_Tactics_Effect._dm4f_TAC_repr
  =
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
                   | FStar_Pervasives_Native.Some (uu____527,rhs) ->
                       FStar_Tactics_Effect.bind implies_intro
                         (fun eq_h  ->
                            FStar_Tactics_Effect.bind
                              (FStar_Tactics_Builtins.rewrite eq_h)
                              (fun uu___65_536  ->
                                 FStar_Tactics_Effect.bind
                                   FStar_Tactics_Builtins.clear
                                   (fun uu___64_538  ->
                                      visit simplify_eq_implication)))))) ()
let rewrite_all_equalities:
  Prims.unit ->
    (Prims.unit,(Prims.unit FStar_Tactics_Effect.__result,Obj.t)
                  Prims.l_Forall)
      FStar_Tactics_Effect._dm4f_TAC_repr
  = visit simplify_eq_implication
let rec unfold_definition_and_simplify_eq':
  FStar_Reflection_Types.term ->
    Prims.unit ->
      (Prims.unit,(Prims.unit FStar_Tactics_Effect.__result,Obj.t)
                    Prims.l_Forall)
        FStar_Tactics_Effect._dm4f_TAC_repr
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
           | uu____642 ->
               FStar_Tactics_Effect.bind
                 (FStar_Tactics_Derived.destruct_equality_implication g)
                 (fun r  ->
                    match r with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Tactics_Derived.fail
                          "Not an equality implication"
                    | FStar_Pervasives_Native.Some (uu____663,rhs) ->
                        FStar_Tactics_Effect.bind implies_intro
                          (fun eq_h  ->
                             FStar_Tactics_Effect.bind
                               (FStar_Tactics_Builtins.rewrite eq_h)
                               (fun uu___67_672  ->
                                  FStar_Tactics_Effect.bind
                                    FStar_Tactics_Builtins.clear
                                    (fun uu___66_674  ->
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
let vbind:
  'Ap 'Aq . 'Ap Prims.squash -> ('Ap -> 'Aq Prims.squash) -> 'Aq Prims.squash
  = fun sq  -> fun f  -> ()
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
                 (FStar_Reflection_Syntax.mk_e_app v [t])))
           (fun uu___68_780  ->
              FStar_Tactics_Effect.bind FStar_Tactics_Builtins.intro
                (fun b  ->
                   FStar_Tactics_Effect.return
                     (FStar_Reflection_Basic.pack
                        (FStar_Reflection_Data.Tv_Var b)))))
let squash_intro: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.apply
    (FStar_Tactics_Derived.quote_lid ["FStar"; "Squash"; "return_squash"])
let or_ind:
  'Ap 'Aq 'Aphi .
    ('Ap,'Aq) Prims.l_or ->
      ('Ap,'Aphi) Prims.l_imp Prims.squash ->
        ('Aq,'Aphi) Prims.l_imp Prims.squash -> 'Aphi Prims.squash
  = fun o  -> fun l  -> fun r  -> ()
let cases_or:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic =
  fun o  ->
    FStar_Tactics_Effect.bind
      (FStar_Tactics_Derived.quote_lid
         ["FStar"; "Tactics"; "Logic"; "or_ind"])
      (fun oi  ->
         FStar_Tactics_Builtins.apply
           (FStar_Tactics_Effect.return
              (FStar_Reflection_Syntax.mk_e_app oi [o])))
let bool_ind:
  Prims.bool ->
    Prims.unit ->
      ((Prims.bool,Prims.unit,Prims.unit) Prims.eq2,Obj.t) Prims.l_imp
        Prims.squash ->
        ((Prims.bool,Prims.unit,Prims.unit) Prims.eq2,Obj.t) Prims.l_imp
          Prims.squash -> Obj.t Prims.squash
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
                 (FStar_Reflection_Syntax.mk_e_app bi [b])))
           (FStar_Tactics_Effect.bind
              (FStar_Tactics_Builtins.trytac
                 (FStar_Tactics_Effect.bind implies_intro
                    (fun b1  ->
                       FStar_Tactics_Effect.bind
                         (FStar_Tactics_Builtins.rewrite b1)
                         (fun uu___69_993  -> FStar_Tactics_Builtins.clear))))
              (fun uu___70_995  -> FStar_Tactics_Derived.idtac)))
let or_intro_1:
  'Ap 'Aq . 'Ap Prims.squash -> ('Ap,'Aq) Prims.l_or Prims.squash =
  fun uu____1028  -> ()
let or_intro_2:
  'Ap 'Aq . 'Aq Prims.squash -> ('Ap,'Aq) Prims.l_or Prims.squash =
  fun uu____1063  -> ()
let left: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.apply
    (FStar_Tactics_Derived.quote_lid
       ["FStar"; "Tactics"; "Logic"; "or_intro_1"])
let right: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.apply
    (FStar_Tactics_Derived.quote_lid
       ["FStar"; "Tactics"; "Logic"; "or_intro_2"])
let __and_elim:
  'Ap 'Aq 'Aphi .
    ('Ap,'Aq) Prims.l_and ->
      ('Ap,('Aq,'Aphi) Prims.l_imp) Prims.l_imp Prims.squash ->
        'Aphi Prims.squash
  = fun p_and_q  -> fun f  -> ()
let and_elim:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic =
  fun t  ->
    FStar_Tactics_Effect.bind
      (FStar_Tactics_Derived.quote_lid
         ["FStar"; "Tactics"; "Logic"; "__and_elim"])
      (fun ae  ->
         FStar_Tactics_Builtins.apply
           (FStar_Tactics_Effect.return
              (FStar_Reflection_Syntax.mk_e_app ae [t])))