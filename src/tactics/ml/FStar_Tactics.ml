open Prims
type binders = FStar_Tactics_Types.binder Prims.list
type goal = (FStar_Tactics_Types.env* FStar_Tactics_Types.term)
type goals = goal Prims.list
type state = (goals* goals)
type 'Aa __result =
  | Success of 'Aa* state
  | Failed of Prims.string* state
let uu___is_Success projectee =
  match projectee with | Success (_0,_1) -> true | uu____40 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success (_0,_1) -> _0
let __proj__Success__item___1 projectee =
  match projectee with | Success (_0,_1) -> _1
let uu___is_Failed projectee =
  match projectee with | Failed (_0,_1) -> true | uu____96 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed (_0,_1) -> _0
let __proj__Failed__item___1 projectee =
  match projectee with | Failed (_0,_1) -> _1
type 'Aa __tac = state -> 'Aa __result
let __ret x s = Success (x, s)
let __bind t1 t2 p =
  match t1 p with
  | Success (a,q) -> t2 a q
  | Failed (msg,q) -> Failed (msg, q)
let __get: Prims.unit -> state -> state __result =
  fun uu____223  -> fun s0  -> Success (s0, s0)
type 'Aa __tac_wp = state -> Prims.unit -> Obj.t
type ('Aa,'Ab,'Awp,'Af,'Aps,'Apost) g_bind = 'Awp
type ('Aa,'Awp) g_compact = Prims.unit
type ('Ar,'Aa,'Ab,'Awp,'Af) __TAC_eff_override_bind_wp = Prims.unit
type ('Aa,'Awp,'As,'Ap') _dm4f_TAC_lift_from_pure = 'Awp
type ('Aa,'Ax,'As,'Ap') _dm4f_TAC_return_wp = 'Ap'
let _dm4f_TAC_return_elab x s = Success (x, s)
let _dm4f_TAC_bind_elab t1 t2__w t2 p =
  match t1 p with
  | Success (a,q) -> t2 a q
  | Failed (msg,q) -> Failed (msg, q)
let _dm4f_TAC___proj__TAC__item____get_elab:
  Prims.unit ->
    ((FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list*
      (FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list) ->
      ((FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list*
        (FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list)
        __result
  = fun uu____590  -> fun s0  -> Success (s0, s0)
type _dm4f_TAC___proj__TAC__item____get_complete_type =
  Prims.unit ->
    ((FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list*
      (FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list) ->
      ((FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list*
        (FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list)
        __result
type ('Aa,'Awp_a) _dm4f_TAC_repr =
  ((FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list*
    (FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list) ->
    'Aa __result
type _dm4f_TAC_pre =
  ((FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list*
    (FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list) -> 
    Obj.t
type 'Aa _dm4f_TAC_post = 'Aa __result -> Obj.t
type 'Aa _dm4f_TAC_wp =
  ((FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list*
    (FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list) ->
    Prims.unit -> Obj.t
type ('Aa,'At) _dm4f_TAC_ctx =
  ((FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list*
    (FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list) ->
    Prims.unit -> 'At
type ('Aa,'At) _dm4f_TAC_gctx =
  ((FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list*
    (FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list) ->
    Prims.unit -> 'At
let _dm4f_TAC_pure x uu____790 uu____791 = x
let _dm4f_TAC_app l r uu____886 uu____887 = Obj.magic ()
let _dm4f_TAC_lift1 f a1 uu____990 uu____991 = Obj.magic ()
let _dm4f_TAC_lift2 f a1 a2 uu____1112 uu____1113 = Obj.magic ()
let _dm4f_TAC_push f uu____1216 uu____1217 e1 = Obj.magic ()
type ('Aa,'Ac,'Auu____1254,'Auu____1255,'Auu____1256,'Auu____1257) _dm4f_TAC_wp_if_then_else =
  Prims.unit
type ('Aa,'Aq,'Awp,'Auu____1278,'Auu____1279) _dm4f_TAC_wp_assert =
  Prims.unit
type ('Aa,'Aq,'Awp,'Auu____1295,'Auu____1296) _dm4f_TAC_wp_assume =
  Prims.unit
type ('Aa,'Ab,'Af,'Auu____1313,'Auu____1314) _dm4f_TAC_wp_close = Prims.unit
type ('Aa,'Awp1,'Awp2) _dm4f_TAC_stronger = Prims.unit
type ('Aa,'Awp,'Auu____1371,'Auu____1372) _dm4f_TAC_wp_ite = Prims.unit
type ('Aa,'Auu____1399,'Auu____1400) _dm4f_TAC_null_wp = Prims.unit
type ('Aa,'Awp) _dm4f_TAC_wp_trivial = Prims.unit
let __proj__TAC__item__return = _dm4f_TAC_return_elab
let __proj__TAC__item__bind = _dm4f_TAC_bind_elab
let __proj__TAC__item____get uu____1477 s0 = Success (s0, s0)
type 'Aa tactic = Prims.unit -> ('Aa,Prims.unit) _dm4f_TAC_repr
let return x uu____1563 s = Success (x, s)
let bind t f uu____1611 p =
  match (t ()) p with
  | Success (a,q) -> (f a ()) q
  | Failed (msg,q) -> Failed (msg, q)
let idtac: Prims.unit tactic = return ()
let rec fix ff u = ff (fix ff) ()
let rec fix1 ff x u = ff (fix1 ff) x ()
let __fail msg s0 = Failed (msg, s0)
let fail msg uu____1849 = __fail msg
let reify_tactic t s = (t ()) s
let trytac t uu____1904 ps =
  match reify_tactic t ps with
  | Success (a,ps') -> Success ((Some a), ps')
  | Failed (uu____1925,uu____1926) -> Success (None, ps)
let or_else t1 t2 =
  bind (trytac t1)
    (fun r  -> match r with | Some x -> return x | None  -> t2)
let rec repeat t uu____2026 =
  bind (trytac t)
    (fun r  ->
       match r with
       | None  -> return []
       | Some x -> bind (repeat t) (fun xs  -> return (x :: xs))) ()
let __embed =
  Obj.magic (fun uu____2083  -> failwith "Not yet implemented:__embed")
let quote x uu____2098 s = Success ((__embed x), s)
let __forall_intros: binders __tac =
  Obj.magic
    (fun uu____2117  -> failwith "Not yet implemented:__forall_intros")
let forall_intros: Prims.unit -> binders __tac =
  fun uu____2143  -> __forall_intros
let __implies_intro: FStar_Tactics_Types.binder __tac =
  Obj.magic
    (fun uu____2153  -> failwith "Not yet implemented:__implies_intro")
let implies_intro: Prims.unit -> FStar_Tactics_Types.binder __tac =
  fun uu____2179  -> __implies_intro
let __trivial: Prims.unit __tac =
  Obj.magic (fun uu____2189  -> failwith "Not yet implemented:__trivial")
let trivial: Prims.unit -> Prims.unit __tac = fun uu____2215  -> __trivial
let __simpl: Prims.unit __tac =
  Obj.magic (fun uu____2225  -> failwith "Not yet implemented:__simpl")
let simpl: Prims.unit -> Prims.unit __tac = fun uu____2251  -> __simpl
let __revert: Prims.unit __tac =
  Obj.magic (fun uu____2261  -> failwith "Not yet implemented:__revert")
let revert: Prims.unit -> Prims.unit __tac = fun uu____2287  -> __revert
let __clear: Prims.unit __tac =
  Obj.magic (fun uu____2297  -> failwith "Not yet implemented:__clear")
let clear: Prims.unit -> Prims.unit __tac = fun uu____2323  -> __clear
let __split: Prims.unit __tac =
  Obj.magic (fun uu____2333  -> failwith "Not yet implemented:__split")
let split: Prims.unit -> Prims.unit __tac = fun uu____2359  -> __split
let __merge: Prims.unit __tac =
  Obj.magic (fun uu____2369  -> failwith "Not yet implemented:__merge")
let merge: Prims.unit -> Prims.unit __tac = fun uu____2395  -> __merge
let __rewrite: FStar_Tactics_Types.binder -> Prims.unit __tac =
  Obj.magic (fun uu____2407  -> failwith "Not yet implemented:__rewrite")
let rewrite: FStar_Tactics_Types.binder -> Prims.unit -> Prims.unit __tac =
  fun b  -> fun uu____2418  -> __rewrite b
let __smt: Prims.unit __tac =
  Obj.magic (fun uu____2428  -> failwith "Not yet implemented:__smt")
let smt: Prims.unit -> Prims.unit -> Prims.unit __tac =
  fun uu____2440  -> fun uu____2442  -> __smt
let __focus: Prims.unit __tac -> Prims.unit __tac =
  Obj.magic (fun uu____2459  -> failwith "Not yet implemented:__focus")
let focus: Prims.unit tactic -> Prims.unit -> Prims.unit __tac =
  fun f  -> fun uu____2481  -> __focus (reify_tactic f)
let __seq: Prims.unit __tac -> Prims.unit __tac -> Prims.unit __tac =
  Obj.magic
    (fun uu____2515  ->
       fun uu____2516  -> failwith "Not yet implemented:__seq")
let seq:
  Prims.unit tactic -> Prims.unit tactic -> Prims.unit -> Prims.unit __tac =
  fun f  ->
    fun g  -> fun uu____2551  -> __seq (reify_tactic f) (reify_tactic g)
let __exact: FStar_Tactics_Types.term -> Prims.unit __tac =
  Obj.magic (fun uu____2581  -> failwith "Not yet implemented:__exact")
let exact:
  FStar_Tactics_Types.term tactic ->
    Prims.unit ->
      ((FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list*
        (FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list) ->
        Prims.unit __result
  =
  fun t  ->
    fun uu____2601  ->
      fun p  ->
        match (t ()) p with
        | Success (a,q) -> __exact a q
        | Failed (msg,q) -> Failed (msg, q)
let __apply_lemma: FStar_Tactics_Types.term -> Prims.unit __tac =
  Obj.magic (fun uu____2663  -> failwith "Not yet implemented:__apply_lemma")
let apply_lemma:
  FStar_Tactics_Types.term tactic ->
    Prims.unit ->
      ((FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list*
        (FStar_Tactics_Types.env* FStar_Tactics_Types.term) Prims.list) ->
        Prims.unit __result
  =
  fun t  ->
    fun uu____2683  ->
      fun p  ->
        match (t ()) p with
        | Success (a,q) -> __apply_lemma a q
        | Failed (msg,q) -> Failed (msg, q)
let __print: Prims.string -> Prims.unit __tac =
  Obj.magic (fun uu____2745  -> failwith "Not yet implemented:__print")
let print: Prims.string -> Prims.unit -> Prims.unit __tac =
  fun msg  -> fun uu____2756  -> __print msg
let __dump: Prims.string -> Prims.unit __tac =
  Obj.magic (fun uu____2768  -> failwith "Not yet implemented:__dump")
let dump: Prims.string -> Prims.unit -> Prims.unit __tac =
  fun msg  -> fun uu____2779  -> __dump msg
let __grewrite:
  FStar_Tactics_Types.term -> FStar_Tactics_Types.term -> Prims.unit __tac =
  Obj.magic
    (fun uu____2795  ->
       fun uu____2796  -> failwith "Not yet implemented:__grewrite")
let grewrite:
  FStar_Tactics_Types.term ->
    FStar_Tactics_Types.term -> Prims.unit -> Prims.unit __tac
  = fun t1  -> fun t2  -> fun uu____2811  -> __grewrite t1 t2
let __refl: Prims.unit __tac =
  Obj.magic (fun uu____2821  -> failwith "Not yet implemented:__refl")
let refl: Prims.unit -> Prims.unit __tac = fun uu____2847  -> __refl
let __pointwise: Prims.unit __tac -> Prims.unit __tac =
  Obj.magic (fun uu____2864  -> failwith "Not yet implemented:__pointwise")
let pointwise: Prims.unit tactic -> Prims.unit -> Prims.unit __tac =
  fun tau  -> fun uu____2886  -> __pointwise (reify_tactic tau)
let __later: Prims.unit __tac =
  Obj.magic (fun uu____2906  -> failwith "Not yet implemented:__later")
let later: Prims.unit -> Prims.unit __tac = fun uu____2932  -> __later
let rec revert_all: binders -> Prims.unit tactic =
  fun bs  ->
    match bs with
    | [] -> return ()
    | uu____2947::tl1 -> bind revert (fun uu___40_2954  -> revert_all tl1)
let get:
  Prims.unit -> (state,(state __result,Obj.t) Prims.l_Forall) _dm4f_TAC_repr
  = Obj.magic (fun uu____2978  -> __proj__TAC__item____get ())
let cur_goal: goal tactic =
  bind get
    (fun ps  ->
       match ps with
       | (goals,uu____2994) ->
           (match goals with
            | [] -> fail "No more goals"
            | hd1::uu____2999 -> return hd1))
let destruct_equality_implication:
  FStar_Tactics_Types.term ->
    (FStar_Reflection_Formula.formula* FStar_Tactics_Types.term) Prims.option
      tactic
  =
  fun t  ->
    match FStar_Reflection_Formula.term_as_formula t with
    | FStar_Reflection_Formula.Implies (lhs,rhs) ->
        (match FStar_Reflection_Formula.term_as_formula lhs with
         | FStar_Reflection_Formula.Comp
             (FStar_Reflection_Formula.Eq ,uu____3034,uu____3035,uu____3036)
             ->
             return
               (Some ((FStar_Reflection_Formula.term_as_formula lhs), rhs))
         | uu____3044 -> return None)
    | uu____3052 -> return None
let rec visit:
  Prims.unit tactic -> Prims.unit -> (Prims.unit,Prims.unit) _dm4f_TAC_repr =
  fun callback  ->
    fun uu____3105  ->
      focus
        (or_else callback
           (bind cur_goal
              (fun eg  ->
                 match eg with
                 | (e,g) ->
                     (match FStar_Reflection_Formula.term_as_formula g with
                      | FStar_Reflection_Formula.Forall (b,phi) ->
                          bind forall_intros
                            (fun binders  ->
                               seq (visit callback) (revert_all binders))
                      | FStar_Reflection_Formula.And (p,q) ->
                          seq split
                            (bind (visit callback)
                               (fun uu___42_3199  ->
                                  bind (trytac merge)
                                    (fun uu___41_3209  -> return ())))
                      | FStar_Reflection_Formula.Implies (p,q) ->
                          bind implies_intro
                            (fun uu___43_3219  -> seq (visit callback) revert)
                      | uu____3228 -> or_else trivial (smt ()))))) ()
let rec simplify_eq_implication:
  Prims.unit -> (Prims.unit,Prims.unit) _dm4f_TAC_repr =
  fun u  ->
    bind cur_goal
      (fun g  ->
         match g with
         | (context,goal_t) ->
             bind (destruct_equality_implication goal_t)
               (fun r  ->
                  match r with
                  | None  -> fail "Not an equality implication"
                  | Some (uu____3317,rhs) ->
                      bind implies_intro
                        (fun eq_h  ->
                           bind (rewrite eq_h)
                             (fun uu___45_3334  ->
                                bind clear
                                  (fun uu___44_3337  ->
                                     visit simplify_eq_implication))))) ()
let rec try_rewrite_equality:
  FStar_Tactics_Types.term -> binders -> Prims.unit tactic =
  fun x  ->
    fun bs  ->
      match bs with
      | [] -> return ()
      | x_t::bs1 ->
          (match FStar_Reflection_Formula.term_as_formula
                   (FStar_Reflection_Syntax.type_of_binder x_t)
           with
           | FStar_Reflection_Formula.Comp
               (FStar_Reflection_Formula.Eq ,uu____3362,y,uu____3364) ->
               if FStar_Reflection_Syntax.term_eq x y
               then rewrite x_t
               else try_rewrite_equality x bs1
           | uu____3371 -> try_rewrite_equality x bs1)
let rec rewrite_all_context_equalities: binders -> Prims.unit tactic =
  fun bs  ->
    match bs with
    | [] -> return ()
    | x_t::bs1 ->
        (match FStar_Reflection_Formula.term_as_formula
                 (FStar_Reflection_Syntax.type_of_binder x_t)
         with
         | FStar_Reflection_Formula.Comp
             (FStar_Reflection_Formula.Eq ,uu____3394,uu____3395,uu____3396)
             ->
             bind (rewrite x_t)
               (fun uu___46_3405  -> rewrite_all_context_equalities bs1)
         | uu____3408 -> rewrite_all_context_equalities bs1)
let rewrite_eqs_from_context: Prims.unit tactic =
  bind cur_goal
    (fun g  ->
       match g with
       | (context,uu____3428) ->
           rewrite_all_context_equalities
             (FStar_Reflection_Syntax.binders_of_env context))
let rewrite_equality: FStar_Tactics_Types.term tactic -> Prims.unit tactic =
  fun x  ->
    bind cur_goal
      (fun g  ->
         match g with
         | (context,uu____3462) ->
             bind x
               (fun t  ->
                  try_rewrite_equality t
                    (FStar_Reflection_Syntax.binders_of_env context)))
let rewrite_all_equalities:
  Prims.unit ->
    (Prims.unit,(Prims.unit __result,Obj.t) Prims.l_Forall) _dm4f_TAC_repr
  = visit simplify_eq_implication
let rec unfold_definition_and_simplify_eq':
  FStar_Tactics_Types.term ->
    Prims.unit -> (Prims.unit,Prims.unit) _dm4f_TAC_repr
  =
  fun tm  ->
    fun u  ->
      bind cur_goal
        (fun g  ->
           match g with
           | (uu____3551,goal_t) ->
               (match FStar_Reflection_Formula.term_as_formula goal_t with
                | FStar_Reflection_Formula.App (hd1,arg) ->
                    if FStar_Reflection_Syntax.term_eq hd1 tm
                    then trivial
                    else return ()
                | uu____3560 ->
                    bind (destruct_equality_implication goal_t)
                      (fun r  ->
                         match r with
                         | None  -> fail "Not an equality implication"
                         | Some (uu____3581,rhs) ->
                             bind implies_intro
                               (fun eq_h  ->
                                  bind (rewrite eq_h)
                                    (fun uu___48_3598  ->
                                       bind clear
                                         (fun uu___47_3601  ->
                                            visit
                                              (unfold_definition_and_simplify_eq'
                                                 tm))))))) ()
let __prune: Prims.string -> Prims.unit __tac =
  Obj.magic (fun uu____3611  -> failwith "Not yet implemented:__prune")
let prune: Prims.string -> Prims.unit -> Prims.unit __tac =
  fun ns  -> fun uu____3622  -> __prune ns
let __addns: Prims.string -> Prims.unit __tac =
  Obj.magic (fun uu____3634  -> failwith "Not yet implemented:__addns")
let addns: Prims.string -> Prims.unit -> Prims.unit __tac =
  fun ns  -> fun uu____3645  -> __addns ns
let unfold_definition_and_simplify_eq:
  FStar_Tactics_Types.term tactic -> Prims.unit tactic =
  fun tm  -> bind tm (fun tm'  -> unfold_definition_and_simplify_eq' tm')
type ('a,'At,'Ap) by_tactic = 'Ap
let assert_by_tactic t p = ()
let liftM1' f ma = bind ma (fun a  -> f a)
let liftM1 f = liftM1' (fun x  -> return (f x))
let liftM2' f ma mb = bind ma (fun a  -> bind mb (fun b  -> f a b))
let liftM2 f = liftM2' (fun x  -> fun y  -> return (f x y))