open Prims
let quote_lid:
  FStar_Reflection_Syntax.name ->
    FStar_Reflection_Types.term FStar_Tactics_Effect.tactic
  =
  fun ns  ->
    FStar_Tactics_Effect.return
      (FStar_Reflection_Syntax.pack
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Syntax.pack_fv ns)))
let liftM1' f ma = FStar_Tactics_Effect.bind ma (fun a  -> f a)
let liftM1 f = liftM1' (fun x  -> FStar_Tactics_Effect.return (f x))
let liftM2' f ma mb =
  FStar_Tactics_Effect.bind ma
    (fun a  -> FStar_Tactics_Effect.bind mb (fun b  -> f a b))
let liftM2 f =
  liftM2' (fun x  -> fun y  -> FStar_Tactics_Effect.return (f x y))
let rec mapM f l =
  match l with
  | [] -> FStar_Tactics_Effect.return []
  | x::xs ->
      FStar_Tactics_Effect.bind (f x)
        (fun y  ->
           FStar_Tactics_Effect.bind (mapM f xs)
             (fun ys  -> FStar_Tactics_Effect.return (y :: ys)))
let idtac: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.return ()
let __fail msg s0 = FStar_Tactics_Effect.Failed (msg, s0)
let fail msg uu____380 = __fail msg
let or_else t1 t2 =
  FStar_Tactics_Effect.bind (FStar_Tactics_Builtins.trytac t1)
    (fun r  ->
       match r with | Some x -> FStar_Tactics_Effect.return x | None  -> t2)
let rec repeat t uu____475 =
  FStar_Tactics_Effect.bind (FStar_Tactics_Builtins.trytac t)
    (fun r  ->
       match r with
       | None  -> FStar_Tactics_Effect.return []
       | Some x ->
           FStar_Tactics_Effect.bind (repeat t)
             (fun xs  -> FStar_Tactics_Effect.return (x :: xs))) ()
let repeat1 t =
  FStar_Tactics_Effect.bind t
    (fun x  ->
       FStar_Tactics_Effect.bind (repeat t)
         (fun xs  -> FStar_Tactics_Effect.return (x :: xs)))
let rec repeatseq t uu____602 =
  FStar_Tactics_Effect.bind
    (FStar_Tactics_Builtins.trytac
       (FStar_Tactics_Builtins.seq
          (FStar_Tactics_Effect.bind t
             (fun uu___50_629  -> FStar_Tactics_Effect.return ()))
          (repeatseq t)))
    (fun uu___51_638  -> FStar_Tactics_Effect.return ()) ()
let simpl: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.norm
    [FStar_Reflection_Syntax.Simpl; FStar_Reflection_Syntax.Primops]
let whnf: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.norm
    [FStar_Reflection_Syntax.WHNF; FStar_Reflection_Syntax.Primops]
let __cut f x = f x
let tcut:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.binder FStar_Tactics_Effect.tactic
  =
  fun t  ->
    FStar_Tactics_Effect.bind
      (quote_lid ["FStar"; "Tactics"; "Derived"; "__cut"])
      (fun qq  ->
         FStar_Tactics_Effect.bind
           (FStar_Tactics_Builtins.apply
              (FStar_Tactics_Effect.return
                 (FStar_Reflection_Syntax.pack
                    (FStar_Reflection_Data.Tv_App (qq, t)))))
           (fun uu___52_712  -> FStar_Tactics_Builtins.intro))
let rec revert_all:
  FStar_Reflection_Syntax.binders -> Prims.unit FStar_Tactics_Effect.tactic =
  fun bs  ->
    match bs with
    | [] -> FStar_Tactics_Effect.return ()
    | uu____726::tl1 ->
        FStar_Tactics_Effect.bind FStar_Tactics_Builtins.revert
          (fun uu___53_733  -> revert_all tl1)
let assumption: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_env
    (fun e  ->
       let rec aux bs =
         match bs with
         | [] -> fail "no assumption matches goal"
         | b::bs1 ->
             let t =
               FStar_Reflection_Syntax.pack
                 (FStar_Reflection_Data.Tv_Var b) in
             or_else
               (FStar_Tactics_Builtins.exact (FStar_Tactics_Effect.return t))
               (aux bs1) in
       aux (FStar_Reflection_Syntax.binders_of_env e))
let destruct_equality_implication:
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Formula.formula* FStar_Reflection_Types.term) option
      FStar_Tactics_Effect.tactic
  =
  fun t  ->
    match FStar_Reflection_Formula.term_as_formula t with
    | FStar_Reflection_Formula.Implies (lhs,rhs) ->
        (match FStar_Reflection_Formula.term_as_formula' lhs with
         | FStar_Reflection_Formula.Comp
             (FStar_Reflection_Formula.Eq ,uu____807,uu____808,uu____809) ->
             FStar_Tactics_Effect.return
               (Some ((FStar_Reflection_Formula.term_as_formula' lhs), rhs))
         | uu____817 -> FStar_Tactics_Effect.return None)
    | uu____825 -> FStar_Tactics_Effect.return None
let rec try_rewrite_equality:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Syntax.binders -> Prims.unit FStar_Tactics_Effect.tactic
  =
  fun x  ->
    fun bs  ->
      match bs with
      | [] -> FStar_Tactics_Effect.return ()
      | x_t::bs1 ->
          (match FStar_Reflection_Formula.term_as_formula'
                   (FStar_Reflection_Syntax.type_of_binder x_t)
           with
           | FStar_Reflection_Formula.Comp
               (FStar_Reflection_Formula.Eq ,uu____859,y,uu____861) ->
               if FStar_Reflection_Syntax.term_eq x y
               then FStar_Tactics_Builtins.rewrite x_t
               else try_rewrite_equality x bs1
           | uu____868 -> try_rewrite_equality x bs1)
let rec rewrite_all_context_equalities:
  FStar_Reflection_Syntax.binders -> Prims.unit FStar_Tactics_Effect.tactic =
  fun bs  ->
    match bs with
    | [] -> FStar_Tactics_Effect.return ()
    | x_t::bs1 ->
        FStar_Tactics_Effect.bind
          (match FStar_Reflection_Formula.term_as_formula'
                   (FStar_Reflection_Syntax.type_of_binder x_t)
           with
           | FStar_Reflection_Formula.Comp
               (FStar_Reflection_Formula.Eq ,uu____897,lhs,uu____899) ->
               (match FStar_Reflection_Syntax.inspect lhs with
                | FStar_Reflection_Data.Tv_Var uu____901 ->
                    FStar_Tactics_Builtins.rewrite x_t
                | uu____904 -> idtac)
           | uu____907 -> idtac)
          (fun uu___54_912  -> rewrite_all_context_equalities bs1)
let rewrite_eqs_from_context: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_env
    (fun e  ->
       rewrite_all_context_equalities
         (FStar_Reflection_Syntax.binders_of_env e))
let rewrite_equality:
  FStar_Reflection_Types.term FStar_Tactics_Effect.tactic ->
    Prims.unit FStar_Tactics_Effect.tactic
  =
  fun x  ->
    FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_env
      (fun e  ->
         FStar_Tactics_Effect.bind x
           (fun t  ->
              try_rewrite_equality t
                (FStar_Reflection_Syntax.binders_of_env e)))
let unfold_point:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic =
  fun t  ->
    FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_env
      (fun e  ->
         FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
           (fun g  ->
              match FStar_Reflection_Formula.term_as_formula g with
              | FStar_Reflection_Formula.Comp
                  (FStar_Reflection_Formula.Eq ,uu____989,l,r) ->
                  if FStar_Reflection_Syntax.term_eq l t
                  then
                    FStar_Tactics_Effect.bind
                      (FStar_Tactics_Builtins.norm
                         [FStar_Reflection_Syntax.Delta])
                      (fun uu___55_999  -> FStar_Tactics_Builtins.trefl)
                  else FStar_Tactics_Builtins.trefl
              | uu____1001 -> fail "impossible"))
let unfold_def:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic =
  fun t  -> FStar_Tactics_Builtins.pointwise (unfold_point t)
let grewrite':
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic
  =
  fun t1  ->
    fun t2  ->
      fun eq1  ->
        FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
          (fun g  ->
             match FStar_Reflection_Formula.term_as_formula g with
             | FStar_Reflection_Formula.Comp
                 (FStar_Reflection_Formula.Eq ,uu____1052,l,uu____1054) ->
                 if FStar_Reflection_Syntax.term_eq l t1
                 then
                   FStar_Tactics_Builtins.exact
                     (FStar_Tactics_Effect.return eq1)
                 else FStar_Tactics_Builtins.trefl
             | uu____1065 -> fail "impossible")
let mk_sq_eq:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term
  =
  fun t1  ->
    fun t2  ->
      FStar_Reflection_Syntax.mk_app
        (FStar_Reflection_Syntax.pack
           (FStar_Reflection_Data.Tv_FVar
              (FStar_Reflection_Syntax.pack_fv
                 FStar_Reflection_Syntax.squash_qn)))
        [FStar_Reflection_Syntax.mk_app
           (FStar_Reflection_Syntax.pack
              (FStar_Reflection_Data.Tv_FVar
                 (FStar_Reflection_Syntax.pack_fv
                    FStar_Reflection_Syntax.eq2_qn))) [t1; t2]]
let grewrite:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic
  =
  fun t1  ->
    fun t2  ->
      FStar_Tactics_Effect.bind (tcut (mk_sq_eq t1 t2))
        (fun e  ->
           FStar_Tactics_Builtins.pointwise
             (grewrite' t1 t2
                (FStar_Reflection_Syntax.pack
                   (FStar_Reflection_Data.Tv_Var e))))
let focus f =
  FStar_Tactics_Effect.bind
    (FStar_Tactics_Builtins.divide (Prims.parse_int "1") f idtac)
    (fun res  -> FStar_Tactics_Effect.return (fst res))
