open Prims
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
let fail msg uu____369 = __fail msg
let or_else t1 t2 =
  FStar_Tactics_Effect.bind (FStar_Tactics_Builtins.trytac t1)
    (fun r  ->
       match r with | Some x -> FStar_Tactics_Effect.return x | None  -> t2)
let rec repeat t uu____464 =
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
let rec repeatseq t uu____591 =
  FStar_Tactics_Effect.bind
    (FStar_Tactics_Builtins.trytac
       (FStar_Tactics_Builtins.seq
          (FStar_Tactics_Effect.bind t
             (fun uu___50_618  -> FStar_Tactics_Effect.return ()))
          (repeatseq t)))
    (fun uu___51_627  -> FStar_Tactics_Effect.return ()) ()
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
      (fun uu____683  ->
         fun s  -> FStar_Tactics_Effect.Success ((Obj.magic ()), s))
      (fun qq  ->
         FStar_Tactics_Effect.bind
           (FStar_Tactics_Builtins.apply
              (FStar_Tactics_Effect.return
                 (FStar_Reflection_Syntax.pack
                    (FStar_Reflection_Syntax.Tv_App (qq, t)))))
           (fun uu___52_715  -> FStar_Tactics_Builtins.intro))
let rec revert_all:
  FStar_Reflection_Syntax.binders -> Prims.unit FStar_Tactics_Effect.tactic =
  fun bs  ->
    match bs with
    | [] -> FStar_Tactics_Effect.return ()
    | uu____729::tl1 ->
        FStar_Tactics_Effect.bind FStar_Tactics_Builtins.revert
          (fun uu___53_736  -> revert_all tl1)
let assumption: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_env
    (fun e  ->
       let rec aux bs =
         match bs with
         | [] -> fail "no assumption matches goal"
         | b::bs1 ->
             let t =
               FStar_Reflection_Syntax.pack
                 (FStar_Reflection_Syntax.Tv_Var b) in
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
             (FStar_Reflection_Formula.Eq ,uu____810,uu____811,uu____812) ->
             FStar_Tactics_Effect.return
               (Some ((FStar_Reflection_Formula.term_as_formula' lhs), rhs))
         | uu____820 -> FStar_Tactics_Effect.return None)
    | uu____828 -> FStar_Tactics_Effect.return None
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
               (FStar_Reflection_Formula.Eq ,uu____862,y,uu____864) ->
               if FStar_Reflection_Syntax.term_eq x y
               then FStar_Tactics_Builtins.rewrite x_t
               else try_rewrite_equality x bs1
           | uu____871 -> try_rewrite_equality x bs1)
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
               (FStar_Reflection_Formula.Eq ,uu____900,lhs,uu____902) ->
               (match FStar_Reflection_Syntax.inspect lhs with
                | FStar_Reflection_Syntax.Tv_Var uu____904 ->
                    FStar_Tactics_Builtins.rewrite x_t
                | uu____907 -> idtac)
           | uu____910 -> idtac)
          (fun uu___54_915  -> rewrite_all_context_equalities bs1)
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
                  (FStar_Reflection_Formula.Eq ,uu____992,l,r) ->
                  if FStar_Reflection_Syntax.term_eq l t
                  then
                    FStar_Tactics_Effect.bind
                      (FStar_Tactics_Builtins.norm
                         [FStar_Reflection_Syntax.Delta])
                      (fun uu___55_1002  -> FStar_Tactics_Builtins.trefl)
                  else FStar_Tactics_Builtins.trefl
              | uu____1004 -> fail "impossible"))
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
                 (FStar_Reflection_Formula.Eq ,uu____1055,l,uu____1057) ->
                 if FStar_Reflection_Syntax.term_eq l t1
                 then
                   FStar_Tactics_Builtins.exact
                     (FStar_Tactics_Effect.return eq1)
                 else FStar_Tactics_Builtins.trefl
             | uu____1068 -> fail "impossible")
let mk_sq_eq:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term
  =
  fun t1  ->
    fun t2  ->
      FStar_Reflection_Syntax.mk_app
        (FStar_Reflection_Syntax.pack
           (FStar_Reflection_Syntax.Tv_FVar
              (FStar_Reflection_Syntax.pack_fv
                 FStar_Reflection_Syntax.squash_qn)))
        [FStar_Reflection_Syntax.mk_app
           (FStar_Reflection_Syntax.pack
              (FStar_Reflection_Syntax.Tv_FVar
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
                   (FStar_Reflection_Syntax.Tv_Var e))))