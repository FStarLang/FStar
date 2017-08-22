open Prims
let quote_lid:
  FStar_Reflection_Types.name ->
    FStar_Reflection_Types.term FStar_Tactics_Effect.tactic
  =
  fun ns  ->
    FStar_Tactics_Effect.return
      (FStar_Reflection_Basic.pack
         (FStar_Reflection_Data.Tv_FVar (FStar_Reflection_Basic.pack_fv ns)))
let liftM1':
  'a 'b .
    ('a -> 'b FStar_Tactics_Effect.tactic) ->
      'a FStar_Tactics_Effect.tactic -> 'b FStar_Tactics_Effect.tactic
  = fun f  -> fun ma  -> FStar_Tactics_Effect.bind ma (fun a  -> f a)
let liftM1:
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Tactics_Effect.tactic -> 'b FStar_Tactics_Effect.tactic
  = fun f  -> liftM1' (fun x  -> FStar_Tactics_Effect.return (f x))
let liftM2':
  'a 'b 'c .
    ('a -> 'b -> 'c FStar_Tactics_Effect.tactic) ->
      'a FStar_Tactics_Effect.tactic ->
        'b FStar_Tactics_Effect.tactic -> 'c FStar_Tactics_Effect.tactic
  =
  fun f  ->
    fun ma  ->
      fun mb  ->
        FStar_Tactics_Effect.bind ma
          (fun a  -> FStar_Tactics_Effect.bind mb (fun b  -> f a b))
let liftM2:
  'a 'b 'c .
    ('a -> 'b -> 'c) ->
      'a FStar_Tactics_Effect.tactic ->
        'b FStar_Tactics_Effect.tactic -> 'c FStar_Tactics_Effect.tactic
  =
  fun f  -> liftM2' (fun x  -> fun y  -> FStar_Tactics_Effect.return (f x y))
let rec mapM:
  'a 'b .
    ('a -> 'b FStar_Tactics_Effect.tactic) ->
      'a Prims.list -> 'b Prims.list FStar_Tactics_Effect.tactic
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> FStar_Tactics_Effect.return []
      | x::xs ->
          FStar_Tactics_Effect.bind (f x)
            (fun y  ->
               FStar_Tactics_Effect.bind (mapM f xs)
                 (fun ys  -> FStar_Tactics_Effect.return (y :: ys)))
let idtac: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.return ()
let __fail: 'Aa . Prims.string -> 'Aa FStar_Tactics_Effect.__tac =
  fun msg  -> fun s0  -> FStar_Tactics_Effect.Failed (msg, s0)
let fail: 'Aa . Prims.string -> 'Aa FStar_Tactics_Effect.tactic =
  fun msg  -> fun uu____383  -> __fail msg
let or_else:
  'Aa .
    'Aa FStar_Tactics_Effect.tactic ->
      'Aa FStar_Tactics_Effect.tactic -> 'Aa FStar_Tactics_Effect.tactic
  =
  fun t1  ->
    fun t2  ->
      FStar_Tactics_Effect.bind (FStar_Tactics_Builtins.trytac t1)
        (fun r  ->
           match r with
           | FStar_Pervasives_Native.Some x -> FStar_Tactics_Effect.return x
           | FStar_Pervasives_Native.None  -> t2)
let rec repeat:
  'Aa .
    'Aa FStar_Tactics_Effect.tactic ->
      Prims.unit ->
        ('Aa Prims.list,('Aa Prims.list FStar_Tactics_Effect.__result,
                          Obj.t) Prims.l_Forall)
          FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t  ->
    fun uu____497  ->
      FStar_Tactics_Effect.bind (FStar_Tactics_Builtins.trytac t)
        (fun r  ->
           match r with
           | FStar_Pervasives_Native.None  -> FStar_Tactics_Effect.return []
           | FStar_Pervasives_Native.Some x ->
               FStar_Tactics_Effect.bind (repeat t)
                 (fun xs  -> FStar_Tactics_Effect.return (x :: xs))) ()
let repeat1:
  'Aa .
    'Aa FStar_Tactics_Effect.tactic ->
      'Aa Prims.list FStar_Tactics_Effect.tactic
  =
  fun t  ->
    FStar_Tactics_Effect.bind t
      (fun x  ->
         FStar_Tactics_Effect.bind (repeat t)
           (fun xs  -> FStar_Tactics_Effect.return (x :: xs)))
let rec repeatseq:
  'Aa .
    'Aa FStar_Tactics_Effect.tactic ->
      Prims.unit ->
        (Prims.unit,(Prims.unit FStar_Tactics_Effect.__result,Obj.t)
                      Prims.l_Forall)
          FStar_Tactics_Effect._dm4f_TAC_repr
  =
  fun t  ->
    fun uu____640  ->
      FStar_Tactics_Effect.bind
        (FStar_Tactics_Builtins.trytac
           (FStar_Tactics_Builtins.seq
              (FStar_Tactics_Effect.bind t
                 (fun uu___63_656  -> FStar_Tactics_Effect.return ()))
              (repeatseq t)))
        (fun uu___64_662  -> FStar_Tactics_Effect.return ()) ()
let simpl: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.norm
    [FStar_Reflection_Data.Simpl; FStar_Reflection_Data.Primops]
let whnf: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Builtins.norm
    [FStar_Reflection_Data.WHNF; FStar_Reflection_Data.Primops]
let __cut: 'Ab 'Aa . ('Aa -> 'Ab) -> 'Aa -> 'Ab = fun f  -> fun x  -> f x
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
                 (FStar_Reflection_Basic.pack
                    (FStar_Reflection_Data.Tv_App
                       (qq, (t, FStar_Reflection_Data.Q_Explicit))))))
           (fun uu___65_717  -> FStar_Tactics_Builtins.intro))
let rec revert_all:
  FStar_Reflection_Types.binders -> Prims.unit FStar_Tactics_Effect.tactic =
  fun bs  ->
    match bs with
    | [] -> FStar_Tactics_Effect.return ()
    | uu____730::tl1 ->
        FStar_Tactics_Effect.bind FStar_Tactics_Builtins.revert
          (fun uu___66_735  -> revert_all tl1)
let assumption: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_env
    (fun e  ->
       let rec aux bs =
         match bs with
         | [] -> fail "no assumption matches goal"
         | b::bs1 ->
             let t =
               FStar_Reflection_Basic.pack (FStar_Reflection_Data.Tv_Var b) in
             or_else
               (FStar_Tactics_Builtins.exact (FStar_Tactics_Effect.return t))
               (aux bs1) in
       aux (FStar_Reflection_Basic.binders_of_env e))
let destruct_equality_implication:
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Formula.formula,FStar_Reflection_Types.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
      FStar_Tactics_Effect.tactic
  =
  fun t  ->
    match FStar_Reflection_Formula.term_as_formula t with
    | FStar_Reflection_Formula.Implies (lhs,rhs) ->
        (match FStar_Reflection_Formula.term_as_formula' lhs with
         | FStar_Reflection_Formula.Comp
             (FStar_Reflection_Formula.Eq ,uu____805,uu____806,uu____807) ->
             FStar_Tactics_Effect.return
               (FStar_Pervasives_Native.Some
                  ((FStar_Reflection_Formula.term_as_formula' lhs), rhs))
         | uu____818 ->
             FStar_Tactics_Effect.return FStar_Pervasives_Native.None)
    | uu____829 -> FStar_Tactics_Effect.return FStar_Pervasives_Native.None
let rec try_rewrite_equality:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.binders -> Prims.unit FStar_Tactics_Effect.tactic
  =
  fun x  ->
    fun bs  ->
      match bs with
      | [] -> FStar_Tactics_Effect.return ()
      | x_t::bs1 ->
          (match FStar_Reflection_Formula.term_as_formula
                   (FStar_Reflection_Basic.type_of_binder x_t)
           with
           | FStar_Reflection_Formula.Comp
               (FStar_Reflection_Formula.Eq ,uu____867,y,uu____869) ->
               if FStar_Reflection_Basic.term_eq x y
               then FStar_Tactics_Builtins.rewrite x_t
               else try_rewrite_equality x bs1
           | uu____873 -> try_rewrite_equality x bs1)
let rec rewrite_all_context_equalities:
  FStar_Reflection_Types.binders -> Prims.unit FStar_Tactics_Effect.tactic =
  fun bs  ->
    match bs with
    | [] -> FStar_Tactics_Effect.return ()
    | x_t::bs1 ->
        FStar_Tactics_Effect.bind
          (match FStar_Reflection_Formula.term_as_formula
                   (FStar_Reflection_Basic.type_of_binder x_t)
           with
           | FStar_Reflection_Formula.Comp
               (FStar_Reflection_Formula.Eq ,uu____900,lhs,uu____902) ->
               (match FStar_Reflection_Basic.inspect lhs with
                | FStar_Reflection_Data.Tv_Var uu____905 ->
                    FStar_Tactics_Builtins.rewrite x_t
                | uu____906 -> idtac)
           | uu____907 -> idtac)
          (fun uu___67_909  -> rewrite_all_context_equalities bs1)
let rewrite_eqs_from_context: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_env
    (fun e  ->
       rewrite_all_context_equalities
         (FStar_Reflection_Basic.binders_of_env e))
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
                (FStar_Reflection_Basic.binders_of_env e)))
let unfold_point:
  FStar_Reflection_Types.term -> Prims.unit FStar_Tactics_Effect.tactic =
  fun t  ->
    FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_env
      (fun e  ->
         FStar_Tactics_Effect.bind FStar_Tactics_Builtins.cur_goal
           (fun g  ->
              match FStar_Reflection_Formula.term_as_formula g with
              | FStar_Reflection_Formula.Comp
                  (FStar_Reflection_Formula.Eq ,uu____976,l,r) ->
                  if FStar_Reflection_Basic.term_eq l t
                  then
                    FStar_Tactics_Effect.bind
                      (FStar_Tactics_Builtins.norm
                         [FStar_Reflection_Data.Delta])
                      (fun uu___68_982  -> FStar_Tactics_Builtins.trefl)
                  else FStar_Tactics_Builtins.trefl
              | uu____984 -> fail "impossible"))
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
                 (FStar_Reflection_Formula.Eq ,uu____1030,l,uu____1032) ->
                 if FStar_Reflection_Basic.term_eq l t1
                 then
                   FStar_Tactics_Builtins.exact
                     (FStar_Tactics_Effect.return eq1)
                 else FStar_Tactics_Builtins.trefl
             | uu____1036 -> fail "impossible")
let mk_sq_eq:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Reflection_Types.term
  =
  fun t1  ->
    fun t2  ->
      FStar_Reflection_Syntax.mk_e_app
        (FStar_Reflection_Basic.pack
           (FStar_Reflection_Data.Tv_FVar
              (FStar_Reflection_Basic.pack_fv
                 FStar_Reflection_Syntax.squash_qn)))
        [FStar_Reflection_Syntax.mk_e_app
           (FStar_Reflection_Basic.pack
              (FStar_Reflection_Data.Tv_FVar
                 (FStar_Reflection_Basic.pack_fv
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
                (FStar_Reflection_Basic.pack (FStar_Reflection_Data.Tv_Var e))))
let focus:
  'a . 'a FStar_Tactics_Effect.tactic -> 'a FStar_Tactics_Effect.tactic =
  fun f  ->
    FStar_Tactics_Effect.bind
      (FStar_Tactics_Builtins.divide (Prims.parse_int "1") f idtac)
      (fun res  ->
         FStar_Tactics_Effect.return (FStar_Pervasives_Native.fst res))
let rec iseq:
  Prims.unit FStar_Tactics_Effect.tactic Prims.list ->
    Prims.unit FStar_Tactics_Effect.tactic
  =
  fun ts  ->
    match ts with
    | t::ts1 ->
        FStar_Tactics_Effect.bind
          (FStar_Tactics_Builtins.divide (Prims.parse_int "1") t (iseq ts1))
          (fun uu___69_1145  -> FStar_Tactics_Effect.return ())
    | [] -> FStar_Tactics_Effect.return ()