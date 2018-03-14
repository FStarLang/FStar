module StringPrinterRecC
include StringPrinterRec

(* This file depends on KreMLin. *)

module Loops = C.Loops
module U32 = FStar.UInt32

type do_while_sz_interm (tin: Type) (tout: Type) =
  | ILeft: U32.t -> tin -> do_while_sz_interm tin tout
  | IRight: U32.t -> tout -> do_while_sz_interm tin tout
  | IOverflow

let do_while_sz_measure
  (tin: Type)
  (tout: Type)
  (decrease: tin -> GTot lex_t)
  (x: do_while_sz_interm tin tout)
: GTot lex_t
= match x with
  | ILeft _ x' -> decrease x'
  | _ -> LexTop

inline_for_extraction
let do_while_sz_continue
  (tin: Type)
  (tout: Type)
  (x: do_while_sz_interm tin tout)
: Tot bool
= ILeft? x

let do_while_sz_inv
  (tin tout: Type)
  (decrease: (tin -> GTot lex_t))
  (body: ((x: tin) -> Tot (y: m (c_or (tin_decr tin decrease x) tout))))
  (x0: tin)
  (continue: bool)
  (x: do_while_sz_interm tin tout)
: GTot Type0
= continue == do_while_sz_continue tin tout x /\ (
    match x with
    | ILeft sz x' ->
      let (y, log) = do_while tin tout decrease body x0 () in
      let (y', log') = do_while tin tout decrease body x' () in
      y == y' /\ Seq.length log == U32.v sz + Seq.length log'
    | IRight sz y' ->
      let (y, log) = do_while tin tout decrease body x0 () in
      y == y' /\ Seq.length log == U32.v sz
    | _ ->
      let (_, log) = do_while tin tout decrease body x0 () in
      Seq.length log > 4294967295
  )

inline_for_extraction
let do_while_sz_body
  (tin tout: Type)
  (decrease: (tin -> GTot lex_t))
  (body: ((x: tin) -> Tot (y: m (c_or (tin_decr tin decrease x) tout))))
  (body_sz: ((x: tin) -> Tot (m_sz (body x))))
  (x0: tin)
  (x: do_while_sz_interm tin tout)
: Pure (do_while_sz_interm tin tout)
  (requires (do_while_sz_inv tin tout decrease body x0 true x))
  (ensures (fun y ->
    do_while_sz_inv tin tout decrease body x0 (do_while_sz_continue tin tout y) y /\ (
    if do_while_sz_continue tin tout y
    then do_while_sz_measure tin tout decrease y << do_while_sz_measure tin tout decrease x
    else True
  )))
= let (ILeft sz_accu x) = x in
  body_sz x
    (do_while_sz_interm tin tout)
    (fun y' sz' h ->
      if U32.sub 4294967295ul sz' `U32.lt` sz_accu
      then IOverflow
      else
        [@inline_let]
        let sz_accu' = U32.add sz_accu sz' in
        match y' with
        | Left x' -> ILeft sz_accu' x'
        | Right y -> IRight sz_accu' y
    )
    (fun h -> IOverflow)

inline_for_extraction
let do_while_sz
  (tin tout: Type)
  (decrease: (tin -> GTot lex_t))
  (body: ((x: tin) -> Tot (y: m (c_or (tin_decr tin decrease x) tout))))
  (body_sz: ((x: tin) -> Tot (m_sz (body x))))
  (x: tin)
 : Tot (m_sz (do_while tin tout decrease body x))
= fun t' g g' ->
  let res =
    Loops.total_while_gen
      #(do_while_sz_interm tin tout)
      (do_while_sz_measure tin tout decrease)
      (do_while_sz_inv tin tout decrease body x)
      (do_while_sz_continue tin tout)
      (fun x' -> do_while_sz_body tin tout decrease body body_sz x x')
      (ILeft 0ul x)
  in
  match res with
  | IRight sz y' -> g y' sz ()
  | IOverflow -> g' ()

module T = FStar.Tactics

let do_while_tm () : T.Tac T.term = quote do_while

let compile_do_while
  (do_while_sz_tm: T.term)
  (env: T.env)
  (t: T.term)
  (compile: (env' : T.env) -> (ty' : T.term) -> (t' : T.term { t' << t } ) -> T.Tac T.term)
: T.Tac T.term
= admit ();
  T.print "compile_do_while";
  let (f, ar) = app_head_tail t in
  let test = tm_eq_fvar f (do_while_tm ()) in
  tassert test;
  match ar with
  | [(tin, _); (tout, _); (decrease, _); (body, _); (x, _)] ->
    let (x', body_) = match T.inspect body with
      | T.Tv_Abs x' body_ -> (x', body_)
      | _ ->
        let x' = T.fresh_binder_named "name4eman" tin in
        let body_ = T.mk_app body [T.pack (T.Tv_Var (T.bv_of_binder x')), T.Q_Explicit] in
        (x', body_)
    in
    let ty' = T.mk_app (quote c_or) [
      T.mk_app (quote tin_decr) [
        tin, T.Q_Explicit;
        decrease, T.Q_Explicit;
        T.pack (T.Tv_Var (T.bv_of_binder x')), T.Q_Explicit;
      ], T.Q_Explicit;
      tout, T.Q_Explicit;
    ]
    in
    let env' = T.push_binder env x' in
    let body_tr = compile env' ty' body_ in
    let body' = T.pack (T.Tv_Abs x' body_tr) in
    let res = T.mk_app (quote do_while_sz) [
      tin, T.Q_Explicit;
      tout, T.Q_Explicit;
      decrease, T.Q_Explicit;
      body, T.Q_Explicit;
      body', T.Q_Explicit;
      x, T.Q_Explicit;
    ]
    in
    res
  | _ -> tfail "compile_do_while expects 5 arguments"

#reset-options "--z3rlimit 32"
  
let rec compile
  (
    ret_sz_tm
    bind_sz_tm
    print_char_sz_tm
    coerce_sz_tm
    ifthenelse_sz_tm
    do_while_sz_tm
  : T.term)
  (env: T.env)
  (fuel: nat) (ty: T.term) (t: T.term)
: T.Tac T.term
  (decreases (LexCons fuel (LexCons t LexTop)))
= T.print "BEGIN compile";
  let compile_term_lt (env' : T.env) (ty' : T.term) (t' : T.term {t' << t}) : T.Tac T.term =
    compile ret_sz_tm bind_sz_tm print_char_sz_tm coerce_sz_tm ifthenelse_sz_tm do_while_sz_tm env' fuel ty' t'
  in
  let compile_fuel_lt (env' : T.env) (ty' : T.term) (t' : T.term) : T.Tac T.term =
    if fuel = 0
    then tfail "Fuel exhausted"
    else compile ret_sz_tm bind_sz_tm print_char_sz_tm coerce_sz_tm ifthenelse_sz_tm do_while_sz_tm env' (fuel - 1) ty' t'
  in
  let res = first [
    (fun () -> compile_ret ret_sz_tm t);
    (fun () -> compile_bind bind_sz_tm env ty t compile_term_lt);
    (fun () -> compile_print_char print_char_sz_tm t);
    (fun () -> compile_do_while do_while_sz_tm env t compile_term_lt);
    (fun () -> compile_fvar coerce_sz_tm env (compile_fuel_lt env) ty t);
    (fun () -> compile_ifthenelse ifthenelse_sz_tm ty t (compile_term_lt env));
  ]
  in
  T.print ("END compile, result: " ^ T.term_to_string res);
  res

#reset-options

let mk_sz
  (env: T.env)
  (fuel: nat) (ty: T.term) (t: T.term)
: T.Tac T.term
= compile
    (quote ret_sz)
    (quote bind_sz)
    (quote print_char_sz)
    (quote coerce_sz)
    (quote ifthenelse_sz)
    (quote do_while_sz)
    env
    fuel
    ty
    t

let test_tac (#ty: Type0) (m: m ty) : T.Tac unit =
  let open T in
    let x = quote m in
    let ty' = quote ty in
    let t = mk_sz (T.cur_env ()) 4 ty' x in
    exact_guard t

#reset-options "--print_bound_var_types --print_implicits"

let dw (x: U32.t) : Tot (m unit) =
  do_while
    _
    _
    (fun _ -> LexTop)
    (fun x -> ret (Right ()))
    x

let dw_sz (x: U32.t) : Tot (m_sz (dw x)) =
  T.synth_by_tactic (fun () -> test_tac (dw x))

let example_sz (x: U32.t) : Tot (m_sz (example x)) =
  coerce_sz
    _
    (example_do_while x)
    (T.synth_by_tactic (fun () -> test_tac (example_do_while x)))
    (example x)
    ()
