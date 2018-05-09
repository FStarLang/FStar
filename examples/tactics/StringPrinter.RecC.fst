module StringPrinter.RecC
include StringPrinter.Rec

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

module B = FStar.Buffer
module G = FStar.Ghost
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U8 = FStar.UInt8

noeq
type do_while_st_interm (tin tout: Type) = {
  do_while_st_interm_res: c_or tin tout;
  do_while_st_interm_log: B.buffer U8.t;
}

inline_for_extraction
let do_while_st_inv
  (tin tout: Type)
  (decrease: (tin -> GTot lex_t))
  (body: ((x: tin) -> Tot (y: m (c_or (tin_decr tin decrease x) tout))))
  (h0: G.erased HS.mem)
  (x0: tin)
  (blog: B.buffer U8.t)
  (binterm: B.buffer (do_while_st_interm tin tout))
  (h: HS.mem)
  (interrupt: bool)
: GTot Type0
= let (y0, log0) = do_while tin tout decrease body x0 () in
  B.disjoint binterm blog /\
  B.live (G.reveal h0) binterm /\
  B.live (G.reveal h0) blog /\
  B.live h binterm /\
  B.live h blog /\
  B.length binterm == 1 /\
  Seq.length log0 <= B.length blog /\ (
    let interm = B.get h binterm 0 in
    let bout = interm.do_while_st_interm_log in
    B.length bout <= B.length blog /\ (
    let blhs = B.length blog - B.length bout in
    let blhs32 = U32.uint_to_t blhs in
    B.modifies_2 (B.sub blog 0ul blhs32) binterm (G.reveal h0) h /\
    bout == B.sub blog blhs32 (U32.uint_to_t (B.length bout)) /\ (
    match interm.do_while_st_interm_res with
    | Left x ->
      interrupt == false /\ (
      let (y, log) = do_while tin tout decrease body x () in
      y0 == y /\
      log0 = Seq.append (Seq.slice (B.as_seq h blog) 0 blhs) log /\
      Seq.length log <= B.length bout
      )
    | Right y ->
      interrupt == true /\
      y0 == y /\
      log0 == Seq.slice (B.as_seq h blog) 0 blhs
  )))

#reset-options "--z3rlimit 128 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

inline_for_extraction
let do_while_st_body
  (tin tout: Type)
  (decrease: (tin -> GTot lex_t))
  (body: ((x: tin) -> Tot (y: m (c_or (tin_decr tin decrease x) tout))))
  (body_st: ((x: tin) -> Tot (m_st (body x))))
  (h0: G.erased HS.mem)
  (x0: tin)
  (blog: B.buffer U8.t)
  (binterm: B.buffer (do_while_st_interm tin tout))
: HST.Stack bool
  (requires (fun h ->
    do_while_st_inv tin tout decrease body h0 x0 blog binterm h false
  ))
  (ensures (fun _ b h ->
    do_while_st_inv tin tout decrease body h0 x0 blog binterm h b
  ))
= let h1 = HST.get () in
  let interm = B.index binterm 0ul in
  let bout = interm.do_while_st_interm_log in
  let (Left x) = interm.do_while_st_interm_res in
  let (res', bout') = body_st x bout in
  let h2 = HST.get () in
  let res = match res' with | Left x' -> Left (x' <: tin) | Right y -> Right y in
  B.upd binterm 0ul ({
    do_while_st_interm_res = res;
    do_while_st_interm_log = bout';
  });
  let b = Right? res in
  let h = HST.get () in
  let prf () : Lemma
    (do_while_st_inv tin tout decrease body h0 x0 blog binterm h b)
  = let (y0, log0) = do_while tin tout decrease body x0 () in
    let bout_pre = bout in
    let interm = B.get h binterm 0 in
    let bout = interm.do_while_st_interm_log in
    assert (B.length bout <= B.length blog);
    let blhs = B.length blog - B.length bout in
    let blhs32 = U32.uint_to_t blhs in
    assert (bout == B.sub blog blhs32 (U32.uint_to_t (B.length bout)));
    let bl = B.sub blog 0ul blhs32 in
    let blhs_pre = B.length blog - B.length bout_pre in
    let blhs_pre32 = U32.uint_to_t blhs_pre in
    let bout_pre_l32 = U32.uint_to_t (B.length bout_pre - B.length bout) in
    let bl_pre = B.sub blog 0ul blhs_pre32 in
    assert (bl_pre == B.sub bl 0ul blhs_pre32);
    assert (B.modifies_2 bl_pre binterm (G.reveal h0) h1);
    assert (B.includes bl bl_pre);
    B.modifies_subbuffer_2 (G.reveal h0) h1 bl_pre binterm bl;
    let bout_pre_l = B.sub bout_pre 0ul bout_pre_l32 in
    assert (bout_pre_l == B.sub bl blhs_pre32 bout_pre_l32);
    assert (B.modifies_1 bout_pre_l h1 h2);
    B.modifies_subbuffer_1 h1 h2 bout_pre_l bl;
    B.lemma_modifies_2_1 bl binterm (G.reveal h0) h1 h2;
    B.lemma_modifies_2_1 binterm bl (G.reveal h0) h2 h;
    assert (B.modifies_2 bl binterm (G.reveal h0) h);
    Seq.lemma_split (B.as_seq h bl) blhs_pre;
    match interm.do_while_st_interm_res with
      | Left x ->
        assert (b == false);
        let (y, log) = do_while tin tout decrease body x () in
        assert (y0 == y);
        Seq.append_assoc (Seq.slice (B.as_seq h bl) 0 blhs_pre) (Seq.slice (B.as_seq h bl) blhs_pre blhs) log;
        assert (log0 == Seq.append (Seq.slice (B.as_seq h blog) 0 blhs) log);
        assert (Seq.length log <= B.length bout);
        assert (do_while_st_inv tin tout decrease body h0 x0 blog binterm h b)
      | Right y ->
        assert (y0 == y);
        assert (b == true);
        assert (do_while_st_inv tin tout decrease body h0 x0 blog binterm h b)
  in
  prf ();
  b

#reset-options "--z3rlimit 64 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

inline_for_extraction
let do_while_st
  (tin tout: Type)
  (decrease: (tin -> GTot lex_t))
  (body: ((x: tin) -> Tot (y: m (c_or (tin_decr tin decrease x) tout))))
  (body_st: ((x: tin) -> Tot (m_st (body x))))
  (x: tin)
: Tot (m_st (do_while tin tout decrease body x))
= fun blog ->
  let h0 = HST.get () in
  HST.push_frame ();
  let binterm = B.create
    ({
      do_while_st_interm_res = Left x;
      do_while_st_interm_log = blog;
    })
    1ul
  in
  let h1 = G.hide (HST.get ()) in
  Loops.do_while
    (do_while_st_inv tin tout decrease body h1 x blog binterm)
    (fun () -> do_while_st_body tin tout decrease body body_st h1 x blog binterm);
  let interm = B.index binterm 0ul in
  let (Right y) = interm.do_while_st_interm_res in
  let res = (y, interm.do_while_st_interm_log) in
  HST.pop_frame ();
  let h = HST.get () in
  res

#reset-options

module T = FStar.Tactics

let do_while_tm () : T.Tac T.term = quote do_while

let compile_do_while
  (do_while_sz_tm: T.term)
  (env: T.env)
  (t: T.term)
  (compile: (env' : T.env) -> (ty' : T.term) -> (t' : T.term) -> T.Tac T.term)
: T.Tac T.term
= T.debug "compile_do_while";
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
    let res = T.mk_app do_while_sz_tm [
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
  (ty: T.term) (t: T.term)
: T.Tac T.term
= T.debug "BEGIN compile";
  let compile' = compile ret_sz_tm bind_sz_tm print_char_sz_tm coerce_sz_tm ifthenelse_sz_tm do_while_sz_tm in
  let res = first [
    (fun () -> compile_ret ret_sz_tm t);
    (fun () -> compile_bind bind_sz_tm env ty t compile');
    (fun () -> compile_print_char print_char_sz_tm t);
    (fun () -> compile_do_while do_while_sz_tm env t compile');
    (fun () -> compile_fvar coerce_sz_tm env (compile' env) ty t);
    (fun () -> compile_ifthenelse ifthenelse_sz_tm ty t (compile' env));
  ]
  in
  T.debug ("END compile, result: " ^ T.term_to_string res);
  res

#reset-options

let mk_sz'
  (env: T.env)
  (ty: T.term) (t: T.term)
: T.Tac T.term
= compile
    (quote ret_sz)
    (quote bind_sz)
    (quote print_char_sz)
    (quote coerce_sz)
    (quote ifthenelse_sz)
    (quote do_while_sz)
    env
    ty
    t

let mk_sz (#ty: Type0) (m: m ty) : T.Tac unit =
  let open T in
    let x = quote m in
    let ty' = quote ty in
    let t = mk_sz' (T.cur_env ()) ty' x in
    exact_guard t

let mk_st'
  (env: T.env)
  (ty: T.term) (t: T.term)
: T.Tac T.term
= compile
    (quote ret_st)
    (quote bind_st)
    (quote print_char_st)
    (quote coerce_st)
    (quote ifthenelse_st)
    (quote do_while_st)
    env
    ty
    t

let mk_st (#ty: Type0) (m: m ty) : T.Tac unit =
  let open T in
    let x = quote m in
    let ty' = quote ty in
    let t = mk_st' (T.cur_env ()) ty' x in
    exact_guard t
