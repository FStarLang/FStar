module StringPrinter.Base

(* Ghost Specifications *)

module S = FStar.Seq
module U8 = FStar.UInt8

(* Prims.c_or is not supported by KreMLin, so let's use ours. *)
type c_or   (p:Type) (q:Type) =
  | Left  : p -> c_or p q
  | Right : q -> c_or p q

type string = S.seq U8.t

type m t = (unit -> GTot (t * string))

let ret (#t: Type0) (x: t) : Tot (m t) =
  (fun () -> (x, S.createEmpty))

let s_append (#a: Type) (s1 s2: S.seq a) : Tot (s: S.seq a { S.length s == S.length s1 + S.length s2 } ) =
  S.append s1 s2

let bind (#t1 #t2: Type0) (x: m t1) (y: t1 -> Tot (m t2)) : Tot (m t2) =
  (fun () ->
    match x () with
    (x1, accu1) ->
    match y x1 () with
    (x2, accu2) ->
    (x2, s_append accu1 accu2))

let seq (#t2: Type0) (x: m unit) (y: m t2) : Tot (m t2) =
  bind #unit #t2 x (fun () -> y)

let print_char (c: U8.t) : Tot (m unit) =
  fun () -> ((), S.create 1 c)

let log (#t: Type0) (x: m t) : GTot string = 
  let (_, log) = x () in
  log

(* Pure and Stateful Implementations *)

(* 1: compute the size *)

module U32 = FStar.UInt32

let m_sz_res_pred
  #t (f: m t) (x: t) (r: U32.t) : GTot Type0 =
    match f () with
    (x', log) ->
    x' == x /\
    S.length log == U32.v r

let m_sz_correct
  #t (f: m t) (t' : Type)
    (g: (x: t) -> (r: U32.t) -> (u: unit { m_sz_res_pred f x r }) -> Tot t')
    (g' : (u: unit { S.length (log f) > 4294967295 } ) -> Tot t')
    (y: t')
: GTot Type0
= match f () with
  | (r, log) ->
  let l = S.length log in
  if l > 4294967295
  then y == g' ()
  else y == g r (U32.uint_to_t l) ()
 
type m_sz #t (f: m t) = (
  (t' : Type) ->
  (g: ((x: t) -> (r: U32.t) -> (u: unit { m_sz_res_pred f x r } ) -> Tot t')) -> 
  (g' : ((u: unit { S.length (log f) > 4294967295 } ) -> Tot t')) ->
  Tot (y: t' {
    m_sz_correct f t' g g' y
  }))

inline_for_extraction
let add_overflow (u v: U32.t) : Tot (y: option U32.t {
  if U32.v u + U32.v v < 4294967296
  then (
    Some? y /\ (
    let (Some sz) = y in
    U32.v sz == U32.v u + U32.v v
  ))
  else None? y
})
= if U32.lt (U32.sub 4294967295ul v) u
  then None
  else Some (U32.add u v)

inline_for_extraction
let ret_sz (#t: Type0) (x: t) : Tot (m_sz (ret x)) =
  (fun _ g _ -> g x 0ul ())

let m_sz_res_pred_bind
  (#t1 #t2: Type0)
  (x: m t1)
  (rx: t1)
  (sx: U32.t)
  (y: t1 -> Tot (m t2))
  (ry: t2)
  (sy: U32.t)
: Lemma
  (requires (
    m_sz_res_pred x rx sx /\
    m_sz_res_pred (y rx) ry sy /\
    U32.lt (U32.sub 4294967295ul sy) sx == false
  ))
  (ensures (
    U32.v sx + U32.v sy < 4294967296 /\
    m_sz_res_pred (bind x y) ry (U32.add sx sy)
  ))
= let (rx', logx) = x () in
  let (ry', logy) = y rx () in
  ()

inline_for_extraction
let bind_sz
  (#t1 #t2: Type0)
  (#x: m t1)
  (x_sz: m_sz x)
  (#y: t1 -> Tot (m t2))
  (y_sz: (r: t1) -> Tot (m_sz (y r)))
: Tot (m_sz (bind x y))
= (fun t' g g' ->
   [@inline_let]
   let gx (rx: t1) (sx: U32.t) (u: unit { m_sz_res_pred x rx sx } ) : Tot (res: t' { m_sz_correct (bind x y) t' g g' res } ) =
     [@inline_let]
     let gy (ry: t2) (sy: U32.t) (u: unit { m_sz_res_pred (y rx) ry sy } ) : Tot (res: t' { m_sz_correct (bind x y) t' g g' res } ) =
       [@inline_let]
       let su = U32.sub 4294967295ul sy in
       [@inline_let]
       let c = U32.lt su sx in
       [@inline_let]
       let res =
         if c
         then
           [@inline_let]
           let _ = assert (
             let (rx', logx) = x () in
             let (ry', logy) = y rx () in
             True
           )
           in
           g' ()
         else
           [@inline_let]
           let r = U32.add sx sy in
           [@inline_let]
           let _ = m_sz_res_pred_bind x rx sx y ry sy in
           g ry r ()
       in
       [@inline_let]
       let _ = assert (m_sz_correct (bind x y) t' g g' res) in
       res
     in
     [@inline_let]
     let res = y_sz rx t' gy g' in
     [@inline_let]
     let _ = assert (
       let (_, _) = x () in
       let (_, _) = y rx () in
       m_sz_correct (bind x y) t' g g' res
     ) in
     res
   in
   [@inline_let]
   let res : t' = x_sz t' gx g' in
   [@inline_let]
   let _ = assert (
     let (rx, _) = x () in
     let (_, _) = y rx () in
     m_sz_correct (bind x y) t' g g' res
   )
   in
   res
  )

inline_for_extraction
let seq_sz
  (t2: Type0)
  (x: m unit)
  (x_sz: m_sz x)
  (y: m t2)
  (y_sz: m_sz y)
: Tot (m_sz (seq x y))
= bind_sz x_sz (fun _ -> y_sz)

inline_for_extraction
let print_char_sz
  (c: U8.t)
: Tot (m_sz (print_char c))
= fun _ g _ -> g () 1ul ()

let cond_eq (#t: Type) (lhs rhs: t) : Tot Type0 =
  (u: unit { lhs == rhs } )

inline_for_extraction
let ifthenelse_sz
  (t: Type0)
  (c: bool)
  (ft: (cond_eq true c -> Tot (m t)))
  (ft_sz: ((u: cond_eq true c) -> m_sz (ft u)))
  (ff: (cond_eq false c -> Tot (m t)))
  (ff_sz: (u: cond_eq false c ) -> m_sz (ff u))
: Tot (m_sz (if c then ft () else ff ()))
= fun _ g g' ->
    if c
    then ft_sz () _ g g'
    else ff_sz () _ g g'

inline_for_extraction
let destruct_pair_sz
  (t1: Type0)
  (t2: Type0)
  (t: Type0)
  (x: t1 * t2)
  (f: ((x1: t1) -> (x2: t2) -> cond_eq x (x1, x2) -> Tot (m t)))
  (f_sz: ((x1: t1) -> (x2: t2) -> cond_eq x (x1, x2) -> Tot (m_sz (f x1 x2 ()))))
: Tot (m_sz (let (x1, x2) = x in f x1 x2 ()))
= fun _ g ->
    let (x1, x2) = x in
    f_sz x1 x2 () _ g

inline_for_extraction
let log_size
  (#t: Type0)
  (#f: m t)
  (f_sz: m_sz f)
: Pure (option U32.t)
  (requires True)
  (ensures (fun y ->
    let sz = S.length (log f) in
    if sz > 4294967295
    then y == None
    else (
      Some? y /\ (
      let (Some sz') = y in
      U32.v sz' == sz
  ))))
= f_sz _ (fun _ r _ -> Some r) (fun _ -> None)

module T = FStar.Tactics

let tfail (#a: Type) (s: Prims.string) : T.Tac a =
  T.debug ("Tactic failure: " ^ s);
  T.fail s

let unfold_fv (t: T.fv) : T.Tac T.term =
  let env = T.cur_env () in
  let n = T.inspect_fv t in
  match T.lookup_typ env n with
  | Some s ->
    begin match T.inspect_sigelt s with
    | T.Sg_Let false _ _ def -> def
    | _ -> tfail "Not a non-recursive let definition"
    end
  | _ -> tfail "Definition not found"


module L = FStar.List.Tot

let rec app_head_rev_tail (t: T.term) :
  T.Tac (T.term * list T.argv)
=
  let ins = T.inspect t in
  if T.Tv_App? ins
  then
    let (T.Tv_App u v) = ins in
    let (x, l) = app_head_rev_tail u in
    (x, v :: l)
  else
    (t, [])

let app_head_tail (t: T.term) :
    T.Tac (T.term * list T.argv)
= let (x, l) = app_head_rev_tail t in
  (x, L.rev l)

// GM: This is cool!
let tassert (x: bool) : T.Tac (y: unit { x == true } ) =
  if x then () else (
    let y = quote x in
    tfail ("Tactic assert failure: " ^ T.term_to_string y)
  )

let tm_eq_fvar (t1 t2: T.term) : T.Tac bool =
  match T.inspect t1, T.inspect t2 with
  | T.Tv_FVar f1, T.Tv_FVar f2 ->
    (T.inspect_fv f1 = T.inspect_fv f2)
  | _ -> false

let ret_tm () : T.Tac T.term =
  quote ret

let bind_tm () : T.Tac T.term =
  quote bind

let seq_tm () : T.Tac T.term =
  quote seq

let print_char_tm () : T.Tac T.term =
  quote print_char

inline_for_extraction
let coerce_sz
  (t: Type0)
  (ft1: m t)
  (ft1_sz: m_sz ft1)
  (ft2: m t)
  (u: cond_eq (ft1 ()) (ft2 ()))
: Tot (m_sz ft2)
= fun t' -> ft1_sz t'

let compile_ret
  (ret_sz_tm: T.term)
  (t: T.term)
: T.Tac T.term
= T.debug "compile_ret";
  let (f, ar) = app_head_tail t in
  let test = tm_eq_fvar f (ret_tm ()) in
  tassert test;
  let res = T.mk_app ret_sz_tm ar in
  T.debug (T.term_to_string res);
  res

let compile_bind
  (bind_sz_tm: T.term)
  (env: T.env)
  (ty: T.term)
  (t: T.term)
  (compile: (env' : T.env) -> (ty' : T.term) -> (t' : T.term) -> T.Tac T.term)
: T.Tac T.term
= T.debug "compile_bind";
  let (f, ar) = app_head_tail t in
  let test = tm_eq_fvar f (bind_tm ()) in
  tassert test;
  match ar with
  | [ (t1, _); (t2, _); (x, _); (y, _) ] ->
    begin match T.inspect y with
    | T.Tv_Abs v y' ->
      let x_ = compile env t1 x in
      let (v_, _) = T.inspect_binder v in
      let v' = T.pack (T.Tv_Var v_) in
      let env' = T.push_binder env v in
      let y_ = compile env' t2 y' in
      let res = T.mk_app bind_sz_tm [
       (t1, T.Q_Implicit);
        (t2, T.Q_Implicit);
        (x, T.Q_Implicit);
        (x_, T.Q_Explicit);
        (y, T.Q_Implicit);
        (T.pack (T.Tv_Abs v y_), T.Q_Explicit);
      ]
      in
      T.debug (T.term_to_string res);
      res
    | _ -> tfail ("compile: Not an abstraction: " ^ T.term_to_string y)
    end
  | _ -> tfail ("compile_bind: 4 arguments expected")

let compile_print_char
  (print_char_sz_tm: T.term)
  (t: T.term)
: T.Tac T.term
= T.debug "compile_print_char";
  let (f, ar) = app_head_tail t in
  let test = tm_eq_fvar f (print_char_tm ()) in
  tassert test;
  let res = T.mk_app print_char_sz_tm ar in
  T.debug (T.term_to_string res);
  res

let compile_fvar
  (coerce_sz_tm: T.term)
  (env: T.env)
  (compile: (ty' : T.term) -> (t' : T.term) -> T.Tac T.term)
  (ty: T.term)
  (t: T.term)
: T.Tac T.term
= T.debug ("compile_fvar: " ^ T.term_to_string t);
  let (f, ar) = app_head_tail t in
  T.debug "after app_head_tail";
  let ins = T.inspect f in
  T.debug "after inspect";
  let test = T.Tv_FVar? ins in
  tassert test;
  let (T.Tv_FVar v) = ins in
    let v' = unfold_fv v in
    let t' = T.mk_app v' ar in
    // unfolding might have introduced a redex,
    // so we find an opportunity to reduce it here
    T.debug ("before norm_term: " ^ T.term_to_string t');
    let t' = T.norm_term_env env [iota] t' in // beta implicit
    T.debug "after norm_term";
    let res' = compile ty t' in
    let u = quote () in
    let res = T.mk_app coerce_sz_tm [
      ty, T.Q_Explicit;
      t', T.Q_Explicit;
      res', T.Q_Explicit;
      t, T.Q_Explicit;
      u, T.Q_Explicit;
    ]
    in
    res

let compile_ifthenelse
  (ifthenelse_sz_tm: T.term)
  (ty: T.term)
  (t: T.term)
  (compile: (ty' : T.term) -> (t' : T.term) -> T.Tac T.term)
: T.Tac T.term
= T.debug "compile_ifthenelse";
  let (f, ar) = app_head_tail t in
  let ins = T.inspect f in
  match ins with
  | T.Tv_Match cond [T.Pat_Constant T.C_True, tt; _, tf] ->
    (* ifthenelse: the second branch can be a wildcard or false *)
    let ct = quote (cond_eq true) in
    let ut = T.mk_app ct [cond, T.Q_Explicit] in
    let vt = T.fresh_binder_named "name1eman" ut in
    let ft = T.pack (T.Tv_Abs vt tt) in
    let ft_sz_body = compile ty tt in
    let ft_sz = T.pack (T.Tv_Abs vt ft_sz_body) in
    let cf = quote (cond_eq false) in
    let uf = T.mk_app cf [cond, T.Q_Explicit] in
    let vf = T.fresh_binder_named "name2eman" uf in
    let ff = T.pack (T.Tv_Abs vf tf) in
    let ff_sz_body = compile ty tf in
    let ff_sz = T.pack (T.Tv_Abs vf ff_sz_body) in
    T.mk_app ifthenelse_sz_tm [
      ty, T.Q_Explicit;
      cond, T.Q_Explicit;
      ft, T.Q_Explicit;
      ft_sz, T.Q_Explicit;
      ff, T.Q_Explicit;
      ff_sz, T.Q_Explicit;
    ]
  | _ -> tfail "Not an ifthenelse"

let rec first (#t: Type) (l: list (unit -> T.Tac t)) : T.Tac t =
  match l with
  | [] -> tfail "All tactics failed"
  | a :: q ->
    T.or_else a (fun () -> T.debug "failed"; first q)

let rec compile
  (
    ret_sz_tm
    bind_sz_tm
    print_char_sz_tm
    coerce_sz_tm
    ifthenelse_sz_tm
  : T.term)
  (env: T.env)
  (ty: T.term) (t: T.term)
: T.Tac T.term
= T.debug "BEGIN compile";
  let compile' = compile ret_sz_tm bind_sz_tm print_char_sz_tm coerce_sz_tm ifthenelse_sz_tm in
  let res = first [
    (fun () -> compile_ret ret_sz_tm t);
    (fun () -> compile_bind bind_sz_tm env ty t compile');
    (fun () -> compile_print_char print_char_sz_tm t);
    (fun () -> compile_fvar coerce_sz_tm env (compile' env) ty t);
    (fun () -> compile_ifthenelse ifthenelse_sz_tm ty t (compile' env));
  ]
  in
  T.debug ("END compile, result: " ^ T.term_to_string res);
  res

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
    env
    ty
    t

let unfold_ (#t: Type) (x: t) : T.Tac T.term =
  let open T in
  let u = quote x in
  match inspect u with
  | Tv_FVar v -> unfold_fv v
  | _ -> fail ("unfold_def: Not a free variable: " ^ term_to_string u)

let mk_sz (#ty: Type0) (m: m ty) : T.Tac unit =
  let open T in
    let x = quote m in
    let ty' = quote ty in
    let t = mk_sz' (T.cur_env ()) ty' x in
    exact_guard t

module B = FStar.Buffer
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack

let m_st_post (#t: Type) (f: m t) (b: B.buffer U8.t) (h: HS.mem) (rb': t * B.buffer U8.t) (h': HS.mem) : GTot Type0 =
  B.live h b /\
  S.length (log f) <= B.length b /\ (
    let (r, b') = rb' in
    let (r', log) = f () in
    let sz = U32.uint_to_t (S.length log) in
    let bl = B.sub b 0ul sz in
    r' == r /\
    B.modifies_1 bl h h' /\
    B.as_seq h' bl == log /\
    b' == B.sub b sz (U32.uint_to_t (B.length b - S.length log))
  )

type m_st #t (f: m t) =
  (b: B.buffer U8.t) ->
  HST.Stack (t * B.buffer U8.t)
  (requires (fun h ->
    B.live h b /\
    S.length (log f) <= B.length b
  ))
  (ensures (fun h rb' h' ->
    m_st_post f b h rb' h'
  ))

inline_for_extraction
let ret_st (#t: Type0) (x: t) : Tot (m_st (ret x)) =
  fun b -> (x, b)

module G = FStar.Ghost

#reset-options "--z3rlimit 32 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

inline_for_extraction
let bind_st
  (#t1 #t2: Type0)
  (#x: m t1)
  (x_st: m_st x)
  (#y: t1 -> Tot (m t2))
  (y_st: (r: t1) -> Tot (m_st (y r)))
: Tot (m_st (bind x y))
= fun b ->
  let h = HST.get () in
  let (rx, br_x) = x_st b in
  let hx = HST.get () in
  let (ry, br) = y_st rx br_x in
  let h' = HST.get () in
  let len_bl : G.erased U32.t = G.hide (U32.uint_to_t (B.length b - B.length br)) in
  let len_bl_x : G.erased U32.t = G.hide (U32.uint_to_t (B.length b - B.length br_x)) in
  let bl : G.erased (B.buffer U8.t) = G.hide (B.sub b 0ul (G.reveal len_bl)) in
  let bl_x : G.erased (B.buffer U8.t) = G.hide (B.sub b 0ul (G.reveal len_bl_x)) in
  assert (B.modifies_1 (G.reveal bl_x) h hx);
  assert (G.reveal bl_x == B.sub (G.reveal bl) 0ul (G.reveal len_bl_x));
  assert (B.modifies_1 (G.reveal bl) h hx);
  let len_bl_y : G.erased U32.t = G.hide (U32.uint_to_t (B.length br_x - B.length br)) in
  let bl_y : G.erased (B.buffer U8.t) = G.hide (B.sub br_x 0ul (G.reveal len_bl_y)) in
  assert (B.modifies_1 (G.reveal bl_y) hx h');
  assert (G.reveal bl_y == B.sub (G.reveal bl) (G.reveal len_bl_x) (G.reveal len_bl_y));
  assert (B.modifies_1 (G.reveal bl) hx h');
  assert (B.as_seq h' (G.reveal bl_x) == log x);
  assert (B.as_seq h' (G.reveal bl_y) == log (y (fst (x ()))));
  assert (S.equal (B.as_seq h' (G.reveal bl)) (S.append (B.as_seq h' (G.reveal bl_x)) (B.as_seq h' (G.reveal bl_y))));
  (ry, br)

#reset-options

inline_for_extraction
let seq_st
  (t2: Type0)
  (x: m unit)
  (x_st: m_st x)
  (y: m t2)
  (y_st: m_st y)
: Tot (m_st (seq x y))
= bind_st x_st (fun _ -> y_st)

inline_for_extraction
let print_char_st (c: U8.t) : Tot (m_st (print_char c)) =
  fun b ->
  [@inline_let]
  let b0 = B.sub b 0ul 1ul in
  B.upd b0 0ul c ;
  let b' = B.offset b 1ul in
  let h' = HST.get () in
  assert (Seq.equal (B.as_seq h' b0) (Seq.create 1 c));
  ((), b')

inline_for_extraction
let ifthenelse_st
  (t: Type0)
  (c: bool)
  (ft: (cond_eq true c -> Tot (m t)))
  (ft_st: ((u: cond_eq true c) -> m_st (ft u)))
  (ff: (cond_eq false c -> Tot (m t)))
  (ff_st: (u: cond_eq false c ) -> m_st (ff u))
: Tot (m_st (if c then ft () else ff ()))
= fun b ->
    if c
    then ft_st () b
    else ff_st () b

inline_for_extraction
let coerce_st
  (t: Type0)
  (ft1: m t)
  (ft1_st: m_st ft1)
  (ft2: m t)
  (u: unit { ft1 () == ft2 () } )
: Tot (m_st ft2)
= fun b -> ft1_st b

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
    env
    ty
    t

let mk_st (#ty: Type0) (m: m ty) : T.Tac unit =
  let open T in
    let x = quote m in
    let ty' = quote ty in
    let t = mk_st' (T.cur_env ()) ty' x in
    exact_guard t

// unfold // FAILS if set
let buffer_is_mm (#t: Type) (b: B.buffer t) : GTot bool = HS.is_mm (B.content b)

let buffer_create_mm_post
  (#t: Type)
  (r: HS.rid)
  (h h' : HS.mem)
  (b: B.buffer t)
: GTot Type0
=   b `B.unused_in` h /\
    B.live h' b /\
    B.idx b == 0 /\
    Map.domain (HS.get_hmap h') == Map.domain (HS.get_hmap h) /\
    (HS.get_tip h') == (HS.get_tip h) /\
    HS.modifies (Set.singleton r) h h' /\
    HS.modifies_ref r Set.empty h h' /\
    buffer_is_mm b

let alloc_and_fill_in_post
  (#t: Type0)
  (x: m t)
  (resb: t * B.buffer U8.t)
  (h h' : HS.mem)
: GTot Type0
=   let (res, b) = resb in
    let (res', log) = x () in
    res == res' /\
    buffer_create_mm_post HS.root h h' b /\
    log == B.as_seq h' b

inline_for_extraction
let alloc_and_fill_in
  (#t: Type0)
  (x: m t)
  (x_sz: U32.t)
  (x_st: m_st x)
: HST.ST (t * B.buffer U8.t)
  (requires (fun _ ->
    U32.v x_sz == S.length (log x)
  ))
  (ensures (fun h resb h' ->
    alloc_and_fill_in_post x resb h h'
  ))
= let b = B.rcreate_mm HS.root 42uy x_sz in
  let h1 = HST.get () in
  let (r, _) = x_st b in
  let h2 = HST.get () in
  B.lemma_reveal_modifies_1 b h1 h2;
  (r, b)

let phi_post
  (#t: Type0)
  (x: m t)
  (h: HS.mem)
  (res: option (t * B.buffer U8.t))
  (h' : HS.mem)
: GTot Type0
= if S.length (log x) > 4294967295
  then (res == None /\ h' == h)
  else (Some? res /\ (let (Some rb) = res in alloc_and_fill_in_post x rb h h'))

let phi_t (#t: Type0) (x: m t) : Type =
  unit ->
  HST.ST (option (t * B.buffer U8.t))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    phi_post x h res h'
  ))

unfold
let phi_t_internal
  (#t: Type0)
  (x: m t)
  (h0: HS.mem)
: Tot Type
= (unit -> HST.ST (option (t * B.buffer U8.t)) (requires (fun h -> h == h0)) (ensures (fun _ res h' -> phi_post x h0 res h')))

(* FIXME: the following does not extract to KreMLin. This was an attempt to push the CPS-style down to the effectful code as well, but does not work.

inline_for_extraction
let phi
  (#t: Type0)
  (x: m t)
  (x_sz: m_sz x)
  (x_st: m_st x)
: Tot (phi_t x)
= fun () ->
  let h0 = HST.get () in
  x_sz
//    (phi_t_internal x h0) // does not typecheck
    (unit -> HST.ST (option (t * B.buffer U8.t)) (requires (fun h -> h == h0)) (ensures (fun _ res h' -> phi_post x h0 res h')))
    (fun _ sz u () -> Some (alloc_and_fill_in x sz x_st))
    (fun _ () -> None)
    ()
*)

inline_for_extraction
let phi
  (#t: Type0)
  (x: m t)
  (x_sz: m_sz x)
  (x_st: m_st x)
: Tot (phi_t x)
= fun () ->
  match log_size x_sz with
  | Some sz ->
    Some (alloc_and_fill_in x sz x_st)
  | None -> None

let phi_tac (#ty: Type0) (m: m ty) : T.Tac unit =
  let open T in
    let x = quote m in
    let ty' = quote ty in
    let t_sz = mk_sz' (T.cur_env ()) ty' x in
    let t_st = mk_st' (T.cur_env ()) ty' x in
    let q = quote phi in
    let t = mk_app q [
      ty', Q_Implicit;
      x, Q_Explicit;
      t_sz, Q_Explicit;
      t_st, Q_Explicit;
    ]
    in
    exact_guard t
