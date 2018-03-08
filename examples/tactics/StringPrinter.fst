module StringPrinter

(* Ghost Specifications *)

module S = FStar.Seq
module U8 = FStar.UInt8

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
  #t (f: m t) (g: (x: t) -> (r: U32.t) -> (u: unit { m_sz_res_pred f x r }) ->
  Tot (option U32.t)) (y: option U32.t)
: GTot Type0
= match f () with
  | (r, log) ->
  let l = S.length log in
  if l > 4294967295
  then y == None
  else y == g r (U32.uint_to_t l) ()
 
type m_sz #t (f: m t) = ((g: ((x: t) -> (r: U32.t) -> (u: unit { m_sz_res_pred f x r } ) -> Tot (option U32.t))) -> Tot (y: option U32.t {
  m_sz_correct f g y
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
  (fun g -> g x 0ul ())

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
= (fun g ->
   [@inline_let]
   let gx (rx: t1) (sx: U32.t) (u: unit { m_sz_res_pred x rx sx } ) : Tot (res: option U32.t { m_sz_correct (bind x y) g res } ) =
     [@inline_let]
     let gy (ry: t2) (sy: U32.t) (u: unit { m_sz_res_pred (y rx) ry sy } ) : Tot (res: option U32.t { m_sz_correct (bind x y) g res } ) =
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
           None
         else
           [@inline_let]
           let r = U32.add sx sy in
           [@inline_let]
           let _ = m_sz_res_pred_bind x rx sx y ry sy in
           g ry r ()
       in
       [@inline_let]
       let _ = assert (m_sz_correct (bind x y) g res) in
       res
     in
     [@inline_let]
     let res = y_sz rx gy in
     [@inline_let]
     let _ = assert (
       let (_, _) = x () in
       let (_, _) = y rx () in
       m_sz_correct (bind x y) g res
     ) in
     res
   in
   [@inline_let]
   let res : option U32.t = x_sz gx in
   [@inline_let]
   let _ = assert (
     let (rx, _) = x () in
     let (_, _) = y rx () in
     m_sz_correct (bind x y) g res
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
= fun g -> g () 1ul ()

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
= fun g ->
    if c
    then ft_sz () g
    else ff_sz () g

inline_for_extraction
let destruct_pair_sz
  (t1: Type0)
  (t2: Type0)
  (t: Type0)
  (x: t1 * t2)
  (f: ((x1: t1) -> (x2: t2) -> cond_eq x (x1, x2) -> Tot (m t)))
  (f_sz: ((x1: t1) -> (x2: t2) -> cond_eq x (x1, x2) -> Tot (m_sz (f x1 x2 ()))))
: Tot (m_sz (let (x1, x2) = x in f x1 x2 ()))
= fun g ->
    let (x1, x2) = x in
    f_sz x1 x2 () g

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
= f_sz (fun _ r _ -> Some r)

module Cast = FStar.Int.Cast

let cast (x: U32.t) : Pure (y: U8.t { U8.v y == U32.v x } ) (requires (U32.v x < 256)) (ensures (fun _ -> True)) =
  Cast.uint32_to_uint8 x

let example (x: U32.t) : Tot (m unit) =
  if U32.lt x 256ul
  then begin
    g <-- ret (cast x) ;
    print_char g
  end else begin
    ret ()
  end

#set-options "--use_two_phase_tc true"

inline_for_extraction
let example_sz (x: U32.t) : Tot (m_sz (example x)) =
  ifthenelse_sz
    _
    (U32.lt x 256ul)
    _
    (fun _ -> bind_sz (ret_sz (cast x)) (fun g -> print_char_sz g))
    _
    (fun _ -> ret_sz ())

(* This should give the same thing as the test function at the very end of this file *)
inline_for_extraction
let test_ (x: U32.t) : Tot (option U32.t) =
  log_size (example_sz x)

module T = FStar.Tactics

// GM: I think you can just use (String.concat ".") for this
let rec string_of_name (x: T.name) : T.Tac Prims.string =
  match x with
  | [] -> T.fail "string_of_name: degenerate case, should not happen"
  | [a] -> a
  | a :: q ->
    let open T in
    a ^ "." ^ string_of_name q

let unfold_fv (t: T.fv) : T.Tac T.term =
  let open T in
  let n = string_of_name (T.inspect_fv t) in
  T.norm_term [Prims.delta_only [n]] (T.pack (T.Tv_FVar t))

module L = FStar.List.Tot

// GM: We might need to make `inspect` an effectful function,
// and then you wouldn't be able to use it in the refinement.
let rec app_head_rev_tail (t: T.term) :
    T.Tac (res: ((x: T.term { ~ (T.Tv_App? (T.inspect x)) }) * list (tl: T.argv { tl << t } ))
                { if Cons? (snd res) then fst res << t else fst res == t } ) =
  match T.inspect t with
  | T.Tv_App u v ->
    let open T in
    let (x, l) = app_head_rev_tail u in
    let res : ((x: T.term { ~ (T.Tv_App? (T.inspect x)) } ) * list (tl: T.argv { tl << t } )) = (x, v :: L.map (fun (x: argv {x << u}) -> (x <: (x: argv { x << t } ))) l) in
    let (res: ((x: T.term { ~ (T.Tv_App? (T.inspect x)) } ) * list (tl: T.argv { tl << t } )) { if Cons? (snd res) then fst res << t else fst res == t } ) = res in
    res
  | _ -> (t, [])

let rev_is_cons (#a: Type) (l: list a) : Lemma
  (requires (Cons? l))
  (ensures (Cons? (L.rev l)))
= L.rev_rev' l

let app_head_tail (t: T.term) :
    T.Tac (res: ((x: T.term { ~ (T.Tv_App? (T.inspect x)) } ) * list (tl: T.argv { tl << t } ))
                { if Cons? (snd res) then fst res << t else fst res == t } ) =
  let open T in
  let (x, l) = app_head_rev_tail t in
  let (res : ((x: T.term { ~ (T.Tv_App? (T.inspect x)) } ) * list (tl: T.argv { tl << t } ))) = (x, L.rev l) in
  Classical.move_requires rev_is_cons l;
  let (res: ((x: T.term { ~ (T.Tv_App? (T.inspect x)) } ) * list (tl: T.argv { tl << t } )) { if Cons? (snd res) then fst res << t else fst res == t } ) = res in
  res

// GM: This is cool!
let tassert (x: bool) : T.Tac (y: unit { x == true } ) =
  if x then () else (
    let open T in
    let y = quote x in
    fail ("Tactic assert failure: " ^ term_to_string y)
  )

let tm_eq_fvar (t1 t2: T.term) : Tot bool =
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

let rec neutralize_argv (t: T.term) (ar: list (x: T.argv { x << t } )) : Tot (list T.argv) =
  match ar with
  | [] -> []
  | a :: q -> a :: neutralize_argv t q

inline_for_extraction
let coerce_sz
  (t: Type0)
  (ft1: m t)
  (ft1_sz: m_sz ft1)
  (ft2: m t)
: Pure (m_sz ft2)
  (requires (ft1 () == ft2 ()))
  (ensures (fun _ -> True))
= fun g -> ft1_sz g

let rec mk_sz (fuel: nat) (ty: T.term) (t: T.term) : T.Tac T.term
  //(decreases (LexCons fuel (LexCons t LexTop)))
=
  let open T in
  admit (); // GM: VC is too hard, admit for now
  let (f, ar) = app_head_tail t in
  let ins = T.inspect f in
  match ins with
  | T.Tv_FVar v -> begin
    print ("Number of arguments: " ^ string_of_int (L.length ar));
    let r = ret_tm () in
    let b = bind_tm () in
    let s = seq_tm () in
    let p = print_char_tm () in
    if tm_eq_fvar f r
    then begin
      print "is RET";
      let ret_sz_tm = quote ret_sz in
      let res = mk_app ret_sz_tm (neutralize_argv t ar) in
      print (term_to_string res);
      res
    end else if tm_eq_fvar f b
    then begin
      print "is BIND";
      match ar with
      | [ (t1, _); (t2, _); (x, _); (y, _) ] ->
        print "4 arguments" ;
        begin match T.inspect y with
        | T.Tv_Abs v y' ->
          let x_ = mk_sz fuel t1 x in
          let v' = pack (T.Tv_Var v) in
          let t2' = mk_app t2 [
            v', Q_Explicit;
          ]
          in
          let y_ = mk_sz fuel t2' y' in
          let bind_sz_tm = quote bind_sz in
          let res = mk_app bind_sz_tm [
            (t1, Q_Implicit);
            (t2, Q_Implicit);
            (x, Q_Implicit);
            (x_, Q_Explicit);
            (y, Q_Implicit);
            (pack (Tv_Abs v y_), Q_Explicit);
          ]
          in
          print (term_to_string res);
          res
        | _ -> fail ("mk_sz: Not an abstraction: " ^ term_to_string y)
        end
      | _ -> fail ("mk_sz: Not the right number of arguments (expected 4, found " ^ string_of_int (L.length ar) ^ ")")
    end else if tm_eq_fvar f p
    then begin
      print "is PRINT_CHAR";
      let print_char_sz_tm = quote print_char_sz in
      let res = mk_app print_char_sz_tm (neutralize_argv t ar) in
      print (term_to_string res) ;
      res
    end else if tm_eq_fvar f s
    then begin
      print "is SEQ";
      match ar with
      | [ (t2, _); (x, _); (y, _) ] ->
        let q = quote unit in
        let x_ = mk_sz fuel q x in
        let y_ = mk_sz fuel t2 y in
        let seq_sz_tm = quote seq_sz in
        let res = mk_app seq_sz_tm [
          (t2, Q_Explicit);
          (x, Q_Explicit);
          (x_, Q_Explicit);
          (y, Q_Explicit);
          (y_, Q_Explicit);
        ]
        in
        print (term_to_string res);
        res
      | _ -> fail ("mk_sz: Not the right number of arguments (expected 3, found " ^ string_of_int (L.length ar) ^ ")")
    end else begin
      print "is something else" ;
      if fuel = 0
      then fail "mk_sz: Not enough unfolding fuel"
      else
        let v' = unfold_fv v in
        let t' = mk_app v' (neutralize_argv t ar) in
        // unfolding might have introduced a redex,
        // so we find an opportunity to reduce it here
        let t' = T.norm_term [Prims.iota] t' in // beta implicit
        let res' = mk_sz (fuel - 1) ty t' in
        let q = quote coerce_sz in
        let res = T.mk_app q [
          ty, T.Q_Explicit;
          t', T.Q_Explicit;
          res', T.Q_Explicit;
          t, T.Q_Explicit;
        ]
        in
        res
    end
  end
  | T.Tv_Match cond [T.Pat_Constant T.C_True, tt; _, tf] ->
    (* ifthenelse: the second branch can be a wildcard or false *)
    let ct = quote (cond_eq true) in
    let ut = T.mk_app ct [cond, T.Q_Explicit] in
    let vt = T.fresh_binder ut in
    let ft = T.pack (T.Tv_Abs vt tt) in
    let ft_sz_body = mk_sz (fuel - 1) ty tt in
    let ft_sz = T.pack (T.Tv_Abs vt ft_sz_body) in
    let cf = quote (cond_eq false) in
    let uf = T.mk_app cf [cond, T.Q_Explicit] in
    let vf = T.fresh_binder uf in
    let ff = T.pack (T.Tv_Abs vf tf) in
    let ff_sz_body = mk_sz (fuel - 1) ty tf in
    let ff_sz = T.pack (T.Tv_Abs vf ff_sz_body) in
    let i = quote ifthenelse_sz in
    T.mk_app i [
      ty, T.Q_Explicit;
      cond, T.Q_Explicit;
      ft, T.Q_Explicit;
      ft_sz, T.Q_Explicit;
      ff, T.Q_Explicit;
      ff_sz, T.Q_Explicit;
    ]
  | _ -> T.fail ("head is not a Tv_FVar, we have instead: " ^ T.term_to_string t)

let unfold_ (#t: Type) (x: t) : T.Tac T.term =
  let open T in
  let u = quote x in
  match inspect u with
  | Tv_FVar v -> unfold_fv v
  | _ -> fail ("unfold_def: Not a free variable: " ^ term_to_string u)

let test_tac (#ty: Type0) (m: m ty) : T.Tac unit =
  let open T in
    let x = quote m in
    let ty' = quote ty in
    let t = mk_sz 2 ty' x in
    exact_guard t

let example0 : (m int) =
  ret 42

(* Works *)
let z0 : m_sz example0 =
  T.synth_by_tactic (fun () -> test_tac example0)

let example0' : (m unit) =
  print_char 128uy

(* Works *)
let z0' : m_sz example0' =
  T.synth_by_tactic (fun () -> test_tac example0')

let example1 : (m unit) =
  seq
    (print_char 42uy)
    (ret ())

(* Works, finally *)
let z1 : m_sz example1 =
  T.synth_by_tactic (fun () -> test_tac example1)

(* The following term is the term printed by the tactic. This works. *)
let z1_ : m_sz example1 =
  seq_sz Prims.unit
  (print_char (FStar.UInt8.uint_to_t 42))
  (print_char_sz (FStar.UInt8.uint_to_t 42))
  (ret ())
  (ret_sz ())

let example2 : (m unit) =
  x <-- ret 18uy ;
  print_char x

let z2 : m_sz example2 =
  T.synth_by_tactic (fun () -> test_tac example2)

let example3 (x: U8.t) : Tot (m unit) =
  y <-- ret (if U8.lt 0uy x then U8.sub x 1uy else x) ;
  print_char y

let z3 (x: U8.t) : Tot (m_sz (example3 x)) =
  T.synth_by_tactic (fun () -> test_tac (example3 x))

inline_for_extraction
let z (x: U32.t) : Tot (m_sz (example x)) =
  T.synth_by_tactic (fun () -> test_tac (example x))

inline_for_extraction
let test (x: U32.t) : Tot (option U32.t) =
  log_size (z x)

module B = FStar.Buffer
module HST = FStar.HyperStack.ST

type m_st #t (f: m t) =
  (b: B.buffer U8.t) ->
  HST.StackInline (t * B.buffer U8.t)
  (requires (fun h ->
    B.live h b /\
    S.length (log f) <= B.length b
  ))
  (ensures (fun h (r, b') h' ->
    let (r', log) = f () in
    let sz = U32.uint_to_t (S.length log) in
    let bl = B.sub b 0ul sz in
    r' == r /\
    B.modifies_1 bl h h' /\
    B.as_seq h' bl == log /\
    b' == B.sub b sz (U32.uint_to_t (B.length b - S.length log))
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

#set-options "--use_two_phase_tc true"
