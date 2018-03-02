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

inline_for_extraction
let ifthenelse_sz
  (#t: Type0)
  (c: bool)
  (#ft: (u: unit { c == true } ) -> Tot (m t))
  (ft_sz: (u: unit { c == true } ) -> m_sz (ft u))
  (#ff: (u: unit { c == false } ) -> Tot (m t))
  (ff_sz: (u: unit { c == false } ) -> m_sz (ff u))
: Tot (m_sz (if c then ft () else ff ()))
= fun g ->
    if c
    then ft_sz () g
    else ff_sz () g

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
    (U32.lt x 256ul)
    (fun _ -> bind_sz (ret_sz (cast x)) (fun g -> print_char_sz g))
    (fun _ -> ret_sz ())

inline_for_extraction
let test (x: U32.t) : Tot (option U32.t) =
  log_size (example_sz x)

module T = FStar.Tactics

let rec string_of_name (x: T.name) : Tot (T.tactic Prims.string) =
  match x with
  | [] -> T.fail "string_of_name: degenerate case, should not happen"
  | [a] -> T.return a
  | a :: q ->
    let open T in
    y <-- string_of_name q ;
    T.return (a ^ "." ^ y)

let unfold_fv (t: T.fv) : Tot (T.tactic T.term) =
  let open T in
  n <-- string_of_name (T.inspect_fv t) ;
  T.norm_term [Prims.delta_only [n]] (T.pack (T.Tv_FVar t))

module L = FStar.List.Tot

let rec app_head_rev_tail (t: T.term) : Tot (T.tactic (res: ((x: T.term { ~ (T.Tv_App? (T.inspect x)) }) * list (tl: T.argv { tl << t } )) { if Cons? (snd res) then fst res << t else fst res == t } )) =
  match T.inspect t with
  | T.Tv_App u v ->
    let open T in
    xl <-- app_head_rev_tail u ;
    let (x, l) = xl in
    let res : ((x: T.term { ~ (T.Tv_App? (T.inspect x)) } ) * list (tl: T.argv { tl << t } )) = (x, v :: L.map (fun (x: argv {x << u}) -> (x <: (x: argv { x << t } ))) l) in
    let (res: ((x: T.term { ~ (T.Tv_App? (T.inspect x)) } ) * list (tl: T.argv { tl << t } )) { if Cons? (snd res) then fst res << t else fst res == t } ) = res in
    return res
  | _ -> T.return (t, [])

let rev_is_cons (#a: Type) (l: list a) : Lemma
  (requires (Cons? l))
  (ensures (Cons? (L.rev l)))
= L.rev_rev' l

let app_head_tail (t: T.term) : Tot (T.tactic (res: ((x: T.term { ~ (T.Tv_App? (T.inspect x)) } ) * list (tl: T.argv { tl << t } )) { if Cons? (snd res) then fst res << t else fst res == t } )) =
  let open T in
  xl <-- app_head_rev_tail t ;
  let (x, l) = xl in
  let (res : ((x: T.term { ~ (T.Tv_App? (T.inspect x)) } ) * list (tl: T.argv { tl << t } ))) = (x, L.rev l) in
  Classical.move_requires rev_is_cons l;
  let (res: ((x: T.term { ~ (T.Tv_App? (T.inspect x)) } ) * list (tl: T.argv { tl << t } )) { if Cons? (snd res) then fst res << t else fst res == t } ) = res in
  return res

let tassert (x: bool) : Tot (T.tactic (y: unit { x == true } )) =
  if x then T.return () else (
    let open T in
    y <-- quote x ;
    fail ("Tactic assert failure: " ^ term_to_string y)
  )

let tm_eq_fvar (t1 t2: T.term) : Tot bool =
  match T.inspect t1, T.inspect t2 with
  | T.Tv_FVar f1, T.Tv_FVar f2 ->
    (T.inspect_fv f1 = T.inspect_fv f2)
  | _ -> false

let ret_tm : T.tactic T.term =
  T.quote ret

let bind_tm : T.tactic T.term =
  T.quote bind

let seq_tm : T.tactic T.term =
  T.quote seq

let print_char_tm : T.tactic T.term =
  T.quote print_char

let rec neutralize_argv (t: T.term) (ar: list (x: T.argv { x << t } )) : Tot (list T.argv) =
  match ar with
  | [] -> []
  | a :: q -> a :: neutralize_argv t q

let rec mk_sz (fuel: nat) (t: T.term) : Tot (T.tactic T.term)
  (decreases (LexCons fuel (LexCons t LexTop)))
=
  let open T in
  far <-- app_head_tail t ;
  let (f, ar) = far in
  let ins = T.inspect f in
  match ins with
  | T.Tv_FVar v ->
    _ <-- print ("Number of arguments: " ^ string_of_int (L.length ar)) ;
    r <-- ret_tm ;
    b <-- bind_tm ;
    s <-- seq_tm ;
    p <-- print_char_tm ;
    if tm_eq_fvar f r
    then begin
      _ <-- print "is RET" ;
      ret_sz_tm <-- quote ret_sz ;
      let res = mk_app ret_sz_tm (neutralize_argv t ar) in
      _ <-- print (term_to_string res) ;
      return res
    end else if tm_eq_fvar f b
    then begin
      _ <-- print "is BIND" ;
      match ar with
      | [ t1; t2; (x, _); (y, _) ] ->
        _ <-- print "4 arguments" ;
        begin match T.inspect y with
        | T.Tv_Abs v y' ->
          x_ <-- mk_sz fuel x ;
          y_ <-- mk_sz fuel y' ;
          bind_sz_tm <-- quote bind_sz ;
          let v' = fresh_binder (type_of_binder v) in
          let res = mk_app bind_sz_tm [
            t1;
            t2;
            (x, Q_Implicit);
            (x_, Q_Explicit);
            (y, Q_Implicit);
            (pack (Tv_Abs v' y_), Q_Explicit);
          ]
          in
          _ <-- print (term_to_string res) ;
          return res
        | _ -> fail ("mk_sz: Not an abstraction: " ^ term_to_string y)
        end
      | _ -> fail ("mk_sz: Not the right number of arguments (expected 4, found " ^ string_of_int (L.length ar) ^ ")")
    end else if tm_eq_fvar f p
    then begin
      _ <-- print "is PRINT_CHAR" ;
      print_char_sz_tm <-- quote print_char_sz ;
      let res = mk_app print_char_sz_tm (neutralize_argv t ar) in
      _ <-- print (term_to_string res) ;
      return res
    end else if tm_eq_fvar f s
    then begin
      _ <-- print "is SEQ" ;
      match ar with
      | [ (t2, _); (x, _); (y, _) ] ->
        x_ <-- mk_sz fuel x ;
        y_ <-- mk_sz fuel y ;
        seq_sz_tm <-- quote seq_sz ;
        let res = mk_app seq_sz_tm [
          (t2, Q_Explicit);
          (x, Q_Explicit);
          (x_, Q_Explicit);
          (y, Q_Explicit);
          (y_, Q_Explicit);
        ]
        in
        _ <-- print (term_to_string res) ;
        return res
      | _ -> fail ("mk_sz: Not the right number of arguments (expected 3, found " ^ string_of_int (L.length ar) ^ ")")
    end else begin
      _ <-- print "is something else" ;
      t' <-- unfold_fv v ;
      if fuel = 0
      then fail "mk_sz: Not enough unfolding fuel"
      else mk_sz (fuel - 1) (mk_app t' (neutralize_argv t ar))
    end
  | _ -> T.fail "head is not a Tv_FVar"

let unfold_ (#t: Type) (x: t) : Tot (T.tactic T.term) =
  let open T in
  u <-- quote x ;
  match inspect u with
  | Tv_FVar v -> unfold_fv v
  | _ -> fail ("unfold_def: Not a free variable: " ^ term_to_string u)

let test_tac (#t: Type0) (m: m t) : Tot (T.tactic unit) =
  let open T in
  x <-- quote m ;
  t <-- mk_sz 2 x ;
  exact_guard (return t)

let example0 : (m int) =
  ret 42

(* Works *)
let z0 : m_sz example0 =
  T.synth_by_tactic (test_tac example0)

let example0' : (m unit) =
  print_char 128uy

(* Works *)
let z0' : m_sz example0' =
  T.synth_by_tactic (test_tac example0')

let example1 : (m unit) =
  seq
    (print_char 42uy)
    (ret ())

(* FAILS:
let z1 : m_sz example1 =
  T.synth_by_tactic (test_tac example1)
*)

(* The following term is the term printed by the tactic. This works. *)
let z1 : m_sz example1 =
  seq_sz Prims.unit
  (print_char (FStar.UInt8.uint_to_t 42))
  (print_char_sz (FStar.UInt8.uint_to_t 42))
  (ret ())
  (ret_sz ())
