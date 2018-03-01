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

inline_for_extraction
let example_sz (x: U32.t) : Tot (m_sz (example x)) =
  [@inline_let]
  let c = U32.lt x 256ul in
  ifthenelse_sz
    (U32.lt x 256ul)
    #(fun (u: unit { c == true } ) -> g <-- ret (cast x) ; print_char g)
    (fun (u: unit { c == true } ) ->
      [@inline_let]
      let p = ret (cast x) in
      [@inline_let]
      let r : m_sz p = ret_sz (cast x) in
      bind_sz r (fun g ->
      print_char_sz g
    ))
    #(fun (u: unit { c == false } ) -> ret ())
    (fun (u: unit { c == false } ) -> ret_sz ())

inline_for_extraction
let test (x: U32.t) : Tot (option U32.t) =
  log_size (example_sz x)
