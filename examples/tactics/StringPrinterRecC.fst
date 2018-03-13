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
