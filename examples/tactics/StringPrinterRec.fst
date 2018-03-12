module StringPrinterRec
include StringPrinter

(* NOTE: This file requires KreMLin. DO NOT include it in F* CI *)

module Loops = C.Loops
module T = FStar.Tactics

module Ca = FStar.Int.Cast
module U32 = FStar.UInt32

let rec example (x: U32.t) : Tot (m unit) (decreases (U32.v x)) =
  _ <-- print_char (Ca.uint32_to_uint8 x) ;
  if U32.lt x 256ul
  then ret ()
  else example (U32.div x 256ul)

let _ = T.assert_by_tactic True (fun () ->
  let q = quote (let f (x: nat) : Tot unit (decreases x) = () in f) in
  T.print (T.term_to_string q)
)

let do_while_body_post
  (tin tout: Type)
  (f: ((x: tin) -> Tot (m tout)))
  (x: tin)
  (y: m (c_or tin tout))
: GTot Type0
= f x () == bind y (fun y' -> begin match y' with
  | Left x' -> f x'
  | Right y' -> ret y'
  end) ()

let do_while_body_decreases
  (tin tout: Type)
  (decreases: (tin -> GTot lex_t))
  (x: tin)
  (y: m (c_or tin tout))
: GTot Type0
= match y () with
  | (Left x', _) -> decreases x' << decreases x
  | _ -> True

unfold
let do_while_body_res_t
  (tin tout: Type)
  (f: ((x: tin) -> Tot (m tout)))
  (decreases: (tin -> GTot lex_t))
  (x: tin)
: Tot Type
= (y: m (c_or tin tout) { do_while_body_post tin tout f x y /\ do_while_body_decreases tin tout decreases x y } )

let do_while_body_t
  (tin tout: Type)
  (f: ((x: tin) -> Tot (m tout)))
  (decreases: (tin -> GTot lex_t))
: Tot Type
= (x: tin) ->
  GTot (do_while_body_res_t tin tout f decreases x)

let lift_c_or
  (tin tout: Type)
  (x: m tout)
: Tot (m (c_or tin tout))
= bind x (fun x' -> ret (Right x'))

let ret_left
  (tin tout: Type)
  (x: tin)
: Tot (m (c_or tin tout))
= ret (Left x)

#set-options "--z3rlimit 32"

let rec mk_do_while_body
  (tin tout: T.term)
  (t: T.term)
  (f: T.fv)
: T.Tac T.term
//  (decreases t)
= 
  admit ();
  let (t', ar) = app_head_tail t in
  let ins = T.inspect t' in
  let tty = T.mk_app (quote c_or) [
    tin, T.Q_Explicit;
    tout, T.Q_Explicit;
  ]
  in
  match ins with
  | T.Tv_FVar v ->
    if T.inspect_fv v = T.inspect_fv f
    then
    begin match ar with
    | [x, T.Q_Explicit] ->
      T.mk_app (quote ret_left) [
        tin, T.Q_Explicit;
        tout, T.Q_Explicit;
        x, T.Q_Explicit
      ]
    | _ -> T.fail "mk_do_while_body: only supports recursive functions with 1 argument"
    end
    else if tm_eq_fvar t' (bind_tm ())
    then
      match ar with
      | [ (t1, _); _; (x, _); (y, _) ] ->
        begin match T.inspect y with
        | T.Tv_Abs v y' ->
          let y_ = mk_do_while_body tin tout y' f in
          T.mk_app (bind_tm ()) [
            (t1, T.Q_Implicit);
            (tty, T.Q_Implicit);
            (x, T.Q_Explicit);
            (T.pack (T.Tv_Abs v y_), T.Q_Explicit);
          ]
        | _ -> T.fail "Not an abstraction"
        end
      | _ -> T.fail "Not the right number of arguments to bind"
    else
      T.mk_app (quote (lift_c_or)) [
        tin, T.Q_Explicit;
        tout, T.Q_Explicit;
        t, T.Q_Explicit
      ]
  | T.Tv_Match cond [T.Pat_Constant T.C_True, tt; pat, tf] ->
    (* ifthenelse: the second branch can be a wildcard or false *)
    let tt' = mk_do_while_body tin tout tt f in
    let tf' = mk_do_while_body tin tout tf f in
    T.pack (T.Tv_Match cond [T.Pat_Constant T.C_True, tt'; pat, tf'])
  | _ -> T.fail "mk_do_while_body: unsupported"

// let unfold_rec_fv (t: T.fv) : T.Tac T.term =

let rec example' (x: nat) : Tot (m unit) =
  _ <-- print_char 25uy ;
  if x < 256
  then ret ()
  else example' (x / 256)

let mk_do_while_body_tac (#t: Type) (x: t) : T.Tac unit =
    let q = quote x in
    match T.inspect q with
    | T.Tv_FVar v ->
      let env = T.cur_env () in
      let n = T.inspect_fv v in
      begin match T.lookup_typ env n with
      | Some s ->
        begin match T.inspect_sigelt s with
        | T.Sg_Let true _ ty tm ->
          begin match T.inspect ty with
          | T.Tv_Arrow tin' tout' ->
            begin match T.inspect_comp tout' with
            | T.C_Unknown -> T.fail "UNKNOWN"
            | T.C_Total tout_ decr ->
              begin match T.inspect tout_ with
              | T.Tv_App m_tm (tout, T.Q_Explicit) ->
                if tm_eq_fvar m_tm (quote m)
                then
                  begin match T.inspect tm with
                  | T.Tv_Abs x body ->
                    let tin = T.type_of_binder tin' in
                    let body' = mk_do_while_body tin tout body v in
                    T.print (T.term_to_string body');
                    // let y = T.fresh_binder (T.mk_app (quote do_while_body_res_t) [
                    // ])
                    // in
                    T.exact_guard (T.pack (T.Tv_Abs x body'))
                  | _ -> T.fail "KO 1"
                  end
                else
                  T.fail "KO 2"
              | _ -> T.fail "KO 3"
              end
            | _ -> T.fail "KO 4"
            end
          | _ -> T.fail "KO 5"
          end
        | _ -> T.fail "KO 6"
        end
      | _ -> T.fail "KO 7"
      end
    | _ -> T.fail "KO 8"

#set-options "--print_implicits --print_bound_var_types --z3rlimit 64 --max_fuel 8 --max_ifuel 8"

(* This pattern is necessary to prove do_while_body_post *)
private let seq_append_empty_r
  (s: Seq.seq FStar.UInt8.t)
: Lemma
  (ensures (Seq.append s Seq.createEmpty == s))
  [SMTPat (Seq.append s Seq.createEmpty)]
= Seq.append_empty_r s

let example'_body // : do_while_body_t nat unit example' (fun (x: nat) -> x) =
: (x: nat) -> Tot (m (c_or nat unit)) =
  T.synth_by_tactic (fun () -> mk_do_while_body_tac example' )

let example'_body_prf (x: nat) : Tot unit =
  let y = example'_body x in
  let f = example' in
  assert (do_while_body_post nat unit example' x (example'_body x));
  assert (do_while_body_decreases nat unit (fun x -> LexCons x LexTop) x (example'_body x))
