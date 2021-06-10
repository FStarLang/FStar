(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module StringPrinter.Rec
include StringPrinter.Base

module T = FStar.Tactics

module Ca = FStar.Int.Cast
module U32 = FStar.UInt32

let tin_decr
  (#a:Type)
  (tin: Type)
  (dec: tin -> GTot a)
  (x: tin)
: Tot Type
= (x' : tin { dec x' << dec x } )

let do_while_body_post
  (#a:Type)
  (tin tout: Type)
  (dec: tin -> GTot a)
  (f: ((x: tin) -> Tot (m tout)))
  (x: tin)
  (y: m (c_or (tin_decr tin dec x) tout))
: GTot Type0
= f x () == bind y (fun (y' : c_or (tin_decr tin dec x) tout) -> begin match y' with
  | Left x' -> f x'
  | Right y' -> ret y'
  end) ()

let do_while_body_res_t
  (#a:Type)
  (tin tout: Type)
  (f: ((x: tin) -> Tot (m tout)))
  (dec: tin -> GTot a)
  (x: tin)
: Tot Type
= (y: m (c_or (tin_decr tin dec x) tout) { do_while_body_post tin tout dec f x y } )

let do_while_body_t'
  (#a:Type)
  (tin tout: Type)
  (f: ((x: tin) -> Tot (m tout)))
  (dec: tin -> GTot a)
: Tot Type
= (x: tin) ->
  Tot (do_while_body_res_t tin tout f dec x)

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

let rec mk_do_while_body
  (tin tout: T.term)
  (t: T.term)
  (f: T.fv)
: T.Tac T.term
= let (t', ar) = app_head_tail t in
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
  | T.Tv_Match cond ret_opt [T.Pat_Constant T.C_True, tt; pat, tf] ->
    (* ifthenelse: the second branch can be a wildcard or false *)
    let tt' = mk_do_while_body tin tout tt f in
    let tf' = mk_do_while_body tin tout tf f in
    T.pack (T.Tv_Match cond ret_opt [T.Pat_Constant T.C_True, tt'; pat, tf'])
  | _ -> T.fail "mk_do_while_body: unsupported"

let do_while_body_res_intro
  (#a:Type)
  (tin tout: Type)
  (f: ((x: tin) -> Tot (m tout)))
  (dec: tin -> GTot a)
  (x: tin)
  (y: m (c_or (tin_decr tin dec x) tout))
: Pure (do_while_body_res_t tin tout f dec x)
  (requires (do_while_body_post tin tout dec f x y))
  (ensures (fun y' -> y' == y))
= y

let rec do_while
  (#a:Type)
  (tin tout: Type)
  (decrease: tin -> GTot a)
  (body: ((x: tin) -> Tot (m (c_or (tin_decr tin decrease x) tout))))
  (x: tin)
: Tot (m tout)
  (decreases (decrease x))
= bind (body x) (fun (y' : c_or (tin_decr tin decrease x) tout) -> match y' with
  | Left x' -> do_while tin tout decrease body x'
  | Right y' -> ret y'
  )

let rec do_while_correct
  (#a:Type)
  (tin tout: Type)
  (f: ((x: tin) -> Tot (m tout)))
  (decrease: tin -> GTot a)
  (body: do_while_body_t' tin tout f decrease)
  (x: tin)
: Lemma
  (requires True)
  (ensures (
    do_while tin tout decrease body x () == f x ()
  ))
  (decreases (decrease x))
= let g : m (c_or (tin_decr tin decrease x) tout) = body x in
  match g () with
  | (Left x', log) -> do_while_correct tin tout f decrease body x'
  | (Right y, log) -> ()

(* This pattern is necessary to prove rewrite_do_while below *)
private let seq_append_empty_l
  (s: Seq.seq FStar.UInt8.t)
: Lemma
  (ensures (Seq.append Seq.empty s == s))
  [SMTPat (Seq.append Seq.empty s)]
= Seq.append_empty_l s

let rewrite_do_while
  (#a:Type)
  (tin tout: Type)
  (f: ((x: tin) -> Tot (m tout)))
  (decrease: tin -> GTot a)
  (body: do_while_body_t' tin tout f decrease)
  (x: tin)
: Tot (y: m tout { y () == f x () } )
= bind (ret (do_while_correct tin tout f decrease body x)) (fun _ -> do_while tin tout decrease body x)

let mk_do_while (#t: Type) (x: t) : T.Tac unit =
    let q = quote x in
    match T.inspect q with
    | T.Tv_FVar v ->
      let env = T.cur_env () in
      let n = T.inspect_fv v in
      begin match T.lookup_typ env n with
      | Some s ->
        begin match T.inspect_sigelt s with
        | T.Sg_Let true _ _ ty tm ->
          begin match T.inspect ty with
          | T.Tv_Arrow tin' tout' ->
            begin match T.inspect_comp tout' with
            | T.C_GTotal _ _ -> T.fail "C_GTotal"
            | T.C_Eff _ _ _ _ -> T.fail "C_Eff"
            | T.C_Total tout_ decr ->
              begin match T.inspect tout_ with
              | T.Tv_App m_tm (tout, T.Q_Explicit) ->
                if tm_eq_fvar m_tm (quote m)
                then
                  begin match T.inspect tm with
                  | T.Tv_Abs x body ->
                    let tin = T.type_of_binder tin' in
                    let decr_body = match decr with
                      | [t] -> t
                      | _ -> T.pack (T.Tv_Var (T.bv_of_binder tin')) in
                    let decr_body_t = T.fresh_uvar None in
                    let decr = T.pack (T.Tv_Abs tin' decr_body) in
                    let decr_ty = T.pack (T.Tv_Arrow tin' (T.pack_comp (T.C_Total decr_body_t []))) in
                    let decr_binder = T.fresh_binder decr_ty in
                    let x_tm = T.pack (T.Tv_Var (T.bv_of_binder x)) in
                    let tin_decr = T.mk_app (quote tin_decr) [
                      decr_body_t, T.Q_Implicit;
                      tin, T.Q_Explicit;
                      decr, T.Q_Explicit;
                      x_tm, T.Q_Explicit;
                    ]
                    in
                    let body_pre_coerce = mk_do_while_body tin_decr tout body v in
                    let body' = T.mk_app (quote do_while_body_res_intro) [
                      tin, T.Q_Explicit;
                      tout, T.Q_Explicit;
                      q, T.Q_Explicit;
                      decr, T.Q_Explicit;
                      x_tm, T.Q_Explicit;
                      body_pre_coerce, T.Q_Explicit;
                    ]
                    in
                    let res =
                      T.mk_app (quote rewrite_do_while) [
                        tin, T.Q_Explicit;
                        tout, T.Q_Explicit;
                        q, T.Q_Explicit;
                        decr, T.Q_Explicit;
                        T.pack (T.Tv_Abs x body'), T.Q_Explicit;
                      ]
                    in
                    T.debug (T.term_to_string res);
                    T.exact_guard res
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

(* This pattern is necessary to prove do_while_body_post *)
let seq_append_empty_r
  (s: Seq.seq FStar.UInt8.t)
: Lemma
  (ensures (Seq.append s Seq.empty == s))
  [SMTPat (Seq.append s Seq.empty)]
= Seq.append_empty_r s
