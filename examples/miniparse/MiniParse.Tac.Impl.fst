module MiniParse.Tac.Impl
include MiniParse.Impl.Combinators
include MiniParse.Impl.Int

module T = FStar.Tactics
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

let tfail (#a: Type) (s: Prims.string) : T.Tac a =
  T.debug ("Tactic failure: " ^ s);
  T.fail s

let unfold_fv (t: T.fv) : T.Tac T.term =
  let env = T.cur_env () in
  let n = T.inspect_fv t in
  match T.lookup_typ env n with
  | Some s ->
    begin match T.inspect_sigelt s with
    | T.Sg_Let false _ _ _ def -> def
    | _ -> tfail "Not a non-recursive let definition"
    end
  | _ -> tfail "Definition not found"

let unfold_term (t: T.term) : T.Tac T.term =
  match T.inspect t with
  | T.Tv_FVar v -> unfold_fv v
  | _ -> tfail "Not a global variable"

(* Generate the parser implementation from the parser specification *)

let rec gen_parser32' (p: T.term) : T.Tac T.term =
  let (hd, tl) = app_head_tail p in
  if hd `T.term_eq` (`(parse_ret))
  then begin
    T.mk_app (`(parse32_ret)) tl
  end else
  if hd `T.term_eq` (`(parse_u8))
  then begin
    (`(parse32_u8))
  end else
  if hd `T.term_eq` (`(nondep_then))
  then match tl with
  | [k1; t1; (p1, _); k2; t2; (p2, _)] ->
    let p1' = gen_parser32' p1 in
    let p2' = gen_parser32' p2 in
    T.mk_app (`(parse32_nondep_then)) [
      k1;
      t1;
      (p1, T.Q_Implicit);
      (p1', T.Q_Explicit);
      k2;
      t2;
      (p2, T.Q_Implicit);
      (p2', T.Q_Explicit);
    ]
  | _ -> tfail "Not enough arguments to nondep_then"
  else
  if hd `T.term_eq` (`(parse_synth))
  then match tl with
  | [k; qt1; t2; qp1; qf2] ->
    let (p1, _) = qp1 in
    let (t1, _) = qt1 in
    let (f2, _) = qf2 in
    let bx = T.fresh_binder t1 in
    let x = T.pack (T.Tv_Var (T.bv_of_binder bx)) in
    let f2' = T.pack (T.Tv_Abs bx (T.mk_app f2 [x, T.Q_Explicit])) in
    let p1' = gen_parser32' p1 in
    T.mk_app (`(parse32_synth)) [
      k;
      qt1;
      t2;
      qp1;
      qf2;
      (f2', T.Q_Explicit);
      (p1', T.Q_Explicit);
      ((`()), T.Q_Explicit);
    ]
  | _ -> tfail "Not enough arguments to synth"
  else
  if L.length tl = 0
  then begin
    gen_parser32' (unfold_term p)
  end else
    tfail "Unknown parser combinator"

let p = parse_u8 `nondep_then` parse_ret 42

let tsuccess () : T.Tac unit =
  T.qed ();
  T.print "Success!"

let gen_parser32 (p: T.term) : T.Tac unit =
  T.set_guard_policy T.Goal;
  T.exact_guard (gen_parser32' p);
  if T.ngoals () > 0
  then begin
    T.first [
      (fun () ->
        let _ = T.repeat (fun () -> T.forall_intro `T.or_else` T.implies_intro) in
        T.print "Trying reflexivity";
        T.trefl ();
        tsuccess ()
      );
      (fun () ->
        T.print "Trying SMT";
        T.smt ();
        tsuccess ()        
      );
    ]
  end

let q : parser32 p = T.synth_by_tactic (fun () -> gen_parser32 (`(p)))

let p' = p `nondep_then` parse_u8

// let p' = (parse_u8 `nondep_then` parse_ret 42) `nondep_then` parse_u8

#push-options "--print_implicits"

let q' : parser32 p' = T.synth_by_tactic (fun () -> gen_parser32 (`(p')))

let r = parse_ret 42 `parse_synth` (fun x -> x + 1)

let r' : parser32 r = T.synth_by_tactic (fun () -> gen_parser32 (`(r)))

