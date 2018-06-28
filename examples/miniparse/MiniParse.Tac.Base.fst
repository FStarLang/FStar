module MiniParse.Tac.Base

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

let tsuccess () : T.Tac unit =
  T.qed ();
  T.print "Success!"

let rec solve_goal () : T.Tac unit =
    T.first [
      (fun () ->
        let _ = T.repeat (fun () -> T.forall_intro `T.or_else` T.implies_intro) in
        T.print "Trying reflexivity";
        T.trefl ();
        tsuccess ()
      );
      (fun () ->
        T.print "split";
        T.split ();
        T.iseq [
          solve_goal;
          solve_goal;
        ];
        tsuccess ()
      );
      (fun () ->
        T.print "Trying SMT";
        T.smt ();
        tsuccess ()
      );
    ];
    tsuccess ()

let tconclude () : T.Tac unit =
  if T.ngoals () > 0
  then begin
    T.dump "a goal";
    solve_goal ()
  end
  else T.print "No goals left"
