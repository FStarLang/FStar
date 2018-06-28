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

let tsuccess (s: string) : T.Tac unit =
  T.qed ();
  T.print ("Success: " ^ s)

let rec solve_goal () : T.Tac unit =
  match T.trytac (fun () -> T.first [
    (fun () ->
      T.print "Trying trivial";
      T.trivial ();
      tsuccess "trivial"
    );
    (fun () ->
      T.print "Trying reflexivity";
      T.trefl ();
      tsuccess "reflexivity"
    );
    (fun () ->
      T.print "Trying tassumption";
      T.assumption ();
      tsuccess "assumption"
    );
    (fun () ->
      T.print "Trying return_squash; tassumption";
      T.apply (`(FStar.Squash.return_squash));
      T.assumption ();
      tsuccess "return_squash assumption"
    );
  ]) with
  | Some _ -> ()
  | _ ->
  begin match T.trytac T.forall_intro with
  | Some _ -> solve_goal ()
  | _ ->
    begin match T.trytac T.implies_intro with
    | Some _ -> solve_goal ()
    | _ ->
      begin match T.trytac T.split with
      | Some _ -> T.iseq [ solve_goal; solve_goal ]
      | _ ->
        T.dump "MUST USE SMT FOR THIS ONE";
        T.smt ();
        tsuccess "smt"
      end
    end
  end

let tconclude () : T.Tac unit =
  if T.ngoals () > 0
  then
    let _ = T.repeat solve_goal in
    T.qed ()
  else T.print "No goals left"
