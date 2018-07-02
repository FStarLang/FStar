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

inline_for_extraction
let ctest (v: bool) (test: bool) : Tot Type =
  (x: unit { test == v } )

inline_for_extraction
let mk_if_t (#t: Type) (test: bool) (x1: (ctest true test -> Tot t)) (x2: (ctest false test -> Tot t)) : Tot t =
  if test then x1 () else x2 ()

let mk_if (test ty e_true e_false: T.term) : T.Tac T.term =
  let bt = T.fresh_binder (T.mk_app (`(ctest true)) [test, T.Q_Explicit]) in
  let bf = T.fresh_binder (T.mk_app (`(ctest false)) [test, T.Q_Explicit]) in
  let ft = T.pack (T.Tv_Abs bt e_true) in
  let ff = T.pack (T.Tv_Abs bf e_false) in
  T.mk_app (`(mk_if_t)) [
    ty, T.Q_Implicit;
    test, T.Q_Explicit;
    ft, T.Q_Explicit;
    ff, T.Q_Explicit;
  ]

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
  T.print ("Checking success for: " ^ s);
  T.qed ();
  T.print ("Success: " ^ s)

let rec to_all_goals (t: unit -> T.Tac unit) : T.Tac unit =
  if T.ngoals () = 0
  then ()
  else
    let _ = T.divide 1 t (fun () -> to_all_goals t) in
    ()

let admit_others (t: unit -> T.Tac unit) : T.Tac unit =
  if T.ngoals () = 0
  then ()
  else if T.ngoals () = 1
  then t ()
  else
    tfail "There should be only one goal here"
(*    
    let _ = T.divide 1 t (fun () -> to_all_goals tadmit) in
    ()
*)    

let rec imm_solve_goal () : T.Tac unit =
  T.first [
    (fun () ->
      T.trivial ();
      tsuccess "trivial"
    );
    (fun () ->
      T.trefl ();
      tsuccess "reflexivity"
    );
    (fun () ->
      T.assumption ();
      tsuccess "assumption"
    );
    (fun () ->
      T.norm [delta; zeta; iota; primops];
      T.trivial ();
      tsuccess "norm trivial"
    );
    (fun () ->
      T.apply (`(FStar.Squash.return_squash));
      to_all_goals imm_solve_goal;
      tsuccess "return_squash imm_solve"
    );    
  ]

let rec solve_goal () : T.Tac unit =
  if T.ngoals () = 0
  then ()
  else begin
    begin
      if T.ngoals () > 1
      then
        tfail "More than one goal here"
      else ()
    end;
  match T.trytac imm_solve_goal with
  | Some _ -> ()
  | _ ->
  begin match T.trytac (fun () -> T.with_policy T.Drop T.forall_intro) with
  | Some _ ->
    T.print ("Applied: forall_intro");
    admit_others solve_goal
  | _ ->
    begin match T.trytac (fun () -> T.with_policy T.Drop T.implies_intro) with
    | Some _ ->
      T.print ("Applied: implies_intro");
      admit_others solve_goal
    | _ ->
      begin match T.trytac (fun () -> T.with_policy T.Drop T.split) with
      | Some _ ->
        let n = T.ngoals () in
        if n > 2
        then
          tfail "There should be only at most 2 goals here"
(*        
          let _ = T.divide 2 (fun () -> to_all_goals solve_goal) (fun () -> to_all_goals T.tadmit) in
          ()
*)          
        else
          to_all_goals solve_goal
      | _ ->
        T.dump "MUST USE SMT FOR THIS ONE";
        T.smt ();
        tsuccess "smt"
      end
    end
  end
  end

let rec tconclude () : T.Tac unit =
  if T.ngoals () > 0
  then begin
    T.dump "Some goals left";
    let _ = T.divide 1 solve_goal tconclude in
    ()
  end else T.print "No goals left"
