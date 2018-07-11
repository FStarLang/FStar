module MiniParse.Tac.Base

module T = FStar.Tactics
module L = FStar.List.Tot

let pack_nat (n: nat) : T.Tac T.term =
  T.pack (T.Tv_Const (T.C_Int n))

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
  (x: squash (test == v))

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

let rec string_of_name (n: T.name) : Tot string =
  match n with
  | [] -> ""
  | [a] -> a
  | a :: b -> a ^ "." ^ string_of_name b

let unfold_fv (t: T.fv) : T.Tac T.term =
  let env = T.cur_env () in
  let n = T.inspect_fv t in
  match T.lookup_typ env n with
  | Some s ->
    begin match T.inspect_sigelt s with
    | T.Sg_Let false _ _ _ def ->
      let nm = string_of_name n in
      T.print ("Unfolded definition: " ^ nm);
      def
    | _ ->
      let nm = string_of_name n in
      tfail (nm ^ ": not a non-recursive let definition")
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

let rec imm_solve_goal (l: list (unit -> T.Tac unit)) : T.Tac unit =
  T.first (List.Tot.append l [
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
      to_all_goals (fun () -> imm_solve_goal l);
      tsuccess "return_squash imm_solve"
    );    
  ])

let tforall_intro () = T.forall_intro ()

let timplies_intro () = T.implies_intro ()

let tsplit () = T.split ()

let rec solve_goal (l: list (unit -> T.Tac unit)) : T.Tac unit =
  if T.ngoals () = 0
  then ()
  else begin
    begin
      if T.ngoals () > 1
      then
        tfail "More than one goal here"
      else ()
    end;
  begin match T.trytac tforall_intro with
  | Some _ ->
    T.print ("Applied: forall_intro");
    to_all_goals (fun () -> solve_goal l)
  | _ ->
    begin match T.trytac timplies_intro with
    | Some _ ->
      T.print ("Applied: implies_intro");
      to_all_goals (fun () -> solve_goal l)
    | _ ->
      begin match T.trytac tsplit with
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
          to_all_goals (fun () -> solve_goal l)
      | _ ->
        begin match T.trytac (fun () -> imm_solve_goal l) with
        | Some _ -> ()
        | _ ->
          T.dump "MUST USE SMT FOR THIS ONE";
          T.smt ();
          tsuccess "smt"
        end
      end
    end
  end
  end

let rec tconclude_with (l: list (unit -> T.Tac unit)) : T.Tac unit =
  if T.ngoals () > 0
  then begin
    T.dump "Some goals left";
    let _ = T.divide 1 (fun () -> solve_goal l) (fun () -> tconclude_with l) in
    ()
  end else T.print "No goals left"

let tconclude () : T.Tac unit = tconclude_with []

let according_to (pol: T.guard_policy) (t: (unit -> T.Tac unit)) : T.Tac unit =
  match pol with
  | T.SMT -> to_all_goals T.smt
  | T.Drop -> to_all_goals T.tadmit
  | _ -> T.with_policy pol t
