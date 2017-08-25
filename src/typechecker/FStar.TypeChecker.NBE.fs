#light "off"
module FStar.TypeChecker.NBE
open FStar.All
open FStar
open FStar.TypeChecker
open FStar.Syntax.Syntax

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module Range = FStar.Range
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print

(* Utils *)

let debug_term (t : term) =
  Printf.printf "%s\n" (P.term_to_string t)

type var = bv
type sort = int

//IN F*: type atom : Type0 =
type atom = //JUST FSHARP
  | Var of var
  | Sort of sort
  | Prod of t * t
  (* keep original branches for readback -- 
     only used to find the original patterns *)
  | Match of list<branch> * t * (t -> t) 
  | Fix of (t -> t) * t * int
//IN F*: and t : Type0 =
and t = //JUST FSHARP
  | Lam of (t -> t)
  | Accu of atom * list<t>
  (* For simplicity represent constructors with fv as in F* terms *)
  | Construct of fv * list<t>
  | Unit
  | Bool of bool
type head = t
type annot = option<t> 

let app (f:t) (x:t) =
  match f with
  | Lam f -> f x
  | Accu (a, ts) -> Accu(a, x::ts)
  | Construct(i, ts) -> Construct (i, x::ts)
  | Unit
  | Bool _ -> failwith "Ill-typed application"

let mkConstruct i ts = Construct(i,ts)

let mkAccuVar (v:var) = Accu(Var v, [])
let mkAccuMatch (b : list<branch>) (s : t) (c : t -> t) = 
  Accu(Match (b, s, c), [])

let rec pickBranch (c : fv) (branches : list<branch>) : term = 
  match branches with
  | [] -> failwith "Branch not found"
  | ({v = Pat_cons (c', args)}, _, e) :: bs when (fv_eq c c') ->
    e
  | b :: bs -> pickBranch c bs

let rec mkBranches branches cont = 
  match branches with 
  | ({ v = (Pat_cons (fv, pats))}, _, _) :: branches' -> 
    (* a new binder for each argument *)
    let (args, binders) = 
      List.foldBack
        (fun (p : pat * bool) ((args, bs) : list<t> * list<pat * bool>) -> 
           let x = S.new_bv None S.tun in 
           (mkAccuVar x :: args, (S.withinfo (Pat_var x) Range.dummyRange, snd p) :: bs)
        ) pats ([], []) in
    let value = Construct (fv, args) in
    let pat = S.withinfo (Pat_cons (fv, binders)) Range.dummyRange  in
    let branch = (pat, None, cont value) in
    branch :: mkBranches branches' cont
  | _ -> failwith "Unexpected pattern" 

let rec translate (bs:list<t>) (e:term) : t =
    match (SS.compress e).n with
    | Tm_delayed _ -> failwith "Impossible"

    | Tm_constant (FStar.Const.Const_unit) ->
      Unit

    | Tm_constant (FStar.Const.Const_bool b) ->
      Bool b

    | Tm_bvar db -> //de Bruijn
      List.nth bs db.index

    | Tm_name x ->
      mkAccuVar x

    | Tm_abs ([x], body, _) ->
      Lam (fun (y:t) -> translate (y::bs) body)

    | Tm_fvar v ->
      mkConstruct v []
      
    | Tm_abs (x::xs, body, _) ->
      let rest = S.mk (Tm_abs(xs, body, None)) None Range.dummyRange in
      let tm = S.mk (Tm_abs([x], rest, None)) None e.pos in
      translate bs tm

    | Tm_app (e, [arg]) ->
      app (translate bs e) (translate bs (fst arg))

    | Tm_app(head, arg::args) ->
      let first = S.mk (Tm_app(head, [arg])) None Range.dummyRange in
      let tm = S.mk (Tm_app(first, args)) None e.pos in
      translate bs tm
    
    | Tm_match(scrut, branches) ->
      let rec case (scrut : t) : t = 
        match scrut with 
        | Construct(c, args) -> (* Scrutinee is a constructed value *)
          (* Assuming that all the arguments to the pattern constructors 
             are binders -- i.e. no nested patterns for now  *) 
          (* XXX : is rev needed? *)
          let branch = translate ((List.rev args) @ args) (pickBranch c branches) in
          branch
        | _ -> 
          mkAccuMatch branches scrut case
      in 
      case (translate bs scrut)

    | _ -> debug_term e; failwith "Not yet implemented"

and readback (x:t) : term =
    match x with
    | Unit -> S.unit_const
    | Bool true -> U.exp_true_bool
    | Bool false -> U.exp_false_bool
    | Lam f ->
      let x = S.new_bv None S.tun in
      let body = readback (f (mkAccuVar x)) in
      U.abs [S.mk_binder x] body None
    | Construct (fv, args) -> 
      let args = List.map (fun x -> as_arg (readback x)) args in
      (match args with 
       | [] -> (S.mk (Tm_fvar fv) None Range.dummyRange)
       | _ -> U.mk_app (S.mk (Tm_fvar fv) None Range.dummyRange) args)
    | Accu (Var bv, []) ->
      S.bv_to_name bv
    | Accu (Var bv, ts) ->
      let args = List.map (fun x -> as_arg (readback x)) ts in
      U.mk_app (S.bv_to_name bv) args
    | Accu (Match (branches, scrut, cases), ts) ->
      let args = List.map (fun x -> as_arg (readback x)) ts in
      let branches = mkBranches branches (fun v -> readback (cases v)) in 
      let head =  S.mk (Tm_match (readback scrut, branches)) None Range.dummyRange in
      (match ts with 
       | [] -> head
       | _ -> U.mk_app head args)
    | _ -> failwith "Not yet implemented"
    
and normalize (e:term) : term = readback (translate [] e)
