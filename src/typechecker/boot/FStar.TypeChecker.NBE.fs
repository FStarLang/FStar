#light "off"
module FStar.TypeChecker.NBE
open FStar.All
open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Ident

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module Range = FStar.Range
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print
module BU = FStar.Util
module Env = FStar.TypeChecker.Env


(* Utils *)

// VD: This seems necessary for the OCaml build
let max a b = if a > b then a else b

let map_rev (f : 'a -> 'b) (l : list<'a>) : list<'b> =
  let rec aux (l:list<'a>) (acc:list<'b>) = //NS: weird, this needs an annotation to type-check in F*; cf issue #
    match l with
    | [] -> acc
    | x :: xs -> aux xs (f x :: acc)
  in  aux l []

let rec drop (p: 'a -> bool) (l: list<'a>): list<'a> =
  match l with
  | [] -> []
  | x::xs -> if p x then x::xs else drop p xs

let debug f =
    if Options.debug_at_level "Test" (Options.Other "NBE")
    then f ()

let debug_term (t : term) =
  BU.print1 "%s\n" (P.term_to_string t)

let debug_sigmap (m : BU.smap<sigelt>) =
  BU.smap_fold m (fun k v u -> BU.print2 "%s -> %%s\n" k (P.sigelt_to_string_short v)) ()

type var = bv
type sort = int

//IN F*: type atom : Type0 =
type atom = //JUST FSHARP
  | Var of var
  | Type of universe (* Zoe: Not sure why this needs to be an atom, just following the paper *)
  | Match of t * (* the scutinee *)
             (t -> t) (* the closure that pattern matches the scrutiny *)
  | Rec of letbinding * list<t> (* Danel: This wraps a unary F* rec. def. as a thunk in F# *)
//IN F*: and t : Type0 =
and t = //JUST FSHARP
  | Lam of (t -> t) * aqual
  | Accu of atom * list<(t * aqual)>
  (* For simplicity represent constructors with fv as in F* *)
  | Construct of fv * list<universe> * list<(t * aqual)> (* Zoe: This is used for both type and data constructors*)
  | Unit
  | Bool of bool

type head = t
type annot = option<t>

let rec t_to_string (x:t) =
    match x with
    | Lam _ -> "Lam"
    | Accu (a, l) -> "Accu (" ^ (atom_to_string a) ^ ") (" ^ (String.concat "; " (List.map (fun x -> t_to_string (fst x)) l)) ^ ")"
    | Construct (fv, us, l) -> "Construct (" ^ (P.fv_to_string fv) ^ ") [" ^ (String.concat "; "(List.map P.univ_to_string us)) ^ "] (" ^ (String.concat "; " (List.map (fun x -> t_to_string (fst x)) l)) ^ ")"
    | Unit -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"

and atom_to_string (a: atom) =
    match a with
    | Var v -> "Var " ^ (P.bv_to_string v)
    | Type u -> "Type " ^ (P.univ_to_string u)
    | Match (t, _) -> "Match " ^ (t_to_string t)
    | Rec (_, l) -> "Rec (" ^ (String.concat "; " (List.map t_to_string l)) ^ ")"

let is_not_accu (x:t) =
  match x with
  | Accu (_, _) -> false
  | _ -> true

let mkConstruct i us ts = Construct(i, us, ts)

let mkAccuVar (v:var) = Accu(Var v, [])
let mkAccuMatch (s : t) (c : t -> t) = Accu(Match (s, c), [])
let mkAccuRec (b:letbinding) (env:list<t>) = Accu(Rec(b, env), [])
let mkAccuTyp (u:universe) = Accu(Type u, [])
//let mkAccUniv (u:universe) = Accu(Univ u, [])

let isAccu (trm:t) =
  match trm with
  | Accu _ -> true
  | _ -> false

let isAccuTyp (x:t) =
  match x with
  | Accu(Type _, _) -> true
  | _ -> false

let rec pickBranch (c : fv) (branches : list<branch>) (args: list<t * aqual>) = // : term * list<t>  =
  match branches with
  | [] -> failwith "Branch not found"
  | ({v = Pat_cons (c', pats')}, _, e) :: bs when (fv_eq c c') ->
      assert (List.length args = List.length pats');
      debug (fun () -> BU.print1 ">>>> args: %s\n" (String.concat "; " (List.map (fun (x, _) -> t_to_string x) args)));
      let args2 = List.filter_map (fun x -> x) <| List.map2 (fun (p,_) (a,_) -> match p.v with Pat_dot_term _ -> None | _ when (not (isAccuTyp a)) (*Nik:  when it's not a universe*)  -> Some a) pats' args in
      debug (fun () -> BU.print1 ">>>> args2: %s\n" (String.concat "; " (List.map (fun x -> t_to_string x) args2)));
      // (e, (List.map (fun (x, _) -> x) args))
      (e, args)
      //(e, args2)
  | b :: bs -> pickBranch c bs args

(* Tests is the application is full and if none of the arguments is symbolic *)
let rec test_args ts cnt =
  match ts with
  | [] -> cnt <= 0
  | t :: ts -> (not (isAccu (fst t))) && test_args ts (cnt - 1)

(* Count the number of abstractions in the body of a let rec.
   It accounts for abstractions instantiated inside the body.
   This analysis needs further refinement, for example see the let in case.
*)
let rec count_abstractions (t : term) : int =
    match (SS.compress t).n with
    | Tm_delayed _ | Tm_unknown -> failwith "Impossible"
    | Tm_bvar _
    | Tm_name _
    | Tm_fvar _
    | Tm_constant _
    | Tm_type _
    | Tm_arrow _
    | Tm_uvar _
    | Tm_refine _
    | Tm_unknown -> 0

    | Tm_uinst (t, _)  -> count_abstractions t

    | Tm_abs (xs, body, _) ->
      List.length xs + count_abstractions body

    | Tm_app(head, args) ->
      max (count_abstractions head - List.length args) 0

    | Tm_match(scrut, branches) ->
      (match branches with
       | [] -> failwith "Branch not found"
       (* count just one branch assuming it is well-typed *)
       | (_, _, e) :: bs -> count_abstractions e)

    | Tm_let (_, t)
      (* This is not quite right. We need to somehow cound the abstractions of the let definition
         as it might be used in head position. For instance we might have something like [let t = e in t]
       *)
    | Tm_meta (t, _)
    | Tm_ascribed (t, _, _) -> count_abstractions t


(* XXX unused *)
// let rec mkBranches branches cont =
//   match branches with
//   | ({ v = (Pat_cons (fv, pats))}, _, _) :: branches' ->
//     (* a new binder for each argument *)
//     let (args, binders) =
//       List.fold_right
//         (fun (p : pat * bool) ((args:list<t>), (bs:list<(pat * bool)>)) ->
//            let x = S.new_bv None S.tun in
//            (mkAccuVar x :: args, (S.withinfo (Pat_var x) Range.dummyRange, snd p) :: bs)
//         ) pats ([], []) in
//     let value = Construct (fv, args) in
//     let pat = S.withinfo (Pat_cons (fv, binders)) Range.dummyRange  in
//     let branch = (pat, None, cont value) in
//     branch :: mkBranches branches' cont
//   | _ -> failwith "Unexpected pattern"

let find_sigelt_in_gamma (env: Env.env) (lid:lident): option<sigelt> =
  let mapper (lr, rng) =
    match lr with
    | BU.Inr (elt, None) -> Some elt
    | BU.Inr (elt, Some us) ->
        debug (fun () -> BU.print1 "Universes in local declaration: %s\n" (P.univs_to_string us));
        Some elt
    | _ -> None in
  BU.bind_opt (Env.lookup_qname env lid) mapper

let translate_univ (env: Env.env) (bs: list<t>) (u: universe): t =
    let u = SS.compress_univ u in
    match u with
    | U_bvar i ->
        // BU.print1 "%%% In universe translation for %s:\n" (P.univ_to_string u);
        // BU.print1 "%%% BS list: %s\n" (String.concat ",\n " (List.map (fun x -> t_to_string x) bs));
        // BU.print2 "%%% Index: %s - List length: %s" (BU.string_of_int i) (BU.string_of_int (List.length bs));
        // List.nth bs i

        //VD: Not binding any universe variable
        mkAccuTyp U_unknown
    | _ ->
        mkAccuTyp u

(* We are not targeting tagless normalization at this point *)
let rec app (f:t) (x:t) (q:aqual) =
  debug (fun () -> BU.print2 "When creating app: %s applied to %s\n" (t_to_string f) (t_to_string x));
  match f with
  | Lam (f, _) -> f x
  | Accu (a, ts) -> Accu (a, (x,q)::ts)
  | Construct (i, us, ts) -> Construct (i, us, (x,q)::ts)
  | Unit
  | Bool _ -> failwith "Ill-typed application"

and iapp (f:t) (args:list<(t * aqual)>) =
  match args with
  | [] -> f
  | _ -> iapp (app f (fst (List.hd args)) (snd (List.hd args))) (List.tl args)

and translate_fv (env: Env.env) (bs:list<t>) (us:list<universe>) (fvar:fv): t =
  let find_in_sigtab (env : Env.env) (lid : lident) : option<sigelt> = BU.smap_try_find env.sigtab (text_of_lid lid) in
  //VD: for now, also search in local environment (local definitions are not part of env.sigtab)
  match List.find BU.is_some [find_sigelt_in_gamma env fvar.fv_name.v; find_in_sigtab env fvar.fv_name.v] with
   | Some elt ->
     (match elt with
      | Some { sigel = Sig_let ((is_rec, [lb]), _) } ->
        if is_rec then
          mkAccuRec lb []
        else
          begin
             debug (fun () -> BU.print2 "Type of lbdef: %s - %s\n" (P.tag_of_term (SS.compress lb.lbtyp)) (P.term_to_string (SS.compress lb.lbtyp)));
             debug (fun () -> BU.print2 "Body of lbdef: %s - %s\n" (P.tag_of_term (SS.compress lb.lbdef)) (P.term_to_string (SS.compress lb.lbdef)));
             let t = SS.compress lb.lbdef in
             let x = (S.new_bv None S.tun, None) in
             let t' = S.mk (Tm_abs([x], t, None)) None t.pos in
             app (translate env bs t') (translate_univ env bs (List.hd us)) None
             // translate env [] lb.lbdef
          end
      | Some { sigel = Sig_datacon(_, _, _, _, _, []) } ->
          mkConstruct fvar us []
      // VD: This was a stopgap for definitions not found in environment:
      // | Some { sigel = Sig_declare_typ(lid, univs, ty) } ->
      //     (match (SS.compress ty).n with
      //      | Tm_type u -> mkAccuTyp u
      //      | _ -> failwith "impossible?")
      | Some { sigel = Sig_inductive_typ(lid, univs, bs, ty, _, _) } ->
          mkConstruct fvar us []
      | None ->
          mkConstruct fvar us [] (* Zoe : Treat all other cases as type/data constructors for now. *)
      | Some s ->
          BU.format1 "Sig %s\n" (P.sigelt_to_string s) |> failwith
     )
   | None ->
       mkConstruct fvar us [] (* Zoe : Z and S dataconstructors from the examples are not in the environment *)


and translate (env:Env.env) (bs:list<t>) (e:term) : t =
    debug (fun () -> BU.print2 "Term: %s - %s\n" (P.tag_of_term (SS.compress e)) (P.term_to_string (SS.compress e)));
    debug (fun () -> BU.print1 "BS list: %s\n" (String.concat "; " (List.map (fun x -> t_to_string x) bs)));

    match (SS.compress e).n with
    | Tm_delayed (_, _) -> failwith "Tm_delayed: Impossible"

    | Tm_unknown -> failwith "Tm_unknown: Impossible"

    | Tm_constant (FStar.Const.Const_unit) ->
      Unit

    | Tm_constant (FStar.Const.Const_bool b) ->
      Bool b

    | Tm_constant c ->
      let err = "Tm_constant " ^ (P.const_to_string c) ^ ": Not yet implemented" in
      debug_term e; failwith err

    | Tm_bvar db -> //de Bruijn
      List.nth bs db.index

    | Tm_uinst (t, [u]) ->
      debug (fun () -> BU.print3 "Term with univs: %s - %s\nUniv %s\n" (P.tag_of_term t) (P.term_to_string t) (P.univ_to_string u));
      (match (SS.compress t).n with
       | Tm_fvar fv ->
          translate_fv env bs [u] fv
          // let tr = translate env bs t in
          // //t is always an fv
          // // specialize the definition of t for u (if it has one, i.e. not a constructor)
          // // don't do this here, but when looking up def of fv; if it's a constructor, just mkConstructor
          // (match tr with
          //  | Lam _ ->
          //      let x = (S.new_bv None S.tun, None) in
          //      let t' = S.mk (Tm_abs([x], t, None)) None t.pos in
          //      app (translate env bs t') (translate_univ env bs u) None
          //  | _ ->
          //      app tr (translate_univ env bs u) None)

       | _ -> failwith "Expected an fv")

    | Tm_uinst (t, _) ->
      debug (fun () -> BU.print1 "Term with univs: %s\n" (P.term_to_string t));
      // List.iter (fun x -> BU.print1 "Univ %s\n" (P.univ_to_string (translate_univ x))) u;
      // translate ((map_rev (fun x -> mkAccuUniv (translate_univ x)) u) @ bs) t
      debug_term e; failwith "Not yet implemented Tm_uinst"

    | Tm_type u -> failwith "Unreachable?" //mkAccuTyp u

    | Tm_arrow (bs, c) -> debug_term e; failwith "Tm_arrow: Not yet implemented"

    | Tm_refine _ -> debug_term e; failwith "Tm_refine: Not yet implemented"

    | Tm_ascribed (t, _, _) -> translate env bs t

    | Tm_uvar (uvar, t) -> debug_term e; failwith "Tm_uvar: Not yet implemented"

    | Tm_meta (e, _) -> translate env bs e

    | Tm_name x ->
      mkAccuVar x

    | Tm_abs ([x], body, _) ->
      debug (fun () -> BU.print2 "Tm_abs body : %s - %s\n" (P.tag_of_term body) (P.term_to_string body));
      Lam ((fun (y:t) -> translate env (y::bs) body), snd x)

    | Tm_abs (x::xs, body, _) ->
      let rest = S.mk (Tm_abs(xs, body, None)) None Range.dummyRange in
      let tm = S.mk (Tm_abs([x], rest, None)) None e.pos in
      translate env bs tm

    | Tm_fvar fvar ->
        translate_fv env bs [] fvar

    | Tm_app (e, [arg]) ->
      debug (fun () -> BU.print2 "Application %s / %s\n" (P.term_to_string e) (P.term_to_string (fst arg)));
      app (translate env bs e) (translate env bs (fst arg)) (snd arg)

    | Tm_app(head, arg::args) ->
      debug (fun () -> BU.print2 "Application %s / %s (...more agrs)\n" (P.term_to_string head) (P.term_to_string (fst arg)));
      let first = S.mk (Tm_app(head, [arg])) None Range.dummyRange in
      let tm = S.mk (Tm_app(first, args)) None e.pos in
      translate env bs tm

    | Tm_match(scrut, branches) ->
      let rec case (scrut : t) : t =
        match scrut with
        | Construct(c, us, args) -> (* Scrutinee is a constructed value *)
          (* Assuming that all the arguments to the pattern constructors
             are binders -- i.e. no nested patterns for now *)
          (* XXX : is rev needed?  VD: I don't think so *)
          debug (fun () -> BU.print1 "Match args: %s\n" (String.concat "; " (List.map (fun (x, q) -> (if BU.is_some q then "#" else "") ^(t_to_string x)) args)));
          let branch, args = (pickBranch c branches args) in
          // translate env (args @ bs) branch
          translate env ((List.map (fun (x, _) -> x) args) @ bs) branch
        | _ ->
          mkAccuMatch scrut case
      in
      case (translate env bs scrut)

    | Tm_let((false, [lb]), body) -> // non-recursive let
      let def = translate env bs lb.lbdef in
      translate env (def::bs) body

    | Tm_let((true, [lb]), body) -> // recursive let with only one recursive definition
      let f = mkAccuRec lb bs in
      translate env (f::bs) body (* Danel: storing the rec. def. as F* code wrapped in a thunk *)

      // this will loop infinitely when the recursive argument is symbolic
      // let def = lb.lbdef in
      // let fnorm f = translate (f::bs) def in
      // let rec f = fnorm f in
      // translate (f::bs) body
      //failwith "Not yet implemented"


(* [readback] creates named binders and not De Bruijn *)
and readback (env:Env.env) (x:t) : term =
    debug (fun () -> BU.print1 "Readback: %s\n" (t_to_string x));
    match x with
    | Unit -> S.unit_const

    | Bool true -> U.exp_true_bool
    | Bool false -> U.exp_false_bool

    | Lam (f, q) ->
      let x = S.new_bv None S.tun in
      let body = readback env (f (mkAccuVar x)) in
      U.abs [(x, q)] body None

    | Construct (fv, us, args) ->
      let args = map_rev (fun (x, q) -> (readback env x, q)) args in
      (match args with
       | [] -> (S.mk (Tm_fvar fv) None Range.dummyRange)
       | h::hs ->
         // VD: This will currently not do the right thing if there's more than one universe variable
         //(match (fst h).n with
         (match us with
          | [u] (* Tm_type u *) -> U.mk_app (S.mk_Tm_uinst (S.mk (Tm_fvar fv) None Range.dummyRange) [u]) hs
          | [] -> U.mk_app (S.mk (Tm_fvar fv) None Range.dummyRange) args
          | _ -> failwith "Case not handled" ))

    | Accu (Var bv, []) ->
      S.bv_to_name bv
    | Accu (Var bv, ts) ->
      let args = map_rev (fun (x, q) -> (readback env x, q)) ts in
      U.mk_app (S.bv_to_name bv) args

    | Accu (Type u, []) ->
      S.mk (Tm_type u) None Range.dummyRange
    | Accu (Type u, ts) ->
      let args = map_rev (fun (x, q) -> (readback env x, q)) ts in
      U.mk_app (S.mk (Tm_type u) None Range.dummyRange) args

    | Accu (Match (scrut, cases), ts) ->
      let args = map_rev (fun (x, q) -> (readback env x, q)) ts in
      let head =  readback env (cases scrut) in
      (match ts with
       | [] -> head
       | _ -> U.mk_app head args)

    | Accu (Rec(lb, bs), ts) ->
       let rec curry hd args =
       match args with
       | [] -> hd
       | [arg] -> app hd (fst arg) (snd arg)
       | arg :: args -> app (curry hd args) (fst arg) (snd arg)
       in
       let args_no = count_abstractions lb.lbdef in
       // Printf.printf "Args no. %d\n" args_no;
       if test_args ts args_no then (* if the arguments are not symbolic and the application is not partial compute *)
         readback env (curry (translate env ((mkAccuRec lb bs) :: bs) lb.lbdef) ts)
       else (* otherwise do not unfold *)
         let head =
           (* Zoe: I want the head to be [let rec f = lb in f]. Is this the right way to construct it? *)
           let f = match lb.lbname with
                   | BU.Inl bv -> S.bv_to_name bv
                   | BU.Inr fv -> failwith "Not yet implemented"
           in
           S.mk (Tm_let((true, [lb]), f)) None Range.dummyRange
         in
         let args = map_rev (fun (x, q) -> (readback env x, q)) ts in
         (match ts with
          | [] -> head
          | _ -> U.mk_app head args)

// Zoe: Commenting out conflict with Danel
// =======
//     | Accu (Rec (lb, bs), ts) ->
//        (match (SS.compress lb.lbdef).n with
//         | Tm_abs (args, _, _) ->
//             if (List.length ts = List.length args &&
//                 List.fold_right (fun x y -> x && y) (List.map is_not_accu ts) true)
//             then readback (iapp (translate ((Accu (Rec (lb, bs), []))::bs) lb.lbdef) ts)
//             else (let args = List.map (fun x -> as_arg (readback x)) ts in
//                   let body = (match args with
//                               | [] -> (match lb.lbname with
//                                        | BU.Inl bv -> S.bv_to_name bv
//                                        | BU.Inr fv -> failwith "Not yet implemented")
//                               | _  -> (match lb.lbname with
//                                        | BU.Inl bv -> U.mk_app (S.bv_to_name bv) args
//                                        | BU.Inr fv -> failwith "Not yet implemented")) in
//                   S.mk (Tm_let((true, [lb]), body)) None Range.dummyRange)
//                   (* Currently not normalizing the let-bound definition on its own,
//                      only normalizing it when it is unfolded *)
//         | _ -> failwith "Recursive definition not a function")
// >>>>>>> 86f93ae6edc257258f376954fed7fba11f53ff83

let normalize (env : Env.env) (e:term) : term =
  //debug_sigmap env.sigtab;
  readback env (translate env [] e)
