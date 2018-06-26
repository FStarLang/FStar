#light "off"
module FStar.TypeChecker.NBE
open FStar.All
open FStar.Exn
open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Errors
open FStar.TypeChecker.Normalize
open FStar.TypeChecker.NBETerm

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module Range = FStar.Range
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print
module BU = FStar.Util
module Env = FStar.TypeChecker.Env
module Z = FStar.BigInt
module C = FStar.Const
module Cfg = FStar.TypeChecker.Cfg
module N = FStar.TypeChecker.Normalize
module FC = FStar.Const
module EMB = FStar.Syntax.Embeddings
open FStar.TypeChecker.Cfg

(* Utils *)

// VD: This seems necessary for the OCaml build
let max a b = if a > b then a else b

let map_rev (f : 'a -> 'b) (l : list<'a>) : list<'b> =
  let rec aux (l:list<'a>) (acc:list<'b>) = //NS: weird, this needs an annotation to type-check in F*; cf issue #
    match l with
    | [] -> acc
    | x :: xs -> aux xs (f x :: acc)
  in  aux l []

let map_rev_append (f : 'a -> 'b) (l1 : list<'a>) (l2 : list<'b>) : list<'b> =
  let rec aux (l:list<'a>) (acc:list<'b>) =
    match l with
    | [] -> l2
    | x :: xs -> aux xs (f x :: acc)
  in  aux l1 l2

let rec map_append (f : 'a -> 'b)  (l1 : list<'a>) (l2 : list<'b>) : list<'b> =
  match l1 with
  | [] -> l2
  | x :: xs -> (f x) :: map_append f xs l2

let rec drop (p: 'a -> bool) (l: list<'a>): list<'a> =
  match l with
  | [] -> []
  | x::xs -> if p x then x::xs else drop p xs

// NBE debuging

let debug cfg f =
  if Env.debug (Cfg.cfg_env cfg) (Options.Other "NBE")
  then f ()

let debug_term (t : term) =
  BU.print1 "%s\n" (P.term_to_string t)

let debug_sigmap (m : BU.smap<sigelt>) =
  BU.smap_fold m (fun k v u -> BU.print2 "%s -> %%s\n" k (P.sigelt_to_string_short v)) ()



let pickBranch cfg (scrut : t) (branches : list<branch>) : option<(term * list<t>)> =
  let rec pickBranch_aux (scrut : t) (branches : list<branch>) (branches0 : list<branch>) : option<(term * list<t>)> =
    //NS: adapted from FStar.TypeChecker.Normalize: rebuild_match
    let rec matches_pat (scrutinee:t) (p:pat)
        : BU.either<list<t>, bool> =
        (* Inl ts: p matches t and ts are bindings for the branch *)
        (* Inr false: p definitely does not match t *)
        (* Inr true: p may match t, but p is an open term and we cannot decide for sure *)
        match p.v with
        | Pat_var bv
        | Pat_wild bv ->
            BU.Inl [scrutinee]

        | Pat_dot_term _ ->
            BU.Inl []

        | Pat_constant s ->
            let matches_const (c: t) (s: S.sconst) =
                debug cfg (fun () -> BU.print2 "Testing term %s against pattern %s\n"
                                    (t_to_string c) (P.const_to_string s));
                match c with
                | Constant (Unit) -> s = C.Const_unit
                | Constant (Bool b) -> (match s with | C.Const_bool p -> b = p | _ -> false)
                | Constant (Int i) -> (match s with | C.Const_int (p, None) -> i = Z.big_int_of_string p | _ -> false)
                | Constant (String (st, _)) -> (match s with | C.Const_string(p, _) -> st = p | _ -> false)
                | Constant (Char c) -> (match s with | C.Const_char p -> c = p | _ -> false)
                | _ -> false
            in
            if matches_const scrutinee s then BU.Inl [] else BU.Inr false

        | Pat_cons(fv, arg_pats) ->
            let rec matches_args out (a:list<(t * aqual)>) (p:list<(pat * bool)>)
                : BU.either<list<t>, bool> =
                match a, p with
                | [], [] -> BU.Inl out
                | (t, _)::rest_a, (p, _)::rest_p ->
                  (match matches_pat t p with
                   | BU.Inl s -> matches_args (out@s) rest_a rest_p
                   | m -> m)
                | _ ->
                BU.Inr false
            in
            match scrutinee with
            | Construct(fv', _us, args_rev) ->
                if fv_eq fv fv'
                then matches_args [] (List.rev args_rev) arg_pats
                else BU.Inr false

            | _ -> //must be a variable
            BU.Inr true
    in
    match branches with
    | [] -> failwith "Branch not found"
    | (p, _wopt, e)::branches ->
      match matches_pat scrut p with
      | BU.Inl matches ->
        debug cfg (fun () -> BU.print1 "Pattern %s matches\n" (P.pat_to_string p));
        Some (e, matches)
      | BU.Inr false -> //definitely did not match
        pickBranch_aux scrut branches branches0
      | BU.Inr true -> //maybe matches; stop
        None
  in pickBranch_aux scrut branches branches

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
    | _ -> 0

let find_sigelt_in_gamma cfg (env: Env.env) (lid:lident): option<sigelt> =
  let mapper (lr, rng) =
    match lr with
    | BU.Inr (elt, None) -> Some elt
    | BU.Inr (elt, Some us) ->
        debug cfg (fun () -> BU.print1 "Universes in local declaration: %s\n" (P.univs_to_string us));
        Some elt
    | _ -> None in
  BU.bind_opt (Env.lookup_qname env lid) mapper

let is_univ (tm : t)=
match tm with
| Univ _ -> true
| _ -> false

let un_univ (tm:t) : universe =
match tm with
| Univ u -> u
| _ -> failwith "Not a universe"

let is_constr_fv (fvar : fv) : bool =
  fvar.fv_qual = Some Data_ctor

let is_constr (q : qninfo) : bool =
  match q with
  | Some (BU.Inr ({ sigel = Sig_datacon (_, _, _, _, _, _) }, _), _) -> true
  | _ -> false

let translate_univ (bs:list<t>) (u:universe) : t =
    let rec aux u =
        let u = SS.compress_univ u in
        match u with
        | U_bvar i ->
          let u' = List.nth bs i in //it has to be a Univ term at position i
          (un_univ u')

        | U_succ u ->
          U_succ (aux u)

        | U_max us ->
          U_max (List.map aux us)

        | U_unknown
        | U_name _
        | U_unif _
        | U_zero ->
          u
    in
    Univ (aux u)

(* Creates the environment of mutually recursive function definitions *)
let make_rec_env (lbs:list<letbinding>) (bs:list<t>) : list<t> =
  let rec aux (lbs:list<letbinding>) (lbs0:list<letbinding>) (bs:list<t>) (bs0:list<t>) : list<t> =
  match lbs with
  | [] -> bs
  | lb::lbs' -> aux lbs' lbs0 ((mkAccuRec lb lbs0 bs0) :: bs) bs0
  in
  aux lbs lbs bs bs

let find_let (lbs : list<letbinding>) (fvar : fv) =
  BU.find_map lbs (fun lb -> match lb.lbname with
                   | BU.Inl _ -> failwith "find_let : impossible"
                   | BU.Inr name ->
                     if fv_eq name fvar
                     then Some lb
                     else None)

(* We are not targeting tagless normalization at this point *)
let app cfg (f:t) (x:t) (q:aqual) =
  debug cfg (fun () -> BU.print2 "When creating app: %s applied to %s\n" (t_to_string f) (t_to_string x));
  match f with
  | Lam (f, _, _) -> f [x]
  | Accu (a, ts) -> Accu (a, (x,q)::ts)
  | Construct (i, us, ts) ->
    (match x with
     | Univ u -> Construct (i, u::us, ts)
     | _ -> Construct (i, us, (x,q)::ts))
  | FV (i, us, ts) ->
     (match x with
     | Univ u -> FV (i, u::us, ts)
     | _ -> FV (i, us, (x,q)::ts))
 // | Refinement (b, r) -> Refinement (b, app cfg  r x q)
  | Constant _ | Univ _ | Type_t _ | Unknown | Arrow _ -> failwith "Ill-typed application"

let rec iapp (f:t) (args:args) : t =
  match f with
  | Lam (f, targs, n) ->
    let m = List.length args in
    if m < n then
      // partial application
      let (_, targs') = List.splitAt m targs in
      Lam ((fun l -> f (map_append fst args l)), targs', n - m)
    else if m = n then
      // full application
      f (List.map fst args)
    else
      // extra arguments
      let (args, args') = List.splitAt n args in
      iapp (f (List.map fst args)) args'
  | Accu (a, ts) -> Accu (a, List.rev_append args ts)
  | Construct (i, us, ts) ->
    let rec aux args us ts =
      match args with
      | (Univ u, _) :: args -> aux args (u :: us) ts
      | a :: args -> aux args us (a :: ts)
      | [] -> (us, ts)
    in
    let (us', ts') = aux args us ts in
    Construct (i, us', ts')
  | FV (i, us, ts) ->
    let rec aux args us ts =
      match args with
      | (Univ u, _) :: args -> aux args (u :: us) ts
      | a :: args -> aux args us (a :: ts)
      | [] -> (us, ts)
    in
    let (us', ts') = aux args us ts in
    FV (i, us', ts')
  | Constant _ | Univ _ | Type_t _ | Unknown | Arrow _ -> failwith "Ill-typed application"


and translate_fv (cfg: Cfg.cfg) (bs:list<t>) (fvar:fv): t =
   let debug = debug cfg in
   let qninfo = Env.lookup_qname (Cfg.cfg_env cfg) (S.lid_of_fv fvar) in
   if is_constr qninfo || is_constr_fv fvar then mkConstruct fvar [] []
   else
     match N.should_unfold cfg (fun _ -> cfg.reifying) fvar qninfo with
     | N.Should_unfold_fully  ->
       failwith "Not yet handled"

     | N.Should_unfold_no ->
       debug (fun () -> BU.print1 "(1) Decided to not unfold %s\n" (P.fv_to_string fvar));
       mkFV fvar [] []

     | N.Should_unfold_reify
     | N.Should_unfold_yes -> begin
       match qninfo with
       | Some (BU.Inr ({ sigel = Sig_let ((is_rec, lbs), names) }, _us_opt), _rng) ->
          let lbm = find_let lbs fvar in
          (match lbm with
           | Some lb ->
             if is_rec then
               mkAccuRec lb [] [] (* ZP: both the environment and the lists of mutually defined functions are empty
                                   since they are already present in the global environment *)
             else
               begin
                  debug (fun() -> BU.print "Translate fv: it's a Sig_let\n" []);
                  debug (fun () -> BU.print2 "Type of lbdef: %s - %s\n" (P.tag_of_term (SS.compress lb.lbtyp)) (P.term_to_string (SS.compress lb.lbtyp)));
                  debug (fun () -> BU.print2 "Body of lbdef: %s - %s\n" (P.tag_of_term (SS.compress lb.lbdef)) (P.term_to_string (SS.compress lb.lbdef)));
                  // VD: Don't unfold primops
                  if Cfg.is_prim_step cfg fvar then
                    mkFV fvar [] []
                  else
                    translate_letbinding cfg [] lb
               end
           | None -> failwith "Could not find mutually recursive definition" (* TODO: is this correct? *))
       | _ ->
        debug (fun () -> BU.print1 "(2) Decided to not unfold %s\n" (P.fv_to_string fvar));
        mkFV fvar [] [] (* Zoe : Z and S data constructors from the examples are not in the environment *)
      end

(* translate a let-binding - local or global *)
and translate_letbinding (cfg:Cfg.cfg) (bs:list<t>) (lb:letbinding) : t =
  let debug = debug cfg in
  let us = lb.lbunivs in
  // GM: Ugh! need this to use <| and get the inner lambda into ALL, but why !?
  let id x = x in
  match us with
  | [] -> translate cfg bs lb.lbdef
  | _ ->
    Lam ((fun us -> translate cfg (List.rev_append us bs) lb.lbdef),
          List.map (fun _ -> (fun () -> id <| (Constant Unit, None))) us,
          // Zoe: Bogus type! The idea is that we will never readback these lambdas
          List.length us)
  // Note, we only have universe polymorphic top-level pure terms (i.e., fvars bound to pure terms)
  // Thunking them is probably okay, since the common case is really top-level function
  // rather than top-level pure computation


and translate_constant (c : sconst) : constant =
    match c with
    | C.Const_unit -> Unit
    | C.Const_bool b -> Bool b
    | C.Const_int (s, None) -> Int (Z.big_int_of_string s)
    | C.Const_string (s, r) -> String (s,r)
    | C.Const_char c -> Char c
    | C.Const_range r -> Range r
    | _ -> failwith ("Tm_constant " ^ (P.const_to_string c) ^ ": Not yet implemented")

// GM: Not called?
and translate_pat (p : pat) : t =
    match p.v with
    | Pat_constant c -> Constant (translate_constant c)
    | Pat_cons (cfv, pats) -> iapp (mkConstruct cfv [] []) (List.map (fun (p,_) -> (translate_pat p, None)) pats) // Zoe : TODO universe args?
    | Pat_var bvar -> mkAccuVar bvar
    | Pat_wild bvar -> mkAccuVar bvar
    | Pat_dot_term (bvar, t) -> failwith "Pat_dot_term not implemented"

and translate (cfg:Cfg.cfg) (bs:list<t>) (e:term) : t =
    let debug = debug cfg in
    debug (fun () -> BU.print2 "Term: %s - %s\n" (P.tag_of_term (SS.compress e)) (P.term_to_string (SS.compress e)));
    debug (fun () -> BU.print1 "BS list: %s\n" (String.concat ";; " (List.map (fun x -> t_to_string x) bs)));

    match (SS.compress e).n with
    | Tm_delayed (_, _) ->
      failwith "Tm_delayed: Impossible"

    | Tm_unknown -> Unknown

    | Tm_constant c ->
      Constant (translate_constant c)

    | Tm_bvar db -> //de Bruijn
      List.nth bs db.index

    | Tm_uinst(t, us) ->
      debug (fun () -> BU.print3 "Term with univs: %s - %s\nUniv %s\n" (P.tag_of_term t)
                                                                    (P.term_to_string t)
                                                                    (List.map P.univ_to_string us |> String.concat ", "));
      List.fold_left (fun head u -> app cfg head (translate_univ bs u) None)
                     (translate cfg bs t)
                     us

    | Tm_type u ->
      Type_t (un_univ (translate_univ bs u))

    | Tm_arrow (bs, c) -> debug_term e; failwith "Tm_arrow: Not yet implemented"

    | Tm_refine (db, tm) -> failwith "Tm_refine: Not yet implemented"
    //  Refinement ((db, None), Lam ((fun (y:t) -> translate cfg (y::bs) tm), (fun () -> Constant Unit), None)) // XXX: Bogus type?

    | Tm_ascribed (t, _, _) -> translate cfg bs t

    | Tm_uvar (uvar, t) -> debug_term e; failwith "Tm_uvar: Not yet implemented"

    | Tm_name x ->
      mkAccuVar x

    | Tm_abs ([], _, _) -> failwith "Impossible: abstraction with no binders"

    // | Tm_abs ([x], body, _) ->
    //   debug (fun () -> BU.print2 "Tm_abs body : %s - %s\n" (P.tag_of_term body) (P.term_to_string body));
    //   let x1 = fst x in
    //   Lam ((fun (y:t) -> translate cfg (y::bs) body), (fun () -> translate cfg bs x1.sort), snd x)

    | Tm_abs (xs, body, _) ->
      Lam ((fun ys -> translate cfg (List.rev_append ys bs) body),
           List.map (fun x () -> (translate cfg bs (fst x).sort, snd x)) xs,
           List.length xs)

    | Tm_fvar fvar ->
      translate_fv cfg bs fvar

    // | Tm_app (e, [arg]) ->
    //   debug (fun () -> BU.print2 "Application: %s @ %s\n" (P.term_to_string e) (P.term_to_string (fst arg)));
    //   app cfg (translate cfg bs e) (translate cfg bs (fst arg)) (snd arg)

    | Tm_app({n=Tm_constant FC.Const_reify}, arg::more::args)
        when cfg.steps.reify_ ->
      let reifyh, _ = U.head_and_args e in
      let head = S.mk_Tm_app reifyh [arg] None e.pos in
      translate cfg bs (S.mk_Tm_app head (more::args) None e.pos)

    | Tm_app({n=Tm_constant FC.Const_reify}, [arg])
        when cfg.steps.reify_ ->
      assert (not cfg.reifying);
      let cfg = {cfg with reifying=true} in
      translate cfg bs (fst arg)

    | Tm_app(head, args) ->
      debug (fun () -> BU.print2 "Application: %s @ %s\n" (P.term_to_string head) (P.args_to_string args));
      iapp (translate cfg bs head) (List.map (fun x -> (translate cfg bs (fst x), snd x)) args) // Zoe : TODO avoid translation pass for args

    | Tm_match(scrut, branches) ->
      let rec case (scrut : t) : t =
        match scrut with
        | Construct(c, us, args) -> (* Scrutinee is a constructed value *)
          (* Assuming that all the arguments to the pattern constructors
             are binders -- i.e. no nested patterns for now *)
          debug (fun () ->
                 BU.print1 "Match args: %s\n"
                            (args
                             |> List.map (fun (x, q) -> (if BU.is_some q then "#" else "") ^ t_to_string x)
                             |> String.concat "; "));
          begin
          match pickBranch cfg scrut branches with
          | Some (branch, args) ->
            translate cfg (List.fold_left (fun bs x -> x::bs) bs args) branch
          | None -> //no branch is determined
            mkAccuMatch scrut case make_branches
          end
        | Constant c ->
          (* same as for construted values, but args are either empty or is a singleton list (for wildcard patterns) *)
          (match pickBranch cfg scrut branches with
           | Some (branch, []) ->
             translate cfg bs branch
           | Some (branch, [arg]) ->
             translate cfg (arg::bs) branch
           | None -> //no branch is determined
             mkAccuMatch scrut case make_branches
           | Some (_, hd::tl) -> failwith "Impossible: Matching on constants cannot bind more than one variable")

        | _ ->
          mkAccuMatch scrut case make_branches
      (* Thunked computation that reconstructs the patterns *)
      (* Zoe TODO : maybe rewrite in CPS? *)
      and make_branches (readback:t -> term) : list<branch> =
        let rec process_pattern bs (p:pat) : list<t> * pat = (* returns new environment and pattern *)
          let (bs, p_new) =
            match p.v with
            | Pat_constant c -> (bs, Pat_constant c)
            | Pat_cons (fvar, args) ->
              let (bs', args') =
                  List.fold_left (fun (bs, args) (arg, b) ->
                                    let (bs', arg') = process_pattern bs arg in
                                    (bs', (arg', b) :: args)) (bs, []) args
              in
              (bs', Pat_cons (fvar, List.rev args'))
            | Pat_var bvar ->
              let x = S.new_bv None (readback (translate cfg bs bvar.sort)) in
              (mkAccuVar x :: bs, Pat_var x)
            | Pat_wild bvar ->
              let x = S.new_bv None (readback (translate cfg bs bvar.sort)) in
              (mkAccuVar x :: bs, Pat_wild x)
              (* Zoe: I'm not sure what this pattern binds, just speculating the translation *)
            | Pat_dot_term (bvar, tm) ->
              let x = S.new_bv None (readback (translate cfg bs bvar.sort)) in
              (mkAccuVar x :: bs,
               Pat_dot_term (x, readback (translate cfg bs tm)))
          in
          (bs, {p with v = p_new}) (* keep the info and change the pattern *)
        in
        List.map (fun (pat, when_clause, e) ->
                  let (bs', pat') = process_pattern bs pat in
                  (* TODO : handle when clause *)
                  U.branch (pat', when_clause, readback (translate cfg bs' e))) branches
      in
      case (translate cfg bs scrut)

    | Tm_meta (e, Meta_monadic(m, t))
        when cfg.reifying ->
      translate_monadic (m, t) cfg bs e

    | Tm_meta (e, Meta_monadic_lift(m, m', t))
        when cfg.reifying ->
      translate_monadic_lift (m, m', t) cfg bs e

    | Tm_let((false, lbs), body) -> // non-recursive let
      let bs' =
        List.fold_left (fun bs' lb -> let b = translate_letbinding cfg bs lb in b :: bs') bs lbs  in
      translate cfg bs' body

    | Tm_let((true, lbs), body) ->
      translate cfg (make_rec_env lbs bs) body (* Danel: storing the rec. def. as F* code wrapped in a thunk *)

    | Tm_meta (e, _) ->
      //TODO: we need to put the "meta" back when reading back
      translate cfg bs e

    | Tm_lazy _ | Tm_quoted(_,_) -> failwith "Not yet handled"

and translate_monadic (m, ty) cfg bs e : t =
   let e = U.unascribe e in
   match e.n with
   | Tm_let((false, [lb]), body) -> //elaborate this to M.bind
     begin
     match Env.effect_decl_opt cfg.tcenv (Env.norm_eff_name cfg.tcenv m) with
     | None ->
       failwith (BU.format1 "Effect declaration not found: %s" (Ident.string_of_lid m))

     | Some (ed, q) ->
       let cfg' = {cfg with reifying=false} in
       let body_lam =
           let body_rc = {
                residual_effect=m;
                residual_flags=[];
                residual_typ=Some ty
            } in
           S.mk (Tm_abs([(BU.left lb.lbname, None)], body, Some body_rc)) None body.pos
       in
       let maybe_range_arg =
           if BU.for_some (U.attr_eq U.dm4f_bind_range_attr) ed.eff_attrs
           then [translate cfg [] (EMB.embed EMB.e_range lb.lbpos lb.lbpos), None;
                 translate cfg [] (EMB.embed EMB.e_range body.pos body.pos), None]
           else []
       in
       iapp (iapp (translate cfg' [] (U.un_uinst (snd ed.bind_repr)))
                  [Univ U_unknown, None;  //We are cheating here a bit
                   Univ U_unknown, None]) //to avoid re-computing the universe of lb.lbtyp
                                          //and ty below; but this should be okay since these
                                          //arguments should not actually appear in the resulting
                                          //term
           (
           [(translate cfg' bs lb.lbtyp, None); //translating the type of the bound term
            (translate cfg' bs ty, None)]       //and the body is sub-optimal; it is often unused
           @maybe_range_arg    //some effects take two additional range arguments for debugging
           @[(Unknown, None) ; //unknown WP of lb.lbdef; same as the universe argument ... should not appear in the result
            (translate cfg bs lb.lbdef, None);
            (Unknown, None) ;  //unknown WP of body; ditto
            (translate cfg bs body_lam, None)]
           )

      end

   | Tm_app({n=Tm_constant (FC.Const_reflect _)}, [(e, _)]) ->
     translate ({cfg with reifying=false}) bs e


   | _ -> failwith (BU.format1 "Unexpected case in translate_monadic: %s" (P.tag_of_term e))

and translate_monadic_lift (msrc, mtgt, ty) cfg bs e : t =
   let e = U.unascribe e in
   if U.is_pure_effect msrc || U.is_div_effect msrc
   then let ed = Env.get_effect_decl cfg.tcenv (Env.norm_eff_name cfg.tcenv mtgt) in
        let cfg' = {cfg with reifying=false} in
        iapp (iapp (translate cfg' [] (U.un_uinst (snd ed.return_repr)))
                   [Univ U_unknown, None])
              [(translate cfg' bs ty, None); //translating the type of the returned term
               (translate cfg' bs e, None)]  //translating the returned term itself
   else
    match Env.monad_leq cfg.tcenv msrc mtgt with
    | None ->
      failwith (BU.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                            (Ident.text_of_lid msrc)
                            (Ident.text_of_lid mtgt))
    | Some {mlift={mlift_term=None}} ->
      failwith (BU.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                            (Ident.text_of_lid msrc)
                            (Ident.text_of_lid mtgt))

    | Some {mlift={mlift_term=Some lift}} ->
      (* We don't have any reasonable wp to provide so we just pass unknow *)
      (* Usually the wp is only necessary to typecheck, so this should not *)
      (* create a big issue. *)
      let lift_lam =
        let x = S.new_bv None S.tun in
        U.abs [(x, None)]
              (lift U_unknown ty S.tun (S.bv_to_name x))
              None
      in
      let cfg' = {cfg with reifying=false} in
      iapp (translate cfg' [] lift_lam)
           [(translate cfg bs e, None)]

(* [readback] creates named binders and not De Bruijn *)
and readback (cfg:Cfg.cfg) (x:t) : term =
    let debug = debug cfg in
    debug (fun () -> BU.print1 "Readback: %s\n" (t_to_string x));
    match x with
    | Univ u -> failwith "Readback of universes should not occur"

    | Unknown -> S.mk Tm_unknown None Range.dummyRange

    | Constant Unit -> S.unit_const
    | Constant (Bool true) -> U.exp_true_bool
    | Constant (Bool false) -> U.exp_false_bool
    | Constant (Int i) -> Z.string_of_big_int i |> U.exp_int
    | Constant (String (s, r)) -> mk (S.Tm_constant (C.Const_string (s, r))) None Range.dummyRange
    | Constant (Char c) -> U.exp_char c
    | Constant (Range r) -> EMB.embed EMB.e_range r Range.dummyRange

    | Type_t u ->
      S.mk (Tm_type u) None Range.dummyRange

    | Lam (f, targs, arity) ->
      let (args, accus) = List.fold_left (fun (args, accus) tf ->
                                            let (xt, q) = tf () in
                                            let x = S.new_bv None (readback cfg xt) in
                                            ((x, q) :: args, (mkAccuVar x) :: accus)) ([], []) targs
      in
      let body = readback cfg (f accus) in
      U.abs args body None

    | Construct (fv, us, args) ->
      let args = map_rev (fun (x, q) -> (readback cfg x, q)) args in
      let apply tm =
      match args with
      | [] -> tm
      | _ ->  U.mk_app tm args
      in
      (match us with
       | _ :: _ -> apply (S.mk_Tm_uinst (S.mk (Tm_fvar fv) None Range.dummyRange) (List.rev us))
       | [] -> apply (S.mk (Tm_fvar fv) None Range.dummyRange))

    | FV (fv, us, args) ->
      let args = map_rev (fun (x, q) -> (readback cfg x, q)) args in
      let apply tm =
        match args with
         | [] -> tm
         | _ ->  U.mk_app tm args
      in
      let tm () =
        match us with
        | _ :: _ -> apply (S.mk_Tm_uinst (S.mk (Tm_fvar fv) None Range.dummyRange) (List.rev us))
        | [] -> apply (S.mk (Tm_fvar fv) None Range.dummyRange)
      in
      (match Cfg.find_prim_step cfg fv with
       | Some prim_step when prim_step.strong_reduction_ok (* TODO : || not cfg.strong *) ->
         (* TODO : can primops be universe polymorphic? *)
         begin
           let l = List.length args in
           let args_1, args_2 = if l = prim_step.arity
                                then args, []
                                else List.splitAt prim_step.arity args
           in
           let psc = {
             Cfg.psc_range = Range.dummyRange;
             Cfg.psc_subst = (fun () -> if prim_step.requires_binder_substitution
                                 then failwith "Cannot handle primops that require substitution"
                                 else [])
           } in
           match prim_step.interpretation psc args_1 with
           | Some tm -> U.mk_app tm args_2
           | None -> tm ()
         end
       | _ -> tm ())

    | Accu (Var bv, []) ->
      S.bv_to_name bv

    | Accu (Var bv, ts) ->
      let args = map_rev (fun (x, q) -> (readback cfg x, q)) ts in
      U.mk_app (S.bv_to_name bv) args

    | Accu (Match (scrut, cases, make_branches), ts) ->
      let args = map_rev (fun (x, q) -> (readback cfg x, q)) ts in
      let head =
        let scrut_new = readback cfg scrut in
        let branches_new = make_branches (readback cfg) in
        S.mk (Tm_match (scrut_new, branches_new)) None Range.dummyRange
      in
      (*  When `cases scrut` returns a Accu(Match ..))
          we need to reconstruct a source match node.

          To do this, we need to decorate that Match node with the
          patterns in each branch.

          e.g., Consider this source node:

              (match x with
               | Inl (a:ta) -> e1
               | Inr (b:tb) -> e2)

          Match([[x]],
                (cases: t -> t),
                (patterns:[Inl (a:ta); Inr (b:tb)]))

          let branches =
            map (fun v -> v, readback (cases (translate v)))
                patterns
          in
          match (readback [[x]])
                branches
       *)

      (match ts with
       | [] -> head
       | _ -> U.mk_app head args)

    | Accu (Rec(lb, lbs, bs), ts) ->
       let rec curry hd args =
       match args with
       | [] -> hd
       | [arg] -> app cfg hd (fst arg) (snd arg)
       | arg :: args -> app cfg (curry hd args) (fst arg) (snd arg)
       in
       let args_no = count_abstractions lb.lbdef in
       // Printf.printf "Args no. %d\n" args_no;
       if test_args ts args_no then (* if the arguments are not symbolic and the application is not partial compute *)
         readback cfg (curry (translate_letbinding cfg (make_rec_env lbs bs) lb) ts)
       else (* otherwise do not unfold *)
         let head =
           (* Zoe: I want the head to be [let rec f = lb in f]. Is this the right way to construct it? *)
           let f = match lb.lbname with
                   | BU.Inl bv -> S.bv_to_name bv
                   | BU.Inr fv -> failwith "Not yet implemented"
           in
           S.mk (Tm_let((true, lbs), f)) None Range.dummyRange
         in
         let args = map_rev (fun (x, q) -> (readback cfg x, q)) ts in
         (match ts with
          | [] -> head
          | _ -> U.mk_app head args)
    | Arrow _ -> failwith "Arrows not yet handled"

    // | Refinement (b, r) ->
    //    let body = translate cfg [] (readback cfg r) in
    //    debug (fun () -> BU.print1 "Translated refinement body: %s\n" (t_to_string body));
    //    S.mk (Tm_refine(fst b, readback cfg body)) None Range.dummyRange

type step =
  | Primops
  | UnfoldUntil of delta_depth
  | UnfoldOnly  of list<FStar.Ident.lid>
  | UnfoldAttr of attribute
  | UnfoldTac
  | Reify

let step_as_normalizer_step = function
  | Primops -> Env.Primops
  | UnfoldUntil d -> Env.UnfoldUntil d
  | UnfoldOnly lids -> Env.UnfoldOnly lids
  | UnfoldAttr attr -> Env.UnfoldAttr attr
  | UnfoldTac -> Env.UnfoldTac
  | Reify -> Env.Reify

let normalize' (steps:list<Env.step>) (env : Env.env) (e:term) : term =
  let cfg = Cfg.config steps env in
  //debug_sigmap env.sigtab;
  let cfg = {cfg with steps={cfg.steps with reify_=true}} in
  readback cfg (translate cfg [] e)


  (* ONLY FOR UNIT TESTS! *)
let test_normalize (steps:list<step>) (env : Env.env) (e:term) : term =
  let cfg = Cfg.config (List.map step_as_normalizer_step steps) env in
  //debug_sigmap env.sigtab;
  let cfg = {cfg with steps={cfg.steps with reify_=true}} in
  readback cfg (translate cfg [] e)


