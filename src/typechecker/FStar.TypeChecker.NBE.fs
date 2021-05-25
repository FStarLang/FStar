(*
   Copyright 2017-2019 Microsoft Research

   Authors: Zoe Paraskevopoulou, Guido Martinez, Nikhil Swamy

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
#light "off"
module FStar.TypeChecker.NBE
open FStar.Pervasives
open FStar.All
open FStar.Exn
open FStar
open FStar.TypeChecker.Cfg
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

(* Broadly, the algorithm implemented here is inspired by

   Full Reduction at Full Throttle:
     https://dl.acm.org/citation.cfm?id=2178141

   Except, we don't implement any of the native tricks in the OCaml
   runtime for compiling inductives and pattern matching. So, you
   could see what we're doing here as, perhaps, "Full Reduction at
   Half Throttle".

   More classically, what we have here is a definitional interpreter,
   in the tradition of Reynolds' Definitional Interpreters:
     https://dl.acm.org/citation.cfm?id=805852 (1972)
     A more recent version of that paper is here:
     http://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/reynolds-definitional-interpreters-1998.pdf

   The broad idea of the algorithm is sketched for a tiny lambda
   calculus in examples/metatheory/FullReductionInterpreter.fst

   That's a good thing to digest before getting into the complexity of
   the module here.

   A lot of the complexity here is in handling all the features of F*,
   notably in the handling of inductive datatypes, pattern matching,
   recursive definitions, and reified effects.
*)


////////////////////////////////////////////////////////////////////////////////
// Utilities: Many of these should just move to FStar.List, if it's
// not already there
////////////////////////////////////////////////////////////////////////////////

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

let fmap_opt (f : 'a -> 'b) (x : option<'a>) : option<'b> =
  BU.bind_opt x (fun x -> Some (f x))

let drop_until (f : 'a -> bool) (l : list<'a>) : list<'a> =
  let rec aux l =
    match l with
    | [] -> []
    | x :: xs -> if f x then l else aux xs
  in aux l

let trim (l : list<bool>) : list<bool> = (* trim a list of booleans after the last true *)
    List.rev (drop_until id (List.rev l))


let implies b1 b2 =
  match b1, b2 with
  | false, _ -> true
  | true, b2 -> b2

let let_rec_arity (b:letbinding) : int * list<bool> =
  let (ar, maybe_lst) = U.let_rec_arity b in
  match maybe_lst with
  | None ->
    ar,
    FStar.Common.tabulate ar (fun _ -> true) (* treat all arguments as recursive *)
  | Some lst ->
    ar, lst
    // let l = trim lst in
    // List.length l, l

// NBE debuging

let debug_term (t : term) =
  BU.print1 "%s\n" (P.term_to_string t)

let debug_sigmap (m : BU.smap<sigelt>) =
  BU.smap_fold m (fun k v u -> BU.print2 "%s -> %%s\n" k (P.sigelt_to_string_short v)) ()


////////////////////////////////////////////////////////////////////////////////
//End utilities
////////////////////////////////////////////////////////////////////////////////
type config = {
  core_cfg:Cfg.cfg;
  fv_cache:BU.smap<t>
}
let new_config (cfg:Cfg.cfg) = {
  core_cfg = cfg;
  fv_cache = BU.smap_create 51
}
let reifying_false (cfg:config) =
  if cfg.core_cfg.reifying
  then new_config ({cfg.core_cfg with reifying=false}) //blow away cache
  else cfg
let reifying_true (cfg:config) =
  if not (cfg.core_cfg.reifying)
  then new_config ({cfg.core_cfg with reifying=true}) //blow away cache
  else cfg
let zeta_false (cfg:config) =
    let cfg_core = cfg.core_cfg in
    if cfg_core.steps.zeta
    then
      let cfg_core' = {cfg_core with steps={cfg_core.steps with zeta=false}} in // disable zeta flag
      new_config cfg_core' //blow away cache
    else cfg
let cache_add (cfg:config) (fv:fv) (v:t) =
  let lid = fv.fv_name.v in
  BU.smap_add cfg.fv_cache (string_of_lid lid) v
let try_in_cache (cfg:config) (fv:fv) : option<t> =
  let lid = fv.fv_name.v in
  BU.smap_try_find cfg.fv_cache (string_of_lid lid)
let debug cfg f =
  log_nbe cfg.core_cfg f

(* GM, Aug 19th 2018: This should not (at least always) be recursive.
 * Forcing the thunk on an NBE term (Lazy i) triggers arbitrary
 * computation, and it might very well turn out to normalize to another
 * (Lazy i') (probably with i=i'). An example, from Meta-F*, is
 * (pack_binder (pack_bv .., Q_Explicit)).
 *)
let rec unlazy_unmeta t =
    match t.nbe_t with
    | Lazy (_, t) -> unlazy_unmeta (Thunk.force t)
    | Meta(t0, m) ->
      begin
      match Thunk.force m with
      | Meta_monadic(_, _)
      | Meta_monadic_lift(_, _, _) -> t
      | _ -> unlazy_unmeta t0
      end
    | _ -> t

let pickBranch (cfg:config) (scrut : t) (branches : list<branch>) : option<(term * list<t>)> =
  let all_branches = branches in
  let rec pickBranch_aux (scrut : t) (branches : list<branch>) (branches0 : list<branch>) : option<(term * list<t>)> =
    //NS: adapted from FStar.TypeChecker.Normalize: rebuild_match
    let rec matches_pat (scrutinee0:t) (p:pat)
        : either<list<t>, bool> =
        (* Inl ts: p matches t and ts are bindings for the branch *)
        (* Inr false: p definitely does not match t *)
        (* Inr true: p may match t, but p is an open term and we cannot decide for sure *)
        debug cfg (fun () -> BU.print2 "matches_pat (%s, %s)\n" (t_to_string scrutinee0) (P.pat_to_string p));
        let scrutinee = unlazy_unmeta scrutinee0 in
        let r = match p.v with
        | Pat_var bv
        | Pat_wild bv ->
            // important to use the non-unfolded variant, some embeddings
            // have no decent unfolding (i.e. they cheat)
            Inl [scrutinee0]

        | Pat_dot_term _ ->
            Inl []

        | Pat_constant s ->
            let matches_const (c: t) (s: S.sconst) =
                debug cfg (fun () -> BU.print2 "Testing term %s against pattern %s\n"
                                    (t_to_string c) (P.const_to_string s));
                match c.nbe_t with
                | Constant (Unit) -> s = C.Const_unit
                | Constant (Bool b) -> (match s with | C.Const_bool p -> b = p | _ -> false)
                | Constant (Int i) -> (match s with | C.Const_int (p, None) -> i = Z.big_int_of_string p | _ -> false)
                | Constant (String (st, _)) -> (match s with | C.Const_string(p, _) -> st = p | _ -> false)
                | Constant (Char c) -> (match s with | C.Const_char p -> c = p | _ -> false)
                | _ -> false
            in
            if matches_const scrutinee s then Inl [] else Inr false

        | Pat_cons(fv, arg_pats) ->
            let rec matches_args out (a:list<(t * aqual)>) (p:list<(pat * bool)>)
                : either<list<t>, bool> =
                match a, p with
                | [], [] -> Inl out
                | (t, _)::rest_a, (p, _)::rest_p ->
                  (match matches_pat t p with
                   | Inl s -> matches_args (out@s) rest_a rest_p
                   | m -> m)
                | _ ->
                Inr false
            in
            match scrutinee.nbe_t with
            | Construct(fv', _us, args_rev) ->
                if fv_eq fv fv'
                then matches_args [] (List.rev args_rev) arg_pats
                else Inr false

            | _ -> //must be a variable
              Inr true
        in
        let res_to_string = function
        | Inr b -> "Inr " ^ BU.string_of_bool b
        | Inl bs -> "Inl " ^ BU.string_of_int (List.length bs)
        in
        debug cfg (fun () -> BU.print3 "matches_pat (%s, %s) = %s\n" (t_to_string scrutinee) (P.pat_to_string p) (res_to_string r));
        r
    in
    match branches with
    | [] ->
      None

    // TODO: Consider the when clause!
    | (p, _wopt, e)::branches ->
      match matches_pat scrut p with
      | Inl matches ->
        debug cfg (fun () -> BU.print1 "Pattern %s matches\n" (P.pat_to_string p));
        Some (e, matches)
      | Inr false -> //definitely did not match
        pickBranch_aux scrut branches branches0
      | Inr true -> //maybe matches; stop
        None
  in pickBranch_aux scrut branches branches

// Tests if a recursive function should be reduced based on
// the arguments provided and the arity/decreases clause of the function.
// Returns:
//  should_unfold: bool, true, if the application is full and if none of the recursive
//                 arguments is symbolic.
//  arguments : list<arg>, the arguments to the recursive function in reverse order
//  residual args: list<arg>, any additional arguments, beyond the arity of the function
let should_reduce_recursive_definition
       (arguments:args)
       (formals_in_decreases:list<bool>)
  : (bool * args * args) (* can unfold x full arg list x residual args *)
  =
  let rec aux ts ar_list acc =
    match ts, ar_list with
    | _, [] ->
      true, acc, ts
    | [], _ :: _ ->
      false, acc, []  (* It's partial! *)
    | t :: ts, in_decreases_clause :: bs ->
      if in_decreases_clause
      && isAccu (fst t)  //one of the recursive arguments is symbolic, so we shouldn't reduce
      then false, List.rev_append ts acc, []
      else aux ts bs (t::acc)
  in
  aux arguments formals_in_decreases []

let find_sigelt_in_gamma cfg (env: Env.env) (lid:lident): option<sigelt> =
  let mapper (lr, rng) =
    match lr with
    | Inr (elt, None) -> Some elt
    | Inr (elt, Some us) ->
        debug cfg (fun () -> BU.print1 "Universes in local declaration: %s\n" (P.univs_to_string us));
        Some elt
    | _ -> None in
  BU.bind_opt (Env.lookup_qname env lid) mapper

let is_univ (tm : t) =
  match tm.nbe_t with
  | Univ _ -> true
  | _ -> false

let un_univ (tm:t) : universe =
  match tm.nbe_t with
  | Univ u -> u
  | _ -> failwith ("Not a universe: " ^ t_to_string tm)

let is_constr_fv (fvar : fv) : bool =
  fvar.fv_qual = Some Data_ctor

let is_constr (q : qninfo) : bool =
  match q with
  | Some (Inr ({ sigel = Sig_datacon (_, _, _, _, _, _) }, _), _) -> true
  | _ -> false

let translate_univ (cfg:config) (bs:list<t>) (u:universe) : universe =
  let rec aux u =
    let u = SS.compress_univ u in
      match u with
      | U_bvar i ->
        if i < List.length bs
        then
          let u' = List.nth bs i in //it has to be a Univ term at position i
          (un_univ u')
        else if cfg.core_cfg.steps.allow_unbound_universes
        then U_zero
        else failwith "Universe index out of bounds"

      | U_succ u -> U_succ (aux u)

      | U_max us -> U_max (List.map aux us)

      | U_unknown | U_name _ | U_unif _ | U_zero -> u
    in
    aux u

let find_let (lbs : list<letbinding>) (fvar : fv) =
  BU.find_map lbs (fun lb -> match lb.lbname with
                   | Inl _ -> failwith "find_let : impossible"
                   | Inr name ->
                     if fv_eq name fvar
                     then Some lb
                     else None)

let mk_rt r t = { nbe_t = t; nbe_r = r }
let mk_t t = { nbe_t = t; nbe_r = Range.dummyRange }

/// Normalization is implemented using two mutually recursive functions,
/// translate and readback,
///  i.e., `norm cfg t = readback cfg (translate cfg [] t)`
///
/// For `translate`:
///
///  - `cfg` records various configuration options, e.g., which
///     definitions are to be unfolded
///
/// -  `bs` is an environment for the bound variables in scope, in de
///     Bruijn order (i.e., most recent binders are the head of the list)
///
/// -  `e:term` is the syntax being reduced
///
/// The main idea is to translate syntactic entities, notably
/// functions, into functions of the host language; and
/// correspondingly, source beta redexes into host language
/// applications. As such, the process of translation triggers
/// call-by-value reduction of the syntax, relying on the reduction
/// strategy of the host.
let rec translate (cfg:config) (bs:list<t>) (e:term) : t =
    let debug = debug cfg in
    let mk_t t = mk_rt e.pos t in
    debug (fun () -> BU.print2 "Term: %s - %s\n" (P.tag_of_term (SS.compress e)) (P.term_to_string (SS.compress e)));
//    debug (fun () -> BU.print1 "BS list: %s\n" (String.concat ";; " (List.map (fun x -> t_to_string x) bs)));
    match (SS.compress e).n with
    | Tm_delayed (_, _) ->
      failwith "Tm_delayed: Impossible"

    | Tm_unknown ->
      mk_t Unknown

    | Tm_constant c ->
      mk_t <| Constant (translate_constant c)

    | Tm_bvar db -> //de Bruijn
      if db.index < List.length bs
      then
        let t = List.nth bs db.index in
        debug (fun () -> BU.print2 "Resolved bvar to %s\n\tcontext is [%s]\n"
                    (t_to_string t)
                    (List.map t_to_string bs |> String.concat "; ")
                    );
        t
      else failwith "de Bruijn index out of bounds"

    | Tm_uinst(t, us) ->
      debug (fun () -> BU.print2 "Uinst term : %s\nUnivs : %s\n" (P.term_to_string t)
                                                              (List.map P.univ_to_string us |> String.concat ", "));
      iapp cfg (translate cfg bs t) (List.map (fun x -> as_arg (mk_t <| Univ (translate_univ cfg bs x))) us)

    | Tm_type u ->
      mk_t <| Type_t (translate_univ cfg bs u)

    | Tm_arrow (xs, c) ->
      let norm () =
        let ctx, binders_rev =
          List.fold_left
            (fun (ctx, binders_rev) b ->
              let x = b.binder_bv in
              let t = readback cfg (translate cfg ctx x.sort) in
              let x = { S.freshen_bv x with sort = t } in
              let ctx = mkAccuVar x :: ctx in
              ctx, ({b with binder_bv=x}) :: binders_rev)
            (bs, [])
            xs
        in
        let c = readback_comp cfg (translate_comp cfg ctx c) in
        U.arrow (List.rev binders_rev) c
      in
      mk_t <| Arrow (Inl (Thunk.mk norm))

    | Tm_refine (bv, tm) ->
      if cfg.core_cfg.steps.for_extraction
      then translate cfg bs bv.sort //if we're only extracting, then drop the refinement
      else mk_t <| Refinement ((fun (y:t) -> translate cfg (y::bs) tm),
                              (fun () -> as_arg (translate cfg bs bv.sort))) // XXX: Bogus type?

    | Tm_ascribed (t, _, _) ->
      translate cfg bs t

    | Tm_uvar (u, (subst, set_use_range)) ->
      let norm_uvar () =
        let norm_subst_elt = function
          | NT(x, t) ->
            NT(x, readback cfg (translate cfg bs t))
          | NM(x, i) ->
            let x_i = S.bv_to_tm ({x with index=i}) in
            let t = readback cfg (translate cfg bs x_i) in
            (match t.n with
            | Tm_bvar x_j -> NM(x, x_j.index)
            | _ -> NT(x, t))
          | _ -> failwith "Impossible: subst invariant of uvar nodes"
        in
        let subst = List.map (List.map norm_subst_elt) subst in
        { e with n = Tm_uvar(u, (subst, set_use_range)) }
      in
      mk_t <| Accu(UVar (Thunk.mk norm_uvar), [])

    | Tm_name x ->
      mkAccuVar x

    | Tm_abs ([], _, _) -> failwith "Impossible: abstraction with no binders"

    | Tm_abs (xs, body, resc) ->
      mk_t <| Lam ((fun ys -> translate cfg (List.append ys bs) body),
                  Inl (bs, xs, resc),
                  List.length xs)

    | Tm_fvar fvar ->
      begin
      match try_in_cache cfg fvar with
      | Some t -> t
      | _ -> translate_fv cfg bs (S.set_range_of_fv fvar e.pos)
      end

    | Tm_app({n=Tm_constant FC.Const_reify},   arg::more::args)
    | Tm_app({n=Tm_constant (FC.Const_reflect _)}, arg::more::args) ->
      let head, _ = U.head_and_args e in
      let head = S.mk_Tm_app head [arg] e.pos in
      translate cfg bs (S.mk_Tm_app head (more::args) e.pos)

    | Tm_app({n=Tm_constant (FC.Const_reflect _)}, [arg]) when cfg.core_cfg.reifying ->
      let cfg = reifying_false cfg in
      translate cfg bs (fst arg)

    | Tm_app({n=Tm_constant (FC.Const_reflect _)}, [arg]) ->
      mk_t <| Reflect (translate cfg bs (fst arg))

    | Tm_app({n=Tm_constant FC.Const_reify}, [arg])
        when cfg.core_cfg.steps.reify_ ->
      assert (not cfg.core_cfg.reifying);
      let cfg = reifying_true cfg in
      translate cfg bs (fst arg)

    | Tm_app(head, args) ->
      debug (fun () -> BU.print2 "Application: %s @ %s\n" (P.term_to_string head) (P.args_to_string args));
      iapp cfg (translate cfg bs head) (List.map (fun x -> (translate cfg bs (fst x), snd x)) args) // Zoe : TODO avoid translation pass for args

    | Tm_match(scrut, ret_opt, branches) ->
      (* Thunked computation to reconstrct the returns annotation *)
      let make_returns () : option<ascription> =
        match ret_opt with
        | None -> None
        | Some (Inl t, tacopt) -> Some (Inl (readback cfg (translate cfg bs t)), tacopt)
        | Some (Inr c, tacopt) -> Some (Inr (readback_comp cfg (translate_comp cfg bs c)), tacopt) in

      (* Thunked computation that reconstructs the patterns *)
      let make_branches () : list<branch> =
        let cfg = zeta_false cfg in
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
              let x = S.new_bv None (readback cfg (translate cfg bs bvar.sort)) in
              (mkAccuVar x :: bs, Pat_var x)
            | Pat_wild bvar ->
              let x = S.new_bv None (readback cfg (translate cfg bs bvar.sort)) in
              (mkAccuVar x :: bs, Pat_wild x)
            | Pat_dot_term (bvar, tm) ->
              let x = S.new_bv None (readback cfg (translate cfg bs bvar.sort)) in
              (bs,
               Pat_dot_term (x, readback cfg (translate cfg bs tm)))
          in
          (bs, {p with v = p_new}) (* keep the info and change the pattern *)
        in
        List.map (fun (pat, when_clause, e) ->
                  let (bs', pat') = process_pattern bs pat in
                  (* TODO : handle when clause *)
                  U.branch (pat', when_clause, readback cfg (translate cfg bs' e))) branches
      in

      let scrut = translate cfg bs scrut in
      debug (fun () -> BU.print2 "%s: Translating match %s\n"
                              (Range.string_of_range e.pos)
                              (P.term_to_string e));
      let scrut = unlazy_unmeta scrut in
      begin
      match scrut.nbe_t with
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
            mkAccuMatch scrut make_returns make_branches
          end
      | Constant c ->
          debug (fun () -> BU.print1 "Match constant : %s\n" (t_to_string scrut));
          (* same as for construted values, but args are either empty or is a singleton list (for wildcard patterns) *)
          (match pickBranch cfg scrut branches with
           | Some (branch, []) ->
             translate cfg bs branch
           | Some (branch, [arg]) ->
             translate cfg (arg::bs) branch
           | None -> //no branch is determined
             mkAccuMatch scrut make_returns make_branches
           | Some (_, hd::tl) ->
             failwith "Impossible: Matching on constants cannot bind more than one variable")

        | _ ->
          mkAccuMatch scrut make_returns make_branches
      end

    | Tm_meta (e, Meta_monadic(m, t))
        when cfg.core_cfg.reifying ->
      translate_monadic (m, t) cfg bs e

    | Tm_meta (e, Meta_monadic_lift(m, m', t))
        when cfg.core_cfg.reifying ->
      translate_monadic_lift (m, m', t) cfg bs e

    | Tm_meta (e, meta) ->
      let norm_meta () =
        let norm t = readback cfg (translate cfg bs t) in
        match meta with
          | Meta_named _
          | Meta_labeled _
          | Meta_desugared _ -> meta
          | Meta_pattern (ts, args) ->
            Meta_pattern (List.map norm ts,
                          List.map (List.map (fun (t, a) -> norm t, a)) args)
          | Meta_monadic(m, t) ->
            Meta_monadic(m, norm t)
          | Meta_monadic_lift(m0, m1, t) ->
            Meta_monadic_lift(m0, m1, norm t)
      in
      mk_t <| Meta(translate cfg bs e, Thunk.mk norm_meta)

    | Tm_let((false, [lb]), body) -> // non-recursive let
      if Cfg.should_reduce_local_let cfg.core_cfg lb
      then if cfg.core_cfg.steps.for_extraction
           && U.is_unit lb.lbtyp
           && U.is_pure_or_ghost_effect lb.lbeff
           then let bs = mk_rt (S.range_of_lbname lb.lbname) (Constant Unit) :: bs in
                translate cfg bs body
           else let bs = translate_letbinding cfg bs lb :: bs in
                translate cfg bs body
      else let def () =
               if cfg.core_cfg.steps.for_extraction
               && U.is_unit lb.lbtyp
               && U.is_pure_or_ghost_effect lb.lbeff
               then mk_t <| Constant Unit
               else translate cfg bs lb.lbdef
           in
           let typ () = translate cfg bs lb.lbtyp in
           let name = freshen_bv (BU.left lb.lbname) in
           let bs = mk_rt (S.range_of_bv name) (Accu (Var name, [])) :: bs in
           let body () = translate cfg bs body in
           mk_t <| Accu(UnreducedLet(name, Thunk.mk typ, Thunk.mk def, Thunk.mk body, lb), [])

    | Tm_let((_rec, lbs), body) -> //recursive let
      if not cfg.core_cfg.steps.zeta &&
         cfg.core_cfg.steps.pure_subterms_within_computations
      then //can't reduce this let rec
           let vars = List.map (fun lb -> freshen_bv (BU.left lb.lbname)) lbs in
           let typs = List.map (fun lb -> translate cfg bs lb.lbtyp) lbs in
           let rec_bs = List.map (fun v -> mk_rt (S.range_of_bv v) <| Accu (Var v, [])) vars @ bs in
           let defs = List.map (fun lb -> translate cfg rec_bs lb.lbdef) lbs in
           let body = translate cfg rec_bs body in
           mk_t <| Accu(UnreducedLetRec(List.zip3 vars typs defs, body, lbs), [])
      else translate cfg (make_rec_env lbs bs) body

    | Tm_quoted (qt, qi) ->
      let close t =
        let bvs = List.map (fun _ -> S.new_bv None S.tun) bs in
        let s1 = List.mapi (fun i bv -> DB (i, bv)) bvs in
        let s2 = List.map (fun (bv, t) -> NT (bv, readback cfg t)) (List.zip bvs bs) in
        SS.subst s2 (SS.subst s1 t)
      in
      begin match qi.qkind with
      | Quote_dynamic ->
        let qt = close qt in
        mk_t <| Quote (qt, qi)
      | Quote_static  ->
        let qi = S.on_antiquoted close qi in
        mk_t <| Quote (qt, qi)
      end

    | Tm_lazy li ->
      let f () =
          let t = U.unfold_lazy li in
          debug (fun () -> BU.print1 ">> Unfolding Tm_lazy to %s\n" (P.term_to_string t));
          translate cfg bs t
      in
      mk_t <| Lazy (Inl li, Thunk.mk f)

and translate_comp cfg bs (c:S.comp) : comp =
  match c.n with
  | S.Total  (typ, u) -> Tot (translate cfg bs typ, fmap_opt (translate_univ cfg bs) u)
  | S.GTotal (typ, u) -> GTot (translate cfg bs typ, fmap_opt (translate_univ cfg bs) u)
  | S.Comp   ctyp      -> Comp (translate_comp_typ cfg bs ctyp)

(* uncurried application *)
and iapp (cfg : config) (f:t) (args:args) : t =
  // meta and lazy nodes shouldn't block reduction
  let mk t = mk_rt f.nbe_r t in
  match (unlazy_unmeta f).nbe_t with
  | Lam (f, binders, n) ->
    let m = List.length args in
    if m < n then
      // partial application
      let arg_values_rev = map_rev fst args in
      let binders =
        match binders with
        | Inr raw_args ->
          let _, raw_args = List.splitAt m raw_args in
          Inr raw_args

        | Inl (ctx, xs, rc) ->
          let _, xs = List.splitAt m xs in
          let ctx = List.append arg_values_rev ctx in
          Inl (ctx, xs, rc)
      in
      mk <|
      Lam((fun l -> f (List.append l arg_values_rev)),
          binders,
          n - m)
    else if m = n then
      // full application
      let arg_values_rev = map_rev fst args in
      f arg_values_rev
    else
      // extra arguments
      let (args, args') = List.splitAt n args in
      iapp cfg (f (map_rev fst args)) args'
  | Accu (a, ts) -> mk <| Accu (a, List.rev_append args ts)
  | Construct (i, us, ts) ->
    let rec aux args us ts =
      match args with
      | ({nbe_t=Univ u}, _) :: args -> aux args (u :: us) ts
      | a :: args -> aux args us (a :: ts)
      | [] -> (us, ts)
    in
    let (us', ts') = aux args us ts in
    mk <| Construct (i, us', ts')
  | FV (i, us, ts) ->
    let rec aux args us ts =
      match args with
      | ({nbe_t=Univ u}, _) :: args -> aux args (u :: us) ts
      | a :: args -> aux args us (a :: ts)
      | [] -> (us, ts)
    in
    let (us', ts') = aux args us ts in
    mk <| FV (i, us', ts')

  | TopLevelLet(lb, arity, args_rev) ->
    let args_rev = List.rev_append args args_rev in
    let n_args_rev = List.length args_rev in
    let n_univs = List.length lb.lbunivs in
    debug cfg (fun () ->
      BU.print3 "Reached iapp for %s with arity %s and n_args = %s\n"
                (P.lbname_to_string lb.lbname)
                (BU.string_of_int arity)
                (BU.string_of_int n_args_rev));
    if n_args_rev >= arity
    then let bs, body =
           match (U.unascribe lb.lbdef).n with
           | Tm_abs(bs, body, _) -> bs, body
           | _ -> [], lb.lbdef
         in
         if n_univs + List.length bs = arity
         then let extra, args_rev = BU.first_N (n_args_rev - arity) args_rev in
              debug cfg (fun () ->
                BU.print3 "Reducing body of %s = %s,\n\twith args = %s\n"
                  (P.lbname_to_string lb.lbname)
                  (P.term_to_string body)
                  (List.map (fun (x, _) -> t_to_string x) args_rev |> String.concat ", "));
              let t = translate cfg (List.map fst args_rev) body in
              match extra with
              | [] -> t
              | _ -> iapp cfg t (List.rev extra)
         else let extra, univs = BU.first_N (n_args_rev - n_univs) args_rev in
              iapp cfg (translate cfg (List.map fst univs) lb.lbdef) (List.rev extra)
    else mk <| TopLevelLet (lb, arity, args_rev) //not enough args  yet

  | TopLevelRec (lb, arity, decreases_list, args') ->
    let args = List.append args' args in
    if List.length args >= arity
    then let should_reduce, _, _ =
           should_reduce_recursive_definition args decreases_list
         in
         if not should_reduce
         then begin
           let fv = BU.right lb.lbname in
           debug cfg (fun () -> BU.print1 "Decided to not unfold recursive definition %s\n" (P.fv_to_string fv));
           iapp cfg (mk_rt (S.range_of_fv fv) (FV (fv, [], []))) args
         end
         else begin
           debug cfg (fun () -> BU.print1 "Yes, Decided to unfold recursive definition %s\n" (P.fv_to_string (BU.right lb.lbname)));
           let univs, rest = BU.first_N (List.length lb.lbunivs) args in
           iapp cfg (translate cfg (List.rev (List.map fst univs)) lb.lbdef) rest
         end
    else //not enough args yet
         mk <| TopLevelRec (lb, arity, decreases_list, args)

  | LocalLetRec(i, lb, mutual_lbs, local_env, acc_args, remaining_arity, decreases_list) ->
    if remaining_arity = 0 //we've already decided to not unfold this, so just accumulate
    then mk <| LocalLetRec(i, lb, mutual_lbs, local_env, acc_args @ args, remaining_arity, decreases_list)
    else
      let n_args = List.length args in
      if n_args < remaining_arity //still a partial application, just accumulate
      then mk <| LocalLetRec(i, lb, mutual_lbs, local_env, acc_args @ args, remaining_arity - n_args, decreases_list)
      else begin
         let args = acc_args @ args in (* Not in reverse order *)
         let should_reduce, _, _ =
           should_reduce_recursive_definition args decreases_list
         in
         //local let binding don't have universes
         if not should_reduce
         then mk <| LocalLetRec(i, lb, mutual_lbs, local_env, args, 0, decreases_list)
         else let env = make_rec_env mutual_lbs local_env in
              let _ =
                debug cfg (fun () ->
                  BU.print1 "LocalLetRec Env = {\n\t%s\n}\n" (String.concat ",\n\t " (List.map t_to_string env));
                  BU.print1 "LocalLetRec Args = {\n\t%s\n}\n" (String.concat ",\n\t " (List.map (fun (t, _) -> t_to_string t) args)))
              in
              iapp cfg (translate cfg env lb.lbdef) args
      end

  | Constant (SConst FStar.Const.Const_range_of) ->
    begin
    match args with
    | [(a, _)] -> mk_rt a.nbe_r (Constant (Range a.nbe_r))
    | _ ->     failwith ("NBE ill-typed application: " ^ t_to_string f)
    end

  | Constant (SConst FStar.Const.Const_set_range_of) ->
    begin
    match args with
    | [(t, _); ({nbe_t=Constant (Range r)}, _)] ->
      { t with nbe_r = r}
    | _ ->      failwith ("NBE ill-typed application: " ^ t_to_string f)
    end
  | _ ->
    failwith ("NBE ill-typed application: " ^ t_to_string f)


and translate_fv (cfg: config) (bs:list<t>) (fvar:fv): t =
   let debug = debug cfg in
   let qninfo = Env.lookup_qname (Cfg.cfg_env cfg.core_cfg) (S.lid_of_fv fvar) in
   if is_constr qninfo || is_constr_fv fvar then mkConstruct fvar [] []
   else
     match N.should_unfold cfg.core_cfg (fun _ -> cfg.core_cfg.reifying) fvar qninfo with
     | N.Should_unfold_fully  ->
       failwith "Not yet handled"

     | N.Should_unfold_no ->
       debug (fun () -> BU.print1 "(1) Decided to not unfold %s\n" (P.fv_to_string fvar));
       begin match Cfg.find_prim_step cfg.core_cfg fvar with
       | Some prim_step when prim_step.strong_reduction_ok (* TODO : || not cfg.strong *) ->
         let arity = prim_step.arity + prim_step.univ_arity in
         debug (fun () -> BU.print1 "Found a primop %s\n" (P.fv_to_string fvar));
         mk_t <| Lam ((fun args_rev ->
                 let args' = map_rev NBETerm.as_arg args_rev in
                 let callbacks = {
                   iapp = iapp cfg;
                   translate = translate cfg bs;
                 }
                 in
                 match prim_step.interpretation_nbe callbacks args' with
                 | Some x ->
                   debug (fun () -> BU.print2 "Primitive operator %s returned %s\n" (P.fv_to_string fvar) (t_to_string x));
                   x
                 | None ->
                   debug (fun () -> BU.print1 "Primitive operator %s failed\n" (P.fv_to_string fvar));
                   iapp cfg (mkFV fvar [] []) args'),
              (let f (_:int) = S.mk_binder (S.new_bv None S.t_unit) in
               Inl ([], FStar.Common.tabulate arity f, None)),
              arity)

       | Some _ -> debug (fun () -> BU.print1 "(2) Decided to not unfold %s\n" (P.fv_to_string fvar)); mkFV fvar [] []
       | _      -> debug (fun () -> BU.print1 "(3) Decided to not unfold %s\n" (P.fv_to_string fvar)); mkFV fvar [] []
       end


     | N.Should_unfold_reify
     | N.Should_unfold_yes ->
       let t =
         let is_qninfo_visible =
           Option.isSome (Env.lookup_definition_qninfo cfg.core_cfg.delta_level fvar.fv_name.v qninfo)
         in
         if is_qninfo_visible
         then begin
           match qninfo with
           | Some (Inr ({ sigel = Sig_let ((is_rec, lbs), names) }, _us_opt), _rng) ->
             debug (fun () -> BU.print1 "(1) Decided to unfold %s\n" (P.fv_to_string fvar));
             let lbm = find_let lbs fvar in
             begin match lbm with
             | Some lb ->
               if is_rec && cfg.core_cfg.steps.zeta
               then
                 let ar, lst = let_rec_arity lb in
                 mk_rt (S.range_of_fv fvar) <| TopLevelRec(lb, ar, lst, [])
               else
                 translate_letbinding cfg bs lb
             | None -> failwith "Could not find let binding"
             end
           | _ ->
             debug (fun () -> BU.print1 "(1) qninfo is None for (%s)\n" (P.fv_to_string fvar));
             mkFV fvar [] []
           end
         else begin
           debug (fun () -> BU.print1 "(1) qninfo is not visible at this level (%s)\n" (P.fv_to_string fvar));
           mkFV fvar [] []
         end
       in
       cache_add cfg fvar t;
       t

(* translate a let-binding - local or global *)
and translate_letbinding (cfg:config) (bs:list<t>) (lb:letbinding) : t =
  let debug = debug cfg in
  let us = lb.lbunivs in
  let formals, _ = U.arrow_formals lb.lbtyp in
  let arity = List.length us + List.length formals in
  if arity = 0
  then translate cfg bs lb.lbdef
  else if BU.is_right lb.lbname
  then let _ = debug (fun () -> BU.print2 "Making TopLevelLet for %s with arity %s\n" (P.lbname_to_string lb.lbname) (BU.string_of_int arity)) in
       mk_rt (S.range_of_lbname lb.lbname) <| TopLevelLet(lb, arity, [])
  else translate cfg bs lb.lbdef //local let-binding, cannot be universe polymorphic
  // Note, we only have universe polymorphic top-level pure terms (i.e., fvars bound to pure terms)
  // Thunking them is probably okay, since the common case is really top-level function
  // rather than top-level pure computation


and mkRec i (b:letbinding) (bs:list<letbinding>) (env:list<t>) =
  let (ar, ar_lst) = let_rec_arity b in
  mk_t <| LocalLetRec(i, b, bs, env, [], ar, ar_lst)

(* Creates the environment of mutually recursive function definitions *)
and make_rec_env (all_lbs:list<letbinding>) (all_outer_bs:list<t>) : list<t> =
  let rec_bindings = List.mapi (fun i lb -> mkRec i lb all_lbs all_outer_bs) all_lbs in
  List.rev_append rec_bindings all_outer_bs

and translate_constant (c : sconst) : constant =
    match c with
    | C.Const_unit -> Unit
    | C.Const_bool b -> Bool b
    | C.Const_int (s, None) -> Int (Z.big_int_of_string s)
    | C.Const_string (s, r) -> String (s,r)
    | C.Const_char c -> Char c
    | C.Const_range r -> Range r
    | _ -> SConst c

and readback_comp cfg (c: comp) : S.comp =
  let c' =
    match c with
    | Tot  (typ, u) -> S.Total (readback cfg typ, u)
    | GTot (typ, u) -> S.GTotal (readback cfg typ, u)
    | Comp ctyp     -> S.Comp (readback_comp_typ cfg ctyp)
   in S.mk c' Range.dummyRange

and translate_comp_typ cfg bs (c:S.comp_typ) : comp_typ =
  let { S.comp_univs  = comp_univs
      ; S.effect_name = effect_name
      ; S.result_typ  = result_typ
      ; S.effect_args = effect_args
      ; S.flags       = flags } = c in
  { comp_univs = List.map (translate_univ cfg bs) comp_univs;
    effect_name = effect_name;
    result_typ = translate cfg bs result_typ;
    effect_args = List.map (fun x -> translate cfg bs (fst x), snd x) effect_args;
    flags = List.map (translate_flag cfg bs) flags }

and readback_comp_typ cfg (c:comp_typ) : S.comp_typ =
  { S.comp_univs = c.comp_univs;
    S.effect_name = c.effect_name;
    S.result_typ = readback cfg c.result_typ;
    S.effect_args = List.map (fun x -> readback cfg (fst x), snd x) c.effect_args;
    S.flags = List.map (readback_flag cfg) c.flags }

and translate_residual_comp cfg bs (c:S.residual_comp) : residual_comp =
    let { S.residual_effect  = residual_effect
        ; S.residual_typ     = residual_typ
        ; S.residual_flags   = residual_flags } = c in
    { residual_effect = residual_effect;
      residual_typ =
        (if cfg.core_cfg.steps.for_extraction
         then None
         else BU.map_opt residual_typ (translate cfg bs));
      residual_flags = List.map (translate_flag cfg bs) residual_flags }

and readback_residual_comp cfg (c:residual_comp) : S.residual_comp =
    { S.residual_effect = c.residual_effect;
      S.residual_typ = BU.map_opt c.residual_typ (fun x -> debug cfg (fun () -> BU.print1 "Reading back residualtype %s\n" (t_to_string x)); readback cfg x);
      S.residual_flags = List.map (readback_flag cfg) c.residual_flags }

and translate_flag cfg bs (f : S.cflag) : cflag =
    match f with
    | S.TOTAL -> TOTAL
    | S.MLEFFECT -> MLEFFECT
    | S.RETURN -> RETURN
    | S.PARTIAL_RETURN -> PARTIAL_RETURN
    | S.SOMETRIVIAL -> SOMETRIVIAL
    | S.TRIVIAL_POSTCONDITION -> TRIVIAL_POSTCONDITION
    | S.SHOULD_NOT_INLINE -> SHOULD_NOT_INLINE
    | S.LEMMA -> LEMMA
    | S.CPS -> CPS
    | S.DECREASES (S.Decreases_lex l) -> DECREASES (l |> List.map (translate cfg bs))

and readback_flag cfg (f : cflag) : S.cflag =
    match f with
    | TOTAL -> S.TOTAL
    | MLEFFECT -> S.MLEFFECT
    | RETURN -> S.RETURN
    | PARTIAL_RETURN -> S.PARTIAL_RETURN
    | SOMETRIVIAL -> S.SOMETRIVIAL
    | TRIVIAL_POSTCONDITION -> S.TRIVIAL_POSTCONDITION
    | SHOULD_NOT_INLINE -> S.SHOULD_NOT_INLINE
    | LEMMA -> S.LEMMA
    | CPS -> S.CPS
    | DECREASES l -> S.DECREASES (S.Decreases_lex (l |> List.map (readback cfg)))

and translate_monadic (m, ty) cfg bs e : t =
   let e = U.unascribe e in
   match e.n with
   | Tm_let((false, [lb]), body) -> //elaborate this to M.bind
     begin
     match Env.effect_decl_opt cfg.core_cfg.tcenv (Env.norm_eff_name cfg.core_cfg.tcenv m) with
     | None ->
       failwith (BU.format1 "Effect declaration not found: %s" (Ident.string_of_lid m))

     | Some (ed, q) ->
       let cfg' = reifying_false cfg in
       let body_lam =
           let body_rc = {
                S.residual_effect=m;
                S.residual_flags=[];
                S.residual_typ=Some ty
            } in
           S.mk (Tm_abs([S.mk_binder (BU.left lb.lbname)], body, Some body_rc)) body.pos
       in
       let maybe_range_arg =
           if BU.for_some (U.attr_eq U.dm4f_bind_range_attr) ed.eff_attrs
           then [translate cfg [] (Cfg.embed_simple EMB.e_range lb.lbpos lb.lbpos), None;
                 translate cfg [] (Cfg.embed_simple EMB.e_range body.pos body.pos), None]
           else []
       in
       let t =
       iapp cfg (iapp cfg (translate cfg' [] (U.un_uinst (ed |> U.get_bind_repr |> BU.must |> snd)))
                      [mk_t <| Univ U_unknown, None;  //We are cheating here a bit
                       mk_t <| Univ U_unknown, None])  //to avoid re-computing the universe of lb.lbtyp
                                              //and ty below; but this should be okay since these
                                              //arguments should not actually appear in the resulting
                                              //term
           (
           [(translate cfg' bs lb.lbtyp, None); //translating the type of the bound term
            (translate cfg' bs ty, None)]       //and the body is sub-optimal; it is often unused
           @maybe_range_arg    //some effects take two additional range arguments for debugging
           @[(mk_t Unknown, None) ; //unknown WP of lb.lbdef; same as the universe argument ... should not appear in the result
             (translate cfg bs lb.lbdef, None);
             (mk_t Unknown, None) ;  //unknown WP of body; ditto
             (translate cfg bs body_lam, None)]
           )
      in
      debug cfg (fun () -> BU.print1 "translate_monadic: %s\n" (t_to_string t));
      t

      end

   | Tm_app({n=Tm_constant (FC.Const_reflect _)}, [(e, _)]) ->
     translate (reifying_false cfg) bs e

   | Tm_app (head, args) ->
     debug cfg (fun () -> BU.print2 "translate_monadic app (%s) @ (%s)\n" (P.term_to_string head)
                                                                          (P.args_to_string args));
     let fallback1 () =
         translate cfg bs e
     in
     let fallback2 () =
         translate (reifying_false cfg) bs (S.mk (Tm_meta (e, Meta_monadic (m, ty))) e.pos)
     in
     begin match (U.un_uinst head).n with
     | Tm_fvar fv ->
        let lid = S.lid_of_fv fv in
        let qninfo = Env.lookup_qname cfg.core_cfg.tcenv lid in
        if not (Env.is_action cfg.core_cfg.tcenv lid) then fallback1 () else

        (* GM: I think the action *must* be fully applied at this stage
         * since we were triggered into this function by a Meta_monadic
         * annotation. So we don't check anything. *)

        (* Fallback if it does not have a definition. This happens,
         * but I'm not sure why. *)
        if Option.isNone (Env.lookup_definition_qninfo cfg.core_cfg.delta_level fv.fv_name.v qninfo)
        then fallback2 ()
        else

        (* Turn it info (reify head) args, then translate_fv will kick in on the head *)
        let e = S.mk_Tm_app (U.mk_reify head) args e.pos in
        translate (reifying_false cfg) bs e
     | _ ->
        fallback1 ()
     end

   | Tm_match (sc, asc_opt, branches) ->
     (* Commutation of reify with match. See the comment in the normalizer about it. *)
     let branches = branches |> List.map (fun (pat, wopt, tm) -> pat, wopt, U.mk_reify tm) in
     let tm = S.mk (Tm_match(sc, asc_opt, branches)) e.pos in
     translate (reifying_false cfg) bs tm

   | Tm_meta (t, Meta_monadic _) ->
     translate_monadic (m, ty) cfg bs e

   | Tm_meta (t, Meta_monadic_lift (msrc, mtgt, ty')) ->
     translate_monadic_lift (msrc, mtgt, ty') cfg bs e

   | _ -> failwith (BU.format1 "Unexpected case in translate_monadic: %s" (P.tag_of_term e))

and translate_monadic_lift (msrc, mtgt, ty) cfg bs e : t =
   let e = U.unascribe e in
   if U.is_pure_effect msrc || U.is_div_effect msrc
   then let ed = Env.get_effect_decl cfg.core_cfg.tcenv (Env.norm_eff_name cfg.core_cfg.tcenv mtgt) in
        let ret = match (SS.compress (ed |> U.get_return_repr |> BU.must |> snd)).n with
                  | Tm_uinst (ret, [_]) -> S.mk (Tm_uinst (ret, [U_unknown])) e.pos
                  | _ -> failwith "NYI: Reification of indexed effect (NBE)"
        in
        let cfg' = reifying_false cfg in
        let t =
        iapp cfg' (iapp cfg' (translate cfg' [] ret)
                       [mk_t <| Univ U_unknown, None])
                       [(translate cfg' bs ty, None); //translating the type of the returned term
                        (translate cfg' bs e, None)]  //translating the returned term itself
        in
        debug cfg (fun () -> BU.print1 "translate_monadic_lift(1): %s\n" (t_to_string t));
        t
   else
    match Env.monad_leq cfg.core_cfg.tcenv msrc mtgt with
    | None ->
      failwith (BU.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                            (Ident.string_of_lid msrc)
                            (Ident.string_of_lid mtgt))
    | Some {mlift={mlift_term=None}} ->
      failwith (BU.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                            (Ident.string_of_lid msrc)
                            (Ident.string_of_lid mtgt))

    | Some {mlift={mlift_term=Some lift}} ->
      (* We don't have any reasonable wp to provide so we just pass unknown *)
      (* The wp is only necessary to typecheck, so this should not create an issue. *)
      let lift_lam =
        let x = S.new_bv None S.tun in
        U.abs [S.mk_binder x]
              (lift U_unknown ty (S.bv_to_name x))
              None
      in
      let cfg' = reifying_false cfg in
      let t =
      iapp cfg (translate cfg' [] lift_lam)
               [(translate cfg bs e, None)]
      in
      debug cfg (fun () -> BU.print1 "translate_monadic_lift(2): %s\n" (t_to_string t));
      t

/// `readback` is the other half of the main normalization routine
///
/// Give a translated term `x:t` we read it back as a syntactic term.
///
/// The cases where `x:t` is a fully reduced value of base type are
/// easy: We read each host language constant back as a syntactic
/// constant
///
/// The main work is when we read back terms with binders, e.g.,
/// lambdas, unreduced matches, etc.
///
/// In each of these cases, readback descends under the binder, and
/// recursively normalizes the term (i.e., translates and reads back)
/// in an extended context with a fresh name in scope.
and readback (cfg:config) (x:t) : term =
    let debug = debug cfg in
    let readback_args cfg args =
      map_rev (fun (x, q) -> (readback cfg x, q)) args
    in
    let with_range t = { t with pos = x.nbe_r } in
    let mk t = S.mk t x.nbe_r in
    debug (fun () -> BU.print1 "Readback: %s\n" (t_to_string x));
    match x.nbe_t with
    | Univ u -> failwith "Readback of universes should not occur"

    | Unknown -> S.mk Tm_unknown x.nbe_r

    | Constant Unit -> with_range S.unit_const
    | Constant (Bool true) -> with_range U.exp_true_bool
    | Constant (Bool false) -> with_range U.exp_false_bool
    | Constant (Int i) -> with_range (U.exp_int (Z.string_of_big_int i))
    | Constant (String (s, r)) -> mk (S.Tm_constant (C.Const_string (s, r)))
    | Constant (Char c) -> with_range (U.exp_char c)
    | Constant (Range r) -> Cfg.embed_simple EMB.e_range x.nbe_r r
    | Constant (SConst c) -> mk (S.Tm_constant c)

    | Meta(t, m) ->
      mk (S.Tm_meta (readback cfg t, Thunk.force m))

    | Type_t u ->
      mk (Tm_type u)

    | Lam (f, binders, arity) ->
      let binders, accus_rev, rc =
        match binders with
        | Inl (ctx, binders, rc) ->
          let ctx, binders_rev, accus_rev =
            List.fold_left
              (fun (ctx, binders_rev, accus_rev) b ->
                let x = b.binder_bv in
                let tnorm = readback cfg (translate cfg ctx x.sort) in
                let x = { S.freshen_bv x with sort = tnorm } in
                let ax = mkAccuVar x in
                let ctx = ax :: ctx in
                ctx, ({b with binder_bv=x})::binders_rev, ax::accus_rev)
              (ctx, [], [])
              binders
          in
          let rc =
            match rc with
            | None -> None
            | Some rc ->
              Some (readback_residual_comp cfg (translate_residual_comp cfg ctx rc))
          in
          List.rev binders_rev,
          accus_rev,
          rc
        | Inr args ->
          let binders, accus =
            List.fold_right
              (fun (t, _) (binders, accus) ->
                let x = S.new_bv None (readback cfg t) in
                (S.mk_binder x)::binders, mkAccuVar x :: accus)
              args
              ([],[])
          in
          binders, List.rev accus, None
      in
      let body = readback cfg (f accus_rev) in
      with_range (U.abs binders body rc)

    | Refinement (f, targ) ->
      if cfg.core_cfg.steps.for_extraction
      then readback cfg (fst (targ ()))
      else
        let x =  S.new_bv None (readback cfg (fst (targ ()))) in
        let body = readback cfg (f (mkAccuVar x)) in
        let refinement = U.refine x body in
        with_range (
          if cfg.core_cfg.steps.simplify
          then Common.simplify cfg.core_cfg.debug.wpe refinement
          else refinement
        )

    | Reflect t ->
      let tm = readback cfg t in
      with_range (U.mk_reflect tm)

    | Arrow (Inl f) ->
      with_range (Thunk.force f)

    | Arrow (Inr (args, c)) ->
      let binders =
        List.map
          (fun (t, q) ->
            let t = readback cfg t in
            let x = S.new_bv None t in
            S.mk_binder_with_attrs x q [])
          args
      in
      let c = readback_comp cfg c in
      with_range (U.arrow binders c)

    | Construct (fv, us, args) ->
      let args = map_rev (fun (x, q) -> (readback cfg x, q)) args in
      let fv = S.mk (Tm_fvar fv) (S.range_of_fv fv) in
      let app = U.mk_app (S.mk_Tm_uinst fv (List.rev us)) args in
      with_range (app)

    | FV (fv, us, args) ->
      let args = map_rev (fun (x, q) -> (readback cfg x, q)) args in
      let fv = S.mk (Tm_fvar fv) Range.dummyRange in
      let app = U.mk_app (S.mk_Tm_uinst fv (List.rev us)) args in
      with_range (
        if cfg.core_cfg.steps.simplify
        then Common.simplify cfg.core_cfg.debug.wpe app
        else app
      )

    | Accu (Var bv, []) ->
      with_range (S.bv_to_name bv)

    | Accu (Var bv, args) ->
      let args = readback_args cfg args in
      let app = U.mk_app (S.bv_to_name bv) args in
      with_range (
        if cfg.core_cfg.steps.simplify
        then Common.simplify cfg.core_cfg.debug.wpe app
        else app
      )

    | Accu (Match (scrut, make_returns, make_branches), args) ->
      let args = readback_args cfg args in
      let head =
        let scrut_new = readback cfg scrut in
        let returns_new = make_returns () in
        let branches_new = make_branches () in
        S.mk (Tm_match (scrut_new, returns_new, branches_new)) scrut.nbe_r
      in
      (*  When `cases scrut` returns a Accu(Match ..))
          we need to reconstruct a source match node.

          To do this, we need to decorate that Match node with the
          patterns in each branch.

          e.g., Consider this source node:

              (match x with
               | Inl (a:ta) -> e1eenv
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
      let app = U.mk_app head args in
      with_range (
        if cfg.core_cfg.steps.simplify
        then Common.simplify cfg.core_cfg.debug.wpe app
        else app
      )

    | Accu(UnreducedLet (var, typ, defn, body, lb), args) ->
      let typ = readback cfg (Thunk.force typ) in
      let defn = readback cfg (Thunk.force defn) in
      let body = SS.close [S.mk_binder var] (readback cfg (Thunk.force body)) in
      let lbname = Inl ({ BU.left lb.lbname with sort = typ }) in
      let lb = { lb with lbname = lbname; lbtyp = typ; lbdef = defn } in
      let hd = S.mk (Tm_let((false, [lb]), body)) Range.dummyRange in
      let args = readback_args cfg args in
      with_range (U.mk_app hd args)

    | Accu(UnreducedLetRec (vars_typs_defns, body, lbs), args) ->
      let lbs =
        List.map2
        (fun (v,t,d) lb ->
          let t = readback cfg t in
          let def = readback cfg d in
          let v = {v with sort = t} in
          {lb with lbname = Inl v;
                   lbtyp = t;
                   lbdef = def})
        vars_typs_defns
        lbs
      in
      let body = readback cfg body in
      let lbs, body = SS.close_let_rec lbs body in
      let hd = S.mk (Tm_let((true, lbs), body)) Range.dummyRange in
      let args = readback_args cfg args in
      with_range (U.mk_app hd args)

    | Accu(UVar f, args) ->
      let hd = Thunk.force f in
      let args = readback_args cfg args in
      with_range (U.mk_app hd args)

    | TopLevelLet(lb, arity, args_rev) ->
      let n_univs = List.length lb.lbunivs in
      let n_args = List.length args_rev in
      let args_rev, univs = BU.first_N (n_args - n_univs) args_rev in
      readback cfg (iapp cfg (translate cfg (List.map fst univs) lb.lbdef) (List.rev args_rev))

    | TopLevelRec(lb, _, _, args) ->
      let fv = BU.right lb.lbname in
      let head = S.mk (Tm_fvar fv) Range.dummyRange in
      let args = List.map (fun (t, q) -> readback cfg t, q) args in
      with_range (U.mk_app head args)

    | LocalLetRec(i, _, lbs, bs, args, _ar, _ar_lst) ->
      (* if this point is reached then the local let rec is unreduced
         and we have to read it back as a let rec.

         The idea is to read it back as a `
         ```
           (let rec f0 = e0
            and ... fn = en
            in fi) args
         ```
         where `e0 ... en` are the normalized bodies of
         each arm of the mutually recursive nest, reduced in
         context where all the mutually recursive definitions
         are just fresh symbolic variables
         (so, reducing the e_i will not trigger further
          recursive reductions of th f0..fn)
      *)
      //1. generate fresh symbolic names for the let recs
      let lbnames =
          List.map (fun lb -> S.gen_bv (Ident.string_of_id (BU.left lb.lbname).ppname) None lb.lbtyp) lbs
      in
      //2. these names are in scope for all the bodies
      //   together with whatever other names (bs) that
      //   are in scope at this point
      let let_rec_env =
          List.rev_append (List.map (fun x -> mk_rt (S.range_of_bv x) (Accu (Var x, []))) lbnames) bs
      in
      //3. Reduce each e_i, both its definition (in the rec env)
      //   and its type, which doesn't have the recursive names in scope
      let lbs =
          List.map2
            (fun lb lbname ->
              let lbdef = readback cfg (translate cfg let_rec_env lb.lbdef) in
              let lbtyp = readback cfg (translate cfg bs lb.lbtyp) in
              {lb with
                lbname = Inl lbname;
                lbdef  = lbdef;
                lbtyp  = lbtyp})
            lbs
            lbnames
      in
      //4. Set the body of let rec  ... in ...
      //   to be the name chosen for the ith let rec, the one
      //   referred to in the LocalLetRec
      let body = S.bv_to_name (List.nth lbnames i) in
      //5. close everything to switch back to locally nameless
      let lbs, body = FStar.Syntax.Subst.close_let_rec lbs body in
      //6. Build the head term
      let head = S.mk (Tm_let ((true, lbs), body)) Range.dummyRange in
      //7. Readback the arguments and apply it to the head
      let args = List.map (fun (x, q) -> readback cfg x, q) args in
      with_range (U.mk_app head args)

    | Quote (qt, qi) ->
      mk (Tm_quoted (qt, qi))

    // Need this case for "cheat" embeddings
    | Lazy (Inl li, _) ->
      mk (Tm_lazy li)

    | Lazy (_, thunk) ->
      readback cfg (Thunk.force thunk)

type step =
  | Primops
  | UnfoldUntil of delta_depth
  | UnfoldOnly  of list<FStar.Ident.lid>
  | UnfoldAttr  of list<FStar.Ident.lid>
  | UnfoldTac
  | Reify

let step_as_normalizer_step = function
  | Primops -> Env.Primops
  | UnfoldUntil d -> Env.UnfoldUntil d
  | UnfoldOnly lids -> Env.UnfoldOnly lids
  | UnfoldAttr lids -> Env.UnfoldAttr lids
  | UnfoldTac -> Env.UnfoldTac
  | Reify -> Env.Reify

let reduce_application cfg t args =
  iapp (new_config cfg) t args

let normalize psteps (steps:list<Env.step>)
                (env : Env.env) (e:term) : term =
  let cfg = Cfg.config' psteps steps env in
  //debug_sigmap env.sigtab;
  let cfg = {cfg with steps={cfg.steps with reify_=true}} in
  if Env.debug env (Options.Other "NBETop")
  ||  Env.debug env (Options.Other "NBE")
  then BU.print1 "Calling NBE with (%s) {\n" (P.term_to_string e);
  let cfg = new_config cfg in
  let r = readback cfg (translate cfg [] e) in
  if Env.debug env (Options.Other "NBETop")
  ||  Env.debug env (Options.Other "NBE")
  then BU.print1 "}\nNBE returned (%s)\n" (P.term_to_string r);
  r

(* ONLY FOR UNIT TESTS! *)
let normalize_for_unit_test (steps:list<Env.step>) (env : Env.env) (e:term) : term =
  let cfg = Cfg.config steps env in
  //debug_sigmap env.sigtab;
  let cfg = {cfg with steps={cfg.steps with reify_=true}} in
  let cfg = new_config cfg in
  debug cfg (fun () -> BU.print1 "Calling NBE with (%s) {\n" (P.term_to_string e));
  let r = readback cfg (translate cfg [] e) in
  debug cfg (fun () -> BU.print1 "}\nNBE returned (%s)\n" (P.term_to_string r));
  r
