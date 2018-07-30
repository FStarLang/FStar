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

// NBE debuging

let debug cfg f =
  if Env.debug (Cfg.cfg_env cfg) (Options.Other "NBE")
  then f ()

let debug_term (t : term) =
  BU.print1 "%s\n" (P.term_to_string t)

let debug_sigmap (m : BU.smap<sigelt>) =
  BU.smap_fold m (fun k v u -> BU.print2 "%s -> %%s\n" k (P.sigelt_to_string_short v)) ()

let rec unlazy t =
    match t with
    | Lazy (_, t) -> unlazy (FStar.Common.force_thunk t)
    | t -> t

let pickBranch cfg (scrut : t) (branches : list<branch>) : option<(term * list<t>)> =
  let rec pickBranch_aux (scrut : t) (branches : list<branch>) (branches0 : list<branch>) : option<(term * list<t>)> =
    //NS: adapted from FStar.TypeChecker.Normalize: rebuild_match
    let rec matches_pat (scrutinee0:t) (p:pat)
        : BU.either<list<t>, bool> =
        (* Inl ts: p matches t and ts are bindings for the branch *)
        (* Inr false: p definitely does not match t *)
        (* Inr true: p may match t, but p is an open term and we cannot decide for sure *)
        let scrutinee = unlazy scrutinee0 in
        debug cfg (fun () -> BU.print2 "matches_pat (%s, %s)\n" (t_to_string scrutinee) (P.pat_to_string p));
        let r = match p.v with
        | Pat_var bv
        | Pat_wild bv ->
            // important to use the non-unfolded variant, some embeddings
            // have no decent unfolding (i.e. they cheat)
            BU.Inl [scrutinee0]

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
        let res_to_string = function
        | BU.Inr b -> "Inr " ^ BU.string_of_bool b
        | BU.Inl bs -> "Inl " ^ BU.string_of_int (List.length bs)
        in
        debug cfg (fun () -> BU.print3 "matches_pat (%s, %s) = %s\n" (t_to_string scrutinee) (P.pat_to_string p) (res_to_string r));
        r
    in
    match branches with
    | [] -> failwith "Branch not found"
    // TODO: Consider the when clause!
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

(* Tests is the application is full and if none of the recursive arguments is symbolic *)
let test_args ts ar_list : (bool * args * args) = (* can unfold x full arg list x residual args *)
  let rec aux ts ar_list acc res =
    match ts, ar_list with
    | _, [] -> true, List.rev acc, ts
    | [], _ :: _ -> (false, List.rev acc, [])  (* It's partial! *)
    | t :: ts, b :: bs -> aux ts bs (t :: acc) (res && implies b (not (isAccu (fst t))))
  in
  aux ts ar_list [] true

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
  | t -> failwith ("Not a universe: " ^ t_to_string t)

let is_constr_fv (fvar : fv) : bool =
  fvar.fv_qual = Some Data_ctor

let is_constr (q : qninfo) : bool =
  match q with
  | Some (BU.Inr ({ sigel = Sig_datacon (_, _, _, _, _, _) }, _), _) -> true
  | _ -> false

let translate_univ (bs:list<t>) (u:universe) : universe =
  let rec aux u =
    let u = SS.compress_univ u in
      match u with
      | U_bvar i ->
        if i < List.length bs
        then
          let u' = List.nth bs i in //it has to be a Univ term at position i
          (un_univ u')
        else failwith "Universe index out of bounds"

      | U_succ u -> U_succ (aux u)

      | U_max us -> U_max (List.map aux us)

      | U_unknown | U_name _ | U_unif _ | U_zero -> u
    in
    aux u

let find_let (lbs : list<letbinding>) (fvar : fv) =
  BU.find_map lbs (fun lb -> match lb.lbname with
                   | BU.Inl _ -> failwith "find_let : impossible"
                   | BU.Inr name ->
                     if fv_eq name fvar
                     then Some lb
                     else None)

(* uncurried application *)
let rec iapp (cfg : Cfg.cfg) (f:t) (args:args) : t =
  match f with
  | Lam (f, targs, n, res) ->
    let m = List.length args in
    if m < n then
      // partial application
      let (_, targs') = List.splitAt m targs in
      let targs' = List.map (fun targ -> (fun (l (* has length n - m *)) -> targ (List.rev (map_append fst args l)))) targs' in
      Lam ((fun l -> f (map_append fst args l)), targs', n - m, res)
    else if m = n then
      // full application
      f (List.map fst args)
    else
      // extra arguments
      let (args, args') = List.splitAt n args in
      iapp cfg (f (List.map fst args)) args'
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
  | Rec(lb, lbs, bs, acc, ar, ar_lst, tr_lb) ->
    (* ZP : this can be made more efficient by storing the arity and avoiding test args for
            partial apps *)
    let no_args = List.length args in
    if (ar > no_args) then
      (* Application is still partial -- accumulate args *)
      Rec (lb, lbs, bs, acc @ args, ar - no_args, ar_lst, tr_lb)
    else if (ar = 0) then
      (* Cannot unfold -- accumulate args *)
      Rec (lb, lbs, bs, acc @ args, ar, ar_lst, tr_lb)
    else (* Full application, test for unfolding. This should happen only once for each application *)
      begin
        let full_args = acc @ args in (* Not in reverse order *)

        let (can_unfold, args, res) = test_args full_args ar_lst in

        if not cfg.steps.zeta then
          begin
            debug cfg (fun () -> BU.print1 "Zeta is not set; will not unfold %s\n" (P.lbname_to_string lb.lbname));
            Rec (lb, lbs, bs, full_args, 0, ar_lst, tr_lb)
          end
        else if can_unfold then (* compute *)
          begin
            debug cfg (fun () -> BU.print1 "Beta reducing recursive function %s\n" (P.lbname_to_string lb.lbname));
             match res with
             | [] -> (* no residual args *)
               iapp cfg (tr_lb (make_rec_env tr_lb lbs bs) lb) args
             | _ :: _ ->
               let t = iapp cfg (tr_lb (make_rec_env tr_lb lbs bs) lb) args in
               iapp cfg t res
          end
        else (* cannot unfold -- accumulate args *)
          Rec (lb, lbs, bs, full_args, 0, ar_lst, tr_lb)
      end

  | Quote _ | Reflect _
  | Lazy _ | Constant _ | Univ _ | Type_t _ | Unknown | Refinement _ | Arrow _ ->
    failwith ("NBE ill-typed application: " ^ t_to_string f)

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
       begin match Cfg.find_prim_step cfg fvar with
       | Some prim_step when prim_step.strong_reduction_ok (* TODO : || not cfg.strong *) ->
         let arity = prim_step.arity + prim_step.univ_arity in
         debug (fun () -> BU.print1 "Found a primop %s\n" (P.fv_to_string fvar));
         Lam ((fun args -> let args' = (List.map NBETerm.as_arg args) in
              let callbacks = {
                iapp = iapp cfg;
                translate = translate cfg bs;
              }
              in
              match prim_step.interpretation_nbe callbacks args' with
              | Some x -> debug (fun () -> BU.print2 "Primitive operator %s returned %s\n" (P.fv_to_string fvar) (t_to_string x));
                         x
              | None -> debug (fun () -> BU.print1 "Primitive operator %s failed\n" (P.fv_to_string fvar));
                       iapp cfg (mkFV fvar [] []) args'),
              (let f (_:int) _ : t * S.aqual = (Constant Unit, None) in FStar.Common.tabulate arity f),
              arity, None)

       | Some _ -> debug (fun () -> BU.print1 "(2) Decided to not unfold %s\n" (P.fv_to_string fvar)); mkFV fvar [] []
       | _      -> debug (fun () -> BU.print1 "(3) Decided to not unfold %s\n" (P.fv_to_string fvar)); mkFV fvar [] []
       end


     | N.Should_unfold_reify
     | N.Should_unfold_yes ->
       begin match qninfo with
       | Some (BU.Inr ({ sigel = Sig_let ((is_rec, lbs), names) }, _us_opt), _rng) ->
         let lbm = find_let lbs fvar in
         begin match lbm with
         | Some lb ->
           if is_rec then
             mkRec cfg lb [] [] (* ZP: both the environment and the lists of mutually defined functions are empty
                               since they are already present in the global environment *)
           else
             begin
               debug (fun() -> BU.print "Translate fv: it's a Sig_let\n" []);
               debug (fun () -> BU.print2 "Type of lbdef: %s - %s\n" (P.tag_of_term (SS.compress lb.lbtyp)) (P.term_to_string (SS.compress lb.lbtyp)));
               debug (fun () -> BU.print2 "Body of lbdef: %s - %s\n" (P.tag_of_term (SS.compress lb.lbdef)) (P.term_to_string (SS.compress lb.lbdef)));
               translate_letbinding cfg bs lb
             end
         | None -> failwith "Could not find let binding"
         end
       | _ -> mkFV fvar [] []
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
          List.map (fun _ -> (fun _ts -> id <| (Constant Unit, None))) us,
          // Zoe: Bogus type! The idea is that we will never readback these lambdas
          List.length us, None)
  // Note, we only have universe polymorphic top-level pure terms (i.e., fvars bound to pure terms)
  // Thunking them is probably okay, since the common case is really top-level function
  // rather than top-level pure computation


and mkRec' callback (b:letbinding) (bs:list<letbinding>) (env:list<t>) =
  let (ar, maybe_lst) = U.let_rec_arity b in
  let (ar, ar_lst) =
    match maybe_lst with
    | None ->
      //BU.print "No rec list\n" [];
      ar, FStar.Common.tabulate ar (fun _ -> true) (* treat all arguments as recursive *)
    | Some lst ->
      //BU.print "Trimming rec list\n" [];
      let l = trim lst in List.length l, l
  in
  // BU.print2 "Creating rec definition with arrity %s : %s\n"
  //   (BU.string_of_int ar) (P.list_to_string BU.string_of_bool ar_lst);
  // BU.print1 "Type of rec def: %s\n" (P.term_to_string b.lbtyp);
  Rec(b, bs, env, [], ar, ar_lst, callback)

and mkRec cfg b bs env = mkRec' (translate_letbinding cfg) b bs env

(* Creates the environment of mutually recursive function definitions *)
and make_rec_env callback (lbs:list<letbinding>) (bs:list<t>) : list<t> =
  let rec aux (lbs:list<letbinding>) (lbs0:list<letbinding>) (bs:list<t>) (bs0:list<t>) : list<t> =
  match lbs with
  | [] -> bs
  | lb::lbs' -> aux lbs' lbs0 ((mkRec' callback lb lbs0 bs0) :: bs) bs0
  in
  aux lbs lbs bs bs

and translate_constant (c : sconst) : constant =
    match c with
    | C.Const_unit -> Unit
    | C.Const_bool b -> Bool b
    | C.Const_int (s, None) -> Int (Z.big_int_of_string s)
    | C.Const_string (s, r) -> String (s,r)
    | C.Const_char c -> Char c
    | C.Const_range r -> Range r
    | _ -> failwith ("Tm_constant " ^ (P.const_to_string c) ^ ": Not yet implemented")

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
      if db.index < List.length bs
      then List.nth bs db.index
      else failwith "de Bruijn index out of bounds"

    | Tm_uinst(t, us) ->
      debug (fun () -> BU.print2 "Uinst term : %s\nUnivs : %s\n" (P.term_to_string t)
                                                              (List.map P.univ_to_string us |> String.concat ", "));
      iapp cfg (translate cfg bs t) (List.map (fun x -> as_arg (Univ (translate_univ bs x))) us)

    | Tm_type u ->
      Type_t (translate_univ bs u)

    | Tm_arrow (xs, c) ->
      Arrow ((fun ys -> translate_comp cfg (List.rev_append ys bs) c),
              List.fold_right (fun x formals ->
                                   let next_formal prefix_of_xs_rev = (* will only be fully applied during readback *)
                                     translate cfg (List.append prefix_of_xs_rev bs) (fst x).sort,
                                     snd x
                                   in
                                   next_formal :: formals) xs [])

    | Tm_refine (bv, tm) ->
      Refinement ((fun (y:t) -> translate cfg (y::bs) tm), (fun () -> as_arg (translate cfg bs bv.sort))) // XXX: Bogus type?

    | Tm_ascribed (t, _, _) -> translate cfg bs t

    | Tm_uvar (uvar, t) -> debug_term e; failwith "Tm_uvar: Not yet implemented"

    | Tm_name x ->
      mkAccuVar x

    | Tm_abs ([], _, _) -> failwith "Impossible: abstraction with no binders"

    | Tm_abs (xs, body, resc) ->
      Lam ((fun ys -> translate cfg (List.rev_append ys bs) body),
           List.fold_right (fun x formals ->
                             let next_formal prefix_of_xs_rev =
                                 translate cfg (List.append prefix_of_xs_rev bs) (fst x).sort,
                                 snd x
                             in
                             next_formal :: formals)
                          xs
                          [],
           List.length xs, BU.map_opt resc (fun c -> (fun () -> translate_residual_comp cfg bs c)))

    | Tm_fvar fvar ->
      translate_fv cfg bs fvar

    | Tm_app({n=Tm_constant FC.Const_reify},   arg::more::args)
    | Tm_app({n=Tm_constant (FC.Const_reflect _)}, arg::more::args) ->
      let head, _ = U.head_and_args e in
      let head = S.mk_Tm_app head [arg] None e.pos in
      translate cfg bs (S.mk_Tm_app head (more::args) None e.pos)

    | Tm_app({n=Tm_constant (FC.Const_reflect _)}, [arg]) when cfg.reifying ->
      let cfg = {cfg with reifying=false} in
      translate cfg bs (fst arg)

    | Tm_app({n=Tm_constant (FC.Const_reflect _)}, [arg]) ->
      Reflect (translate cfg bs (fst arg))

    | Tm_app({n=Tm_constant FC.Const_reify}, [arg])
        when cfg.steps.reify_ ->
      assert (not cfg.reifying);
      let cfg = {cfg with reifying=true} in
      translate cfg bs (fst arg)

    | Tm_app(head, args) ->
      debug (fun () -> BU.print2 "Application: %s @ %s\n" (P.term_to_string head) (P.args_to_string args));
      iapp cfg (translate cfg bs head) (List.map (fun x -> (translate cfg bs (fst x), snd x)) args) // Zoe : TODO avoid translation pass for args

    | Tm_match(scrut, branches) ->
      (* Thunked computation that reconstructs the patterns *)
      (* Zoe TODO : maybe rewrite in CPS? *)
      let make_branches (readback:t -> term) : list<branch> =
        let cfg = {cfg with steps={cfg.steps with zeta=false}} in // disable zeta flag
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
              (bs,
               Pat_dot_term (x, readback (translate cfg bs tm)))
          in
          (bs, {p with v = p_new}) (* keep the info and change the pattern *)
        in
        List.map (fun (pat, when_clause, e) ->
                  let (bs', pat') = process_pattern bs pat in
                  (* TODO : handle when clause *)
                  U.branch (pat', when_clause, readback (translate cfg bs' e))) branches
      in

      let rec case (scrut : t) : t =
        debug (fun () -> BU.print2 "Match case: (%s) -- (%s)\n" (P.term_to_string (readback cfg scrut))
                                                        (t_to_string scrut));
        let scrut = unlazy scrut in
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
          debug (fun () -> BU.print1 "Match constant : %s\n" (t_to_string scrut));
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
      translate cfg (make_rec_env (translate_letbinding cfg) lbs bs) body

    | Tm_meta (e, _) ->
      //TODO: we need to put the "meta" back when reading back
      translate cfg bs e

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
        Quote (qt, qi)
      | Quote_static  ->
        let qi = S.on_antiquoted close qi in
        Quote (qt, qi)
      end

    | Tm_lazy li ->
      Lazy (BU.Inl li, FStar.Common.mk_thunk (fun () -> translate cfg bs (U.unfold_lazy li)))

and translate_comp cfg bs (c:S.comp) : comp =
  match c.n with
  | S.Total  (typ, u) -> Tot (translate cfg bs typ, fmap_opt (translate_univ bs) u)
  | S.GTotal (typ, u) -> GTot (translate cfg bs typ, fmap_opt (translate_univ bs) u)
  | S.Comp   ctyp      -> Comp (translate_comp_typ cfg bs ctyp)

and readback_comp cfg (c: comp) : S.comp =
  let c' =
    match c with
    | Tot  (typ, u) -> S.Total (readback cfg typ, u)
    | GTot (typ, u) -> S.GTotal (readback cfg typ, u)
    | Comp ctyp     -> S.Comp (readback_comp_typ cfg ctyp)
   in S.mk c' None Range.dummyRange

and translate_comp_typ cfg bs (c:S.comp_typ) : comp_typ =
  let { S.comp_univs  = comp_univs
      ; S.effect_name = effect_name
      ; S.result_typ  = result_typ
      ; S.effect_args = effect_args
      ; S.flags       = flags } = c in
  { comp_univs = List.map (translate_univ bs) comp_univs;
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
      residual_typ = BU.map_opt residual_typ (translate cfg bs);
      residual_flags = List.map (translate_flag cfg bs) residual_flags }

and readback_residual_comp cfg (c:residual_comp) : S.residual_comp =
    { S.residual_effect = c.residual_effect;
      S.residual_typ = BU.map_opt c.residual_typ (readback cfg);
      S.residual_flags = List.map (readback_flag cfg) c.residual_flags }

and translate_flag cfg bs (f : S.cflags) : cflags =
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
    | S.DECREASES tm -> DECREASES (translate cfg bs tm)

and readback_flag cfg (f : cflags) : S.cflags =
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
    | DECREASES t -> S.DECREASES (readback cfg t)

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
                S.residual_effect=m;
                S.residual_flags=[];
                S.residual_typ=Some ty
            } in
           S.mk (Tm_abs([(BU.left lb.lbname, None)], body, Some body_rc)) None body.pos
       in
       let maybe_range_arg =
           if BU.for_some (U.attr_eq U.dm4f_bind_range_attr) ed.eff_attrs
           then [translate cfg [] (Cfg.embed_simple EMB.e_range lb.lbpos lb.lbpos), None;
                 translate cfg [] (Cfg.embed_simple EMB.e_range body.pos body.pos), None]
           else []
       in
       let t =
       iapp cfg (iapp cfg (translate cfg' [] (U.un_uinst (snd ed.bind_repr)))
                      [Univ U_unknown, None;  //We are cheating here a bit
                      Univ U_unknown, None])  //to avoid re-computing the universe of lb.lbtyp
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
      in
      debug cfg (fun () -> BU.print1 "translate_monadic: %s\n" (t_to_string t));
      t

      end

   | Tm_app({n=Tm_constant (FC.Const_reflect _)}, [(e, _)]) ->
     translate ({cfg with reifying=false}) bs e

   | Tm_app (head, args) ->
     debug cfg (fun () -> BU.print2 "translate_monadic app (%s) @ (%s)\n" (P.term_to_string head)
                                                                          (P.args_to_string args));
     let fallback1 () =
         translate cfg bs e
     in
     let fallback2 () =
         translate ({cfg with reifying=false}) bs (S.mk (Tm_meta (e, Meta_monadic (m, ty))) None e.pos)
     in
     begin match (U.un_uinst head).n with
     | Tm_fvar fv ->
        let lid = S.lid_of_fv fv in
        let qninfo = Env.lookup_qname cfg.tcenv lid in
        if not (Env.is_action cfg.tcenv lid) then fallback1 () else

        (* GM: I think the action *must* be fully applied at this stage
         * since we were triggered into this function by a Meta_monadic
         * annotation. So we don't check anything. *)

        (* Fallback if it does not have a definition. This happens,
         * but I'm not sure why. *)
        if Option.isNone (Env.lookup_definition_qninfo cfg.delta_level fv.fv_name.v qninfo)
        then fallback2 ()
        else

        (* Turn it info (reify head) args, then translate_fv will kick in on the head *)
        let e = S.mk_Tm_app (U.mk_reify head) args None e.pos in
        translate ({cfg with reifying=false}) bs e
     | _ ->
        fallback1 ()
     end

   | Tm_match (sc, branches) ->
     (* Commutation of reify with match. See the comment in the normalizer about it. *)
     let branches = branches |> List.map (fun (pat, wopt, tm) -> pat, wopt, U.mk_reify tm) in
     let tm = S.mk (Tm_match(sc, branches)) None e.pos in
     translate ({ cfg with reifying = false }) bs tm

   | Tm_meta (t, Meta_monadic _) ->
     translate_monadic (m, ty) cfg bs e

   | Tm_meta (t, Meta_monadic_lift (msrc, mtgt, ty')) ->
     translate_monadic_lift (msrc, mtgt, ty') cfg bs e

   | _ -> failwith (BU.format1 "Unexpected case in translate_monadic: %s" (P.tag_of_term e))

and translate_monadic_lift (msrc, mtgt, ty) cfg bs e : t =
   let e = U.unascribe e in
   if U.is_pure_effect msrc || U.is_div_effect msrc
   then let ed = Env.get_effect_decl cfg.tcenv (Env.norm_eff_name cfg.tcenv mtgt) in
        let ret = match (SS.compress (snd ed.return_repr)).n with
                  | Tm_uinst (ret, [_]) -> S.mk (Tm_uinst (ret, [U_unknown])) None e.pos
                  | _ -> failwith "NYI: Reification of indexed effect (NBE)"
        in
        let cfg' = {cfg with reifying=false} in
        let t =
        iapp cfg' (iapp cfg' (translate cfg' [] ret)
                       [Univ U_unknown, None])
                       [(translate cfg' bs ty, None); //translating the type of the returned term
                        (translate cfg' bs e, None)]  //translating the returned term itself
        in
        debug cfg (fun () -> BU.print1 "translate_monadic_lift(1): %s\n" (t_to_string t));
        t
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
      (* We don't have any reasonable wp to provide so we just pass unknown *)
      (* The wp is only necessary to typecheck, so this should not create an issue. *)
      let lift_lam =
        let x = S.new_bv None S.tun in
        U.abs [(x, None)]
              (lift U_unknown ty S.tun (S.bv_to_name x))
              None
      in
      let cfg' = {cfg with reifying=false} in
      let t =
      iapp cfg (translate cfg' [] lift_lam)
               [(translate cfg bs e, None)]
      in
      debug cfg (fun () -> BU.print1 "translate_monadic_lift(2): %s\n" (t_to_string t));
      t

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
    | Constant (Range r) -> Cfg.embed_simple EMB.e_range r Range.dummyRange

    | Type_t u ->
      S.mk (Tm_type u) None Range.dummyRange

    | Lam (f, targs, arity, resc) ->
      let (args_rev, accus_rev) =
          List.fold_left (fun (args_rev, accus_rev) tf ->
                            let (xt, q) = tf accus_rev in
                            let x = S.new_bv None (readback cfg xt) in
                            ((x, q) :: args_rev,
                            (mkAccuVar x) :: accus_rev))
                         ([], [])
                         targs
      in
      let body = readback cfg (f (List.rev accus_rev)) in
      // GM: Isn't this closing the binders over the body/lcomp? Why?
      U.abs (List.rev args_rev) body (BU.map_opt resc (fun thunk -> readback_residual_comp cfg (thunk ())))

    | Refinement (f, targ) ->
      let x =  S.new_bv None (readback cfg (fst (targ ()))) in
      let body = readback cfg (f (mkAccuVar x)) in
      U.refine x body

    | Reflect t ->
      let tm = readback cfg t in
      U.mk_reflect tm

    | Arrow (f, targs) ->
      let (args_rev, accus_rev) =
          List.fold_left (fun (args_rev, accus_rev) tf ->
                             let (xt, q) = tf accus_rev in
                             let x = S.new_bv None (readback cfg xt) in
                             ((x, q) :: args_rev,
                             (mkAccuVar x) :: accus_rev))
                         ([], [])
                         targs in

      let cmp = readback_comp cfg (f (List.rev accus_rev)) in
      U.arrow (List.rev args_rev) cmp

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
      begin match us with
      | _ :: _ -> apply (S.mk_Tm_uinst (S.mk (Tm_fvar fv) None Range.dummyRange) (List.rev us))
      | [] -> apply (S.mk (Tm_fvar fv) None Range.dummyRange)
      end
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

    | Rec(lb, lbs, bs, args, _ar, _ar_lst, _cfg) -> (* if this point is reached then we cannot unfold Rec *)
      let head =
       (* Zoe: I want the head to be [let rec f = lb in f]. Is this the right way to construct it? *)
        match lb.lbname with
        | BU.Inl bv ->
          failwith "Reading back of local recursive definitions is not supported yet."
        | BU.Inr fv -> S.mk (Tm_fvar fv) None Range.dummyRange
      in

      let args = map_rev (fun (x, q) -> (readback cfg x, q)) args in
      (match args with
          | [] -> head
          | _ -> U.mk_app head args)

    | Quote (qt, qi) ->
        S.mk (Tm_quoted (qt, qi)) None Range.dummyRange


    // Need this case for "cheat" embeddings
    | Lazy (BU.Inl li, _) ->
        S.mk (Tm_lazy li) None Range.dummyRange

    | Lazy (_, thunk) ->
        readback cfg (FStar.Common.force_thunk thunk)

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

let normalize psteps (steps:list<Env.step>)
                (env : Env.env) (e:term) : term =
  let cfg = Cfg.config' psteps steps env in
  //debug_sigmap env.sigtab;
  let cfg = {cfg with steps={cfg.steps with reify_=true}} in
  debug cfg (fun () -> BU.print1 "Calling NBE with (%s) {\n" (P.term_to_string e));
  let r = readback cfg (translate cfg [] e) in
  debug cfg (fun () -> BU.print1 "}\nNBE returned (%s)\n" (P.term_to_string r));
  r

(* ONLY FOR UNIT TESTS! *)
let normalize_for_unit_test (steps:list<Env.step>) (env : Env.env) (e:term) : term =
  let cfg = Cfg.config steps env in
  //debug_sigmap env.sigtab;
  let cfg = {cfg with steps={cfg.steps with reify_=true}} in
  debug cfg (fun () -> BU.print1 "Calling NBE with (%s) {\n" (P.term_to_string e));
  let r = readback cfg (translate cfg [] e) in
  debug cfg (fun () -> BU.print1 "}\nNBE returned (%s)\n" (P.term_to_string r));
  r
