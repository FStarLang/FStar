module FStar.TypeChecker.Core
open FStar.Compiler
open FStar.Compiler.Util
open FStar.Compiler.Effect
open FStar.Syntax.Syntax
module Env = FStar.TypeChecker.Env
module SS = FStar.Syntax.Subst
module S = FStar.Syntax.Syntax
module R = FStar.Compiler.Range
module U = FStar.Syntax.Util
module N = FStar.TypeChecker.Normalize
module PC = FStar.Parser.Const
module I = FStar.Ident
module P = FStar.Syntax.Print
module BU = FStar.Compiler.Util
module TcUtil = FStar.TypeChecker.Util

type env = {
   tcenv : Env.env;
   allow_universe_instantiation : bool
}

let push_binders g bs = { g with tcenv = Env.push_binders g.tcenv bs }

let precondition = option typ

let success a = a & precondition

type context = {
  no_guard : bool;
  error_context: list (string & option term)
}

let print_context (ctx:context)
  : string =
  let rec aux (depth:string) (ctx:_) =
    match ctx with
    | [] -> ""
    | (msg, topt)::tl ->
      let hd =
        BU.format3
          "%s %s (%s)\n"
          depth
          msg
          (match topt with
          | None -> ""
          | Some t -> P.term_to_string t)
      in
      let tl = aux (depth ^ ">") tl in
      hd ^ tl
  in
  aux "" (List.rev ctx.error_context)

let error = context & string

let print_error (err:error) =
  let ctx, msg = err in
  BU.format2 "%s%s" (print_context ctx) msg

let print_error_short (err:error) = snd err

let result a = context -> either (success a) error

type effect_label =
  | E_TOTAL
  | E_GHOST

type hash_entry = {
   he_term:term;
   he_gamma:list binding;
   he_res:success (effect_label & typ);
}

type tc_table = FStar.Hash.hashtable term hash_entry
let table : tc_table = FStar.Hash.create FStar.Syntax.Hash.equal_term
type cache_stats_t = { hits : int; misses : int }
let cache_stats = Util.mk_ref { hits = 0; misses = 0 }
let record_cache_hit () =
   let cs = !cache_stats in
    cache_stats := { cs with hits = cs.hits + 1 }
let record_cache_miss () =
   let cs = !cache_stats in
    cache_stats := { cs with misses = cs.misses + 1 }
let reset_cache_stats () =     
    cache_stats := { hits = 0; misses = 0 }
let report_cache_stats () = !cache_stats
let clear_memo_table () = FStar.Hash.clear table
let insert (g:env) (e:term) (res:success (effect_label & typ)) =
    let entry = {
       he_term = e;
       he_gamma = g.tcenv.gamma;
       he_res = res
    }
    in
    FStar.Hash.insert (e, FStar.Syntax.Hash.hash_term) entry table

inline_for_extraction
let return (#a:Type) (x:a) : result a = fun _ -> Inl (x, None)

let and_pre (p1 p2:precondition) =
  match p1, p2 with
  | None, None -> None
  | Some p, None
    | None, Some p -> Some p
  | Some p1, Some p2 -> Some (U.mk_conj p1 p2)

inline_for_extraction
let (let!) (#a:Type) (#b:Type) (x:result a) (y:a -> result b)
  : result b
  = fun ctx0 ->
      match x ctx0 with
      | Inl (x, g1) ->
        (match y x ctx0 with
         | Inl (y, g2) -> Inl (y, and_pre g1 g2)
         | err -> err)
      | Inr err -> Inr err

inline_for_extraction
let (and!) (#a:Type) (#b:Type) (x:result a) (y:result b)
  : result (a & b)
  = let! v = x in
    let! u = y in
    return (v, u)

let (let?) (#a:Type) (#b:Type) (x:option a) (f: a -> option b)
  : option b
  = match x with
    | None -> None
    | Some x -> f x

let fail #a msg : result a = fun ctx -> Inr (ctx, msg)

let dump_context
  : result unit
  = fun ctx ->
      BU.print_string (print_context ctx);
      return () ctx

inline_for_extraction
let handle_with (#a:Type) (x:result a) (h: unit -> result a)
  : result a
  = fun ctx ->
      match x ctx with
      | Inr _ -> h () ctx
      | res -> res

inline_for_extraction
let with_context (#a:Type) (msg:string) (t:option term) (x:unit -> result a)
  : result a
  = fun ctx ->
     let ctx' = { ctx with error_context=((msg,t)::ctx.error_context) } in
     // (if Options.debug_any()
     //  then BU.print_string (print_context ctx'));
     x () ctx'

let mk_type (u:universe) = S.mk (Tm_type u) R.dummyRange

let is_type (g:env) (t:term)
  : result universe
  = let aux t =
        match (SS.compress t).n with
        | Tm_type u ->
          return u

        | _ ->
          fail (BU.format1 "Expected a type; got %s" (P.term_to_string t))
    in
    with_context "is_type" (Some t) (fun _ ->
      handle_with
        (aux t)
        (fun _ -> aux (U.unrefine (N.unfold_whnf g.tcenv t))))

let rec is_arrow (g:env) (t:term)
  : result (binder & effect_label & typ)
  = let rec aux t =
        match (SS.compress t).n with
        | Tm_arrow ([x], c) ->
          if U.is_tot_or_gtot_comp c
          then
            let [x], c = SS.open_comp [x] c in
            let eff =
              if U.is_total_comp c
              then E_TOTAL
              else E_GHOST
            in
            return (x, eff, U.comp_result c)
          else (
            let e_tag =
              let Comp ct = c.n in
              if Ident.lid_equals ct.effect_name PC.effect_Pure_lid
              then Some E_TOTAL
              else if Ident.lid_equals ct.effect_name PC.effect_Ghost_lid
              then Some E_GHOST
              else None
            in
            (* Turn   x:t -> Pure/Ghost t' pre post
               into   x:t{pre} -> Tot/GTot (y:t'{post})

               This is ok for pre.
               But, it loses precision for post.
               In effect form, the post is in scope for the entire continuation.
               Whereas the refinement on the result is not.
             *)
            match e_tag with
            | None -> fail (BU.format1 "Expected total or gtot arrow, got %s" (Ident.string_of_lid (U.comp_effect_name c)))
            | Some e_tag ->
              let [x], c = U.arrow_formals_comp t in
              let (pre, _)::(post, _)::_ = U.comp_effect_args c in
              let arg_typ = U.refine x.binder_bv pre in
              let res_typ =
                let r = S.new_bv None (U.comp_result c) in
                let post = S.mk_Tm_app post [(S.bv_to_name r, None)] post.pos in
                U.refine r post
              in
              let xbv = { x.binder_bv with sort = arg_typ } in
              let x = { x with binder_bv = xbv } in
              return (x, e_tag, res_typ)
          )

        | Tm_arrow (x::xs, c) ->
          let t = S.mk (Tm_arrow(xs, c)) t.pos in
          let [x], t = SS.open_term [x] t in
          return (x, E_TOTAL, t)

        | Tm_refine(x, _) ->
          is_arrow g x.sort

        | Tm_meta(t, _)
        | Tm_ascribed(t, _, _) ->
          aux t

        | _ ->
          fail (BU.format2 "Expected an arrow, got (%s) %s" (P.tag_of_term t) (P.term_to_string t))
    in
    with_context "is_arrow" None (fun _ ->
      handle_with
        (aux t)
        (fun _ -> aux (N.unfold_whnf g.tcenv t)))

let check_arg_qual (a:aqual) (b:bqual)
  : result unit
  = match b with
    | Some (Implicit _) ->
      begin
      match a with
      | Some ({aqual_implicit=true}) ->
        return ()
      | _ ->
        fail "missing arg qualifier implicit"
      end

    | _ ->
      begin
      match a with
      | Some ({aqual_implicit=true}) ->
        fail "extra arg qualifier implicit"
      | _ -> return ()
      end

let check_bqual (b0 b1:bqual)
  : result unit
  = match b0, b1 with
    | None, None -> return ()
    | Some (Implicit b0), Some (Implicit b1)
      when b0=b1 ->
      return ()
    | _ ->
      fail "Binder qualifier mismatch"

let check_aqual (a0 a1:aqual)
  : result unit
  = match a0, a1 with
    | None, None -> return ()
    | Some ({aqual_implicit=b0}), Some ({aqual_implicit=b1}) ->
      if b0 = b1
      then return ()
      else fail "Unequal arg qualifiers"
    | _ ->
      fail "Unequal arg qualifiers"

let mk_forall_l (us:universes) (xs:binders) (t:term)
  : term
  = FStar.Compiler.List.fold_right2
        (fun u x t -> U.mk_forall u x.binder_bv t)
        us
        xs
        t

let close_guard (xs:binders) (us:universes) (g:precondition)
  : precondition
  = match g with
    | None -> None
    | Some t -> Some (mk_forall_l us xs t)

let close_guard_with_definition (x:binder) (u:universe) (t:term) (g:precondition)
  : precondition
  = match g with
    | None -> None
    | Some t ->
      Some (
       let t = U.mk_imp (U.mk_eq2 u x.binder_bv.sort (S.bv_to_name x.binder_bv) t) t in
       U.mk_forall u x.binder_bv t
      )

let with_binders (#a:Type) (xs:binders) (us:universes) (f:result a)
  : result a
  = fun ctx ->
      match f ctx with
      | Inl (t, g) -> Inl (t, close_guard xs us g)
      | err -> err

let with_definition (#a:Type) (x:binder) (u:universe) (t:term) (f:result a)
  : result a
  = fun ctx ->
      match f ctx with
      | Inl (a, g) -> Inl (a, close_guard_with_definition x u t g)
      | err -> err

let guard (t:typ)
  : result unit
  = fun _ -> Inl ((), Some t)

let abs (a:typ) (f: binder -> term) : term =
  let x = S.new_bv None a in
  let xb = S.mk_binder x in
  U.abs [xb] (f xb) None

let weaken_subtyping_guard (p:term)
                           (g:precondition)
  : precondition
  = BU.map_opt g (fun q -> U.mk_imp p q)

let strengthen_subtyping_guard (p:term)
                               (g:precondition)
  : precondition
  = Some (BU.dflt p (BU.map_opt g (fun q -> U.mk_conj p q)))

let weaken (p:term) (g:result 'a)
  = fun ctx ->
      match g ctx with
      | Inl (x, q) -> Inl (x, weaken_subtyping_guard p q)
      | err -> err

let weaken_with_guard_formula (p:FStar.TypeChecker.Common.guard_formula) (g:result 'a)
  = match p with
    | Common.Trivial -> g
    | Common.NonTrivial p -> weaken p g
    
let strengthen (p:term) (g:result 'a)
  = fun ctx ->
      match g ctx with
      | Inl (x, q) -> Inl (x, strengthen_subtyping_guard p q)
      | err -> err

let no_guard (g:result 'a)
  : result 'a
  = fun ctx ->
      match g ({ ctx with no_guard = true}) with
      | Inl (x, None) -> Inl (x, None)
      | Inl (x, Some g) -> fail (BU.format1 "Unexpected guard: %s" (P.term_to_string g)) ctx
      | err -> err

let equatable g t = 
  let head, _ = U.head_and_args t in
  Rel.may_relate_with_logical_guard g.tcenv true head

let apply_predicate x p = fun e -> SS.subst [NT(x.binder_bv, e)] p

let curry_arrow (x:binder) (xs:binders) (c:comp) =
  let tail = S.mk (Tm_arrow (xs, c)) R.dummyRange in
  S.mk (Tm_arrow([x], S.mk_Total tail)) R.dummyRange

let curry_abs (b0:binder) (b1:binder) (bs:binders) (body:term) (ropt: option residual_comp) =
  let tail = S.mk (Tm_abs(b1::bs, body, ropt)) body.pos in
  S.mk (Tm_abs([b0], tail, None)) body.pos

let is_gtot_comp c = U.is_tot_or_gtot_comp c && not (U.is_total_comp c)

let rec context_included (g0 g1: list binding) =
  match g0, g1 with
  | [], _ -> true

  | b0::g0', b1::g1' ->
     begin
     match b0, b1 with
     | Binding_var x0, Binding_var x1 ->
       if x0.index = x1.index
       then context_included g0' g1'
       else context_included g0 g1'

     | Binding_lid _, Binding_lid _
     | Binding_univ _, Binding_univ _ ->
       true

     | _ ->
       false
     end

  | _ -> false

let curry_application hd arg args p =
    let head = S.mk (Tm_app(hd, [arg])) p in
    let t = S.mk (Tm_app(head, args)) p in
    t


let lookup (g:env) (e:term) : result (effect_label & typ) =
   match FStar.Hash.lookup (e, FStar.Syntax.Hash.hash_term) table with
   | None -> fail "not in cache"
   | Some he ->
     if he.he_gamma `context_included` g.tcenv.gamma
     then (
       record_cache_hit();
       //BU.print1 "cache hit %s\n" (P.term_to_string e);
       fun _ -> Inl he.he_res
     )
     else (
       record_cache_miss();
       fail "not in cache"
     )

let check_no_escape (bs:binders) t =
    let xs = FStar.Syntax.Free.names t in
    if BU.for_all (fun b -> not (BU.set_mem b.binder_bv xs)) bs
    then return ()
    else fail "Name escapes its scope"

let rec map (#a #b:Type) (f:a -> result b) (l:list a) : result (list b) =
  match l with
  | [] -> return []
  | hd::tl ->
    let! hd = f hd in
    let! tl = map f tl in
    return (hd::tl)

let rec iter2 (xs ys:list 'a) (f: 'a -> 'a -> 'b -> result 'b) (b:'b)
  : result 'b
  = match xs, ys with
    | [], [] -> return b
    | x::xs, y::ys ->
      let! b = f x y b in
      iter2 xs ys f b
    | _ -> fail "Lists of differing length"

let non_informative g t
  : bool
  = N.non_info_norm g.tcenv t

let as_comp (g:env) (et: (effect_label & typ))
  : comp
  = match et with
    | E_TOTAL, t -> S.mk_Total t
    | E_GHOST, t ->
      if non_informative g t
      then S.mk_Total t
      else S.mk_GTotal t

let comp_as_effect_label_and_type (c:comp)
  : option (effect_label & typ)
  = if U.is_total_comp c
    then Some (E_TOTAL, U.comp_result c)
    else if U.is_tot_or_gtot_comp c
    then Some (E_GHOST, U.comp_result c)
    else None

let join_eff e0 e1 =
  match e0, e1 with
  | E_GHOST, _
  | _, E_GHOST -> E_GHOST
  | _ -> E_TOTAL

let join_eff_l es = List.Tot.fold_right join_eff es E_TOTAL

let guard_not_allowed
  : result bool
  = fun ctx -> Inl (ctx.no_guard, None)

let default_norm_steps : Env.steps = 
  let open Env in
  [ Primops;
    Weak;
    HNF;
    UnfoldUntil delta_constant;
    Unascribe;
    Eager_unfolding;
    Iota;
    Exclude Zeta ] 

let debug g f = 
  if Env.debug g.tcenv (Options.Other "Core")
  then f ()

(*
     G |- e : t0 <: t1 | p

or   G |- t0 <: t1 | p

 *)
let rec check_subtype_whnf (g:env) (e:option term) (t0 t1: typ)
  : result unit
  = let fail (s:string) = 
      debug g (fun () ->
        BU.print2 "check_subtype_whnf  [[%s <: %s]] failed\n" (P.term_to_string t0) (P.term_to_string t1));        
      fail (BU.format3 "Subtyping failed because %s: %s </: %s"
              s
              (P.term_to_string t0)
              (P.term_to_string t1))
    in
    debug g (fun () ->
      BU.print2 "check_subtype_whnf %s <: %s\n" (P.term_to_string t0) (P.term_to_string t1));
    let! guard_not_ok = guard_not_allowed in
    let guard_ok = not guard_not_ok in
    let fallback g t0 t1 = 
      if guard_ok && (equatable g t0 || equatable g t1)
      then
        let! u = universe_of g t0 in
        debug g (fun () ->
          BU.print2 "exiting check_subtype_whnf [[%s <: %s]] with guard\n" (P.term_to_string t0) (P.term_to_string t1));
        guard (U.mk_eq2 u (mk_type u) t0 t1)
      else (
          fail "no subtyping rule is applicable"
      )
    in
    match (SS.compress t0).n, (SS.compress t1).n with
    | Tm_refine _, Tm_refine _
      when guard_not_ok ->
      check_equality_whnf g t0 t1

    | Tm_refine(x0, p0), _ ->
      let [x0], p0 = SS.open_term [S.mk_binder x0] p0 in
      if Some? e
      then (
        weaken
          (apply_predicate x0 p0 (Some?.v e))
          (check_subtype g e x0.binder_bv.sort t1)
      )
      else (
        let! u0 = universe_of g x0.binder_bv.sort in
        with_binders [x0] [u0] (
          weaken p0
            (check_subtype (push_binders g [x0]) 
                           (Some (S.bv_to_name x0.binder_bv))
                           x0.binder_bv.sort
                           t1))
      )


    | _, Tm_refine(x1, p1) ->
      let [x1], p1 = SS.open_term [S.mk_binder x1] p1 in
      if Some? e
      then (
        strengthen
          (apply_predicate x1 p1 (Some?.v e))
          (check_subtype g e t0 x1.binder_bv.sort)
      )
      else (
        let! u0 = universe_of g t0 in
        let x0 = S.new_bv None t0 in
        strengthen
            (mk_forall_l [u0] [mk_binder x0] (SS.subst [NT(x1.binder_bv, S.bv_to_name x0)] p1))
            (check_subtype g None t0 x1.binder_bv.sort)
      )
  
    | Tm_arrow (x0::x1::xs, c0), _ ->
      check_subtype_whnf g e (curry_arrow x0 (x1::xs) c0) t1

    | _, Tm_arrow(x0::x1::xs, c1) ->
      check_subtype_whnf g e t0 (curry_arrow x0 (x1::xs) c1)

    | Tm_arrow ([x0], c0), Tm_arrow([x1], c1) ->
      let [x0], c0 = SS.open_comp [x0] c0 in
      let [x1], c1 = SS.open_comp [x1] c1 in
      let! _ = check_bqual x0.binder_qual x1.binder_qual in
      let! u1 = universe_of g x1.binder_bv.sort in
      with_binders [x1] [u1] (
        check_subtype g (Some (S.bv_to_name x1.binder_bv)) x1.binder_bv.sort x0.binder_bv.sort ;!
        check_subcomp (push_binders g [x1])
                      (if U.is_pure_or_ghost_comp c0
                       then let? e in Some (S.mk_Tm_app e (snd (U.args_of_binders [x1])) R.dummyRange)
                       else None)
                      (SS.subst_comp [NT(x0.binder_bv, S.bv_to_name x1.binder_bv)] c0)
                      c1
      )

    | Tm_ascribed (t0, _, _), _ ->
      check_subtype_whnf g e t0 t1
      
    | _, Tm_ascribed (t1, _, _) -> 
      check_subtype_whnf g e t0 t1

    | Tm_type _, Tm_type _ ->
      check_equality_whnf g t0 t1

    | Tm_app _, _
    | _, Tm_app _ ->
      let smt_ok = not (guard_not_ok) in
      let mr, ts = Rel.head_matches_delta g.tcenv smt_ok t0 t1 in
      debug g (fun _ -> BU.print_string "Back from head_matches_delta\n");
      begin
      match mr, ts with
      | Rel.MisMatch _, _
      | Rel.HeadMatch true, _ ->
        //HeadMatch true: heads may match, e.g, both heads are Tm_match nodes, but we can't decide.
        //So, just handle as a fallback
        fallback g t0 t1

      | _, Some (t0', t1') ->
        //match after reduction to t0, t1
        debug g (fun _ ->
          BU.print4 "check_subtype_whnf after redunction [[%s <: %s]] reduced to [[%s <: %s]]\n"
                       (P.term_to_string t0) (P.term_to_string t1)
                       (P.term_to_string t0') (P.term_to_string t1'));
        check_subtype_whnf g e t0' t1'
      
      | Rel.FullMatch, _
      | Rel.HeadMatch false, _ ->
        //heads already match
        check_equality_whnf g t0 t1
      end
      

    | Tm_match (e0, _, brs0, _), Tm_match (e1, _, brs1, _) ->
      //
      // TODO: this will currently check equality of branches,
      //   it could check subtyping instead
      //
      check_equality_match g e0 brs0 e1 brs1
    
    | _ ->
      if U.eq_tm t0 t1 = U.Equal
      then (
        debug g (fun _ -> BU.print_string "exiting check_subtype_whnf (EQUAL)\n");      
        return ()
      )
      else fallback g t0 t1

and check_subtype (g:env) (e:option term) (t0 t1:typ)
  = debug g (fun () ->
      BU.print2 "check_subtype %s <: %s\n" (P.term_to_string t0) (P.term_to_string t1));
    match U.eq_tm t0 t1 with
    | U.Equal -> 
      debug g (fun _ -> BU.print_string "exiting check_subtype (EQUAL)\n");
      return ()
    | _ ->
      let t0' = N.normalize_refinement default_norm_steps g.tcenv t0 in
      let t1' = N.normalize_refinement default_norm_steps g.tcenv t1 in
      check_subtype_whnf g e t0' t1'

and check_equality_formula (g:env) (phi0 phi1:typ) =
  guard (U.mk_iff phi0 phi1)

and check_equality_match (g:env)
  (scrutinee0:term) (brs0:list branch)
  (scrutinee1:term) (brs1:list branch)
  = let fail (s:string) = 
      fail (BU.format3 "match equality failed because %s: %s </: %s"
              s
              (P.term_to_string (S.mk (Tm_match (scrutinee0, None, brs0, None)) Range.dummyRange))
              (P.term_to_string (S.mk (Tm_match (scrutinee1, None, brs1, None)) Range.dummyRange))) in

    let! _ = check_equality_whnf g scrutinee0 scrutinee1 in

    let rec check_equality_branches (brs0 brs1:list branch)
      : result unit
      = match brs0, brs1 with
        | [], [] -> return ()
        | _, []
        | [], _ -> fail "different number of branches in match nodes"
        | (p0, None, body0)::brs0, (p1, None, body1)::brs1 ->
          //
          // TODO: S.eq_pat does not compare universes or bound variables
          //       Compare bv sorts for the bvs in here?
          //
          if not (S.eq_pat p0 p1)
          then fail "patterns not equal"
          else begin
            let (p0, _, body0) = SS.open_branch (p0, None, body0) in
            let (p1, _, body1) = SS.open_branch (p1, None, body1) in
            match PatternUtils.raw_pat_as_exp g.tcenv p0, PatternUtils.raw_pat_as_exp g.tcenv p1 with
            | Some (_, bvs0), Some (_, bvs1) ->
              let s = List.map2 (fun bv0 bv1 ->
                NT(bv1, S.bv_to_name bv0)
              ) bvs0 bvs1 in
              let body1 = SS.subst s body1 in
              let bs0 = List.map S.mk_binder bvs0 in
              //
              // We need universes for the binders
              // Don't expect it to fail
              //
              let! _, us, g = check_binders g bs0 in
              let! _ = with_binders bs0 us (check_equality g body0 body1) in
              check_equality_branches brs0 brs1
             | _ -> fail "raw_pat_as_exp failed in check_equality match rule"
          end
        | _, _ -> fail "check_equality does not support branches with when"
    in
    check_equality_branches brs0 brs1

and check_equality_whnf (g:env) (t0 t1:typ)
  = let err () =
        fail (BU.format2 "not equal terms: %s <> %s"
                         (P.term_to_string t0)
                         (P.term_to_string t1))
    in
    let! guard_not_ok = guard_not_allowed in
    let guard_ok = not guard_not_ok in
    let fallback t0 t1 =
      if guard_ok
      then if equatable g t0
            || equatable g t1
           then let! _, t_typ = check' g t0 in
                let! u = universe_of g t_typ in
                guard (U.mk_eq2 u t_typ t0 t1)
           else err ()
      else err ()
    in
    if Env.debug g.tcenv (Options.Other "Core")
    then BU.print2 "check_equality_whnf %s =?= %s\n" (P.term_to_string t0) (P.term_to_string t1);
    if U.eq_tm t0 t1 = U.Equal
    then return ()
    else
      match t0.n, t1.n with
      | Tm_uinst (f0, us0), Tm_uinst(f1, us1) ->
        //        when g.allow_universe_instantiation ->
        // I had initially thought that the only place we might need
        // universe instantiation was at the top-level, but that isn't true
        // The tactic framework is often presented with goals that look like
        //
        // (eq2<2> #pre_t (?77 uu___) (return_pre (?69 (reveal<U_unif ?15:460.45> #unit (return<U_unif ?15:460.45> #unit ())))))
        //
        // i.e., they contain unresolved universes like U_unif ...
        //
        // So the solution we check may contain these universe variables too
        // and we need to solve them here
        if U.eq_tm f0 f1 = U.Equal
        then if Rel.teq_nosmt_force g.tcenv t0 t1
             then return ()
             else err ()
        else err ()

      | Tm_type u0, Tm_type u1 ->
        // when g.allow_universe_instantiation ->
        // See above remark regarding universe instantiations
        if Rel.teq_nosmt_force g.tcenv t0 t1
        then return ()
        else err ()
        
      | Tm_abs(b0::b1::bs, body, ropt), _ ->
        let t0 = curry_abs b0 b1 bs body ropt in
        check_equality_whnf g t0 t1

      | _, Tm_abs(b0::b1::bs, body, ropt) ->
        let t1 = curry_abs b0 b1 bs body ropt in
        check_equality_whnf g t0 t1

      | Tm_abs([b0], body0, _), Tm_abs([b1], body1, _) ->
        check_equality g b0.binder_bv.sort b1.binder_bv.sort;!
        check_bqual b0.binder_qual b1.binder_qual;!
        let! u = universe_of g b0.binder_bv.sort in
        let [b0], body0 = SS.open_term [b0] body0 in
        //little strange to use a DB substitution here
        //Maybe cleaner to open both and use an NT subst
        let body1 = SS.subst [DB(0, b0.binder_bv)] body1 in
        with_binders [b0] [u]
          (let g = push_binders g [b0] in
           check_equality g body0 body1)

      | Tm_refine(b0, phi0), Tm_refine(b1, phi1) ->
        check_equality_whnf g b0.sort b1.sort;!
        let [b], phi0 = SS.open_term [S.mk_binder b0] phi0 in
        //little strange to use a DB substitution here
        //Maybe cleaner to open both and use an NT subst
        let phi1 = SS.subst [DB(0, b.binder_bv)] phi1 in
        begin
        match! guard_not_allowed with
        | true -> check_equality g phi0 phi1
        | _ ->
          let! u = universe_of g b.binder_bv.sort in
          with_binders [b] [u]
            (let g = push_binders g [b] in
              handle_with
              (check_equality g phi0 phi1)
              (fun _ -> check_equality_formula g phi0 phi1))
        end

      | Tm_match (e0, _, brs0, _), Tm_match (e1, _, brs1, _) ->
        check_equality_match g e0 brs0 e1 brs1

      | Tm_ascribed (t0, _, _), _ ->
        check_equality g t0 t1
        
      | _, Tm_ascribed(t1, _, _) ->
        check_equality g t0 t1
        
      | Tm_app _, _
      | _, Tm_app _ ->
        let mr, ts = Rel.head_matches_delta g.tcenv guard_ok t0 t1 in
        begin
        match mr, ts with
        | Rel.MisMatch _, _
        | Rel.HeadMatch true, _ ->
          fallback t0 t1

        | _, Some (t0, t1) ->
          check_equality_whnf g t0 t1

        | Rel.FullMatch, _
        | Rel.HeadMatch false, _ ->
          if guard_ok 
          && (equatable g t0 || equatable g t1)
          then fallback t0 t1
          else (
            match (SS.compress t0).n, (SS.compress t1).n with
            | Tm_app (hd0, args0), Tm_app(hd1, args1) ->
              check_equality_whnf g hd0 hd1;!
              check_equality_args g args0 args1
            | _ -> fallback t0 t1
          )
        end

      | _ -> fallback t0 t1

and check_equality (g:env) (t0 t1:typ)
  = match U.eq_tm t0 t1 with
    | U.Equal -> return ()
    | _ ->
      //reduce to whnf, but don't unfold tac_opaque symbols
      let t0' = N.normalize_refinement default_norm_steps g.tcenv t0 in
      let t1' = N.normalize_refinement default_norm_steps g.tcenv t1 in
      check_equality_whnf g t0' t1'

and check_equality_args (g:env) (a0 a1:args)
  : result unit
  = if List.length a0 = List.length a1
    then iter2 a0 a1
         (fun (t0, q0) (t1, q1) _ ->
            check_aqual q0 q1;!
            check_equality g t0 t1)
         ()
    else fail "Unequal number of arguments"

and check_subcomp (g:env) (e:option term) (c0 c1:comp)
  : result unit
  = let destruct_comp c =
        if U.is_total_comp c
        then Some (E_TOTAL, U.comp_result c)
        else if U.is_tot_or_gtot_comp c
        then Some (E_GHOST, U.comp_result c)
        else None
    in
    match destruct_comp c0, destruct_comp c1 with
    | None, _
    | _, None ->
      if U.eq_comp c0 c1 = U.Equal
      then return ()
      else (
        let ct_eq ct0 ct1 =
          check_equality g ct0.result_typ ct1.result_typ ;!
          check_equality_args g ct0.effect_args ct1.effect_args
        in
        let ct0 = U.comp_to_comp_typ_nouniv c0 in
        let ct1 = U.comp_to_comp_typ_nouniv c1 in
        if I.lid_equals ct0.effect_name ct1.effect_name
        then ct_eq ct0 ct1
        else (
          let ct0 = Env.unfold_effect_abbrev g.tcenv c0 in
          let ct1 = Env.unfold_effect_abbrev g.tcenv c1 in          
          if I.lid_equals ct0.effect_name ct1.effect_name
          then ct_eq ct0 ct1
          else fail (BU.format2 "Subcomp failed: Unequal computation types %s and %s" 
                            (Ident.string_of_lid ct0.effect_name)
                            (Ident.string_of_lid ct1.effect_name))
        )
      )

    | Some (E_TOTAL, t0), Some (_, t1)
    | Some (E_GHOST, t0), Some (E_GHOST, t1) ->
      check_subtype g e t0 t1

    | Some (E_GHOST, t0), Some (E_TOTAL, t1) ->
      if non_informative g t1
      then check_subtype g e t0 t1
      else fail "Expected a Total computation, but got Ghost"

and memo_check (g:env) (e:term)
  : result (effect_label & typ)
  = handle_with
      (lookup g e)
      (fun _ ctx ->
         let r = check' g e ctx in
         match r with
         | Inl res ->
           insert g e res;
           r
         | _ -> r)

and check (msg:string) (g:env) (e:term)
  : result (effect_label & typ)
  = with_context msg (Some e) (fun _ -> memo_check g e)

(*  G |- e : Tot t | pre *)
and check' (g:env) (e:term)
  : result (effect_label & typ) =
  // (if Env.debug g.tcenv (Options.Other "Core")
  //  then dump_context
  //  else return ());!
  let e = SS.compress e in
  match e.n with
  | Tm_lazy ({lkind=Lazy_embedding _}) ->
    check' g (U.unlazy e)

  | Tm_lazy i ->
    return (E_TOTAL, i.ltyp)
    
  | Tm_meta(t, _) ->
    memo_check g t

  | Tm_uvar (uv, s) ->
    return (E_TOTAL, SS.subst' s (U.ctx_uvar_typ uv))

  | Tm_name x ->
    begin
    match Env.try_lookup_bv g.tcenv x with
    | None ->
      fail (BU.format1 "Variable not found: %s" (P.bv_to_string x))
    | Some (t, _) ->
      return (E_TOTAL, t)
    end

  | Tm_fvar f ->
    begin
    match Env.try_lookup_lid g.tcenv f.fv_name.v with
    | Some (([], t), _) ->
      return (E_TOTAL, t)

    | _ -> //no implicit universe instantiation allowed
      fail "Missing universes instantiation"
    end

  | Tm_uinst ({n=Tm_fvar f}, us) ->
    begin
    match Env.try_lookup_and_inst_lid g.tcenv us f.fv_name.v with
    | None ->
      fail (BU.format1 "Top-level name not found: %s" (Ident.string_of_lid f.fv_name.v))

    | Some (t, _) ->
      return (E_TOTAL, t)
    end

  | Tm_constant c ->
    begin
    let open FStar.Const in
    match c with
    | Const_range_of
    | Const_set_range_of
    | Const_reify
    | Const_reflect _ ->
      fail "Unhandled constant"

    | _ ->
      let t = FStar.TypeChecker.TcTerm.tc_constant g.tcenv e.pos c in
      return (E_TOTAL, t)
    end

  | Tm_type u ->
    return (E_TOTAL, mk_type (U_succ u))

  | Tm_refine(x, phi) ->
    let [x], phi = SS.open_term [S.mk_binder x] phi in
    let! _, t = check "refinement head" g x.binder_bv.sort in
    let! u = is_type g t in
    with_binders [x] [u] (
      let g' = push_binders g [x] in
      let! _, t' = check "refinement formula" g' phi in
      is_type g' t';!
      return (E_TOTAL, t)
    )

  | Tm_abs(xs, body, _) ->
    let xs, body = SS.open_term xs body in
    let! xs, us, g = with_context "abs binders" None (fun _ -> check_binders g xs) in
    with_binders xs us (
      let! t = check "abs body" g body in
      return (E_TOTAL, U.arrow xs (as_comp g t))
    )

  | Tm_arrow(xs, c) ->
    let xs, c = SS.open_comp xs c in
    let! xs, us, g = with_context "arrow binders" None (fun _ -> check_binders g xs) in
    with_binders xs us (
      let! u = with_context "arrow comp" None (fun _ -> check_comp g c) in
      return (E_TOTAL, mk_type (S.U_max (u::us)))
    )

  | Tm_app (hd, [(t1, None); (t2, None)])
    when TcUtil.short_circuit_head hd ->
    let! eff_hd, t_hd = check "app head" g hd in
    let! x, eff_arr1, s1 = is_arrow g t_hd in    
    let! eff_arg1, t_t1 = check "app arg" g t1 in
    with_context "operator arg1" None (fun _ -> check_subtype g (Some t1) t_t1 x.binder_bv.sort) ;!    
    let s1 = SS.subst [NT(x.binder_bv, t1)] s1 in
    let! y, eff_arr2, s2 = is_arrow g s1 in
    let guard_formula = TcUtil.short_circuit hd [(t1, None)]in
    let! eff_arg2, t_t2 = weaken_with_guard_formula guard_formula (check "app arg" g t2) in    
    with_context "operator arg2" None (fun _ -> check_subtype g (Some t2) t_t2 y.binder_bv.sort) ;!
    return (join_eff_l [eff_hd; eff_arr1; eff_arr2; eff_arg1; eff_arg2],
            SS.subst [NT(y.binder_bv, t2)] s2)

  | Tm_app (hd, [(arg, arg_qual)]) ->
    let! eff_hd, t = check "app head" g hd in
    let! x, eff_arr, t' = is_arrow g t in
    let! eff_arg, t_arg = check "app arg" g arg in
    with_context "app subtyping" None (fun _ -> check_subtype g (Some arg) t_arg x.binder_bv.sort) ;!
    with_context "app arg qual" None (fun _ -> check_arg_qual arg_qual x.binder_qual) ;!
    return (join_eff eff_hd (join_eff eff_arr eff_arg), SS.subst [NT(x.binder_bv, arg)] t')

  | Tm_app(hd, arg::args) ->
    let head = S.mk (Tm_app(hd, [arg])) e.pos in
    let t = S.mk (Tm_app(head, args)) e.pos in
    memo_check g t

  | Tm_ascribed (e, (Inl t, _, eq), _) ->
    let! eff, te = check "ascription head" g e in
    let! _, t' = check "ascription type" g t in
    is_type g t';!
    with_context "ascription subtyping" None (fun _ -> check_subtype g (Some e) te t);!
    return (eff, t)

  | Tm_ascribed (e, (Inr c, _, _), _) ->
    if U.is_tot_or_gtot_comp c
    then (
      let! eff, te = check "ascription head" g e in
      let! _ = with_context "ascription comp" None (fun _ -> check_comp g c) in
      let c_e = as_comp g (eff, te) in
      check_subcomp g (Some e) c_e c;!
      let Some (eff, t) = comp_as_effect_label_and_type c in
      return (eff, t)
    )
    else fail (BU.format1 "Effect ascriptions are not fully handled yet: %s" (P.comp_to_string c))

  | Tm_let((false, [lb]), body) ->
    let Inl x = lb.lbname in
    let [x], body = SS.open_term [S.mk_binder x] body in
    if I.lid_equals lb.lbeff PC.effect_Tot_lid
    then (
      let! eff_def, tdef = check "let definition" g lb.lbdef in
      let! _, ttyp = check "let type" g lb.lbtyp in
      let! u = is_type g ttyp in
      with_context "let subtyping" None (fun _ -> check_subtype g (Some lb.lbdef) tdef ttyp) ;!
      with_definition x u lb.lbdef (
        let g = push_binders g [x] in
        let! eff_body, t = check "let body" g body in
        check_no_escape [x] t;!
        return (join_eff eff_def eff_body, t)
      )
    )
    else (
      fail "Let binding is effectful"
    )

  | Tm_match(sc, None, branches, rc_opt) ->
    let! eff_sc, t_sc = check "scrutinee" g sc in
    let! u_sc = with_context "universe_of" (Some t_sc) (fun _ -> universe_of g t_sc) in
    let rec check_branches path_condition
                           branch_typ_opt
                           branches
      : result (effect_label & typ)
      = match branches with
        | [] ->
          (match branch_typ_opt with
           | None ->
             fail "could not compute a type for the match"

           | Some et ->
             guard (U.mk_imp path_condition U.t_false);!
             return et)

        | (p, None, b) :: rest ->
          let (p, _, b) = SS.open_branch (p, None, b) in
          match PatternUtils.raw_pat_as_exp g.tcenv p with
          | None ->
            fail "Ill-formed pattern"

          | Some (e, bvs) ->
            let binders = List.map S.mk_binder bvs in
            let! bs_g = check_binders g binders in
            let bs, us, g' = bs_g in
            let! eff_pat, t = check "pattern term" g' e in
            with_context "Pattern and scrutinee type compatibility" None
                          (fun _ -> no_guard (check_scrutinee_pattern_type_compatible g' t_sc t)) ;!
            let pat_sc_eq = U.mk_eq2 u_sc t_sc sc e in
            let! eff_br, tbr =
              with_binders bs us
                (weaken
                  (U.mk_conj path_condition pat_sc_eq)
                  (let! eff_br, tbr = check "branch" g' b in
                   match branch_typ_opt with
                   | None ->
                     check_no_escape bs tbr;!
                     return (eff_br, tbr)

                   | Some (acc_eff, expect_tbr) ->
                     check_subtype g' (Some b) tbr expect_tbr;!
                     return (join_eff eff_br acc_eff, expect_tbr))) in
            let path_condition =
              U.mk_conj path_condition
                        (mk_forall_l us bs (U.mk_neg pat_sc_eq))
            in
            match p.v with
            | Pat_var _
            | Pat_wild _ ->
              //trivially exhaustive
              (match rest with
               | _ :: _ -> fail "Redundant branches after wildcard"
               | _ -> return (eff_br, tbr))

            | _ ->
              check_branches path_condition (Some (eff_br, tbr)) rest
    in

    let! branch_typ_opt =
        match rc_opt with
        | Some ({ residual_typ = Some t }) ->
          with_context "residual type" (Some t) (fun _ -> universe_of g t) ;!
          return (Some (E_TOTAL, t))

        | _ ->
          return None
    in
    let! eff_br, t_br = check_branches U.t_true branch_typ_opt branches in
    return (join_eff eff_sc eff_br, t_br)

  | Tm_match(sc, Some (as_x, (Inl returns_ty, None, eq)), branches, rc_opt) ->
    let! eff_sc, t_sc = check "scrutinee" g sc in
    let! u_sc = with_context "universe_of" (Some t_sc) (fun _ -> universe_of g t_sc) in
    let [as_x], returns_ty = SS.open_term [as_x] returns_ty in
    let as_x = {as_x with binder_bv = { as_x.binder_bv with sort = t_sc } } in
    let g_as_x = push_binders g [as_x] in
    let! _eff_t, returns_ty_t = check "return type" g_as_x returns_ty in
    let! _u_ty = is_type g_as_x returns_ty_t in
    let rec check_branches (path_condition: S.term)
                           (branches: list S.branch)
                           (acc_eff: effect_label)
      : result effect_label
      = match branches with
        | [] ->
          guard (U.mk_imp path_condition U.t_false);!
          return acc_eff

        | (p, None, b) :: rest ->
          let (p, _, b) = SS.open_branch (p, None, b) in
          match PatternUtils.raw_pat_as_exp g.tcenv p with
          | None ->
            fail "Ill-formed pattern"

          | Some (e, bvs) ->
            let binders = List.map S.mk_binder bvs in
            let! bs_g = check_binders g binders in
            let bs, us, g' = bs_g in
            let! eff_pat, t = check "pattern term" g' e in
            // TODO: use pattern scrutinee type compatibility function
            with_context "Pattern and scrutinee type compatibility"
                         None
                          (fun _ -> no_guard (check_subtype g' (Some e) t_sc t)) ;!
            let pat_sc_eq = U.mk_eq2 u_sc t_sc sc e in
            let! eff_br, tbr =
              with_binders bs us
                (weaken
                  (U.mk_conj path_condition pat_sc_eq)
                  (let! eff_br, tbr = check "branch" g' b in
                   let expect_tbr = SS.subst [NT(as_x.binder_bv, e)] returns_ty in
                   (if eq
                    then check_equality g' tbr expect_tbr
                    else check_subtype  g' (Some b) tbr expect_tbr);!
                    return (join_eff eff_br acc_eff, expect_tbr))) in
            let path_condition =
              U.mk_conj path_condition
                        (mk_forall_l us bs (U.mk_neg pat_sc_eq))
            in
            match p.v with
            | Pat_var _
            | Pat_wild _ ->
              //trivially exhaustive
              (match rest with
               | _ :: _ -> fail "Redundant branches after wildcard"
               | _ -> return eff_br)

            | _ ->
              check_branches path_condition rest eff_br
    in
    let! eff = check_branches U.t_true branches E_TOTAL in
    let ty = SS.subst [NT(as_x.binder_bv, sc)] returns_ty in
    return (eff, ty)

  | Tm_match _ ->
    fail "Match with effect returns ascription, or tactic handler"

  | _ ->
    fail (BU.format1 "Unexpected term: %s" (FStar.Syntax.Print.tag_of_term e))

and check_binders (g:env) (xs:binders)
  : result (binders & list universe & env)
  = match xs with
    | [] ->
      return ([], [], g)

    | x ::xs ->
      let! _, t = check "binder sort" g x.binder_bv.sort in
      let! u = is_type g t in
      with_binders [x] [u] (
        let g' = push_binders g [x] in
        let! xs, us, g = check_binders g' xs in
        return (x :: xs, u::us, g)
      )

//
// May be called with an effectful comp type, e.g. from within an arrow
// Caller should enforce Tot/GTot if needed
//
and check_comp (g:env) (c:comp)
  : result universe
  = match c.n with
    | Total(t, _)
    | GTotal(t, _) ->
      let! _, t = check "(G)Tot comp result" g (U.comp_result c) in
      is_type g t
    | Comp ct ->
      if List.length ct.comp_univs <> 1
      then fail "Unexpected/missing universe instantitation in comp"
      else let u = List.hd ct.comp_univs in
           let effect_app_tm =
             let head = S.mk_Tm_uinst (S.fvar ct.effect_name delta_constant None) [u] in
             S.mk_Tm_app head ((as_arg ct.result_typ)::ct.effect_args) ct.result_typ.pos in
           let! _, t = check "effectful comp" g effect_app_tm in
           with_context "comp fully applied" None (fun _ -> check_subtype g None t S.teff);!
           let c_lid = Env.norm_eff_name g.tcenv ct.effect_name in           
           let is_total = Env.lookup_effect_quals g.tcenv c_lid |> List.existsb (fun q -> q = S.TotalEffect) in
           if not is_total
           then return S.U_zero  //if it is a non-total effect then u0
           else if U.is_pure_or_ghost_effect c_lid
           then return u
           else (
              match Env.effect_repr g.tcenv c u with
              | None -> fail (BU.format2 "Total effect %s (normalized to %s) does not have a representation"
                                        (Ident.string_of_lid (U.comp_effect_name c))
                                        (Ident.string_of_lid c_lid))
              | Some tm -> universe_of g tm
           )

and universe_of (g:env) (t:typ)
  : result universe
  = let! _, t = check "universe of" g t in
    is_type g t

and check_scrutinee_pattern_type_compatible (g:env) (t_sc t_pat:typ)
  : result precondition
  = let open Env in
    let err (s:string) =
      fail (BU.format3 "Scrutinee type %s and Pattern type %s are not compatible because %s"
              (P.term_to_string t_sc)
              (P.term_to_string t_pat)
              s) in

    let t_sc = t_sc |> N.normalize_refinement N.whnf_steps g.tcenv
                    |> U.unrefine in

    let head_sc, args_sc = U.head_and_args t_sc in
    let head_pat, args_pat = U.head_and_args t_pat in

    let! (t_fv:fv) =
      match (SS.compress head_sc).n, (SS.compress head_pat).n with
      | Tm_fvar (fv_head), Tm_fvar (fv_pat)
        when Ident.lid_equals (lid_of_fv fv_head) (lid_of_fv fv_pat) -> return fv_head
      | Tm_uinst ({n=Tm_fvar (fv_head)}, us_head), Tm_uinst ({n=Tm_fvar (fv_pat)}, us_pat)
        when Ident.lid_equals (lid_of_fv fv_head) (lid_of_fv fv_pat) ->
        if Rel.teq_nosmt_force g.tcenv head_sc head_pat
        then return fv_head
        else err "Incompatible universe instantiations"
      | _, _ -> err (BU.format2 "Head constructors(%s and %s) not fvar"
                      (P.tag_of_term head_sc)
                      (P.tag_of_term head_pat)) in

    (if Env.is_type_constructor g.tcenv (lid_of_fv t_fv)
     then return t_fv
     else err (BU.format1 "%s is not a type constructor" (P.fv_to_string t_fv)));!

    (if List.length args_sc = List.length args_pat then return t_fv
     else err (BU.format2 "Number of arguments don't match (%s and %s)"
                          (string_of_int (List.length args_sc))
                          (string_of_int (List.length args_pat))));!

   let params_sc, params_pat =
     match Env.num_inductive_ty_params g.tcenv (S.lid_of_fv t_fv) with
     | None -> args_sc, args_pat
     | Some n -> fst (BU.first_N n args_sc), fst (BU.first_N n args_pat) in

   let! (_:unit) = iter2 params_sc params_pat (fun (t_sc, _) (t_pat, _) _ ->
     check_equality g t_sc t_pat
   ) () in

   // TODO: return equality of indices for the caller to weaken the guard with?

   return None

let check_term_top g e t (must_tot:bool)
  : result unit
  = let g = { tcenv = g; allow_universe_instantiation = false } in
    let! eff_te = check "top" g e in
    let target_comp = 
      if must_tot || fst eff_te = E_TOTAL
      then S.mk_Total t
      else S.mk_GTotal t
    in
    with_context "top-level subtyping" None (fun _ ->
      check_subcomp ({ g with allow_universe_instantiation = true}) (Some e) (as_comp g eff_te) target_comp)

let simplify_steps =
    [Env.Beta; 
     Env.UnfoldUntil delta_constant;
     Env.UnfoldQual ["unfold"];
     Env.UnfoldOnly [PC.pure_wp_monotonic_lid; PC.pure_wp_monotonic0_lid];
     Env.Simplify;
     Env.Primops;
     Env.NoFullNorm]

let profile_check_term_top g e t must_tot ctx = 
  FStar.Profiling.profile
    (fun _ -> check_term_top g e t must_tot ctx)
    None
    "FStar.TypeChecker.Core.check_term_top"
    
let check_term g e t (must_tot:bool)
  = if Env.debug g (Options.Other "Core")
    then BU.print2 "Entering core with %s <: %s\n"
                   // (BU.stack_dump ())
                   (P.term_to_string e)
                   (P.term_to_string t);
    reset_cache_stats();
    let ctx = { no_guard = false; error_context = [] } in
    let res = 
      match profile_check_term_top g e t must_tot ctx with
      | Inl (_, g) -> Inl g
      | Inr err -> Inr err
    in
    (
    let res = 
      match res with
      | Inl (Some guard0) ->
        // Options.push();
        // Options.set_option "debug_level" (Options.List [Options.String "Unfolding"]);
        let guard = N.normalize simplify_steps g guard0 in
        // Options.pop();
        if Env.debug g (Options.Other "CoreExit")
        || Env.debug g (Options.Other "Core")
        then
          BU.print2 "Exiting core: Simplified guard from {{%s}} to {{%s}}\n"
            (P.term_to_string guard0)
            (P.term_to_string guard);
        Inl (Some guard)

      | Inl _ ->
        if Env.debug g (Options.Other "Core")        
        then BU.print_string "Exiting core (ok)\n";
        res

      | Inr _ ->
        if Env.debug g (Options.Other "Core")        
        then BU.print_string "Exiting core (failed)\n";      
        res
    in
    if FStar.Options.profile_enabled None "FStar.TypeChecker.Core.check_term_top"
    then (
      let cs = report_cache_stats() in
      BU.print2 "Cache_stats { hits = %s; misses = %s }\n"
                     (BU.string_of_int cs.hits)
                     (BU.string_of_int cs.misses)
    );
    res
    )
