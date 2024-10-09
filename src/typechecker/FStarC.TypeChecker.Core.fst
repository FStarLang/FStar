module FStarC.TypeChecker.Core
open FStarC
open FStar.List.Tot
open FStarC.Compiler
open FStarC.Compiler.Util
open FStarC.Compiler.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
module Env = FStarC.TypeChecker.Env
module S = FStarC.Syntax.Syntax
module R = FStarC.Compiler.Range
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module PC = FStarC.Parser.Const
module I = FStarC.Ident
module P = FStarC.Syntax.Print
module BU = FStarC.Compiler.Util
module TcUtil = FStarC.TypeChecker.Util
module Hash = FStarC.Syntax.Hash
module Subst = FStarC.Syntax.Subst
module TEQ = FStarC.TypeChecker.TermEqAndSimplify

open FStarC.Class.Show
open FStarC.Class.Setlike
open FStarC.Class.Tagged

let dbg       = Debug.get_toggle "Core"
let dbg_Eq    = Debug.get_toggle "CoreEq"
let dbg_Top   = Debug.get_toggle "CoreTop"
let dbg_Exit  = Debug.get_toggle "CoreExit"

let goal_ctr = BU.mk_ref 0
let get_goal_ctr () = !goal_ctr
let incr_goal_ctr () = let v = !goal_ctr in goal_ctr := v + 1; v + 1

let guard_handler_t = Env.env -> typ -> bool

type env = {
   tcenv : Env.env;
   allow_universe_instantiation : bool;
   max_binder_index : int;
   guard_handler : option guard_handler_t;
   should_read_cache: bool
}

let push_binder g b =
  if b.binder_bv.index <= g.max_binder_index
  then failwith "Assertion failed: unexpected shadowing in the core environment"
  else { g with tcenv = Env.push_binders g.tcenv [b]; max_binder_index = b.binder_bv.index }

let push_binders = List.fold_left push_binder

let fresh_binder (g:env) (old:binder)
  : env & binder
  = let ctr = g.max_binder_index + 1 in
    let bv = { old.binder_bv with index = ctr } in
    let b = S.mk_binder_with_attrs bv old.binder_qual old.binder_positivity old.binder_attrs in
    push_binder g b, b

let open_binders (g:env) (bs:binders)
  = let g, bs_rev, subst =
        List.fold_left
          (fun (g, bs, subst) b ->
            let bv = { b.binder_bv with sort = Subst.subst subst b.binder_bv.sort } in
            let b = { binder_bv = bv;
                      binder_qual = Subst.subst_bqual subst b.binder_qual;
                      binder_positivity = b.binder_positivity;
                      binder_attrs = List.map (Subst.subst subst) b.binder_attrs } in
            let g, b' = fresh_binder g b in
            g, b'::bs, DB(0, b'.binder_bv)::Subst.shift_subst 1 subst)
          (g, [], [])
          bs
    in
    g, List.rev bs_rev, subst

let open_pat (g:env) (p:pat)
  : env & pat & subst_t
  = let rec open_pat_aux g p sub =
        match p.v with
        | Pat_constant _ -> g, p, sub

        | Pat_cons(fv, us_opt, pats) ->
          let g, pats, sub =
            List.fold_left
              (fun (g, pats, sub) (p, imp) ->
                let g, p, sub = open_pat_aux g p sub in
                (g, (p,imp)::pats, sub))
              (g, [], sub)
              pats
            in
            g, {p with v=Pat_cons(fv, us_opt, List.rev pats)}, sub

        | Pat_var x ->
          let bx = S.mk_binder {x with sort = Subst.subst sub x.sort} in
          let g, bx' = fresh_binder g bx in
          let sub = DB(0, bx'.binder_bv)::Subst.shift_subst 1 sub in
          g, {p with v=Pat_var bx'.binder_bv}, sub

        | Pat_dot_term eopt ->
          let eopt = BU.map_option (Subst.subst sub) eopt in
          g, {p with v=Pat_dot_term eopt}, sub
    in
    open_pat_aux g p []


let open_term (g:env) (b:binder) (t:term)
  : env & binder & term
  = let g, b' = fresh_binder g b in
    let t = FStarC.Syntax.Subst.subst [DB(0, b'.binder_bv)] t in
    g, b', t

let open_term_binders (g:env) (bs:binders) (t:term)
  : env & binders & term
  = let g, bs, subst = open_binders g bs in
    g, bs, Subst.subst subst t

let open_comp (g:env) (b:binder) (c:comp)
  : env & binder & comp
  = let g, bx = fresh_binder g b in
    let c = FStarC.Syntax.Subst.subst_comp [DB(0, bx.binder_bv)] c in
    g, bx, c

let open_comp_binders (g:env) (bs:binders) (c:comp)
  : env & binders & comp
  = let g, bs, s = open_binders g bs in
    let c = FStarC.Syntax.Subst.subst_comp s c in
    g, bs, c

let arrow_formals_comp g c =
    let bs, c = U.arrow_formals_comp_ln c in
    let g, bs, subst = open_binders g bs in
    g, bs, Subst.subst_comp subst c

let open_branch (g:env) (br:S.branch)
  : env & branch
  = let (p, wopt, e) = br in
    let g, p, s = open_pat g p in
    g, (p, BU.map_option (Subst.subst s) wopt, Subst.subst s e)

//br0 and br1 are expected to have equal patterns
let open_branches_eq_pat (g:env) (br0 br1:S.branch)
  = let (p0, wopt0, e0) = br0 in
    let (_,  wopt1, e1) = br1 in
    let g, p0, s = open_pat g p0 in
    g,
    (p0, BU.map_option (Subst.subst s) wopt0, Subst.subst s e0),
    (p0, BU.map_option (Subst.subst s) wopt1, Subst.subst s e1)

let precondition = option typ

let success a = a & precondition

type relation =
  | EQUALITY
  | SUBTYPING : option term -> relation

let relation_to_string = function
  | EQUALITY -> "=?="
  | SUBTYPING None -> "<:?"
  | SUBTYPING (Some tm) -> BU.format1 "( <:? %s)" (show tm)

type context_term =
  | CtxTerm : term -> context_term
  | CtxRel : term -> relation -> term -> context_term

let context_term_to_string (c:context_term) =
  match c with
  | CtxTerm term -> show term
  | CtxRel t0 r t1 ->
    BU.format3 "%s %s %s"
              (show t0)
              (relation_to_string r)
              (show t1)

type context = {
  no_guard : bool;
  unfolding_ok : bool;
  error_context: list (string & option context_term)
}

(* The instance prints some brief info on the error_context. `print_context`
below is a full printer. *)
instance showable_context : showable context = {
  show = (fun context -> BU.format3 "{no_guard=%s; unfolding_ok=%s; error_context=%s}"
                                    (show context.no_guard)
                                    (show context.unfolding_ok)
                                    (show (List.map fst context.error_context)));
}

let print_context (ctx:context)
  : string =
  let rec aux (depth:string) (ctx:_) =
    match ctx with
    | [] -> ""
    | (msg, ctx_term)::tl ->
      let hd =
        BU.format3
          "%s %s (%s)\n"
          depth
          msg
          (match ctx_term with None -> "" | Some ctx_term -> context_term_to_string ctx_term)
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

type __result a =
  | Success of a
  | Error of error

instance showable_result #a (_ : showable a) : Tot (showable (__result a)) = {
  show = (function
          | Success a -> "Success " ^ show a
          | Error e ->   "Error " ^ print_error_short e);
}

let result a = context -> __result (success a)

type hash_entry = {
   he_term:term;
   he_gamma:list binding;
   he_res:success (tot_or_ghost & typ);
}
module THT = FStarC.Syntax.TermHashTable
type tc_table = THT.hashtable hash_entry
let equal_term_for_hash t1 t2 =
  FStarC.Profiling.profile (fun _ -> Hash.equal_term t1 t2) None "FStarC.TypeChecker.Core.equal_term_for_hash"
let equal_term t1 t2 =
  FStarC.Profiling.profile (fun _ -> Hash.equal_term t1 t2) None "FStarC.TypeChecker.Core.equal_term"
let table : tc_table = THT.create 1048576 //2^20
type cache_stats_t = { hits : int; misses : int }
let cache_stats = BU.mk_ref { hits = 0; misses = 0 }
let record_cache_hit () =
   let cs = !cache_stats in
    cache_stats := { cs with hits = cs.hits + 1 }
let record_cache_miss () =
   let cs = !cache_stats in
    cache_stats := { cs with misses = cs.misses + 1 }
let reset_cache_stats () =
    cache_stats := { hits = 0; misses = 0 }
let report_cache_stats () = !cache_stats
let clear_memo_table () = THT.clear table
let insert (g:env) (e:term) (res:success (tot_or_ghost & typ)) =
    let entry = {
       he_term = e;
       he_gamma = g.tcenv.gamma;
       he_res = res
    }
    in
    THT.insert e entry table

inline_for_extraction
let return (#a:Type) (x:a) : result a = fun _ -> Success (x, None)

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
      | Success (x, g1) ->
        (match y x ctx0 with
         | Success (y, g2) -> Success (y, and_pre g1 g2)
         | err -> err)
      | Error err -> Error err

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

let fail #a msg : result a = fun ctx -> Error (ctx, msg)

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
      | Error _ -> h () ctx
      | res -> res

inline_for_extraction
let with_context (#a:Type) (msg:string) (t:option context_term) (x:unit -> result a)
  : result a
  = fun ctx ->
     let ctx = { ctx with error_context=((msg,t)::ctx.error_context) } in
     x () ctx

let mk_type (u:universe) = S.mk (Tm_type u) R.dummyRange

let is_type (g:env) (t:term)
  : result universe
  = let aux t =
        match (Subst.compress t).n with
        | Tm_type u ->
          return u

        | _ ->
          fail (BU.format1 "Expected a type; got %s" (show t))
    in
    with_context "is_type" (Some (CtxTerm t)) (fun _ ->
      handle_with
        (aux t)
        (fun _ -> aux (U.unrefine (N.unfold_whnf g.tcenv t))))

let rec is_arrow (g:env) (t:term)
  : result (binder & tot_or_ghost & typ)
  = let rec aux t =
        match (Subst.compress t).n with
        | Tm_arrow {bs=[x]; comp=c} ->
          if U.is_tot_or_gtot_comp c
          then
            let g, x, c = open_comp g x c in
            let eff =
              if U.is_total_comp c
              then E_Total
              else E_Ghost
            in
            return (x, eff, U.comp_result c)
          else (
            let e_tag =
              let Comp ct = c.n in
              if Ident.lid_equals ct.effect_name PC.effect_Pure_lid  ||
                 Ident.lid_equals ct.effect_name PC.effect_Lemma_lid
              then Some E_Total
              else if Ident.lid_equals ct.effect_name PC.effect_Ghost_lid
              then Some E_Ghost
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
              let g, [x], c = arrow_formals_comp g t in
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

        | Tm_arrow {bs=x::xs; comp=c} ->
          let t = S.mk (Tm_arrow {bs=xs; comp=c}) t.pos in
          let g, x, t = open_term g x t in
          return (x, E_Total, t)

        | Tm_refine {b=x} ->
          is_arrow g x.sort

        | Tm_meta {tm=t}
        | Tm_ascribed {tm=t} ->
          aux t

        | _ ->
          fail (BU.format2 "Expected an arrow, got (%s) %s" (tag_of t) (show t))
    in
    with_context "is_arrow" None (fun _ ->
      handle_with
        (aux t)
        (fun _ -> aux (N.unfold_whnf g.tcenv t)))

let check_arg_qual (a:aqual) (b:bqual)
  : result unit
  = match b with
    | Some (Implicit _)
    | Some (Meta _) ->
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
    | Some (Implicit b0), Some (Implicit b1) ->
      //we don't care about the inaccessibility qualifier
      //when comparing bquals
      return ()
    | Some Equality, Some Equality ->
      return ()
    | Some (Meta t1), Some (Meta t2) ->
      if equal_term t1 t2
      then return ()
      else fail "Binder qualifier mismatch"
    | _ ->
      fail "Binder qualifier mismatch"

let check_aqual (a0 a1:aqual)
  : result unit
  = match a0, a1 with
    | None, None -> return ()
    | Some ({aqual_implicit=b0}), Some ({aqual_implicit=b1}) ->
      if b0 = b1
      then return ()
      else fail (BU.format2 "Unequal arg qualifiers: lhs implicit=%s and rhs implicit=%s"
                    (string_of_bool b0) (string_of_bool b1))
    | None, Some { aqual_implicit=false }
    | Some { aqual_implicit=false }, None ->
      return ()
    | _ ->
      fail (BU.format2 "Unequal arg qualifiers: lhs %s and rhs %s"
              (show a0) (show a1))

let check_positivity_qual (rel:relation) (p0 p1:option positivity_qualifier)
  : result unit
  = if FStarC.TypeChecker.Common.check_positivity_qual (SUBTYPING? rel) p0 p1
    then return ()
    else fail "Unequal positivity qualifiers"

let mk_forall_l (us:universes) (xs:binders) (t:term)
  : term
  = FStarC.Compiler.List.fold_right2
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
      | Success (t, g) -> Success (t, close_guard xs us g)
      | err -> err

let with_definition (#a:Type) (x:binder) (u:universe) (t:term) (f:result a)
  : result a
  = fun ctx ->
      match f ctx with
      | Success (a, g) -> Success (a, close_guard_with_definition x u t g)
      | err -> err

let guard (t:typ)
  : result unit
  = fun _ -> Success ((), Some t)

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
      | Success (x, q) -> Success (x, weaken_subtyping_guard p q)
      | err -> err

let weaken_with_guard_formula (p:FStarC.TypeChecker.Common.guard_formula) (g:result 'a)
  = match p with
    | Common.Trivial -> g
    | Common.NonTrivial p -> weaken p g

let push_hypothesis (g:env) (h:term) =
    let bv = S.new_bv (Some h.pos) h in
    let b = S.mk_binder bv in
    fst (fresh_binder g b)

let strengthen (p:term) (g:result 'a)
  = fun ctx ->
      match g ctx with
      | Success (x, q) -> Success (x, strengthen_subtyping_guard p q)
      | err -> err

let no_guard (g:result 'a)
  : result 'a
  = fun ctx ->
      match g ({ ctx with no_guard = true}) with
      | Success (x, None) -> Success (x, None)
      | Success (x, Some g) -> fail (BU.format1 "Unexpected guard: %s" (show g)) ctx
      | err -> err

let equatable g t =
  t |> U.leftmost_head |> Rel.may_relate_with_logical_guard g.tcenv true

let apply_predicate x p = fun e -> Subst.subst [NT(x.binder_bv, e)] p

let curry_arrow (x:binder) (xs:binders) (c:comp) =
  let tail = S.mk (Tm_arrow {bs=xs; comp=c}) R.dummyRange in
  S.mk (Tm_arrow {bs=[x]; comp=S.mk_Total tail}) R.dummyRange

let curry_abs (b0:binder) (b1:binder) (bs:binders) (body:term) (ropt: option residual_comp) =
  let tail = S.mk (Tm_abs {bs=b1::bs; body; rc_opt=ropt}) body.pos in
  S.mk (Tm_abs {bs=[b0]; body=tail; rc_opt=None}) body.pos

let is_gtot_comp c = U.is_tot_or_gtot_comp c && not (U.is_total_comp c)

let rec context_included (g0 g1: list binding) =
  if BU.physical_equality g0 g1 then true else
  match g0, g1 with
  | [], _ -> true

  | b0::g0', b1::g1' ->
     begin
     match b0, b1 with
     | Binding_var x0, Binding_var x1 ->
       if x0.index = x1.index
       then equal_term x0.sort x1.sort
            && context_included g0' g1'
       else context_included g0 g1'

     | Binding_lid _, Binding_lid _
     | Binding_univ _, Binding_univ _ ->
       true

     | _ ->
       false
     end

  | _ -> false

let curry_application hd arg args p =
    let head = S.mk (Tm_app {hd; args=[arg]}) p in
    let t = S.mk (Tm_app {hd=head; args}) p in
    t


let lookup (g:env) (e:term) : result (tot_or_ghost & typ) =
   match THT.lookup e table with
   | None ->
     record_cache_miss ();
     fail "not in cache"
   | Some he ->
     if he.he_gamma `context_included` g.tcenv.gamma
     then (
       record_cache_hit();
       if !dbg then
         BU.print4 "cache hit\n %s |- %s : %s\nmatching env %s\n"
           (show g.tcenv.gamma)
           (show e)
           (show (snd (fst he.he_res)))
           (show he.he_gamma);
       fun _ -> Success he.he_res
     )
     else (
       // record_cache_miss();
       fail "not in cache"
     )

let check_no_escape (bs:binders) t =
    let xs = FStarC.Syntax.Free.names t in
    if BU.for_all (fun b -> not (mem b.binder_bv xs)) bs
    then return ()
    else fail "Name escapes its scope"

let rec map (#a #b:Type) (f:a -> result b) (l:list a) : result (list b) =
  match l with
  | [] -> return []
  | hd::tl ->
    let! hd = f hd in
    let! tl = map f tl in
    return (hd::tl)

let mapi (#a #b:Type) (f:int -> a -> result b) (l:list a) : result (list b) =
  let rec aux i l =
    match l with
    | [] -> return []
    | hd::tl ->
      let! hd = f i hd in
      let! tl = aux (i + 1) tl in
      return (hd::tl)
  in
  aux 0 l

let rec map2 (#a #b #c:Type) (f:a -> b -> result c) (l1:list a) (l2:list b) : result (list c) =
  match l1, l2 with
  | [], [] -> return []
  | hd1::tl1, hd2::tl2 ->
    let! hd = f hd1 hd2 in
    let! tl = map2 f tl1 tl2 in
    return (hd::tl)

let rec fold (#a #b:Type) (f:a -> b -> result a) (x:a) (l:list b) : result a =
  match l with
  | [] -> return x
  | hd::tl ->
    let! x = f x hd in
    fold f x tl

let rec fold2 (#a #b #c:Type) (f:a -> b -> c -> result a) (x:a) (l1:list b) (l2:list c) : result a =
  match l1, l2 with
  | [], [] -> return x
  | hd1::tl1, hd2::tl2 ->
    let! x = f x hd1 hd2 in
    fold2 f x tl1 tl2

let rec iter2 (xs ys:list 'a) (f: 'a -> 'a -> 'b -> result 'b) (b:'b)
  : result 'b
  = match xs, ys with
    | [], [] -> return b
    | x::xs, y::ys ->
      let! b = f x y b in
      iter2 xs ys f b
    | _ -> fail "Lists of differing length"

let is_non_informative g t = Some? (N.non_info_norm g t)

let non_informative g t
  : bool
  = is_non_informative g.tcenv t

let as_comp (g:env) (et: (tot_or_ghost & typ))
  : comp
  = match et with
    | E_Total, t -> S.mk_Total t
    | E_Ghost, t ->
      if non_informative g t
      then S.mk_Total t
      else S.mk_GTotal t

let comp_as_tot_or_ghost_and_type (c:comp)
  : option (tot_or_ghost & typ)
  = if U.is_total_comp c
    then Some (E_Total, U.comp_result c)
    else if U.is_tot_or_gtot_comp c
    then Some (E_Ghost, U.comp_result c)
    else None

let join_eff e0 e1 =
  match e0, e1 with
  | E_Ghost, _
  | _, E_Ghost -> E_Ghost
  | _ -> E_Total

let join_eff_l es = List.Tot.fold_right join_eff es E_Total

let guard_not_allowed
  : result bool
  = fun ctx -> Success (ctx.no_guard, None)

let unfolding_ok
  : result bool
  = fun ctx -> Success (ctx.unfolding_ok, None)

let debug g f =
  if !dbg
  then f ()

instance showable_side = {
    show = (function
            | Left -> "Left"
            | Right -> "Right"
            | Both -> "Both"
            | Neither -> "Neither");
}

let boolean_negation_simp b =
  if Hash.equal_term b U.exp_false_bool
  then None
  else Some (U.mk_boolean_negation b)

let combine_path_and_branch_condition (path_condition:term)
                                      (branch_condition:option term)
                                      (branch_equality:term)
  : term & term
  = let this_path_condition =
        let bc =
            match branch_condition with
            | None -> branch_equality
            | Some bc -> U.mk_conj_l [U.b2t bc; branch_equality]
        in
        U.mk_conj (U.b2t path_condition) bc
    in
    let next_path_condition =
        match branch_condition with
        | None -> U.exp_false_bool
        | Some bc ->
          if Hash.equal_term path_condition U.exp_true_bool
          then U.mk_boolean_negation bc
          else U.mk_and path_condition (U.mk_boolean_negation bc)
    in
    this_path_condition, //:Type
    next_path_condition  //:bool

let maybe_relate_after_unfolding (g:Env.env) t0 t1 : side =
  let dd0 = Env.delta_depth_of_term g t0 in
  let dd1 = Env.delta_depth_of_term g t1 in

  if dd0 = dd1 then
    Both
  else if Common.delta_depth_greater_than dd0 dd1 then
    Left
  else
    Right

(*
     G |- e : t0 <: t1 | p

or   G |- t0 <: t1 | p

 *)
let rec check_relation (g:env) (rel:relation) (t0 t1:typ)
  : result unit
  = let err () =
        match rel with
        | EQUALITY ->
          fail (BU.format2 "not equal terms: %s <> %s"
                           (show t0)
                           (show t1))
        | _ ->
          fail (BU.format2 "%s is not a subtype of %s"
                           (show t0)
                           (show t1))
    in
    let rel_to_string rel =
      match rel with
      | EQUALITY -> "=?="
      | SUBTYPING _ -> "<:?"
    in
    if !dbg
    then BU.print5 "check_relation (%s) %s %s (%s) %s\n"
                   (tag_of t0)
                   (show t0)
                   (rel_to_string rel)
                   (tag_of t1)
                   (show t1);
    let! guard_not_ok = guard_not_allowed in
    let guard_ok = not guard_not_ok in
    let head_matches t0 t1
      : bool
      = let head0 = U.leftmost_head t0 in
        let head1 = U.leftmost_head t1 in
        match (U.un_uinst head0).n, (U.un_uinst head1).n with
        | Tm_fvar fv0, Tm_fvar fv1 -> fv_eq fv0 fv1
        | Tm_name x0, Tm_name x1 -> bv_eq x0 x1
        | Tm_constant c0, Tm_constant c1 -> equal_term head0 head1
        | Tm_type _, Tm_type _
        | Tm_arrow _, Tm_arrow _
        | Tm_match _, Tm_match _ -> true
        | _ -> false
    in
    let which_side_to_unfold t0 t1 =
      maybe_relate_after_unfolding g.tcenv t0 t1 in
    let maybe_unfold_side side t0 t1
      : option (term & term)
      = Profiling.profile (fun _ ->
        match side with
        | Neither -> None
        | Both -> (
          match N.maybe_unfold_head g.tcenv t0,
                N.maybe_unfold_head g.tcenv t1
          with
          | Some t0, Some t1 -> Some (t0, t1)
          | Some t0, None -> Some (t0, t1)
          | None, Some t1 -> Some (t0, t1)
          | _ -> None
        )
        | Left -> (
          match N.maybe_unfold_head g.tcenv t0 with
          | Some t0 -> Some (t0, t1)
          | _ -> None
        )
        | Right -> (
          match N.maybe_unfold_head g.tcenv t1 with
          | Some t1 -> Some (t0, t1)
          | _ -> None
        ))
        None
        "FStarC.TypeChecker.Core.maybe_unfold_side"
    in
    let maybe_unfold t0 t1
      : result (option (term & term))
      = if! unfolding_ok
        then return (maybe_unfold_side (which_side_to_unfold t0 t1) t0 t1)
        else return None
    in
    let emit_guard t0 t1 =
       let! _, t_typ = with_context "checking lhs while emitting guard" None (fun _ -> do_check g t0) in
       let! u = universe_of g t_typ in
       guard (U.mk_eq2 u t_typ t0 t1)
    in
    let fallback t0 t1 =
      if guard_ok
      then if equatable g t0
            || equatable g t1
           then emit_guard t0 t1
           else err ()
      else err ()
    in
    let maybe_unfold_side_and_retry side t0 t1 =
      if! unfolding_ok then
        match maybe_unfold_side side t0 t1 with
        | None -> fallback t0 t1
        | Some (t0, t1) -> check_relation g rel t0 t1
      else
        fallback t0 t1
    in
    let maybe_unfold_and_retry t0 t1 =
      maybe_unfold_side_and_retry (which_side_to_unfold t0 t1) t0 t1
    in
    let beta_iota_reduce t =
        let t = Subst.compress t in
        let t = N.normalize [Env.HNF; Env.Weak; Env.Beta; Env.Iota; Env.Primops] g.tcenv t in
        match t.n with
        | Tm_refine _ ->
          U.flatten_refinement t
        | _ -> t
    in
    let beta_iota_reduce t =
        Profiling.profile
          (fun () -> beta_iota_reduce t)
          None
          "FStarC.TypeChecker.Core.beta_iota_reduce"
    in
    let t0 = Subst.compress (beta_iota_reduce t0) |> U.unlazy_emb in
    let t1 = Subst.compress (beta_iota_reduce t1) |> U.unlazy_emb in
    let check_relation g rel t0 t1 =
      with_context "check_relation" (Some (CtxRel t0 rel t1))
        (fun _ -> check_relation g rel t0 t1)
    in
    if equal_term t0 t1 then return ()
    else
      match t0.n, t1.n with
      | Tm_type u0, Tm_type u1 ->
        // when g.allow_universe_instantiation ->
        // See above remark regarding universe instantiations
        if Rel.teq_nosmt_force g.tcenv t0 t1
        then return ()
        else err ()

      | Tm_meta {tm=t0; meta=Meta_pattern _}, _
      | Tm_meta {tm=t0; meta=Meta_named _}, _
      | Tm_meta {tm=t0; meta=Meta_labeled _}, _
      | Tm_meta {tm=t0; meta=Meta_desugared _}, _
      | Tm_ascribed {tm=t0}, _ ->
        check_relation g rel t0 t1

      | _, Tm_meta {tm=t1; meta=Meta_pattern _}
      | _, Tm_meta {tm=t1; meta=Meta_named _}
      | _, Tm_meta {tm=t1; meta=Meta_labeled _}
      | _, Tm_meta {tm=t1; meta=Meta_desugared _}
      | _, Tm_ascribed {tm=t1} ->
        check_relation g rel t0 t1

      | Tm_uinst (f0, us0), Tm_uinst(f1, us1) ->
        if equal_term f0 f1
        then ( //heads are equal, equate universes
             if Rel.teq_nosmt_force g.tcenv t0 t1
             then return ()
             else err ()
        )
        else maybe_unfold_and_retry t0 t1

      | Tm_fvar _, Tm_fvar _ ->
        maybe_unfold_and_retry t0 t1


      | Tm_refine {b=x0; phi=f0}, Tm_refine {b=x1; phi=f1} ->
        if head_matches x0.sort x1.sort
        then (
          check_relation g EQUALITY x0.sort x1.sort ;!
          let! u = universe_of g x0.sort in
          let g, b, f0 = open_term g (S.mk_binder x0) f0 in
          let f1 = Subst.subst [DB(0, b.binder_bv)] f1 in
            (match! guard_not_allowed with
             | true ->
               with_binders [b] [u]
                 (check_relation g EQUALITY f0 f1)

             | _ ->
               match rel with
               | EQUALITY ->
                 with_binders [b] [u]
                   (handle_with
                      (check_relation g EQUALITY f0 f1)
                      (fun _ -> guard (U.mk_iff f0 f1)))

               | SUBTYPING (Some tm) ->
                 guard (Subst.subst [NT(b.binder_bv, tm)] (U.mk_imp f0 f1))

               | SUBTYPING None ->
                 guard (U.mk_forall u b.binder_bv (U.mk_imp f0 f1)))
        )
        else (
          match! maybe_unfold x0.sort x1.sort with
          | None ->
            if !dbg then
              BU.print2 "Cannot match ref heads %s and %s\n" (show x0.sort) (show x1.sort);
            fallback t0 t1
          | Some (t0, t1) ->
            let lhs = S.mk (Tm_refine {b={x0 with sort = t0}; phi=f0}) t0.pos in
            let rhs = S.mk (Tm_refine {b={x1 with sort = t1}; phi=f1}) t1.pos in
            check_relation g rel (U.flatten_refinement lhs) (U.flatten_refinement rhs)
        )

      | Tm_refine {b=x0; phi=f0}, _ ->
        if head_matches x0.sort t1
        then (
          (* For subtyping, we just check that x0.sort <: t1. But for equality,
          we must show that the refinement on the LHS is constantly true. *)
          if rel = EQUALITY then (
            let! u0 = universe_of g x0.sort in
            let g, b0, f0 = open_term g (S.mk_binder x0) f0 in
            if! guard_not_allowed then
              with_binders [b0] [u0]
                (check_relation g EQUALITY U.t_true f0)
            else (
              with_binders [b0] [u0]
                (handle_with
                    (check_relation g EQUALITY U.t_true f0)
                    (fun _ -> guard f0))
            )
          ) else return ();!
          check_relation g rel x0.sort t1
        )
        else (
          match! maybe_unfold x0.sort t1 with
          | None -> fallback t0 t1
          | Some (t0, t1) ->
            let lhs = S.mk (Tm_refine {b={x0 with sort = t0}; phi=f0}) t0.pos in
            check_relation g rel (U.flatten_refinement lhs) t1
        )

      | _, Tm_refine {b=x1; phi=f1} ->
        if head_matches t0 x1.sort
        then (
          let! u1 = universe_of g x1.sort in
          check_relation g EQUALITY t0 x1.sort ;!
          let g, b1, f1 = open_term g (S.mk_binder x1) f1 in
          if! guard_not_allowed then
            with_binders [b1] [u1]
              (check_relation g EQUALITY U.t_true f1)
          else (
            match rel with
            | EQUALITY ->
              with_binders [b1] [u1]
                (handle_with
                    (check_relation g EQUALITY U.t_true f1)
                    (fun _ -> guard f1))

            | SUBTYPING (Some tm) ->
                 guard (Subst.subst [NT(b1.binder_bv, tm)] f1)

            | SUBTYPING None ->
                 guard (U.mk_forall u1 b1.binder_bv f1)
          )
        )
        else (
          match! maybe_unfold t0 x1.sort with
          | None -> fallback t0 t1
          | Some (t0, t1) ->
            let rhs = S.mk (Tm_refine {b={x1 with sort = t1}; phi=f1}) t1.pos in
            check_relation g rel t0 (U.flatten_refinement rhs)
        )

      | Tm_uinst _, _
      | Tm_fvar _, _
      | Tm_app _, _
      | _, Tm_uinst _
      | _, Tm_fvar _
      | _, Tm_app _ ->
        let head_matches = head_matches t0 t1 in
        let head0, args0 = U.leftmost_head_and_args t0 in
        let head1, args1 = U.leftmost_head_and_args t1 in
        if not (head_matches && List.length args0 = List.length args1)
        then maybe_unfold_and_retry t0 t1
        else (
          (* If we're proving equality, SMT queries are ok, and either head
             is equatable:
              - first try proving equality structurally, without a guard.
              - if that fails, then emit an SMT query
             This is designed to be able to prove things like `v.v1 == u.v1`
             first by trying to unify `v` and `u` and if it fails
             then prove `v.v1 == u.v1` *)
          let compare_head_and_args () =
            handle_with
              (check_relation g EQUALITY head0 head1 ;!
               check_relation_args g EQUALITY args0 args1)
              (fun _ -> maybe_unfold_side_and_retry Both t0 t1)
          in
          if guard_ok &&
            (rel=EQUALITY) && 
            (equatable g t0 || equatable g t1)
          then (
            handle_with 
              (no_guard (compare_head_and_args ()))
              (fun _ -> emit_guard t0 t1)
          )
          else compare_head_and_args ()
        )

      | Tm_abs {bs=b0::b1::bs; body; rc_opt=ropt}, _ ->
        let t0 = curry_abs b0 b1 bs body ropt in
        check_relation g rel t0 t1

      | _, Tm_abs {bs=b0::b1::bs; body; rc_opt=ropt} ->
        let t1 = curry_abs b0 b1 bs body ropt in
        check_relation g rel t0 t1

      | Tm_abs {bs=[b0]; body=body0}, Tm_abs {bs=[b1]; body=body1} ->
        check_relation g EQUALITY b0.binder_bv.sort b1.binder_bv.sort;!
        check_bqual b0.binder_qual b1.binder_qual;!
        check_positivity_qual EQUALITY b0.binder_positivity b1.binder_positivity;!
        let! u = universe_of g b0.binder_bv.sort in
        let g, b0, body0 = open_term g b0 body0 in
        let body1 = Subst.subst [DB(0, b0.binder_bv)] body1 in
        with_binders [b0] [u]
          (check_relation g EQUALITY body0 body1)

      | Tm_arrow {bs=x0::x1::xs; comp=c0}, _ ->
        check_relation g rel (curry_arrow x0 (x1::xs) c0) t1

      | _, Tm_arrow {bs=x0::x1::xs; comp=c1} ->
        check_relation g rel t0 (curry_arrow x0 (x1::xs) c1)

      | Tm_arrow {bs=[x0]; comp=c0}, Tm_arrow {bs=[x1]; comp=c1} ->
        with_context "subtype arrow" None (fun _ ->
          let! _ = check_bqual x0.binder_qual x1.binder_qual in
          check_positivity_qual rel x0.binder_positivity x1.binder_positivity;!
          let! u1 = universe_of g x1.binder_bv.sort in
          let g_x1, x1, c1 = open_comp g x1 c1 in
          let c0 = Subst.subst_comp [DB(0, x1.binder_bv)] c0 in
          with_binders [x1] [u1] (
            let rel_arg =
              match rel with
              | EQUALITY -> EQUALITY
              | _ -> SUBTYPING (Some (S.bv_to_name x1.binder_bv))
            in
            let rel_comp =
              match rel with
              | EQUALITY -> EQUALITY
              | SUBTYPING e ->
                SUBTYPING
                  (if U.is_pure_or_ghost_comp c0
                   then let? e in Some (S.mk_Tm_app e (snd (U.args_of_binders [x1])) R.dummyRange)
                   else None)
            in
            check_relation g rel x1.binder_bv.sort x0.binder_bv.sort ;!
            with_context "check_subcomp" None (fun _ ->
              check_relation_comp g_x1 rel_comp c0 c1
            )
          )
        )

      | Tm_match {scrutinee=e0;brs=brs0}, Tm_match {scrutinee=e1;brs=brs1} ->
        let relate_branch br0 br1 (_:unit)
          : result unit
          = match br0, br1 with
            | (p0, None, body0), (p1, None, body1) ->
              if not (S.eq_pat p0 p1)
              then fail "patterns not equal"
              else begin
                let g', (p0, _, body0), (p1, _, body1) = open_branches_eq_pat g (p0, None, body0) (p1, None, body1) in
                match PatternUtils.raw_pat_as_exp g.tcenv p0 with
                | Some (_, bvs0) ->
                  let bs0 = List.map S.mk_binder bvs0 in
                  // We need universes for the binders
                  let! us = check_binders g bs0 in
                  with_context "relate_branch" None (fun _ -> with_binders bs0 us (check_relation g' rel body0 body1))
             | _ -> fail "raw_pat_as_exp failed in check_equality match rule"
             end
            | _ -> fail "Core does not support branches with when"
        in
        handle_with
          (check_relation g EQUALITY e0 e1 ;!
           iter2 brs0 brs1 relate_branch ())
          (fun _ -> fallback t0 t1)

      | _ -> fallback t0 t1

and check_relation_args (g:env) rel (a0 a1:args)
  : result unit
  = if List.length a0 = List.length a1
    then iter2 a0 a1
         (fun (t0, q0) (t1, q1) _ ->
            check_aqual q0 q1;!
            check_relation g rel t0 t1)
         ()
    else fail "Unequal number of arguments"

and check_relation_comp (g:env) rel (c0 c1:comp)
  : result unit
  = let destruct_comp c =
        if U.is_total_comp c
        then Some (E_Total, U.comp_result c)
        else if U.is_tot_or_gtot_comp c
        then Some (E_Ghost, U.comp_result c)
        else None
    in
    match destruct_comp c0, destruct_comp c1 with
    | None, _
    | _, None ->
      if TEQ.eq_comp g.tcenv c0 c1 = TEQ.Equal
      then return ()
      else (
        let ct_eq res0 args0 res1 args1 =
          check_relation g EQUALITY res0 res1 ;!
          check_relation_args g EQUALITY args0 args1
        in
        let eff0, res0, args0 = U.comp_eff_name_res_and_args c0 in
        let eff1, res1, args1 = U.comp_eff_name_res_and_args c1 in
        if I.lid_equals eff0 eff1
        then ct_eq res0 args0 res1 args1
        else (
          let ct0 = Env.unfold_effect_abbrev g.tcenv c0 in
          let ct1 = Env.unfold_effect_abbrev g.tcenv c1 in
          if I.lid_equals ct0.effect_name ct1.effect_name
          then ct_eq ct0.result_typ ct0.effect_args ct1.result_typ ct1.effect_args
          else fail (BU.format2 "Subcomp failed: Unequal computation types %s and %s"
                            (Ident.string_of_lid ct0.effect_name)
                            (Ident.string_of_lid ct1.effect_name))
        )
      )

    | Some (E_Total, t0), Some (_, t1) // why is this right? what about EQUALITY?
    | Some (E_Ghost, t0), Some (E_Ghost, t1) ->
      check_relation g rel t0 t1

    | Some (E_Ghost, t0), Some (E_Total, t1) ->
      if non_informative g t1
      then check_relation g rel t0 t1
      else fail "Expected a Total computation, but got Ghost"


and check_subtype (g:env) (e:option term) (t0 t1:typ)
  = fun ctx ->
    Profiling.profile
      (fun () ->
        let rel = SUBTYPING e in
        with_context (if ctx.no_guard then "check_subtype(no_guard)" else "check_subtype")
                     (Some (CtxRel t0 rel t1))
          (fun _ -> check_relation g rel t0 t1)
          ctx)
      None
      "FStarC.TypeChecker.Core.check_subtype"

and memo_check (g:env) (e:term)
  : result (tot_or_ghost & typ)
  = let check_then_memo g e ctx =
      let r = do_check_and_promote g e ctx in
      match r with
      | Success (res, None) ->
        insert g e (res, None);
        r

      | Success (res, Some guard) ->
        (match g.guard_handler with
         | None -> insert g e (res, Some guard); r
         | Some gh ->
           if gh g.tcenv guard
           then let r = (res, None) in
                insert g e r; Success r
           else fail "guard handler failed" ctx)

      | _ -> r
    in
    fun ctx ->
      if not g.should_read_cache
      then check_then_memo g e ctx
      else (
        match lookup g e ctx with
        | Error _ -> //cache miss; check and insert
          check_then_memo g e ctx

        | Success (et, None) -> //cache hit with no guard; great, just return
          Success (et, None)

        | Success (et, Some pre) -> //cache hit with a guard
          match g.guard_handler with
          | None -> Success (et, Some pre) //if there's no guard handler, then just return
          | Some _ ->
            //otherwise check then memo, since this can
            //repopulate the cache with a "better" entry that has no guard
            //But, don't read the cache again, since many subsequent lookups
            //are likely to be hits with a guard again
            check_then_memo { g with should_read_cache = false } e ctx
      )

and check (msg:string) (g:env) (e:term)
  : result (tot_or_ghost & typ)
  = with_context msg (Some (CtxTerm e)) (fun _ -> memo_check g e)

and do_check_and_promote (g:env) (e:term)
  : result (tot_or_ghost & typ)
  = let! (eff, t) = do_check g e in
    let eff =
      match eff with
      | E_Total -> E_Total
      | E_Ghost -> if non_informative g t then E_Total else E_Ghost in
    return (eff, t)

(*  G |- e : Tot t | pre *)
and do_check (g:env) (e:term)
  : result (tot_or_ghost & typ) =
  let e = Subst.compress e in
  match e.n with
  | Tm_lazy ({lkind=Lazy_embedding _}) ->
    do_check g (U.unlazy e)

  | Tm_lazy i ->
    return (E_Total, i.ltyp)

  | Tm_meta {tm=t} ->
    memo_check g t

  | Tm_uvar (uv, s) ->
    return (E_Total, Subst.subst' s (U.ctx_uvar_typ uv))

  | Tm_name x ->
    begin
    match Env.try_lookup_bv g.tcenv x with
    | None ->
      fail (BU.format1 "Variable not found: %s" (show x))
    | Some (t, _) ->
      return (E_Total, t)
    end

  | Tm_fvar f ->
    begin
    match Env.try_lookup_lid g.tcenv f.fv_name.v with
    | Some (([], t), _) ->
      return (E_Total, t)

    | _ -> //no implicit universe instantiation allowed
      fail "Missing universes instantiation"
    end

  | Tm_uinst ({n=Tm_fvar f}, us) ->
    begin
    match Env.try_lookup_and_inst_lid g.tcenv us f.fv_name.v with
    | None ->
      fail (BU.format1 "Top-level name not found: %s" (Ident.string_of_lid f.fv_name.v))

    | Some (t, _) ->
      return (E_Total, t)
    end

  | Tm_constant c ->
    begin
    let open FStarC.Const in
    match c with
    | Const_range_of
    | Const_set_range_of
    | Const_reify _
    | Const_reflect _ ->
      fail "Unhandled constant"

    | _ ->
      let t = FStarC.TypeChecker.TcTerm.tc_constant g.tcenv e.pos c in
      return (E_Total, t)
    end

  | Tm_type u ->
    return (E_Total, mk_type (U_succ u))

  | Tm_refine {b=x; phi} ->
    let! _, t = check "refinement head" g x.sort in
    let! u = is_type g t in
    let g', x, phi = open_term g (S.mk_binder x) phi in
    with_binders [x] [u] (
      let! _, t' = check "refinement formula" g' phi in
      is_type g' t';!
      return (E_Total, t)
    )

  | Tm_abs {bs=xs; body} ->
    let g', xs, body = open_term_binders g xs body in
    let! us = with_context "abs binders" None (fun _ -> check_binders g xs) in
    with_binders xs us (
      let! t = check "abs body" g' body in
      return (E_Total, U.arrow xs (as_comp g t))
    )

  | Tm_arrow {bs=xs; comp=c} ->
    let g', xs, c = open_comp_binders g xs c in
    let! us = with_context "arrow binders" None (fun _ -> check_binders g xs) in
    with_binders xs us (
      let! u = with_context "arrow comp" None (fun _ -> check_comp g' c) in
      return (E_Total, mk_type (S.U_max (u::us)))
    )

  | Tm_app _ -> (
    let rec check_app_arg (eff_hd, t_hd) (arg, arg_qual) =
      let! x, eff_arr, t' = is_arrow g t_hd in
      let! eff_arg, t_arg = check "app arg" g arg in
      with_context "app subtyping" None (fun _ -> check_subtype g (Some arg) t_arg x.binder_bv.sort) ;!
      with_context "app arg qual" None (fun _ -> check_arg_qual arg_qual x.binder_qual) ;!
      return (join_eff eff_hd (join_eff eff_arr eff_arg), Subst.subst [NT(x.binder_bv, arg)] t')
    in
    let check_app hd args =
       let! eff_hd, t = check "app head" g hd in
       fold check_app_arg (eff_hd, t) args
    in
    let hd, args = U.head_and_args_full e in
    match args with
    | [(t1, None); (t2, None)] when TcUtil.short_circuit_head hd ->
      let! eff_hd, t_hd = check "app head" g hd in
      let! x, eff_arr1, s1 = is_arrow g t_hd in
      let! eff_arg1, t_t1 = check "app arg" g t1 in
      with_context "operator arg1" None (fun _ -> check_subtype g (Some t1) t_t1 x.binder_bv.sort) ;!
      let s1 = Subst.subst [NT(x.binder_bv, t1)] s1 in
      let! y, eff_arr2, s2 = is_arrow g s1 in
      let guard_formula = TcUtil.short_circuit hd [(t1, None)] in
      let g' =
        match guard_formula with
        | Common.Trivial -> g
        | Common.NonTrivial gf -> push_hypothesis g gf
      in
      let! eff_arg2, t_t2 = weaken_with_guard_formula guard_formula (check "app arg" g' t2) in
      with_context "operator arg2" None (fun _ -> check_subtype g' (Some t2) t_t2 y.binder_bv.sort) ;!
      return (join_eff_l [eff_hd; eff_arr1; eff_arr2; eff_arg1; eff_arg2],
             Subst.subst [NT(y.binder_bv, t2)] s2)
    | _ -> check_app hd args
  )

  | Tm_ascribed {tm=e; asc=(Inl t, _, eq)} ->
    let! eff, te = check "ascription head" g e in
    let! _, t' = check "ascription type" g t in
    is_type g t';!
    with_context "ascription subtyping" None (fun _ -> check_subtype g (Some e) te t);!
    return (eff, t)

  | Tm_ascribed {tm=e; asc=(Inr c, _, _)} ->
    if U.is_tot_or_gtot_comp c
    then (
      let! eff, te = check "ascription head" g e in
      let! _ = with_context "ascription comp" None (fun _ -> check_comp g c) in
      let c_e = as_comp g (eff, te) in
      with_context "ascription subtyping (comp)" None (fun _ -> check_relation_comp g (SUBTYPING (Some e)) c_e c);!
      let Some (eff, t) = comp_as_tot_or_ghost_and_type c in
      return (eff, t)
    )
    else fail (BU.format1 "Effect ascriptions are not fully handled yet: %s" (show c))

  | Tm_let {lbs=(false, [lb]); body} ->
    let Inl x = lb.lbname in
    let g', x, body = open_term g (S.mk_binder x) body in
    if U.is_pure_or_ghost_effect lb.lbeff
    then (
      let! eff_def, tdef = check "let definition" g lb.lbdef in
      let! _, ttyp = check "let type" g lb.lbtyp in
      let! u = is_type g ttyp in
      with_context "let subtyping" None (fun _ -> check_subtype g (Some lb.lbdef) tdef lb.lbtyp) ;!
      with_definition x u lb.lbdef (
        let! eff_body, t = check "let body" g' body in
        check_no_escape [x] t;!
        return (join_eff eff_def eff_body, t)
      )
    )
    else (
      fail (format1 "Let binding is effectful (lbeff = %s)" (show lb.lbeff))
    )

  | Tm_match {scrutinee=sc; ret_opt=None; brs=branches; rc_opt} ->
    let! eff_sc, t_sc = check "scrutinee" g sc in
    let! u_sc = with_context "universe_of" (Some (CtxTerm t_sc)) (fun _ -> universe_of g t_sc) in
    let rec check_branches path_condition
                           branch_typ_opt
                           branches
      : result (tot_or_ghost & typ)
      = match branches with
        | [] ->
          (match branch_typ_opt with
           | None ->
             fail "could not compute a type for the match"

           | Some et ->
             match boolean_negation_simp path_condition with
             | None ->
               return et

             | Some g ->
               guard (U.b2t g) ;!
               return et)

        | (p, None, b) :: rest ->
          let _, (p, _, b) = open_branch g (p, None, b) in
          let! (bs, us) = with_context "check_pat" None (fun _ -> check_pat g p t_sc) in
          let! branch_condition = pattern_branch_condition g sc p in
          let pat_sc_eq =
            U.mk_eq2 u_sc t_sc sc
            (PatternUtils.raw_pat_as_exp g.tcenv p |> must |> fst) in
          let this_path_condition, next_path_condition =
              combine_path_and_branch_condition path_condition branch_condition pat_sc_eq
          in
          let g' = push_binders g bs in
          let g' = push_hypothesis g' this_path_condition in
          let! eff_br, tbr =
            with_binders bs us
              (weaken
                 this_path_condition
                 (let! eff_br, tbr = with_context "branch" (Some (CtxTerm b)) (fun _ -> check "branch" g' b) in
                  match branch_typ_opt with
                  | None ->
                    check_no_escape bs tbr;!
                    return (eff_br, tbr)

                  | Some (acc_eff, expect_tbr) ->
                    with_context "check_branch_subtype" (Some (CtxRel tbr (SUBTYPING (Some b)) expect_tbr))
                      (fun _ -> check_subtype g' (Some b) tbr expect_tbr) ;!
                    return (join_eff eff_br acc_eff, expect_tbr))) in
          match p.v with
          | Pat_var _ ->
            //trivially exhaustive
            (match rest with
             | _ :: _ -> fail "Redundant branches after wildcard"
             | _ -> return (eff_br, tbr))

          | _ ->
            check_branches next_path_condition (Some (eff_br, tbr)) rest
    in

    let! branch_typ_opt =
        match rc_opt with
        | Some ({ residual_typ = Some t }) ->
          with_context "residual type" (Some (CtxTerm t)) (fun _ -> universe_of g t) ;!
          return (Some (E_Total, t))

        | _ ->
          return None
    in
    let! eff_br, t_br =
      let ctx =
        match branch_typ_opt with
        | None -> None
        | Some (_, t) -> Some (CtxTerm t)
      in
      with_context "check_branches" ctx
        (fun _ -> check_branches U.exp_true_bool branch_typ_opt branches)
    in
    return (join_eff eff_sc eff_br, t_br)

  | Tm_match {scrutinee=sc; ret_opt=Some (as_x, (Inl returns_ty, None, eq)); brs=branches; rc_opt} ->
    let! eff_sc, t_sc = check "scrutinee" g sc in
    let! u_sc = with_context "universe_of" (Some (CtxTerm t_sc)) (fun _ -> universe_of g t_sc) in
    let as_x = {as_x with binder_bv = { as_x.binder_bv with sort = t_sc } } in
    let g_as_x, as_x, returns_ty = open_term g as_x returns_ty in
    let! _eff_t, returns_ty_t =
      with_binders [as_x] [u_sc] (check "return type" g_as_x returns_ty) in
    let! _u_ty = is_type g_as_x returns_ty_t in
    let rec check_branches (path_condition: S.term)
                           (branches: list S.branch)
                           (acc_eff: tot_or_ghost)
      : result tot_or_ghost
      = match branches with
        | [] ->
          (match boolean_negation_simp path_condition with
           | None ->
             return acc_eff

           | Some g ->
             guard (U.b2t g) ;!
             return acc_eff)

        | (p, None, b) :: rest ->
          let _, (p, _, b) = open_branch g (p, None, b) in
          let! (bs, us) = with_context "check_pat" None (fun _ -> check_pat g p t_sc) in
          let! branch_condition = pattern_branch_condition g sc p in
          let pat_sc_eq =
            U.mk_eq2 u_sc t_sc sc
            (PatternUtils.raw_pat_as_exp g.tcenv p |> must |> fst) in
          let this_path_condition, next_path_condition =
              combine_path_and_branch_condition path_condition branch_condition pat_sc_eq
          in
          let g' = push_binders g bs in
          let g' = push_hypothesis g' this_path_condition in
          let! eff_br, tbr =
            with_binders bs us
              (weaken
                 this_path_condition
                 (let! eff_br, tbr = check "branch" g' b in
                  let expect_tbr = Subst.subst [NT(as_x.binder_bv, sc)] returns_ty in
                  let rel =
                    if eq
                    then EQUALITY
                    else SUBTYPING (Some b)
                  in
                  with_context "branch check relation" None (fun _ -> check_relation g' rel tbr expect_tbr);!
                  return (join_eff eff_br acc_eff, expect_tbr))) in
          match p.v with
          | Pat_var _ ->
            //trivially exhaustive
            (match rest with
             | _ :: _ -> fail "Redundant branches after wildcard"
             | _ -> return eff_br)

          | _ ->
            check_branches next_path_condition rest eff_br in

    let! eff = check_branches U.exp_true_bool branches E_Total in
    let ty = Subst.subst [NT(as_x.binder_bv, sc)] returns_ty in
    return (eff, ty)

  | Tm_match _ ->
    fail "Match with effect returns ascription, or tactic handler"

  | _ ->
    fail (BU.format1 "Unexpected term: %s" (tag_of e))

and check_binders (g_initial:env) (xs:binders)
  : result (list universe)
  = let rec aux g xs =
      match xs with
      | [] ->
        return []

      | x ::xs ->
        let! _, t = check "binder sort" g x.binder_bv.sort in
        let! u = is_type g t in
        with_binders [x] [u] (
          let! us = aux (push_binder g x) xs in
          return (u::us)
        )
    in
    aux g_initial xs

//
// May be called with an effectful comp type, e.g. from within an arrow
// Caller should enforce Tot/GTot if needed
//
and check_comp (g:env) (c:comp)
  : result universe
  = match c.n with
    | Total t
    | GTotal t ->
      let! _, t = check "(G)Tot comp result" g (U.comp_result c) in
      is_type g t
    | Comp ct ->
      if List.length ct.comp_univs <> 1
      then fail "Unexpected/missing universe instantitation in comp"
      else let u = List.hd ct.comp_univs in
           let effect_app_tm =
             let head = S.mk_Tm_uinst (S.fvar ct.effect_name None) [u] in
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

and check_pat (g:env) (p:pat) (t_sc:typ) : result (binders & universes) =
  let unrefine_tsc t_sc =
    t_sc |> N.normalize_refinement N.whnf_steps g.tcenv
         |> U.unrefine in

  match p.v with
  | Pat_constant c ->
    let e =
      match c with
      | FStarC.Const.Const_int(repr, Some sw) ->
        FStarC.ToSyntax.ToSyntax.desugar_machine_integer g.tcenv.dsenv repr sw p.p
      | _ ->
        mk (Tm_constant c) p.p in
    let! _, t_const = check "pat_const" g e in
    let! _ = with_context "check_pat constant" None (fun () -> check_subtype g (Some e) t_const (unrefine_tsc t_sc)) in
    return ([], [])

  | Pat_var bv ->
    let b = S.mk_binder {bv with sort=t_sc} in
    let! [u] = with_context "check_pat_binder" None (fun _ -> check_binders g [b]) in
    return ([b], [u])

  | Pat_cons (fv, usopt, pats) ->
    let us = if is_none usopt then [] else usopt |> must in

    let formals, t_pat =
      Env.lookup_and_inst_datacon g.tcenv us (S.lid_of_fv fv)
      |> U.arrow_formals in

    let dot_pats, rest_pats =
      let pats = pats |> List.map fst in
      pats |> BU.prefix_until (fun p -> match p.v with
                                    | Pat_dot_term _ -> false
                                    | _ -> true)
           |> BU.map_option (fun (dot_pats, pat, rest_pats) ->
                            dot_pats, (pat::rest_pats))
           |> BU.dflt (pats, []) in

    let dot_formals, rest_formals = List.splitAt (List.length dot_pats) formals in

    let! ss = fold2 (fun ss {binder_bv=f} p ->
      let expected_t = Subst.subst ss f.sort in
      let! pat_dot_t =
        match p.v with
        | Pat_dot_term (Some t) -> return t
        | _ -> fail "check_pat in core has unset dot pattern" in

      let! _, p_t = check "pat dot term" g pat_dot_t in
      let!_ = with_context "check_pat cons" None (fun _ -> check_subtype g (Some pat_dot_t) p_t expected_t) in

      return (ss@[NT (f, pat_dot_t)])) [] dot_formals dot_pats in

    let! _, ss, bs, us = fold2 (fun (g, ss, bs, us) {binder_bv=f} p ->
      let expected_t = Subst.subst ss f.sort in
      let! (bs_p, us_p) = with_binders bs us (check_pat g p expected_t) in
      let p_e = PatternUtils.raw_pat_as_exp g.tcenv p |> must |> fst in
      return (push_binders g bs_p,
              ss@[NT (f, p_e)],
              bs@bs_p,
              us@us_p)) (g, ss, [], []) rest_formals rest_pats in

    let t_pat = Subst.subst ss t_pat in

    let!_ = no_guard (check_scrutinee_pattern_type_compatible g (unrefine_tsc t_sc) t_pat) in

    return (bs, us)

  | _ -> fail "check_pat called with a dot pattern"

and check_scrutinee_pattern_type_compatible (g:env) (t_sc t_pat:typ)
  : result precondition
  = let open Env in
    let err (s:string) =
      fail (BU.format3 "Scrutinee type %s and Pattern type %s are not compatible because %s"
              (show t_sc)
              (show t_pat)
              s) in

    let head_sc, args_sc = U.head_and_args t_sc in
    let head_pat, args_pat = U.head_and_args t_pat in

    let! (t_fv:fv) =
      match (Subst.compress head_sc).n, (Subst.compress head_pat).n with
      | Tm_fvar (fv_head), Tm_fvar (fv_pat)
        when Ident.lid_equals (lid_of_fv fv_head) (lid_of_fv fv_pat) -> return fv_head
      | Tm_uinst ({n=Tm_fvar (fv_head)}, us_head), Tm_uinst ({n=Tm_fvar (fv_pat)}, us_pat)
        when Ident.lid_equals (lid_of_fv fv_head) (lid_of_fv fv_pat) ->
        if Rel.teq_nosmt_force g.tcenv head_sc head_pat
        then return fv_head
        else err "Incompatible universe instantiations"
      | _, _ -> err (BU.format2 "Head constructors(%s and %s) not fvar"
                      (tag_of head_sc)
                      (tag_of head_pat)) in

    (if Env.is_type_constructor g.tcenv (lid_of_fv t_fv)
     then return t_fv
     else err (BU.format1 "%s is not a type constructor" (show t_fv)));!

    (if List.length args_sc = List.length args_pat then return t_fv
     else err (BU.format2 "Number of arguments don't match (%s and %s)"
                          (string_of_int (List.length args_sc))
                          (string_of_int (List.length args_pat))));!

   let params_sc, params_pat =
     match Env.num_inductive_ty_params g.tcenv (S.lid_of_fv t_fv) with
     | None -> args_sc, args_pat
     | Some n -> fst (BU.first_N n args_sc), fst (BU.first_N n args_pat) in

  iter2 params_sc params_pat (fun (t_sc, _) (t_pat, _) _ ->
     check_relation g EQUALITY t_sc t_pat) () ;!

   // TODO: return equality of indices for the caller to weaken the guard with?

   return None

and pattern_branch_condition (g:env)
                             (scrutinee:term)
                             (pat:pat)
  : result (option term)
  = match pat.v with
    | Pat_var _ ->
      return None
    | Pat_constant c ->
      let const_exp =
        match PatternUtils.raw_pat_as_exp g.tcenv pat with
        | None -> failwith "Impossible"
        | Some (e, _) -> e
      in
      let! _, t_const = check "constant pattern" g const_exp in
      return (Some (U.mk_decidable_eq t_const scrutinee const_exp))

    | Pat_cons(fv, us_opt, sub_pats) ->
      let wild_pat pos = S.withinfo (Pat_var (S.new_bv None S.tun)) pos in
      let mk_head_discriminator () =
        let pat = S.withinfo (Pat_cons(fv, us_opt, List.map (fun (s, b) -> wild_pat s.p, b) sub_pats)) pat.p in
        let branch1 = (pat, None, U.exp_true_bool) in
        let branch2 = (S.withinfo (Pat_var (S.new_bv None S.tun)) pat.p, None, U.exp_false_bool) in
        S.mk (Tm_match {scrutinee; ret_opt=None; brs=[branch1; branch2]; rc_opt=None}) scrutinee.pos
      in
      let mk_ith_projector i =
        let ith_pat_var, ith_pat =
            let bv = S.new_bv None S.tun in
            bv, S.withinfo (Pat_var bv) scrutinee.pos
        in
        let sub_pats = List.mapi (fun j (s,b) -> if i <> j then wild_pat s.p,b else ith_pat,b) sub_pats in
        let pat = S.withinfo (Pat_cons(fv, us_opt, sub_pats)) pat.p in
        let branch = S.bv_to_name ith_pat_var in
        let eqn = Subst.close_branch (pat, None, branch) in
        S.mk (Tm_match {scrutinee; ret_opt=None; brs=[eqn]; rc_opt=None}) scrutinee.pos
      in
      let discrimination =
        let is_induc, datacons = Env.datacons_of_typ g.tcenv (Env.typ_of_datacon g.tcenv fv.fv_name.v) in
        (* Why the `not is_induc`? We may be checking an exception pattern. See issue #1535. *)
        if not is_induc || List.length datacons > 1
        then let discriminator = U.mk_discriminator fv.fv_name.v in
             match Env.try_lookup_lid g.tcenv discriminator with
             | None ->
               // We don't use the discriminator if we are typechecking it
               None
             | _ ->
               Some (mk_head_discriminator())
        else None //single constructor inductives do not need a discriminator
      in
      let! sub_term_guards =
          mapi
          (fun i (pi, _) ->
            match pi.v with
            | Pat_dot_term _
            | Pat_var _ ->
              return None
            | _ ->
              let scrutinee_sub_term = mk_ith_projector i in
              pattern_branch_condition g (mk_ith_projector i) pi)
          sub_pats
      in
      let guards = List.collect (function None -> [] | Some t -> [t]) (discrimination :: sub_term_guards) in
      match guards with
      | [] -> return None
      | guards -> return (Some (U.mk_and_l guards))

let initial_env g gh =
  let max_index =
      List.fold_left
        (fun index b ->
          match b with
          | Binding_var x ->
            if x.index > index
            then x.index
            else index
          | _ -> index)
        0 g.Env.gamma
  in
  { tcenv = g;
    allow_universe_instantiation = false;
    max_binder_index = max_index;
    guard_handler = gh;
    should_read_cache = true }

//
// In case the expected type and effect are set,
//   they are returned as is
//
let check_term_top g e topt (must_tot:bool) (gh:option guard_handler_t)
  : result (tot_or_ghost & typ)
  = let g = initial_env g gh in
    let! eff_te = check "top" g e in
    match topt with
    | None ->
      // check expected effect
      if must_tot
      then let eff, t = eff_te in 
           if eff = E_Ghost &&
              not (non_informative g t)
           then fail "expected total effect, found ghost"
           else return (E_Total, t)
      else return eff_te
    | Some t ->
      let target_comp, eff =
        if must_tot || fst eff_te = E_Total
        then S.mk_Total t, E_Total
        else S.mk_GTotal t, E_Ghost
      in
      with_context "top-level subtyping" None (fun _ ->
        check_relation_comp
          ({ g with allow_universe_instantiation = true})
          (SUBTYPING (Some e))
          (as_comp g eff_te)
          target_comp) ;!
      return (eff, t)

let simplify_steps =
    [Env.Beta;
     Env.UnfoldUntil delta_constant;
     Env.UnfoldQual ["unfold"];
     Env.UnfoldOnly [PC.pure_wp_monotonic_lid; PC.pure_wp_monotonic0_lid];
     Env.Simplify;
     Env.Primops;
     Env.NoFullNorm]


let check_term_top_gh g e topt (must_tot:bool) (gh:option guard_handler_t)
  : __result ((tot_or_ghost & S.typ) & precondition)
  = if !dbg_Eq
    then BU.print1 "(%s) Entering core ... \n"
                   (show (get_goal_ctr()));

    if !dbg || !dbg_Top
    then BU.print3 "(%s) Entering core with %s <: %s\n"
                   (show (get_goal_ctr())) (show e) (show topt);
    THT.reset_counters table;
    reset_cache_stats();
    let ctx = { unfolding_ok = true; no_guard = false; error_context = [("Top", None)] } in
    let res =
      Profiling.profile
        (fun () ->
          match check_term_top g e topt must_tot gh ctx with
          | Success (et, g) -> Success (et, g)
          | Error err -> Error err)
        None
        "FStarC.TypeChecker.Core.check_term_top"
    in
    (
    let res =
      match res with
      | Success (et, Some guard0) ->
        // Options.push();
        // Options.set_option "debug" (Options.List [Options.String "Unfolding"]);
        let guard = N.normalize simplify_steps g guard0 in
        // Options.pop();
        if !dbg || !dbg_Top || !dbg_Exit
        then begin
          BU.print3 "(%s) Exiting core: Simplified guard from {{%s}} to {{%s}}\n"
            (BU.string_of_int (get_goal_ctr()))
            (show guard0)
            (show guard);
          let guard_names = Syntax.Free.names guard |> elems in
          match List.tryFind (fun bv -> List.for_all (fun binding_env ->
            match binding_env with
            | Binding_var bv_env -> not (S.bv_eq bv_env bv)
            | _ -> true) g.gamma) guard_names with
          | Some bv ->
            BU.print1 "WARNING: %s is free in the core generated guard\n" (show (S.bv_to_name bv))
          | _ -> ()
        end;
        Success (et, Some guard)

      | Success _ ->
        if !dbg || !dbg_Top
        then BU.print1 "(%s) Exiting core (ok)\n"
                    (BU.string_of_int (get_goal_ctr()));
        res

      | Error _ ->
        if !dbg || !dbg_Top
        then BU.print1 "(%s) Exiting core (failed)\n"
                       (BU.string_of_int (get_goal_ctr()));
        res
    in
    if !dbg_Eq
    then (
      THT.print_stats table;
      let cs = report_cache_stats() in
      BU.print2 "Cache_stats { hits = %s; misses = %s }\n"
                     (BU.string_of_int cs.hits)
                     (BU.string_of_int cs.misses)
    );
    res
    )

let check_term g e t must_tot =
  match check_term_top_gh g e (Some t) must_tot None with
  | Success (_, g) -> Inl g
  | Error err -> Inr err

let check_term_at_type g e t =
  let must_tot = false in
  match check_term_top_gh g e (Some t) must_tot None with
  | Success ((eff, _), g) -> Inl (eff, g)
  | Error err -> Inr err

let compute_term_type_handle_guards g e gh =
  let e = FStarC.Syntax.Compress.deep_compress true true e in
  let must_tot = false in
  match check_term_top_gh g e None must_tot (Some gh) with
  | Success (r, None) -> Inl r
  | Success (_, Some _) -> failwith "Impossible: All guards should have been handled already"
  | Error err -> Inr err

let open_binders_in_term (env:Env.env) (bs:binders) (t:term) =
  let g = initial_env env None in
  let g', bs, t = open_term_binders g bs t in
  g'.tcenv, bs, t

let open_binders_in_comp (env:Env.env) (bs:binders) (c:comp) =
  let g = initial_env env None in
  let g', bs, c = open_comp_binders g bs c in
  g'.tcenv, bs, c

let check_term_equality guard_ok unfolding_ok g t0 t1
  = let g = initial_env g None in
    if !dbg_Top then
       BU.print4 "Entering check_term_equality with %s and %s (guard_ok=%s; unfolding_ok=%s) {\n"
         (show t0) (show t1) (show guard_ok) (show unfolding_ok);
    let ctx = { unfolding_ok = unfolding_ok; no_guard = not guard_ok; error_context = [("Eq", None)] } in
    let r = check_relation g EQUALITY t0 t1 ctx in
    if !dbg_Top then
       BU.print3 "} Exiting check_term_equality (%s, %s). Result = %s.\n" (show t0) (show t1) (show r);
    let r =
      match r with
      | Success (_, g) -> Inl g
      | Error err -> Inr err
    in
    r

let check_term_subtyping guard_ok unfolding_ok g t0 t1
  = let g = initial_env g None in
    let ctx = { unfolding_ok = unfolding_ok; no_guard = not guard_ok; error_context = [("Subtyping", None)] } in
    match check_relation g (SUBTYPING None) t0 t1 ctx with
    | Success (_, g) -> Inl g
    | Error err -> Inr err
