module FStar.TypeChecker.Core
open FStar.Compiler
open FStar.Compiler.Util
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

type env = {
   tcenv : Env.env;
   allow_universe_instantiation : bool
}

let push_binders g bs = { g with tcenv = Env.push_binders g.tcenv bs }

let precondition = option typ

let success a = a & precondition

let context = list (string & option term)

let error = context & string

let result a = context -> either (success a) error

type hash_entry = {
   he_term:term;
   he_gamma:list binding;
   he_res:success typ;
}

type tc_table = FStar.Hash.hashtable term hash_entry
let table : tc_table = FStar.Hash.create FStar.Syntax.Hash.equal_term
let clear_memo_table () = FStar.Hash.clear table
let insert (g:env) (e:term) (res:success typ) =
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
let bind (#a:Type) (#b:Type) (x:result a) (y:a -> result b)
  : result b
  = fun ctx0 ->
      match x ctx0 with
      | Inl (x, g1) ->
        (match y x ctx0 with
         | Inl (y, g2) -> Inl (y, and_pre g1 g2)
         | err -> err)
      | Inr err -> Inr err

let fail #a msg : result a = fun ctx -> Inr (ctx, msg)

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
  = fun ctx -> x () ((msg,t)::ctx)

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
  
let is_tot_arrow (g:env) (t:term)
  : result (binder & typ)
  = let aux t =
        match (SS.compress t).n with
        | Tm_arrow ([x], c) ->
          if U.is_total_comp c
          then 
            let [x], c = SS.open_comp [x] c in
            return (x, U.comp_result c)
          else fail "Expected total arrow"
          
        | Tm_arrow (x::xs, c) ->
          let t = S.mk (Tm_arrow(xs, c)) t.pos in
          let [x], t = SS.open_term [x] t in
          return (x, t)

        | _ ->
          fail "Expected an arrow"
    in
    with_context "is_tot_arrow" None (fun _ -> 
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
  = Some (BU.dflt p (BU.map_opt g (fun q -> U.mk_and p q)))

let weaken (p:term) (g:result 'a)
  = fun ctx ->
      match g ctx with
      | Inl (x, q) -> Inl (x, weaken_subtyping_guard p q)
      | err -> err

let strengthen (p:term) (g:result 'a)
  = fun ctx -> 
      match g ctx with
      | Inl (x, q) -> Inl (x, strengthen_subtyping_guard p q)
      | err -> err

let no_guard (g:result 'a)
  : result 'a
  = fun ctx ->
      match g ctx with
      | Inl (x, None) -> Inl (x, None)
      | Inl _ -> fail "Unexpected guard" ctx
      | err -> err
      
let equatable t0 t1 =
  match (SS.compress t0).n, (SS.compress t1).n with
  | Tm_name _, _
  | _, Tm_name _ -> true
  | _ -> false

let apply_predicate x p = fun e -> SS.subst [NT(x.binder_bv, e)] p

let curry_arrow (x:binder) (xs:binders) (c:comp) = 
  let tail = S.mk (Tm_arrow (xs, c)) R.dummyRange in
  S.mk (Tm_arrow([x], S.mk_Total tail)) R.dummyRange

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
    

let lookup (g:env) (e:term) : result typ =
   match FStar.Hash.lookup (e, FStar.Syntax.Hash.hash_term) table with
   | None -> fail "not in cache"
   | Some he ->
     if he.he_gamma `context_included` g.tcenv.gamma
     then (
       //BU.print1 "cache hit %s\n" (P.term_to_string e);
       fun _ -> Inl he.he_res
     )
     else fail "not in cache"

let check_no_escape (bs:binders) t =
    let xs = FStar.Syntax.Free.names t in
    if BU.for_all (fun b -> not (BU.set_mem b.binder_bv xs)) bs
    then return ()
    else fail "Name escapes its scope"

(*
     G |- e : t0 <: t1 | p
 *)
let rec check_subtype_whnf (g:env) (e:term) (t0 t1: typ)
  : result unit
  = match (SS.compress t0).n, (SS.compress t1).n with
    | Tm_refine(x0, p0), _ ->
      let [x0], p0 = SS.open_term [S.mk_binder x0] p0 in       
      weaken
        (apply_predicate x0 p0 e)
        (check_subtype g e x0.binder_bv.sort t1)

    | _, Tm_refine(x1, p1) ->
      let [x1], p1 = SS.open_term [S.mk_binder x1] p1 in       
      strengthen
        (apply_predicate x1 p1 e)
        (check_subtype g e t0 x1.binder_bv.sort)

    | Tm_arrow ([x0], c0), Tm_arrow([x1], c1) ->
      let [x0], c0 = SS.open_comp [x0] c0 in
      let [x1], c1 = SS.open_comp [x1] c1 in
      check_bqual x0.binder_qual x1.binder_qual ;;
      u1 <-- universe_of g x1.binder_bv.sort;
      with_binders [x1] [u1] (
        check_subtype g (S.bv_to_name x1.binder_bv) x1.binder_bv.sort x0.binder_bv.sort ;;
        check_subcomp g (S.mk_Tm_app e (snd (U.args_of_binders [x1])) R.dummyRange) c0 c1           
      )
         
    | Tm_arrow (x0::xs0, c0), Tm_arrow(x1::xs1, c1) ->
      check_subtype_whnf g e (curry_arrow x0 xs0 c0) (curry_arrow x1 xs1 c1)

    | Tm_app (hd0, [(arg0, aq0)]), Tm_app(hd1, [(arg1, aq1)]) ->
      check_equality_whnf g hd0 hd1 ;;
      check_equality g arg0 arg1      

    | Tm_app(hd0, arg0::args0), Tm_app(hd1, arg1::args1) ->
      check_subtype g e (curry_application hd0 arg0 args0 t0.pos)
                        (curry_application hd1 arg1 args1 t1.pos)

    | Tm_type u0, Tm_type u1 ->
      check_equality_whnf g t0 t1
  
    | _ ->
      if U.eq_tm t0 t1 = U.Equal
      then return ()
      else if equatable t0 t1
      then (
        u <-- universe_of g t0;
        guard (U.mk_eq2 u (mk_type u) t0 t1)
      )
      else fail (BU.format2 "Subtyping failed: %s </: %s"
                           (P.term_to_string t0)
                           (P.term_to_string t1))

and check_subtype (g:env) (e:term) (t0 t1:typ)
  = match U.eq_tm t0 t1 with
    | U.Equal -> return ()
    | _ ->
      let open Env in
      let t0 = N.normalize_refinement [Primops; Weak; HNF; UnfoldUntil delta_constant] g.tcenv t0 in
      let t1 = N.normalize_refinement [Primops; Weak; HNF; UnfoldUntil delta_constant] g.tcenv t1 in      
      check_subtype_whnf g e t0 t1

and check_equality_whnf (g:env) (t0 t1:typ)
  = let fail () = 
        fail (BU.format2 "not equal terms: %s <> %s"
                         (P.term_to_string t0)
                         (P.term_to_string t1))
    in
    if U.eq_tm t0 t1 = U.Equal
    then return ()
    else if g.allow_universe_instantiation
    then match t0.n, t1.n with
         | Tm_uinst (f0, us0), Tm_uinst(f1, us1) ->
           if U.eq_tm f0 f1 = U.Equal
           then if Rel.teq_nosmt_force g.tcenv t0 t1
                then return ()
                else fail ()
           else fail ()
           
         | Tm_type u0, Tm_type u1 ->
           if Rel.teq_nosmt_force g.tcenv t0 t1
           then return ()
           else fail ()         
            
         | _ -> fail ()
    else fail ()
    

and check_equality (g:env) (t0 t1:typ)
  = match U.eq_tm t0 t1 with
    | U.Equal -> return ()
    | _ ->
      let open Env in
      let t0 = N.normalize_refinement [Primops; Weak; HNF; UnfoldUntil delta_constant] g.tcenv t0 in
      let t1 = N.normalize_refinement [Primops; Weak; HNF; UnfoldUntil delta_constant] g.tcenv t1 in      
      check_equality_whnf g t0 t1

and check_subcomp (g:env) (e:term) (c0 c1:comp)
  : result unit
  = 
    if (U.is_total_comp c0 && U.is_tot_or_gtot_comp c1)
    ||  (is_gtot_comp c0 && is_gtot_comp c1)
    then check_subtype g e (U.comp_result c0) (U.comp_result c1)
    else fail "Subcomp failed"

and memo_check (g:env) (e:term)
  : result typ
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
  : result typ
  = with_context msg (Some e) (fun _ -> memo_check g e)
  
(*  G |- e : Tot t | pre *)
and check' (g:env) (e:term)
  : result typ =
  let e = SS.compress e in         
  match e.n with
  | Tm_meta(t, _) ->
    memo_check g t

  | Tm_uvar (uv, s) ->
    return (SS.subst' s (U.ctx_uvar_typ uv))

  | Tm_name x ->
    let t, _ = Env.lookup_bv g.tcenv x in
    return t

  | Tm_fvar f ->
    begin
    match Env.try_lookup_lid g.tcenv f.fv_name.v with
    | Some (([], t), _) ->
      return t
      
    | _ -> //no implicit universe instantiation allowed
      fail "Missing universes instantiation"
    end
    
  | Tm_uinst ({n=Tm_fvar f}, us) ->
    begin
    match Env.try_lookup_and_inst_lid g.tcenv us f.fv_name.v with
    | None ->
      fail "Top-level name not found"

    | Some (t, _) ->
      return t
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
      return t
    end
    
  | Tm_type u ->
    return (mk_type (U_succ u))
    
  | Tm_refine(x, phi) ->
    let [x], phi = SS.open_term [S.mk_binder x] phi in
    t <-- check "refinement head" g x.binder_bv.sort ;
    u <-- is_type g t;
    with_binders [x] [u] (
      let g' = push_binders g [x] in
      t' <-- check "refinement formula" g' phi;
      is_type g' t';;
      return t
    )

  | Tm_abs(xs, body, _) ->
    let xs, body = SS.open_term xs body in
    xs_g <--  with_context "abs binders" None (fun _ -> check_binders g xs) ;
    let xs, us, g = xs_g in
    with_binders xs us (
      t <-- check "abs body" g body;
      return (U.arrow xs (S.mk_Total t))
    )

  | Tm_arrow(xs, c) ->
    let xs, c = SS.open_comp xs c in
    xs_g <-- with_context "arrow binders" None (fun _ -> check_binders g xs);
    let xs, us, g = xs_g in
    with_binders xs us (
      u <-- with_context "arrow comp" None (fun _ -> check_comp g c);
      return (mk_type (S.U_max (u::us)))
    )

  | Tm_app (hd, [(arg, arg_qual)]) ->
    t <-- check "app head" g hd ;
    x_r <-- is_tot_arrow g t;
    let x, t' = x_r in
    t_arg <-- check "app arg" g arg ;
    with_context "app subtyping" None (fun _ -> check_subtype g arg t_arg x.binder_bv.sort) ;;
    with_context "app arg qual" None (fun _ -> check_arg_qual arg_qual x.binder_qual) ;;
    return (SS.subst [NT(x.binder_bv, arg)] t')

  | Tm_app(hd, arg::args) ->
    let head = S.mk (Tm_app(hd, [arg])) e.pos in
    let t = S.mk (Tm_app(head, args)) e.pos in
    memo_check g t

  | Tm_ascribed (e, (Inl t, _, eq), _) ->
    te <-- check "ascription head" g e ;
    t' <-- check "ascription type" g t ;
    is_type g t' ;;
    with_context "ascription subtyping" None (fun _ -> check_subtype g e te t);;
    return t

  | Tm_ascribed (_, (Inr e, _, _), _) -> 
    fail "Effect ascriptions are not handled yet"
    
  | Tm_let((false, [lb]), body) ->
    let Inl x = lb.lbname in
    let [x], body = SS.open_term [S.mk_binder x] body in
    if I.lid_equals lb.lbeff PC.effect_Tot_lid
    then (
      tdef <-- check "let definition" g lb.lbdef ;
      ttyp <-- check "let type" g lb.lbtyp ;
      u <-- is_type g ttyp ;
      with_context "let subtyping" None (fun _ -> check_subtype g lb.lbdef tdef ttyp) ;;
      with_definition x u lb.lbdef (
        let g = push_binders g [x] in
        t <-- check "let body" g body ;
        check_no_escape [x] t;;
        return t
      )
    ) 
    else (
      fail "Let binding is effectful"
    )
    
  | Tm_match(sc, None, branches, rc_opt) ->
    t_sc <-- check "scrutinee" g sc ;
    u_sc <--  with_context "universe_of" (Some t_sc) (fun _ -> universe_of g t_sc);
    let rec check_branches path_condition
                           branch_typ_opt
                           branches
      : result typ
      = match branches with
        | [] ->
          (match branch_typ_opt with
           | None ->
             fail "could not compute a type for the match"

           | Some t ->
             guard (U.mk_imp path_condition U.t_false);;
             return t)
          
        | (p, None, b) :: rest ->
          match PatternUtils.raw_pat_as_exp g.tcenv p with
          | None ->
            fail "Ill-formed pattern"

          | Some (e, bvs) ->
            let binders = List.map S.mk_binder bvs in
            bs_g <-- check_binders g binders ;
            let bs, us, g' = bs_g in
            t <-- check "pattern term" g' e ;
            no_guard (check_subtype g' e t_sc t) ;;
            let pat_sc_eq = (U.mk_eq2 u_sc t_sc sc e) in
            tbr <--
              with_binders bs us 
                (weaken 
                  (U.mk_conj path_condition pat_sc_eq)
                  (tbr <-- check "branch" g' b ;
                   match branch_typ_opt with
                   | None -> 
                     check_no_escape bs tbr;;
                     return tbr
                   
                   | Some expect_tbr ->
                     check_subtype g' b tbr expect_tbr;;
                     return expect_tbr));
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
               | _ -> return tbr)
               
            | _ ->
              check_branches path_condition (Some tbr) rest
    in
    branch_typ_opt <-- (
      match rc_opt with
      | Some ({ residual_typ = Some t }) ->
        with_context "residual type" (Some t) (fun _ -> universe_of g t) ;;
        return (Some t)
        
      | _ ->
        return None
    );
    check_branches U.t_true branch_typ_opt branches

  | Tm_match _ ->
    fail "Match with returns clause is not handled yet"  
    
  | _ -> 
    fail (BU.format1 "Unexpected term: %s" (FStar.Syntax.Print.tag_of_term e))

and check_binders (g:env) (xs:binders)
  : result (binders & list universe & env)
  = match xs with
    | [] ->
      return ([], [], g)
      
    | x ::xs ->
      t <-- check "binder sort" g x.binder_bv.sort;
      u <-- is_type g t ;
      with_binders [x] [u] (
        let g' = push_binders g [x] in
        xs_g <-- check_binders g' xs;
        let xs, us, g = xs_g in
        return (x :: xs, u::us, g)
      )

and check_comp (g:env) (c:comp)
  : result universe
  = if U.is_tot_or_gtot_comp c
    then (
      t <-- check "comp result" g (U.comp_result c) ;
      is_type g t
    )
    else fail "Computation type is not Tot or GTot"

and universe_of (g:env) (t:typ)
  : result universe
  = t <-- check "universe of" g t ;
    is_type g t

let check_term_top g e t
  : result unit
  = let g = { tcenv = g; allow_universe_instantiation = false } in
    te <-- check "top" g e;
    with_context "top-level subtyping" None (fun _ ->
      check_subtype ({ g with allow_universe_instantiation = true}) e te t)

let check_term g e t
  = match check_term_top g e t [] with
    | Inl (_, g) -> Inl g
    | Inr err -> Inr err

let print_error (err:error) =
  let rec print_context (depth:string) (ctx:context) = 
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
      let tl = print_context (depth ^ ">") tl in
      hd ^ tl
  in
  let ctx, msg = err in
  BU.format2 "%s%s"
             (print_context "" (FStar.Compiler.List.rev ctx))
             msg
