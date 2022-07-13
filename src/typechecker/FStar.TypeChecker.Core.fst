module FStar.TypeChecker.Core
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

let precondition = option typ

let result (a:Type) = option (a & precondition)

type hash_entry = {
   he_term:term;
   he_gamma:list binding;
   he_res:result typ;
}

type tc_table = FStar.Hash.hashtable term hash_entry
let table : tc_table = FStar.Hash.create FStar.Syntax.Hash.equal_term
let clear_memo_table () = FStar.Hash.clear table
let insert (g:Env.env) (e:term) (res:result typ) =
    let entry = {
       he_term = e;
       he_gamma = g.gamma;
       he_res = res
    }
    in
    FStar.Hash.insert (e, FStar.Syntax.Hash.hash_term) entry table

let lookup (g:Env.env) (e:term) : option (result typ) =
   match FStar.Hash.lookup (e, FStar.Syntax.Hash.hash_term) table with
   | None -> None
   | Some he ->
     if FStar.Syntax.Hash.equal_term e he.he_term
     && (* we should allow g.gamma to be bigger, to internalize weakening *)
       FStar.Compiler.List.forall2 
        (fun b1 b2  ->
          match b1, b2 with
          | Binding_var x1, Binding_var x2 -> 
            x1.index = x2.index
          | _ -> true)
        he.he_gamma g.gamma
     then Some he.he_res
     else None

inline_for_extraction
let return (#a:Type) (x:a) : result a = Some (x, None)

let and_pre (p1 p2:precondition) =
  match p1, p2 with
  | None, None -> None
  | Some p, None
  | None, Some p -> Some p
  | Some p1, Some p2 -> Some (U.mk_conj p1 p2)

inline_for_extraction  
let bind (#a:Type) (#b:Type) (x:result a) (y:a -> result b)
  : result b
  = match x with
    | None -> None
    | Some (x, g1) ->
      match y x with
      | None -> None
      | Some (y, g2) -> Some (y, and_pre g1 g2)

let fail #a () : result a = None

inline_for_extraction
let handle_with (#a:Type) (x:result a) (h: unit -> result a)
  : result a
  = match x with
    | None -> h ()
    | res -> res
    
let mk_type (u:universe) = S.mk (Tm_type (U_succ u)) R.dummyRange

let is_type (g:Env.env) (t:term)
  : result universe
  = let aux t = 
        match (SS.compress t).n with
        | Tm_type u ->
          return u
    
        | _ -> 
          fail ()
    in
    handle_with
      (aux t)
      (fun _ -> aux (U.unrefine (N.unfold_whnf g t)))

let is_tot_arrow (g:Env.env) (t:term)
  : result (binder & typ)
  = let aux t =
        match (SS.compress t).n with
        | Tm_arrow ([x], c)
           when U.is_total_comp c ->
          let [x], c = SS.open_comp [x] c in
          return (x, U.comp_result c)
          
        | Tm_arrow (x::xs, c) ->
          let t = S.mk (Tm_arrow(xs, c)) t.pos in
          let [x], t = SS.open_term [x] t in
          return (x, t)

        | _ ->
          fail()
    in
    handle_with
      (aux t)
      (fun _ -> aux (N.unfold_whnf g t))

let check_arg_qual (a:aqual) (b:bqual)
  : result unit
  = match b, a with
    | None, None -> return ()
    | Some (Implicit _), Some ({ aqual_implicit = true}) -> return ()
    | Some _, None
    | Some _, Some ({ aqual_implicit = false }) -> return ()
    | _ -> fail ()

let check_bqual (b0 b1:bqual)
  : result unit
  = match b0, b1 with
    | None, None -> return ()
    | Some (Implicit b0), Some (Implicit b1) 
      when b0=b1 ->
      return ()
    | _ -> 
      fail ()

let close_guard (xs:binders) (us:universes) (g:precondition)
  : precondition
  = match g with
    | None -> None
    | Some t -> 
      Some (
        FStar.Compiler.List.fold_right2
          (fun u x t -> U.mk_forall u x.binder_bv t)
          us
          xs
          t
      )

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
  = match f with
    | None -> None
    | Some (t, g) -> Some (t, close_guard xs us g)

let with_definition (#a:Type) (x:binder) (u:universe) (t:term) (f:result a)
  : result a
  = match f with
    | None -> None
    | Some (t, g) -> Some (t, close_guard_with_definition x u t g)

let guard (t:typ) 
  : result unit 
  = Some ((), Some t)

module BU = FStar.Compiler.Util
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
  = match g with
    | None -> None
    | Some (x, q) -> Some (x, weaken_subtyping_guard p q)

let strengthen (p:term) (g:result 'a)
  = match g with
    | None -> None
    | Some (x, q) -> Some (x, strengthen_subtyping_guard p q)
                           
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

(*
     G |- e : t0 <: t1 | p
 *)
let rec check_subtype_whnf (g:Env.env) (e:term) (t0 t1: typ)
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

    | _ ->
      if equatable t0 t1
      then (
        u <-- universe_of g t0;
        guard (U.mk_eq2 u (mk_type u) t0 t1)
      )
      else fail ()

and check_subtype (g:Env.env) (e:term) (t0 t1:typ)
  = match U.eq_tm t0 t1 with
    | U.Equal -> return ()
    | _ ->
      let open Env in
      let t0 = N.normalize_refinement [Primops; Weak; HNF; UnfoldUntil delta_constant] g t0 in
      let t1 = N.normalize_refinement [Primops; Weak; HNF; UnfoldUntil delta_constant] g t1 in      
      check_subtype_whnf g e t0 t1

and check_subcomp (g:Env.env) (e:term) (c0 c1:comp)
  : result unit
  = 
    if (U.is_total_comp c0 && U.is_tot_or_gtot_comp c1)
    ||  (is_gtot_comp c0 && is_gtot_comp c1)
    then check_subtype g e (U.comp_result c0) (U.comp_result c1)
    else fail ()

and check  (g:Env.env) (e:term)
  : result typ
  = match lookup g e with
    | Some r -> r
    | None -> 
      let r = check' g e in
      insert g e r;
      r
      
(*  G |- e : Tot t | pre *)
and check' (g:Env.env) (e:term)
  : result typ =
  match (SS.compress e).n with
  | Tm_meta(t, _) ->
    check g t

  | Tm_uvar (uv, s) ->
    return (SS.subst' s (U.ctx_uvar_typ uv))

  | Tm_name x ->
    let t, _ = Env.lookup_bv g x in
    return t

  | Tm_fvar f ->
    begin
    match Env.try_lookup_lid g f.fv_name.v with
    | Some (([], t), _) ->
      return t
      
    | _ -> //no implicit universe instantiation allowed
      fail()
    end
    
  | Tm_uinst ({n=Tm_fvar f}, us) ->
    begin
    match Env.try_lookup_and_inst_lid g us f.fv_name.v with
    | None ->
      fail()

    | Some (t, _) ->
      return t
    end

  | Tm_constant c ->
    let t = FStar.TypeChecker.TcTerm.tc_constant g e.pos c in
    return t
    
  | Tm_type u ->
    return (mk_type (U_succ u))
    
  | Tm_refine(x, phi) ->
    let [x], phi = SS.open_term [S.mk_binder x] phi in
    t <-- check g x.binder_bv.sort ;
    u <-- is_type g t;
    with_binders [x] [u] (
      let g' = Env.push_binders g [x] in
      t' <-- check g' phi;
      is_type g' t';;
      return t
    )

  | Tm_abs(xs, body, _) ->
    let xs, body = SS.open_term xs body in
    xs_g <-- check_binders g xs;
    let xs, us, g = xs_g in
    with_binders xs us (
      t <-- check g body;
      return (U.arrow xs (S.mk_Total t))
    )

  | Tm_arrow(xs, c) ->
    let xs, c = SS.open_comp xs c in
    xs_g <-- check_binders g xs;
    let xs, us, g = xs_g in
    with_binders xs us (
      u <-- check_comp g c;
      return (mk_type (S.U_max (u::us)))
    )

  | Tm_app (hd, [(arg, arg_qual)]) ->
    t <-- check g hd ;
    x_r <-- is_tot_arrow g t;
    let x, t' = x_r in
    t_arg <-- check g arg ;
    check_subtype g arg t_arg x.binder_bv.sort ;;
    check_arg_qual arg_qual x.binder_qual ;;
    return (SS.subst [NT(x.binder_bv, arg)] t')

  | Tm_app(hd, arg::args) ->
    let head = S.mk (Tm_app(hd, [arg])) e.pos in
    let t = S.mk (Tm_app(head, args)) e.pos in
    check g t

  | Tm_ascribed (e, (Inl t, _, eq), _) ->
    te <-- check g e ;
    t' <-- check g t ;
    is_type g t' ;;
    check_subtype g e te t;;
    return t
    
  | Tm_let((false, [lb]), body) ->
    let Inl x = lb.lbname in
    let [x], body = SS.open_term [S.mk_binder x] body in
    if I.lid_equals lb.lbeff PC.effect_Tot_lid
    then (
      tdef <-- check g lb.lbdef ;
      ttyp <-- check g lb.lbtyp ;
      u <-- is_type g ttyp ;
      check_subtype g lb.lbdef tdef ttyp ;;
      with_definition x u lb.lbdef (
        let g = Env.push_binders g [x] in
        check g body
      )
    ) 
    else (
      fail ()
    )
    
  | Tm_match(sc, None, branches, Some ({ residual_typ = Some t })) ->
    fail ()

  | Tm_match _ ->
    fail ()
    
  | _ -> 
    fail ()

and check_binders (g:Env.env) (xs:binders)
  : result (binders & list universe & Env.env)
  = match xs with
    | [] ->
      return ([], [], g)
      
    | x ::xs ->
      t <-- check g x.binder_bv.sort;
      u <-- is_type g t ;
      with_binders [x] [u] (
        let g' = Env.push_binders g [x] in
        xs_g <-- check_binders g' xs;
        let xs, us, g = xs_g in
        return (x :: xs, u::us, g)
      )

and check_comp (g:Env.env) (c:comp)
  : result universe
  = if U.is_tot_or_gtot_comp c
    then (
      t <-- check g (U.comp_result c) ;
      is_type g t
    )
    else fail ()

and universe_of (g:Env.env) (t:typ)
  : result universe
  = t <-- check g t ;
    is_type g t
