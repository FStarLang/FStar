open Prims
open FStar_Ident
open Pulse_Syntax_Base
module U = Pulse_Syntax_Pure
module S = FStar_Syntax_Syntax
type universe = Pulse_Syntax_Base.universe
type range = FStar_Compiler_Range.range
let u_zero : universe = U.u_zero
let u_succ (u:universe) : universe = U.u_succ u
let u_var (s:string) : universe = U.u_var s
let u_max (u0:universe) (u1:universe) : universe = U.u_max u0 u1
let u_unknown : universe = U.u_unknown

type qualifier = Pulse_Syntax_Base.qualifier
let as_qual (imp:bool) = if imp then Some Pulse_Syntax_Base.Implicit else None
type bv = Pulse_Syntax_Base.bv
let mk_bv (i:index) (name:string) (r:range) : bv =
 let pp = { name; range=r} in
 { bv_index = i; bv_ppname=pp }

type nm = Pulse_Syntax_Base.nm
let mk_nm (i:index) (name:string) (r:range) : nm =
 let pp = { name; range=r} in
 { nm_index = i; nm_ppname=pp }


type fv = Pulse_Syntax_Base.fv
let mk_fv (nm:lident) (r:range) : fv = 
 { fv_name = FStar_Ident.path_of_lid nm;
   fv_range = r }

type term = Pulse_Syntax_Base.term
type binder = Pulse_Syntax_Base.binder
type comp = Pulse_Syntax_Base.comp
type vprop = term

let ppname_of_id (i:ident) : ppname = { name = FStar_Ident.string_of_id i; range = i.idRange }

let mk_binder (x:ident) (t:term) : binder =
  { binder_ty = t;
    binder_ppname=ppname_of_id x}


let tm_bvar (bv:bv) : term = U.tm_bvar bv
let tm_var (x:nm) : term = U.tm_var x
let tm_fvar (x:fv) : term = U.tm_fvar x
let tm_uinst (l:fv) (us:universe list) : term = U.tm_uinst l us
let tm_emp : term = Tm_Emp
let tm_pure (p:term) : term = Tm_Pure p
let tm_star (p0:term) (p1:term) : term = Tm_Star (p0, p1)
let tm_exists (b:binder) (body:vprop) : term = Tm_ExistsSL (U_unknown, b, body)
let map_aqual (q:S.aqual) =
  match q with
  | Some { S.aqual_implicit = true } -> Some Implicit
  | _ -> None
let tm_arrow (b:binder) (q:S.aqual) (body:comp) : term =
  U.tm_arrow b (map_aqual q) body
let tm_expr (t:S.term) : term = Tm_FStar (t, t.pos)
let tm_unknown : term = Tm_Unknown


let mk_st_comp (pre:term) (ret:binder) (post:term) : st_comp =
  { u = U_unknown;
    res = ret.binder_ty;
    pre = pre;
    post = post
  }

let mk_comp (pre:term) (ret:binder) (post:term) : comp =
   C_ST (mk_st_comp pre ret post)

let ghost_comp (inames:term) (pre:term) (ret:binder) (post:term) : comp =
   C_STGhost (inames, mk_st_comp pre ret post)

let atomic_comp (inames:term) (pre:term) (ret:binder) (post:term) : comp =
   C_STAtomic (inames, mk_st_comp pre ret post)

module PSB = Pulse_Syntax_Builder
type st_term = Pulse_Syntax_Base.st_term
let tm_return (t:term) r : st_term = PSB.(with_range (tm_return STT false t) r)

let tm_abs (b:binder)
           (q:qualifier option)
           (pre:term)
           (body:st_term)
           (ret_ty:term option)
           (post:term option)
           r
  : st_term 
  = PSB.(with_range (tm_abs b q (Some pre) body ret_ty post) r)

let tm_st_app (head:term) (q:S.aqual) (arg:term) r : st_term =
  PSB.(with_range (tm_stapp head (map_aqual q) arg) r)
    
let tm_bind (x:binder) (e1:st_term) (e2:st_term) r : st_term =
  PSB.(with_range (tm_bind x e1 e2) r)

let tm_totbind (x:binder) (e1:term) (e2:st_term) r : st_term =
  PSB.(with_range (tm_totbind x e1 e2) r)

let tm_let_mut (x:binder) (v:term) (k:st_term) r : st_term =
  PSB.(with_range (tm_with_local x v k) r)
   
let tm_while (head:st_term) (invariant: (ident * vprop)) (body:st_term) r : st_term =
  PSB.(with_range (tm_while (snd invariant) head (ppname_of_id (fst invariant)) body) r)
   
let tm_if (head:term) (returns_annot:vprop option) (then_:st_term) (else_:st_term) r : st_term =
  PSB.(with_range (tm_if head then_ else_ returns_annot) r)

let tm_intro_exists (erased:bool) (p:vprop) (witnesses:term list) r : st_term =
  PSB.(with_range (tm_intro_exists erased p witnesses) r)

let is_tm_intro_exists (s:st_term) : bool =
  match s.term1 with
  | Tm_IntroExists _ -> true
  | _ -> false

let tm_protect (s:st_term) : st_term = PSB.(with_range (tm_protect s) s.range1)

let tm_par p1 p2 q1 q2 b1 b2 r : st_term =
  PSB.(with_range (tm_par p1 b1 q1 p2 b2 q2) r)

let tm_rewrite p1 p2 r : st_term =
  PSB.(with_range (tm_rewrite p1 p2) r)

let close_term t v = Pulse_Syntax_Naming.close_term t v
let close_st_term t v = Pulse_Syntax_Naming.close_st_term t v
let close_comp t v = Pulse_Syntax_Naming.close_comp t v
let comp_pre c =
  match c with
   | C_ST st
   | C_STAtomic (_, st)
   | C_STGhost (_, st) -> st.pre
   | _ -> tm_emp

let comp_res c =
  match c with
   | C_ST st
   | C_STAtomic (_, st)
   | C_STGhost (_, st) -> st.res
   | C_Tot t -> t

let comp_post c =
  match c with
   | C_ST st
   | C_STAtomic (_, st)
   | C_STGhost (_, st) -> st.post
   | _ -> tm_emp

let print_exn (e:exn) = Printexc.to_string e

open FStar_Pervasives
module Env = FStar_TypeChecker_Env
let tac_to_string (env:Env.env) f =
    let ps =
        FStar_Tactics_Basic.proofstate_of_goals 
                (Env.get_range env)
                env
                []
                []
    in
    match f ps with
    | FStar_Tactics_Result.Success (x, _) -> x
    | FStar_Tactics_Result.Failed (exn, _) -> failwith (print_exn exn)

let binder_to_string (env:Env.env) (b:binder)
  : string
  = tac_to_string env (Pulse_Syntax_Printer.binder_to_string b)
let term_to_string (env:Env.env) (t:term)
  : string
  = tac_to_string env (Pulse_Syntax_Printer.term_to_string t)
let st_term_to_string (env:Env.env) (t:st_term)
  : string
  = tac_to_string env (Pulse_Syntax_Printer.st_term_to_string t)
let comp_to_string (env:Env.env) (t:comp)
  : string
  = tac_to_string env (Pulse_Syntax_Printer.comp_to_string t)  
