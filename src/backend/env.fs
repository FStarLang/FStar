#light "off"
module Microsoft.FStar.Backends.ML.Env
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.ML.Syntax
open Microsoft.FStar.Backends.ML
open Microsoft.FStar.Tc

type binding = 
    | Ty  of btvar * mlident * mlty           //a, 'a, ('a | Top)  
    | Bv  of bvvar * mlident * mltyscheme     //x,  x, translation (typeof x)
    | Fv  of fvvar * mlpath * mltyscheme     //f,  f, translation (typeof f)

type env = {
    tcenv:Tc.Env.env;
    gamma:list<binding>;
    tydefs:list<mltydecl>; 
}

let lookup_ty (g:env) (x:either<btvar,ftvar>) : mlty = failwith "NYI"
let lookup  (g:env) (x:either<bvvar,fvvar>) : (mlexpr * mltyscheme) = failwith "NYI"

let lookup_var g e = match e.n with 
    | Exp_bvar x -> lookup g (Inl x)
    | Exp_fvar (x, _) -> lookup g (Inr x)
    | _ -> failwith "impossible" 

let extend_ty (g:env) (a:btvar) (mapped_to:option<mlty>) : env = 
    let ml_a = Util.as_mlident a.v in 
    let mapped_to = match mapped_to with 
        | None -> MLTY_Var ml_a
        | Some t -> t in
    let gamma = Ty(a, ml_a, mapped_to)::g.gamma in 
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_typ(a.v, a.sort)) in
    {g with gamma=gamma; tcenv=tcenv} 
    
let extend_bv (g:env) (x:bvvar) (t_x:mltyscheme) : env =
    let gamma = Bv(x, Util.as_mlident x.v, t_x)::g.gamma in 
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_var(x.v, x.sort)) in
    {g with gamma=gamma; tcenv=tcenv} 

let extend_fv' (g:env) (x:fvvar) (y:mlpath) (t_x:mltyscheme) : env =
    let gamma = Fv(x, y, t_x)::g.gamma in 
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_lid(x.v, x.sort)) in
    {g with gamma=gamma; tcenv=tcenv} 

let extend_fv (g:env) (x:fvvar) (t_x:mltyscheme) : env =
    extend_fv' g x (Util.mlpath_of_lident x.v) t_x

let extend_lb (g:env) (l:lbname) (t:typ) (t_x:mltyscheme) : (env * mlident) = 
    match l with 
        | Inl x -> 
          extend_bv g (Util.bvd_to_bvar_s x t) t_x, Util.as_mlident x
        | Inr f -> 
          let _, y = Util.mlpath_of_lident f in
          extend_fv' g (Util.fvvar_of_lid f t) ([], y) t_x, (y,0)

let extend_tydef (g:env) (td:mltydecl) : env = failwith "NYI"
