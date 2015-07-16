#light "off"
module Microsoft.FStar.Backends.ML.Env
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.ML.Syntax
open Microsoft.FStar.Tc

type binding = 
    | Ty  of btvar * mlident
    | Val of bvvar * mlident * mltyscheme  
    | Fv  of fvvar * mlident * mltyscheme

type env = {
    tcenv:Tc.Env.env;
    gamma:list<binding>;
    tydefs:list<mltydecl>; 
}

let lookup_ty (g:env) (x:either<btvar,ftvar>) : option<mlty> = failwith "NYI"
let lookup  (g:env) (x:either<bvvar,fvvar>) : option<(mlexpr * mltyscheme)> = failwith "NYI"

let lookup_var g e = match e.n with 
    | Exp_bvar x -> lookup g (Inl x)
    | Exp_fvar (x, _) -> lookup g (Inr x)
    | _ -> failwith "impossible" 

let as_mlident (x:bvdef<'a>) = x.realname.idText, 0

let extend_ty (g:env) (b:binder) : env = match b with 
    | Inl a, _ -> 
      let gamma = Ty(a, as_mlident a.v)::g.gamma in 
      let tcenv = Env.push_local_binding g.tcenv (Env.Binding_typ(a.v, a.sort)) in
      {g with gamma=gamma; tcenv=tcenv} 

   | Inr x, _ -> failwith "NYI" //somethign similar, but for Val

let extend_tydef (g:env) (td:mltydecl) : env = failwith "NYI"
