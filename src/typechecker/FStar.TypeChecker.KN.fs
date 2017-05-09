module FStar.TypeChecker.KN

open FStar.All

open Prims
open FStar
open FStar.Ident
open FStar.Util

open FStar.Syntax.Syntax

type leftover_term_info = {     //leftover term info needed for rebuilding neutral terms
    tk:memo<term'>;
    pos:Range.range;
    vars:memo<free_vars>;
}

let ti_leftover : term -> leftover_term_info =
    fun t -> { tk=t.tk;
               pos=t.pos;
               vars=t.vars }

type leftover_lcomp_info = {    //leftover computation type info needed for rebuilding neutral terms
    eff_name: lident;
    cflags: list<cflags>;
    comp: unit -> comp
}

let li_leftover : lcomp -> leftover_lcomp_info =
    fun l -> { eff_name=l.eff_name;
               cflags=l.cflags;
               comp=l.comp }

type env =
  | Emp
  | Clos of term * env * env    //a closure
  | AVar of int * env           //an abstract variable

type stack = 
  | Emp
  | AppArgs  of args * env * leftover_term_info * stack            //arguments of function applications

  | LamTys   of binders * binder * binders                         //for reduction of types in lambda abstractions
              * term * option<either<lcomp, residual_comp>>    
              * env * env * leftover_term_info * stack    

  | LamBody  of binders * option<either<lcomp, residual_comp>>     //for reduction of the body of a lamba abstraction
              * env * leftover_term_info * stack

  | LamResTy of binders * term * leftover_lcomp_info               //for reduction of the result type of a lambda abstraction
              * env * leftover_term_info * stack   


type cfg = {
    t:term;         //term,
    e:env;          //environment
    s:stack;        //stack
    level:int;      //DeBruijn level
}

let rec add_args_to_env : args -> env -> env -> env =
    fun ts e e' -> 
        match ts with
          | [] -> e'
          | t::ts -> Clos(fst t,e,add_args_to_env ts e e')

let rec normalize : cfg -> cfg =
    fun cfg -> 
        match cfg.t.n with
          | Tm_app(t,ts) -> normalize { t=t; 
                                        e=cfg.e; 
                                        s=AppArgs(ts,cfg.e,ti_leftover cfg.t,cfg.s); 
                                        level=cfg.level }
          | Tm_abs(bs,t,ty) ->
            match cfg.s with
              | AppArgs(ts,e,_,s)                                               //beta-reduction for function application
                when (List.length bs = List.length ts) -> normalize { t=t;
                                                                      e=add_args_to_env ts e cfg.e;
                                                                      s=s;
                                                                      level=cfg.level }
              | _ -> match bs with                                              //unapplied lamba abstractions
                       | [] -> normalize { t=t;                                 //no binders, reducing the body
                                           e=cfg.e;
                                           s=LamBody(bs,ty,cfg.e,ti_leftover cfg.t,cfg.s);
                                           level=cfg.level }
                       | b::bs -> normalize { t=(fst b).sort;                   //some binders, reducing the first type annotation
                                              e=cfg.e;
                                              s=LamTys([],b,bs,t,ty,cfg.e,cfg.e,ti_leftover cfg.t,cfg.s);
                                              level=cfg.level }
          | _ -> failwith "catching all unimplemented cases"

and rebuild : cfg -> cfg =
    fun cfg ->
        match cfg.s with
        | LamTys(bs,b,bs',t,ty,e,e',ti,s) -> 
          match bs' with
            | [] -> let b' = ({ppname=(fst b).ppname; index=(fst b).index; sort=t},snd b) in          //reducing the body of a lambda
                    let level' = cfg.level + 1 in
                    let e''=AVar(level',e) in
                    normalize { t=t; 
                                e=e';
                                s=LamBody(List.append bs [b'],ty,e',ti,s);
                                level=level' }
            | b'::bs' -> let b'' = ({ppname=(fst b).ppname; index=(fst b).index; sort=t},snd b) in    //reducing the next type annotation
                         let level' = cfg.level + 1 in
                         let e'' = AVar(level',e) in
                         normalize { t=(fst b').sort;
                                     e=e'';
                                     s=LamTys(List.append bs [b''],b',bs',t,ty,e'',e',ti,s);
                                     level=level' }
        | LamBody(bs,ty,e,ti,s) -> 
          match ty with
            | None -> let t' = { n=Tm_abs(bs,cfg.t,ty); tk=ti.tk; pos=ti.pos; vars=ti.vars } in
                      rebuild { t=t';
                                e=e;
                                s=s;
                                level=cfg.level - List.length bs }
            | Some(Inl(ty')) -> normalize { t=ty'.res_typ;
                                            e=e;
                                            s=LamResTy(bs,cfg.t,li_leftover ty',e,ti,s);
                                            level=cfg.level - List.length bs }
            | Some(Inr(res)) -> let t' = { n=Tm_abs(bs,cfg.t,ty); tk=ti.tk; pos=ti.pos; vars=ti.vars } in
                                rebuild { t=t';
                                          e=e;
                                          s=s;
                                          level=cfg.level - List.length bs }
        | LamResTy(bs,t,li,e,ti,s) -> let ty = { eff_name=li.eff_name; res_typ=cfg.t; cflags=li.cflags; comp=li.comp } in
                                      let t' = { n=Tm_abs(bs,t,Some(Inl(ty))); tk=ti.tk; pos=ti.pos; vars=ti.vars } in
                                      rebuild { t=t';
                                                e=e;
                                                s=s;
                                                level=cfg.level }
        | _ -> failwith "catching all unimplemented cases"
