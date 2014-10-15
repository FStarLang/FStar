module Visit

type either 'a 'b =
  | Inl of 'a
  | Inr of 'b
type knd
type typ
type exp

type withinfo_t<'a,'t> = {
  v: 'a; 
  sort: 't;
} 
type inst<'a> = ref<option<'a>>
type bvdef<'a> = {name:int; instantiation:inst<'a>}
type bvar<'a,'t> = withinfo_t<bvdef<'a>,'t> 
type btvar = bvar<typ,knd>
type bvvar = bvar<exp,typ>

let visit_simple skel
    (h: 'env -> knd -> ('env * knd))
    (f: 'env -> typ -> ('env * typ))
    (g: 'env -> exp -> ('env * exp))
    (env:'env) (t:'kte) : ('env * 'kte) =  
  let null_extension benv (x:either<btvar, bvvar>) = match x with
    | Inl tv -> (benv, Inl tv.v)
    | Inr xv -> (benv, Inr xv.v) in
  skel
    (fun env _ k -> h env k)
    (fun env _ t -> f env t)
    (fun env _ e -> g env e)
    (fun _ e -> e)
    null_extension
    env () t
