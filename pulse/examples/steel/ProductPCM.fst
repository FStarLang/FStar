module ProductPCM

open FStar.PCM

/// We can define a PCM for structs with two fields {a; b} by defining
/// a PCM for tuples (a & b) in terms of (potentially user-defined)
/// PCMs for a and b.

val tuple_comp : pcm 'a -> pcm 'b -> 'a & 'b -> 'a & 'b -> prop
let tuple_comp p q (xa, xb) (ya, yb) = composable p xa ya /\ composable q xb yb

val tuple_op : p: pcm 'a -> q: pcm 'b -> x:('a & 'b) -> y:('a & 'b){tuple_comp p q x y} -> 'a & 'b
let tuple_op p q (xa, xb) (ya, yb) = (op p xa ya, op q xb yb)

val tuple_pcm : pcm 'a -> pcm 'b -> pcm ('a & 'b)
let tuple_pcm p q = FStar.PCM.({
  p = {
    composable=tuple_comp p q;
    op=tuple_op p q;
    one=(p.p.one, q.p.one)
  };
  comm = (fun (xa, xb) (ya, yb) -> p.comm xa ya; q.comm xb yb);
  assoc = (fun (xa, xb) (ya, yb) (za, zb) -> p.assoc xa ya za; q.assoc xb yb zb);
  assoc_r = (fun (xa, xb) (ya, yb) (za, zb) -> p.assoc_r xa ya za; q.assoc_r xb yb zb);
  is_unit = (fun (xa, xb) -> p.is_unit xa; q.is_unit xb);
  refine = (fun (xa, xb) ->
    (xa, xb) == (p.p.one, q.p.one) \/
    (p.refine xa /\ q.refine xb /\ ~ (xa == p.p.one) /\ ~ (xb == q.p.one)))
})

/// If no custom PCM is needed, p and q can be instantiated with an all-or-none PCM:

val opt_comp : option 'a -> option 'a -> prop
let opt_comp x y = match x, y with None, _ | _, None -> True | _ -> False

val opt_op : x:option 'a -> y:option 'a {opt_comp x y} -> option 'a
let opt_op x y = match x, y with None, z | z, None -> z

val opt_pcm : pcm (option 'a)
let opt_pcm #a = FStar.PCM.({
  p = {
    composable=opt_comp;
    op=opt_op;
    one=None
  };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun _ -> True);
})

/// We can generalize to 'a-ary products (z:'a -> f z), given a PCM for each z:

open FStar.FunctionalExtensionality

val prod_comp :
  f:('a -> Type) -> (z:'a -> pcm (f z)) ->
  restricted_t 'a f -> restricted_t 'a f -> prop
let prod_comp f p x y = forall z. composable (p z) (x z) (y z)

val prod_op :
  f:('a -> Type) -> p:(z:'a -> pcm (f z)) -> 
  x:restricted_t 'a f -> y: restricted_t 'a f {prod_comp f p x y} -> 
  restricted_t 'a f
let prod_op #a f p x y = on_domain a (fun z -> op (p z) (x z) (y z))

val prod_one : f:('a -> Type) -> (z:'a -> pcm (f z)) -> restricted_t 'a f
let prod_one f p = on_domain _ (fun z -> (p z).p.one)

let ext (a: Type) (b: (a -> Type)) (f g: restricted_t a b)
  : Lemma (ensures (feq #a #b f g <==> f == g))
= extensionality a b f g

val prod_pcm' : f:('a -> Type) -> (z:'a -> pcm (f z)) -> pcm' (restricted_t 'a f)
let prod_pcm' #a f p = FStar.PCM.({
  composable = prod_comp f p;
  op = prod_op f p;
  one = prod_one f p;
})

open FStar.Classical
val prod_comm :
  f:('a -> Type) -> p:(z:'a -> pcm (f z)) ->
  x:restricted_t 'a f ->
  y:restricted_t 'a f {prod_comp f p x y} ->
  Lemma (prod_op f p x y == prod_op f p y x)
let prod_comm #a f p x y =
  let comm (z:a): Lemma ((p z).p.op (x z) (y z) == (p z).p.op (y z) (x z)) =
    (p z).comm (x z) (y z)
  in forall_intro comm;
  ext a f (prod_op f p x y) (prod_op f p y x)

val prod_assoc :
  f:('a -> Type) -> p:(w:'a -> pcm (f w)) ->
  x:restricted_t 'a f ->
  y:restricted_t 'a f ->
  z:restricted_t 'a f {prod_comp f p y z /\ prod_comp f p x (prod_op f p y z)} ->
  Lemma (prod_comp f p x y /\
         prod_comp f p (prod_op f p x y) z /\
         prod_op f p x (prod_op f p y z) == prod_op f p (prod_op f p x y) z)
let prod_assoc #a f p x y z =
  let assoc (w:a): 
    Lemma (composable (p w) (x w) (y w) /\
           composable (p w) (op (p w) (x w) (y w)) (z w) /\
           op (p w) (x w) (op (p w) (y w) (z w)) == op (p w) (op (p w) (x w) (y w)) (z w)) 
  = (p w).assoc (x w) (y w) (z w) in
  forall_intro assoc;
  ext a f (prod_op f p x (prod_op f p y z)) (prod_op f p (prod_op f p x y) z)

val prod_assoc_r :
  f:('a -> Type) -> p:(w:'a -> pcm (f w)) ->
  x:restricted_t 'a f ->
  y:restricted_t 'a f ->
  z:restricted_t 'a f {prod_comp f p x y /\ prod_comp f p (prod_op f p x y) z} ->
  Lemma (prod_comp f p y z /\
         prod_comp f p x (prod_op f p y z) /\
         prod_op f p x (prod_op f p y z) == prod_op f p (prod_op f p x y) z)
let prod_assoc_r #a f p x y z =
  let assoc_r (w:a): 
    Lemma (composable (p w) (y w) (z w) /\
           composable (p w) (x w) (op (p w) (y w) (z w)) /\
           op (p w) (x w) (op (p w) (y w) (z w)) == op (p w) (op (p w) (x w) (y w)) (z w)) 
  = (p w).assoc_r (x w) (y w) (z w) in
  forall_intro assoc_r;
  ext a f (prod_op f p x (prod_op f p y z)) (prod_op f p (prod_op f p x y) z)

val prod_is_unit :
  f:('a -> Type) -> p:(z:'a -> pcm (f z)) ->
  x:restricted_t 'a f ->
  Lemma (prod_comp f p x (prod_one f p) /\
         prod_op f p x (prod_one f p) == x)
let prod_is_unit #a f p x =
  let is_unit (y:a): 
    Lemma (composable (p y) (x y) (prod_one f p y) /\
           op (p y) (x y) (prod_one f p y) == x y)
  = (p y).is_unit (x y) in
  forall_intro is_unit;
  ext a f (prod_op f p x (prod_one f p)) x

val prod_pcm : f:('a -> Type) -> (z:'a -> pcm (f z)) -> pcm (restricted_t 'a f)
let prod_pcm #a f p = FStar.PCM.({
  p = prod_pcm' f p;
  comm = prod_comm f p;
  assoc = prod_assoc f p;
  assoc_r = prod_assoc_r f p;
  is_unit = prod_is_unit f p;
  refine = (fun x ->
    (forall z. x z == (p z).p.one) \/
    (forall z. (p z).refine (x z) /\ ~ (x z == (p z).p.one)))
})

/// Similarly, given a PCM for each z:a, we can model a-ary unions with an PCM for option (x:a & f x), where
/// - None is the unit of the PCM
/// - Some (x, y) is a union with tag x and content y

let union (a:Type) (f:a -> Type) (p:(x:a -> pcm (f x))) = option (x:a & f x)

val union_comp :
  f:('a -> Type) -> p:(z:'a -> pcm (f z)) ->
  symrel (union 'a f p)
let union_comp f p x y = match x, y with
  | None, z | z, None -> True
  | Some (|xa, xb|), Some (|ya, yb|) -> xa == ya /\ composable (p xa) xb yb

val union_op :
  f:('a -> Type) -> p:(z:'a -> pcm (f z)) ->
  x:union 'a f p -> y:union 'a f p {union_comp f p x y} -> union 'a f p
let union_op f p x y = match x, y with
  | None, z | z, None -> z
  | Some (|xa, xb|), Some (|ya, yb|) -> Some (|xa, (p xa).p.op xb yb|)

val union_pcm : f:('a -> Type) -> p:(x: 'a -> pcm (f x)) -> pcm (union 'a f p)
let union_pcm #a f p = FStar.PCM.({
  p = {
    composable=union_comp f p;
    op=union_op f p;
    one=None
  };
  comm = (fun x y -> match x, y with
    | None, _ | _, None -> ()
    | Some (|xa, xb|), Some (|ya, yb|) -> (p xa).comm xb yb);
  assoc = (fun x y z -> match x, y, z with
    | None, _, _ | _, _, None | _, None, _ -> ()
    | Some (|xa, xb|), Some (|ya, yb|), Some (|za, zb|) -> (p xa).assoc xb yb zb);
  assoc_r = (fun x y z -> match x, y, z with
    | None, _, _ | _, _, None | _, None, _ -> ()
    | Some (|xa, xb|), Some (|ya, yb|), Some (|za, zb|) -> (p xa).assoc_r xb yb zb);
  is_unit = (fun _ -> ());
  refine = (fun x -> match x with
    | None -> True
    | Some (|xa, xb|) -> (p xa).refine xb /\ ~(xb == (p xa).p.one))
})
