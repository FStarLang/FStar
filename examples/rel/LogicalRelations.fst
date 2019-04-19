module LogicalRelations

(* This module is a small development of a theory of relational
   equivalences over pure, simply typed F* terms.

   It also provides an axiomatic treatment of "equivalence up to",
   meant to serve as a basis for hypothetical and probabilistic
   equivalence
*)


/// `rel'` : The type of relations
let rel' (s:Type) = s -> s -> prop

let refl (#s:Type) (r: rel' s) =
  (forall x. x `r` x)

let sym (#s:Type) (r: rel' s) =
  (forall x y. x `r` y <==> y `r` x)

let trans (#s:Type) (r: rel' s) =
  (forall x y z. x `r` y /\ y `r` z ==> x `r` z)


/// `equiv r`: `r` is an equivalence relation
unfold
let equiv (#s:Type) (r: rel' s) =
  refl r /\
  sym r /\
  trans r

/// `rel` : The type of equivalence relations
let rel (s:Type) = r:rel' s { equiv r }

/// Maybe we could package all types as relational types
/// to avoid some redundancy.
/// But, we're not yet doing that ...
let rel_t = (t:Type & rel t)

/// `( ** )`: product relation
///  Building an equivalence relation on a pair from
///  equivalence relations on its components
let ( ** ) (#a:Type) (#b:Type) (arel:rel a) (brel:rel b) : rel (a & b) =
  let f (x0, y0) (x1, y1) : prop = x0 `arel` x1 /\ y0 `brel` y1 in
  f


/// ` arrow_rel' `: A relation (not necessarily an equivalence relation) on
///  arrows, from equivalence relation on domain and co-domain
let arrow_rel' (#a:Type) (#b:Type) (arel:rel a) (brel:rel b) : rel' (a -> b) =
  let r (f g : a -> b) : prop =
    forall x0 x1. x0 `arel` x1 ==>
             f x0 `brel` g x1
  in
  r

/// ` ^--> `: the type of arrows that take related arguments to related results
let ( ^--> ) (#a:Type) (#b:Type) (arel:rel a) (brel:rel b) =
  f:(a -> b){ arrow_rel' arel brel f f }

///  `arrow_rel` is an equivalence relation on `^-->` arrows
let arrow #a #b (ra:rel a) (rb:rel b) : rel (ra ^--> rb) = arrow_rel' ra rb

/// Some simple relations

/// `lo`: The "low security relation", i.e., adversary visible values
/// must equal on both sides
let lo a : rel a = fun x y -> (x == y <: prop)

/// `hi`: The "high security relation", i.e., any two secret values
/// are related
let hi a : rel a = fun x y -> (True <: prop)

/// Some simple functions with relational types

/// Some information flow types for a simple function
let f : (lo int ^--> lo int) = fun x -> x + 45
let f' : (hi int ^--> hi int) = fun x -> x + 45
let f'' : (lo int ^--> hi int) = fun x -> x + 45
[@(expect_failure [19])]
let f''' : (hi int ^--> lo int) = fun x -> x + 45
let f'''' : (hi int ^--> lo int) = fun x -> x - x

/// g manipulates both secrets and public values
/// but doesn't leak secrets
let g : (lo int ** hi int ^--> lo int ** hi int)
      = fun (l, h) -> l + h - h, h + h

/// another version of `g`
let g' : (lo int ** hi int ^--> lo int ** hi int)
      = fun (l, h) -> l, h + h

/// another version of `g`
let g'' : (lo int ** lo int ^--> lo int ** lo int)
      = fun (l, h) -> l, h + h + 1

/// we can also prove relations among functions with relational types
/// E.g.,  g is of course related to g'
let g_rel_g' : squash (g `arrow (lo int ** hi int) (lo int ** hi int)` g') = ()

/// And they satisfy many relations
let g_rel_g'_alt : squash (g `arrow (lo (int * int)) (lo (int * int))` g') = ()
let g_rel_g'_alt' : squash (g `arrow (lo int ** lo int) (lo int ** lo int)` g') = ()

(*
 A relational variant of the standard state monad
  st s a = s -> a * s
*)
/// `st`: A relational state monad
let st (#s:Type) (#a:Type) (srel:rel s) (arel:rel a) =
  srel ^--> (arel ** srel)

/// `st_rel`: an equivalence relation for the relational state monad
let st_rel #s #a
    (srel: rel s)
    (arel: rel a)
    : rel (st srel arel)
  = arrow srel (arel ** srel)

  // let r (f g:st  srel arel) : prop =
  //    (forall s0 s1. s0 `srel` s1 ==>
  //              f s0 `(arel ** srel)` g s1) in
  //   r

/// `bind`: sequential composition for the relational state monad
let bind #s #a (#srel:rel s) (#arel:rel a) #b (#brel:rel b)
         ($f:st srel arel)
         (g:arel ^--> st_rel srel brel)
   : st srel brel =
   fun s0 ->
     let x, s1 = f s0 in
     g x s1

/// `return`: a "unit", or a way to promote a value, to st
let return #s #a (#srel:rel s) (#arel:rel a) (x:a)
  : st srel arel
  = fun s0 -> x, s0

/// `get`: The "reading" action for st
let get #s (#srel:rel s) : st srel srel =
  fun s0 -> s0, s0

/// `put`: The "writing" action for st
let put #s (#srel:rel s) : (srel ^--> st_rel srel (lo unit)) =
  fun s _ -> (), s

/// Instantiating the st monad with a particular state
/// state = (public:int * private:int)
let state_rel = (lo int ** hi int)

/// And some specific actions for it
let get_fst : st state_rel (lo int) =
  //bind get (fun x -> return (fst x))
  x <-- get ;
  return (fst x)

let get_snd : st state_rel (hi int) =
  //bind get (fun x -> return (snd x))
  x <-- get ;
  return (snd x)

let t_one = lo int ^--> st_rel state_rel (lo int)
let t_two = lo int ^--> st_rel state_rel (lo bool)

let one_a : t_one =
  fun x ->
    l <-- get_fst ;
    return (l + x)

let one_b : t_one =
  fun x ->
    l <-- get_fst ;
    return (x + l)

let two_a : t_two =
  fun x ->
    l <-- get_fst ;
    return (l = x)

let two_b : t_two =
  fun x ->
    l <-- get_fst ;
    return (x = l)

#push-options "--max_fuel 0 --z3rlimit_factor 8 --max_ifuel 0"
let one_a_rel_one_b : squash (one_a `arrow (lo int) (st_rel state_rel (lo int))` one_b) = ()
let two_a_rel_two_b : squash (two_a `arrow (lo int) (st_rel state_rel (lo bool))` two_b) = ()
#pop-options


////////////////////////////////////////////////////////////////////////////////
// Modules
////////////////////////////////////////////////////////////////////////////////

module DM = FStar.DependentMap

/// The type of module signatures
///
/// E.g.,
///  sig = {
///     val f : nat -> nat;
///     val rel_f : rel (nat -> nat)
///
///     val g : bool -> bool
///     val rel_g: rel (bool -> bool)
///  }
///
///  A signature maps labels (`f`, `g`, etc.)
///  to their types (nat -> nat, bool -> bool, etc.)
///  and also equivalence relations on those types (rel_f, rel_g, etc.)
noeq
type sig = {
  labels:eqtype;
  ops:labels -> Type;
  rels:(l:labels -> rel (ops l))
}

/// A module is a map providing the operations in the signature
let module_t (s:sig) =
  DM.t s.labels s.ops

/// `sig_rel`: an equivalence relation on module signatures
/// lifting pointwise an equivalence relation on its elements
let sig_rel (s:sig)
   : rel (module_t s)
   = let r (m1 m2: module_t s) : prop =
       forall (k:s.labels). DM.sel m1 k `s.rels k` DM.sel m2 k
     in
     r

/// An example module: The trivial unit module

/// The unit signature has one label and one operation, i.e., () : unit
let sig_unit = {
  labels=unit;
  ops=(fun _ -> unit);
  rels=(fun l -> (fun _ _ -> (True <: prop)) <: rel unit)
}

/// The implementation of the unit signature provides its single operation
let mod_unit : module_t sig_unit =
  DM.create (fun () -> ())

/// Its equivalence relation is just the lifting from its signature
let rel_sig_unit : rel (module_t sig_unit) = sig_rel sig_unit


/// Another example module: The module with no operations

/// The empty signature has no labels
let sig_empty = {
  labels=False;
  ops=(fun _ -> False);
  rels=(fun (l:False) ->
          let r : rel _ =
            fun _ _ -> True
          in
          r)
}

/// The implementation of the unit signature provides its single operation
let mod_empty : module_t sig_empty =
  DM.create (fun _ -> false_elim())

/// Its equivalence relation is just the lifting from its signature
let rel_sig_empty : rel (module_t sig_empty) = sig_rel sig_empty

/// We might have a constant module


/// Here's a module with a couple of fields

/// `key`: A type of labels
type key =
  | ONE
  | TWO

// t_one = int -> state -> int * state
let field_types : key -> Type =
    function  ONE -> t_one
            | TWO -> t_two

let field_rels : (k:key -> rel (field_types k)) =
  function
    | ONE -> arrow (lo int) (st_rel state_rel (lo int))
    | TWO -> arrow (lo int) (st_rel state_rel (lo bool))

let sig_x = {
  labels=key;
  ops=field_types;
  rels=field_rels
}

let module_a : module_t sig_x =
  DM.create #_ #sig_x.ops
    (function ONE -> one_a
            | TWO -> two_a)

let module_b : module_t sig_x =
  DM.create #_ #sig_x.ops
    (function ONE -> one_b
            | TWO -> two_b)

let equiv_module_0_1 : squash (module_a `sig_rel sig_x` module_b) = ()


////////////////////////////////////////////////////////////////////////////////
// Functors
////////////////////////////////////////////////////////////////////////////////


/// Functors are equivalence-preserving functions from underlays to
/// overlays.
///
/// This means that functors are equipped already with this
/// contextual equivalence
///
///   A ( B )
///   B ~ B'
///  ===============
///   A (B) ~ A (B')
///
let functor_t (#underlay:sig) (urel:rel (module_t underlay))
              (#overlay:sig) (orel:rel (module_t overlay)) =
  urel ^--> orel

/// Lifting a module to a functor
///   by parameterizing it over the unit module
let as_fun (#s:sig) (m:module_t s)
  : functor_t rel_sig_unit
              (sig_rel s)
  = fun _ -> m

/// Functor composition
let comp (#a:sig) (#rel_a:rel (module_t a))
         (#b:sig) (#rel_b:rel (module_t b))
         (f:functor_t rel_a rel_b)
         (#c:sig) (#rel_c:rel (module_t c))
         (g:functor_t rel_c rel_a)
  : functor_t rel_c rel_b
  = fun x -> f (g x)

/// Functor composition is associative
///   Note, we prove that left-associative composition is
///   logically related to right-associative composition
///
///   NOT that the two are extensionally equal (although we might try
///   that too ... not sure it's needed)
let assoc (#a:sig) (#rel_a:rel (module_t a))
          (#b:sig) (#rel_b:rel (module_t b))
          (f_ab:functor_t rel_a rel_b)
          (#c:sig) (#rel_c:rel (module_t c))
          (f_ca:functor_t rel_c rel_a)
          (#d:sig) (#rel_d:rel (module_t d))
          (f_dc:functor_t rel_d rel_c)
  : Lemma
      (let f1 : functor_t rel_d rel_b = f_ab `comp` (f_ca `comp` f_dc) in
       let f2 : functor_t rel_d rel_b = (f_ab `comp` f_ca) `comp` f_dc in
       f1 `arrow rel_d rel_b` f2)
  = ()

/// A polymorphic identity functor
let id_func (#a:sig) (#rel_a: rel (module_t a))
  : functor_t rel_a rel_a
  = fun m -> m


/// The product signature
let sig_prod (a:sig) (b:sig) : sig = {
   labels=either a.labels b.labels;
   ops=(function
         | Inl l -> a.ops l
         | Inr r -> b.ops r);
   rels=(function
         | Inl l -> a.rels l
         | Inr r -> b.rels r)
}

/// product of modules
let module_prod (a:sig) (b:sig)
    :  (sig_rel a ^--> (arrow (sig_rel b) (sig_rel (a `sig_prod` b))))
   = fun (ma:module_t a) (mb:module_t b) ->
       let ab = a `sig_prod` b in
       let f : (l:ab.labels -> Tot (ab.ops l)) =
         fun (x:either a.labels b.labels) ->
         match x with
         | Inl l -> DM.sel ma l
         | Inr r -> DM.sel mb r
       in
     let m : module_t ab =
       DM.create #_ #ab.ops f
     in
     m

/// Now for axiomatic some epsilon equivalences
let eps = nat

// eq r eps x y
//    x and y are related by `r`, up to eps
// Maybe index by the set of hypotheses
noeq
type eq (#a:Type) (r:rel a) : eps -> a -> a -> Type =
  | Perfect :
    x:a ->
    y:a ->
    squash (x `r` y) ->
    eq r 0 x y

  | Trans:
    x:a ->
    y:a ->
    z:a ->
    e1:eps ->
    e2:eps ->
    eq r e1 x y ->
    eq r e2 y z ->
    eq r (e1 + e2) x z

  | Ctx:
    #b:Type ->
    e:eps ->
    x:b ->
    y:b ->
    rb:rel b ->
    eq rb e x y ->
    f:(rb ^--> r) ->
    eq r e (f x) (f y)

  | Hyp:
    x:a ->
    y:a ->
    e:eps ->
    eq r e x y

let g_eq_g' : eq (arrow (lo int ** hi int) (lo int ** hi int)) 0 g g' =
  Perfect g g' ()
