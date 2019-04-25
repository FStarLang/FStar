module LogicalRelations

(* This module is a small development of a theory of relational
   equivalences over pure, simply typed F* terms.

   It also provides an axiomatic treatment of "equivalence up to",
   meant to serve as a basis for hypothetical and probabilistic
   equivalence
*)


/// `rel'` : The type of relations
let rel (s:Type) = s -> s -> prop

let type_of (#a:_) (r:rel a) = a

let refl (#s:Type) (r: rel s) =
  (forall x. x `r` x)

let sym (#s:Type) (r: rel s) =
  (forall x y. x `r` y <==> y `r` x)

let trans (#s:Type) (r: rel s) =
  (forall x y z. x `r` y /\ y `r` z ==> x `r` z)

let is_per #a (r:rel a) =
    sym r /\
    trans r
/// `per a`: a partial equivalence relation on `a`
let per (a:Type) = r:rel a{ is_per r }

/// `equiv r`: `r` is an equivalence relation
unfold
let equiv (#s:Type) (r: rel s) =
  refl r /\
  is_per r

/// `rel` : The type of equivalence relations
let erel (s:Type) = r:rel s { equiv r }

/// Maybe we could package all types as relational types
/// to avoid some redundancy.
/// But, we're not yet doing that ...
let rel_t = (t:Type & rel t)

/// `( ** )`: product relation
///  Building an equivalence relation on a pair from
///  equivalence relations on its components
let ( ** ) (#a:Type) (#b:Type) (arel:rel a) (brel:rel b) (p0 p1:(a & b)) : prop =
  let (x0, y0) = p0 in
  let (x1, y1) = p1 in
  x0 `arel` x1 /\ y0 `brel` y1

/// ` arrow_rel' `: A relation (not necessarily an equivalence relation) on
///  arrows, from equivalence relation on domain and co-domain
let arrow_rel (#a:Type) (#b:Type) (arel:rel a) (brel:rel b) (f g : (a -> b)) : prop =
    forall x0 x1. x0 `arel` x1 ==>
             f x0 `brel` g x1

/// ` ^--> `: the type of arrows that take related arguments to related results
let ( ^--> ) (#a:Type) (#b:Type) (arel:rel a) (brel:rel b) =
  f:(a -> b){ arrow_rel arel brel f f }

///  `arrow_rel` is an equivalence relation on `^-->` arrows
let arrow_rel_is_equiv #a #b (ra:erel a) (rb:erel b) : Lemma (equiv #(ra ^--> rb) (arrow_rel ra rb)) = ()
let arrow #a #b (ra:erel a) (rb:erel b) : erel (ra ^--> rb) = arrow_rel ra rb

/// Some simple relations

/// `lo`: The "low security relation", i.e., adversary visible values
/// must equal on both sides
let lo a : erel a = fun x y -> (x == y <: prop)

/// `hi`: The "high security relation", i.e., any two secret values
/// are related
let hi a : erel a = fun x y -> (True <: prop)

/// Some simple functions with relational types

/// Some information flow types for a simple function
let f : (lo int ^--> lo int) = fun x -> x + 45
let f' : (hi int ^--> hi int) = fun x -> x + 45
let f'' : (lo int ^--> hi int) = fun x -> x + 45
[@(expect_failure [19])]
let f''' : (hi int ^--> lo int) = fun x -> x + 45
let f'''' : (hi int ^--> lo int) = fun x -> x - x
let f''''' : int -> int = fun x -> x - x
let _ = assert (f''''' `arrow_rel (hi int) (lo int)` f''''')

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
    (srel: erel s)
    (arel: erel a)
    : erel (st srel arel)
  = arrow srel (arel ** srel)
  // let r (f g:st  srel arel) : prop =
  //    (forall s0 s1. s0 `srel` s1 ==>
  //              f s0 `(arel ** srel)` g s1) in
  //   r

/// `bind`: sequential composition for the relational state monad
let bind #s #a (#srel:erel s) (#arel:erel a) #b (#brel:erel b)
         ($f:st srel arel)
         (g:arel ^--> st_rel srel brel)
   : st srel brel =
   fun s0 ->
     let x, s1 = f s0 in
     g x s1

/// `return`: a "unit", or a way to promote a value, to st
let return #s #a (#srel:erel s) (#arel:erel a) (x:a)
  : st srel arel
  = fun s0 -> x, s0

/// `get`: The "reading" action for st
let get #s (#srel:erel s) : st srel srel =
  fun s0 -> s0, s0

/// `put`: The "writing" action for st
let put #s (#srel:erel s) : (srel ^--> st_rel srel (lo unit)) =
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

let one_a_rel_one_b : squash (one_a `arrow (lo int) (st_rel state_rel (lo int))` one_b) = ()
let two_a_rel_two_b : squash (two_a `arrow (lo int) (st_rel state_rel (lo bool))` two_b) = ()


////////////////////////////////////////////////////////////////////////////////
// Modules
////////////////////////////////////////////////////////////////////////////////

module DM = FStar.DependentMap

/// The type of module signatures
///
/// E.g.,
///  sig = {
///     val f : nat -> nat;
///     val rel_f : erel (nat -> nat)
///
///     val g : bool -> bool
///     val rel_g: erel (bool -> bool)
///  }
///
///  A signature maps labels (`f`, `g`, etc.)
///  to their types (nat -> nat, bool -> bool, etc.)
///  and also equivalence relations on those types (rel_f, rel_g, etc.)
noeq
type sig = {
  labels:eqtype;
  ops:labels -> Type;
  rels:(l:labels -> erel (ops l))
}

/// A module is a map providing the operations in the signature
let module_t (s:sig) =
  DM.t s.labels s.ops

/// `sig_rel`: an equivalence relation on module signatures
/// lifting pointwise an equivalence relation on its elements
let sig_rel' (s:sig) (m1 m2: module_t s)
  : prop
  = forall (k:s.labels). DM.sel m1 k `s.rels k` DM.sel m2 k

let sig_rel (s:sig)
  : erel (module_t s)
  = sig_rel' s

/// An example module: The trivial unit module

/// The unit signature has one label and one operation, i.e., () : unit
let sig_unit = {
  labels=unit;
  ops=(fun _ -> unit);
  rels=(fun l -> (fun _ _ -> (True <: prop)) <: erel unit)
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
let rel_sig_empty : erel (module_t sig_empty) = sig_rel sig_empty

/// We might show here a constant module


/// Here's a module with a couple of fields

/// `key`: A type of labels
type key =
  | ONE
  | TWO

// t_one = int -> state -> int * state
let field_types : key -> Type =
    function  ONE -> t_one
            | TWO -> t_two

let field_rels : (k:key -> erel (field_types k)) =
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
let functor_t (underlay:sig) (overlay:sig) =
  sig_rel underlay ^--> sig_rel overlay

/// Lifting a module to a functor
///   by parameterizing it over the unit module
let as_fun (#s:sig) (m:module_t s)
  : functor_t sig_unit s
  = fun _ -> m

/// Functor composition
let comp (#a:sig) (#b:sig) (f:functor_t a b)
         (#c:sig) (g:functor_t c a)
  : functor_t c b
  = fun x -> f (g x)

/// Functor composition is associative
///   Note, we prove that left-associative composition is
///   logically related to right-associative composition
///
///   NOT that the two are extensionally equal (although we might try
///   that too ... not sure it's needed)
let assoc (#a:sig) (#b:sig) (f_ab:functor_t a b)
          (#c:sig) (f_ca:functor_t c a)
          (#d:sig) (f_dc:functor_t d c)
  : Lemma
      (let f1 : functor_t d b = f_ab `comp` (f_ca `comp` f_dc) in
       let f2 : functor_t d b = (f_ab `comp` f_ca) `comp` f_dc in
       f1 `arrow (sig_rel d) (sig_rel b)` f2)
  = ()

/// A polymorphic identity functor
let id_func (#a:sig)
  : functor_t a a
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
    :  type_of (arrow (sig_rel a)
                      (arrow (sig_rel b)
                             (sig_rel (a `sig_prod` b))))
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

/// projection of modules
let module_fst (a:sig) (b:sig)
    :  functor_t (a `sig_prod` b) a
   = fun (ma:module_t (a `sig_prod` b)) ->
       let f : (l:a.labels -> Tot (a.ops l)) =
         fun (x:a.labels) -> DM.sel ma (Inl x)
       in
       let m : module_t a =
         DM.create #_ #a.ops f
       in
       m

/// projection of modules
let module_snd (a:sig) (b:sig)
    : functor_t (a `sig_prod` b) b
   = fun (mb:module_t (a `sig_prod` b)) ->
       let f : (l:b.labels -> Tot (b.ops l)) =
         fun (x:b.labels) -> DM.sel mb (Inr x)
       in
       let m : module_t b =
         DM.create #_ #b.ops f
       in
       m

/// product of functors
let functor_prod (a0 a1: sig) (b0 b1:sig)
                 (fa: functor_t a0 a1)
                 (fb: functor_t b0 b1)
   : functor_t (a0 `sig_prod` b0) (a1 `sig_prod` b1)
   = fun (m:module_t (a0 `sig_prod` b0)) ->
       let ma0 = module_fst a0 b0 m in
       let ma1 = fa ma0 in
       let mb0 = module_snd a0 b0 m in
       let mb1 = fb mb0 in
       module_prod a1 b1 ma1 mb1

(* Epsilon equivalences *)

/// Now for axiomatic some epsilon equivalences
let eps = nat

// eq r eps x y
//    x and y are related by `r`, up to eps
// Maybe index by the set of hypotheses
noeq
type eq : #a:Type -> per a -> eps -> a -> a -> Type =
  | Sym:
    #a:Type ->
    #r:per a ->
    #x:a ->
    #y:a ->
    #e:eps ->
    eq r e x y ->
    eq r e y x

  | Trans:
    #a:Type ->
    #r:per a ->
    #x:a ->
    #y:a ->
    #z:a ->
    #e1:eps ->
    #e2:eps ->
    eq r e1 x y ->
    eq r e2 y z ->
    eq r (e1 + e2) x z

  | Perfect :
    #a:Type ->
    #r:per a ->
    x:a ->
    y:a ->
    squash (x `r` y) ->
    eq r 0 x y

  | Weaken:
    #a:Type ->
    #r:per a ->
    #x:a ->
    #y:a ->
    #e1:eps ->
    e2:eps{e1 < e2} ->
    eq #a r e1 x y ->
    eq #a r e2 x y

  | Refine:
    #a:Type ->
    #r:per a ->
    #x:a ->
    #y:a ->
    #e:eps ->
    ref:(a -> Type){ref x /\ ref y} ->
    eq #a r e x y ->
    eq #(x:a{ref x}) r e x y

  | Ctx:
    #a:Type ->
    #r:per a ->
    #b:Type ->
    #e:eps ->
    #x:b ->
    #y:b ->
    #rb:per b ->
    eq rb e x y ->
    f:(rb ^--> r) ->
    eq r e (f x) (f y)

let eeq' #a (r:per a) (x y : a) = (e:eps & eq r e x y)
let eeq #a (r:per a) : rel a = fun x y -> squash (eeq' r x y)
let get_eeq #a (r:per a) (x:a) (y:a{eeq r x y})
  : Tot (eeq r x y)
  = FStar.Squash.join_squash (() <: squash (eeq r x y))

let per_eeq #a (r:per a)
  : Lemma (sym (eeq r) /\
           trans (eeq r))
          [SMTPat (is_per (eeq r))]
  = let sym_eeq (x:a) (y:a)
      : Lemma
        (requires eeq r x y)
        (ensures eeq r y x)
        [SMTPat (eeq r y x)]
    = let open FStar.Squash in
      let eeq_xy : eeq r x y = get_eeq r x y in
      let eeq_yx : eeq r y x =
          bind_squash eeq_xy (fun (| e, eq_xy |) ->
          return_squash (| e, Sym eq_xy |)) in
      eeq_yx
    in
    let trans_eeq (x y z:a)
      : Lemma
        (requires eeq r x y /\ eeq r y z)
        (ensures eeq r x z)
        [SMTPat (eeq r x y);
         SMTPat (eeq r y z)]
      = let open FStar.Squash in
        let eeq_xy : eeq r x y = get_eeq r x y in
        let eeq_yz : eeq r y z = get_eeq r y z in
        let eeq_xz : eeq r x z =
          bind_squash eeq_xy (fun (| e0, eq_xy |) ->
          bind_squash eeq_yz (fun (| e1, eq_yz |) ->
          return_squash #(eeq' r x z) (| e0+e1, Trans eq_xy eq_yz |)))
        in
        eeq_xz
    in
    ()

let erel_eeq #a (r:erel a)
  : Lemma (equiv (eeq r))
  = let refl (x:a)
      : Lemma (eeq r x x)
              [SMTPat (eeq r x x)]
      = let e : eps = 0 in
        let p : eq r e x x = Perfect x x () in
        let y : eeq r x x =
          FStar.Squash.return_squash #(eeq' r x x) (| 0, Perfect x x () |) in
        y
    in
    ()

let eeq_diag (r:per 'a) (x:'a) = x `eeq r` x
let eeq_t (r:per 'a) = f:'a{eeq_diag r f}

#push-options "--max_fuel 0 --max_ifuel 0"
let nat_ref (x:int) : Type = b2t (x >= 0)
let test_diag (x y : nat) (r:per int) (eps:eps) (e:eq r eps x y)
  : eq #(x:int{nat_ref x}) r eps x y
  = Refine nat_ref e

let refine_eeq #a (r0:per a) (x y: a)
  : Lemma
    (requires
      x `eeq #a r0` y)
    (ensures (
      let r : per (eeq_t r0) = r0 in
      x `eeq #a r0` x /\
      y `eeq #a r0` y /\
      x `eeq #(eeq_t r0) r` y))
  = assert (is_per (eeq #a r0));
    let r : per (eeq_t r0) = r0 in
    let eeq_r0_xy : eeq r0 x y = get_eeq r0 x y in
    let eeq_r_xy : eeq r x y =
        FStar.Squash.bind_squash eeq_r0_xy (fun (| e, eq_r0_xy |) ->
          let eq_r_xy : eq #(eeq_t r0) r e x y = Refine (eeq_diag r0) eq_r0_xy in
          let eeq_r_xy : eeq' r x y = (| e, eq_r_xy |) in
          FStar.Squash.return_squash eeq_r_xy)
    in
    eeq_r_xy

let refl_closure_erel #a (r:per a)
  : Lemma (let r : per (eeq_t r) = r in
           equiv (eeq r))
  = let r0 = r in
    let r : per (eeq_t r0) = r0 in
    let refine (x y:eeq_t r0)
      : Lemma
        (requires (eeq r0 x y))
        (ensures (eeq r x y))
        [SMTPat (eeq r x y)]
      = refine_eeq r0 x y
    in
    let refl_ (x:eeq_t r0)
      : Lemma (eeq r x x)
              [SMTPat (eeq r x x)]
      = ()
    in
    per_eeq r

let refl_closure (r:per 'a) : erel (eeq_t r) =
  refl_closure_erel r;
  let r : per (eeq_t r) = r in
  eeq r


let hi_lo_rel : per (int & int -> int) = arrow_rel (hi int ** lo int) (lo int)
let hi_lo_eeq : per (int & int -> int) = eeq hi_lo_rel
assume val enc : int & int -> int
assume val ideal_enc: (hi int ** lo int) ^--> lo int
assume val enc_eeq_ideal_enc : squash (hi_lo_eeq enc ideal_enc)

let enc_in_rel : squash (eeq hi_lo_rel enc enc) =
  // sym_eeq hi_lo_rel enc ideal_enc;
  // trans_eeq hi_lo_rel enc ideal_enc enc
  ()

let ideal_enc_in_rel : squash (eeq hi_lo_rel ideal_enc ideal_enc) =
  FStar.Squash.return_squash
    (FStar.Squash.return_squash (| 0, Perfect #_ #hi_lo_rel ideal_enc ideal_enc () |))

let enc' : eeq_t hi_lo_rel = enc
let ideal_enc' : eeq_t hi_lo_rel = ideal_enc

let hi_lo_eeq_erel : erel (eeq_t hi_lo_rel) =
  refl_closure_erel hi_lo_rel;
  let hi_lo_rel : rel (eeq_t hi_lo_rel) = hi_lo_rel in
  eeq hi_lo_rel

let enc_ideal_enc_rel : squash (hi_lo_eeq_erel enc ideal_enc) =
  refine_eeq hi_lo_rel enc ideal_enc
