(*
   Copyright 2008-2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: K. Kohbrok, M. Kohlweiss, T. Ramananandro, N. Swamy
*)

module Setoids

/// Markulf and Konrad do proofs of cryptographic security by
/// reasoning about equivalences of cryptographic functionalities
/// expressed as functors.
///
/// Konrad's slides from a talk at Bertinoro provide a good overview
/// https://github.com/kkohbrok/kkohbrok.github.io/raw/master/talks/skech2018.pdf
///
/// For instance, they write things like:
///              PKAE⁰
///    =         MOD-PKAE⁰ . (ODH⁰ | AE⁰) . KEY
///    ~εₒ + εₐ  MOD-PKAE¹ . (ODH¹ | AE¹) . KEY
///    =         PKAE¹
///
/// to express the security of a authenticated encryption construction.
///
/// Elements like ODH⁰ are functors (parameterized modules) expressing
/// cryptographic hypotheses
///      `.` is functor composition
///      `|` is functor product
///
/// The equivalences are all contextual, i.e., an attacker functor
/// when interacting cannot tell two sides of an equivalence apart,
/// except with a probability ε

/// In trying to formalize what this style of proof might mean in F*,
/// we develop here a small theory of equivalences for simply typed,
/// but pure, higher order, monadic F* code packaged into an encoding
/// of modules and functors within F*'s term language.
///
/// This is still work in progress: we have yet to validate whether
/// this style of proof might work at a scale needed for interesting
/// crypto proofs. But, it's already quite a bit of fun, I think.

/// It turns out that the techniques we use are related to setoids and
/// partial equivalence relations. To learn more about those, you
/// might want to read:
///
///   Setoids in type theory:
///       http://www.cs.nott.ac.uk/~pszvc/publications/Setoids_JFP_2003.pdf
///   PER model of secure information flow
///       https://www.cse.chalmers.se/~andrei/esop99.pdf

(** First, some basics **)

/// `rel'` : The type of relations
let rel (s:Type) = s -> s -> Type0

/// `type_of` :
///
/// A convenience to compute that type of elements of a relation
unfold
let type_of #a (r:rel a) = a

/// Reflexivity
let refl #s (r: rel s) =
  forall x. x `r` x

/// Symmetry
let sym #s (r: rel s) =
  forall x y. x `r` y <==> y `r` x

/// Transitivity
let trans #s (r: rel s) =
  forall x y z. x `r` y /\ y `r` z ==> x `r` z

/// A partial equivalence relation (PER) is not necessarily reflexive,
/// but is symmetric and transitive
let is_per #a (r:rel a) =
  sym r /\
  trans r

/// `per a`: a partial equivalence relation on `a`
let per (a:Type) = r:rel a{ is_per r }

/// `equiv r`: `r` is an equivalence relation
///   i.e., a reflexive PER
let equiv (#s:Type) (r: rel s) =
  refl r /\
  is_per r

/// `rel` : The type of equivalence relations
let erel (s:Type) = r:rel s { equiv r }

/// `erel_of_per`: Any PER can be seen as an an equivalence relation
///  on the diagonal of its domain
let erel_of_per (#a:Type) (r:per a)
  : erel (x:a{x `r` x})
  = r

/// In fact, every pair of elements in the PER is also on its diagonal
///   (through symmetry and transitivity)
let per_diagonal #a (r:per a) (x y : a)
  : Lemma
    (requires x `r` y)
    (ensures
      x `r` x /\
      y `r` y)
  = ()


/// `perₜ` : A partial setoid.
///
///    Note, rather than using `perₜ` below, we use instead its
///    curried form, which turns out to be more convenient for type
///    inference
let per_t = (t:Type & per t)

/// `( ** )`: product relation
///  Building a relation on pairs from
///  relations on its components
let ( ** ) (#a:Type) (#b:Type) (arel:rel a) (brel:rel b) (p0 p1:(a & b)) : prop =
  let (x0, y0) = p0 in
  let (x1, y1) = p1 in
  x0 `arel` x1 /\
  y0 `brel` y1

/// ` arrow_rel' `:
///  A relation on arrows, from relations on domain and co-domain
let arrow_rel (#a:Type) (#b:Type) (arel:rel a) (brel:rel b) (f g : (a -> b)) : prop =
    forall x0 x1. x0 `arel` x1 ==>
             f x0 `brel` g x1

/// `arrow_rel` is a PER when its arguments are PERs
///
///  Note, `arrow_rel` is not an equivalence relation on `a -> b`
///  since it need not be reflexive.
let arrow #a #b (ra:per a) (rb:per b) : per (a -> b) = arrow_rel ra rb

/// ` ^--> `: the type of functions that take related arguments to related results
let ( ^--> ) (#a:Type) (#b:Type) (arel:rel a) (brel:rel b) =
  f:(a -> b){ f `arrow_rel arel brel` f}

/// `e_arrow_rel`: But it is an equivalence relation on reflexive
/// elements of `arrow_rel`
let e_arrow_rel #a #b (ra:per a) (rb:per b) : erel (ra ^--> rb) = arrow_rel ra rb

/// Now for some simple examples

/// `lo`: The "low security relation", i.e., adversary visible values
/// must be equal on both sides
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

/// `st`: A relational variant of the standard state monad `s -> a * s`
let st (#s:Type) (#a:Type) (srel:rel s) (arel:rel a) =
  srel ^--> (arel ** srel)

/// `st_rel`: an equivalence relation for the relational state monad
let st_rel #s #a
    (srel: erel s)
    (arel: erel a)
    : erel (st srel arel)
  = arrow_rel srel (arel ** srel)

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

/// A couple of `st` types
let t_one = lo int ^--> st_rel state_rel (lo int)
let t_two = lo int ^--> st_rel state_rel (lo bool)

/// An a couple of simple functions implementing those types
///
/// The type of each proves that they are related to themselves e.g.,
/// that each is information flow secure according to their types
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

/// Further, `one_a` and `one_b` cannot be distinguished by an adversary
let one_a_rel_one_b : squash (one_a `arrow (lo int) (st_rel state_rel (lo int))` one_b) = ()
/// Likewise for `two_a` and `two_b`
let two_a_rel_two_b : squash (two_a `arrow (lo int) (st_rel state_rel (lo bool))` two_b) = ()

////////////////////////////////////////////////////////////////////////////////
// Encoding modules
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
  rels:(l:labels -> per (ops l))
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
  : per (module_t s)
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

let equiv_module_ab : squash (module_a `sig_rel sig_x` module_b) = ()
let equiv_module_aa : squash (module_a `sig_rel sig_x` module_a) = ()
let equiv_module_bb : squash (module_b `sig_rel sig_x` module_b) = ()

////////////////////////////////////////////////////////////////////////////////
// Functors
////////////////////////////////////////////////////////////////////////////////


/// Functors are equivalence-preserving functions from modules to
/// modules
///
/// This means that functors are equipped already with this
/// contextual equivalence
///
///   A ( B )
///   B ~ B'
///  ===============
///   A (B) ~ A (B')
///
/// Thought of in term of layers, a functor consumes an "underlay" and
/// provides an "overlay"
///
///   overlay  : sig
///     impl
///   underlay : sig
let functor_t (underlay:sig) (overlay:sig) =
  sig_rel underlay ^--> sig_rel overlay

/// Lifting a module to a functor
///   by parameterizing it over the unit module
let as_fun (#s:sig) (m:module_t s{m `sig_rel s` m})
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


/// Epsilon equivalences:
///     Imperfect equivalences indexed by an adversary's advantage


/// `atk s t` is an attacker context that can interact with a `s -> t`
/// functor.
///
/// Ultimately, given a "whole program" functor `unit -> t` (i.e, with
/// a trivial underlay), the attacker is a `t -> unit` context that
/// can interact with it.
let atk (s t : sig) = functor_t t s

/// The advantage is a probability associated with an attacker
let eps s t = atk s t -> nat

/// Advantages have a zero and can be summed
let eps_z #s #t : eps s t = fun m -> 0
let sum #s #t (e1 e2:eps s t) : eps s t = fun m -> e1 m + e2 m

/// Given an attacker on `s -> t`, and a functor `f: t -> r` we can
/// adapt the advantage to apply it to `s -> r`
let eps_trans #r #s #t (f:functor_t t r) (e: eps s t)
  : eps s r
  = fun (a:atk s r) ->
      let a':atk s t =
        fun (m:module_t t) ->
          a (f m)
      in
      e a'

// eq r eps x y
//    x and y are related by `r`, up to eps
// Maybe index by the set of hypotheses
noeq
type eq (#s:sig) (#t:sig) (r:per (functor_t s t)) : eps s t -> functor_t s t -> functor_t s t -> Type =
  | Sym:
    #x:functor_t s t ->
    #y:functor_t s t ->
    #e:eps s t ->
    eq r e x y ->
    eq r e y x

  | Trans:
    #x:functor_t s t ->
    #y:functor_t s t ->
    #z:functor_t s t ->
    #e1:eps s t ->
    #e2:eps s t ->
    eq r e1 x y ->
    eq r e2 y z ->
    eq r (e1 `sum` e2) x z

  | Perfect :
    x:functor_t s t ->
    y:functor_t s t ->
    squash (x `r` y) ->
    eq r eps_z x y

  | Ctx:
    #q:sig ->
    #e:eps s q ->
    #x:functor_t s q ->
    #y:functor_t s q ->
    #rb:per (functor_t s q) ->
    eq rb e x y ->
    f:functor_t q t ->
    eq r (eps_trans f e) (f `comp` x) (f `comp` y)

let eeq #s #t (r:per (functor_t s t))
  : rel (functor_t s t)
  = fun (x y : functor_t s t) -> (e:eps s t & squash (eq r e x y))

let get_eeq #s #t (r:per (functor_t s t)) (x:functor_t s t) (y:functor_t s t{eeq r x y})
  : Tot (squash (eeq r x y))
  = ()

let per_eeq #s #t (r:per (functor_t s t))
  : Lemma (sym (eeq r) /\
           trans (eeq r))
          [SMTPat (is_per (eeq r))]
  = let sym_eeq (x y:functor_t s t)
      : Lemma
        (requires eeq r x y)
        (ensures eeq r y x)
        [SMTPat (eeq r y x)]
    = let open FStar.Squash in
      let eeq_xy : squash (eeq r x y) = () in
      let eeq_yx : squash (eeq r y x) =
          bind_squash eeq_xy (fun (| e, s_eq_xy |) ->
          let s_eq_xy : squash (eq r e y x) =
            bind_squash s_eq_xy (fun eq_xy ->
            return_squash (Sym eq_xy))
          in
          return_squash (| e, s_eq_xy |))
      in
      eeq_yx
    in
    let trans_eeq (x y z:functor_t s t)
      : Lemma
        (requires eeq r x y /\ eeq r y z)
        (ensures eeq r x z)
        [SMTPat (eeq r x y);
         SMTPat (eeq r y z)]
      = let open FStar.Squash in
        let eeq_xy = get_eeq r x y in
        let eeq_yz = get_eeq r y z in
        let eeq_xz : squash (eeq r x z) =
          bind_squash eeq_xy (fun (| e0, s_eq_xy |) ->
          bind_squash eeq_yz (fun (| e1, s_eq_yz |) ->
          let s_eq_xz : squash (eq r (e0 `sum` e1) x z) =
            bind_squash s_eq_xy (fun eq_xy ->
            bind_squash s_eq_yz (fun eq_yz ->
            return_squash (Trans eq_xy eq_yz)))
          in
          return_squash #(eeq r x z) (| e0 `sum` e1, s_eq_xz |)))
        in
        eeq_xz
    in
    ()

//TODO: restore this to work with the new functorized eeq
// let hi_lo_rel : per (int & int -> int) = arrow_rel (hi int ** lo int) (lo int)
// let hi_lo_eeq : per (int & int -> int) = eeq hi_lo_rel
// assume val enc : int & int -> int
// assume val ideal_enc: (hi int ** lo int) ^--> lo int
// assume val enc_eeq_ideal_enc : squash (hi_lo_eeq enc ideal_enc)
// let _ = assert (enc `erel_of_per hi_lo_eeq` ideal_enc)
