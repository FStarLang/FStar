module MLInterop

(** ** `public` and `tainted` classes *)
(* Intuition, without extra checking and wrapping:
- the types we can safely import from malicious ML code have to be `tainted`
- the types we can safely export to malicious ML code have to be `public`
This interoperability model is all *up to extraction*,
but again without adding extra checking and wrapping.
*)

class public (t:Type) = { pdummy : unit }
class tainted (t:Type) = { tdummy : unit }


// TODO: How to properly declare empty type classes?
// GM: I should add that.

// TODO: Any way to declare "sealed type classes"? Or more generally,
//       restricting who can add new instances, since it's a dangerous operation
// GM: Not in any very robust way. We don't have "real" typeclasses as in
//     Haskell. Instead we have 1) custom implicit argument resolution and
//     2) a bunch of sugar. I think there's a way by making the class private
//     and using a proxy, but not sure it's bulletproof. In any case I'd be wary
//     of using typeclasses to enforce any kind of invariant.

let is_public t [| public t |] = ()
let is_tainted t [| tainted t |] = ()

// Basic ML types are all public and tainted
instance public_unit : public unit = { pdummy = () }
instance tainted_unit : tainted unit = { tdummy = () }
instance public_bool : public bool = { pdummy = () }
instance tainted_bool : tainted bool = { tdummy = () }
instance public_int : public int = { pdummy = () }
instance tainted_int : tainted int = { tdummy = () }
instance public_string : public string = { pdummy = () }
instance tainted_string : tainted string = { tdummy = () }

// Refinement types are public, but only trivial refinements are tainted
instance public_refined t p [| public t |] : public (x:t{p x}) = { pdummy = () }
instance tainted_refined t [| tainted t |] : tainted (x:t{True}) = { tdummy = () }

let untainted = x:int{x = 42}

let _ = is_public (x:int{x = 42}); is_tainted (x:int{True})

(* let _ = is_public untainted -- TODO: this should work, why are things not unfolded *)
(* GM: This is the unifier failing to unify `x:int{x = 42}` with `x:?t{?p x}`. Will look into it.
       Also reminds me of #1486 *)

(* [@(expect_failure)] -- TODO: the code below does fail, but this expect_failure blows up
let _ = is_tainted untainted *)

// Non-dependent pairs work pointwise
instance public_pair t1 t2 [| public t1 |] [| public t2 |] : public (t1 * t2) = { pdummy = () }
instance tainted_pair t1 t2 [| tainted t1 |] [| tainted t2 |] : tainted (t1 * t2) = { tdummy = () }
let _ = is_public (int*bool); is_tainted (int*bool)
(* let _ = is_tainted (int*untainted) -- fails as it should *)

// Dependent pairs are not tainted
(* let _ = is_tainted (x:int & (y:int{x = y} -> int)) -- fails as it should *)

// Dependent pairs could be public if we can make it work technically
instance public_dpair t1 t2 (_ : public t1) (f : (x:t1 -> public (t2 x))) : public (x:t1 & (t2 x))
  = { pdummy = () }
  
open FStar.Tactics.Typeclasses

(* //let _ = is_public (x:int & (y:int{True})) *)
(* // GM: Again the unifier failing to apply public_dpair *)
(* let _ = is_public (x:int & (y:int{True})) #(public_dpair int (fun _ -> int) solve (fun _ -> solve)) *)
(* // GM: ^ that works by giving the types manually *)

// Simple inductives like lists are also co-variant
instance public_list t [| public t |] : public (list t) = { pdummy = () }
instance tainted_list t [| tainted t |] : tainted (list t) = { tdummy = () }
let _ = is_public (list int); is_tainted (list bool)
(* let _ = is_tainted (list untainted) -- fails as it should *)


// TODO: any kind of "deriving" mechanism that could give us instances for all ML-like inductives?
// GM: we've coded up similar things, as in `examples/tactics/Printers.fst`

open FStar.Exn
open FStar.All

// Non-dependent arrows are contravariant in arguments and covariant in results, as usual,
// but only ML arrows can be tainted!
instance public_arrow t1 t2 [| tainted t1 |] [| public t2 |] : public (t1 -> t2) = { pdummy = () }
instance public_exarrow t1 t2 [| tainted t1 |] [| public t2 |] : public (t1 -> Ex t2) = { pdummy = () }
instance public_mlarrow t1 t2 [| tainted t1 |] [| public t2 |] : public (t1 -> ML t2) = { pdummy = () }
instance tainted_mlarrow t1 t2 [| public t1 |] [| tainted t2 |] : tainted (t1 -> ML t2) = { tdummy = () }

let _ = is_public (int -> bool); is_public (int -> Ex bool);
        is_public (int -> ML bool); is_tainted (bool -> ML int)
let _ = is_public (bool -> x:int{x = 42}); is_public (bool -> Ex (x:int{x = 42}));
        is_public (bool -> ML (x:int{x = 42})); is_tainted (x:int{x = 42} -> ML int)
(* let _ = is_public ((x:int{x = 42}) -> bool) -- fails as it should *)
(* let _ = is_tainted (int -> x:int{x = 42}) -- fails as it should *)
(* let _ = is_tainted (bool -> int) -- fails as it should *)
(* let _ = is_tainted (x:int{x = 42} -> int) -- fails as it should *)

// Dependent arrows are neither public not tainted ? TODO: think a bit more
(* let _ = is_public (x:int -> y:int{x=42}) -- fails as it should? *)
(* let _ = is_tainted (x:int -> y:int{x=42}) -- fails as it should? *)

(** ** `ml` class *)
(* Intuition, this are morally ML types written in F* syntax *)

class ml (t:Type) = { mldummy : unit }

// Basic ML types
instance ml_unit : ml unit = { mldummy = () }
instance ml_bool : ml bool = { mldummy = () }
instance ml_int : ml int = { mldummy = () }
instance ml_string : ml string = { mldummy = () }

instance ml_pair t1 t2 [| ml t1 |] [| ml t2 |] : ml (t1 * t2) = { mldummy = () }

instance ml_mlarrow t1 t2 [| ml t1 |] [| ml t2 |] : ml (t1 -> ML t2) = { mldummy = () }

(** ** `exportable` and `importable` classes *)
(* Intuition, **with** extra checking, wrapping, and type erasure (extraction):
- the types of values we can safely `import` from malicious ML code
- the types of values we can safely `export` to malicious ML code
This interoperability model includes extraction as well as
adding extra checking and wrapping.
*)

open FStar.Tactics.Typeclasses

exception Contract_failure

class exportable (t : Type) = { etype : Type; export : t -> etype; ml_etype : ml etype }
class importable (t : Type) = { itype : Type; import : itype -> Ex t; ml_itype : ml itype }

let mk_exportable (#t1 t2 : Type) [|ml t2|] (exp : t1 -> t2) : exportable t1 =
  { etype = t2; export = exp;  ml_etype = solve }
let mk_importable (t1 #t2 : Type) [|ml t1|] (imp : t1 -> Ex t2) : importable t2 =
  { itype = t1; import = imp;  ml_itype = solve }

instance ml_exportable (#t : Type) (d : exportable t) : ml (d.etype) = d.ml_etype
instance ml_importable (#t : Type) (d : importable t) : ml (d.itype) = d.ml_itype

instance exportable_ml t [| ml t|] : exportable t = mk_exportable t (fun x -> x)
instance importable_ml t [| ml t|] : importable t = mk_importable t (fun x -> x)

instance exportable_refinement t [| d:exportable t |] (p : t -> Type0)  : exportable (x:t{p x})
= mk_exportable (d.etype) export // TODO: Eta expanding causes type error

class decidable (t:Type) (p : t -> Type0) = { dec : (x:t -> b:bool{b <==> p x}) }
// could move to something weaker here
class checkable (t:Type) (p : t -> Type0) = { check : (x:t -> b:bool{b ==> p x}) }

instance importable_refinement t [| d:importable t |] (p : t -> Type0) [| decidable t p |] : importable (x:t{p x}) 
= mk_importable (d.itype)
    (fun (x:d.itype) -> let x : t = import x in
                        if dec #t #p x then x <: Ex (x:t{p x}) else raise Contract_failure)
    (* TODO: quite a few type annotations needed above *)

instance exportable_pair t1 t2 [| d1:exportable t1 |] [| d2:exportable t2 |] : exportable (t1 * t2) =
  mk_exportable (d1.etype * d2.etype) (fun (x,y) -> (export x, export y))

(* TODO: this explodes, minimize and file bug: *)
(* instance importable_pair t1 t2 [| d1:importable t1 |] [| d2:importable t2 |] : importable (t1 * t2) = *)
(*   mk_importable (d1.itype * d2.itype) (fun (x,y) -> (import x, import y) <: Ex (t1 * t2)) *)

instance exportable_arrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> t2)  =
  mk_exportable (d1.itype -> ML d2.etype)
    (fun (f:(t1->t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: ML d2.etype))

instance exportable_exarrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> Ex t2)  =
  mk_exportable (d1.itype -> ML d2.etype)
    (fun (f:(t1->Ex t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: ML d2.etype))

instance exportable_mlarrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> ML t2)  =
  mk_exportable (d1.itype -> ML d2.etype)
    (fun (f:(t1->ML t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: ML d2.etype))

instance importable_mlarrow t1 t2 [| d1:exportable t1 |] [| d2:importable t2 |] : importable (t1 -> ML t2)  =
  mk_importable (d1.etype -> ML d2.itype)
    (fun (f:(d1.etype -> ML d2.itype)) -> (fun (x:t1) -> import (f (export x)) <: ML t2))

(* Dependent pairs are neither importable not exportable?

   For the exportable part things are quite funny.
   It seems We can't implement this in F*: *)
(* instance exportable_dpair t1 t2 [| d1:exportable t1 |] (d2:(x:t1 -> exportable (t2 x))) : exportable (x:t1 & t2 x) = *)
(*   mk_exportable (d1.etype * d2.etype) (fun (x,y) -> (export x, export y)) *)
// - intuitively I still think it should be public/exportable
//   + the problem seems technical, not being able to internalize F* erasure
//   + which might be justification for building exportable/importable on top of
//     public/tainted (which doesn't require to internalize extraction)
//     instead of ml (which does)

(* TODO: This seems related to Eric's early work on Coq-ML interop
         https://arxiv.org/abs/1506.04205
         http://www.mlworkshop.org/lost-in-extraction-recovered.pdf
         https://github.com/tabareau/Cocasse
   - interesting idea on type dependencies: "To recover type dependencies, we
     propose to exploit type isomorphisms between dependently-typed structures
     and plain structures with subset types, and then exploit the cast framework
     presented in the previous section to safely eliminate the subset types."
   - they don't properly deal with ML effects (ignored) and cast failures
     (unsound axiom), but we can do much better here *)

(* TODO: Is this related in any way to the F*-ML interop of Zoe / native tactics?
   - similar instances for arrows and pairs
     https://arxiv.org/pdf/1803.06547.pdf#page=42 *)

(* TODO: What would be a good soundness criterion for all this?
         And can it be internalized within F*? Maybe for importable/exportable?
  - Do Michael Sammler et al prove any generic property?
      No, they couldn't find any, especially for (affine) sealing!
  - Can we take inspiration from the dynamic contracts / gradual typing world?
  - Is etype always a supertype? Is itype always a subtype?
  - Roundtripping of imports and exports (as long as we don't do affine sealing)
  - Secure compilation to ML (need to formalize extraction, see MetaCoq work)
 *)

(* Next steps:
   - deal with pre-post conditions / WPs for effects (refined computation types)
   - stateful coercions (dynamic sealing)
   - connect this with our IO work
     + export and import instances for IO functions with pre/post conditions
     + Michael: the untrusted part is really just C (the context in our
       diagram), and the interaction with anything happen via wrappers
     + Michael: if one tracks capabilities like file handlers one is able
       to reduce the amount of global state.
*)
