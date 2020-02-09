module MLInterop

(** ** `public` and `tainted` classes *)
(* Intuition, without extra checking and wrapping:
- the types we can safely import for malicious ML code have to be `tainted`
- the types we can safely export to malicious ML code have to be `public` *)

class public (t:Type) = { pdummy : unit }
class tainted (t:Type) = { tdummy : unit }
// TODO: How to properly declare empty type classes?
// TODO: Any way to declare "sealed type classes"? Or more generally,
//       restricting who can add new instances, since it's a dangerous operation

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
(* [@(expect_failure)] -- TODO: the code below does fail, but this expect_failure blows up
let _ = is_tainted untainted *)

// Non-dependent pairs work pointwise
instance public_pair t1 t2 [| public t1 |] [| public t2 |] : public (t1 * t2) = { pdummy = () }
instance tainted_pair t1 t2 [| tainted t1 |] [| tainted t2 |] : tainted (t1 * t2) = { tdummy = () }
let _ = is_public (int*bool); is_tainted (int*bool)
(* let _ = is_tainted (int*untainted) -- fails as it should *)

// Dependent pairs are not tainted
(* let _ = is_tainted (x:int & (y:int{True})) -- fails as it should *)

// Dependent pairs could in principle be made public
// TODO: provided we find a way to make this actually work in practice:
(* instance public_dpair t1 t2 [| public t1 |] [| (x:t1 -> public (t2 x)) |] : public (x:t1 & (t2 x)) *)
(*   = { pdummy = () } *)
(* let _ = is_public (x:int & (y:int{True})) -- try to make this work *)

// Simple inductives like lists are also co-variant
instance public_list t [| public t |] : public (list t) = { pdummy = () }
instance tainted_list t [| tainted t |] : tainted (list t) = { tdummy = () }
let _ = is_public (list int); is_tainted (list bool)
(* let _ = is_tainted (list untainted) -- fails as it should *)
// TODO: any kind of "deriving" mechanism that could give us instances for all ML-like inductives?

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

(** ** `exportable` and `importable` classes *)
(* Intuition, **with** extra checking and wrapping:
- the types of values we can safely `import` from malicious ML code
- the types of values we can safely `export` to malicious ML code *)

open FStar.Tactics.Typeclasses

exception Contract_failure

class exportable (t1 t2 : Type) = { export : t1 -> t2; public_super : public t2 }
class importable (t1 t2 : Type) = { import : t1 -> Ex t2; tainted_super : tainted t1 }

let mk_exportable (#t1 #t2 : Type) [|public t2|] (exp : t1 -> t2) : exportable t1 t2 =
  { export = exp;  public_super = solve }
let mk_importable (#t1 #t2 : Type) [|tainted t1|] (imp : t1 -> Ex t2) : importable t1 t2 =
  { import = imp;  tainted_super = solve }

(* TODO: Superclass projectors should be autogenerated, and they anyway don't seem to work *)
instance public_exportable (#t1 #t2 : Type) (d : exportable t1 t2) : public t2 = d.public_super
instance tainted_importable (#t1 #t2 : Type) (d : importable t1 t2) : tainted t1 = d.tainted_super

instance exportable_public t [| public t|] : exportable t t = mk_exportable (fun x -> x)
instance importable_tainted t [| tainted t|] : importable t t = mk_importable (fun x -> x)

instance exportable_refinement t1 t2 [| exportable t1 t2 |]
                                     [| public t2 |] (* -- TODO: This shouldn't be needed, but it is *)
    (p : t1 -> Type0)  : exportable (x:t1{p x}) t2
= mk_exportable (fun (x:(x:t1{p x})) -> export (x <: t1))

class decidable (t:Type) (p : t -> Type0) = { dec : (x:t -> b:bool{b <==> p x}) }

instance importable_refinement t1 t2 [| importable t1 t2 |]
                                     [| tainted t1 |]  (* -- TODO: This shouldn't be needed, but it is *)
    (p : t2 -> Type0) [| decidable t2 p |]
    : importable t1 (x:t2{p x}) 
= mk_importable (fun (x:t1) -> let x : t2 = import x in
                               if dec #t2 #p x then x <: Ex (x:t2{p x}) else raise Contract_failure)
    (* TODO: quite a few type annotations needed above *)

instance exportable_pair t1 u1 t2 u2 [| exportable t1 t2 |] [| exportable u1 u2 |]
      [| public t2 |] [| public u2 |] (* -- TODO: These two shouldn't be needed, but they are *)
    : exportable (t1 * u1) (t2 * u2) =
  mk_exportable (fun (x,y) -> (export x, export y))

instance importable_pair t1 u1 t2 u2 [| importable t1 t2 |] [| importable u1 u2 |]
      [| tainted t1 |] [| tainted u1 |] (* -- TODO: These two shouldn't be needed, but they are *)
    : importable (t1 * u1) (t2 * u2) =
  mk_importable (fun (x,y) -> (import x, import y))

instance exportable_arrow t1 u1 t2 u2 [| importable t2 t1 |] [| exportable u1 u2 |]
      [| tainted t2 |] [| public u2 |] (* -- TODO: These two shouldn't be needed, but they are *)
    : exportable (t1 -> u1) (t2 -> Ex u2) =
  mk_exportable (fun (f:(t1->u1)) -> (fun (x:t2) -> export (f (import x)) <: Ex u2))

instance exportable_exarrow t1 u1 t2 u2 [| importable t2 t1 |] [| exportable u1 u2 |]
      [| tainted t2 |] [| public u2 |] (* -- TODO: These two shouldn't be needed, but they are *)
    : exportable (t1 -> Ex u1) (t2 -> Ex u2) =
  mk_exportable (fun (f:(t1->Ex u1)) -> (fun (x:t2) -> export (f (import x)) <: Ex u2))

instance exportable_mlarrow t1 u1 t2 u2 [| importable t2 t1 |] [| exportable u1 u2 |]
      [| tainted t2 |] [| public u2 |] (* -- TODO: These two shouldn't be needed, but they are *)
    : exportable (t1 -> ML u1) (t2 -> ML u2) =
  mk_exportable (fun (f:(t1->ML u1)) -> (fun (x:t2) -> export (f (import x)) <: ML u2))

instance importable_mlarrow t1 u1 t2 u2 [| exportable t2 t1 |] [| importable u1 u2 |]
      [| public t1 |] [| tainted u1 |] (* -- TODO: These two shouldn't be needed, but they are *)
    : importable (t1 -> ML u1) (t2 -> ML u2) =
  mk_importable (fun (f:(t1->ML u1)) -> (fun (x:t2) -> import (f (export x)) <: ML u2))
