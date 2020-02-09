module MLInterop

(** ** `public` and `tainted` classes *)
(* Intuition, without extra checking and wrapping:
- the types we can safely import from malicious ML code have to be `tainted`
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

class exportable (t : Type) = { etype : Type; export : t -> etype; public_etype : public etype }
class importable (t : Type) = { itype : Type; import : itype -> Ex t; tainted_itype : tainted itype }

let mk_exportable (#t1 t2 : Type) [|public t2|] (exp : t1 -> t2) : exportable t1 =
  { etype = t2; export = exp;  public_etype = solve }
let mk_importable (t1 #t2 : Type) [|tainted t1|] (imp : t1 -> Ex t2) : importable t2 =
  { itype = t1; import = imp;  tainted_itype = solve }

instance public_exportable (#t : Type) (d : exportable t) : public (d.etype) = d.public_etype
instance tainted_importable (#t : Type) (d : importable t) : tainted (d.itype) = d.tainted_itype

instance exportable_public t [| public t|] : exportable t = mk_exportable t (fun x -> x)
instance importable_tainted t [| tainted t|] : importable t = mk_importable t (fun x -> x)

instance exportable_refinement t [| d:exportable t |] (p : t -> Type0)  : exportable (x:t{p x})
= mk_exportable (d.etype) (fun (x:(x:t{p x})) -> export (x <: t))

class decidable (t:Type) (p : t -> Type0) = { dec : (x:t -> b:bool{b <==> p x}) }

instance importable_refinement t [| d:importable t |] (p : t -> Type0) [| decidable t p |] : importable (x:t{p x}) 
= mk_importable (d.itype)
    (fun (x:d.itype) -> let x : t = import x in
                        if dec #t #p x then x <: Ex (x:t{p x}) else raise Contract_failure)
    (* TODO: quite a few type annotations needed above *)

instance exportable_pair t1 t2 [| d1:exportable t1 |] [| d2:exportable t2 |] : exportable (t1 * t2) =
  mk_exportable (d1.etype * d2.etype) (fun (x,y) -> (export x, export y))

(* TODO: this explodes, minimize and file bug: *)
(* instance importable_pair t1 t2 [| d1:importable t1 |] [| d2:importable t2 |] : importable (t1 * t2) = *)
(*   mk_importable (d1.itype * d2.itype) (fun (x,y) -> (import x, import y)) *)

instance exportable_arrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> t2)  =
  mk_exportable (d1.itype -> Ex d2.etype)
    (fun (f:(t1->t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: Ex d2.etype))

instance exportable_exarrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> Ex t2)  =
  mk_exportable (d1.itype -> Ex d2.etype)
    (fun (f:(t1->Ex t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: Ex d2.etype))

instance exportable_mlarrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> ML t2)  =
  mk_exportable (d1.itype -> ML d2.etype)
    (fun (f:(t1->ML t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: ML d2.etype))

instance importable_mlarrow t1 t2 [| d1:exportable t1 |] [| d2:importable t2 |] : importable (t1 -> ML t2)  =
  mk_importable (d1.etype -> ML d2.itype)
    (fun (f:(d1.etype -> ML d2.itype)) -> (fun (x:t1) -> import (f (export x)) <: ML t2))
