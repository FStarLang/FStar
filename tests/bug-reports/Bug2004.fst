module Bug2004

open FStar.Exn
open FStar.All
open FStar.Tactics.Typeclasses

class ml (t:Type) = { mldummy : unit }

instance ml_pair t1 t2 [| ml t1 |] [| ml t2 |] : ml (t1 * t2) = { mldummy = () }

class importable (t : Type) = { itype : Type; import : itype -> Ex t; ml_itype : ml itype }

let mk_importable (t1 #t2 : Type) [|ml t1|] (imp : t1 -> Ex t2) : importable t2 =
  { itype = t1; import = imp;  ml_itype = solve }

instance ml_importable (#t : Type) (d : importable t) : ml (d.itype) = d.ml_itype

instance importable_ml t [| ml t|] : importable t = mk_importable t (fun x -> x)

(* this fails with the following error: *)
instance importable_pair t1 t2 [| d1:importable t1 |] [| d2:importable t2 |] : importable (t1 * t2) =
  mk_importable (d1.itype * d2.itype) (fun (x,y) -> (import x, import y) <: Ex (t1 * t2))
