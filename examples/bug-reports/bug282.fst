module Bug282

assume new type p:unit -> Type

assume val lem1: u:unit -> Lemma (requires True) (ensures (p u))
assume val lem2: u:unit -> Lemma (requires True) (ensures (p u)) [SMTPat (p u)]

assume val qintro  : #a:Type -> #p:(a -> Type) -> =f:(x:a -> Lemma (p x)) -> Lemma (forall (x:a). p x)

val lem1': unit -> Lemma (requires True) (ensures (forall u. p u))
let lem1' _ = qintro #unit #(fun u -> p u) lem1 // Works

val lem2': unit -> Lemma (requires True) (ensures (forall u. p u))
let lem2' _ = qintro #unit #(fun u -> p u) lem2 // Fails

(*
$ fstar.exe --universes Bug282.fst

/Users/anonymous/fstar/examples/bug-reports/bug282.fst(12,43-12,47) : Error
Expected expression of type "(x:Prims.unit -> Lemma (Prims.unit))";
got expression "Bug282.lem2" of type "(u:Prims.unit -> Lemma (Prims.unit))"

$ fstar.exe --universes Bug282.fst --print_effect_args

Bug282.fst(12,43-12,47) : Error
Expected expression of type "(x:Prims.unit -> Lemma (Prims.unit) Prims.l_True, (Bug282.p x@0), (Prims.Nil ))";
got expression "Bug282.lem2" of type "(u:Prims.unit -> Lemma (Prims.unit) Prims.l_True, (Bug282.p u@0), (Prims.Cons (Prims.SMTPat (Bug282.p u@0)) (Prims.Nil )))"
*)
