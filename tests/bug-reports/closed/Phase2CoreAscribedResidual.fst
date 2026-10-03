module Phase2CoreAscribedResidual

(* A function literal whose body is ascribed a refinement type has that
   residual type in all its copies: in the unfolded definition of [cast], and
   in the guard of [cast_inverse]. Core must not erase it in the latter, or the
   two copies are encoded as distinct SMT terms. *)

assume val app (#a:Type) (#b:Type) (f: a -> b) (x:a) : b
assume val app_eq (#a:Type) (#b:Type) (f: a -> b) (x:a) : Lemma (app f x == f x)

let cast (t:eqtype) (p1 p2: t -> prop) (lem: (x:t -> Lemma (p1 x ==> p2 x))) (x:t{p1 x}) : (x:t{p2 x}) =
  let id_cast = fun (x:t{p1 x}) -> let _ = lem x in (x <: (x:t{p2 x})) in
  app id_cast x

let cast_inverse (t:eqtype) (p1 p2: t -> prop) (lem: (x:t -> Lemma (p1 x ==> p2 x)))
  (x:t{p1 x}) (y:t{p2 y})
  : Pure (z:t{p1 z}) (requires cast t p1 p2 lem x = y) (ensures fun z -> z = y) =
  let id_cast = fun (x:t{p1 x}) -> let _ = lem x in (x <: (x:t{p2 x})) in
  let _ = app_eq #(x:t{p1 x}) #(x:t{p2 x}) id_cast x in
  x
