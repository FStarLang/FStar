module DynCurry

(* A monad dictionary passed at run time ([dyn], custard.md 3.2c1), used at a
   result type that is itself an arrow: [Mktuple2 <$> x <*> y], the way
   [FStarC.Syntax.VisitM] builds a pair at the identity monad.  The
   dictionary's methods take and return [any], so a curried constructor goes
   into [any] and back out at an arrow, and the continuation [ap] gives [bind]
   has a binder of arrow type. *)

open FStar.All

noeq type mon (m:Type0 -> Type0) = {
  ret : #a:Type0 -> a -> ML (m a);
  bnd : #a:Type0 -> #b:Type0 -> m a -> (a -> ML (m b)) -> ML (m b);
}

type id (a:Type0) = | I : run:a -> id a

let mid : mon id = { ret = (fun x -> I x); bnd = (fun (I a) f -> f a) }

let fmap (#m:Type0 -> Type0) (d:mon m) (#a #b:Type0) (f:a -> b) (x:m a) : ML (m b) =
  d.bnd x (fun v -> d.ret (f v))

let ap (#m:Type0 -> Type0) (d:mon m) (#a #b:Type0) (f:m (a -> b)) (x:m a) : ML (m b) =
  d.bnd f (fun g -> d.bnd x (fun v -> d.ret (g v)))

let pair (#m:Type0 -> Type0) (d:mon m) (x:m int) (y:m bool) : ML (m (int & bool)) =
  ap d (fmap d Mktuple2 x) y

let main () : ML unit =
  let I (n, b) = pair (FStar.Custard.dyn mid) (I 41) (I true) in
  FStar.IO.print_string (string_of_int (n + 1));
  FStar.IO.print_string (if b then "t\n" else "f\n")
