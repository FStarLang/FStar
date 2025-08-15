module FStarC.Writer

open FStarC.Class.Monoid
open FStarC.Class.Monad

let writer_return #m {| monoid m |} #a (x:a) : writer m a =
  Wr (mzero, x)

let run_writer #m {| monoid m |} #a (x : writer m a) : m & a =
  let Wr (m, x) = x in
  (m, x)

let writer_bind #m {| monoid m |} #a #b (x : writer m a) (f : a -> writer m b) : writer m b =
  let Wr (a, x) = x in
  let Wr (b, y) = f x in
  Wr (mplus a b, y)

instance monad_writer (m :_ ) (d : monoid m) : Tot (monad (writer m)) = {
  return = writer_return;
  bind   = writer_bind;
}

let emit #m {| monoid m |} (x : m) : writer m unit =
  Wr (x, ())
