module FStarC.Writer

open FStarC.Class.Monoid
open FStarC.Class.Monad

type writer (m : Type) {| monoid m |} (a : Type0) =
  | Wr of m & a

val run_writer #m {| monoid m |} #a (x : writer m a) : m & a

instance val monad_writer (m :_ ) (d : monoid m) : Tot (monad (writer m))

val emit #m {| monoid m |} (x : m) : writer m unit
