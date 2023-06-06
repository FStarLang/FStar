module FStar.Reflection.TypeReveal

module R = FStar.Reflection.Types
module S = FStar.Syntax.Syntax

val refl2syntax : R.term -> Tot S.term
val syntax2refl : S.term -> Tot R.term
