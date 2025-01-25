module FStarC.Class.PP

open FStarC.Effect
open FStarC.Pprint

class pretty (a:Type) = {
  pp : a -> ML document;
}

instance val pp_unit : pretty unit
instance val pp_int : pretty int
instance val pp_bool : pretty bool
//instance val pp_char : pretty char

(* We intentionally do not add a `pretty string` instance, as there
are many differenta ways of pprinting a string (doc_of_string, text,
arbitrary_string). *)

instance val pp_list (a:Type) (_ : pretty a) : Tot (pretty (list a))

instance val pp_option (a:Type) (_ : pretty a) : Tot (pretty (option a))

instance val pp_either
   (_ : pretty 'a)
   (_ : pretty 'b)
: Tot (pretty (either 'a 'b))

instance val pp_tuple2
   (_ : pretty 'a)
   (_ : pretty 'b)
: Tot (pretty ('a & 'b))

instance val pp_tuple3
   (_ : pretty 'a)
   (_ : pretty 'b)
   (_ : pretty 'c)
: Tot (pretty ('a & 'b & 'c))

instance val pp_tuple4
   (_ : pretty 'a)
   (_ : pretty 'b)
   (_ : pretty 'c)
   (_ : pretty 'd)
: Tot (pretty ('a & 'b & 'c & 'd))

instance val pp_tuple5
   (_ : pretty 'a)
   (_ : pretty 'b)
   (_ : pretty 'c)
   (_ : pretty 'd)
   (_ : pretty 'e)
: Tot (pretty ('a & 'b & 'c & 'd & 'e))

instance val pp_tuple6
   (_ : pretty 'a)
   (_ : pretty 'b)
   (_ : pretty 'c)
   (_ : pretty 'd)
   (_ : pretty 'e)
   (_ : pretty 'f)
: Tot (pretty ('a & 'b & 'c & 'd & 'e & 'f))

val pretty_from_showable (#a:Type) {| _ : Show.showable a |} : Tot (pretty a)

val showable_from_pretty (#a:Type) {| _ : pretty a |} : Tot (Show.showable a)
