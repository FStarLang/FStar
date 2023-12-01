module FStar.Class.Show

open FStar.Compiler.Effect
open FStar.Class.Printable

class showable (a:Type) = {
  show : a -> ML string;
}

(* This extends the printable class from ulib, but also allows for an
ML effect of the `printer. *)
instance val printableshow (_ : printable 'a) : Tot (showable 'a)

instance val show_list (a:Type) (_ : showable a) : Tot (showable (list a))

instance val show_option (a:Type) (_ : showable a) : Tot (showable (option a))

instance val show_either
   (_ : showable 'a)
   (_ : showable 'b)
: Tot (showable (either 'a 'b))

instance val show_tuple2
   (_ : showable 'a)
   (_ : showable 'b)
: Tot (showable ('a & 'b))

instance val show_tuple3
   (_ : showable 'a)
   (_ : showable 'b)
   (_ : showable 'c)
: Tot (showable ('a & 'b & 'c))

instance val show_tuple4
   (_ : showable 'a)
   (_ : showable 'b)
   (_ : showable 'c)
   (_ : showable 'd)
: Tot (showable ('a & 'b & 'c & 'd))

instance val show_tuple5
   (_ : showable 'a)
   (_ : showable 'b)
   (_ : showable 'c)
   (_ : showable 'd)
   (_ : showable 'e)
: Tot (showable ('a & 'b & 'c & 'd & 'e))

instance val show_tuple6
   (_ : showable 'a)
   (_ : showable 'b)
   (_ : showable 'c)
   (_ : showable 'd)
   (_ : showable 'e)
   (_ : showable 'f)
: Tot (showable ('a & 'b & 'c & 'd & 'e & 'f))
