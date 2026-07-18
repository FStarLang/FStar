module FStar.Class.Embeddable

open FStar.Reflection.V2

class embeddable (a:Type) = {
  embed : a -> Tot term;
  typ : term;
}

instance val embeddable_string : embeddable string
instance val embeddable_bool   : embeddable bool
instance val embeddable_int    : embeddable int

instance val embeddable_list (a:Type) (ea : embeddable a) : embeddable (list a)
