module Bug102

noeq type hst : h:Type -> (h -> Tot bool) -> (h -> Tot bool) -> Type -> Type =
    | Hst : #h:Type
         -> #pre:(h -> Tot bool)
         -> #post:(h -> Tot bool)
         -> #a:Type
         -> e:h{pre e} -> (a * e':h{post e})
         -> hst h pre post a
