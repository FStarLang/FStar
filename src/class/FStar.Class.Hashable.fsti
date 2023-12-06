module FStar.Class.Hashable

include FStar.Hash

class hashable (a:Type) = {
  hash : a -> hash_code;
}

instance hashable_int    : hashable int = { hash = of_int; }
instance hashable_string : hashable string = { hash = of_string; }

instance showable_hash_code : showable hash_code = { show = string_of_hash_code; }
