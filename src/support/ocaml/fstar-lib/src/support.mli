module Prims : sig
  type 'a list =
    | Nil
    | Cons of 'a * 'a list
end


module ST : sig
  val read : 'a ref -> 'a
end


module Microsoft : sig
  module FStar : sig
    module Util : sig
      val mk_ref : 'a -> 'a ref
    end
    module Platform : sig
      val exe : string -> string
    end
  end
end
