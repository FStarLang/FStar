module Prims : sig
  type 'a list =
    | Nil
    | Cons of 'a * 'a list
  val pipe_left : ('a -> 'b) -> 'a -> 'b
  val pipe_right : 'a -> ('a -> 'b) -> 'b
  val ignore : 'a -> unit
end


module ST : sig
  val read : 'a ref -> 'a
end


module String : sig
  val strcat : string -> string -> string
end


module List : sig
  val iter : ('a -> unit) -> 'a Prims.list -> unit
end


module Microsoft : sig
  module FStar : sig
    module Util : sig
      val print_string : string -> unit
      val mk_ref : 'a -> 'a ref
      val expand_environment_variable : string -> string
    end
    module Platform : sig
      val exe : string -> string
    end
  end
end
