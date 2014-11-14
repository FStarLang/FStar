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
      val format1: string -> string -> string
      val format2: string -> string -> string -> string
      val format3: string -> string -> string -> string -> string
      val print_string : string -> unit
      val int_of_string : string -> int
      val mk_ref : 'a -> 'a ref
      val expand_environment_variable : string -> string
    end
    module Platform : sig
      val exe : string -> string
    end
    module Getopt : sig
      val noshort : char
      type opt_variant =
        | ZeroArgs of (unit -> unit)
        | OneArg of (string -> unit) * string
    end
  end
end
