module Prims : sig
  type byte = char
  (* Fix this... *)
  type double  = float
  type 'a list =
    | Nil
    | Cons of 'a * 'a list
  val pipe_left : ('a -> 'b) -> 'a -> 'b
  val pipe_right : 'a -> ('a -> 'b) -> 'b
  val ignore : 'a -> unit
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
  val exit : BatInt32.t -> 'a
end


module ST : sig
  val read : 'a ref -> 'a
end


module String : sig
  val strcat : string -> string -> string
end


module List : sig
  val iter : ('a -> unit) -> 'a Prims.list -> unit
  val partition : ('a -> bool) -> 'a Prims.list -> 'a Prims.list * 'a Prims.list
  val append : 'a Prims.list -> 'a Prims.list -> 'a Prims.list
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b Prims.list -> 'a
end


module Microsoft : sig
  module FStar : sig
    module Util : sig
      type 'a set = 'a Prims.list * ('a -> 'a -> bool)

      type 'v smap = (string, 'v) BatHashtbl.t

      val format1: string -> string -> string
      val format2: string -> string -> string -> string
      val format3: string -> string -> string -> string -> string
      val print_string : string -> unit
      val int_of_string : string -> BatInt32.t
      type ('a,'b) either =
        | Inl of 'a
        | Inr of 'b
      val for_some : ('a -> bool) -> 'a Prims.list -> bool
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
