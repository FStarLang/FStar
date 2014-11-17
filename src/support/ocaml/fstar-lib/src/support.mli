module Prims : sig
  (* Fix this... *)
  type double  = float
  type int32 = int

  type byte = char
  type 'a list =
    | Nil
    | Cons of 'a * 'a list
  val pipe_left : ('a -> 'b) -> 'a -> 'b
  val pipe_right : 'a -> ('a -> 'b) -> 'b
  val ignore : 'a -> unit
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end


module ST : sig
  val read : 'a ref -> 'a
end


module String : sig
  val strcat : string -> string -> string
  val split : char Prims.list -> string -> string Prims.list
  val compare : string -> string -> Prims.int32
end


module List : sig
  val map : ('a -> 'b) -> 'a Prims.list -> 'b Prims.list
  val iter : ('a -> unit) -> 'a Prims.list -> unit
  val partition : ('a -> bool) -> 'a Prims.list -> 'a Prims.list * 'a Prims.list
  val append : 'a Prims.list -> 'a Prims.list -> 'a Prims.list
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b Prims.list -> 'a
end


module Microsoft : sig
  module FStar : sig
    module Util : sig
      type 'a set = 'a Prims.list * ('a -> 'a -> bool)
      val new_set: ('a -> 'a -> Prims.int32) -> ('a -> Prims.int32) -> 'a set

      type 'v smap = (string, 'v) BatHashtbl.t

      val format1: string -> string -> string
      val format2: string -> string -> string -> string
      val format3: string -> string -> string -> string -> string
      val print_string : string -> unit
      val concat_l : string -> string Prims.list -> string
      val int_of_string : string -> Prims.int32
      val hashcode: string -> Prims.int32
      val compare: string -> string -> Prims.int32
      type ('a,'b) either =
        | Inl of 'a
        | Inr of 'b
      val for_some : ('a -> bool) -> 'a Prims.list -> bool
      val prefix: 'a Prims.list -> 'a Prims.list * 'a
      val mk_ref : 'a -> 'a ref
      val expand_environment_variable : string -> string
    end
    module Unionfind : sig
      type 'a cell = {mutable contents : 'a contents}
       and 'a contents =
         | Data of 'a list * Prims.int32
         | Fwd of 'a cell
      type 'a uvar = 'a cell
      exception Impos
      val uvar_id : 'a uvar -> Prims.int32
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
