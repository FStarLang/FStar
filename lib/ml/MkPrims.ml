module Make = functor (X: sig
  type int
  val ( + ): int -> int -> int
  val ( - ): int -> int -> int
  val ( * ): int -> int -> int
  val ( / ): int -> int -> int
  val ( mod ): int -> int -> int
  val ( <= ): int -> int -> bool
  val ( >= ): int -> int -> bool
  val ( < ): int -> int -> bool
  val ( < ): int -> int -> bool
  val ( ~- ): int -> int
  val parse_int: string -> int
end) -> struct
  include X

  type nonrec unit = unit
  type nonrec bool = bool
  type nonrec string = string
  type nonrec 'a array = 'a array
  type nonrec exn = exn
  type nonrec 'a list = 'a list
  type nonrec 'a option = 'a option

  type nat       = int
  type pos       = int
  type 'd b2t    = unit

  type (' p, ' q) l_or =
    | Left of ' p
    | Right of ' q

  let uu___is_Left = function Left _ -> true | Right _ -> false

  let uu___is_Right = function Left _ -> false | Right _ -> true

  type (' p, ' q) l_and =
  | And of ' p * ' q

  let uu___is_And _ = true

  type l__True =
    | T

  let uu___is_T _ = true

  type l__False = unit
  (*This is how Coq extracts Inductive void := . Our extraction needs to be fixed to recognize when there
         are no constructors and generate this type abbreviation*)

  type (' p, ' q) l_imp = ' p  ->  ' q

  type (' p, ' q) l_iff = ((' p, ' q) l_imp, (' q, ' p) l_imp) l_and

  type ' p l_not = (' p, l__False) l_imp

  type (' a, ' p) l__Forall = ' a  ->  ' p

  type ' f l__ForallTyp = unit  ->  ' f

  type (' a, ' p) l__Exists =
  | MkExists of ' a * ' p


  type (' p, ' q, 'dummyP, 'dummyQ) l__Eq2 =  unit
  let ignore _ = ()
  let cut = ()
  let fst = fst
  let snd = snd
  let admit () = ()
  let _assume () = ()
  let _assert x = ()
  let magic () = failwith "no magic"
  let unsafe_coerce x = Obj.magic x
  let op_Negation x = not x

  let op_Addition x y = x + y
  let op_Equality x y = x = y
  let op_disEquality x y = x<>y
  let op_AmpAmp x y = x && y
  let op_BarBar x y  = x || y
  let uu___is_Nil l = l = [] (*consider redefining List.isEmpty as this function*)
  let uu___is_Cons l = not (uu___is_Nil l)
  let strcat x y = x ^ y
  let uu___is_Some = function (*consider redefining Option.isSome as this function*)
      | Some _ -> true
      | None -> false
  let uu___is_None o = not (uu___is_Some o)
  let raise e = raise e

  let ___Some___v x = match x with
    | Some v -> v
    | None   -> failwith "impossible"

  type ('a, 'b) either =
    | Inl of 'a
    | Inr of 'b

  let uu___is_Inl = function
    | Inl _ -> true
    | _     -> false

  let uu___is_Inr x = not (uu___is_Inl x)

  let ___Inl___v x = match x with
    | Inl v -> v
    | _     -> failwith "impossible"

  let ___Inr___v x = match x with
    | Inr v -> v
    | _     -> failwith "impossible"

  let string_of_bool = string_of_bool
  let string_of_int = Z.to_string

  type ('a, 'b) l__DTuple2 =
    | MkDTuple2 of unit * unit * 'a * 'b

  type ('a, 'b, 'c) l__DTuple3 =
    | MkDTuple3 of unit * unit * unit * 'a * 'b * 'c

  type ('a, 'b, 'c, 'd) l__DTuple4 =
    | MkDTuple4 of unit * unit * unit * unit * 'a * 'b * 'c * 'd
end
