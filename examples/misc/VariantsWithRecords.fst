module VariantsWithRecords

(**** General usage *)

/// A record type is declared using the following syntax:
type record = { field1: int; field2: string (* ... *) }

/// A variant type can be of any arity, and can be declared using a
/// few different syntaxes.
type foo =
  (** constructor [A] carries an integer and a string *)
  | A: int -> string -> foo
  (** fields can be named *)
  | B: named:int -> other:string -> foo
  (** for constructor of arity 1, one cam use OCaml's [of] notation *)
  | C of int * string
  (** [D] carries nothing *)
  | D
  (** [E] carries a record *)
  | E { a: int; b: int }

/// Example of a GADT:
type expr: Type -> Type =
  (** [ConstInt] constructs an [expr int] *)
  | ConstInt: int -> expr int
  (** but [ConstStr] constructs an [expr string] *)
  | ConstStr: string -> expr string
  (** [Add] carries a record and constructs a [expr int] *)
  | Add { x: expr int; y: expr int }: expr int
  | StringOfInt { value: expr int }: expr string

let rec eval (e: expr 'a): 'a
  = match e with
  | ConstInt c -> c
  | ConstStr s -> s
  | Add {x; y} -> eval x + eval y
  | StringOfInt {value} -> string_of_int (eval value)

let e = StringOfInt { value = Add { x = ConstInt 3; y = ConstInt 39} }
let _ = assert_norm (eval e == "42")

(**** Desugaring of constructor carrying records *)
/// The type [bar]...
type bar = | X
           | Y { x: int; y: int }
           | Z { z: int; t: int }: bar

/// ...is desugared into the types [bar], [bar__Y__payload] and [bar__Z__payload]:
/// (note: to avoiding name clashes, [']s were added below)
type bar' = | X'
            | Y' of bar'__Y'__payload
            | Z': bar'__Z'__payload -> bar'
and bar'__Y'__payload = { x: int; y: int }
and bar'__Z'__payload = { z: int; t: int }

/// We can actually observe this desugaring by constructing [Y]'s or
/// [Z]'s payloads directly:

let _: bar__Y__payload = {x = 1; y = 2}
let _: bar__Z__payload = {z = 3; t = 4}

/// Note that the desugaring of constructor carrying records doesn't
/// forbid something like [odd] below:
type odd = | Odd {something: int}: string -> odd
let _: odd = Odd {something = 3} "wierd"
