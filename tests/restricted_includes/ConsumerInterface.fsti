module ConsumerInterface

(**** Opening a type *)
// Importing an inductive `a_type` will implicitely import each data
// constructors and each associated desugared record types (here,
// `a_type` as a constructor `Type3` with a record payload: the
// implicit corresponding record type will be imported).
open DefinitionsInterface {a_type}

// `a_type` and its constructors are available
let _ = a_type
let _ = AType1 0 1
let _ = AType2 "hi"
let _ = AType3 { a_type_C_field1 = 3
               ; a_type_C_field2 = DefinitionsInterface.BType1 (* BType1 is not in scope *) }

// The automatically generated type `a_type__AType3__payload` is available as well
let _ = a_type__AType3__payload
let _ = Mka_type__AType3__payload
let _ = { a_type_C_field1 = 3
        ; a_type_C_field2 = DefinitionsInterface.BType1 (* BType1 is not in scope *) }

// Fields projectors are imported
let _ = (AType1?.a1, AType2?._0, AType3?._0)

// The constructors of `a_type` are imported:
let _ = (AType1, AType2, AType3)

// Fields names are imported correctly
let _ = fun x -> x.a_type_C_field1

// Other definitions are not visible:
[@@expect_failure [72]] let _ = a_record
[@@expect_failure [72]] let _ = fn_example
[@@expect_failure [72]] let _ = b_type
[@@expect_failure [72]] let _ = BType1
[@@expect_failure [72]] let _ = BType2
[@@expect_failure [72]] let _ = BType3

(**** Include works as well *)
// Exactly the same syntax and expressivity works for `include` as
// well.
include DefinitionsInterface {a_type}

(**** Renaming *)
include DefinitionsInterface {AType2 as AnotherNicerName}
include DefinitionsInterface {BType1 as RenamedBType1}
include DefinitionsInterface {BType2}
include DefinitionsInterface {fn_example as fn_renamed}

let _: a_type = AnotherNicerName "hello"

(**** Missing names or redundant names *)
// If a include or open exposes missing redundant names, this is an error.
[@@expect_failure [47]] open DefinitionsInterface {AType2 as AType1, AType1}
[@@expect_failure [47]] open DefinitionsInterface {AType1, AType1}
[@@expect_failure [47]] open DefinitionsInterface {a_type, AType1}

(**** Opening a module anonymously *)
// Let's first bring in scope the method `to_int` of the typeclass `to_int_tc`:
open TypeclassDefinition {to_int}

// The module `TypeclassInstance` defines an instance of `to_int_tc`
// for `int`. I can open it without exposing any name into my scope:
open TypeclassInstance {}

// Now, I can use `to_int` on int:
let _ = assert (to_int 3 == 3)

