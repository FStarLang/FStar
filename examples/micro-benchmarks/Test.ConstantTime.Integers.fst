module Test.ConstantTime.Integers
open FStar.Integers
open FStar.IFC
open FStar.ConstantTime.Integers


/// Overloading `+` for math integers
let ex0 (x:int) (y:int) = x + y

/// Overloading `+` for math integers
let ex0_1 (x:Prims.int) (y:Prims.int) = x + y

/// Overloading `+` for machine integers
let ex0_2 (x:uint_32) (y:uint_32) = x +% y

/// And also for monomorpic secret integers
///    s_uint32 = t (Secret hacl_label (Unsigned W32))
let ex1 (x:s_uint32) (y:s_uint32) = x +% y


/// But, you can also work with label-polymorphic code
[@mark_for_norm]
unfold
let l_uint32 #sl (l:lattice_element sl) =
  t (Secret l (Unsigned W32))

/// Like so ...
let ex_poly #sl (#l:lattice_element sl) (x:l_uint32 l) (y:l_uint32 l) =
  x +% y

/// And extraction result follow, with remarks inlined preficed by "NS:"

(*

$ fstar --codegen OCaml --extract Test.ConstantTime.Integers Test.ConstantTime.Integers.fst
$ cat Test_ConstantTime_Integers.ml

open Prims

//NS: overloading on math integers resolved to Prims
let (ex0 : Prims.int -> Prims.int -> Prims.int) = fun x  -> fun y  -> x + y

//NS: overloading on fixed secret integers resolved to
//    the functions in the abstraction layer
//    Given support for cross-module inlining
//    (as a replacement for --expose_interfaces)
//    we should expect this to resolve to FStar.UInt32.addition_mod
let (ex1 :
  FStar_ConstantTime_Integers.s_uint32 ->
    FStar_ConstantTime_Integers.s_uint32 ->
      (unit,unit,unit) FStar_ConstantTime_Integers.secret_int)
  =
  fun x  ->
    fun y  ->
      FStar_ConstantTime_Integers.addition_mod () ()
        (FStar_Integers.Unsigned FStar_Integers.W32) x y

type ('Asl,'Al) l_uint32 =
  (unit,unit,unit) FStar_ConstantTime_Integers.secret_int


//NS: label-polymorphic code is extracted just like
//    the monomorphic `ex1`,
//    except we have additional unit arguments for the erased
//    lattice and lattice element.
//    Kremlin should be able to remove these redundant arguments, though.
let (ex_poly :
  unit ->
    unit ->
      (unit,unit,unit) FStar_ConstantTime_Integers.secret_int ->
        (unit,unit,unit) FStar_ConstantTime_Integers.secret_int ->
          (unit,unit,unit) FStar_ConstantTime_Integers.secret_int)
  =
  fun sl  ->
    fun l  ->
      fun x  ->
        fun y  ->
          FStar_ConstantTime_Integers.addition_mod () ()
            (FStar_Integers.Unsigned FStar_Integers.W32) x y
*)
