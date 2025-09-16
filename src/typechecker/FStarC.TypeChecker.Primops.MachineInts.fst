module FStarC.TypeChecker.Primops.MachineInts

(* Primops about machine integers *)

open FStarC
open FStarC.Effect
open FStar.Char
open FStarC.TypeChecker.Primops.Base
module PC = FStarC.Parser.Const

(* We're going full Haskell in this module *)
open FStarC.Class.Monad
open FStarC.Writer
open FStarC.Class.Show

open FStarC.MachineInts
module E = FStarC.Int.Extra

(* NB: Eta expanding trips typeclass resolution *)
let mymon = writer (list primitive_step)

let bounded_arith_ops_for (k : machint_kind) : mymon unit =
  let mod_name = module_name_for k in
  let nm s = (PC.p2l ["FStar"; module_name_for k; s]) in
  (* Operators common to all *)
  let open FStar.Mul in
  emit [
    mk1 0 (nm "v") (v #k);

    (* basic ops supported by all *)
    mk2 0 (nm "add") (fun (x y : machint k) -> make_as x (v x + v y));
    mk2 0 (nm "sub") (fun (x y : machint k) -> make_as x (v x - v y));
    mk2 0 (nm "mul") (fun (x y : machint k) -> make_as x (v x * v y));

    mk2 0 (nm "gt")  (fun (x y : machint k) -> v x >  v y);
    mk2 0 (nm "gte") (fun (x y : machint k) -> v x >= v y);
    mk2 0 (nm "lt")  (fun (x y : machint k) -> v x <  v y);
    mk2 0 (nm "lte") (fun (x y : machint k) -> v x <= v y);
  ];!

  (* Unsigned ints have more operators *)
  let sz = width k in
  let modulus = pow2 sz in
  let mod (x : int) : int = x % modulus in
  if is_unsigned k then
    emit [
      (* modulo operators *)
      mk2 0 (nm "add_mod") (fun (x y : machint k) -> make_as x (mod (v x + v y)));
      mk2 0 (nm "sub_mod") (fun (x y : machint k) -> make_as x (mod (v x - v y)));
      mk2 0 (nm "div")     (fun (x y : machint k) -> make_as x (mod (v x / v y)));
      mk2 0 (nm "rem")     (fun (x y : machint k) -> make_as x (mod (v x % v y)));

      (* bitwise *)
      mk2 0 (nm "logor")  (fun (x y : machint k) -> make_as x (E.logor (v x) (v y)));
      mk2 0 (nm "logand") (fun (x y : machint k) -> make_as x (E.logand (v x) (v y)));
      mk2 0 (nm "logxor") (fun (x y : machint k) -> make_as x (E.logxor (v x) (v y)));
      mk1 0 (nm "lognot") (fun (x : machint k) ->   make_as x (E.logand (E.lognot (v x)) (mask k)));

      (* NB: shift_{left,right} always take a UInt32 on the right, hence the annotations
      to choose the right instances. *)
      mk2 0 (nm "shift_left")  (fun (x : machint k) (y : machint UInt32) ->
                                 make_as x (E.logand (E.shift_left (v x) (v y)) (mask k)));
      mk2 0 (nm "shift_right")  (fun (x : machint k) (y : machint UInt32) ->
                                 make_as x (E.logand (E.shift_right (v x) (v y)) (mask k)));
    ]
  else return ();!

  (* Most unsigneds, except SizeT, have underspec ops *)
  if is_unsigned k && k <> SizeT then
    emit [
      mk2 0 (nm "add_underspec") (fun (x y : machint k) -> make_as x (mod (v x + v y)));
      mk2 0 (nm "sub_underspec") (fun (x y : machint k) -> make_as x (mod (v x - v y)));
      mk2 0 (nm "mul_underspec") (fun (x y : machint k) -> make_as x (mod (v x * v y)));
    ]
  else return ();!

  (* And except for SizeT and UInt128, they have mul_mod *)
  if is_unsigned k && (k <> SizeT && k <> UInt128) then
    emit [
      mk2 0 (nm "mul_mod") (fun (x y : machint k) -> make_as x (mod (v x * v y)));
    ]
  else return ();!

  return ()

let ops : list primitive_step =
  fst <|
  run_writer <|
  (iterM bounded_arith_ops_for all_machint_kinds ;!
   emit [
        (* Single extra op that returns a U32 *)
        mk1 0 PC.char_u32_of_char (fun (c : char) -> let n = Util.int_of_char c in
                                                        MachineInts.mk #UInt32 n None);
   ])
