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
module EMB = FStarC.Syntax.Embeddings
module NBE = FStarC.TypeChecker.NBETerm
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util

(* NB: Eta expanding trips typeclass resolution *)
let mymon = writer (list primitive_step)

let bounded_arith_ops_for (k : machint_kind) : ML (mymon unit) =
  let mod_name = module_name_for k in
  let nm s = (PC.p2l ["FStar"; module_name_for k; s]) in
  (* Operators common to all *)
  (* [add], [sub] and [mul] have a precondition (no overflow) in every
     FStar.[U]IntN, and so take a proof argument that the step must account
     for; see [with_extra_args].  The modular and underspecified variants,
     the bitwise operators and the comparisons do not. *)
  emit [
    mk1 0 (nm "v") (v #k);

    (* basic ops supported by all *)
    with_extra_args 1 <| mk2 0 (nm "add") (fun (x y : machint k) -> make_as x (v x + v y));
    with_extra_args 1 <| mk2 0 (nm "sub") (fun (x y : machint k) -> make_as x (v x - v y));
    with_extra_args 1 <| mk2 0 (nm "mul") (fun (x y : machint k) -> make_as x (v x * v y));

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
      to choose the right instances.  They also have a precondition (the shift
      is smaller than the width), hence the extra argument. *)
      with_extra_args 1 <|
      mk2 0 (nm "shift_left")  (fun (x : machint k) (y : machint UInt32) ->
                                 make_as x (E.logand (E.shift_left (v x) (v y)) (mask k)));
      with_extra_args 1 <|
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

(* Simplification steps (see [Cfg.simplification_steps]) deciding the range
   predicates [FStar.UInt.size x n] and [FStar.Int.size x n] when [x] and [n]
   are integer constants.  A machine-integer literal such as [4096ul] is
   [FStar.UInt32.uint_to_t 4096] once its [unfold] wrapper is unfolded, and
   typing that application leaves the guard [FStar.UInt.size 4096 32]: these
   steps decide such guards without the SMT solver.

   Being simplification steps, they do not make [size] a primitive, so they
   do not stop it from being unfolded.  The ranges are compared through bit
   lengths, so as not to compute [pow2 n] for a large constant [n]. *)
let rec bit_length (x:int) : int = if x <= 0 then 0 else 1 + bit_length (x / 2)

(* [FStar.UInt.fits x n]: [0 <= x <= pow2 n - 1] *)
let uint_fits (x n : int) : option bool =
  if n < 0 then None
  else Some (x >= 0 && bit_length x <= n)

(* [FStar.Int.fits x n]: [-(pow2 (n-1)) <= x <= pow2 (n-1) - 1] *)
let int_fits (x n : int) : option bool =
  if n <= 0 then None
  else if x >= 0 then Some (bit_length x <= n - 1)
  else Some (bit_length (- x - 1) <= n - 1)

let size_step (lid : Ident.lid) (fits : int -> int -> option bool) : primitive_step =
  let as_prop (b:bool) : EMB.abstract_term =
    EMB.Abstract (if b then U.t_true else U.t_false)
  in
  let as_nbe_prop (b:bool) : NBE.abstract_nbe_term =
    NBE.AbstractNBE (NBE.mkFV (S.lid_as_fv (if b then PC.true_lid else PC.false_lid) None) [] [])
  in
  mk2' 0 lid
    (fun (x n : int) -> Option.map as_prop (fits x n))
    (fun (x n : int) -> Option.map as_nbe_prop (fits x n))

let simplify_ops : list primitive_step = [
  size_step (PC.p2l ["FStar"; "UInt"; "size"]) uint_fits;
  size_step (PC.p2l ["FStar"; "Int"; "size"]) int_fits;
]
