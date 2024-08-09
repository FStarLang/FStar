module FStar.TypeChecker.Primops.Range

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Class.Monad

open FStar.TypeChecker.Primops.Base
open FStar.Compiler.Range

module PC = FStar.Parser.Const
module Z = FStar.BigInt

(* Range ops *)

let ops = [
  mk5 0 PC.mk_range_lid (fun fn from_l from_c to_l to_c ->
      mk_range fn (mk_pos (Z.to_int_fs from_l) (Z.to_int_fs from_c))
                  (mk_pos (Z.to_int_fs to_l) (Z.to_int_fs to_c))
  );

  mk2 0 PC.join_range_lid FStar.Compiler.Range.union_ranges;
]
