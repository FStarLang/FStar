module X86Interpreter

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.Int.Cast
open FStar.UInt8
open FStar.UInt32
open FStar.Buffer
open Ast
open FStar.List

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let u32 = UInt32.t
let u8 = UInt8.t
let uint32s = buffer u32
let bytes = buffer u8

let rec interpret program = begin match program with
  | Skip -> IO.print_string "This a hello from Skip\n" 
  | Store (ea, ed)
  | Load  (ea, ed)-> IO.print_string "This a hello from Load/Store \n"
  | Seq li -> iter interpret li 
  | _   -> IO.print_string "Unsupported instruction *\n"
end

