module Calc.Spec

(** State machine specification for calculator **)

open Calc.Wire
module L = FStar.List.Tot

type calc_stack = list int

let max_stack_size = 10

(** State transition function **)
val step (s:calc_stack) (req:request) : calc_stack & response

let step s req =
  match req with
  | Push x ->
      if L.length s >= max_stack_size
      then (s, Error)  // Stack overflow - return error
      else (x :: s, Ok)
  
  | Peek ->
      begin match s with
      | [] -> (s, Error)  // Stack underflow
      | x :: _ -> (s, Result x)
      end
  
  | Add ->
      begin match s with
      | x :: y :: rest -> (((x + y) % 4294967296) :: rest, Ok)  // Modular add (32-bit)
      | _ -> (s, Error)  // Stack underflow
      end
  
  | Sub ->
      begin match s with
      | x :: y :: rest -> (((y - x) % 4294967296) :: rest, Ok)  // Modular sub
      | _ -> (s, Error)  // Stack underflow
      end
  
  | Mul ->
      begin match s with
      | x :: y :: rest -> (((x * y) % 4294967296) :: rest, Ok)  // Modular mul
      | _ -> (s, Error)  // Stack underflow
      end
  
  | Div ->
      begin match s with
      | x :: y :: rest ->
          if x = 0
          then (s, Error)  // Division by zero
          else ((y / x) :: rest, Ok)  // Integer div doesn't wrap
      | _ -> (s, Error)  // Stack underflow
      end

(** Run multiple operations **)
let rec run (s:calc_stack) (reqs:list request) 
  : Tot (calc_stack & list response) (decreases reqs) =
  match reqs with
  | [] -> (s, [])
  | req :: rest ->
      let (s', resp) = step s req in
      let (s'', resps) = run s' rest in
      (s'', resp :: resps)
