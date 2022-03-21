(*
   Copyright 2019 Microsoft Research

   Authors: Nikhil Swamy

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FullReductionInterpreter
open FStar.All
(* This is an implementation of the tagged normalization strategy of
      Full Reduction at Full Throttle: https://dl.acm.org/citation.cfm?id=2178141

   It is intended to serve as an introductory documentation for the
   more extensive implementation for F* itself in
   FStar.TypeChecker.NBE.fs

*)

type index = nat
type atom = nat

// The source language of lambda terms
type term =
  | BV  : index -> term
  | FV  : atom -> term
  | App : term  -> term -> term
  | Lam : term -> term

let rec open_term (t:term) (i:index) (a:atom)
  = match t with
    | BV j ->
      if i = j then FV a else t
    | FV _ ->
      t
    | App t1 t2 ->
      App (open_term t1 i a) (open_term t2 i a)
    | Lam t ->
      Lam (open_term t (i + 1) a)

let rec close_term (t:term) (i:index) (a:atom)
  = match t with
    | BV _ -> t
    | FV b ->
      if a = b then BV i else t
    | App t1 t2 ->
      App (close_term t1 i a) (close_term t2 i a)
    | Lam t ->
      Lam (close_term t (i + 1) a)

let abs (a:atom) (t:term) = Lam (close_term t 0 a)

#push-options "--warn_error -272" //top-level effect
let fresh_atom : unit -> ML atom  =
  let x : ref atom = alloc 0 in
  fun () ->
    let y = !x in
    x := y + 1;
    y
#pop-options

let abs_body (t:term{Lam? t}) =
  let a = fresh_atom () in
  open_term t 0 a

//An internal language of the interpreter denoting terms using
//host-language abstractions Note, we don't aim to prove termination,
//So, we denote functions into divergent functions (t -> Dv t)
noeq
type t =
  | Fun : (t -> ML t) -> t
  | Acc : atom -> list t -> t

let extend_app (hd:t) (arg:t) =
  match hd with
  | Fun f -> f arg
  | Acc atom args -> Acc atom (arg::args)

module L = FStar.List.Tot

let rec translate (ctx:list t) (x:term)
  : ML t
  = match x with
    | BV i ->
      begin
      match L.nth ctx i with
      | None ->
        failwith "Unbound variable"
      | Some t ->
        t
      end
    | FV a ->
      Acc a []
    | App x0 x1 ->
      extend_app (translate ctx x0) (translate ctx x1)
    | Lam t ->
      Fun (fun x -> translate (x::ctx) t)

let rec readback (x:t)
  : ML term
  = match x with
    | Acc i [] ->
      FV i
    | Acc i (hd::args) ->
      App (readback (Acc i args)) (readback hd)
    | Fun f ->
      let x = fresh_atom () in
      abs x (readback (f (Acc x [])))

let normalize (x:term) : ML term = readback (translate [] x)
