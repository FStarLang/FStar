(*
   Copyright 2008-2018 Microsoft Research

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

module Locals.Effect

module M = FStar.Map

/// The old layered effect has been replaced by its underlying state monad
/// The locals are modeled as a map, that is threaded through in the state passing style
///
/// It's a total effect, and tests below include some termination checking

noeq
type locals_t'= {
  next:nat;
  m:M.t nat (a:Type0 & a)
}

type locals_t = m:locals_t'{
  forall (i:nat). i >= m.next ==> not (M.contains m.m i)
}

type repr (a:Type) = locals_t -> Pure (a & locals_t)

let return (#a:Type) (x:a) : repr a =
  fun m -> (x, m)

let bind (#a #b:Type) (f:repr a) (g:a -> repr b) : repr b =
  fun m ->
    let (x, m) = f m in
    (g x) m

let (let!) (#a #b : Type) (f : repr a) (g : a -> repr b) : repr b =
  bind f g

let create (a:Type0) (x:a) : repr nat
= fun m ->
    let next = m.next in
    next, {
      next = next + 1;
      m = Map.upd m.m next (| a, x |)
    }

let read (#a:Type0) (n:nat) : repr a
= fun m ->
    assume (dfst (m.m `M.sel` n) == a);
    dsnd (m.m `M.sel` n), m

let write (#a:Type0) (n:nat) (x:a) : repr unit
= fun m ->
    assume (n < m.next);
    (), { m with m = Map.upd m.m n (| a, x |) }

let get () : repr (Map.t nat (a:Type0 & a))
= fun m -> m.m, m

let test () : repr unit =
  let! n1 = create nat 0 in
  let! _n2 = create bool true in
  let! _n3 = create unit () in
  let! v1 = read n1 in
  assume (v1 == 0);
  return ()

let emp_locals = {
  next = 0;
  m = Map.restrict Set.empty (Map.const (| unit, () |))
}

let run_with_locals (#a:Type) (f:unit -> repr a) : Pure a =
  fst (f () emp_locals)

/// Testing some termination

let rec sum (n:nat) : repr nat
= if n = 0 then return 0
  else
    let! s = sum (n - 1) in  //let binding is important, can't write 1 + sum (n - 1), see #881
    return (1 + s <: nat)

module L = FStar.List.Tot

let rec test1 (l:list nat) : repr nat
= match l with
  | [] -> return 0
  | _::tl ->
   let! n = test1 tl in  //let binding is important, can't write 1 + test1 tl, see #881
   return (n + 1 <: nat)

/// Termination check failure

[@@expect_failure]
let rec test2 (l:list nat) : repr nat
= test2 l
