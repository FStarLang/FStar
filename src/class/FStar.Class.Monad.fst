module FStar.Class.Monad

open FStar.Compiler
open FStar.Compiler.Effect

let rec mapM f l =
  match l with
   | [] -> return []
   | x::xs ->
      let! y = f x in
      let! ys = mapM f xs in
      return (y::ys)

let rec foldM_left f e xs =
  match xs with
  | [] -> return e
  | x::xs ->
    let! e' = f x e in
    foldM_left f e' xs

let rec foldM_right f xs e =
  match xs with
  | [] -> return e
  | x::xs ->
    let! e' = foldM_right f xs e in
    f x e'
