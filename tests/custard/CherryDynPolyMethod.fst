module CherryDynPolyMethod
open FStar.All

(* A monad over [option] reached through a runtime dictionary: its methods
   build [option a] at a type variable, which Cherry would lay out as an
   [option] of boxed values while the caller's is not.  Refused with error
   399 rather than miscompiled. *)
class monad (m:Type->Type) = {
  return : #a:Type -> a -> m a;
  bind : #a:Type -> #b:Type -> m a -> (a -> ML (m b)) -> ML (m b)
}

instance monad_option : monad option = {
  return = (fun x -> Some x);
  bind = (fun o f -> match o with None -> None | Some v -> f v)
}

let rec mapM #m {| monad m |} #a #b (f: a -> ML (m b)) (l:list a) : ML (m (list b)) =
  match l with
  | [] -> return []
  | x :: xs -> bind (f x) (fun y -> bind (mapM f xs) (fun ys -> return (y :: ys)))

noeq type lvm (m:Type->Type) = { lvm_monad : monad m; g : int -> ML (m int) }

instance _lvm_monad (#m:_) (d : lvm m) : Tot (monad m) = d.lvm_monad

let go (#m:Type->Type) (d:lvm m) (l:list int) : ML (m (list int)) = mapM d.g l

let mk () : lvm option = { lvm_monad = monad_option; g = (fun x -> Some (x + 1)) }

let main () : ML unit =
  match go #option (mk ()) [1; 2] with Some [2; 3] -> () | _ -> failwith "bad"
