module Bug715

let cont (a:Type0) = (a -> M Type0) -> M Type0

let return (a:Type0) (x:a) : cont a = fun (p : a -> M Type0) -> p x

let bind (a:Type0) (b:Type0)
         (m : cont a) (f : a -> Tot (cont b)) (k : b -> M Type0) : M Type0 =
  (* m (fun (x:a) -> f x k) -- This variant causes:
    unknown(0,0-0,0) : Error
    Variable "uu___#2279" not found
  *)
  let mm : cont a = m in mm (fun (x:a) -> let fx : cont b = f x in fx k)

reifiable new_effect {
  CONT: Type -> Effect
  with repr = cont
     ; return = return
     ; bind = bind
}

(*
[hritcu@detained bug-reports]$ fstar.exe bug.fst
Error: Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Invalid_argument("map2: Different_list_size")
*)
