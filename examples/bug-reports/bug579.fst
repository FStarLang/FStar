module Bug579

open FStar.Constructive

type step : int -> int -> Type =
  | SBeta : e1:int ->
            e2:int ->
            step e1 e2

type typing : int -> int -> Type =
  | TyEqu : #e:int ->
            #t1:int ->
            #t2:int ->
            $ht:typing e t1 ->
                typing e t2

(* This variant works *)
val progress' : #e:int -> #t:int -> h:typing e t ->
               Tot (cexists (fun e' -> step e e')) (decreases h)
let rec progress' #e #t h =
  match h with
    | TyEqu #e #t1 #t2 h1 -> progress' #e #t1 h1

(* This variant doesn't; 2 x could not prove post-condition *)
val progress : #e:int -> #t:int -> h:typing e t ->
               Pure (cexists (fun e' -> step e e'))
                    (requires True)
                    (ensures (fun _ -> True)) (decreases h)
let rec progress #e #t h =
  match h with
    | TyEqu #e #t1 #t2 h1 -> progress #e #t1 h1
