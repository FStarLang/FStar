module Bug4104

(* Regression test for #4104: functions with erasable result types
   (e.g. llist a 0 -> unit) must not be erased to () during extraction. *)

open FStar.List
open FStar.All

noeq type serializer (a:Type0) =
{
  serialize: a -> list int;
}

val serializer_pair (#t1 #t2: Type0) (ser1: serializer t1) (ser2: serializer t2) : serializer (t1 & t2)
let serializer_pair ser1 ser2  =
  { serialize = fun (x,y) -> List.append (ser1.serialize x) (ser2.serialize y) }

let serializer_ghost : serializer unit =
  { serialize = (fun () -> []) }

let serializer_int : serializer int =
  { serialize = (fun x -> [x]) }

let serializer_bij (#t1 #t2: Type0) (bij: (t1 -> t2) & (t2 -> t1) { (forall (x:t1). bij._2(bij._1(x)) == x) /\ (forall (x:t2).bij._1(bij._2(x)) == x) }) (ser: serializer t1) : serializer t2 =
  { serialize = (fun x -> ser.serialize (bij._2 x)) }

let rec serializer_list_n (#a: Type0) (ser: serializer a) (n: nat) :
  serializer (llist a n)=
    if n = 0 then
      serializer_bij ((fun () -> [] <: llist a 0), (fun ([]: llist a 0) -> ())) serializer_ghost
    else
      serializer_bij ((fun ((x,y) : a & llist a (n-1)) -> x::y <: llist a n),
                      (fun (x::y : llist a n) -> (x,y) <: a & llist a (n-1)))
        (serializer_pair ser (serializer_list_n ser (n-1)))

let main () : ML unit =
  let ser = serializer_list_n serializer_int 1 in
  if ser.serialize [1] = [1] then
     ()
  else
     failwith "Bug4104: serializer produced wrong result"

let _ = main ()
