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
module FStar.DM4F.IFC

(********************************************************************************)
(* Effect (ifc a) : A monad for dynamic information-flow control                *)
(********************************************************************************)

type label =
  | Low
  | High

let ifc (a:Type) = label -> M (option (a * label))

let return_ifc (a:Type) (x:a) : ifc a = fun l -> Some (x, l)
let bind_ifc (a:Type) (b:Type) (f:ifc a) (g: a -> Tot (ifc b)) : ifc b
  = fun l0 -> let fl0 = f l0 in
              match fl0 with
              | None -> None
              | Some (x, l1) ->
                let gxl1 = g x l1 in
                match gxl1 with
                | None -> None
                | Some (y, l2) -> Some(y, l2)

let join l1 l2 = if l1 = High || l2 = High then High else Low

let flows l1 l2 = not(l1=High && l2=Low)

let read (l:label) : ifc bool =
  fun l0 -> Some (true, join l l0)

let write (l:label) (b:bool) : ifc unit =
  fun l0 -> if flows l0 l then Some ((), l0) else None

reifiable new_effect {
  IFC : a:Type -> Effect
  with
       repr         = ifc
     ; bind         = bind_ifc
     ; return       = return_ifc
     ; read  = read
     ; write = write
}

effect Ifc (a:Type) (req:IFC?.pre) (ens:label -> option (a * label) -> GTot Type0) =
  IFC a (fun (h0:label) (p:IFC?.post a) -> req h0 /\
             (forall r. (req h0 /\ ens h0 r) ==> p r))

unfold let lift_pure_exnst (a:Type) (wp:pure_wp a) (h0:label) (p:IFC?.post a) =
  wp (fun a -> p (Some (a, h0)))
sub_effect PURE ~> IFC = lift_pure_exnst

// A simple program using the IFC effect

let xor (b1:bool) (b2:bool) : Tot bool = not (b1 = b2)

val p : unit ->  Ifc unit (requires (fun l   -> True))
                          (ensures  (fun l r -> r = None))
let p () =
  let b1 = IFC?.read Low in
  let b2 = IFC?.read Low in
  IFC?.write Low (b1 && b2);
  let b3 = IFC?.read High in
  IFC?.write High (b1 || b3);
  IFC?.write Low (xor b3 b3)
