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
module Bug424

open FStar.ST

assume new type f (t:Type)

// making this opaque lets the program check
type t (u:unit) = x:int{u = ()}

noeq type box = | B: v:f (t ()) -> box

val get: b:box -> St (f (t ()))

(* Succeeds *)
// let get b = b.v

(* Succeeds *)
// assume val recall_type: a:Type -> x:a -> Tot unit
// let get b = recall_type (f _) b.v; let r = b.v in r

(* Fails immediately with 'Unknown assertion failed' *)
let get b = let r = b.v in r

(*
This is the crucial assertion that succeeds:
(not (forall ((@t Type) (@x Term))
        (implies (and (HasKind @t Kind_arrow_1603)
                      (HasType @x heap)
                      (forall ((@y Term) (@z Term))
                         (implies (and (HasType @y (Bug.f Typ_refine_1602))
                                       (HasType @z heap))
                                  (Valid (ApplyTE (ApplyTE @t @y) @z)))
                      ) // forall
                 ) // and
                 (forall ((@r Term))
                    (implies (and (HasType @r (Bug.f Typ_refine_1602))
                                  (= @r (Bug.B.v b___8_8)))
                             (Valid (ApplyTE (ApplyTE @t @r) @x))

                    ) // implies
                 ) // forall
        ) // implies
     ) // forall
) // not

This is the crucial assertion that fails:

(not (forall ((@t Type) (@x Term))
        (implies (and (HasKind @t Kind_arrow_1603)
                      (HasType @x heap)
                      (forall ((@y Term) (@z Term))
                         (implies (and (HasType @y (Bug.f Typ_refine_1602))
                                       (HasType @z heap))
                                  (Valid (ApplyTE (ApplyTE @t @y) @z)))
                      ) // forall 
                 ) // and
                 (Valid (ApplyTE (ApplyTE @t (Bug.B.v b___8_8)) @x))
         ) // implies
      ) // forall
) // not

Suffices to prove (HasType (Bug.B.v b___8_8) (Bug.f Typ_refine_1602)), but Z3 says 'unknwon'
to 
(assert (not (HasType (Bug.B.v b___8_8) (Bug.f Typ_refine_1602))))
*)
