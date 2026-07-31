open Prims
type 'ty seq = 'ty Prims.list
let length (uu___ : 'ty seq) : Prims.nat=
  Obj.magic FStar_List_Tot_Base.length uu___
let empty (uu___ : unit) : 'ty seq= (fun uu___ -> Obj.magic []) uu___
let singleton (uu___ : 'ty) : 'ty seq= (fun v -> Obj.magic [v]) uu___
let index (s : 'ty seq) (i : Prims.nat) : 'ty=
  FStar_List_Tot_Base.index (Obj.magic s) i
let op_Dollar_At (uu___ : unit) : 'uuuuu seq -> Prims.nat -> 'uuuuu= index
let build (uu___1 : 'ty seq) (uu___ : 'ty) : 'ty seq=
  (fun s v -> Obj.magic (FStar_List_Tot_Base.append (Obj.magic s) [v]))
    uu___1 uu___
let op_Dollar_Colon_Colon (uu___ : unit) :
  'uuuuu seq -> 'uuuuu -> 'uuuuu seq= build
let append (uu___1 : 'ty seq) (uu___ : 'ty seq) : 'ty seq=
  Obj.magic FStar_List_Tot_Base.append uu___1 uu___
let op_Dollar_Plus (uu___ : unit) : 'uuuuu seq -> 'uuuuu seq -> 'uuuuu seq=
  append
let update (s : 'ty seq) (i : Prims.nat) (v : 'ty) : 'ty seq=
  let uu___ = FStar_List_Tot_Base.split3 (Obj.magic s) i in
  match uu___ with
  | (s1, uu___1, s2) ->
      append (Obj.magic s1) (append (Obj.magic [v]) (Obj.magic s2))
let take (uu___1 : 'ty seq) (uu___ : Prims.nat) : 'ty seq=
  (fun s howMany ->
     let uu___ = FStar_List_Tot_Base.splitAt howMany (Obj.magic s) in
     match uu___ with | (result, uu___1) -> Obj.magic result) uu___1 uu___
let drop (uu___1 : 'ty seq) (uu___ : Prims.nat) : 'ty seq=
  (fun s howMany ->
     let uu___ = FStar_List_Tot_Base.splitAt howMany (Obj.magic s) in
     match uu___ with | (uu___1, result) -> Obj.magic result) uu___1 uu___
let rank (v : 'ty) : 'ty= v
