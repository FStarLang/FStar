module Steel.PCMReference

let read r v0 = as_action (sel_action FStar.Set.empty r v0)
let write r v0 v1 = as_action (upd_action FStar.Set.empty r v0 v1)
let alloc x = as_action (alloc_action FStar.Set.empty x)
let free r x = as_action (free_action FStar.Set.empty r x)

val split' (#a:Type)
          (#p:pcm a)
          (r:ref a p)
          (v0:erased a)
          (v1:erased a{composable p v0 v1})
  : SteelT unit (pts_to r (op p v0 v1))
                (fun _ -> pts_to r v0 `star` pts_to r v1)

let split' #a #p r v0 v1 = as_action (split_action FStar.Set.empty r v0 v1)

let split #a #p r v v0 v1 =
  change_slprop (pts_to r v) (pts_to r (op p v0 v1)) (fun _ -> ());
  split' r v0 v1

let gather r v0 v1 = as_action (gather_action FStar.Set.empty r v0 v1)
let witness r fact v _ = as_action (Steel.Memory.witness FStar.Set.empty r fact v ())
let recall #a #pcm #fact r v = as_action (Steel.Memory.recall #a #pcm #fact FStar.Set.empty r v)

let select_refine #a #p r x f = as_action (Steel.Memory.select_refine Set.empty r x f)

let upd_gen #a #p r x y f = as_action (Steel.Memory.upd_gen Set.empty r x y f)
