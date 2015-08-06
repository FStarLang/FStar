type ('a, 'b, 'c) ordmap = ('a, 'b) BatMap.t

let empty _ = BatMap.empty					 
let const_on g s x = OrdSet.fold g (fun y m -> BatMap.add y x m) s BatMap.empty
let select _ k m = if BatMap.mem k m then Some (BatMap.find k m) else None
let update _ k v m = BatMap.add k v m
let contains _ k m = BatMap.mem k m
let remove _ k m = BatMap.remove k m			    
let choose _ m = if not (BatMap.is_empty m) then Some (BatMap.choose m) else None
let size _ m = BatMap.cardinal m    				   
