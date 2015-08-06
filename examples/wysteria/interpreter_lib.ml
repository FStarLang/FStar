module OrdSet = struct
    type ('a, 'b) ordset = 'a BatSet.t

    let empty _ = BatSet.empty
    let union _ s1 s2 = BatSet.union s1 s2
    let intersect _ s1 s2 = BatSet.intersect s1 s2
    let mem _ x s = BatSet.mem x s					    
    let choose _ s = BatSet.choose s
    let remove _ x s = BatSet.remove x s
    let size _ s = BatSet.cardinal s			       
    let subset _ s1 s2 = BatSet.subset s1 s2
    let singleton _ x = BatSet.singleton x
    let is_singleton _ s = BatSet.cardinal s = 1
    let insert _ x s = BatSet.add x s
    let fold _ f s a = BatSet.fold f s a
end

module OrdMap = struct
    type ('a, 'b, 'c) ordmap = ('a, 'b) BatMap.t

    let empty _ = BatMap.empty					 
    let const_on g s x = OrdSet.fold g (fun y m -> BatMap.add y x m) s BatMap.empty
    let select _ k m = if BatMap.mem k m then Some (BatMap.find k m) else None
    let update _ k v m = BatMap.add k v m
    let contains _ k m = BatMap.mem k m
    let remove _ k m = BatMap.remove k m			    
    let choose _ m = if not (BatMap.is_empty m) then Some (BatMap.choose m) else None
    let size _ m = BatMap.cardinal m    				   
end
