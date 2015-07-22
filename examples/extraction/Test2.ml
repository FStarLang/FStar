
let rec mult = (fun ( a  :  Test1.nnat ) ( b  :  Test1.nnat ) -> (match (a) with
| O -> begin
(Obj.magic O)
end
| S (a') -> begin
(Obj.magic (add (Obj.magic b) (Obj.magic (mult a' b))))
end))




