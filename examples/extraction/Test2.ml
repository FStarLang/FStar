
let rec mult = (fun ( a  :  Test1.nnat ) ( b  :  Test1.nnat ) -> (match (a) with
| Test1.O -> begin
(Obj.magic Test1.O)
end
| Test1.S (a') -> begin
(Obj.magic (Test1.add (Obj.magic b) (Obj.magic (mult a' b))))
end))




