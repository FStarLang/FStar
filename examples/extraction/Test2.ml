
let rec mult = (fun ( a  :  Test1.nnat ) ( b  :  Test1.nnat ) -> (match (a) with
| Test1.O -> begin
Test1.O
end
| Test1.S (a') -> begin
(Test1.add b (mult a' b))
end))




