module FStarC.EditDist
#push-options "--MLish --MLish_effect FStarC.Effect"

open FStarC.Effect

val edit_distance (s1 s2 : string) : int
