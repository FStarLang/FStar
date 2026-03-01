module FStarC.Class.HasRange
#push-options "--MLish --MLish_effect FStarC.Effect"

open FStarC.Range

instance hasRange_range : hasRange range = {
  pos = id;
  setPos = (fun r _ -> r); // not really used
}