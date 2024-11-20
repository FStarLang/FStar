module FStarC.Class.HasRange

open FStarC.Compiler.Range

instance hasRange_range : hasRange range = {
  pos = id;
  setPos = (fun r _ -> r); // not really used
}