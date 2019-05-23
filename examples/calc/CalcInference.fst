module CalcInference

let lem () : squash (2 == 1 + 1) = ()

let test1 () : squash (2 == 1 + 1) =
  calc (==) {
    2;
  == { lem () }
    _;
  }

let test2 () : squash (2 == 1 + 1) =
  calc (==) {
    _;
  == { lem () }
    1 + 1;
  }

let test3 () : squash (2 == 1 + 1) =
  calc (==) {
    _;
  == { lem () }
    _;
  }
