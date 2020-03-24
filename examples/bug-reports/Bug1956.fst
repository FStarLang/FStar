module Bug1956

%Fail
let xx : squash False = ()

// This can succeed if `xx` leaks into the SMT context for this query
%Fail
let _ = assert False
