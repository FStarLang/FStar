/* @flow */

export let read = <T>(x:T): T => x;

export let op_Bang = <T>(x:T): T => read(x);

export let write = <T>(x:T): ((y:T) => null) => ((y:T) => {x = y; return null});

export let op_Colon_Equals = <T>(x:T): ((y:T) => null) => ((y:T) => write(x)(y));

export let uid = 0;

export let alloc = <T>(contents:T): T => contents;

export let recall: (<T>(r:T) => null) = (r) => null;

export let get = () => null;