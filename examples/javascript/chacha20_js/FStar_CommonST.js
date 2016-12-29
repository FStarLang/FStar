/* @flow */

export type ref<T> = T[];

export let read = <T>(x:ref<T>): T => x[0];

export let op_Bang = <T>(x:ref<T>): T => read(x);

export let write = <T>(x:ref<T>): ((y:T) => null) => ((y:T) => {x[0] = y; return null});

export let op_Colon_Equals = <T>(x:ref<T>): ((y:T) => null) => ((y:T) => write(x)(y));

export let alloc = <T>(contents:T): ref<T> => [contents];

export let recall: (<T>(r:T) => null) = (r) => null;

export let get = () => null;