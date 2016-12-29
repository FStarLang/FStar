/* @flow */

import * as FStar_Array from "./FStar_Array";

export type seq<T> = T[];

export let create = FStar_Array.create;
export let append = FStar_Array.append;
export let length = FStar_Array.length;
export let index  = FStar_Array.index;
export let eq = FStar_Array.eq;
export let op_At_Bar = FStar_Array.append;

export let createEmpty = () => []; 

export let upd = <T>(s:T[]): ((n:number) => ((v:T) => T[])) => ((n:number) => ((v:T) => {
	s[n] = v;    
	return s;
}));

export let slice = <T>(s:T[]): ((i:number) => ((j:number) => T[])) => ((i:number) => ((j:number) => s.slice(i, i + j)));