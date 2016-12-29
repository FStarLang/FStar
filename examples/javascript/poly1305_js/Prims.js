/* @flow */
export type list<T> = T[];
export type option<T> = ?T;

export type range  = number;
export type nat    = number;
export type pos    = number;
export type b2t<T> = null;

export type prop = any;
/* for partially variants of the operators */
export let op_Multiply = (x:number) => ((y:number) => x * y);
export let op_Subtraction = (x:number) => ((y:number) => x - y);
export let op_Addition = (x:number) => ((y:number) => x + y);
export let op_LessThanOrEqual = (x:number) => ((y:number) => x <= y);
export let op_LessThan = (x:number) => ((y:number) => x < y);
export let op_GreaterThanOrEqual = (x:number) => ((y:number) => x >= y);
export let op_GreaterThan = (x:number) => ((y:number) => x > y);
export let op_Equality = (x:number) => ((y:number) => x == y);
export let op_disEquality = (x:number) => ((y:number) => x != y);
export let op_AmpAmp = (x:boolean) => ((y:boolean) => x && y);
export let op_BarBar = (x:boolean) => ((y:boolean) => x || y);
export let strcat = (x:string) => ((y:string) => x.concat(y));
export let raise = (e:{_tag: string}) : any => {
	let res = (e) => {throw new Error(e._tag);}
	return res;
};

export let is_None = <T>(x:option<T>):boolean => x == null;
export let is_Some = <T>(x:option<T>):boolean => x != null;
export let get_Some = <T>(x:option<T>):T => {
	if (x != null){
		return x;	
	} else {
		throw "This value doesn't match! ";
	}
};

export let mk_Some = <T>(v:T): option<T> => v;
export let mk_None = <T>(): option<T> => null;

export let is_Cons = <T>(x:list<T>): boolean => (x.length > 0);
export let is_Nil  = <T>(x:list<T>): boolean => (x.length == 0);
export let get_Cons_0 = <T>(x:list<T>): T => x[0];
export let get_Cons_1 = <T>(x:list<T>): list<T> => x.slice(1);
export let mk_Cons = <T>(hd:T): ((tl:list<T>) => list<T>) => ((tl:list<T>) => [hd].concat(tl));
export let mk_Nil = <T>():list<T> => [];

export let ___Some___v = <T>(x:option<T>):T => get_Some(x);
export let __proj__Cons__item__tl = <T>(x:list<T>):list<T> => {
	if (x.length > 0){
		return x.slice(1);	
	} else {
		throw "Impossible ";
	}
};

export let pow2 = (x:number):number => Math.pow(2, x);