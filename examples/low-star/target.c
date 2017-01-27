
/* Example types */
typedef struct alpha{
  /* ... */
} A;
typedef struct beta{
  /* ... */
} B;

/* Tag type */
typedef char tag;

/* Pairs */
/* Flat structure */
typedef struct pair{
  A fst;
  B snd;
} _Pair;
/* Boxed structure */
typedef _Pair* Pair;


/* Option type */
typedef union _option1 {
  void* None;
  A v;
} _Option1;
typedef _Option1* Option1;

typedef A _Option2;
typedef union option2{
  void* None;
  _Option2* v;
} Option2;

typedef A _Option3;
typedef union option3{
  struct {char tag; void* v;} None;
  struct {char tag; _Option3* v;} Some;
} Option3;

typedef union _option4{
  void* None;
  A v;
} _Option4;
typedef union option4{
  struct {char tag; _Option4* v;} None; /* Does not really make sense, 1 struct  would be better */
  struct {char tag; _Option4* v;} Some;
} Option4;

/* Prefered representation for pattern matching */
typedef union _option5{
  void* None;
  A v;
} _Option5;
typedef struct option5{
  char tag;
  _Option5* v;
} Option5;


/* List type (for recursive types more generally */
/* First possibility */
typedef union _list1 _List1;
typedef _List1* List1;
union _list1{
  void* Nil;
  struct{ A hd; List1 tl;} Cons;
};

/* Second possibility */
typedef struct _list2 _List2;
typedef union list2 List2;
struct _list2{
  A hd;
  List2* tl;
};
union list2{
  void* Nil;
  _List2* Cons;
};
/* Also possible like that :
union list2{
  void* Nil;
  struct{ A hd; List2* tl}* Cons;
}; */

/* With tags, better for pattern matching */
typedef union _list4 _List4;
typedef struct list4 List4;
struct _list4{
  A hd;
  List4* tl;
};
struct list4{
  char tag;
  List4* v;
};

/* Sum type */
typedef union _t{
  void* A;
  void* B; /* With a way to distinguish them for pattern matching */
  struct{ int x;} C;
  struct{ int x; char y;} D;
} _T;
/* First possibility */
typedef _T* T1;
/* Second possibility */
typedef struct t2{
  tag t;
  _T* v;
} T2;

int main(){
  return 0;
}
