/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 3  (Week 4) -- Data Structures, Contracts and Termination
   Covers material from Lectures 6 and 7.
   ============================================================

   HOW TO USE THIS FILE
   --------------------
   Open this file in VS Code with the Dafny extension running. A red
   squiggle in the Problems pane means there is work to do.

   This lab is more open than the last two. In Part A you define set
   operations and then state and prove the lemmas that CHARACTERISE how
   they behave (plus one requires-guard). Part B is a bigger piece of
   work: a binary search tree. You are given ONLY English descriptions
   there; translating them into Dafny -- choosing the signatures, the
   bodies, and the lemma statements -- is the exercise.

   Two of the Part B lemmas will NOT go green with an empty  {}  body.
   That is deliberate: they are a first look at proofs, which we take up
   properly next. Each is flagged where it appears.

   Part C (Lecture 7) is an EXTENSION on termination. Items marked (*)
   are stretch goals. Ask questions early and often.
   ============================================================ */


// -------- Given infrastructure (from earlier weeks / Lecture 6) --------

datatype list<T> = Nil | Cons(hd : T, tl : list<T>)
datatype option<V> = None | Some(v : V)

type lset = list<int>   // a set of ints, stored as a list

function length<T>(l : list<T>) : nat
{
  match l
  case Nil => 0
  case Cons(_, xs) => 1 + length(xs)
}

function append<T>(l1 : list<T>, l2 : list<T>) : list<T>
{
  match l1
  case Nil => l2
  case Cons(x, xs) => Cons(x, append(xs, l2))
}

function member(x : int, l : list<int>) : bool
{
  match l
  case Nil => false
  case Cons(y, ys) => x == y || member(x, ys)
}

// Two already-proved helper lemmas you may CALL later if you need them.
lemma lengthAppend<T>(l1 : list<T>, l2 : list<T>)
  ensures length(append(l1, l2)) == length(l1) + length(l2)
{}

lemma member_append(x : int, l1 : list<int>, l2 : list<int>)
  ensures member(x, append(l1, l2)) <==> member(x, l1) || member(x, l2)
{}


/* ------------------------------------------------------------
   PART A -- Set operations and their characterising lemmas
                                                 (Lecture 6)
   ------------------------------------------------------------ */

// Exercise 1.
// insert(x, A) adds x to the set A -- just put it on the front.
function insert(x : int, A : lset) : lset
{
  match A 
  case Nil => Cons(x , Nil)
  case Cons(data , tail) => Cons(x , Cons(data , tail))
}
// TODO: give a body


// Exercise 2.
// delete(x, A) removes EVERY copy of x from A.
function delete(x : int, A : lset) : lset
{
  match A 
  case Nil => Nil 
  case Cons(data , tail) => 
  if (data == x) then delete(x , tail)
  else Cons(data , delete(x , tail))
}
// TODO: give a body


// Exercise 3.
// anyElement(A) returns some element of A. This only makes sense when A
// is non-empty -- otherwise there is no element and  A.hd  is not valid.
// Add a  requires  that rules the empty case out, then return  A.hd .
function anyElement(A : lset) : int
requires A != Nil
{
  A.hd
}
// TODO: add a  requires , then a body


// Exercise 4.
// The lemma that says exactly what insert does to membership: some x is
// a member of  insert(y, A)  precisely when x is the newly-inserted y,
// or x was already a member of A. Write the ensures; {} proves it.
lemma member_insert(x : int, y : int, A : lset)
ensures member(x , insert(y , A)) <==> x == y || member(x, A)
  // TODO: write the ensures  ( member(x, insert(y, A)) <==> ... )
{}


// Exercise 5.
// And the matching lemma for delete: x is a member of  delete(y, A)
// precisely when x is not the deleted y, AND x was already a member of A.
lemma member_delete(x : int, y : int, A : lset)
ensures member(x , delete(y , A)) <==> x != y && member(x , A)
  // TODO: write the ensures
{}


/* ------------------------------------------------------------
   PART B -- Binary search trees   (Lecture 6)
   ------------------------------------------------------------
   You are given the tree type only. Everything else in this part you
   write yourself, from the English. There are no signatures and no
   Dafny below -- work out the types, the bodies and the claims.

   A binary search tree stores integer keys, each with an associated
   value of type V. It is ORDERED: at every node, all keys in the left
   subtree are smaller than the node's key, and all keys in the right
   subtree are larger. (You may assume the trees you are given are
   ordered; you do not have to check it.)
   ------------------------------------------------------------ */

datatype btree<V> = Lf | Node(k : int, value : V, left : btree, right : btree)

// Exercise 6.  Define  size .
//   The number of Node nodes in a tree (a leaf Lf contributes nothing).
function size<V>(tree : btree<V>) : nat
{
  match tree
  case Lf => 0
  case Node(k , v , l , r) => 1 + size(l) + size(r)
}


// Exercise 7.  Define  lookup .
//   Given a tree and a key, return the stored value wrapped as  Some ,
//   or  None  if the key is not in the tree. Use the ordering to search
//   efficiently: compare the wanted key with the node's key -- equal
//   means found; smaller means look in the left subtree; larger means
//   look in the right subtree.

function lookup<V>(key : int , tree : btree<V>) : option<V>
{
  match tree
  case Lf => option.None
  case Node(k , v , l , r) => 
  if (key < k) then lookup(key , l)
  else if(key > k) then lookup(key ,  r)
  else Some(v)
}


// Exercise 8.  Define tree insertion.
//   Given a key, a value and a tree, return the tree updated so that the
//   key maps to the value. If the key is already present, replace its
//   value; if not, add a new node in the correct ordered position.
//   NOTE: you already used the name  insert  in Part A, and Dafny does
//   not allow two functions with the same name -- call this one something
//   else, e.g.  insertT , and use that name in the lemmas below.
function insert_tree<V>(key : int , value  : V , tree : btree<V>) : btree<V>
{
  match tree
  case Lf => Node(key , value , Lf , Lf)
  case Node(k , v , l , r) =>
  if (k == key) then Node(k , value , l , r)
  else if (k > key) then Node(k , v ,insert_tree(key , value , l) , r)
  else Node(k , v , l , insert_tree(key , value , r))
}

// Exercise 9.  Define  keys .
//   Return the list of all keys in the tree, in ascending order: the
//   keys of the left subtree, then this node's key, then the keys of the
//   right subtree. (One of the given helpers builds "a followed by b".)
function keys<V> (tree : btree<V>) : list<int>
{
  match tree
  case Lf => Nil
  case Node(k , v, l , r) =>
  append(keys(l) , Cons(k , keys(r)))
}


// -------- Lemmas about the tree operations --------
// State each of these as a lemma and try to prove it. Unless flagged,
// an empty  {}  body should be enough.

// Exercise 10.
//   Looking up a key straight after inserting it with value v returns
//   exactly  Some(v) .
lemma find_value_after_insert<V>(key : int , value : V , tree : btree<V>)
ensures lookup(key , insert_tree(key , value , tree)) == Some(value)
{}

// Exercise 11.
//   Looking up a key k2 after inserting a DIFFERENT key k1 gives the
//   same answer as looking up k2 in the original tree. (You will need a
//   precondition saying the two keys differ.)
lemma find_key_after_insert_a_different_one<V>(key1 : int , value1 : V , key2 : int , tree : btree<V>)
requires key1 != key2 
ensures lookup(key2 , insert_tree(key1 , value1 , tree)) == lookup(key2 , tree)
{}  

// Exercise 12.
//   Inserting adds at most one node: the size afterwards is no more than
//   one greater than the size before.
lemma size_check_after_insert<V>(key : int, value : V , tree : btree<V>)
ensures size(insert_tree(key , value , tree)) == size(tree) + 1 ||  size(insert_tree(key , value , tree)) == size(tree)
{}

// Exercise 13.  ** FLAGGED: {} is NOT enough here. **
//   Inserting a key that was NOT already present increases the size by
//   exactly one. (Express "not already present" using  member  and your
//   keys function.) Try the empty body first and watch it fail -- this
//   is the kind of fact that needs a real proof. If you want to push on,
//   the given lemma  member_append  is the tool that unlocks it.
lemma size_check_after_insert_not_present<V>(key : int, value : V , tree : btree<V>)
requires member()
ensures size(insert_tree(key , value , tree)) == size(tree) + 1
{}

// Exercise 14.  ** FLAGGED: {} is NOT enough here either **
//   The number of keys of a tree equals its size:  length(keys(t))  is
//   size(t) . The empty body will not close this one either -- to relate
//   the length of the appended key-lists you will need to remind Dafny
//   of the given fact  lengthAppend . (This is a gentle first proof.)
lemma length_key_eq_tree_size<V>(tree : btree<V>)
ensures length(keys(tree)) == size(tree)
{}

/* ------------------------------------------------------------
   PART C -- Termination and  decreases   (Lecture 7)  (*) EXTENSION
   ------------------------------------------------------------
   Each function below is correct, but recurses by counting a variable
   UP towards a bound. Dafny cannot see why that stops, so it squiggles
   the recursive call ("cannot prove termination"). Add a  decreases
   clause giving a quantity that gets SMALLER each call -- think about
   the gap between the counter and its bound.
   ------------------------------------------------------------ */

// Exercise 15.  (*)
// upList(lo, hi) builds the list  [lo, lo+1, ..., hi-1]  by counting
// upward. Add the  decreases  clause that makes Dafny accept it.
function upList(lo : int, hi : int) : list<int>
  requires lo <= hi
  // TODO: add a  decreases  clause
{
  if lo == hi then Nil else Cons(lo, upList(lo + 1, hi))
}

// Exercise 16.  (*)
// fib_loop implements a loop for calculating the n-th Fibonacci
// number, so that fib below can run efficiently. But Dafny
// doesn't see that fib_loop must terminate. Indeed, it doesn't, not for 
// all possible arguments.  In the two contexts where it is called 
// (recursively, and where it is started off in the body of fib),
// it will be fine.  So WHY IS THIS???  

// You will need to add a requires clause to encapsulate that.

/* fi = i'th fib number; fpi = fib number of i - 1 ("previous to i") */
function fib_loop(fi : nat, fpi : nat, i : nat, n : nat) : nat
  // TODO: add a decreases *and* a requires clause
{
  if n == i then fi
  else fib_loop (fi + fpi, fi, i + 1, n)
}

function fib(n:nat) : nat 
{ 
  if n == 0 then 0 
  else fib_loop(1,0,1,n) 
}

// ============================================================
// End of Lab 3. (Parts A and C green; two Part B lemmas are meant
// to resist the empty body -- see you next week for the proofs.)
// ============================================================
