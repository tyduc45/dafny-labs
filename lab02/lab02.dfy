/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 2  (Week 3) -- Recursion over Lists and Trees
   Covers material from Lectures 4 and 5.
   ============================================================

   HOW TO USE THIS FILE
   --------------------
   Open this file in VS Code with the Dafny extension running.

   As in Lab 1, most exercises leave a function without a body, or a
   lemma whose claim (its "ensures") you must write. A red squiggle in
   the Problems pane means there is work to do. YOUR JOB is to make the
   file error-free: every function defined, every lemma checked.

   A theme this week: EVERY lemma below can be proved with an empty
   body  {} . You write the claim; Dafny finds the induction and does
   the proof for you. You never have to write any proof steps yourself.

   The list datatype and  length ,  append ,  min  are given -- you
   wrote length and append last week, so use them freely.

   Items marked (*) are stretch goals. Ask questions early and often.
   ============================================================ */


// -------- Given (recap from Lecture 4 / Lab 1) --------

datatype list<T> = Nil | Cons(hd : T, tl : list<T>)

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

function min(a : nat, b : nat) : nat
{
  if a < b then a else b
}


/* ------------------------------------------------------------
   PART A -- More recursion over lists   (Lecture 4)
   ------------------------------------------------------------ */

// Exercise 1.
// take(n, l) keeps (at most) the first n elements of l:
//   - taking 0 elements gives Nil;
//   - taking from Nil gives Nil;
//   - taking n from Cons(x, xs) keeps x, then takes n-1 from xs.
function take<T>(n : nat, l : list<T>) : list<T>
requires n <= length(l)
{
  match l
  case Nil => Nil
  case Cons(h , t) => if n == 0 then Nil else Cons(h , take(n - 1 , t))
}
// TODO: give a body


// Exercise 2.
// drop(n, l) discards (at most) the first n elements of l:
//   - dropping 0 elements leaves l unchanged;
//   - dropping from Nil gives Nil;
//   - dropping n from Cons(x, xs) drops x, then drops n-1 from xs.
function drop<T>(n : nat, l : list<T>) : list<T>
{
  match l
  case Nil => Nil
  case Cons(_ , t) => if n == 0 then l else drop(n - 1 , t)
}
// TODO: give a body


// Exercise 3.
// reverse(l) reverses a list. The tidy recursive definition puts the
// head on the END of the reversed tail:
//   reverse(Cons(x, xs)) == append(reverse(xs), Cons(x, Nil))
function reverse<T>(l : list<T>) : list<T>
{
  match l 
  case Nil => Nil
  case Cons(x , xs) => append(reverse(xs) , Cons(x , Nil))
}
// TODO: give a body


/* ------------------------------------------------------------
   PART B -- zip and unzip   (Lecture 4)
   ------------------------------------------------------------ */

// Exercise 4.
// zip pairs up two lists element by element, stopping when either
// list runs out:
//   zip(Cons(x, xs), Cons(y, ys)) == Cons((x, y), zip(xs, ys))
//   and Nil whenever either list is Nil.
// Hint: you can match on the pair  (l1, l2)  and use a wildcard  _
// for the "either is Nil" cases:
function zip<A, B>(l1 : list<A>, l2 : list<B>) : list<(A, B)>
{
  match (l1 , l2)
  case (_, Nil)  => Nil
  case (Nil , _) => Nil
  case (Cons(x,xs) , Cons(y,ys)) => Cons((x,y) , zip(xs , ys))
}
// TODO: give a body


// Exercise 5.
// unzip is the reverse operation: it splits a list of pairs back into
// a pair of lists.
//   unzip(Nil) == (Nil, Nil)
//   unzip(Cons((x, y), rest)) == ??
// Hint: you can destructure with  var (xs, ys) := unzip(rest);
function unzip<A, B>(l : list<(A, B)>) : (list<A>, list<B>)
{
  match l
  case Nil => (Nil,Nil)
  case Cons((x , y) , rest) => var (xs , ys) := unzip(rest); (Cons(x , xs) , Cons(y , ys))
}
// TODO: give a body


// Exercise 6.
// Our zip above quietly throws elements away when the two lists differ
// in length. zipPartial is a stricter version that pairs up ALL the
// elements -- it only makes sense when the two lists are the same
// length.

// You might complete it using the constructor test  .Nil?  and the
// selectors  .hd  and  .tl :
//     if l1.Nil? then Nil
//     else Cons((l1.hd, l2.hd), zipPartial(l1.tl, l2.tl))
// Dafny will squiggle on  l2.hd : it cannot see that l2 is non-empty,
// so the selector might be invalid. Add a  requires  clause that rules
// this out. Think about what has to be true of the two lengths.
function zipPartial<A, B>(l1 : list<A>, l2 : list<B>) : list<(A, B)>
 requires length(l1) == length(l2)
{
  if l1.Nil? then Nil 
  else Cons((l1.hd , l2.hd), zipPartial(l1.tl, l2.tl))
}


/* ------------------------------------------------------------
   PART C -- Lemmas: let Dafny do the induction   (Lecture 5)
   ------------------------------------------------------------ */

// Exercise 7.  (induction over the numbers)
// sumUpTo(n) adds up  0 + 1 + 2 + ... + n . Its well-known closed form
// is  n*(n+1)/2 . To keep everything in whole numbers you can double it.
// Write the ensures for
//     2 * sumUpTo(n) == n * (n + 1)
// or
//     sumUpTo(n) == ... / 2
// and leave the body empty: Dafny proves it by induction on n, exactly
// like the example you saw in the lecture.
function sumUpTo(n : nat) : nat
{
  if n == 0 then 0 else n + sumUpTo(n - 1)
}

lemma triangle(n : nat)
  ensures sumUpTo(n) == n * (n + 1) / 2// TODO: write the ensures
{}

// WORKED EXAMPLE -- read this, nothing to do.
// The length of an append is the sum of the lengths. Again the empty
// body: Dafny finds the induction (this time over a list) by itself.
lemma lengthAppend<T>(l1 : list<T>, l2 : list<T>)
  ensures length(append(l1, l2)) == length(l1) + length(l2)
{}

// Exercise 8.
// State and prove: the length of  take(n, l)  is  min(n, length(l)) .
// Write the ensures; leave the body empty and check Dafny is happy.
lemma takeLength<T>(n : nat, l : list<T>)
requires n <= length(l)
ensures length(take(n , l)) == min(length(l) , n)
  // TODO: write the ensures
{}

// Exercise 9.
// State and prove: the length of  drop(n, l)  is ??
//   (You may need to write your own helper function for this.)
function max(a : int , b : int) : int
{
  if a > b then a else b
}

lemma dropLength<T>(n : nat, l : list<T>)
ensures length(drop(n , l)) == max(length(l) - n, 0)
  // TODO: write the ensures
{}

// Exercise 10.
// take and drop fit back together: appending  take(n, l)  and
//  drop(n, l)  gives back  l .
lemma takeDropAppend<T>(n : nat, l : list<T>)
requires n <= length(l)
ensures append(take(n , l) , drop(n,l)) == l
  // TODO: write the ensures
{}

// Exercise 11.  (unzip lengths)
// Unzipping a list of pairs gives two lists, each the same length as
// the original. The result of unzip is a pair, so refer to its parts
// as  unzip(l).0  and  unzip(l).1, or pattern match with
// ensures var(l1,l2) := unzip(l); ...
lemma unzipLength<A, B>(l : list<(A, B)>)
ensures var (l1 , l2) := unzip(l);length(l1) == length(l2)
  // TODO: write the ensures (two of them)
{}

// Exercise 12.  (zipPartial length)
// Because zipPartial pairs up ALL elements, its result has exactly the
// same length as its inputs. Write the ensures for it.
//     length(zipPartial(l1, l2)) == ??
// Note: this lemma mentions zipPartial, so it must satisfy zipPartial's
// precondition -- you will need the same  requires  clause here too.
lemma zipPartialLength<A, B>(l1 : list<A>, l2 : list<B>)
requires length(l1) == length(l2)
ensures length(zipPartial(l1, l2)) == length(l1)
  // TODO: add the same requires as zipPartial, then write the ensures
{}


/* ------------------------------------------------------------
   PART D -- Recursion over trees   (Lectures 4 & 5)
   ------------------------------------------------------------ */

// A binary tree with a value of type T at every internal node.
datatype tree<T> = Leaf | Node(left : tree<T>, val : T, right : tree<T>)

// Exercise 13.
// treeSize counts the internal (Node) nodes: a Leaf has size 0; a Node
// has size 1 plus the sizes of its two subtrees.
function treeSize<T>(t : tree<T>) : nat
{
  match t 
  case Leaf => 0
  case Node(l ,v ,r) => 1 + treeSize(l) + treeSize(r)
}
// TODO: give a body


// Exercise 14.
// mirror reflects a tree left-to-right: at each Node, swap the two
// subtrees (recursively) and keep the value.
function mirror<T>(t : tree<T>) : tree<T>
{
  match t 
  case Leaf => Leaf
  case Node(l,v,r) => Node(mirror(r) , v , mirror(l))
}
// TODO: give a body


// Exercise 15.
// Mirroring does not change the number of nodes. Write the ensures for
//     treeSize(mirror(t)) == ??
lemma mirrorSize<T>(t : tree<T>)
ensures treeSize(mirror(t)) == treeSize(t)
  // TODO: write the ensures
{}

// Exercise 16.
// Mirroring twice gets you back where you started. Write the ensures
// clause capturing this.
lemma mirrorMirror<T>(t : tree<T>)
ensures mirror(mirror(t)) == t
  // TODO: write the ensures
{}

// Exercise 17.
// maxDepth(t) is the length of the longest path from the root down to a
// leaf: a Leaf has depth 0; a Node is 1 plus the LARGER of its two
// subtree depths. You will need a  max  function on ints first -- you
// have seen how to write one in lectures; add it above this exercise.
function maxDepth<T>(t : tree<T>) : nat
{
  match t 
  case Leaf => 0
  case Node(l , v , r) => 1 + max(treeSize(l) , treeSize(r))
}
// TODO: define max (above), then give maxDepth a body


// Exercise 18.
// maxDepth and treeSize are not independent: for EVERY tree, one of
// them stands in a fixed relation to the other (there are multple
// solutions here).

// Work out one such relation, and write it as the ensures, using
// maxDepth(t) and treeSize(t). Leave the body empty.
// If Dafny rejects your claim, it is not true of every tree --
// try a different relation until it holds.
lemma depthAndSize<T>(t : tree<T>)
ensures maxDepth(t) <= treeSize(t)
  // TODO: state a relation between maxDepth(t) and treeSize(t)
{}

// ============================================================
// End of Lab 2. If everything is green, well done!
// ============================================================
