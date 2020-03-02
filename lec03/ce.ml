open QCheck

(** Assignment 1
a. Write a function size : aexp -> int that computes the size of an arithmetic expression.

(What would be a reasonable definition?)

(after sl.13)

b. Using size compute size statistics for the distribution of our generator of arithmetic expressions.

(after sl.42)
 *)
type aexp =
  | X
  | Lit of int
  | Plus of aexp * aexp
  | Times of aexp * aexp

let leafgen = Gen.oneof
                [Gen.return X;
                 Gen.map (fun i -> Lit i) Gen.int]

(* a fixed-point generator without weights *)
let mygen'' =
  Gen.sized (Gen.fix (fun recgen n -> match n with
    | 0 -> leafgen
    | n ->
      Gen.oneof
	      [leafgen;
	       Gen.map2 (fun l r -> Plus(l,r)) (recgen(n/2)) (recgen(n/2));
	       Gen.map2 (fun l r -> Times(l,r)) (recgen(n/2)) (recgen(n/2)); ]))

let rec exp_to_string ae = match ae with
  | X -> "x"
  | Lit i -> string_of_int i
  | Plus (ae0, ae1) ->
    let s0 = exp_to_string ae0 in
    let s1 = exp_to_string ae1 in
    "(" ^ s0 ^ "+" ^ s1 ^ ")"
  | Times (ae0, ae1) ->
    let s0 = exp_to_string ae0 in
    let s1 = exp_to_string ae1 in
    "(" ^ s0 ^ "*" ^ s1 ^ ")"

let arb_tree = make ~print:exp_to_string (mygen'')

let mytree = Plus (Lit 1, Times (X, Lit 3))

let rec size aexp = match aexp with
  | X -> 0
  | Lit(ae0) -> 0
  | Plus(ae0, ae1) ->
    1+(size ae0) + (size ae1)
  | Times(ae0, ae1) ->
    1+(size ae0) + (size ae1)

let rec size2 aexp = match aexp with
  | X -> 1
  | Lit i -> 1
  | Plus(ae0, ae1) ->
    1 + size2 ae0 + size2 ae1
  | Times(ae0, ae1) ->
    1 + size2 ae0 + size2 ae1

let rec size3 aexp = match aexp with
  | X -> 1
  | Lit i -> 1
  | Plus(ae0, ae1) ->
    size3 ae0 + size3 ae1
  | Times(ae0, ae1) ->
    size3 ae0 + size3 ae1

(** Assignment 2 
The abstract machine from the slides operates over a list of instructions and a stack of integers.

a. Write an interpreter for the abstract machine, e.g., with signature

  run : int -> inst list -> int list -> int
accepting an initial value for the x register, an instruction list, and an initial stack.

Declare and throw a suitable exception in error cases.

(after sl.18)

b. QuickCheck that evaluating and compiling+running agrees

c. Extend the previous exercise with subtraction

d. QuickCheck your extension
*)

(* a datatype of abstract machine instructions *)
type inst =
  | Load
  | Push of int
  | Add
  | Subtract
  | Mult
  | Division

let insts = [Push 3; Load; Add]

(* our compiler from arithmetic expressions to instructions *)
let rec compile ae = match ae with
  | X -> [Load]
  | Lit i -> [Push i]
  | Plus (ae0, ae1) ->
    let is0 = compile ae0 in
    let is1 = compile ae1 in
    is0 @ is1 @ [Add]
  | Times (ae0, ae1) ->
    let is0 = compile ae0 in
    let is1 = compile ae1 in
    is0 @ is1 @ [Mult]

exception Stack_doesnot_have_two_elements_exception
exception Cannot_divide_by_zero_exception

let rec run instructions stack reg = match instructions, stack with
  | [], _ -> stack
  | Load::tail, _ -> run tail (reg::stack) reg
  | Push i::tail, _ -> run tail (i::stack) reg
  | Add::tail, el1::el2::rest -> run tail ((el1+el2)::rest) reg
  | Subtract::tail, el1::el2::rest -> run tail ((el1-el2)::rest) reg
  | Mult::tail, el1::el2::rest -> run tail ((el1*el2)::rest) reg
  | Division::tail, el1::el2::rest when el2 != 0 -> run tail ((el1/el2)::rest) reg
  | Division::tail, el1::el2::rest when el2 = 0 -> raise Cannot_divide_by_zero_exception
  | (Add::_ | Subtract::_ | Mult::_ | Division::_), _ -> raise Stack_doesnot_have_two_elements_exception


(** Stuff *)
type person = {name : string;
                age : int};;

let person_to_string p =
  p.name ^ ", " ^ (string_of_int p.age) ^ " years"


(** Assignment 3
The default integer generator int primarily generates large integers. The small_signed_int generator on the other hand favors small numbers.

a. Program an alternative integer generator by combining different generators such that the result has a reasonable chance of generating both, as well as corner cases such as -1, 0, 1, min_int, and max_int.

(after sl.34)

b. Compute statistics for your generator's distribution and compare them
 *)

 let my_gen = Gen.frequency [
   (5, Gen.int);
   (5, Gen.small_signed_int);
   (1, Gen.return (Int64.to_int(Int64.max_int)));
   (1, Gen.return (Int64.to_int(Int64.min_int)));
   (1, Gen.return (-1));
   (1, Gen.return (0));
   (1, Gen.return (1));
 ];;

(** Assignment 4
Use Gen.int_bound to write a generator representing a pair of dices and compute statistics for their sum.
 *)

let dice_gen = 
  Gen.pair (Gen.map (fun i -> i+1) (Gen.int_bound 5)) (Gen.map (fun i -> i+1) (Gen.int_bound 5))

(** Assignment 5
int_of_string : string -> int attempts to parse a string as a number, and throws an exception Failure "int_of_string" when it can't:

# int_of_string "123";;
- : int = 123
# int_of_string "abc";;
Exception: Failure "int_of_string".
Write a wrapper my_int_of_string : string -> int option that calls int_of_string and instead returns an option type representing whether the call went well.
 *)

type result =
  | Ok of int
  | Error

let my_int_of_string str = 
  try 
    let parse = int_of_string str in
    Ok parse
  with Failure "int_of_string" -> Error

(** Assignment 6
List.find_opt : ('a -> bool) -> 'a list -> 'a option returns an option type representing whether a list contains an element satisfying a given property:

# List.find_opt (fun e -> e>4) [2;3;5;0];;
- : int option = Some 5
# List.find_opt (fun e -> e>4) [2;3;0];;
- : int option = None
Write a wrapper my_list_find : ('a -> bool) -> 'a list -> 'a that calls List.find_opt and instead returns the found element or throws exception Not_found.
 *)

let my_list_find predicate list = match List.find_opt predicate list with
  | None -> raise Not_found
  | i -> i


(** Assignment 7
Consider the following representation of Red-Black trees: https://en.wikipedia.org/wiki/Red%E2%80%93black_tree

type color = Red | Black
type 'a rbtree = Leaf | Node of color * 'a * 'a rbtree * 'a rbtree
Trees are either empty (the Leaf constructor) or non-empty (the Node constructor, which expects a color, a tree element, a left sub-tree, and a right sub-tree)

We can represent sets using this representation:

These are also recalled in Hickey p.54-55/64-65 which has been adapted from the Haskell code in the following paper: https://wiki.rice.edu/confluence/download/attachments/2761212/Okasaki-Red-Black.pdf

Since insert produces a new tree, it should satisfy the red-black invariants:

Invariant 1: No red node has a red parent
Invariant 2: Every path from the root to an empty node contains the same number of black nodes
a. Write a (recursive) Boolean-valued function to check invariant 1

b. Write a (recursive) Boolean-valued function to check invariant 2. What type should it have, so that we can check agreement between sub-trees?

c. Write a QCheck test based on a. and b. For simplicity, you should not attempt to generate arbitrary trees satisfying the invariants. Instead generate a list of elements, insert them all with set_of_list, and check that the result satisfies the red-black invariants.
 *)

type color = Red | Black
type 'a rbtree = Leaf | Node of color * 'a * 'a rbtree * 'a rbtree

 (*  empty : 'a set  *)
let empty = Leaf

(*  mem : 'a -> 'a set -> bool  *)
let rec mem x s = match s with
  | Leaf -> false
  | Node (_, y, left, right) ->
     x = y || (x < y && mem x left) || (x > y && mem x right)

(*  balance : color * 'a * ('a tree) * ('a tree) -> 'a tree  *)
let balance t = match t with
  | Black, z, Node(Red, y, Node(Red,x,a,b), c), d
  | Black, z, Node(Red, x, a, Node(Red,y,b,c)), d
  | Black, x, a, Node(Red, z, Node(Red,y,b,c), d)
  | Black, x, a, Node(Red, y, b, Node(Red,z,c,d)) ->
     Node(Red, y, Node(Black,x,a,b), Node(Black,z,c,d))
  | color, x, a, b -> Node(color,x,a,b)

(*  insert : 'a -> 'a set -> 'a set  *)
let insert x s =
  let rec ins s = match s with
    | Leaf -> Node (Red, x, Leaf, Leaf)
    | Node (color,y,a,b) -> if x < y then balance (color, y, ins a, b)
                            else if x > y then balance (color, y, a, ins b)
                            else s (* x = y *)
  in
  match ins s with (* guaranteed to be non-empty *)
    | Node (_,y,a,b) -> Node (Black, y, a, b)
    | Leaf -> raise (Invalid_argument "insert: cannot color empty tree")

(*  set_of_list : 'a list -> 'a set  *)
let rec set_of_list = function
  | [] -> empty
  | x :: l -> insert x (set_of_list l);;
