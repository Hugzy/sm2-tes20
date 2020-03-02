open QCheck

let (<+>) = Iter.(<+>) (* makes the infix operator visible*)

type aexp =
  | X
  | Lit of int
  | Plus of aexp * aexp
  | Times of aexp * aexp

(* a datatype of abstract machine instructions *)
type inst =
  | Load
  | Push of int
  | Add
  | Subtract
  | Mult
  | Division

let insts = [Push 3; Load; Add]

(* our interpreter of arithmetic expressions *)
let rec interpret xval ae = match ae with
  | X -> xval
  | Lit i -> i
  | Plus (ae0, ae1) ->
    let v0 = interpret xval ae0 in
    let v1 = interpret xval ae1 in
    v0 + v1
  | Times (ae0, ae1) ->
    let v0 = interpret xval ae0 in
    let v1 = interpret xval ae1 in
    v0 * v1

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


let leafgen = Gen.oneof
                [Gen.return X;
                 Gen.map (fun i -> Lit i) Gen.int]

let mygen''' =
  Gen.sized (Gen.fix (fun recgen n -> match n with
    | 0 -> leafgen
    | n ->
      Gen.frequency
	      [(1,leafgen);
	       (2,Gen.map2 (fun l r -> Plus(l,r)) (recgen(n/2)) (recgen(n/2)));
	       (2,Gen.map2 (fun l r -> Times(l,r)) (recgen(n/2)) (recgen(n/2))); ]))

let arb_tree = make ~print:exp_to_string (mygen''')

(**Consider the following module implementing (string,int) dictionaries as in Hickey, exercise 3.6:
Write an interface for the module, such that the dictionary type is abstract (hidden) to outsiders.

# Assignment 1

let dictionary = Dict.empty

let dictionary = Dict.add dictionary "foo" 1;;

print_int (Dict.find dictionary "foo");;
*)


(** 
# Excersise 2 

let myshr i = match i with
 | 0 -> Iter.empty
 | i when i > 10000 -> Iter.return (i/10)
 | i when i <= 10000 && i > 1000 -> Iter.return (i/2)
 | i when i <= 1000 -> Iter.return(i-1)
 | _ -> Iter.empty;;
*)

let myshr i = match i with
 | 0 -> Iter.empty
 | _ -> Iter.return(i/10) 
        <+> (Iter.return(i/2)) 
        <+> (Iter.return(i-1))


let t = Test.make (set_shrink myshr int) (fun i -> false);;
let t2 = Test.make (set_shrink myshr int) (fun i -> i < 432);;

(**
    Consider the following test that uses the built-in pair generator and shrinker:
    q: Despite randomization QCheck's pair shrinker consistently produces the same reduced counterexample. Which? Why?

    A: small_nat generats unsigned integers, the output (0,1) or (1,0) is the smallest valid pair of counterexamles
*)

let t3 = Test.make (pair small_nat small_nat) (fun (i,j) -> i+j = 0);;


(**
    a. Formulate in words a more aggressive shrinking strategy for arithmetic expressions. (If you were to simplify such test-input by hand how would you proceed?)

+------+
| ---- |
+------+

+---------------+

                                                        +------+
                                                        | plus |
                                                        +------+
                                                            |
                                            +------------------------------+
                                            |                              |
                                        +------+                        +------+
                                        | Mult |                        | Plus |
                                        +------+                        +------+
                                            |                               |
                                    +---------------+               +---------------+
                                    |               |               |               |
                                +------+        +------+        +------+        +------+
                                | Lit4 |        |   X  |        |   X  |        | Mult |
                                +------+        +------+        +------+        +------+
                                                                                    |
                                                                            +---------------+
                                                                            |               |
                                                                        +------+        +------+
                                                                        |  X   |        | Lit6 |
                                                                        +------+        +------+


    b. Implement the strategy and test how well it works (how much it simplifies, how many steps it uses, how consistent it is) compared to the one I proposed for different false properties such as the following three:
 *)


let rec tshrink e = match e with
    | X -> Iter.empty
    | Lit i -> Iter.map (fun i' -> Lit i') (Shrink.int i)
    | Plus (ae0, ae1) ->
    (Iter.of_list [ae0; ae1])
    (**(Iter.of_list [ae0; ae1])
    <+> Iter.empty (Iter.map (fun ae0' -> Plus (ae0',ae1)) (tshrink ae0))
    <+> Iter.empty (Iter.map (fun ae1' -> Plus (ae0,ae1')) (tshrink ae1))*)
    | Times (ae0, ae1) ->
    (Iter.of_list [ae0; ae1]);;
    (**(Iter.of_list [ae0; ae1])
    <+> Iter.empty (Iter.map (fun ae0' -> Times (ae0',ae1)) (tshrink ae0))
    <+> Iter.empty (Iter.map (fun ae1' -> Times (ae0,ae1')) (tshrink ae1))*);;

let t4 = Test.make ~name:"aexp is zero when x is" (set_shrink tshrink arb_tree) (fun e -> interpret 0 e = 0);;


(**Gen.generate ~n:10 Gen.small_signed_int;;*)

(**QCheck_runner.run_tests [t4];;*)