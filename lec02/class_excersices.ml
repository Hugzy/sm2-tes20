open QCheck;;


let rec msb number = 
    if number = 0
    then 0
    else 1+msb(number lsr 1);;

let rec sum l = match l with
    | [] -> 0
    | elem::elems -> elem + sum(elems)

let rec member needle haystack = match haystack with
    | [] -> false
    | hay::haystack -> match hay with 
                    | needle -> true
                    | _ -> member needle haystack;;

let fst n = match n with
    | (x,_) -> x

let snd n = match n with
    | (_,y) -> y

let mytest = Test.make float (fun f -> floor f <= f);; 

let sum_test = Test.make ~name: "sum" (pair (list int) (list int)) (fun(xs,xy) -> sum(xs@xy) = sum(xs) + sum(xy));;


(*
Properties that should hold
- Output should always be sorted
 *)
let rec merge lhs rhs = match lhs, rhs with
    | (l, [])
    | ([], l) -> l
    | el1::elems1, el2::elems2 -> match el1 > el2 with
        | true -> el2::merge lhs elems2
        | false -> el1::merge elems1 rhs;;

let merge_test = Test.make ~name: "merge" ~count:1000 ~max_gen:1000 (pair (list int) (list int)) (fun(lhs, rhs) -> 
    let sorted_lhs = List.sort compare lhs in
    let sorted_rhs = List.sort compare rhs in
    merge sorted_lhs sorted_rhs = List.sort compare (lhs@rhs));;


let print_test = Test.make ~name:"print" string (fun(str) -> print_string str; true = true);;

QCheck_runner.run_tests [mytest; merge_test; print_test];;