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
                    | _ -> member haystack needle;;

let fst n = match n with
    | (x,_) -> x

let snd n = match n with
    | (_,y) -> y

let mytest = Test.make float (fun f -> floor f <= f);; 

let sum_test = Test.make ~name: "sum" (pair (list int) (list int)) (fun(xs,xy) -> sum(xs@xy) = sum(xs) + sum(xy));;

let rec merge l1 l2 = match l1, l2 with
    | ([], []) -> []
    | (l, []) -> l
    | ([], l) -> l
    | el1::elems1, el2::elems2 -> match el1 > el2 with
        | true -> el2::merge l1 elems2
        | false -> el1::merge elems1 l2;;

    
QCheck_runner.run_tests [mytest];;