open QCheck

(** recursive call *)
let rec fac n = match n with
    | 0 -> 1
    | _ -> n * fac(n-1)

let rec fac' n accumulator = match n with
    | 0 -> accumulator
    | _ -> fac' (n-1) (n*accumulator)

