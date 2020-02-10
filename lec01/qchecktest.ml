open QCheck;;

let mytest = Test.make float (fun f -> floor f <= f);; 

QCheck_runner.run_tests [mytest];;