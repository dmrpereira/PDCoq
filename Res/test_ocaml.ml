open Extr
open Extr.Tests

let decide f =
  let tini = Sys.time() in 
  let s =   
    match f with
    | true -> "Evaluation returned true\n"
    | false -> "Evaluation returned false\n" 
  in
  print_string s ; Printf.printf "Execution time: %fs\n" (Sys.time() -. tini) 


let _ = decide tre1_tre2_test
let _ = decide tre3_tre4_test
let _ = decide tre5_tre6_test
let _ = decide tre7_tre8_test
let _ = decide tre9_tre10_test
let _ = decide tre11_tre12_test
let _ = decide tre13_tre14_test
