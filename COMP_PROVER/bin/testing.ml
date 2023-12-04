open Prover;;

(** Prints out the time taken to run a function on an input *)
let time func input =
  let startTime = Sys.time() in
  let _ = func input in
  Printf.printf "Execution time: %fms\n" ((Sys.time() -. startTime) *. 1000.)

(* Swap theorem example on page 9 of Constructive Logic*)
let swapTheorem = a ** b && b ** a;;
test_theorem swapTheorem;;
time theorem_to_proof swapTheorem;;

(* Example of theorem on page 31 of Constructive Logic *)
let functionSplitTheorem = (a && b ** c) && ((a && b) ** (a && c));;
test_theorem functionSplitTheorem;;
time theorem_to_proof functionSplitTheorem;;

(* Example of theorem on page 13 of Constructive Logic *)
let disTheorem = (S 0 @@ S 1) && (S 1 @@ S 0);;
test_theorem disTheorem;;
time theorem_to_proof disTheorem;;

(* Example of theorem on page 33 of Constructive Logic *)
let functionCompositionTheorem = ((a && b) ** (b && c)) && (a && c);;
test_theorem functionCompositionTheorem;;
time theorem_to_proof functionCompositionTheorem;;

let pairToSingleArg = ((a**a)&&b)&&(a&&b);;
test_theorem pairToSingleArg;;
time theorem_to_proof pairToSingleArg;;

let transpose_of_2x2_or_3x3_matrix_theorem = (a**b**c)**(d**e**f)**(g**h**i) @@ (j**k)**(l**m) && (a**d**g)**(b**e**h)**(c**f**i) @@ (j**l)**(k**m);;
test_theorem transpose_of_2x2_or_3x3_matrix_theorem;;
time theorem_to_proof transpose_of_2x2_or_3x3_matrix_theorem;;
let _ = ((1,(2,3)),((4,(5,6)),(7,(8,9))));;
let _ = ((1,2),(3,4));;