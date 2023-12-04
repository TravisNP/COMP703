open Prover;;

(** Prints out the time taken to run a function on an input *)
let time 
  func input =
  let startTime = Sys.time() in
  let _ = func input in
  Printf.printf "Execution time: %fms\n" ((Sys.time() -. startTime) *. 1000.)

(** Prints out the time taken to prove a theorem *)
let time_prove = 
  time theorem_to_proof;;

(* Swap theorem example on page 9 of Constructive Logic*)
let swapTheorem = a ** b && b ** a;;
test_theorem swapTheorem;;
time_prove swapTheorem;;

(* Example of theorem on page 31 of Constructive Logic *)
let functionSplitTheorem = (a && b ** c) && ((a && b) ** (a && c));;
test_theorem functionSplitTheorem;;
time_prove functionSplitTheorem;;

(* Example of theorem on page 13 of Constructive Logic *)
let disTheorem = (S 0 @@ S 1) && (S 1 @@ S 0);;
test_theorem disTheorem;;
time_prove disTheorem;;

(* Example of theorem on page 33 of Constructive Logic *)
let functionCompositionTheorem = ((a && b) ** (b && c)) && (a && c);;
test_theorem functionCompositionTheorem;;
time_prove functionCompositionTheorem;;

(* Example of a theorem which takes in a function which takes in two arguments and outputs the function which takes only one argument and applies it to both 
   arguments in the input function. For example, running this on add where add is of type (int * int) -> int results in the double function. *)
let pairToSingleArgTheorem = ((a**a)&&b)&&(a&&b);;
test_theorem pairToSingleArgTheorem;;
time_prove pairToSingleArgTheorem;;

(* Example of a theorem which takes in either a 3x3 or 3x3 matrix and outputes the transpose *)
let transpose_of_3x3_or_2x2_matrix_theorem = (a**b**c)**(d**e**f)**(g**h**i) @@ (j**k)**(l**m) && (a**d**g)**(b**e**h)**(c**f**i) @@ (j**l)**(k**m);;
test_theorem transpose_of_3x3_or_2x2_matrix_theorem;;
time_prove transpose_of_3x3_or_2x2_matrix_theorem;;
let _ = ((1,(2,3)),((4,(5,6)),(7,(8,9))));;
let _ = ((1,2),(3,4));;

(* Gets the diagonal of a 1x1, 2x2, or 3x3 matrix *)
let diagonal_of_1x1_or_2x2_or_3x3_matrix = (a @@ ((b**c)**(d**e)) @@ ((f**g**h)**(i**j**k)**(l**m**n))) && (a @@ (b**e) @@ (f**j**m));;
test_theorem diagonal_of_1x1_or_2x2_or_3x3_matrix;;
time_prove diagonal_of_1x1_or_2x2_or_3x3_matrix;;

(* Returns a pair if the input represents two single inputs. Returns a pair of pairs if the input represents two pairs
   Example input: 
   (Left 3) (Left (4.0, "junk"))
   myFunc (Right ("hi", 0)) (Right (("world", 1.0), "junk"));; 
   To reach the abort, mix Left and Right - (Left 4) (Right (("world", 10), "junk"));;*)
let pairValuesTheorem = (a @@ (b**c)) && (((d**(!!(b**c))) @@ ((e**f)**(!!a))) && ((a**d) @@ ((b**e)**(c**f))));;
test_theorem pairValuesTheorem;;
time_prove pairValuesTheorem;;
