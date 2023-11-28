open Prover;;

(* Swap theorem example on page 9 of Constructive Logic*)
let swapTheorem = a ** b && b ** a in
test_theorem swapTheorem;;

(* Example of theorem on page 31 of Constructive Logic *)
let functionSplitTheorem = (a && b ** c) && ((a && b) ** (a && c));;
test_theorem functionSplitTheorem;;

(* Example of theorem on page 13 of Constructive Logic *)
let dis_theorem = (S 0 @@ S 1) && (S 1 @@ S 0);;
print_theorem dis_theorem;;
let dis_proof = theorem_to_proof dis_theorem;;
print_proof dis_proof;;
print_newline ();;

(* Example of theorem on page 33 of Constructive Logic *)
let functionCompositionTheorem = ((a && b) ** (b && c)) && (a && c);;
test_theorem functionCompositionTheorem;;

let pairToSingleArg = ((a**a)&&b)&&(a&&b);;
test_theorem pairToSingleArg;;

(* Tests the chaining of eliminitation and introduction rules *)
let myTheorem = ((b**b)&&c)&&((a&&b)&&(a&&c));;
test_theorem myTheorem;;

(* let transpose_of_3x3_matrix_theorem = ((a**b**c)**(d**e**f)**(g**h**i)) && ((a**d**g)**(b**e**h)**(c**f**i));;
test_theorem transpose_of_3x3_matrix_theorem;; *)