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

let myTheorem = (d&&c)**(c&&b)**(b&&a)&&d&&a;;
test_theorem myTheorem;;

let myTheorem2 = ((c&&b)&&a)&&((d**c)&&b)&&d&&c&&a;;
let proof = theorem_to_proof myTheorem2;;
print_proof proof;;

(* let transpose_of_3x3_matrix_theorem = ((a**b**c)**(d**e**f)**(g**h**i)) && ((a**d**g)**(b**e**h)**(c**f**i));;
test_theorem transpose_of_3x3_matrix_theorem;; *)