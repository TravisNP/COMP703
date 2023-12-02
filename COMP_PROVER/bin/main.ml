open Prover;;

(* Swap theorem example on page 9 of Constructive Logic*)
let swapTheorem = a ** b && b ** a in
test_theorem swapTheorem;;

(* Example of theorem on page 31 of Constructive Logic *)
let functionSplitTheorem = (a && b ** c) && ((a && b) ** (a && c)) in
test_theorem functionSplitTheorem;;

(* Example of theorem on page 13 of Constructive Logic *)
let disTheorem = (S 0 @@ S 1) && (S 1 @@ S 0) in
(* print_theorem dis_theorem;
let dis_proof = theorem_to_proof dis_theorem in
print_proof dis_proof;;
print_newline ();; *)
test_theorem disTheorem;;

(* Example of theorem on page 33 of Constructive Logic *)
let functionCompositionTheorem = ((a && b) ** (b && c)) && (a && c) in
test_theorem functionCompositionTheorem;;

let pairToSingleArg = ((a**a)&&b)&&(a&&b) in
test_theorem pairToSingleArg;;

let myTheorem = (d&&c)**(c&&b)**(b&&a)&&d&&a in
test_theorem myTheorem;;

let myTheorem2 = (a@@(b**c))&&(a@@c) in
test_theorem myTheorem2;;

let transpose_of_2x2_or_3x3_matrix_theorem = (a**b**c)**(d**e**f)**(g**h**i) @@ (j**k)**(l**m) && (a**d**g)**(b**e**h)**(c**f**i) @@ (j**l)**(k**m) in
test_theorem transpose_of_2x2_or_3x3_matrix_theorem;;
let mat3x3 = ((1,(2,3)),((4,(5,6)),(7,(8,9))))
let mat2x2 = ((1,2),(3,4))