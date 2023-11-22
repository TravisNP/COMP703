open Prover;;

(* Swap theorem example on page 9 of Constructive Logic*)
(* let swap_theorem = IMP (CON (S 0, S 1), CON (S 1, S 0));; *)
let swapTheorem = a ** b && b ** a in
test_theorem swapTheorem;;

(* Example of theorem on page 31 of Constructive Logic *)
(* let example_theorem = IMP (IMP (S 0, CON (S 1, S 2)), CON (IMP (S 0, S 1), IMP (S 0, S 2)));; *)
let functionSplitTheorem = (a && b ** c) && ((a && b) ** (a && c));;
test_theorem functionSplitTheorem;;
(* Example of theorem on page 13 of Constructive Logic *)
(* let example_theorem2 = IMP (DIS (S 0, S 1), DIS (S 1, S 0));; *)
(* let example_theorem2 = (S 0 @@ S 1) && (S 1 @@ S 0);;
test_theorem example_theorem2;; *)

(* Example to test that DIS_ELIM rule records the DIS theorem being used *)
(* let dis_theorem = (a**(b@@c)) && (c@@b);;
test_theorem dis_theorem;; *)

(* Example of theorem to test that the gen_new_axioms method is working *)
(* let example_theorem3 = IMP (IMP (IMP (S 0, S 1), CON (IMP (S 2, S 3), S 2)), IMP (IMP (S 0, S 1), S 3));; *)
(* let example_theorem3 = ((S 0 && S 1) && ((S 2 && S 3) ** S 2)) && ((S 0 && S 1) && S 3);;
test_theorem example_theorem3;; *)

(* Example of theorem on page 33 of Constructive Logic *)
(* let example_theorem4 = IMP ( CON (IMP (S 0, S 1), IMP (S 1, S 2)), IMP (S 0, S 2));; *)
let functionCompositionTheorem = ((a && b) ** (b && c)) && (a && c);;
test_theorem functionCompositionTheorem;;

(* Example of first theorem on page 15 of Constructive Logic *)
(* let example_not = IMP (CON (S 0, IMP (S 0, F)), F);; *)
(* let example_not = !!(S 0 ** !!(S 0));;
test_theorem example_not;; *)

(* Example of second theorem on page 15 of Constructive Logic *)
(* let example_not1 = IMP (S 0, IMP (IMP (S 0, F), F));; *)
(* let example_not1 = S 0 && !!(!!(S 0));;
test_theorem example_not1;; *)

let transpose_of_3x3_matrix_theorem = ((a**b**c)**(d**e**f)**(g**h**i)) && ((a**d**g)**(b**e**h)**(c**f**i));;
test_theorem transpose_of_3x3_matrix_theorem;;