(* TODO: Record the CON and IMP elimination rules when used, currently not being recorded *)
open Prover;;

(* Swap theorem example on page 9 of Constructive Logic*)
(* let swap_theorem = IMP (CON (S 0, S 1), CON (S 1, S 0));; *)
let swap_theorem = S 0 ** S 1 && S 1 ** S 0;;
test_theorem swap_theorem;;

(* Example of theorem on page 31 of Constructive Logic *)
(* let example_theorem = IMP (IMP (S 0, CON (S 1, S 2)), CON (IMP (S 0, S 1), IMP (S 0, S 2)));; *)
let example_theorem = (S 0 && (S 1 ** S 2)) && ((S 0 && S 1) ** (S 0 && S 2));;
test_theorem example_theorem;;

(* Example of theorem on page 13 of Constructive Logic *)
(* let example_theorem2 = IMP (DIS (S 0, S 1), DIS (S 1, S 0));; *)
let example_theorem2 = (S 0 @@ S 1) && (S 1 @@ S 0);;
test_theorem example_theorem2;;

(* Example of theorem to test that the gen_new_axioms method is working *)
(* let example_theorem3 = IMP (IMP (IMP (S 0, S 1), CON (IMP (S 2, S 3), S 2)), IMP (IMP (S 0, S 1), S 3));; *)
let example_theorem3 = ((S 0 && S 1) && ((S 2 && S 3) ** S 2)) && ((S 0 && S 1) && S 3);;
test_theorem example_theorem3;;

(* Example of theorem on page 33 of Constructive Logic *)
(* let example_theorem4 = IMP ( CON (IMP (S 0, S 1), IMP (S 1, S 2)), IMP (S 0, S 2));; *)
let example_theorem4 = ((S 0 && S 1) ** (S 1 && S 2)) && (S 0 && S 2);;
test_theorem example_theorem4;;

(* Example of first theorem on page 15 of Constructive Logic *)
(* let example_not = IMP (CON (S 0, IMP (S 0, F)), F);; *)
let example_not = !!(S 0 ** !!(S 0));;
test_theorem example_not;;

(* Example of second theorem on page 15 of Constructive Logic *)
(* let example_not1 = IMP (S 0, IMP (IMP (S 0, F), F));; *)
let example_not1 = S 0 && !!(!!(S 0));;
test_theorem example_not1;;

let ex = ((a ** b) ** c) && (a ** b ** c);;
test_theorem ex;;