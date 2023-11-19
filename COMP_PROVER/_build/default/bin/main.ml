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

let myMap = TheoremMap.empty;;
(* let myMap = TheoremMap.add (b) (PROOF (CON2_ELIM, [PROOF ((ASSUMPTION (a**b)), [], true)], true)) myMap;; *)
let myMap = TheoremMap.add (a) (PROOF (CON1_ELIM, [PROOF ((ASSUMPTION (a**b)), [], true)], true)) myMap;;
let myMap2 = TheoremMap.add (a) (PROOF (CON1_ELIM, [PROOF ((ASSUMPTION (a**b)), [], true)], true)) myMap;;
(* let mergedMap = TheoremMap.union (fun list1 list2 = list1 :: list2) myMap myMap2;; *)
(* let myMap = TheoremMap.add (a**b) (PROOF (ASSUMPTION (a**b), [], true)) myMap;; *)
(* let proof_swap_theorem = 
  PROOF (
    IMP_INTRO, 
    [PROOF (
      CON_INTRO, 
      [PROOF (CON2_ELIM, [PROOF (ASSUMPTION (a**b), [], true)], true); 
       PROOF (CON1_ELIM, [PROOF (ASSUMPTION (a**b), [], true)], true)], 
      true)],
    true);;
print_proof proof_swap_theorem;;
let proof_swap_theorem_prover = prover swap_theorem AssumptionSet.empty AssumptionSet.empty myMap;; *)
module TestMap = Map.Make (Int);;
let m1 = TestMap.empty;;
let m1 = TestMap.add 1 "hello" m1;;
let m1 = TestMap.add 2 "I am 2" m1;;
let m2 = TestMap.empty;;
let m2 = TestMap.add 1 "world" m2;;
let m3 = TestMap.merge (fun _ s1 s2 -> match s1, s2 with
  | Some s1, Some s2 -> Some (s1 ^ s2)
  | Some s1, None -> Some s1
  | None, Some s2 -> Some s2
  | _ -> None)
  m1 m2;;
