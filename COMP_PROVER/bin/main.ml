(* TODO: Record the CON and IMP elimination rules when used, currently not being recorded *)
(* TODO: Separate into different files *)

(* theorem data type, S represents singleton *)
type theorem =
  | CON of theorem * theorem
  | DIS of theorem * theorem
  | IMP of theorem * theorem
  | S of int
  | F

module Theorem = struct
  type t = theorem
  let compare = compare
end

module AxiomSet = Set.Make (Theorem);;

(* rule data type *)
type rule = 
  | CON_INTRO
  | DIS1_INTRO
  | DIS2_INTRO
  | IMP_INTRO
  | IMP_ELIM
  | CON1_ELIM
  | CON2_ELIM
  | DIS_ELIM
  | AXIOM of theorem
  | FAILURE

(* proof data type *)
type proof = {
  rule: rule;
  children: proof list;
  success: bool;
}

(* Custom exception to print out information to terminal *)
exception SomethingIsWrong of string

(* Converts theorem to string *)
let rec theorem_to_string theorem = 
  match theorem with
  | CON (left, right) -> parenthesize left ^ " \u{2227} " ^ parenthesize right
  | DIS (left, right) -> parenthesize left ^ " \u{2228} " ^ parenthesize right
  | IMP (left, right) -> 
    (
      match right with 
      | F -> "\u{ac}" ^ parenthesize left
      | _ -> parenthesize left ^ " \u{2283} " ^ parenthesize right
    )
  | S value -> string_of_int value
  | F -> "\u{22A5}"
and parenthesize theorem = 
  match theorem with
  | S value -> string_of_int value
  | F -> "\u{22A5}"
  | _ -> "(" ^ theorem_to_string theorem ^ ")"

(* Converts proof to string *)
let rec proof_to_string {rule; children; _} =
  let inside = match children with
    | theorem :: [] -> "(" ^ proof_to_string theorem ^ ")"
    | left :: [right] -> "(" ^ proof_to_string left ^ " " ^ proof_to_string right ^ ")"
    | [] -> "I am unused, but exist for the Axiom and Failure cases"
    | _ -> raise (SomethingIsWrong "proof_to_string: Only zero, one, or two children possible with this implementation") in
  match rule with
  | IMP_INTRO -> "\u{2283}I" ^ inside
  | CON_INTRO -> "\u{2227}I" ^ inside
  | DIS1_INTRO -> "\u{2228}I1" ^ inside
  | DIS2_INTRO -> "\u{2228}I2" ^ inside
  | AXIOM theorem -> parenthesize theorem
  | FAILURE -> "FAILURE"
  | DIS_ELIM -> "\u{2228}E" ^ inside
  | _ -> raise (SomethingIsWrong "proof_to_string: ELIM rules for CON and DIS not implemented")

(* Prints theorem to terminal *)
let print_theorem theorem = print_endline (theorem_to_string theorem)

(* Prints proof to terminal *)
let print_proof proof = print_endline (proof_to_string proof)

(* Print axioms to terminal *)
let print_axioms axioms = 
  let axiomsList = AxiomSet.to_list axioms in
  List.iter print_theorem axiomsList

(* Generates the new set of axioms using the CON ELIM and IMP ELIM rules *)
let rec gen_new_axioms axiomSet theoremsToAdd =
  (* CON Elimination rule. For a list of theorems, adds the children of CON to the list. Does so recursively.
       For example, [A&(B&C)] returns [A&(B&C),A,B&C,B,C] *)
  let rec handle_con_elim theoremsToAdd = 
    match theoremsToAdd with
    | theorem :: theoremsToAdd -> 
      (
        match theorem with
        | CON (left, right) -> [theorem] @ (handle_con_elim [left]) @ (handle_con_elim [right]) @ (handle_con_elim theoremsToAdd)
        | _ -> [theorem] @ (handle_con_elim theoremsToAdd)
      )
    | [] -> [] in
  
  (* Breaks apart all outside CON theorems being added to the axiom set using the CON ELIM rule and feeds them into the IMP ELIM rule *)
  let conElimTheoremsToAdd = AxiomSet.of_list (handle_con_elim theoremsToAdd) in
  let conElimNotInAxiomSetTheoremsToAdd = AxiomSet.diff conElimTheoremsToAdd axiomSet in
  handle_imp_elim axiomSet conElimNotInAxiomSetTheoremsToAdd

(* Takes in current axioms and the new theorems to add as axioms.
   Does IMP ELIM rule and feeds any new derived axioms back into gen_new_axioms *)
and handle_imp_elim axiomSet newTheoremsToAdd = 
  (* Returns the conclusion of the IMP theorem if the hypothesis of theorem matches the hypothesis given, None otherwise *)
  let axiomSet = AxiomSet.union axiomSet newTheoremsToAdd in
  let conc_hypo_match hypothesis theorem = match theorem with 
  | IMP (hypo_theorem, conclusion) -> if hypo_theorem = hypothesis then Some conclusion else None
  | _ -> None in

  (* Returns the conlusions of all implications in axiomSet if the implication's hypothesis is in possibleHypothesis *)
  let rec get_conc_if_hypo_match_list axiomSet possibleHypotheses =
    match possibleHypotheses with
    | hypothesis :: hypotheses -> 
        (
          let conclusions = AxiomSet.to_list (AxiomSet.filter_map (conc_hypo_match hypothesis) axiomSet) in
          conclusions @ (get_conc_if_hypo_match_list axiomSet hypotheses)
        )
    | [] -> [] in

  (* Gets the conclusions of all IMP theorems in axiomSet where the hypothesis is in newTheoremsToAdd and the conclusion is not already an axiom *)
  let impMatchAxiomSetConc = AxiomSet.of_list (get_conc_if_hypo_match_list axiomSet (AxiomSet.to_list newTheoremsToAdd)) in
  (* Gets the conclusions of all IMP theorems in newTHeoremsToadd where the hyptohesis is in axiomSet and the conclusion is not already an axiom *)
  let impMatchTheoremsToAddConc = AxiomSet.of_list (get_conc_if_hypo_match_list newTheoremsToAdd (AxiomSet.to_list axiomSet)) in
  let impMatchBothSetsConc = AxiomSet.union impMatchAxiomSetConc impMatchTheoremsToAddConc in
  let impMatchBothConcNotInAxiomSet = AxiomSet.diff impMatchBothSetsConc axiomSet in

  (* If no new conclusions have been generated, convergence has been reached and all new possible axioms have been generated,
     else generate new axioms *)
  if AxiomSet.is_empty impMatchBothConcNotInAxiomSet
    then axiomSet
    else gen_new_axioms axiomSet (AxiomSet.to_list impMatchBothConcNotInAxiomSet)

(*  Main proof function.
  If the theorem is an axiom, return.
  Else check if theorem is of type CON, IMP, DIS, or S.
  Do INTRO rule corresponding to type CON, IMP, or DIS.
  If proof fails, do DIS ELIM rule if possible and reconsider theorem. If not possible, then fail.
  Each time the IMP INTRO and DIS ELIM rule happen, add to Axioms and use CON ELIM and IMP ELIM to add anymore to axioms
     *)
let rec prover theorem axioms usedDIS =
  if AxiomSet.mem theorem axioms 
    then {rule = AXIOM theorem; children = []; success = true;}
    else
      (
        match theorem with
        | CON (left, right) -> 
          (
            let leftProof = prover left axioms usedDIS in
            let rightProof = prover right axioms usedDIS in
            if not leftProof.success || not rightProof.success
              then handle_dis_elim theorem axioms usedDIS
              else {rule = CON_INTRO; children = [leftProof; rightProof]; success = true;}
          )
        | IMP (left, right) ->
            (
              let proof = prover right (gen_new_axioms axioms [left]) usedDIS in
              if not proof.success 
                then handle_dis_elim theorem axioms usedDIS
                else {rule = IMP_INTRO; children = [proof]; success = true;}
            )
        | DIS (left, right) ->
          (
            let leftProof = prover left axioms usedDIS in
            if not leftProof.success
              then (let rightProof = prover right axioms usedDIS in
                if not rightProof.success
                  then handle_dis_elim theorem axioms usedDIS
                  else {rule = DIS2_INTRO; children = [rightProof]; success = true})
              else {rule = DIS1_INTRO; children = [leftProof]; success = true}
          )
        | S _ -> handle_dis_elim theorem axioms usedDIS
        | F -> handle_dis_elim theorem axioms usedDIS
      )

(* Handles the DIS Elimination rule. If a theorem in the axioms has DIS as the outer operator and has not been broken apart before,
    generate the new axiom sets and try to prove the theorem again using the DIS ELIM rule*)
and handle_dis_elim theorem axioms usedDIS = 
  (* get_dis method: Filters a set based on the predicate that a theorom had DIS as the outer operator and hasn't been used before.
  Returns an arbitrary element from the set, None if empty *)
  let get_dis axiomSet usedDIS = 
    let is_dis theorem = match theorem with DIS (_, _) -> true | _ -> false in
    let disAxiomSet = AxiomSet.filter is_dis axiomSet in
    let disAxiomSetNotUsed = AxiomSet.diff disAxiomSet usedDIS in
    AxiomSet.choose_opt disAxiomSetNotUsed in
  
  (* foundDis is a randomly chosen unused DIS axiom. If no such axiom exists, proof fails.
     If one does exist, do DIS ELIM rule. If fails, repeat until success or failure *)
  let foundDis = get_dis axioms usedDIS in
  match foundDis with
  | None -> {rule = FAILURE; children = []; success = false;}
  | Some DIS (left, right) -> 
    (
      let usedDIS = AxiomSet.add (DIS (left, right)) usedDIS in
      let leftProof = prover theorem (gen_new_axioms axioms [left]) usedDIS in
      let rightProof = prover theorem (gen_new_axioms axioms [right]) usedDIS in
      if not leftProof.success || not rightProof.success
        then handle_dis_elim theorem axioms usedDIS
      (* TODO: Might need to add foundDis to children for program extraction? *)
        else {rule = DIS_ELIM; children = [leftProof; rightProof]; success = true}
    )
  | _ -> raise (SomethingIsWrong "handle_dis_elim: DIS Theorem found in axioms doesn't match None or DIS (left, right, false)")

(* Calls the prover with an empty axiom set and empty usedDis set *)
let prove_theorem theorem = prover theorem AxiomSet.empty AxiomSet.empty;;

(* Prints the theorem, tries to prove it, then prints the proof *)
let test_theorem theorem = 
  print_theorem theorem;
  let proof_theorem = prove_theorem theorem in
  print_proof proof_theorem;
  print_newline();;

(* Define operators for NOT, CON, DIS, and IMP. Precedence rules apply !! > ** > @@ > &&. All binary operators are right associative.
   Yes, it is confusing to have IMP defined as &&, however, in order to use only basic OCaml operators, which have a certain precedence order, 
   they have to be overwritten like this. https://v2.ocaml.org/manual/expr.html. Otherwise would have to download and use a dependency *)
let ( !! ) x = IMP(x, F);;
let ( ** ) x y = CON(x, y);;
let ( @@ ) x y = DIS(x, y);;
let ( && ) x y = IMP(x, y);;


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