(* TODO: Record the CON and IMP elimination rules when used, currently not being recorded *)

(** theorem data type *)
type theorem =

  | CON of theorem * theorem (** Conjunction constructor *)

  | DIS of theorem * theorem (** Disjunction constructor *)

  | IMP of theorem * theorem (** Implication constructor *)

  | S of int (** Singleton proposition constructor *)

  | F (** Falsehood constructor *)

module Theorem = struct
  type t = theorem
  let compare = compare
end

module AxiomSet = Set.Make (Theorem);;

(** rule data type *)
type rule = 
  | CON_INTRO (** Conjuction introduction rule *)

  | DIS1_INTRO (** Left disjunction introduction rule *)

  | DIS2_INTRO (** Right disjunction introduction rule *)

  | IMP_INTRO (** Implication introduction rule *)

  | IMP_ELIM (** Implication elimination rule *)

  | CON1_ELIM (** Left conjunction elimination rule *)

  | CON2_ELIM (** Right conjunction elimination rule *)

  | DIS_ELIM (** Disjunction elimination rule *)

  | AXIOM of theorem (** Theorem is an assumpiton rule *)

  | FAILURE (** Signifies proof has failed *)

(** proof data type *)
type proof = {

  rule: rule; (** Rule used in this step of proof *)

  children: proof list; (** The assumptions for this step *)

  success: bool; (** Indicates proof success at this step *)
}

(* Custom exception to print out information to terminal *)
exception SomethingIsWrong of string

(** Converts theorem to string *)
let rec theorem_to_string
  theorem = match theorem with
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

(** Adds parenthesis around all theorems except singletons or falsehood *)
and parenthesize
  theorem = 
  match theorem with
  | S value -> string_of_int value
  | F -> "\u{22A5}"
  | _ -> "(" ^ theorem_to_string theorem ^ ")"

(** Converts proof to string *)
let rec proof_to_string 
  {rule; children; _} =
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
  | CON1_ELIM -> "\u{2227}E1" ^ inside
  | CON2_ELIM -> "\u{2227}E2" ^ inside
  | IMP_ELIM -> "\u{2283}E" ^ inside

(** Prints theorem to terminal *)
let print_theorem
  theorem = print_endline (theorem_to_string theorem)

(** Prints proof to terminal *)
let print_proof
  proof = print_endline (proof_to_string proof)

(** Print a list of theorems to terminal, one on each line *)
let print_axioms
  axioms = 
  let axiomsList = AxiomSet.to_list axioms in
  List.iter print_theorem axiomsList

(** Generates the new set of axioms using the CON ELIM and IMP ELIM rules *)
let rec gen_new_axioms
  axiomSet theoremsToAdd =

  (* CON Elimination rule. For a list of theorems, adds the children of CON to the list. Does so recursively. For example, [A&(B&C)] returns [A&(B&C),A,B&C,B,C] *)
  let rec handle_con_elim 
    theoremsToAdd = 
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

(** Takes in current axioms and the new theorems to add as axioms. Does IMP ELIM rule and feeds any new derived axioms back into gen_new_axioms *)
and handle_imp_elim 
  axiomSet newTheoremsToAdd = 
  let axiomSet = AxiomSet.union axiomSet newTheoremsToAdd in

  (* Returns the conclusion of the IMP theorem if the hypothesis of theorem matches the hypothesis given, None otherwise *)
  let conc_hypo_match
  hypothesis theorem = match theorem with 
  | IMP (hypo_theorem, conclusion) -> if hypo_theorem = hypothesis then Some conclusion else None
  | _ -> None in

  (* Returns the conlusions of all implications in axiomSet if the implication's hypothesis is in possibleHypothesis *)
  let rec get_conc_if_hypo_match_list
    axiomSet possibleHypotheses =
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

(**  Main proof function.
  If the theorem is an axiom, return.
  Else check if theorem is of type CON, IMP, DIS, or S.
  Do INTRO rule corresponding to type CON, IMP, or DIS.
  If proof fails, do DIS ELIM rule if possible and reconsider theorem. If not possible, then fail.
  Each time the IMP INTRO and DIS ELIM rule happen, add to Axioms and use CON ELIM and IMP ELIM to add anymore to axioms
     *)
let rec prover
  theorem axioms usedDIS =
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

(** Handles the DIS Elimination rule. If a theorem in the axioms has DIS as the outer operator and has not been broken apart before,
    generate the new axiom sets and try to prove the theorem again using the DIS ELIM rule*)
and handle_dis_elim 
  theorem axioms usedDIS = 

  (* Filters a set based on the predicate that a theorom had DIS as the outer operator and hasn't been used before.
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

(** Calls the prover with an empty axiom set and empty usedDis set *)
let prove_theorem
  theorem = prover theorem AxiomSet.empty AxiomSet.empty;;

(** First, prints the theorem to terminal. Then, tries to prove the theorem. Finaly, prints the proof (even upon failure) to terminal.*)
let test_theorem
  theorem = 
  print_theorem theorem;
  let proof_theorem = prove_theorem theorem in
  print_proof proof_theorem;
  print_newline();;

(* Define operators for NOT, CON, DIS, and IMP. Precedence rules apply !! > ** > @@ > &&. All binary operators are right associative.
   Yes, it is confusing to have IMP defined as &&, however, in order to use only basic OCaml operators, which have a certain precedence order, 
   they have to be overwritten like this. https://v2.ocaml.org/manual/expr.html. Otherwise would have to download and use a dependency *)
(** Not operator *)
let ( !! )
  x = IMP(x, F);;

(** Conjunction operator *)
let ( ** )
  x y = CON(x, y);;

(** Disjunction operator *)
let ( @@ )
  x y = DIS(x, y);;

(** Implication operator *)
let ( && ) 
  x y = IMP(x, y);;

(** S 1 *)
let a = S 1;;

(** S 2 *)
let b = S 2;;

(** S 3 *)
let c = S 3;;

(** S 4 *)
let d = S 4;;

(** S 5 *)
let e = S 5;;

(** S 6 *)
let f = S 6;;

(** S 7 *)
let g = S 7;;

(** S 8 *)
let h = S 8;;

(** S 9 *)
let i = S 9;;

(** S 10 *)
let j = S 10;;