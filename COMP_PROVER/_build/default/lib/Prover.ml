(** theorem data type *)
type theorem =

  | CON of theorem * theorem (** Conjunction constructor *)

  | DIS of theorem * theorem (** Disjunction constructor *)

  | IMP of theorem * theorem (** Implication constructor *)

  | S of int (** Singleton proposition constructor *)

  | F (** Falsehood constructor *)

(** rule data type *)
type rule = 

  | CON_INTRO (** Conjuction introduction rule *)

  | DIS1_INTRO of theorem (** Left disjunction introduction rule *)

  | DIS2_INTRO of theorem (** Right disjunction introduction rule *)

  | IMP_INTRO of theorem (** Implication introduction rule *)

  | IMP_ELIM  (** Implication elimination rule *)

  | CON1_ELIM (** Left conjunction elimination rule *)

  | CON2_ELIM (** Right conjunction elimination rule *)

  | DIS_ELIM of theorem (** Disjunction elimination rule *)

  | ASSUMPTION of theorem (** Theorem is an assumpiton rule *)

  | FAILURE (** Signifies proof has failed *)

  | CONNECTION (** Connects bottom proof to top proof *)

(** proof data type *)
type proof = 

  PROOF of rule * proof list * int (** Rule used, the proofs of the theorems used, the success of the proof*)

(** temp proof data type when keeping track of IMP and CON ELIM rules *)
type proof_top = 

  PROOF_TOP of rule * theorem list (** Rule used, the theorems used in the proof*)



module Theorem = struct
  type t = theorem
  let compare = compare
end

module ProofTop = struct
  type t = proof_top
  let compare = compare
end

module AssumptionSet = Set.Make (Theorem);;

module ProofTopSet = Set.Make (ProofTop);;

module TheoremMap = Map.Make (Theorem);;



(** Type containing a set of theorems and a map of theorems to proofs *)
type setAndMap = 

  | SET_AND_MAP of AssumptionSet.t * ProofTopSet.t TheoremMap.t

(** Type containing a list of theorems and a map of theorems to proofs *)
  type listAndMap = 

  | LIST_AND_MAP of theorem list * ProofTopSet.t TheoremMap.t

(** Custom exception to print out information to terminal *)
exception SomethingIsWrong of string

(** Exception for when the proof fails *)
exception ProofFailure of string

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
  proof = match proof with 
  | PROOF(rule, children, _) ->
    (
      let inside = match children with
        | theorem :: [] -> "(" ^ proof_to_string theorem ^ ")"
        | left :: [right] -> "(" ^ proof_to_string left ^ " " ^ proof_to_string right ^ ")"
        | left :: middle :: [right] -> "(" ^ proof_to_string left ^ " " ^ proof_to_string middle ^ " " ^ proof_to_string right ^ ")"
        | [] -> ""
        | _ -> raise (SomethingIsWrong "proof_to_string: More than 3 children. Only zero, one, two, or 3 children possible with this implementation") in
      match rule with
      | IMP_INTRO (_) -> "\u{2283}I" ^ inside
      | CON_INTRO -> "\u{2227}I" ^ inside
      | DIS1_INTRO (_) -> "\u{2228}I1" ^ inside
      | DIS2_INTRO (_) -> "\u{2228}I2" ^ inside
      | ASSUMPTION theorem -> parenthesize theorem
      | FAILURE -> "FAILURE"
      | DIS_ELIM (_) -> "\u{2228}E" ^ inside
      | CON1_ELIM -> "\u{2227}E1" ^ inside
      | CON2_ELIM -> "\u{2227}E2" ^ inside
      | IMP_ELIM -> "\u{2283}E" ^ inside
      | CONNECTION -> 
        (
          match children with 
          | theorem :: [] -> proof_to_string theorem
          | left :: [right] -> proof_to_string left ^ " " ^ proof_to_string right
          | [] -> raise (SomethingIsWrong "proof_to_string: PROOF with rule CONNECTION has no children. Impossible")
          | _ -> raise (SomethingIsWrong "proof_to_string: More than 2 children. Only zero, one, or two children possible with this implementation")
        )
    )

(** Prints theorem to terminal *)
let print_theorem
  theorem = print_endline (theorem_to_string theorem)

(** Prints proof to terminal *)
let print_proof
  proof = print_endline (proof_to_string proof)

(** Print a list of theorems to terminal, one on each line *)
let print_assumptions
  assumptions = 
  let assumptionsList = AssumptionSet.to_list assumptions in
  List.iter print_theorem assumptionsList









(* Prover methods --------------------------------------------------------------------------------------------------------------------------------------*)

(** Generates the new set of assumptions using the CON ELIM and IMP ELIM rules *)
let rec gen_new_assumptions
  assumptionSet theoremsToAdd map =

  (* CON Elimination rule. For a list of theorems, adds the children of CON to the list. Does so recursively. For example, [A&(B&C)] returns [A&(B&C),A,B&C,B,C] *)
  let rec handle_con_elim 
    theoremsToAdd map = 
    match theoremsToAdd with
    | theorem :: theoremsToAdd -> 
      (
        match theorem with
        | CON (left, right) -> 
          (
            let leftAssumpAndMap = handle_con_elim [left] map in match leftAssumpAndMap with LIST_AND_MAP (leftAssumptions, leftMap) -> 
              let leftNewMap = TheoremMap.add left (ProofTopSet.singleton (PROOF_TOP (CON1_ELIM, [theorem]))) leftMap in
            let rightAssumpAndMap = handle_con_elim [right] map in match rightAssumpAndMap with LIST_AND_MAP (rightAssumptions, rightMap) ->
              let rightNewMap = TheoremMap.add right (ProofTopSet.singleton (PROOF_TOP (CON2_ELIM, [theorem]))) rightMap in
            let restAssumpAndMap = handle_con_elim theoremsToAdd map in match restAssumpAndMap with LIST_AND_MAP (otherAssumptions, otherMap) ->
            let theorem_map_merge _ proofSet1 proofSet2 = match proofSet1, proofSet2 with 
              | Some proofSet1, Some proofSet2 -> Some (ProofTopSet.union proofSet1 proofSet2)
              | Some proofSet1, None -> Some proofSet1
              | None, Some proofSet2 -> Some proofSet2
              | _ -> None
            in
            let leftRightMap = TheoremMap.merge (theorem_map_merge) leftNewMap rightNewMap in
            let newMap = TheoremMap.merge (theorem_map_merge) leftRightMap otherMap in
            LIST_AND_MAP ([theorem] @ leftAssumptions @ rightAssumptions @ otherAssumptions, newMap)
          )
        | _ -> 
          (
            let assumpAndMap = handle_con_elim theoremsToAdd map in match assumpAndMap with LIST_AND_MAP (assumptions, newMap) ->
            LIST_AND_MAP ([theorem] @ (assumptions), newMap)
          )
      )
    | [] -> LIST_AND_MAP ([], map) in
  
  (* Breaks apart all outside CON theorems being added to the assumption set using the CON ELIM rule and feeds them into the IMP ELIM rule *)
  let assumptAndMap = handle_con_elim theoremsToAdd map in match assumptAndMap with LIST_AND_MAP (assumptions, newMap) ->
  let conElimTheoremsToAdd = AssumptionSet.of_list assumptions in
  let conElimNotInAssumptionSetTheoremsToAdd = AssumptionSet.diff conElimTheoremsToAdd assumptionSet in
  handle_imp_elim assumptionSet conElimNotInAssumptionSetTheoremsToAdd newMap

(** Takes in current assumptions and the new theorems to add as assumptions. Does IMP ELIM rule and feeds any new derived assumptions back into gen_new_assumptions *)
and handle_imp_elim 
  assumptionSet newTheoremsToAdd map = 
  let mapRef = ref map in
  let assumptionSet = AssumptionSet.union assumptionSet newTheoremsToAdd in

  (* Returns the conclusion of the IMP theorem if the hypothesis of theorem matches the hypothesis given, None otherwise *)
  let conc_hypo_match
  hypothesis theorem = match theorem with 
  | IMP (hypo_theorem, conclusion) -> 
      if hypo_theorem = hypothesis 
        then 
          (
            mapRef := TheoremMap.add conclusion (ProofTopSet.singleton (PROOF_TOP (IMP_ELIM, [theorem; hypothesis]))) !mapRef;
            Some conclusion 
          )
        else None
  | _ -> None in

  (* Returns the conlusions of all implications in assumptionSet if the implication's hypothesis is in possibleHypothesis *)
  let rec get_conc_if_hypo_match_list
    assumptionSet possibleHypotheses =
    match possibleHypotheses with
    | hypothesis :: hypotheses -> 
        (
          let conclusions = AssumptionSet.to_list (AssumptionSet.filter_map (conc_hypo_match hypothesis) assumptionSet) in
          conclusions @ (get_conc_if_hypo_match_list assumptionSet hypotheses)
        )
    | [] -> [] in

  (* Gets the conclusions of all IMP theorems in assumptionSet where the hypothesis is in newTheoremsToAdd and the conclusion is not already an assumption *)
  let impMatchAssumptionSetConc = AssumptionSet.of_list (get_conc_if_hypo_match_list assumptionSet (AssumptionSet.to_list newTheoremsToAdd)) in
  (* Gets the conclusions of all IMP theorems in newTheoremsToadd where the hyptohesis is in assumptionSet and the conclusion is not already an assumption *)
  let impMatchTheoremsToAddConc = AssumptionSet.of_list (get_conc_if_hypo_match_list newTheoremsToAdd (AssumptionSet.to_list assumptionSet)) in
  let impMatchBothSetsConc = AssumptionSet.union impMatchAssumptionSetConc impMatchTheoremsToAddConc in
  let impMatchBothConcNotInAssumptionSet = AssumptionSet.diff impMatchBothSetsConc assumptionSet in

  (* If no new conclusions have been generated, convergence has been reached and all new possible assumptions have been generated,
     else generate new assumptions *)
  if AssumptionSet.is_empty impMatchBothConcNotInAssumptionSet
    then SET_AND_MAP (assumptionSet, !mapRef)
    else gen_new_assumptions assumptionSet (AssumptionSet.to_list impMatchBothConcNotInAssumptionSet) !mapRef

(**  Main proof function.
  If the theorem is an assumption, then get the shortest proof.
  Else check if theorem is of type CON, IMP, DIS, or S.
  Do INTRO rule corresponding to type CON, IMP, or DIS.
  If proof fails, do DIS ELIM rule if possible and reconsider theorem. If not possible, then fail.
  Each time the IMP INTRO and DIS ELIM rule happen, add to Assumptions and use CON ELIM and IMP ELIM to add anymore to assumptions *)
let rec prover
  theorem assumptions usedDIS map =
  if AssumptionSet.mem theorem assumptions 
    then 
      ( 
        PROOF (CONNECTION, [get_proof theorem map], 1)
      )
    else
      (
        match theorem with
        | CON (left, right) -> 
          (
            let leftProof = prover left assumptions usedDIS map in
            let rightProof = prover right assumptions usedDIS map in
            let successLeft = is_successful leftProof in
            let successRight = is_successful rightProof in
            if successLeft && successRight
              then PROOF (CON_INTRO, [leftProof; rightProof], 1)
              else handle_dis_elim theorem assumptions usedDIS map
          )
        | IMP (left, right) ->
            (
              let mapWithLeft = addAssumptionToMap left map in
              let assumptionsAndMap = gen_new_assumptions assumptions [left] mapWithLeft in match assumptionsAndMap with SET_AND_MAP(assumptions, newMap) ->
              let proof = prover right assumptions usedDIS newMap in
              let success = is_successful proof in
              if success
                then PROOF (IMP_INTRO (left), [proof], 1)
                else handle_dis_elim theorem assumptions usedDIS map
            )
        | DIS (left, right) ->
          (
            let leftProof = prover left assumptions usedDIS map in
            let successLeft = is_successful leftProof in
            if not successLeft
              then (let rightProof = prover right assumptions usedDIS map in
                let successRight = is_successful rightProof in
                if not successRight
                  then handle_dis_elim theorem assumptions usedDIS map
                  else PROOF (DIS2_INTRO (left), [rightProof], 1)) 
              else PROOF (DIS1_INTRO (right), [leftProof], 1)
          )
        | S _ -> handle_dis_elim theorem assumptions usedDIS map
        | F -> handle_dis_elim theorem assumptions usedDIS map
      )

(** Handles the DIS Elimination rule. If a theorem in the assumptions has DIS as the outer operator and has not been broken apart before,
    generate the new assumption sets and try to prove the theorem again using the DIS ELIM rule*)
and handle_dis_elim 
  theorem assumptions usedDIS map = 

  (* Filters a set based on the predicate that a theorom had DIS as the outer operator and hasn't been used before.
  Returns an arbitrary element from the set, None if empty *)
  let get_dis assumptionSet usedDIS = 
    let is_dis theorem = match theorem with DIS (_, _) -> true | _ -> false in
    let disAssumptionSet = AssumptionSet.filter is_dis assumptionSet in
    let disAssumptionSetNotUsed = AssumptionSet.diff disAssumptionSet usedDIS in
    AssumptionSet.choose_opt disAssumptionSetNotUsed in
  
  (* foundDis is a randomly chosen unused DIS assumption. If no such assumption exists, proof fails.
     If one does exist, do DIS ELIM rule. If fails, repeat until success or failure *)
  let foundDis = get_dis assumptions usedDIS in
  match foundDis with
  | None -> PROOF (FAILURE, [], 0)
  | Some DIS (left, right) -> 
    (
      let usedDIS = AssumptionSet.add (DIS (left, right)) usedDIS in

      let mapWithLeft = addAssumptionToMap left map in
      let assumptionsAndMapLeft = gen_new_assumptions assumptions [left] mapWithLeft in match assumptionsAndMapLeft with SET_AND_MAP(assumptionsLeft, newLeftMap) ->
      let leftProof = prover theorem assumptionsLeft usedDIS newLeftMap in

      let mapWithRight = addAssumptionToMap right map in
      let assumptionsAndMapRight = gen_new_assumptions assumptions [right] mapWithRight in match assumptionsAndMapRight with SET_AND_MAP(assumptionsRight, newRightMap) ->
      let rightProof = prover theorem assumptionsRight usedDIS newRightMap in
      if (is_successful leftProof) && (is_successful rightProof)
        (* TODO: Add proof of foundDis *)
        then PROOF (DIS_ELIM (DIS (left, right)), [get_proof (DIS (left, right)) map; leftProof; rightProof], 1)
        else handle_dis_elim theorem assumptions usedDIS map
    )
  | _ -> raise (SomethingIsWrong "handle_dis_elim: DIS Theorem found in assumptions doesn't match None or DIS (left, right, false)")

  and get_depth_proof proof = match proof with PROOF (_, _, depth) -> depth
  and get_proof_proofTop map proofTop = match proofTop with
    | PROOF_TOP (IMP_ELIM, [theoremUsed; conclusion]) -> 
      (
        let theoremUsedProof = get_proof theoremUsed map in
        let conclusionProof = get_proof conclusion map in
        let depth = max (get_depth_proof theoremUsedProof) (get_depth_proof conclusionProof) in
        PROOF (IMP_ELIM, [theoremUsedProof; conclusionProof], depth)
      )
    | PROOF_TOP (CON1_ELIM, [theoremUsed]) -> let proof = get_proof theoremUsed map in PROOF (CON1_ELIM, [proof], get_depth_proof proof)
    | PROOF_TOP (CON2_ELIM, [theoremUsed]) -> let proof = get_proof theoremUsed map in PROOF (CON2_ELIM, [proof], get_depth_proof proof)
    | PROOF_TOP (ASSUMPTION assumption, []) -> PROOF (ASSUMPTION assumption, [], 0)
    | _ -> raise (SomethingIsWrong "get_proof_proofTop: rule used in PROOF_TOP that is not IMP or CON ELIM or ASSUMPTION. Impossible")

  and get_proof theorem map =
    let proofTopSet = TheoremMap.find theorem map in
    let proofTopList = ProofTopSet.to_list proofTopSet in
    let proofList = List.map (get_proof_proofTop map) proofTopList in
    List.fold_left (fun prf1 prf2 -> if get_depth_proof prf1 < get_depth_proof prf2 then prf1 else prf2) (PROOF (FAILURE, [], max_int)) proofList

(** Returns true if the proof is successful, false otherwise *)
and is_successful
  proof = match proof with
  | PROOF (_, _, 1) -> true
  | _ -> false

(** Removes the current value for theorem in map and replaces it with the ProofTopSet with a single PROOF_TOP with rule ASSUMPTION *)
and addAssumptionToMap theorem map = TheoremMap.update theorem (fun _ -> Some (ProofTopSet.singleton (PROOF_TOP (ASSUMPTION theorem, [])))) map

(** Calls the prover with an empty assumption set and empty usedDis set *)
let theorem_to_proof
  theorem = prover theorem AssumptionSet.empty AssumptionSet.empty TheoremMap.empty

(** First, prints the theorem to terminal. Then, tries to prove the theorem. Finaly, prints the proof (even upon failure) to terminal.*)
let test_theorem
  theorem = 
  print_theorem theorem;
  let proof_theorem = theorem_to_proof theorem in
  print_proof proof_theorem;
  print_newline()


(* Code extraction -------------------------------------------------------------------------------------------------------------------------------------*)

(** program data type *)
type program = 

  | VAR of int (** Introduction of a variable*)

  | PAIR of program * program (** Creates a pair *)

  | ABSTR of program * program (** Lambda abstraction *)

  | INL of theorem * program (** Left injection into a sum type *)

  | INR of theorem * program (** Right injection into a sum type *)

  | FST of program (** Gets the first element of a pair *)

  | SND of program (** Gets the second element of a pair *)

  | APP of program * program (** Application of the first program to the next *)

  | CASE of program * program * program * program * program (** Matches the first program with either the fourth (returns second) or fifth (returns third) program. *)


(** The tag used when using the IMP INTRO or DIS ELIM rules *)
let annotation_number = ref (-1)

(** Gets the next annotation number *)
let next_annotation = 
  fun () ->
    annotation_number := !annotation_number + 1;
    !annotation_number

(** Converts a proof to it's corresponding program. Note that while this implementation is 1-1, it does not have to be (See note in get_theoremTag) *)
let rec program_extractor 
  map proof = 
  let program_extractor_same_map = program_extractor map in
  match proof with
  | PROOF (ASSUMPTION assumption, [], _) -> VAR (TheoremMap.find assumption map)
  | PROOF (CON_INTRO, [leftProof; rightProof], _) -> PAIR (program_extractor_same_map leftProof, program_extractor_same_map rightProof)
  | PROOF (IMP_INTRO (theorem), [proof], _) -> 
      (
        let mapRef = ref map in
        let theoremTag = get_theoremTag theorem mapRef in
        let newMap = !mapRef in
        ABSTR (VAR theoremTag, program_extractor newMap proof)
      )
  | PROOF (DIS1_INTRO (theorem), [proof], _) -> INL (theorem, program_extractor_same_map proof)
  | PROOF (DIS2_INTRO (theorem), [proof], _) -> INR (theorem, program_extractor_same_map proof)
  | PROOF (CON1_ELIM, [proof], _) -> FST (program_extractor_same_map proof)
  | PROOF (CON2_ELIM, [proof], _) -> SND (program_extractor_same_map proof)
  | PROOF (IMP_ELIM, [leftProof; rightProof], _) -> APP (program_extractor_same_map leftProof, program_extractor_same_map rightProof)
  | PROOF (DIS_ELIM (theorem), [leftRightProof; leftProof; rightProof], _) -> 
    (
      match theorem with
      | DIS (left, right) ->
        (
          let mapRef = ref map in
          let theoremTagLeft = get_theoremTag left mapRef in
          let theoremTagRight = get_theoremTag right mapRef in
          let newMap = !mapRef in
          CASE (program_extractor newMap leftRightProof, program_extractor newMap leftProof, program_extractor newMap rightProof, VAR theoremTagLeft, VAR theoremTagRight)
        )
      | _ -> raise (SomethingIsWrong "program_extractor: Non dis theorem used in DIS_ELIM rule")
    )
  | PROOF (CONNECTION, [proof], _) -> program_extractor_same_map proof
  | PROOF (ASSUMPTION _, _, _) -> raise (SomethingIsWrong "program_extractor: Assumption rule does not have 0 children")
  | PROOF (CON_INTRO, _, _) -> raise (SomethingIsWrong "program_extractor: CON_INTRO rule does not have 2 children")
  | PROOF (IMP_INTRO (_), _, _) -> raise (SomethingIsWrong "program_extractor: IMP_INTRO rule does not have 1 child")
  | PROOF (DIS1_INTRO (_), _, _) -> raise(SomethingIsWrong "program_extractor: DIS1_INTRO rule does not have 1 child")
  | PROOF (DIS2_INTRO (_), _, _) -> raise(SomethingIsWrong "program_extractor: DIS2_INTRO rule does not have 1 child")
  | PROOF (CON1_ELIM, _, _) -> raise(SomethingIsWrong "program_extractor: CON1_ELIM rule does not have 1 child")
  | PROOF (CON2_ELIM, _, _) -> raise(SomethingIsWrong "program_extractor: CON2_ELIM rule does not have 1 child")
  | PROOF (IMP_ELIM, _, _) -> raise(SomethingIsWrong "program_extractor: IMP_ELIM rule does not have 2 children")
  | PROOF (DIS_ELIM (_), _, _) -> raise(SomethingIsWrong "program_extractor: DIS_ELIM rule does not have 3 children")
  | PROOF (FAILURE, _, _) -> raise(SomethingIsWrong "program_extractor: FAILURE rule used")
  | PROOF (CONNECTION, _, _) -> raise(SomethingIsWrong "program_extractor: CONNECTION rule does not have 1 child")

(** Gets the next theoremTag if one does not exist for the IMP INTRO and DIS ELIM rules. If one does exist, returns it *)
and get_theoremTag
  theorem mapRef =
  match TheoremMap.find_opt theorem !mapRef with
  (* Note: this is a choice to always use the tag associated with the first time the theorem gets added by the IMP INTRO or DIS ELIM rule. Can be changed *)
        | Some theoremTag -> theoremTag
        | None -> 
          (
            let theoremTag = next_annotation () in
            mapRef := TheoremMap.add theorem theoremTag !mapRef;
            theoremTag
          )

(** Calls the program extractor with an empty theorem-to-tag map *)
let proof_to_program
  proof = 
  annotation_number := -1;
  program_extractor TheoremMap.empty proof

(** Takes in a theorem, proves it, and then returns the corresponding program *)
let theorem_to_program theorem =
  let proof = theorem_to_proof theorem in
  match proof with
  | PROOF (_, _, 1) -> proof_to_program proof
  | _ -> raise (ProofFailure ("The proof has failed: " ^ (proof_to_string proof)))

(** Converts an abstract program to a runnable program in OCaml, returns a string *)
let rec ocaml_converter
  program =
  match program with
  | VAR (theoremTag) -> "var" ^ (string_of_int theoremTag)
  | PAIR (leftProgram, rightProgram) -> "(" ^ (ocaml_converter leftProgram) ^ "," ^ (ocaml_converter rightProgram) ^ ")"
  (* | ABSTR (VAR theoremTag, right) -> "implement me"
  | INL (otherType, injectedProgram) -> "implement me"
  | INR (otherType, injectedProgram) -> "implement me" *)
  | FST (program) -> "fst " ^ (ocaml_converter program)
  | SND (program) -> "snd " ^ (ocaml_converter program)
  | APP (leftProgram, rightProgram) -> (ocaml_converter leftProgram) ^ " " ^ (ocaml_converter rightProgram)
  (* | CASE (matchMeProgram, leftProgram, rightProgram, leftTheoremTag, rightTheoremTag) -> "Impelment Me" *)
  | _ -> raise (SomethingIsWrong "ocaml_converted: Impossible program definition")


(** Calls the ocaml_converter and post-proccesses the result *)
let program_to_ocaml 
  program = "let myProgram " ^ (ocaml_converter program)

(* Ease of use for user --------------------------------------------------------------------------------------------------------------------------------*)

(* Define operators for NOT, CON, DIS, and IMP. Precedence rules apply !! > ** > @@ > &&. All binary operators are right associative.
   Yes, it is confusing to have IMP defined as &&, however, in order to use only basic OCaml operators, which have a certain precedence order, 
   they have to be overwritten like this. https://v2.ocaml.org/manual/expr.html. Otherwise would have to download and use a dependency *)
(** Not operator *)
let ( !! )
  x = IMP(x, F)

(** Conjunction operator *)
let ( ** )
  x y = CON(x, y)

(** Disjunction operator *)
let ( @@ )
  x y = DIS(x, y)

(** Implication operator *)
let ( && ) 
  x y = IMP(x, y)

(** S 1 *)
let a = S 1

(** S 2 *)
let b = S 2

(** S 3 *)
let c = S 3

(** S 4 *)
let d = S 4

(** S 5 *)
let e = S 5

(** S 6 *)
let f = S 6

(** S 7 *)
let g = S 7

(** S 8 *)
let h = S 8

(** S 9 *)
let i = S 9

(** S 10 *)
let j = S 10