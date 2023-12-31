(** theorem data type *)
type theorem =

  | CON of theorem * theorem (** Conjunction constructor - left, right *)

  | DIS of theorem * theorem (** Disjunction constructor - left, right *)

  | IMP of theorem * theorem * bool (** Implication constructor - hypothesis, conclusion, hypothesis proven *)

  | S of int (** Singleton proposition constructor *)

  | F (** Falsehood constructor *)

  | T (** Truth constructor *)

(** rule data type *)
type rule = 

  | CON_INTRO (** Conjuction introduction rule *)

  | DIS1_INTRO of theorem (** Left disjunction introduction rule - Right side of DIS theorem *)

  | DIS2_INTRO of theorem (** Right disjunction introduction rule - Left side of DIS theorem *)

  | IMP_INTRO of theorem (** Implication introduction rule - hypothesis of IMP theorem *)

  | IMP_ELIM  (** Implication elimination rule *)

  | CON1_ELIM (** Left conjunction elimination rule *)

  | CON2_ELIM (** Right conjunction elimination rule *)

  | DIS_ELIM of theorem (** Disjunction elimination rule - DIS theorem being broken apart *)

  | ASSUMPTION of theorem (** Assumption rule - assumption *)

  | FAILURE of string (** Signifies proof has failed - message *)

  | F_ELIM (** Falsehood Elimination rule *)

  | T_INTRO (** Truth Introduction rule*)

(** proof data type *)
type proof = 

  PROOF of rule (* Rule used *)
          * proof list (* Proof of the theorem *)
          * bool (* Success of the proof *)
          * int (* Depth of the proof *)

(** temp proof data type when keeping track of IMP and CON ELIM rules *)
type proof_top = 

  PROOF_TOP of rule (* Rule used *)
              * theorem list (* All possible theorems this theorem can be derived from *)



module Theorem = struct
  type t = theorem
  let compare = compare
end

module ProofTop = struct
  type t = proof_top
  let compare = compare
end

module DerivedSet = Set.Make (Theorem);;

module ProofTopSet = Set.Make (ProofTop);;

module TheoremMap = Map.Make (Theorem);;



(** Type containing a set of theorems, a map of theorems to prooftops, and a map of theorems to proofs - use to pass data back from gen new derived assumptions *)
type setAndMapAndMap = 

  | SET_AND_MAP_AND_MAP of DerivedSet.t * ProofTopSet.t TheoremMap.t * proof TheoremMap.t (** Derived assumptions, Map of theorem to ProofTopSet (tracks CON and IMP ELIM), Map of theorem to proof (tracks all INTRO and DIS ELIM)*)

(** Type containing a list of theorems and a map of theorems to proofTop sets. Used in handling con elim rule *)
  type listAndMap = 

  | LIST_AND_MAP of theorem list * ProofTopSet.t TheoremMap.t (** theorems a theorem is derived from, Map of theorem to ProofTopSet *)

(** Custom exception to print out information to terminal *)
exception CustomException of string

(** Exception for when a rule is used where it is not supposed to *)
exception IncorrectRuleUsage of string

(** Wrong amount of children used in a rule *)
exception WrongChildrenAmount of string

(** Exception for when the proof fails *)
exception ProofFailure of string

(** Custom exception for when F_ELIM rule used *)
exception InvalidInput of string

(** Converts theorem to string *)
let rec theorem_to_string
  theorem = match theorem with
  | CON (left, right) -> parenthesize left ^ " \u{2227} " ^ parenthesize right
  | DIS (left, right) -> parenthesize left ^ " \u{2228} " ^ parenthesize right
  | IMP (left, right, _) -> 
    (
      match right with 
      | F -> "\u{ac}" ^ parenthesize left
      | _ -> parenthesize left ^ " \u{2283} " ^ parenthesize right
    )
  | S value -> string_of_int value
  | F -> "\u{22A5}"
  | T -> "\u{22a4}"

(** Adds parenthesis around all theorems except singletons or falsehood *)
and parenthesize
  theorem = 
  match theorem with
  | S value -> string_of_int value
  | F -> "\u{22A5}"
  | T -> "\u{22a4}"
  | _ -> "(" ^ theorem_to_string theorem ^ ")"

(** Converts proof to a string which takes up only one line *)
let rec proof_to_oneline_string 
  proof = match proof with 
  | PROOF(rule, children, _, _) ->
    (
      let inside = match children with
        | child :: [] -> "(" ^ proof_to_oneline_string child ^ ")"
        | left :: [right] -> "(" ^ proof_to_oneline_string left ^ " " ^ proof_to_oneline_string right ^ ")"
        | left :: middle :: [right] -> "(" ^ proof_to_oneline_string left ^ " " ^ proof_to_oneline_string middle ^ " " ^ proof_to_oneline_string right ^ ")"
        | [] -> ""
        | _ -> raise (WrongChildrenAmount "proof_to_oneline_string: More than 3 children. Only zero, one, two, or 3 children possible with this implementation") in
      match rule with
      | IMP_INTRO (_) -> "\u{2283}I" ^ inside
      | CON_INTRO -> "\u{2227}I" ^ inside
      | DIS1_INTRO (_) -> "\u{2228}I1" ^ inside
      | DIS2_INTRO (_) -> "\u{2228}I2" ^ inside
      | ASSUMPTION theorem -> parenthesize theorem
      | FAILURE (message) -> "FAILURE: " ^ message
      | DIS_ELIM (_) -> "\u{2228}E" ^ inside
      | CON1_ELIM -> "\u{2227}E1" ^ inside
      | CON2_ELIM -> "\u{2227}E2" ^ inside
      | IMP_ELIM -> "\u{2283}E" ^ inside
      | F_ELIM -> "\u{22A5}E" ^ inside
      | T_INTRO -> "\u{22a4}I"
    )

(** Converts proof to a string which takes up multiple lines *)
let rec proof_to_string
  proof depth = match proof with
  | PROOF (rule, children, _, _) ->
    (
      let spacingString = (String.make ((depth + 1) * 2) ' ') in
      let make_line line = match rule with ASSUMPTION theorem -> parenthesize theorem | _ -> "\n" ^ spacingString ^ proof_to_string line (depth + 1) in
      let inside = match children with
        | [] -> "\n"
        | [child] -> make_line child
        | [left; right] -> make_line left ^ make_line right
        | [left;middle;right] -> make_line left ^ make_line middle ^ make_line right
        | _ -> raise (WrongChildrenAmount "proof_to_string: More than 3 children. Only zero, one, two, or 3 children possible with this implementation") in
      match rule with 
      | IMP_INTRO (_) -> "\u{2283}I" ^ inside
      | CON_INTRO -> "\u{2227}I" ^ inside
      | DIS1_INTRO (_) -> "\u{2228}I1" ^ inside
      | DIS2_INTRO (_) -> "\u{2228}I2" ^ inside
      | ASSUMPTION theorem -> parenthesize theorem
      | FAILURE (message) -> "FAILURE: " ^ message
      | DIS_ELIM (_) -> "\u{2228}E" ^ inside
      | CON1_ELIM -> "\u{2227}E1" ^ inside
      | CON2_ELIM -> "\u{2227}E2" ^ inside
      | IMP_ELIM -> "\u{2283}E" ^ inside
      | F_ELIM -> "\u{22A5}E" ^ inside
      | T_INTRO -> "\u{22a4}I"
    )

(** Prints theorem to terminal *)
let print_theorem
  theorem = print_endline (theorem_to_string theorem)

(** Prints proof to terminal *)
let print_proof
  proof = print_endline (proof_to_string proof 0)

(** Prints oneline proof to terminal *)
let print_proof_oneline
  proof = print_endline (proof_to_oneline_string proof)

(** Print a list of theorems to terminal, one on each line *)
let print_derived
  derived = 
  let derivedList = DerivedSet.to_list derived in
  List.iter print_theorem derivedList

(* Prover methods --------------------------------------------------------------------------------------------------------------------------------------*)

(** Generates the new set of derived assumptions using the CON ELIM and IMP ELIM rules *)
let rec gen_new_assumptions
  maxDepthBuildUp assumptionSet theoremsToAdd usedDIS proofTopMap proofMap =
  (* CON Elimination rule. For a list of theorems, adds the children of CON to the list. Does so recursively. For example, [A&(B&C)] returns [A&(B&C),A,B&C,B,C] *)
  let rec handle_con_elim 
    theoremsToAdd proofTopMap = 
    match theoremsToAdd with
    | theorem :: theoremsToAdd -> 
      (
        match theorem with
        | CON (left, right) -> 
          (
            match handle_con_elim [left] proofTopMap with LIST_AND_MAP (leftAssumptions, leftMap) -> 
              let leftNewMap = TheoremMap.add left (ProofTopSet.singleton (PROOF_TOP (CON1_ELIM, [theorem]))) leftMap in
            match handle_con_elim [right] proofTopMap with LIST_AND_MAP (rightAssumptions, rightMap) ->
              let rightNewMap = TheoremMap.add right (ProofTopSet.singleton (PROOF_TOP (CON2_ELIM, [theorem]))) rightMap in
            match handle_con_elim theoremsToAdd proofTopMap with LIST_AND_MAP (otherAssumptions, otherMap) ->
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
            match handle_con_elim theoremsToAdd proofTopMap with LIST_AND_MAP (assumptions, newMap) ->
            LIST_AND_MAP ([theorem] @ (assumptions), newMap)
          )
      )
    | [] -> LIST_AND_MAP ([], proofTopMap) in
  
  (* Breaks apart all outside CON theorems being added to the assumption set using the CON ELIM rule and feeds them into the IMP ELIM rule *)
  match handle_con_elim theoremsToAdd proofTopMap with LIST_AND_MAP (assumptions, newMap) ->
  let conElimTheoremsToAdd = DerivedSet.of_list assumptions in
  let conElimNotInAssumptionSetTheoremsToAdd = DerivedSet.diff conElimTheoremsToAdd assumptionSet in
  handle_imp_elim maxDepthBuildUp assumptionSet conElimNotInAssumptionSetTheoremsToAdd usedDIS newMap proofMap

(** Takes in current assumptions and the new theorems to add as assumptions. Does IMP ELIM rule and feeds any new derived assumptions back into gen_new_assumptions *)
and handle_imp_elim 
  maxDepthBuildUp assumptionSet newTheoremsToAdd usedDIS proofTopMap proofMap = 
  let mapRef = ref proofTopMap in
  let assumptionSet = DerivedSet.union assumptionSet newTheoremsToAdd in
  let assumptionSetRef = ref assumptionSet in

  (* Returns the conclusion of the IMP theorem if the hypothesis of theorem matches the hypothesis given and the theorem has not already been unlucked, None otherwise *)
  let conc_hypo_match
  hypothesis theorem = match theorem with 
  | IMP (hypo_theorem, conclusion, _) -> 
      if hypo_theorem = hypothesis 
        then 
          (
            let proofTop = (PROOF_TOP (IMP_ELIM, [theorem; hypothesis])) in
            let proofTopSet = TheoremMap.find_opt conclusion !mapRef in
            let () = (match proofTopSet with
            | None -> mapRef := TheoremMap.add conclusion (ProofTopSet.singleton proofTop) !mapRef;
            | Some proofTopSet -> mapRef := TheoremMap.add conclusion (ProofTopSet.add proofTop proofTopSet) !mapRef) in
            assumptionSetRef := DerivedSet.remove theorem !assumptionSetRef;
            assumptionSetRef := DerivedSet.add (IMP (hypo_theorem, conclusion, true)) !assumptionSetRef;
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
          let conclusions = DerivedSet.to_list (DerivedSet.filter_map (conc_hypo_match hypothesis) assumptionSet) in
          conclusions @ (get_conc_if_hypo_match_list assumptionSet hypotheses)
        )
    | [] -> [] in

  (* Gets the conclusions of all IMP theorems in assumptionSet where the hypothesis is in newTheoremsToAdd and the conclusion is not already an assumption *)
  let impMatchAssumptionSetConc = DerivedSet.of_list (get_conc_if_hypo_match_list assumptionSet (DerivedSet.to_list newTheoremsToAdd)) in
  (* Gets the conclusions of all IMP theorems in newTheoremsToadd where the hyptohesis is in assumptionSet and the conclusion is not already an assumption *)
  let impMatchTheoremsToAddConc = DerivedSet.of_list (get_conc_if_hypo_match_list newTheoremsToAdd (DerivedSet.to_list assumptionSet)) in
  let impMatchBothSetsConc = DerivedSet.union impMatchAssumptionSetConc impMatchTheoremsToAddConc in
  let impMatchBothConcNotInAssumptionSet = DerivedSet.diff impMatchBothSetsConc assumptionSet in

  (* If no new conclusions have been generated, convergence has been reached and all new possible derived assumptions have been generated,
     else generate new derived assumptions *)
  if DerivedSet.is_empty impMatchBothConcNotInAssumptionSet
    then 
      (
        (* Get all imp theorems not yet broken apart. Try to prove assumption.
           If provable, add theorem to proof to map. Add hypothesis to assumptions.
           If something is provable, rerun gen_new_assumptions, else return stuff *)
        let proofMapRef = ref proofMap in
        let unlockedFlag = ref false in
        let provedHypothesises = ref [] in
        let prove_unproven_imp_hypo theorem =
          match theorem with
          | IMP (hypothesis, conclusion, false) -> 
            (
              let tempAssumptionSet = DerivedSet.add (IMP (hypothesis, conclusion, true)) (DerivedSet.remove theorem !assumptionSetRef) in
              let proof = prover ~maxDepthBuildUp:(maxDepthBuildUp - 1) hypothesis tempAssumptionSet usedDIS !mapRef !proofMapRef in
              match proof with
              | PROOF (FAILURE (_), [], _, _) -> ()
              | _-> 
                (
                  proofMapRef := TheoremMap.add hypothesis proof !proofMapRef;
                  provedHypothesises := !provedHypothesises @ [hypothesis];
                  unlockedFlag := true;
                )
            )
          | _ -> ()
          in
        DerivedSet.iter prove_unproven_imp_hypo !assumptionSetRef;
        if !unlockedFlag
          then gen_new_assumptions maxDepthBuildUp !assumptionSetRef !provedHypothesises usedDIS !mapRef !proofMapRef
          else SET_AND_MAP_AND_MAP (!assumptionSetRef, !mapRef, !proofMapRef)
      )
    else gen_new_assumptions maxDepthBuildUp !assumptionSetRef (DerivedSet.to_list impMatchBothConcNotInAssumptionSet) usedDIS !mapRef proofMap

(**  Main proof function.
  If the theorem is an assumption, then get the shortest proof.
  Else check if theorem is of type CON, IMP, DIS, or S.
  Do INTRO rule corresponding to type CON, IMP, or DIS.
  If proof fails, do DIS ELIM rule if possible and reconsider theorem. If not possible, then fail.
  Each time the IMP INTRO and DIS ELIM rule happen, add to Assumptions and use CON ELIM and IMP ELIM to add anymore to assumptions.
  Also, try to prove the hypothesis of any unbroken IMP assumption *)
and prover
?(maxDepthBuildUp = 100) theorem assumptions usedDIS proofTopMap proofMap =
  if maxDepthBuildUp < 0 then PROOF (FAILURE "Depth limit exceeded in prover", [], false, max_int) else
  if DerivedSet.mem theorem assumptions
    then get_proof maxDepthBuildUp theorem proofTopMap proofMap
    else
      if DerivedSet.mem F assumptions
        then 
          (
            let proof = get_proof (maxDepthBuildUp - 1) F proofTopMap proofMap in
            PROOF (F_ELIM, [proof], true, get_depth_proof proof + 1)
          )
        else
          (
            match theorem with
            | CON (left, right) -> 
              (
                let leftProof = prover ~maxDepthBuildUp:(maxDepthBuildUp - 1) left assumptions usedDIS proofTopMap proofMap in
                if is_successful leftProof 
                  then (
                    let rightProof = prover ~maxDepthBuildUp:(maxDepthBuildUp - 1) right assumptions usedDIS proofTopMap proofMap in
                    if is_successful rightProof
                      then PROOF (CON_INTRO, [leftProof; rightProof], true, max (get_depth_proof leftProof) (get_depth_proof rightProof) + 1)
                      else handle_dis_elim maxDepthBuildUp theorem assumptions usedDIS proofTopMap proofMap
                  )
                  else handle_dis_elim maxDepthBuildUp theorem assumptions usedDIS proofTopMap proofMap
              )
            | IMP (left, right, _) ->
                (
                  (* print_theorem left; *)
                  let mapWithLeft = addAssumptionToMap left proofTopMap in
                  match gen_new_assumptions maxDepthBuildUp assumptions [left] usedDIS mapWithLeft proofMap with SET_AND_MAP_AND_MAP(assumptions, newMap, newProofMap) ->
                  let proof = prover ~maxDepthBuildUp:(maxDepthBuildUp - 1) right assumptions usedDIS newMap newProofMap in
                  if is_successful proof
                    then PROOF (IMP_INTRO (left), [proof], true, get_depth_proof proof + 1)
                    else handle_dis_elim maxDepthBuildUp theorem assumptions usedDIS proofTopMap proofMap
                )
            | DIS (left, right) ->
              (
                let leftProof = prover ~maxDepthBuildUp:(maxDepthBuildUp - 1) left assumptions usedDIS proofTopMap proofMap in
                let rightProof = prover ~maxDepthBuildUp:(maxDepthBuildUp - 1) right assumptions usedDIS proofTopMap proofMap in
                if (is_successful leftProof) && (is_successful rightProof)
                  then (
                    if get_depth_proof leftProof < get_depth_proof rightProof 
                      then PROOF (DIS1_INTRO (right), [leftProof], true, get_depth_proof leftProof + 1)
                      else PROOF (DIS2_INTRO (left), [rightProof], true, get_depth_proof rightProof + 1)
                  )
                  else (
                    if is_successful leftProof 
                      then PROOF (DIS1_INTRO (right), [leftProof], true, get_depth_proof leftProof + 1)
                      else (
                        if is_successful rightProof
                          then PROOF (DIS2_INTRO (left), [rightProof], true, get_depth_proof rightProof + 1)
                          else handle_dis_elim maxDepthBuildUp theorem assumptions usedDIS proofTopMap proofMap
                      )
                  )
              )
            | S _ -> handle_dis_elim maxDepthBuildUp theorem assumptions usedDIS proofTopMap proofMap
            | F -> handle_dis_elim maxDepthBuildUp theorem assumptions usedDIS proofTopMap proofMap
            | T -> PROOF (T_INTRO, [], true, 0)
          )

(** Handles the DIS Elimination rule. If a theorem in the assumptions has DIS as the outer operator and has not been broken apart before,
    generate the new assumption sets and try to prove the theorem again using the DIS ELIM rule*)
and handle_dis_elim 
maxDepthBuildUp theorem assumptions usedDIS proofTopMap proofMap = 

  (* Filters a set based on the predicate that a theorom had DIS as the outer operator and hasn't been used before.
  Returns an arbitrary element from the set, None if empty *)
  let get_dis assumptionSet usedDIS = 
    let is_dis theorem = match theorem with DIS (_, _) -> true | _ -> false in
    let disAssumptionSet = DerivedSet.filter is_dis assumptionSet in
    let disAssumptionSetNotUsed = DerivedSet.diff disAssumptionSet usedDIS in
    DerivedSet.choose_opt disAssumptionSetNotUsed in
  
  (* foundDis is a randomly chosen unused DIS assumption. If no such assumption exists, proof fails.
     If one does exist, do DIS ELIM rule. If fails, repeat until success or failure *)
  let foundDis = get_dis assumptions usedDIS in
  match foundDis with
  | None -> PROOF (FAILURE "Could not be proven", [], false, max_int)
  | Some DIS (left, right) -> 
    (
      let usedDIS = DerivedSet.add (DIS (left, right)) usedDIS in

      let mapWithLeft = addAssumptionToMap left proofTopMap in
      match gen_new_assumptions maxDepthBuildUp assumptions [left] usedDIS mapWithLeft proofMap with SET_AND_MAP_AND_MAP(assumptionsLeft, newLeftMap, newLeftProofMap) ->
      let leftProof = prover ~maxDepthBuildUp:(maxDepthBuildUp - 1) theorem assumptionsLeft usedDIS newLeftMap newLeftProofMap in

      let mapWithRight = addAssumptionToMap right proofTopMap in
      match gen_new_assumptions maxDepthBuildUp assumptions [right] usedDIS mapWithRight proofMap with SET_AND_MAP_AND_MAP(assumptionsRight, newRightMap, newRightProofMap) ->
      let rightProof = prover ~maxDepthBuildUp:(maxDepthBuildUp - 1) theorem assumptionsRight usedDIS newRightMap newRightProofMap in
      if (is_successful leftProof) && (is_successful rightProof)
        then 
          (
            let proof = get_proof (maxDepthBuildUp - 1) (DIS (left, right)) proofTopMap proofMap in
            let depth = max (max (get_depth_proof leftProof) (get_depth_proof rightProof)) (get_depth_proof proof) in
            PROOF (DIS_ELIM (DIS (left, right)), [proof; leftProof; rightProof], true, depth + 1)
          )
        else handle_dis_elim maxDepthBuildUp theorem assumptions usedDIS proofTopMap proofMap
    )
  | _ -> raise (CustomException "handle_dis_elim: DIS Theorem found in assumptions doesn't match None or DIS (left, right, false)")

(** Gets the depth of a proof *)
and get_depth_proof 
  proof = match proof with PROOF (_, _, _, depth) -> depth

(** Converts proofTop to type proof *)
and get_proof_proofTop 
  maxDepthBuildUp proofTopMap proofMap proofTop = 
  if maxDepthBuildUp = -1 then PROOF (FAILURE ("Depth limit exceeded in getting proof"), [], false, max_int) else
  match proofTop with
  | PROOF_TOP (IMP_ELIM, [theoremUsed; conclusion]) -> 
    (
      let theoremUsedProof = get_proof (maxDepthBuildUp - 1) theoremUsed proofTopMap proofMap in
      let conclusionProof = get_proof (maxDepthBuildUp - 1) conclusion proofTopMap proofMap in
      let depth = max (get_depth_proof theoremUsedProof) (get_depth_proof conclusionProof) in
      PROOF (IMP_ELIM, [theoremUsedProof; conclusionProof], true, depth + 1)
    )
  | PROOF_TOP (CON1_ELIM, [theoremUsed]) -> let proof = get_proof (maxDepthBuildUp - 1) theoremUsed proofTopMap proofMap in PROOF (CON1_ELIM, [proof], true, get_depth_proof proof + 1)
  | PROOF_TOP (CON2_ELIM, [theoremUsed]) -> let proof = get_proof (maxDepthBuildUp - 1) theoremUsed proofTopMap proofMap in PROOF (CON2_ELIM, [proof], true, get_depth_proof proof + 1)
  | PROOF_TOP (ASSUMPTION assumption, []) -> PROOF (ASSUMPTION assumption, [], true, 0)
  | _ -> raise (IncorrectRuleUsage "get_proof_proofTop: rule used in PROOF_TOP that is not IMP or CON ELIM or ASSUMPTION. Impossible")

(** Gets the shortest proof of a theorem *)
and get_proof 
  maxDepthBuildUp theorem proofTopMap proofMap =
  match (TheoremMap.find_opt theorem proofMap) with Some proof -> proof | _ ->
  let proofTopSet = TheoremMap.find theorem proofTopMap in
  let proofTopList = ProofTopSet.to_list proofTopSet in
  let proofList = List.map (get_proof_proofTop maxDepthBuildUp proofTopMap proofMap) proofTopList in
  List.fold_left (fun prf1 prf2 -> if get_depth_proof prf1 < get_depth_proof prf2 then prf1 else prf2) (PROOF (FAILURE "", [], false, max_int)) proofList

(** Returns true if the proof is successful, false otherwise *)
and is_successful
  proof = match proof with
  | PROOF (_, _, succ, _) -> succ

(** Removes the current value for theorem in map and replaces it with the ProofTopSet with a single PROOF_TOP with rule ASSUMPTION *)
and addAssumptionToMap theorem proofTopMap = TheoremMap.update theorem (fun _ -> Some (ProofTopSet.singleton (PROOF_TOP (ASSUMPTION theorem, [])))) proofTopMap

(** Calls the prover with an empty assumption set, empty usedDis set, empty proofTopMap, and empty proofMap *)
let theorem_to_proof
  ?(maxDepthBuildUp = 100) theorem = prover ~maxDepthBuildUp:maxDepthBuildUp theorem DerivedSet.empty DerivedSet.empty TheoremMap.empty TheoremMap.empty

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

  | ABT (** Aborts the program *)

  | UNT (** Unit element *)

type ('a, 'b) sum = | Left  of 'a | Right of 'b;;

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
  | PROOF (ASSUMPTION assumption, [], _, _) -> VAR (TheoremMap.find assumption map)
  | PROOF (CON_INTRO, [leftProof; rightProof], _, _) -> PAIR (program_extractor_same_map leftProof, program_extractor_same_map rightProof)
  | PROOF (IMP_INTRO (theorem), [proof], _, _) -> 
      (
        let mapRef = ref map in
        let theoremTag = get_theoremTag theorem mapRef in
        let newMap = !mapRef in
        ABSTR (VAR theoremTag, program_extractor newMap proof)
      )
  | PROOF (DIS1_INTRO (theorem), [proof], _, _) -> INL (theorem, program_extractor_same_map proof)
  | PROOF (DIS2_INTRO (theorem), [proof], _, _) -> INR (theorem, program_extractor_same_map proof)
  | PROOF (CON1_ELIM, [proof], _, _) -> FST (program_extractor_same_map proof)
  | PROOF (CON2_ELIM, [proof], _, _) -> SND (program_extractor_same_map proof)
  | PROOF (IMP_ELIM, [leftProof; rightProof], _, _) -> APP (program_extractor_same_map leftProof, program_extractor_same_map rightProof)
  | PROOF (DIS_ELIM (theorem), [leftRightProof; leftProof; rightProof], _, _) -> 
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
      | _ -> raise (CustomException "program_extractor: Non dis theorem used in DIS_ELIM rule")
    )
  | PROOF (F_ELIM, _, _, _) -> ABT
  | PROOF (T_INTRO, [], _, _) -> UNT
  | PROOF (ASSUMPTION _, _, _, _) -> raise (WrongChildrenAmount "program_extractor: Assumption rule does not have 0 children")
  | PROOF (CON_INTRO, _, _, _) -> raise (WrongChildrenAmount "program_extractor: CON_INTRO rule does not have 2 children")
  | PROOF (IMP_INTRO (_), _, _, _) -> raise (WrongChildrenAmount "program_extractor: IMP_INTRO rule does not have 1 child")
  | PROOF (DIS1_INTRO (_), _, _, _) -> raise(WrongChildrenAmount "program_extractor: DIS1_INTRO rule does not have 1 child")
  | PROOF (DIS2_INTRO (_), _, _, _) -> raise(WrongChildrenAmount "program_extractor: DIS2_INTRO rule does not have 1 child")
  | PROOF (CON1_ELIM, _, _, _) -> raise(WrongChildrenAmount "program_extractor: CON1_ELIM rule does not have 1 child")
  | PROOF (CON2_ELIM, _, _, _) -> raise(WrongChildrenAmount "program_extractor: CON2_ELIM rule does not have 1 child")
  | PROOF (IMP_ELIM, _, _, _) -> raise(WrongChildrenAmount "program_extractor: IMP_ELIM rule does not have 2 children")
  | PROOF (DIS_ELIM (_), _, _, _) -> raise(WrongChildrenAmount "program_extractor: DIS_ELIM rule does not have 3 children")
  | PROOF (T_INTRO, _, _, _) -> raise(WrongChildrenAmount "program_extractor: T_INTRO rule does not have 0 children")
  | PROOF (FAILURE (message), _, _, _) -> raise(ProofFailure ("program_extractor: FAILURE rule used - " ^ message))

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

(** Converts an abstract program to a string *)
let rec program_to_string
  program depth = 
  let spacingString = (String.make ((depth + 1) * 2) ' ') in
  match program with
  | VAR theoremTag -> "var" ^ string_of_int theoremTag
  | PAIR (left, right) -> "Pair (\n" ^ spacingString ^ (program_to_string left (depth + 1)) ^ ",\n" ^ 
      spacingString ^ (program_to_string right (depth + 1)) ^ "\n" ^ (String.make (depth * 2) ' ')  ^ ")"
  | ABSTR (VAR theoremTag, right) -> "\u{03BB}" ^ "var" ^ (string_of_int theoremTag) ^ ".\n" ^ spacingString ^ (program_to_string right (depth + 1))
  | INL (otherType, injectedProgram) -> "inl type " ^ (theorem_to_string otherType) ^ " to " ^ (program_to_string injectedProgram (depth + 1))
  | INR (otherType, injectedProgram) -> "inr type " ^ (theorem_to_string otherType) ^ " to " ^ (program_to_string injectedProgram (depth + 1))
  | FST (program) -> "fst (\n" ^ spacingString ^ (program_to_string program (depth + 1)) ^ "\n"^ (String.make (depth * 2) ' ') ^ ")"
  | SND (program) -> "snd (\n" ^ spacingString ^ (program_to_string program (depth + 1)) ^ "\n"^ (String.make (depth * 2) ' ') ^ ")"
  | APP (left, right) -> "Apply (\n" ^ spacingString ^ "(" ^ (program_to_string left (depth + 1)) ^ ")\n" ^ 
      spacingString ^ "(" ^ (program_to_string right (depth + 1)) ^ ")\n" ^ (String.make (depth * 2) ' ') ^ ")"
  | CASE (matchMe, left, right, leftTag, rightTag) -> "case\n" ^ spacingString ^ (program_to_string matchMe (depth + 1)) ^ " of\n" ^ spacingString ^ 
          "inl (" ^ (program_to_string leftTag depth) ^ ") -> (" ^ (program_to_string left (depth)) ^ ")\n" ^ spacingString ^ 
          "inr (" ^ (program_to_string rightTag depth) ^ ") -> (" ^ (program_to_string right depth) ^ ")"
  | ABT -> "(abort program)"
  | UNT -> "(unit element)"
  | _ -> raise (CustomException "program_to_string: Impossible program definition")

(** Prints an abstract program to the terminal *)
let print_program
  program = print_endline (program_to_string program 0)

(** Calls the program extractor with an empty theorem-to-tag map *)
let proof_to_program
  proof = 
  annotation_number := -1;
  program_extractor TheoremMap.empty proof

(** Takes in a theorem, proves it, and then returns the corresponding program *)
let theorem_to_program ?(maxDepthBuildUp = 100) theorem =
  let proof = theorem_to_proof ~maxDepthBuildUp:maxDepthBuildUp theorem in
  match proof with
  | PROOF (_, _, true, _) -> proof_to_program proof
  | _ -> raise (ProofFailure "The proof has failed. Cannot extract program")

(** Converts an abstract program to a runnable program in OCaml, returns a string *)
let rec program_to_ocaml_string
  program =
  match program with
  | VAR (theoremTag) -> "var" ^ (string_of_int theoremTag)
  | PAIR (leftProgram, rightProgram) -> "(" ^ (program_to_ocaml_string leftProgram) ^ ", " ^ (program_to_ocaml_string rightProgram) ^ ")"
  | ABSTR (VAR theoremTag, right) -> "(fun " ^ "var" ^ (string_of_int theoremTag) ^ " -> (" ^ program_to_ocaml_string right ^ "))"
  | INL (_, injectedProgram) -> "(Left (" ^ (program_to_ocaml_string injectedProgram) ^ "))"
  | INR (_, injectedProgram) -> "(Right (" ^ (program_to_ocaml_string injectedProgram) ^ "))"
  | FST (program) -> "(fst (" ^ (program_to_ocaml_string program) ^ "))"
  | SND (program) -> "(snd (" ^ (program_to_ocaml_string program) ^ "))"
  | APP (leftProgram, rightProgram) -> "((" ^ (program_to_ocaml_string leftProgram) ^ ") (" ^ (program_to_ocaml_string rightProgram) ^ "))"
  | CASE (matchMeProgram, leftProgram, rightProgram, leftTheoremTag, rightTheoremTag) -> 
      "(match " ^ (program_to_ocaml_string matchMeProgram) ^ " with " ^
      "Left (" ^ (program_to_ocaml_string leftTheoremTag) ^ ") -> (" ^ (program_to_ocaml_string leftProgram) ^ ")" ^
      "| Right (" ^ (program_to_ocaml_string rightTheoremTag) ^ ") -> (" ^ (program_to_ocaml_string rightProgram) ^ "))"
  | ABT -> "(raise (InvalidInput \"You have given this function invalid input\"))"
  | UNT -> "()"
  | _ -> raise (CustomException "program_to_ocaml_string: Impossible program definition")

(** Converts a theorem to it's corresponding program in OCaml *)
let theorem_to_ocaml_string
  theorem = program_to_ocaml_string (theorem_to_program theorem)

(** First, prints the theorem to terminal. Then, tries to prove the theorem. Finaly, prints the proof (even upon failure) to terminal.*)
let test_theorem
  ?(maxDepthBuildUp = 100) theorem = 
  print_endline "--------------------------------------------------------";
  let proof = theorem_to_proof ~maxDepthBuildUp:maxDepthBuildUp theorem in
  let program = proof_to_program proof in
  let program_ocaml = program_to_ocaml_string program in
  print_endline "Theorem";
  print_theorem theorem;
  print_endline "Proof";
  print_proof proof;
  print_endline "Program";
  print_program program;
  print_endline "OCaml code";
  print_endline (program_ocaml)
  

(* Ease of use for user --------------------------------------------------------------------------------------------------------------------------------*)

(* Define operators for NOT, CON, DIS, and IMP. Precedence rules apply !! > ** > @@ > &&. All binary operators are right associative.
   Yes, it is confusing to have IMP defined as &&, however, in order to use only basic OCaml operators, which have a certain precedence order, 
   they have to be overwritten like this. https://v2.ocaml.org/manual/expr.html. Otherwise would have to download and use a dependency *)
(** Not operator *)
let ( !! )
  x = IMP(x, F, false)

(** Conjunction operator *)
let ( ** )
  x y = CON(x, y)

(** Disjunction operator *)
let ( @@ )
  x y = DIS(x, y)

(** Implication operator *)
let ( && ) 
  x y = IMP(x, y, false)

(** S 0 *)
let a = S 0

(** S 1 *)
let b = S 1

(** S 2 *)
let c = S 2

(** S 3 *)
let d = S 3

(** S 4 *)
let e = S 4

(** S 5 *)
let f = S 5

(** S 6 *)
let g = S 6

(** S 7 *)
let h = S 7

(** S 8 *)
let i = S 8

(** S 9 *)
let j = S 9

(** S 10 *)
let k = S 10

(** S 11 *)
let l = S 11

(** S 12 *)
let m = S 12

(** S 13 *)
let n = S 13