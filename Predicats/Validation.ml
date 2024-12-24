open Formule_Syllogisme
open DiagVenn
open DiagToInterpretation
open ContreEx

(** atomes_from_form_syll f : renvoie la liste des atomes de la formule f *)
let atomes_from_form_syll : formule_syllogisme -> string list = function
  | PourTout f | IlExiste f -> Proposition.Formule.atomes f

(** atomes_from_form_syll_list fs : renvoie la liste des atomes des formules de la liste fs *)
let atomes_from_form_syll_list : formule_syllogisme list -> string list =
  List.concat_map atomes_from_form_syll

(** Calcule la conjonction de deux listes de diagrammes *)
let conj_diag_list (d1s : diagramme list) (d2s : diagramme list) :
    diagramme list =
  List.concat_map
    (fun d1 -> List.concat_map (fun d2 -> Option.to_list (conj_diag d1 d2)) d2s)
    d1s

(** Teste si, pour chaque diagramme diag de la conjonction des diagrammes des prémisses ps, 
      l'exemple associé à diag permet d'évaluer chaque prémisse comme vraie par l'interpréation *)
let validation_ex (ps : formule_syllogisme list) : bool =
  (* calcul de l'alphabet des formules *)
  let alpha = atomes_from_form_syll_list ps in
  (* calcul des diagrammes de la combinaison des prémisses *)
  let diags =
    List.fold_left
      (fun acc g -> conj_diag_list acc (diag_from_formule alpha g))
      [ Diag.empty ] ps
  in
  (* vérification si toute formule est évaluée comme vraie pour chaque interprétation issue d'un diagramme de la combinaison *)
  List.for_all
    (fun diag ->
      let module M = (val exemple diag) in
      let module EvalM = MakeEval (M) in
      List.for_all (EvalM.eval_syllogisme M.i) ps)
    diags

(** Teste si chaque interprétation obtenue depuis un diagramme des prémisses incompatible avec la conclusion 
    permet d'avaluer les prémisses comme vraies et la conclusion comme fausse *)
let validation_contre_ex (ps : formule_syllogisme list) (c : formule_syllogisme)
    : bool =
  List.for_all
    (fun m ->
      let module M = (val m : ExempleFromEnum) in
      let module EvalM = MakeEval (M) in
      List.for_all (EvalM.eval_syllogisme M.i) ps
      && not (EvalM.eval_syllogisme M.i c))
    (all_contre_ex ps c)
