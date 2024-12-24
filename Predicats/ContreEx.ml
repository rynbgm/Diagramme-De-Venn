open DiagVenn
open DiagToInterpretation
open Formule_Syllogisme

(**renvoie un diagramme contenant les contraintes de vacuité de d2 qui ne sont pas dans d1,
   et si il n’en existe pas elle renvoie un diagramme vide (Diag.empty)*)
let contrainte (d1 : diagramme) (d2 : diagramme) : diagramme =
  Diag.filter (fun key f -> (not (Diag.mem key d1)) && f == Vide) d2

(** Si le diagramme d n'est pas compatible avec c, cherche une contrainte "cont" de c incompatible avec d, puis :
- si cont est une contrainte de non vacuité, renvoie d
- si cont est une contrainte de vacuité, ajoute une contrainte de non vacuité dans d pour la même zone
Sinon, renvoie d
*)
let extend_contre_ex (d : diagramme) (c : diagramme) : diagramme =
  match est_compatible_diag_diag d c with
  | true -> d
  | false ->
      if contrainte d c != Diag.empty then
        Diag.add (fst (List.hd (Diag.to_list (contrainte d c)))) NonVide d
      else d

(** atomes_from_form_syll f : renvoie la liste des atomes de la formule f *)
let atomes_from_form_syll : formule_syllogisme -> string list = function
  | PourTout f | IlExiste f -> Proposition.Formule.atomes f

(** atomes_from_form_syll_list fs : renvoie la liste des atomes des formules de la liste fs *)
let atomes_from_form_syll_list : formule_syllogisme list -> string list =
  List.concat_map atomes_from_form_syll

(**  Construit la listes des couples ((M : Module EnumerableFromInt), i: int interpretation) tels que les
      valeurs de M.values permettent d'évaluer les prémisses comme vraies pour i et la conclusion comme fausse,
      couples définis à partir de chaque diagramme des prémisses incompatible avec les diagrammes de la conclusion  *)
let all_contre_ex (ps : formule_syllogisme list) (conc : formule_syllogisme) :
    (module ExempleFromEnum) list =
  let alpha = atomes_from_form_syll_list (conc :: ps) in
  List.map
    (fun d ->
      match conc with
      | IlExiste _ -> exemple d
      | _ ->
          exemple (extend_contre_ex d (List.hd (diag_from_formule alpha conc))))
    (temoins_incompatibilite_premisses_conc ps conc)
