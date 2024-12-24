open Formule_Syllogisme
open Proposition.Formule

(* open Formule_Log_Prop *)

let atomes_from_form_syll : formule_syllogisme -> string list = function
  | PourTout f | IlExiste f -> Proposition.Formule.atomes f

(** atomes_from_form_syll_list fs : renvoie la liste des atomes des formules de la liste fs *)
let atomes_from_form_syll_list : formule_syllogisme list -> string list =
  List.concat_map atomes_from_form_syll

module Predicate_set = Set.Make (String)
(** Module des ensembles de prédicats représentés par des chaines de caractères *)

(** Type des remplissages possibles d'un diagramme de Venn *)
type fill = Vide | NonVide

module Diag = Map.Make (Predicate_set)
(** Module des Maps dont les clés sont des ensembles de chaines de caractères *)

type diagramme = fill Diag.t
(** Type des diagrammes de Venn *)

let string_of_fill = function Vide -> "Vide" | NonVide -> "NonVide"

let set_to_string (s : Predicate_set.t) : string =
  if Predicate_set.to_list s != [] then
    "{" ^ (Predicate_set.to_list s |> String.concat ", ") ^ "}"
  else "∅"

let diag_to_string (d : diagramme) : (string * fill) list =
  Diag.to_list d |> List.map (fun (xs, d) -> (set_to_string xs, d))

(** string_of_diag d : conversion d'un diagramme d en une chaine de caractères *)
let string_of_diag (d : diagramme) : string =
  diag_to_string d
  |> List.map (fun (x, y) -> (x, string_of_fill y))
  |> List.fold_left (fun acc (x, y) -> x ^ " -> " ^ y ^ "\n" ^ acc) ""

(** diag_from_formule alpha f : construit le diagramme de Venn associé à la formule f sur
      les prédicats issus de f ou de alpha *)
let diag_from_formule (alpha : string list) (f : formule_syllogisme) :
    diagramme list =
  match f with
  | PourTout f' ->
      [
        table_of_formule_with alpha f'
        |> List.filter (fun (_, b) -> not b)
        |> List.map (fun (xs, _) -> (Predicate_set.of_list xs, Vide))
        |> Diag.of_list;
      ]
  | IlExiste f' ->
      table_of_formule_with alpha f'
      |> List.filter (fun (_, b) -> b)
      |> List.map (fun (xs, _) -> [ (Predicate_set.of_list xs, NonVide) ])
      |> List.map Diag.of_list

(** conj_diag d1 d2 : Calcule la combinaison/conjonction de deux diagrammes, renvoyant None si incompatibilité *)
let conj_diag (d1 : diagramme) (d2 : diagramme) : diagramme option =
  Diag.fold
    (fun cle valeur res ->
      match res with
      | None -> None
      | Some diagrame -> (
          match Diag.find_opt cle d1 with
          | None -> Some (Diag.add cle valeur diagrame)
          | Some v when v = valeur -> res
          | _ -> None))
    d2 (Some d1)

let conj_diag_list (d1s : diagramme list) (d2s : diagramme list) :
    diagramme list =
  List.concat_map
    (fun d1 -> List.concat_map (fun d2 -> Option.to_list (conj_diag d1 d2)) d2s)
    d1s

(** est_compatible_diag_diag dp dc : teste si le diagramme dp d'une prémisse est compatible
    avec le diagramme dc d'une conclusion *)
let est_compatible_diag_diag (dp : diagramme) (dc : diagramme) : bool =
  Diag.for_all
    (fun cle valeur ->
      match Diag.find_opt cle dp with
      | Some v when v = valeur -> true
      | _ -> false)
    dc

(** est_compatible_diag_list dp dcs : teste si un diagramme dp d'une prémisse est compatible
    avec un des diagrammes de la liste dcs,
    diagrammes issus d'une conclusion *)
let est_compatible_diag_list (d : diagramme) (dcs : diagramme list) : bool =
  List.exists (fun dc -> est_compatible_diag_diag d dc) dcs

(** est_compatible_list_list dps dcs : teste si chacun des diagrammes de dps, diagrammes issus de prémisses,
    est compatible avec au moins un des diagrammes de dcs, diagrammes issus d'une conclusion *)
let est_compatible_list_list (ds : diagramme list) (dcs : diagramme list) : bool
    =
  List.for_all (fun d -> est_compatible_diag_list d dcs) ds

(** est_compatible_premisses_conc ps c : teste si une liste de prémisses ps est compatible avec une conclusion c *)
let est_compatible_premisses_conc (ps : formule_syllogisme list)
    (c : formule_syllogisme) : bool =
  let univers = atomes_from_form_syll_list (c :: ps) in
  let diag_conc = diag_from_formule univers c in
  let list_diag_prem =
    List.fold_left
      (fun acc x -> conj_diag_list acc x)
      [ Diag.empty ]
      (List.map (diag_from_formule univers) ps)
  in
  est_compatible_list_list list_diag_prem diag_conc

(** temoin_incompatibilite_premisses_conc_opt ps c : renvoie un diagramme de la combinaison des 
    prémisses ps incompatible avec la conclusion c s'il existe, None sinon *)
let temoin_incompatibilite_premisses_conc_opt (l : formule_syllogisme list)
    (c : formule_syllogisme) : diagramme option =
  if est_compatible_premisses_conc l c then None
  else
    let rec aux = function
      | x :: t ->
          if
            est_compatible_diag_list x
              (diag_from_formule (atomes_from_form_syll_list l) c)
          then aux t
          else Some x
      | [] -> None
    in
    aux
      (List.fold_left
         (fun acc x -> conj_diag_list acc x)
         [ Diag.empty ]
         (List.map (diag_from_formule (atomes_from_form_syll_list l)) l))

(** temoins_incompatibilite_premisses_conc ps c : renvoie les diagrammes de la combinaison
    des prémisses ps incompatibles avec la conclusion c *)
let temoins_incompatibilite_premisses_conc (l : formule_syllogisme list)
    (c : formule_syllogisme) : diagramme list =
  if temoin_incompatibilite_premisses_conc_opt l c = None then []
  else
    let rec aux acc = function
      | x :: t ->
          if
            est_compatible_diag_list x
              (diag_from_formule (atomes_from_form_syll_list l) c)
          then aux acc t
          else aux (x :: acc) t
      | [] -> acc
    in
    aux []
      (List.fold_left
         (fun acc x -> conj_diag_list acc x)
         [ Diag.empty ]
         (List.map (diag_from_formule (atomes_from_form_syll_list l)) l))
