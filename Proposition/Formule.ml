(** Le module Formule contient les types et définitions de base
permettant la manipulation des formules de la logique propositionnelle. *)

(** Type des formules de la logique propositionnelle, avec des string comme atomes. *)
type formule =
  | Bot
  | Top
  | Atome of string
  | Imp of (formule * formule)
  | Ou of (formule * formule)
  | Et of (formule * formule)
  | Non of formule

(* ----------------- Exercice 1 : Hauteur ----------------- *)

(** Calcule la hauteur de l'arbre syntaxique d'une formule. *)
let rec hauteur (f : formule) : int =
  match f with
  | Bot | Top | Atome _ -> 1
  | Non f -> 1 + hauteur f
  | Ou (f, g) | Et (f, g) | Imp (f, g) -> 1 + Int.max (hauteur f) (hauteur g)

(* ----------------- Exercice 2 : Représentation en chaîne de caractères ----------------- *)

(** Conversion d'une formule en chaîne de caractères. *)
let rec string_of_formule : formule -> string = function
  | Atome s -> s
  | Bot -> " ⊥ "
  | Top -> " ⊤ "
  | Non f -> String.concat "" [ "("; " ¬"; string_of_formule f; ")" ]
  | Et (f, g) ->
      String.concat ""
        [ "("; string_of_formule f; " ∧ "; string_of_formule g; ")" ]
  | Ou (f, g) ->
      String.concat ""
        [ "("; string_of_formule f; " ∨ "; string_of_formule g; ")" ]
  | Imp (f, g) ->
      String.concat ""
        [ "("; string_of_formule f; " => "; string_of_formule g; ")" ]

(* ----------------- Exercice 3 : Conversion depuis une liste ----------------- *)

(** Transforme une liste de formules [[f1; f2; ... ; fl]] en la formule [f1 ∧ f2 ∧ ... ∧ fl] en considérant les éléments suivants :
Si un des [fi] vaut [Bot], renvoie [Bot].
Si un des [fi] vaut [Top], il n'apparait pas dans le résultat.
Si tous les [fi] valent [Top], renvoie [Top]. *)
let rec conj_of_list (fl : formule list) : formule =
  match fl with
  | [] -> Top
  | Bot :: _ -> Bot
  | Top :: t -> conj_of_list t
  | h :: t -> Et (h, conj_of_list t)

(** Transforme une liste de formules [[f1; f2; ... ; fl]] en la formule [f1 ∨ f2 ∨ ... ∨ fl] en considérant les éléments suivants :
Si un des [fi] vaut [Top], renvoie [Top].
Si un des [fi] vaut [Bot], il n'apparait pas dans le résultat.
Si tous les [fi] valent [Bot], renvoie [Bot]. *)
let rec disj_of_list (f : formule list) : formule =
  match f with
  | [] -> Bot
  | Top :: _ -> Top
  | Bot :: t -> disj_of_list t
  | h :: t -> Ou (h, disj_of_list t)

(** --- Exercice 4 : Fonctions d'évaluation ------- *)

type interpretation = string -> bool
(** Type des interprétations. *)

(** Évalue une formule en fonction d'une interprétation. *)
let rec eval (i : interpretation) (f : formule) : bool =
  match f with
  | Bot -> false
  | Top -> true
  | Atome s -> i s
  | Non f -> not (eval i f)
  | Et (f, g) -> eval i f && eval i g
  | Ou (f, g) -> eval i f || eval i g
  | Imp (f, g) -> eval i f <= eval i g

(** --- Exercice 5 : Tests de satisfaisabilité ------- *)

(** Transforme une liste de string en une interprétation. *)
let interpretation_of_list (l : string list) (s : string) : bool = List.mem s l
(* let interpretation_of_list (l : string list) : interpretation = function s -> List.mem s l *)
(* ya aussi Fun.flip qui echange aussi la place des parametre*)

(** Calcule la liste de toutes les sous-listes d'une liste donnée. *)
let rec all_sublists (l : 'a list) : 'a list list =
  match l with
  | [] -> [ [] ]
  | x :: xs ->
      let sub_liste_xs = all_sublists xs in
      let sub_liste_x = List.map (List.cons x) sub_liste_xs in
      sub_liste_x @ sub_liste_xs

(** Calcule toutes les interprétations pour une liste d'atomes donnée. *)
let all_interpretations (l : string list) : interpretation list =
  List.map interpretation_of_list (all_sublists l)

(** Calcule la liste (triée et sans doublon) des atomes d'une formule.*)
let atomes (f : formule) : string list =
  let rec aux = function
    | Bot | Top -> []
    | Atome s -> [ s ]
    | Et (f, g) | Ou (f, g) | Imp (f, g) -> aux f @ aux g
    | Non f -> aux f
  in

  List.sort_uniq String.compare (aux f)

(** Détermine si une formule est satisfaisable. *)
let est_satisfaisable (f : formule) : bool =
  List.exists (fun i -> eval i f) (all_interpretations (atomes f))

(** Renvoie un témoin de la satisfaisabilité d'une formule, s'il en existe. *)
let ex_sat (f : formule) : interpretation option =
  let rec aux all_i =
    match all_i with
    | [] -> None (*je crois*)
    | i :: t -> ( match eval i f with true -> Some i | _ -> aux t)
  in
  aux (all_interpretations (atomes f))

(** Détermine si une formule est une tautologie. *)
let est_tautologie (f : formule) : bool =
  not
    (List.exists
       (fun element -> element = false)
       (List.map (fun i -> eval i f) (all_interpretations (atomes f))))

(** Détermine si une formule est une contradiction. *)
let est_contradiction (f : formule) : bool = not (est_satisfaisable f)

(** Détermine si une formule est contingente. *)
let est_contingente (f : formule) : bool =
  est_satisfaisable f && not (est_tautologie f)

(** ----------------- Exercice 8 : Tables de vérité ----------------- *)

type ligne = string list * bool
(** Type d'une ligne d'une table de vérité. *)

type table = ligne list
(** Type d'une table de vérité. *)

(** Calcule la table de vérité associée à une formule. *)
let table_of_formule (alpha : string list) (f : formule) : table =
  let all_sublists_of_atomes =
    all_sublists (List.sort_uniq String.compare (alpha @ atomes f))
  in
  let rec aux liste acc =
    match liste with
    | [] -> acc
    | liste_atomes_vraies :: reste_liste ->
        let snd_couple = eval (interpretation_of_list liste_atomes_vraies) f in
        let fst_couple = liste_atomes_vraies in
        let couple = (fst_couple, snd_couple) in
        aux reste_liste (couple :: acc)
  in
  aux all_sublists_of_atomes []

let table_of_formule_with (alpha : string list) (f : formule) : table =
  List.rev
    (List.fold_left
       (fun a x -> (x, eval (interpretation_of_list x) f) :: a)
       []
       (all_sublists (List.sort_uniq String.compare (alpha @ atomes f))))
