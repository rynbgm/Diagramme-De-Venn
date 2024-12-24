open DiagVenn

module Predicate_def = Map.Make (String)
(** Module des Map ayant pour clés des chaînes de caractères *)

module IntSet = Set.Make (Int)
(** Module des ensembles d'entiers *)

(** Renvoie une représentation de l'ensemble d'entiers en chaine de caractère *)
let intset_to_string (set : IntSet.t) : string =
  "{"
  ^ (IntSet.to_list set |> List.map string_of_int |> String.concat ", ")
  ^ "}"

type predicate_def = IntSet.t Predicate_def.t
(** Type synonymes des valeurs de Map ayant pour clés des chaînes de caractères et pour valeur des ensembles d'entiers *)

(** Transforme une Map ayant pour clés des chaines s et pour valeur des ensembles d'entiers ns
      en une liste de couples (chaine s, représentation de l'ensemble ns en chaine) *)
let predicate_def_to_string_couple (d : predicate_def) : (string * string) list
    =
  List.rev
    (Predicate_def.fold
       (fun key value acc -> (key, intset_to_string value) :: acc)
       d [])

(** Renvoie une association predicat -> ensemble d'entiers représentant le diagramme, 
      avec l'entier maximum utilisé, s'il existe *)
let diag_to_predicate_def (d : diagramme) : int option * predicate_def =
  let rec aux d acc k =
    match d with
    | (x, _) :: t -> aux t ((x, [ k ]) :: acc) (k + 1)
    | [] ->
        ( Some (k - 1),
          let rec aux1 ls (accs1 : predicate_def) =
            match ls with
            | (set, y) :: t ->
                aux1 t
                  (let rec aux2 set (accs2 : predicate_def) =
                     match set with
                     | elt :: tail ->
                         aux2 tail
                           (if Predicate_def.mem elt accs2 then
                              let cur_val = Predicate_def.find elt accs2 in
                              Predicate_def.add elt
                                (IntSet.of_list (IntSet.to_list cur_val @ y))
                                accs2
                            else Predicate_def.add elt (IntSet.of_list y) accs2)
                     | [] -> accs2
                   in
                   aux2 (Predicate_set.to_list set) accs1)
            | [] -> accs1
          in

          aux1 acc Predicate_def.empty )
  in
  if List.exists (fun (_, y) -> y = NonVide) (Diag.to_list d) then
    aux (List.filter (fun (_, y) -> y = NonVide) (Diag.to_list d)) [] 0
  else (None, Predicate_def.empty)

(** Module contenant les informations nécessaires à la création d'une interprétation représentant un diagramme de Venn *)
module type ExempleFromEnum = sig
  type t
  (** Type représentant le domaine d'interprétation *)

  include Enumerable.EnumerableFromInt with type t := t
  (** Valeurs indiquant que le type t est énumérable et est un sous-type des entiers *)

  val i : string -> t -> bool
  (** Fonction indiquant si l'ensemble associé à un prédicat contient une valeur donnée *)

  val preds : predicate_def
  (** Map reliant chaque prédicat à l'ensemble d'entier qui lui est associé, d'une façon équivalente à i *)
end

(** Construit un couple ((M : Module EnumerableFromInt), i: int interpretation) tel que les
      valeurs de M.values correspondent aux zones Non Vide de diag, par la correspondance définie par i *)
let exemple (diag : diagramme) : (module ExempleFromEnum) =
  let n_opt, preds = diag_to_predicate_def diag in

  let n = match n_opt with None -> -1 | Some k -> k in

  let module M = (val Enumerable.enum_from_int n) in
  (module struct
    include M

    let i (x : string) (v : M.t) : bool =
      match Predicate_def.find_opt x preds with
      | None -> false
      | Some set -> IntSet.mem (M.to_int v) set

    let preds = preds
  end)
