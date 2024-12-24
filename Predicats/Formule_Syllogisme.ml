open Proposition.Formule

(** Type des formules utilisées pour les syllogismes *)
type formule_syllogisme = PourTout of formule | IlExiste of formule

(* ----------------- Ajouter les définitions nécessaires tirées du TP4 ------------------------- *)

type 'a interpretation = string -> 'a -> bool
(** Fonction d'interprétation des prédicats, ici nullaires pour les syllogismes *)

(** Évalue à l'aide d'une interprétation i la partie non quantifiée d'un syllogisme,
      au point v du domaine d'interprétation *)
let eval_preds_with (i : 'a interpretation) (x : 'a) : formule -> bool =
  let rec aux = function
    | Top -> true
    | Bot -> false
    | Atome s -> i s x
    | Et (f, g) -> aux f && aux g
    | Ou (f, g) -> aux f || aux g
    | Imp (f, g) -> aux f <= aux g
    | Non f -> not (aux f)
  in
  aux

(** Foncteur construisant la fonction d'évaluation d'un syllogisme sur des types énumérables *)
module MakeEval (M : Enumerable.Enumerable) = struct
  let eval_syllogisme (i : M.t interpretation) : formule_syllogisme -> bool =
    let rec aux value form =
      match (value, form) with
      | x :: t, IlExiste f -> if eval_preds_with i x f then true else aux t form
      | [], IlExiste _ -> false
      | x :: t, PourTout f ->
          if eval_preds_with i x f then aux t form else false
      | [], PourTout _ -> true
    in
    aux (List.of_seq M.values)
end
