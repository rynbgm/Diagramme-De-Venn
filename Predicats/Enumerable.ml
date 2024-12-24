(** Signature des modules des types énumérables. *)
module type Enumerable = sig
  type t
  (** Le type à énumérer. *)

  val values : t Seq.t
  (** La séquence contenant les valeurs du type t *)

  val mini : t option
  (** La valeur minimale du type énuméré, si elle existe *)

  val maxi : t option
  (** La valeur maximale du type énuméré, si elle existe *)

  val safe_succ : t -> t option
  (** Renvoie le successeur d'une valeur de type t, s'il existe *)
end

(** Calcule une séquence constituée des éléments obtenus en appliquant d'une façon répétée la fonction succ
  depuis la valeur v_min, jusqu'à obtenir None *)
let from_succ (succ : 't -> 't option) (v_min : 't) : 't Seq.t =
  Seq.unfold
    (fun x -> match x with None -> None | Some y -> Some (y, succ y))
    (Some v_min)

(** Signature des modules des types énumérables basés une sous-partie des entiers. *)
module type EnumerableFromInt = sig
  include Enumerable

  val from_int : int -> t option
  val to_int : t -> int
end

(** Renvoie un module de type EnumerableInt représentant les entiers de 0 à n *)
let enum_from_int (n : int) =
  (module struct
    type t = int

    let values =
      if n < 0 then Seq.empty
      else from_succ (fun x -> if x >= n then None else Some (x + 1)) 0

    let mini = if n >= 0 then Some 0 else None
    let maxi = if n >= 0 then Some n else None
    let safe_succ x = if x = n then None else Some (x + 1)
    let from_int x = if x <= n then Some x else None
    let to_int x = x
  end : EnumerableFromInt)
