open Formule_Syllogisme
open Proposition.Formule
open DiagVenn
open Validation
open ContreEx
open DiagToInterpretation

(* open DiagVenn *)

let a = Atome "a"
let b = Atome "b"
let c = Atome "c"
let d = Atome "d"
let p1 = PourTout (Imp (Ou (a, b), c))
let p2 = PourTout (Imp (c, Ou (a, b)))
let p3 = IlExiste a
let p4 = IlExiste (Imp (a, Non b))

let p5 =
  let xor (a, b) = Ou (Et (a, Non b), Et (Non a, b)) in
  PourTout (Imp (xor (a, b), c))

let p6 = PourTout (Imp (Non c, a))
let p7 = IlExiste (Et (Et (a, c), Non b))
let c1 = IlExiste b
let c2 = IlExiste c
let c3 = IlExiste d

(** test premisses conclusion : teste si chacun des diagrammes de la combinaison
    de la liste prémisses est compatible avec au moins un des diagrammes de conclusion,
    tout en traçant les calculs réalisés et les diagrammes calculés,
    et en affichant tous les contre-exemples le cas échéant. *)
let test (_ : formule_syllogisme list) (_ : formule_syllogisme) : unit =
  failwith "test : à faire"

let a10 = PourTout (Ou (a, b))
let a11 = IlExiste (Et (a, b))
let a12 = IlExiste (Et (a, Non (Ou (b, c))))
let a13 = IlExiste (Et (b, Non (Ou (a, c))))
let c10 = IlExiste c
let dc1 = diag_from_formule [ "a"; "b"; "c" ] c10
let lp = [ a10; a11; a12; a13 ]
let c11 = PourTout (Non c)
let diag = List.map (diag_from_formule [ "a"; "b"; "c" ]) lp
let d1 = List.nth diag 0
let d2 = List.nth diag 1
let d3 = List.nth diag 2
let d4 = List.nth diag 3
let conj1 = conj_diag_list d1 d2
let conj2 = conj_diag_list conj1 d3
let conj3 = conj_diag_list conj2 d4
let d1' = List.nth conj3 1
let d1'' = List.nth conj3 0
let dc = diag_from_formule [ "a"; "b"; "c" ] c11
let dcs = List.nth dc 0
let result = extend_contre_ex d1' dcs

let preds =
  Predicate_def.of_list
    [ ("a", IntSet.of_list [ 1; 2; 3 ]); ("b", IntSet.of_list [ 2; 5; 3 ]) ]

let i = function
  | "a" -> ( function x -> x mod 2 = 0)
  | "b" -> ( function x -> x mod 3 = 0)
  | "c" -> ( function x -> x mod 5 = 0)
  | _ -> ( function _ -> false)

let tem = temoins_incompatibilite_premisses_conc lp c11
let v1 = IlExiste a
let v2 = IlExiste b
let v3 = IlExiste (Et (Non a, Non b))
let v1 = diag_from_formule [] v1
let v2 = diag_from_formule [] v2
let v3 = diag_from_formule [] v3
let v4 = conj_diag_list v1 v2
let v5 = conj_diag_list v4 v3
let v5 = List.hd v5
let test1 = PourTout (Imp (a, b))
let test2 = IlExiste a
let test3 = IlExiste b
