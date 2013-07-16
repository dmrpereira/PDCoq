open Coq_lib
open Term
open Names

(** ---- Begin Extracted Code ----*)

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, y) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (x, y) -> y

(** val length : 'a1 list -> nat **)

let rec lengthk = function
| [] -> O
| y :: l' -> S (lengthk l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type x y c =
  compareSpec2Type c

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val plus : nat -> nat -> nat **)

let rec plus n0 m =
  match n0 with
  | O -> m
  | S p -> S (plus p m)

(** val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n0 f x =
  match n0 with
  | O -> x
  | S n' -> f (nat_iter n' f x)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module type TotalOrder' = 
 sig 
  type t 
 end

module MakeOrderTac = 
 functor (O:TotalOrder') ->
 struct 
  
 end

module MaxLogicalProperties = 
 functor (O:TotalOrder') ->
 functor (M:sig 
  val max : O.t -> O.t -> O.t
 end) ->
 struct 
  module Private_Tac = MakeOrderTac(O)
 end

module Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> nat **)
  
  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive * mask)
      -> positive * mask **)
  
  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       if leb s' r' then ((XI s), (sub_mask r' s')) else ((XO s), (IsPos r'))
     | _ -> ((XO s), (sub_mask (g (f XH)) (XO (XO XH)))))
  
  (** val sqrtrem : positive -> positive * mask **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> (XH, (IsPos (XO XH))))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> (XH, (IsPos XH)))
  | XH -> (XH, IsNul)
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : nat -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI p -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      nat -> positive -> positive -> positive * (positive * positive) **)
  
  let rec ggcdn n0 a b =
    match n0 with
    | O -> (XH, (a, b))
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> (a, (XH, XH))
             | Lt ->
               let (g, p) = ggcdn n1 (sub b' a') a in
               let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
             | Gt ->
               let (g, p) = ggcdn n1 (sub a' b') b in
               let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
          | XO b0 ->
            let (g, p) = ggcdn n1 a b0 in
            let (aa, bb) = p in (g, (aa, (XO bb)))
          | XH -> (XH, (a, XH)))
       | XO a0 ->
         (match b with
          | XI p ->
            let (g, p0) = ggcdn n1 a0 b in
            let (aa, bb) = p0 in (g, ((XO aa), bb))
          | XO b0 -> let (g, p) = ggcdn n1 a0 b0 in ((XO g), p)
          | XH -> (XH, (a, XH)))
       | XH -> (XH, (XH, b)))
  
  (** val ggcd : positive -> positive -> positive * (positive * positive) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> nat -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> nat -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> nat -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | O -> true
       | S n' -> testbit_nat p0 n')
    | XO p0 ->
      (match n0 with
       | O -> false
       | S n' -> testbit_nat p0 n')
    | XH ->
      (match n0 with
       | O -> true
       | S n1 -> false)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> nat **)
  
  let to_nat x =
    iter_op plus x (S O)
  
  (** val of_nat : nat -> positive **)
  
  let rec of_nat = function
  | O -> XH
  | S x ->
    (match x with
     | O -> XH
     | S n1 -> succ (of_nat x))
  
  (** val of_succ_nat : nat -> positive **)
  
  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> nat **)
  
  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive * mask)
      -> positive * mask **)
  
  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       if leb s' r' then ((XI s), (sub_mask r' s')) else ((XO s), (IsPos r'))
     | _ -> ((XO s), (sub_mask (g (f XH)) (XO (XO XH)))))
  
  (** val sqrtrem : positive -> positive * mask **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> (XH, (IsPos (XO XH))))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> (XH, (IsPos XH)))
  | XH -> (XH, IsNul)
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : nat -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI p -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      nat -> positive -> positive -> positive * (positive * positive) **)
  
  let rec ggcdn n0 a b =
    match n0 with
    | O -> (XH, (a, b))
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> (a, (XH, XH))
             | Lt ->
               let (g, p) = ggcdn n1 (sub b' a') a in
               let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
             | Gt ->
               let (g, p) = ggcdn n1 (sub a' b') b in
               let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
          | XO b0 ->
            let (g, p) = ggcdn n1 a b0 in
            let (aa, bb) = p in (g, (aa, (XO bb)))
          | XH -> (XH, (a, XH)))
       | XO a0 ->
         (match b with
          | XI p ->
            let (g, p0) = ggcdn n1 a0 b in
            let (aa, bb) = p0 in (g, ((XO aa), bb))
          | XO b0 -> let (g, p) = ggcdn n1 a0 b0 in ((XO g), p)
          | XH -> (XH, (a, XH)))
       | XH -> (XH, (XH, b)))
  
  (** val ggcd : positive -> positive -> positive * (positive * positive) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> nat -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> nat -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> nat -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | O -> true
       | S n' -> testbit_nat p0 n')
    | XO p0 ->
      (match n0 with
       | O -> false
       | S n' -> testbit_nat p0 n')
    | XH ->
      (match n0 with
       | O -> true
       | S n1 -> false)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> nat **)
  
  let to_nat x =
    iter_op plus x (S O)
  
  (** val of_nat : nat -> positive **)
  
  let rec of_nat = function
  | O -> XH
  | S x ->
    (match x with
     | O -> XH
     | S n1 -> succ (of_nat x))
  
  (** val of_succ_nat : nat -> positive **)
  
  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
  
  (** val eq_dec : positive -> positive -> bool **)
  
  let rec eq_dec p y0 =
    match p with
    | XI p0 ->
      (match y0 with
       | XI p1 -> eq_dec p0 p1
       | _ -> false)
    | XO p0 ->
      (match y0 with
       | XO p1 -> eq_dec p0 p1
       | _ -> false)
    | XH ->
      (match y0 with
       | XH -> true
       | _ -> false)
  
  (** val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let rec peano_rect a f p =
    let f2 = peano_rect (f XH a) (fun p0 x -> f (succ (XO p0)) (f (XO p0) x))
    in
    (match p with
     | XI q -> f (XO q) (f2 q)
     | XO q -> f2 q
     | XH -> a)
  
  (** val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  (** val coq_PeanoView_rect :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rect f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rect f f0 p1 p2)
  
  (** val coq_PeanoView_rec :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rec f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rec f f0 p1 p2)
  
  (** val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xO p = function
  | PeanoOne -> PeanoSucc (XH, PeanoOne)
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (XO p0)), (PeanoSucc ((XO p0), (peanoView_xO p0 q0))))
  
  (** val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xI p = function
  | PeanoOne -> PeanoSucc ((succ XH), (PeanoSucc (XH, PeanoOne)))
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (XI p0)), (PeanoSucc ((XI p0), (peanoView_xI p0 q0))))
  
  (** val peanoView : positive -> coq_PeanoView **)
  
  let rec peanoView = function
  | XI p0 -> peanoView_xI p0 (peanoView p0)
  | XO p0 -> peanoView_xO p0 (peanoView p0)
  | XH -> PeanoOne
  
  (** val coq_PeanoView_iter :
      'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_iter a f p = function
  | PeanoOne -> a
  | PeanoSucc (p0, q0) -> f p0 (coq_PeanoView_iter a f p0 q0)
  
  (** val eqb_spec : positive -> positive -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val switch_Eq : comparison -> comparison -> comparison **)
  
  let switch_Eq c = function
  | Eq -> c
  | x -> x
  
  (** val mask2cmp : mask -> comparison **)
  
  let mask2cmp = function
  | IsNul -> Eq
  | IsPos p0 -> Gt
  | IsNeg -> Lt
  
  (** val leb_spec0 : positive -> positive -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : positive -> positive -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Rev = 
   struct 
    module ORev = 
     struct 
      type t = positive
     end
    
    module MRev = 
     struct 
      (** val max : positive -> positive -> positive **)
      
      let max x y =
        min y x
     end
    
    module MPRev = MaxLogicalProperties(ORev)(MRev)
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : positive -> positive -> bool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : positive -> positive -> bool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : positive -> positive -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : positive -> positive -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module N = 
 struct 
  type t = n
  
  (** val zero : n **)
  
  let zero =
    N0
  
  (** val one : n **)
  
  let one =
    Npos XH
  
  (** val two : n **)
  
  let two =
    Npos (XO XH)
  
  (** val succ_double : n -> n **)
  
  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val double : n -> n **)
  
  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val succ : n -> n **)
  
  let succ = function
  | N0 -> Npos XH
  | Npos p -> Npos (Coq_Pos.succ p)
  
  (** val pred : n -> n **)
  
  let pred = function
  | N0 -> N0
  | Npos p -> Coq_Pos.pred_N p
  
  (** val succ_pos : n -> positive **)
  
  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p
  
  (** val add : n -> n -> n **)
  
  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.add p q))
  
  (** val sub : n -> n -> n **)
  
  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))
  
  (** val mul : n -> n -> n **)
  
  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Npos (Coq_Pos.mul p q))
  
  (** val compare : n -> n -> comparison **)
  
  let compare n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> Eq
       | Npos m' -> Lt)
    | Npos n' ->
      (match m with
       | N0 -> Gt
       | Npos m' -> Coq_Pos.compare n' m')
  
  (** val eqb : n -> n -> bool **)
  
  let rec eqb n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos p ->
      (match m with
       | N0 -> false
       | Npos q -> Coq_Pos.eqb p q)
  
  (** val leb : n -> n -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : n -> n -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val min : n -> n -> n **)
  
  let min n0 n' =
    match compare n0 n' with
    | Gt -> n'
    | _ -> n0
  
  (** val max : n -> n -> n **)
  
  let max n0 n' =
    match compare n0 n' with
    | Gt -> n0
    | _ -> n'
  
  (** val div2 : n -> n **)
  
  let div2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos p
     | XO p -> Npos p
     | XH -> N0)
  
  (** val even : n -> bool **)
  
  let even = function
  | N0 -> true
  | Npos p ->
    (match p with
     | XO p0 -> true
     | _ -> false)
  
  (** val odd : n -> bool **)
  
  let odd n0 =
    negb (even n0)
  
  (** val pow : n -> n -> n **)
  
  let pow n0 = function
  | N0 -> Npos XH
  | Npos p0 ->
    (match n0 with
     | N0 -> N0
     | Npos q -> Npos (Coq_Pos.pow q p0))
  
  (** val square : n -> n **)
  
  let square = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.square p)
  
  (** val log2 : n -> n **)
  
  let log2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos (Coq_Pos.size p)
     | XO p -> Npos (Coq_Pos.size p)
     | XH -> N0)
  
  (** val size : n -> n **)
  
  let size = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.size p)
  
  (** val size_nat : n -> nat **)
  
  let size_nat = function
  | N0 -> O
  | Npos p -> Coq_Pos.size_nat p
  
  (** val pos_div_eucl : positive -> n -> n * n **)
  
  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XH ->
      (match b with
       | N0 -> (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> ((Npos XH), N0)
          | _ -> (N0, (Npos XH))))
  
  (** val div_eucl : n -> n -> n * n **)
  
  let div_eucl a b =
    match a with
    | N0 -> (N0, N0)
    | Npos na ->
      (match b with
       | N0 -> (N0, a)
       | Npos p -> pos_div_eucl na b)
  
  (** val div : n -> n -> n **)
  
  let div a b =
    fst (div_eucl a b)
  
  (** val modulo : n -> n -> n **)
  
  let modulo a b =
    snd (div_eucl a b)
  
  (** val gcd : n -> n -> n **)
  
  let gcd a b =
    match a with
    | N0 -> b
    | Npos p ->
      (match b with
       | N0 -> a
       | Npos q -> Npos (Coq_Pos.gcd p q))
  
  (** val ggcd : n -> n -> n * (n * n) **)
  
  let ggcd a b =
    match a with
    | N0 -> (b, (N0, (Npos XH)))
    | Npos p ->
      (match b with
       | N0 -> (a, ((Npos XH), N0))
       | Npos q ->
         let (g, p0) = Coq_Pos.ggcd p q in
         let (aa, bb) = p0 in ((Npos g), ((Npos aa), (Npos bb))))
  
  (** val sqrtrem : n -> n * n **)
  
  let sqrtrem = function
  | N0 -> (N0, N0)
  | Npos p ->
    let (s, m) = Coq_Pos.sqrtrem p in
    (match m with
     | Coq_Pos.IsPos r -> ((Npos s), (Npos r))
     | _ -> ((Npos s), N0))
  
  (** val sqrt : n -> n **)
  
  let sqrt = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.sqrt p)
  
  (** val coq_lor : n -> n -> n **)
  
  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.coq_lor p q))
  
  (** val coq_land : n -> n -> n **)
  
  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Coq_Pos.coq_land p q)
  
  (** val ldiff : n -> n -> n **)
  
  let rec ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.ldiff p q)
  
  (** val coq_lxor : n -> n -> n **)
  
  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.coq_lxor p q)
  
  (** val shiftl_nat : n -> nat -> n **)
  
  let shiftl_nat a n0 =
    nat_iter n0 double a
  
  (** val shiftr_nat : n -> nat -> n **)
  
  let shiftr_nat a n0 =
    nat_iter n0 div2 a
  
  (** val shiftl : n -> n -> n **)
  
  let shiftl a n0 =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Coq_Pos.shiftl a0 n0)
  
  (** val shiftr : n -> n -> n **)
  
  let shiftr a = function
  | N0 -> a
  | Npos p -> Coq_Pos.iter p div2 a
  
  (** val testbit_nat : n -> nat -> bool **)
  
  let testbit_nat = function
  | N0 -> (fun x -> false)
  | Npos p -> Coq_Pos.testbit_nat p
  
  (** val testbit : n -> n -> bool **)
  
  let testbit a n0 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n0
  
  (** val to_nat : n -> nat **)
  
  let to_nat = function
  | N0 -> O
  | Npos p -> Coq_Pos.to_nat p
  
  (** val of_nat : nat -> n **)
  
  let of_nat = function
  | O -> N0
  | S n' -> Npos (Coq_Pos.of_succ_nat n')
  
  (** val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n0 f x =
    match n0 with
    | N0 -> x
    | Npos p -> Coq_Pos.iter p f x
  
  (** val eq_dec : n -> n -> bool **)
  
  let eq_dec n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos x ->
      (match m with
       | N0 -> false
       | Npos p0 -> Coq_Pos.eq_dec x p0)
  
  (** val discr : n -> positive option **)
  
  let discr = function
  | N0 -> None
  | Npos p -> Some p
  
  (** val binary_rect :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rect f0 f2 fS2 n0 =
    let f2' = fun p -> f2 (Npos p) in
    let fS2' = fun p -> fS2 (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p ->
       let rec f = function
       | XI p1 -> fS2' p1 (f p1)
       | XO p1 -> f2' p1 (f p1)
       | XH -> fS2 N0 f0
       in f p)
  
  (** val binary_rec :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rec =
    binary_rect
  
  (** val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rect f0 f n0 =
    let f' = fun p -> f (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p -> Coq_Pos.peano_rect (f N0 f0) f' p)
  
  (** val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  (** val leb_spec0 : n -> n -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : n -> n -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let recursion x =
    peano_rect x
  
  module Private_OrderTac = 
   struct 
    module Elts = 
     struct 
      type t = n
     end
    
    module Tac = MakeOrderTac(Elts)
   end
  
  module Private_NZPow = 
   struct 
    
   end
  
  module Private_NZSqrt = 
   struct 
    
   end
  
  (** val sqrt_up : n -> n **)
  
  let sqrt_up a =
    match compare N0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> N0
  
  (** val log2_up : n -> n **)
  
  let log2_up a =
    match compare (Npos XH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> N0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  (** val lcm : n -> n -> n **)
  
  let lcm a b =
    mul a (div b (gcd a b))
  
  (** val eqb_spec : n -> n -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2n : bool -> n **)
  
  let b2n = function
  | true -> Npos XH
  | false -> N0
  
  (** val setbit : n -> n -> n **)
  
  let setbit a n0 =
    coq_lor a (shiftl (Npos XH) n0)
  
  (** val clearbit : n -> n -> n **)
  
  let clearbit a n0 =
    ldiff a (shiftl (Npos XH) n0)
  
  (** val ones : n -> n **)
  
  let ones n0 =
    pred (shiftl (Npos XH) n0)
  
  (** val lnot : n -> n -> n **)
  
  let lnot a n0 =
    coq_lxor a (ones n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Rev = 
   struct 
    module ORev = 
     struct 
      type t = n
     end
    
    module MRev = 
     struct 
      (** val max : n -> n -> n **)
      
      let max x y =
        min y x
     end
    
    module MPRev = MaxLogicalProperties(ORev)(MRev)
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : n -> n -> bool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : n -> n -> bool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : n -> n -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : n -> n -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module Z = 
 struct 
  type t = z
  
  (** val zero : z **)
  
  let zero =
    Z0
  
  (** val one : z **)
  
  let one =
    Zpos XH
  
  (** val two : z **)
  
  let two =
    Zpos (XO XH)
  
  (** val double : z -> z **)
  
  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)
  
  (** val succ_double : z -> z **)
  
  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)
  
  (** val pred_double : z -> z **)
  
  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)
  
  (** val pos_sub : positive -> positive -> z **)
  
  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)
  
  (** val add : z -> z -> z **)
  
  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))
  
  (** val opp : z -> z **)
  
  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0
  
  (** val succ : z -> z **)
  
  let succ x =
    add x (Zpos XH)
  
  (** val pred : z -> z **)
  
  let pred x =
    add x (Zneg XH)
  
  (** val sub : z -> z -> z **)
  
  let sub m n0 =
    add m (opp n0)
  
  (** val mul : z -> z -> z **)
  
  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))
  
  (** val pow_pos : z -> positive -> z **)
  
  let pow_pos z0 n0 =
    Coq_Pos.iter n0 (mul z0) (Zpos XH)
  
  (** val pow : z -> z -> z **)
  
  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg p -> Z0
  
  (** val square : z -> z **)
  
  let square = function
  | Z0 -> Z0
  | Zpos p -> Zpos (Coq_Pos.square p)
  | Zneg p -> Zpos (Coq_Pos.square p)
  
  (** val compare : z -> z -> comparison **)
  
  let compare x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> Eq
       | Zpos y' -> Lt
       | Zneg y' -> Gt)
    | Zpos x' ->
      (match y with
       | Zpos y' -> Coq_Pos.compare x' y'
       | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)
  
  (** val sgn : z -> z **)
  
  let sgn = function
  | Z0 -> Z0
  | Zpos p -> Zpos XH
  | Zneg p -> Zneg XH
  
  (** val leb : z -> z -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : z -> z -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val geb : z -> z -> bool **)
  
  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true
  
  (** val gtb : z -> z -> bool **)
  
  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false
  
  (** val eqb : z -> z -> bool **)
  
  let rec eqb x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> true
       | _ -> false)
    | Zpos p ->
      (match y with
       | Zpos q -> Coq_Pos.eqb p q
       | _ -> false)
    | Zneg p ->
      (match y with
       | Zneg q -> Coq_Pos.eqb p q
       | _ -> false)
  
  (** val max : z -> z -> z **)
  
  let max n0 m =
    match compare n0 m with
    | Lt -> m
    | _ -> n0
  
  (** val min : z -> z -> z **)
  
  let min n0 m =
    match compare n0 m with
    | Gt -> m
    | _ -> n0
  
  (** val abs : z -> z **)
  
  let abs = function
  | Zneg p -> Zpos p
  | x -> x
  
  (** val abs_nat : z -> nat **)
  
  let abs_nat = function
  | Z0 -> O
  | Zpos p -> Coq_Pos.to_nat p
  | Zneg p -> Coq_Pos.to_nat p
  
  (** val abs_N : z -> n **)
  
  let abs_N = function
  | Z0 -> N0
  | Zpos p -> Npos p
  | Zneg p -> Npos p
  
  (** val to_nat : z -> nat **)
  
  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> O
  
  (** val to_N : z -> n **)
  
  let to_N = function
  | Zpos p -> Npos p
  | _ -> N0
  
  (** val of_nat : nat -> z **)
  
  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Coq_Pos.of_succ_nat n1)
  
  (** val of_N : n -> z **)
  
  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p
  
  (** val to_pos : z -> positive **)
  
  let to_pos = function
  | Zpos p -> p
  | _ -> XH
  
  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n0 f x =
    match n0 with
    | Zpos p -> Coq_Pos.iter p f x
    | _ -> x
  
  (** val pos_div_eucl : positive -> z -> z * z **)
  
  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)
  
  (** val div_eucl : z -> z -> z * z **)
  
  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, Z0)
       | Zpos p -> pos_div_eucl a' b
       | Zneg b' ->
         let (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, Z0)
       | Zpos p ->
         let (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q, r) = pos_div_eucl a' (Zpos b') in (q, (opp r)))
  
  (** val div : z -> z -> z **)
  
  let div a b =
    let (q, x) = div_eucl a b in q
  
  (** val modulo : z -> z -> z **)
  
  let modulo a b =
    let (x, r) = div_eucl a b in r
  
  (** val quotrem : z -> z -> z * z **)
  
  let quotrem a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in ((of_N q), (of_N r))
       | Zneg b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 ->
         let (q, r) = N.pos_div_eucl a0 (Npos b0) in
         ((of_N q), (opp (of_N r))))
  
  (** val quot : z -> z -> z **)
  
  let quot a b =
    fst (quotrem a b)
  
  (** val rem : z -> z -> z **)
  
  let rem a b =
    snd (quotrem a b)
  
  (** val even : z -> bool **)
  
  let even = function
  | Z0 -> true
  | Zpos p ->
    (match p with
     | XO p0 -> true
     | _ -> false)
  | Zneg p ->
    (match p with
     | XO p0 -> true
     | _ -> false)
  
  (** val odd : z -> bool **)
  
  let odd = function
  | Z0 -> false
  | Zpos p ->
    (match p with
     | XO p0 -> false
     | _ -> true)
  | Zneg p ->
    (match p with
     | XO p0 -> false
     | _ -> true)
  
  (** val div2 : z -> z **)
  
  let div2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p -> Zneg (Coq_Pos.div2_up p)
  
  (** val quot2 : z -> z **)
  
  let quot2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p ->
    (match p with
     | XH -> Z0
     | _ -> Zneg (Coq_Pos.div2 p))
  
  (** val log2 : z -> z **)
  
  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0
  
  (** val sqrtrem : z -> z * z **)
  
  let sqrtrem = function
  | Zpos p ->
    let (s, m) = Coq_Pos.sqrtrem p in
    (match m with
     | Coq_Pos.IsPos r -> ((Zpos s), (Zpos r))
     | _ -> ((Zpos s), Z0))
  | _ -> (Z0, Z0)
  
  (** val sqrt : z -> z **)
  
  let sqrt = function
  | Zpos p -> Zpos (Coq_Pos.sqrt p)
  | _ -> Z0
  
  (** val gcd : z -> z -> z **)
  
  let gcd a b =
    match a with
    | Z0 -> abs b
    | Zpos a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))
    | Zneg a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))
  
  (** val ggcd : z -> z -> z * (z * z) **)
  
  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
  
  (** val testbit : z -> z -> bool **)
  
  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> false
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg p -> false
  
  (** val shiftl : z -> z -> z **)
  
  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Coq_Pos.iter p (mul (Zpos (XO XH))) a
  | Zneg p -> Coq_Pos.iter p div2 a
  
  (** val shiftr : z -> z -> z **)
  
  let shiftr a n0 =
    shiftl a (opp n0)
  
  (** val coq_lor : z -> z -> z **)
  
  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Coq_Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
  
  (** val coq_land : z -> z -> z **)
  
  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Coq_Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Coq_Pos.pred_N a0))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
  
  (** val ldiff : z -> z -> z **)
  
  let ldiff a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.ldiff a0 b0)
       | Zneg b0 -> of_N (N.coq_land (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.ldiff (Coq_Pos.pred_N b0) (Coq_Pos.pred_N a0)))
  
  (** val coq_lxor : z -> z -> z **)
  
  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.coq_lxor a0 b0)
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))
  
  (** val eq_dec : z -> z -> bool **)
  
  let eq_dec x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> true
       | _ -> false)
    | Zpos x0 ->
      (match y with
       | Zpos p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> false)
    | Zneg x0 ->
      (match y with
       | Zneg p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> false)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val leb_spec0 : z -> z -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : z -> z -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_OrderTac = 
   struct 
    module Elts = 
     struct 
      type t = z
     end
    
    module Tac = MakeOrderTac(Elts)
   end
  
  (** val sqrt_up : z -> z **)
  
  let sqrt_up a =
    match compare Z0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> Z0
  
  (** val log2_up : z -> z **)
  
  let log2_up a =
    match compare (Zpos XH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> Z0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  module Private_Div = 
   struct 
    module Quot2Div = 
     struct 
      (** val div : z -> z -> z **)
      
      let div =
        quot
      
      (** val modulo : z -> z -> z **)
      
      let modulo =
        rem
     end
    
    module NZQuot = 
     struct 
      
     end
   end
  
  (** val lcm : z -> z -> z **)
  
  let lcm a b =
    abs (mul a (div b (gcd a b)))
  
  (** val eqb_spec : z -> z -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2z : bool -> z **)
  
  let b2z = function
  | true -> Zpos XH
  | false -> Z0
  
  (** val setbit : z -> z -> z **)
  
  let setbit a n0 =
    coq_lor a (shiftl (Zpos XH) n0)
  
  (** val clearbit : z -> z -> z **)
  
  let clearbit a n0 =
    ldiff a (shiftl (Zpos XH) n0)
  
  (** val lnot : z -> z **)
  
  let lnot a =
    pred (opp a)
  
  (** val ones : z -> z **)
  
  let ones n0 =
    pred (shiftl (Zpos XH) n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Rev = 
   struct 
    module ORev = 
     struct 
      type t = z
     end
    
    module MRev = 
     struct 
      (** val max : z -> z -> z **)
      
      let max x y =
        min y x
     end
    
    module MPRev = MaxLogicalProperties(ORev)(MRev)
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : z -> z -> bool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : z -> z -> bool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : z -> z -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : z -> z -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

(** val z_gt_dec : z -> z -> bool **)

let z_gt_dec x y =
  match Z.compare x y with
  | Gt -> true
  | _ -> false

(** val z_ge_dec : z -> z -> bool **)

let z_ge_dec x y =
  match Z.compare x y with
  | Lt -> false
  | _ -> true

(** val z_gt_le_dec : z -> z -> bool **)

let z_gt_le_dec x y =
  z_gt_dec x y

(** val z_ge_lt_dec : z -> z -> bool **)

let z_ge_lt_dec x y =
  z_ge_dec x y

type 'a orderedType =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_OrderedType *)

(** val _cmp : 'a1 orderedType -> 'a1 -> 'a1 -> comparison **)

let _cmp orderedType0 =
  orderedType0

(** val compare0 : 'a1 orderedType -> 'a1 -> 'a1 -> comparison **)

let compare0 h =
  _cmp h

type 'a specificOrderedType =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_SpecificOrderedType *)

(** val sOT_cmp : 'a1 specificOrderedType -> 'a1 -> 'a1 -> comparison **)

let sOT_cmp specificOrderedType0 =
  specificOrderedType0

(** val sOT_as_OT : 'a1 specificOrderedType -> 'a1 orderedType **)

let sOT_as_OT h =
  sOT_cmp h

(** val z_OrderedType : z specificOrderedType **)

let z_OrderedType =
  Z.compare

(** val prod_compare :
    'a1 orderedType -> 'a2 orderedType -> ('a1 * 'a2) -> ('a1 * 'a2) ->
    comparison **)

let prod_compare h h0 x y =
  let (a, b) = x in
  let (c, d) = y in
  (match compare0 h a c with
   | Eq -> compare0 h0 b d
   | x0 -> x0)

(** val prod_OrderedType :
    'a1 orderedType -> 'a2 orderedType -> ('a1 * 'a2) orderedType **)

let prod_OrderedType h h0 =
  prod_compare h h0

(** val list_compare :
    'a1 orderedType -> 'a1 list -> 'a1 list -> comparison **)

let rec list_compare h x y =
  match x with
  | [] ->
    (match y with
     | [] -> Eq
     | a :: l -> Lt)
  | a :: l ->
    (match y with
     | [] -> Gt
     | a' :: l' ->
       (match compare0 h a a' with
        | Eq -> list_compare h l l'
        | x0 -> x0))

(** val list_OrderedType : 'a1 orderedType -> 'a1 list orderedType **)

let list_OrderedType h =
  list_compare h

type 'a fSet = { empty : __; is_empty : (__ -> bool);
                 mem : ('a -> __ -> bool); add0 : ('a -> __ -> __);
                 singleton : ('a -> __); remove : ('a -> __ -> __);
                 union : (__ -> __ -> __); inter : (__ -> __ -> __);
                 diff : (__ -> __ -> __); equal : (__ -> __ -> bool);
                 subset : (__ -> __ -> bool);
                 fold : (__ -> ('a -> __ -> __) -> __ -> __ -> __);
                 for_all : (('a -> bool) -> __ -> bool);
                 exists_ : (('a -> bool) -> __ -> bool);
                 filter : (('a -> bool) -> __ -> __);
                 partition : (('a -> bool) -> __ -> __ * __);
                 cardinal : (__ -> nat); elements : (__ -> 'a list);
                 choose : (__ -> 'a option); min_elt : (__ -> 'a option);
                 max_elt : (__ -> 'a option);
                 fSet_OrderedType : __ specificOrderedType }

type 'a set = __

(** val empty : 'a1 orderedType -> 'a1 fSet -> 'a1 set **)

let empty _ x = x.empty

(** val mem : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set -> bool **)

let mem _ x = x.mem

(** val add0 : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set -> 'a1 set **)

let add0 _ x = x.add0

(** val singleton : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set **)

let singleton _ x = x.singleton

(** val remove : 'a1 orderedType -> 'a1 fSet -> 'a1 -> 'a1 set -> 'a1 set **)

let remove _ x = x.remove

(** val union :
    'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 set -> 'a1 set **)

let union _ x = x.union

(** val fold :
    'a1 orderedType -> 'a1 fSet -> ('a1 -> 'a2 -> 'a2) -> 'a1 set -> 'a2 ->
    'a2 **)

let fold h fSet0 x x0 x1 =
  let { empty = empty1; is_empty = is_empty1; mem = mem1; add0 = add2;
    singleton = singleton1; remove = remove1; union = union1; inter = inter1;
    diff = diff1; equal = equal1; subset = subset1; fold = fold1; for_all =
    for_all1; exists_ = exists_1; filter = filter1; partition = partition1;
    cardinal = cardinal1; elements = elements1; choose = choose1; min_elt =
    min_elt1; max_elt = max_elt1; fSet_OrderedType = fSet_OrderedType0 } =
    fSet0
  in
  Obj.magic fold1 __ x x0 x1

(** val filter :
    'a1 orderedType -> 'a1 fSet -> ('a1 -> bool) -> 'a1 set -> 'a1 set **)

let filter _ x = x.filter

(** val choose : 'a1 orderedType -> 'a1 fSet -> 'a1 set -> 'a1 option **)

let choose _ x = x.choose

(** val fSet_OrderedType :
    'a1 orderedType -> 'a1 fSet -> 'a1 set specificOrderedType **)

let fSet_OrderedType _ x = x.fSet_OrderedType

module SetList = 
 struct 
  type 'a set = 'a list
  
  (** val empty : 'a1 orderedType -> 'a1 set **)
  
  let empty comparedec =
    []
  
  (** val is_empty : 'a1 orderedType -> 'a1 set -> bool **)
  
  let is_empty comparedec = function
  | [] -> true
  | x :: x0 -> false
  
  (** val mem : 'a1 orderedType -> 'a1 -> 'a1 set -> bool **)
  
  let rec mem comparedec x = function
  | [] -> false
  | y :: l ->
    (match compare0 comparedec x y with
     | Eq -> true
     | Lt -> false
     | Gt -> mem comparedec x l)
  
  (** val add : 'a1 orderedType -> 'a1 -> 'a1 set -> 'a1 set **)
  
  let rec add comparedec x s = match s with
  | [] -> x :: []
  | y :: l ->
    (match compare0 comparedec x y with
     | Eq -> s
     | Lt -> x :: s
     | Gt -> y :: (add comparedec x l))
  
  (** val singleton : 'a1 orderedType -> 'a1 -> 'a1 set **)
  
  let singleton comparedec x =
    x :: []
  
  (** val remove : 'a1 orderedType -> 'a1 -> 'a1 set -> 'a1 set **)
  
  let rec remove comparedec x s = match s with
  | [] -> []
  | y :: l ->
    (match compare0 comparedec x y with
     | Eq -> l
     | Lt -> s
     | Gt -> y :: (remove comparedec x l))
  
  (** val union : 'a1 orderedType -> 'a1 set -> 'a1 set -> 'a1 set **)
  
  let rec union comparedec s = match s with
  | [] -> (fun s' -> s')
  | x :: l ->
    let rec union_aux s' = match s' with
    | [] -> s
    | x' :: l' ->
      (match compare0 comparedec x x' with
       | Eq -> x :: (union comparedec l l')
       | Lt -> x :: (union comparedec l s')
       | Gt -> x' :: (union_aux l'))
    in union_aux
  
  (** val inter : 'a1 orderedType -> 'a1 set -> 'a1 set -> 'a1 set **)
  
  let rec inter comparedec = function
  | [] -> (fun x -> [])
  | x :: l ->
    let rec inter_aux s' = match s' with
    | [] -> []
    | x' :: l' ->
      (match compare0 comparedec x x' with
       | Eq -> x :: (inter comparedec l l')
       | Lt -> inter comparedec l s'
       | Gt -> inter_aux l')
    in inter_aux
  
  (** val diff : 'a1 orderedType -> 'a1 set -> 'a1 set -> 'a1 set **)
  
  let rec diff comparedec s = match s with
  | [] -> (fun x -> [])
  | x :: l ->
    let rec diff_aux s' = match s' with
    | [] -> s
    | x' :: l' ->
      (match compare0 comparedec x x' with
       | Eq -> diff comparedec l l'
       | Lt -> x :: (diff comparedec l s')
       | Gt -> diff_aux l')
    in diff_aux
  
  (** val equal : 'a1 orderedType -> 'a1 set -> 'a1 set -> bool **)
  
  let rec equal comparedec s s' =
    match s with
    | [] ->
      (match s' with
       | [] -> true
       | e :: l -> false)
    | x :: l ->
      (match s' with
       | [] -> false
       | x' :: l' ->
         (match compare0 comparedec x x' with
          | Eq -> equal comparedec l l'
          | _ -> false))
  
  (** val subset : 'a1 orderedType -> 'a1 set -> 'a1 set -> bool **)
  
  let rec subset comparedec s s' =
    match s with
    | [] -> true
    | x :: l ->
      (match s' with
       | [] -> false
       | x' :: l' ->
         (match compare0 comparedec x x' with
          | Eq -> subset comparedec l l'
          | Lt -> false
          | Gt -> subset comparedec s l'))
  
  (** val fold :
      'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 set -> 'a2 -> 'a2 **)
  
  let rec fold comparedec f s i =
    match s with
    | [] -> i
    | x :: l -> fold comparedec f l (f x i)
  
  (** val map_monotonic :
      'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 set -> 'a2
      set **)
  
  let map_monotonic comparedec h f s =
    map f s
  
  (** val filter : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> 'a1 set **)
  
  let rec filter comparedec f = function
  | [] -> []
  | x :: l ->
    if f x then x :: (filter comparedec f l) else filter comparedec f l
  
  (** val for_all : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> bool **)
  
  let rec for_all comparedec f = function
  | [] -> true
  | x :: l -> if f x then for_all comparedec f l else false
  
  (** val exists_ : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> bool **)
  
  let rec exists_ comparedec f = function
  | [] -> false
  | x :: l -> if f x then true else exists_ comparedec f l
  
  (** val partition :
      'a1 orderedType -> ('a1 -> bool) -> 'a1 set -> 'a1 set * 'a1 set **)
  
  let rec partition comparedec f = function
  | [] -> ([], [])
  | x :: l ->
    let (s1, s2) = partition comparedec f l in
    if f x then ((x :: s1), s2) else (s1, (x :: s2))
  
  (** val cardinal : 'a1 orderedType -> 'a1 set -> nat **)
  
  let cardinal comparedec s =
    lengthk s
  
  (** val elements : 'a1 orderedType -> 'a1 set -> 'a1 list **)
  
  let elements comparedec x =
    x
  
  (** val min_elt : 'a1 orderedType -> 'a1 set -> 'a1 option **)
  
  let min_elt comparedec = function
  | [] -> None
  | x :: l -> Some x
  
  (** val max_elt : 'a1 orderedType -> 'a1 set -> 'a1 option **)
  
  let rec max_elt comparedec = function
  | [] -> None
  | x :: l ->
    (match l with
     | [] -> Some x
     | e :: l0 -> max_elt comparedec l)
  
  (** val choose : 'a1 orderedType -> 'a1 set -> 'a1 option **)
  
  let choose comparedec =
    min_elt comparedec
  
  (** val map :
      'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 set -> 'a2
      set **)
  
  let map h h0 f s =
    fold h (fun a sb -> add h0 (f a) sb) s (empty h0)
  
  (** val set_compare :
      'a1 orderedType -> 'a1 set -> 'a1 set -> comparison **)
  
  let set_compare h =
    list_compare h
  
  (** val set_OrderedType : 'a1 orderedType -> 'a1 set orderedType **)
  
  let set_OrderedType h =
    list_OrderedType h
 end

module SetAVL = 
 struct 
  type 'elt tree =
  | Leaf
  | Node of 'elt tree * 'elt * 'elt tree * z
  
  (** val tree_rect :
      'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 ->
      z -> 'a2) -> 'a1 tree -> 'a2 **)
  
  let rec tree_rect h f f0 = function
  | Leaf -> f
  | Node (t1, y, t2, z0) ->
    f0 t1 (tree_rect h f f0 t1) y t2 (tree_rect h f f0 t2) z0
  
  (** val tree_rec :
      'a1 orderedType -> 'a2 -> ('a1 tree -> 'a2 -> 'a1 -> 'a1 tree -> 'a2 ->
      z -> 'a2) -> 'a1 tree -> 'a2 **)
  
  let rec tree_rec h f f0 = function
  | Leaf -> f
  | Node (t1, y, t2, z0) ->
    f0 t1 (tree_rec h f f0 t1) y t2 (tree_rec h f f0 t2) z0
  
  (** val height : 'a1 orderedType -> 'a1 tree -> z **)
  
  let height h = function
  | Leaf -> Z0
  | Node (t0, e, t1, h0) -> h0
  
  (** val cardinal : 'a1 orderedType -> 'a1 tree -> nat **)
  
  let rec cardinal h = function
  | Leaf -> O
  | Node (l, e, r, z0) -> S (plus (cardinal h l) (cardinal h r))
  
  (** val empty : 'a1 orderedType -> 'a1 tree **)
  
  let empty h =
    Leaf
  
  (** val is_empty : 'a1 orderedType -> 'a1 tree -> bool **)
  
  let is_empty h = function
  | Leaf -> true
  | Node (t0, y, t1, z0) -> false
  
  (** val mem : 'a1 orderedType -> 'a1 -> 'a1 tree -> bool **)
  
  let rec mem h x = function
  | Leaf -> false
  | Node (l, y, r, z0) ->
    (match compare0 h x y with
     | Eq -> true
     | Lt -> mem h x l
     | Gt -> mem h x r)
  
  (** val singleton : 'a1 orderedType -> 'a1 -> 'a1 tree **)
  
  let singleton h x =
    Node (Leaf, x, Leaf, (Zpos XH))
  
  (** val create :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let create h l x r =
    Node (l, x, r, (Z.add (Z.max (height h l) (height h r)) (Zpos XH)))
  
  (** val assert_false :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let assert_false h =
    create h
  
  (** val bal :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let bal h l x r =
    let hl = height h l in
    let hr = height h r in
    if z_gt_le_dec hl (Z.add hr (Zpos (XO XH)))
    then (match l with
          | Leaf -> assert_false h l x r
          | Node (ll, lx, lr, z0) ->
            if z_ge_lt_dec (height h ll) (height h lr)
            then create h ll lx (create h lr x r)
            else (match lr with
                  | Leaf -> assert_false h l x r
                  | Node (lrl, lrx, lrr, z1) ->
                    create h (create h ll lx lrl) lrx (create h lrr x r)))
    else if z_gt_le_dec hr (Z.add hl (Zpos (XO XH)))
         then (match r with
               | Leaf -> assert_false h l x r
               | Node (rl, rx, rr, z0) ->
                 if z_ge_lt_dec (height h rr) (height h rl)
                 then create h (create h l x rl) rx rr
                 else (match rl with
                       | Leaf -> assert_false h l x r
                       | Node (rll, rlx, rlr, z1) ->
                         create h (create h l x rll) rlx (create h rlr rx rr)))
         else create h l x r
  
  (** val add : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let rec add h x = function
  | Leaf -> Node (Leaf, x, Leaf, (Zpos XH))
  | Node (l, y, r, h0) ->
    (match compare0 h x y with
     | Eq -> Node (l, y, r, h0)
     | Lt -> bal h (add h x l) y r
     | Gt -> bal h l y (add h x r))
  
  (** val join :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let rec join h l = match l with
  | Leaf -> add h
  | Node (ll, lx, lr, lh) ->
    (fun x ->
      let rec join_aux r = match r with
      | Leaf -> add h x l
      | Node (rl, rx, rr, rh) ->
        if z_gt_le_dec lh (Z.add rh (Zpos (XO XH)))
        then bal h ll lx (join h lr x r)
        else if z_gt_le_dec rh (Z.add lh (Zpos (XO XH)))
             then bal h (join_aux rl) rx rr
             else create h l x r
      in join_aux)
  
  (** val remove_min :
      'a1 orderedType -> 'a1 tree -> 'a1 -> 'a1 tree -> 'a1 tree * 'a1 **)
  
  let rec remove_min h l x r =
    match l with
    | Leaf -> (r, x)
    | Node (ll, lx, lr, lh) ->
      let (l', m) = remove_min h ll lx lr in ((bal h l' x r), m)
  
  (** val merge : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let merge h s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, y, t1, z0) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, r2, h2) ->
         let (s2', m) = remove_min h l2 x2 r2 in bal h s1 m s2')
  
  (** val remove : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let rec remove h x = function
  | Leaf -> Leaf
  | Node (l, y, r, h0) ->
    (match compare0 h x y with
     | Eq -> merge h l r
     | Lt -> bal h (remove h x l) y r
     | Gt -> bal h l y (remove h x r))
  
  (** val min_elt : 'a1 orderedType -> 'a1 tree -> 'a1 option **)
  
  let rec min_elt h = function
  | Leaf -> None
  | Node (l, y, t0, z0) ->
    (match l with
     | Leaf -> Some y
     | Node (t1, y0, t2, z1) -> min_elt h l)
  
  (** val max_elt : 'a1 orderedType -> 'a1 tree -> 'a1 option **)
  
  let rec max_elt h = function
  | Leaf -> None
  | Node (t0, y, r, z0) ->
    (match r with
     | Leaf -> Some y
     | Node (t1, y0, t2, z1) -> max_elt h r)
  
  (** val choose : 'a1 orderedType -> 'a1 tree -> 'a1 option **)
  
  let choose h =
    min_elt h
  
  (** val concat : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let concat h s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, y, t1, z0) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, r2, z1) ->
         let (s2', m) = remove_min h l2 x2 r2 in join h s1 m s2')
  
  type 'elt triple = { t_left : 'elt tree; t_in : bool; t_right : 'elt tree }
  
  (** val triple_rect :
      'a1 orderedType -> ('a1 tree -> bool -> 'a1 tree -> 'a2) -> 'a1 triple
      -> 'a2 **)
  
  let triple_rect h f t0 =
    let { t_left = x; t_in = x0; t_right = x1 } = t0 in f x x0 x1
  
  (** val triple_rec :
      'a1 orderedType -> ('a1 tree -> bool -> 'a1 tree -> 'a2) -> 'a1 triple
      -> 'a2 **)
  
  let triple_rec h f t0 =
    let { t_left = x; t_in = x0; t_right = x1 } = t0 in f x x0 x1
  
  (** val t_left : 'a1 orderedType -> 'a1 triple -> 'a1 tree **)
  
  let t_left _ x = x.t_left
  
  (** val t_in : 'a1 orderedType -> 'a1 triple -> bool **)
  
  let t_in _ x = x.t_in
  
  (** val t_right : 'a1 orderedType -> 'a1 triple -> 'a1 tree **)
  
  let t_right _ x = x.t_right
  
  (** val split : 'a1 orderedType -> 'a1 -> 'a1 tree -> 'a1 triple **)
  
  let rec split h x = function
  | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
  | Node (l, y, r, h0) ->
    (match compare0 h x y with
     | Eq -> { t_left = l; t_in = true; t_right = r }
     | Lt ->
       let { t_left = ll; t_in = b; t_right = rl } = split h x l in
       { t_left = ll; t_in = b; t_right = (join h rl y r) }
     | Gt ->
       let { t_left = rl; t_in = b; t_right = rr } = split h x r in
       { t_left = (join h l y rl); t_in = b; t_right = rr })
  
  (** val inter : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let rec inter h s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> Leaf
       | Node (t0, y, t1, z0) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split h x1 s2 in
         if pres
         then join h (inter h l1 l2') x1 (inter h r1 r2')
         else concat h (inter h l1 l2') (inter h r1 r2'))
  
  (** val diff : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let rec diff h s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> s1
       | Node (t0, y, t1, z0) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split h x1 s2 in
         if pres
         then concat h (diff h l1 l2') (diff h r1 r2')
         else join h (diff h l1 l2') x1 (diff h r1 r2'))
  
  (** val union : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let rec union h s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> s1
       | Node (t0, y, t1, z0) ->
         let { t_left = l2'; t_in = x; t_right = r2' } = split h x1 s2 in
         join h (union h l1 l2') x1 (union h r1 r2'))
  
  (** val elements_aux :
      'a1 orderedType -> 'a1 list -> 'a1 tree -> 'a1 list **)
  
  let rec elements_aux h acc = function
  | Leaf -> acc
  | Node (l, x, r, z0) -> elements_aux h (x :: (elements_aux h acc r)) l
  
  (** val elements : 'a1 orderedType -> 'a1 tree -> 'a1 list **)
  
  let elements h =
    elements_aux h []
  
  (** val filter_acc :
      'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let rec filter_acc h f acc = function
  | Leaf -> acc
  | Node (l, x, r, h0) ->
    filter_acc h f (filter_acc h f (if f x then add h x acc else acc) l) r
  
  (** val filter :
      'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree **)
  
  let filter h f =
    filter_acc h f Leaf
  
  (** val partition_acc :
      'a1 orderedType -> ('a1 -> bool) -> ('a1 tree * 'a1 tree) -> 'a1 tree
      -> 'a1 tree * 'a1 tree **)
  
  let rec partition_acc h f acc = function
  | Leaf -> acc
  | Node (l, x, r, z0) ->
    let (acct, accf) = acc in
    partition_acc h f
      (partition_acc h f
        (if f x then ((add h x acct), accf) else (acct, (add h x accf))) l) r
  
  (** val partition :
      'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> 'a1 tree * 'a1 tree **)
  
  let partition h f =
    partition_acc h f (Leaf, Leaf)
  
  (** val for_all : 'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> bool **)
  
  let rec for_all h f = function
  | Leaf -> true
  | Node (l, x, r, z0) ->
    if if f x then for_all h f l else false then for_all h f r else false
  
  (** val exists_ : 'a1 orderedType -> ('a1 -> bool) -> 'a1 tree -> bool **)
  
  let rec exists_ h f = function
  | Leaf -> false
  | Node (l, x, r, z0) ->
    if if f x then true else exists_ h f l then true else exists_ h f r
  
  (** val map_monotonic :
      'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 tree -> 'a2
      tree **)
  
  let rec map_monotonic h hB f = function
  | Leaf -> Leaf
  | Node (l, x, r, h0) ->
    Node ((map_monotonic h hB f l), (f x), (map_monotonic h hB f r), h0)
  
  (** val fold :
      'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)
  
  let rec fold h f s x =
    match s with
    | Leaf -> x
    | Node (l, x0, r, z0) -> fold h f r (f x0 (fold h f l x))
  
  (** val subsetl :
      'a1 orderedType -> ('a1 tree -> bool) -> 'a1 -> 'a1 tree -> bool **)
  
  let rec subsetl h subset_l1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (l2, x2, r2, h2) ->
    (match compare0 h x1 x2 with
     | Eq -> subset_l1 l2
     | Lt -> subsetl h subset_l1 x1 l2
     | Gt -> if mem h x1 r2 then subset_l1 s2 else false)
  
  (** val subsetr :
      'a1 orderedType -> ('a1 tree -> bool) -> 'a1 -> 'a1 tree -> bool **)
  
  let rec subsetr h subset_r1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (l2, x2, r2, h2) ->
    (match compare0 h x1 x2 with
     | Eq -> subset_r1 r2
     | Lt -> if mem h x1 l2 then subset_r1 s2 else false
     | Gt -> subsetr h subset_r1 x1 r2)
  
  (** val subset : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> bool **)
  
  let rec subset h s1 s2 =
    match s1 with
    | Leaf -> true
    | Node (l1, x1, r1, h1) ->
      (match s2 with
       | Leaf -> false
       | Node (l2, x2, r2, h2) ->
         (match compare0 h x1 x2 with
          | Eq -> if subset h l1 l2 then subset h r1 r2 else false
          | Lt ->
            if subsetl h (subset h l1) x1 l2 then subset h r1 s2 else false
          | Gt ->
            if subsetr h (subset h r1) x1 r2 then subset h l1 s2 else false))
  
  type 'elt enumeration =
  | End
  | More of 'elt * 'elt tree * 'elt enumeration
  
  (** val enumeration_rect :
      'a1 orderedType -> 'a2 -> ('a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 ->
      'a2) -> 'a1 enumeration -> 'a2 **)
  
  let rec enumeration_rect h f f0 = function
  | End -> f
  | More (e0, t0, e1) -> f0 e0 t0 e1 (enumeration_rect h f f0 e1)
  
  (** val enumeration_rec :
      'a1 orderedType -> 'a2 -> ('a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 ->
      'a2) -> 'a1 enumeration -> 'a2 **)
  
  let rec enumeration_rec h f f0 = function
  | End -> f
  | More (e0, t0, e1) -> f0 e0 t0 e1 (enumeration_rec h f f0 e1)
  
  (** val cons :
      'a1 orderedType -> 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)
  
  let rec cons h s e =
    match s with
    | Leaf -> e
    | Node (l, x, r, h0) -> cons h l (More (x, r, e))
  
  (** val compare_more :
      'a1 orderedType -> 'a1 -> ('a1 enumeration -> comparison) -> 'a1
      enumeration -> comparison **)
  
  let compare_more h x1 cont = function
  | End -> Gt
  | More (x2, r2, e3) ->
    (match compare0 h x1 x2 with
     | Eq -> cont (cons h r2 e3)
     | x -> x)
  
  (** val compare_cont :
      'a1 orderedType -> 'a1 tree -> ('a1 enumeration -> comparison) -> 'a1
      enumeration -> comparison **)
  
  let rec compare_cont h s1 cont e2 =
    match s1 with
    | Leaf -> cont e2
    | Node (l1, x1, r1, z0) ->
      compare_cont h l1 (compare_more h x1 (compare_cont h r1 cont)) e2
  
  (** val compare_end : 'a1 orderedType -> 'a1 enumeration -> comparison **)
  
  let compare_end h = function
  | End -> Eq
  | More (e, t0, e0) -> Lt
  
  (** val compare : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> comparison **)
  
  let compare h s1 s2 =
    compare_cont h s1 (compare_end h) (cons h s2 End)
  
  (** val equal : 'a1 orderedType -> 'a1 tree -> 'a1 tree -> bool **)
  
  let equal h s1 s2 =
    match compare h s1 s2 with
    | Eq -> true
    | _ -> false
  
  type 'elt coq_R_mem =
  | R_mem_0 of 'elt tree
  | R_mem_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_mem_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * bool
     * 'elt coq_R_mem
  | R_mem_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * bool
     * 'elt coq_R_mem
  
  (** val coq_R_mem_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool -> 'a1 coq_R_mem ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
      coq_R_mem -> 'a2 **)
  
  let rec coq_R_mem_rect h x f f0 f1 f2 s b = function
  | R_mem_0 s0 -> f s0 __
  | R_mem_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_mem_2 (s0, l, y, r0, _x, res, r1) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_mem_rect h x f f0 f1 f2 l res r1)
  | R_mem_3 (s0, l, y, r0, _x, res, r1) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_mem_rect h x f f0 f1 f2 r0 res r1)
  
  (** val coq_R_mem_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> bool -> 'a1 coq_R_mem ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
      coq_R_mem -> 'a2 **)
  
  let rec coq_R_mem_rec h x f f0 f1 f2 s b = function
  | R_mem_0 s0 -> f s0 __
  | R_mem_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_mem_2 (s0, l, y, r0, _x, res, r1) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_mem_rec h x f f0 f1 f2 l res r1)
  | R_mem_3 (s0, l, y, r0, _x, res, r1) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_mem_rec h x f f0 f1 f2 r0 res r1)
  
  type 'elt coq_R_bal =
  | R_bal_0 of 'elt tree * 'elt * 'elt tree
  | R_bal_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_2 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_3 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z * 'elt tree * 'elt * 'elt tree * z
  | R_bal_4 of 'elt tree * 'elt * 'elt tree
  | R_bal_5 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_6 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z
  | R_bal_7 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt * 'elt tree
     * z * 'elt tree * 'elt * 'elt tree * z
  | R_bal_8 of 'elt tree * 'elt * 'elt tree
  
  (** val coq_R_bal_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree
      -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> __
      -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z
      -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
      -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
      -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> z -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 ->
      'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
      __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a2) ->
      ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
      tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)
  
  let coq_R_bal_rect h f f0 f1 f2 f3 f4 f5 f6 f7 l x r t0 = function
  | R_bal_0 (x0, x1, x2) -> f x0 x1 x2 __ __ __
  | R_bal_1 (x0, x1, x2, x3, x4, x5, x6) ->
    f0 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __
  | R_bal_2 (x0, x1, x2, x3, x4, x5, x6) ->
    f1 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __ __
  | R_bal_3 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f2 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __ x7 x8 x9 x10 __
  | R_bal_4 (x0, x1, x2) -> f3 x0 x1 x2 __ __ __ __ __
  | R_bal_5 (x0, x1, x2, x3, x4, x5, x6) ->
    f4 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __
  | R_bal_6 (x0, x1, x2, x3, x4, x5, x6) ->
    f5 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __ __
  | R_bal_7 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f6 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __ x7 x8 x9 x10 __
  | R_bal_8 (x0, x1, x2) -> f7 x0 x1 x2 __ __ __ __
  
  (** val coq_R_bal_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree
      -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> __
      -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z
      -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
      -> __ -> 'a2) -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
      -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 ->
      'a1 tree -> z -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 ->
      'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z ->
      __ -> __ -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a2) ->
      ('a1 tree -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
      tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)
  
  let coq_R_bal_rec h f f0 f1 f2 f3 f4 f5 f6 f7 l x r t0 = function
  | R_bal_0 (x0, x1, x2) -> f x0 x1 x2 __ __ __
  | R_bal_1 (x0, x1, x2, x3, x4, x5, x6) ->
    f0 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __
  | R_bal_2 (x0, x1, x2, x3, x4, x5, x6) ->
    f1 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __ __
  | R_bal_3 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f2 x0 x1 x2 __ __ x3 x4 x5 x6 __ __ __ x7 x8 x9 x10 __
  | R_bal_4 (x0, x1, x2) -> f3 x0 x1 x2 __ __ __ __ __
  | R_bal_5 (x0, x1, x2, x3, x4, x5, x6) ->
    f4 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __
  | R_bal_6 (x0, x1, x2, x3, x4, x5, x6) ->
    f5 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __ __
  | R_bal_7 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f6 x0 x1 x2 __ __ __ __ x3 x4 x5 x6 __ __ __ x7 x8 x9 x10 __
  | R_bal_8 (x0, x1, x2) -> f7 x0 x1 x2 __ __ __ __
  
  type 'elt coq_R_add =
  | R_add_0 of 'elt tree
  | R_add_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_add_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_add
  | R_add_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_add
  
  (** val coq_R_add_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add
      -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __
      -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 coq_R_add -> 'a2 **)
  
  let rec coq_R_add_rect h x f f0 f1 f2 s t0 = function
  | R_add_0 s0 -> f s0 __
  | R_add_1 (s0, l, y, r0, h0) -> f0 s0 l y r0 h0 __ __
  | R_add_2 (s0, l, y, r0, h0, res, r1) ->
    f1 s0 l y r0 h0 __ __ res r1 (coq_R_add_rect h x f f0 f1 f2 l res r1)
  | R_add_3 (s0, l, y, r0, h0, res, r1) ->
    f2 s0 l y r0 h0 __ __ res r1 (coq_R_add_rect h x f f0 f1 f2 r0 res r1)
  
  (** val coq_R_add_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add
      -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __
      -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 coq_R_add -> 'a2 **)
  
  let rec coq_R_add_rec h x f f0 f1 f2 s t0 = function
  | R_add_0 s0 -> f s0 __
  | R_add_1 (s0, l, y, r0, h0) -> f0 s0 l y r0 h0 __ __
  | R_add_2 (s0, l, y, r0, h0, res, r1) ->
    f1 s0 l y r0 h0 __ __ res r1 (coq_R_add_rec h x f f0 f1 f2 l res r1)
  | R_add_3 (s0, l, y, r0, h0, res, r1) ->
    f2 s0 l y r0 h0 __ __ res r1 (coq_R_add_rec h x f f0 f1 f2 r0 res r1)
  
  type 'elt coq_R_remove_min =
  | R_remove_min_0 of 'elt tree * 'elt * 'elt tree
  | R_remove_min_1 of 'elt tree * 'elt * 'elt tree * 'elt tree * 'elt
     * 'elt tree * z * ('elt tree * 'elt) * 'elt coq_R_remove_min * 'elt tree
     * 'elt
  
  (** val coq_R_remove_min_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      ('a1 tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1 ->
      __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
      coq_R_remove_min -> 'a2 **)
  
  let rec coq_R_remove_min_rect h f f0 l x r p = function
  | R_remove_min_0 (l0, x0, r1) -> f l0 x0 r1 __
  | R_remove_min_1 (l0, x0, r1, ll, lx, lr, _x, res, r2, l', m) ->
    f0 l0 x0 r1 ll lx lr _x __ res r2
      (coq_R_remove_min_rect h f f0 ll lx lr res r2) l' m __
  
  (** val coq_R_remove_min_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1
      tree -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ ->
      ('a1 tree * 'a1) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree -> 'a1 ->
      __ -> 'a2) -> 'a1 tree -> 'a1 -> 'a1 tree -> ('a1 tree * 'a1) -> 'a1
      coq_R_remove_min -> 'a2 **)
  
  let rec coq_R_remove_min_rec h f f0 l x r p = function
  | R_remove_min_0 (l0, x0, r1) -> f l0 x0 r1 __
  | R_remove_min_1 (l0, x0, r1, ll, lx, lr, _x, res, r2, l', m) ->
    f0 l0 x0 r1 ll lx lr _x __ res r2
      (coq_R_remove_min_rec h f f0 ll lx lr res r2) l' m __
  
  type 'elt coq_R_merge =
  | R_merge_0 of 'elt tree * 'elt tree
  | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * 'elt
  
  (** val coq_R_merge_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) ->
      'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)
  
  let coq_R_merge_rect h f f0 f1 s1 s2 t0 = function
  | R_merge_0 (x, x0) -> f x x0 __
  | R_merge_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __
  
  (** val coq_R_merge_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) ->
      'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)
  
  let coq_R_merge_rec h f f0 f1 s1 s2 t0 = function
  | R_merge_0 (x, x0) -> f x x0 __
  | R_merge_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __
  
  type 'elt coq_R_remove =
  | R_remove_0 of 'elt tree
  | R_remove_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_remove_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_remove
  | R_remove_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt coq_R_remove
  
  (** val coq_R_remove_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree
      -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)
  
  let rec coq_R_remove_rect h x f f0 f1 f2 s t0 = function
  | R_remove_0 s0 -> f s0 __
  | R_remove_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_remove_2 (s0, l, y, r0, _x, res, r1) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_remove_rect h x f f0 f1 f2 l res r1)
  | R_remove_3 (s0, l, y, r0, _x, res, r1) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_remove_rect h x f f0 f1 f2 r0 res r1)
  
  (** val coq_R_remove_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree
      -> z -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)
  
  let rec coq_R_remove_rec h x f f0 f1 f2 s t0 = function
  | R_remove_0 s0 -> f s0 __
  | R_remove_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_remove_2 (s0, l, y, r0, _x, res, r1) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_remove_rec h x f f0 f1 f2 l res r1)
  | R_remove_3 (s0, l, y, r0, _x, res, r1) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_remove_rec h x f f0 f1 f2 r0 res r1)
  
  type 'elt coq_R_min_elt =
  | R_min_elt_0 of 'elt tree
  | R_min_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_min_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree
     * 'elt * 'elt tree * z * 'elt option * 'elt coq_R_min_elt
  
  (* (\** val coq_R_min_elt_rect : *)
  (*     'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> *)
  (*     'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> *)
  (*     'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> *)
  (*     'a1 option -> 'a1 coq_R_min_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 *)
  (*     option -> 'a1 coq_R_min_elt -> 'a2 **\) *)
  
  (* let rec coq_R_min_elt_rect h f f0 f1 s o = function *)
  (* | R_min_elt_0 s0 -> f s0 __ *)
  (* | R_min_elt_1 (s0, l, y, _x, _x0) -> f0 s0 l y _x _x0 __ __ *)
  (* | R_min_elt_2 (s0, l, y, _x, _x0, _x1, _x2, _x3, _x4, res, r0) -> *)
  (*   f1 s0 l y _x _x0 __ _x1 _x2 _x3 _x4 __ res r0 *)
  (*     (coq_R_min_elt_rect h f f0 f1 l res r0) *)
  
  (* (\** val coq_R_min_elt_rec : *)
  (*     'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> *)
  (*     'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> *)
  (*     'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> *)
  (*     'a1 option -> 'a1 coq_R_min_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 *)
  (*     option -> 'a1 coq_R_min_elt -> 'a2 **\) *)
  
  (* let rec coq_R_min_elt_rec h f f0 f1 s o = function *)
  (* | R_min_elt_0 s0 -> f s0 __ *)
  (* | R_min_elt_1 (s0, l, y, _x, _x0) -> f0 s0 l y _x _x0 __ __ *)
  (* | R_min_elt_2 (s0, l, y, _x, _x0, _x1, _x2, _x3, _x4, res, r0) -> *)
  (*   f1 s0 l y _x _x0 __ _x1 _x2 _x3 _x4 __ res r0 *)
  (*     (coq_R_min_elt_rec h f f0 f1 l res r0) *)
  
  (* type 'elt coq_R_max_elt = *)
  (* | R_max_elt_0 of 'elt tree *)
  (* | R_max_elt_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z *)
  (* | R_max_elt_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt tree *)
  (*    * 'elt * 'elt tree * z * 'elt option * 'elt coq_R_max_elt *)
  
  (* (\** val coq_R_max_elt_rect : *)
  (*     'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> *)
  (*     'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> *)
  (*     'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> *)
  (*     'a1 option -> 'a1 coq_R_max_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 *)
  (*     option -> 'a1 coq_R_max_elt -> 'a2 **\) *)
  
  (* let rec coq_R_max_elt_rect h f f0 f1 s o = function *)
  (* | R_max_elt_0 s0 -> f s0 __ *)
  (* | R_max_elt_1 (s0, _x, y, r0, _x0) -> f0 s0 _x y r0 _x0 __ __ *)
  (* | R_max_elt_2 (s0, _x, y, r0, _x0, _x1, _x2, _x3, _x4, res, r1) -> *)
  (*   f1 s0 _x y r0 _x0 __ _x1 _x2 _x3 _x4 __ res r1 *)
  (*     (coq_R_max_elt_rect h f f0 f1 r0 res r1) *)
  
  (* (\** val coq_R_max_elt_rec : *)
  (*     'a1 orderedType -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> *)
  (*     'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> *)
  (*     'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> *)
  (*     'a1 option -> 'a1 coq_R_max_elt -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 *)
  (*     option -> 'a1 coq_R_max_elt -> 'a2 **\) *)
  
  (* let rec coq_R_max_elt_rec h f f0 f1 s o = function *)
  (* | R_max_elt_0 s0 -> f s0 __ *)
  (* | R_max_elt_1 (s0, _x, y, r0, _x0) -> f0 s0 _x y r0 _x0 __ __ *)
  (* | R_max_elt_2 (s0, _x, y, r0, _x0, _x1, _x2, _x3, _x4, res, r1) -> *)
  (*   f1 s0 _x y r0 _x0 __ _x1 _x2 _x3 _x4 __ res r1 *)
  (*     (coq_R_max_elt_rec h f f0 f1 r0 res r1) *)
  
  type 'elt coq_R_concat =
  | R_concat_0 of 'elt tree * 'elt tree
  | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * 'elt
  
  (** val coq_R_concat_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) ->
      'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2 **)
  
  let coq_R_concat_rect h f f0 f1 s1 s2 t0 = function
  | R_concat_0 (x, x0) -> f x x0 __
  | R_concat_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __
  
  (** val coq_R_concat_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> __ -> 'a2) ->
      'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2 **)
  
  let coq_R_concat_rec h f f0 f1 s1 s2 t0 = function
  | R_concat_0 (x, x0) -> f x x0 __
  | R_concat_1 (x, x0, x1, x2, x3, x4) -> f0 x x0 x1 x2 x3 x4 __ __
  | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
    f1 x x0 x1 x2 x3 x4 __ x5 x6 x7 x8 __ x9 x10 __
  
  type 'elt coq_R_split =
  | R_split_0 of 'elt tree
  | R_split_1 of 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_split_2 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt triple
     * 'elt coq_R_split * 'elt tree * bool * 'elt tree
  | R_split_3 of 'elt tree * 'elt tree * 'elt * 'elt tree * z * 'elt triple
     * 'elt coq_R_split * 'elt tree * bool * 'elt tree
  
  (** val coq_R_split_rect :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1
      coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple
      -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2)
      -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2 **)
  
  let rec coq_R_split_rect h x f f0 f1 f2 s t0 = function
  | R_split_0 s0 -> f s0 __
  | R_split_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_split_2 (s0, l, y, r0, _x, res, r1, ll, b, rl) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_split_rect h x f f0 f1 f2 l res r1)
      ll b rl __
  | R_split_3 (s0, l, y, r0, _x, res, r1, rl, b, rr) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_split_rect h x f f0 f1 f2 r0 res r1)
      rl b rr __
  
  (** val coq_R_split_rec :
      'a1 orderedType -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple -> 'a1
      coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a1 triple
      -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> bool -> 'a1 tree -> __ -> 'a2)
      -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2 **)
  
  let rec coq_R_split_rec h x f f0 f1 f2 s t0 = function
  | R_split_0 s0 -> f s0 __
  | R_split_1 (s0, l, y, r0, _x) -> f0 s0 l y r0 _x __ __
  | R_split_2 (s0, l, y, r0, _x, res, r1, ll, b, rl) ->
    f1 s0 l y r0 _x __ __ res r1 (coq_R_split_rec h x f f0 f1 f2 l res r1) ll
      b rl __
  | R_split_3 (s0, l, y, r0, _x, res, r1, rl, b, rr) ->
    f2 s0 l y r0 _x __ __ res r1 (coq_R_split_rec h x f f0 f1 f2 r0 res r1)
      rl b rr __
  
  type 'elt coq_R_inter =
  | R_inter_0 of 'elt tree * 'elt tree
  | R_inter_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_inter_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_inter * 'elt tree * 'elt coq_R_inter
  | R_inter_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_inter * 'elt tree * 'elt coq_R_inter
  
  (** val coq_R_inter_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
      coq_R_inter -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter ->
      'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 **)
  
  let rec coq_R_inter_rect h f f0 f1 f2 s1 s2 t0 = function
  | R_inter_0 (s3, s4) -> f s3 s4 __
  | R_inter_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_inter_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_inter_rect h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_inter_rect h f f0 f1 f2 r1 r2' res r2)
  | R_inter_3 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               res0, r0, res, r2) ->
    f2 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_inter_rect h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_inter_rect h f f0 f1 f2 r1 r2' res r2)
  
  (** val coq_R_inter_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> __ -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a1 tree -> 'a1
      coq_R_inter -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_inter ->
      'a2 -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_inter -> 'a2 **)
  
  let rec coq_R_inter_rec h f f0 f1 f2 s1 s2 t0 = function
  | R_inter_0 (s3, s4) -> f s3 s4 __
  | R_inter_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_inter_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_inter_rec h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_inter_rec h f f0 f1 f2 r1 r2' res r2)
  | R_inter_3 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
               res0, r0, res, r2) ->
    f2 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_inter_rec h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_inter_rec h f f0 f1 f2 r1 r2' res r2)
  
  type 'elt coq_R_diff =
  | R_diff_0 of 'elt tree * 'elt tree
  | R_diff_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_diff_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_diff * 'elt tree * 'elt coq_R_diff
  | R_diff_3 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_diff * 'elt tree * 'elt coq_R_diff
  
  (** val coq_R_diff_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> __ -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1
      coq_R_diff -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff ->
      'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 **)
  
  let rec coq_R_diff_rect h f f0 f1 f2 s1 s2 t0 = function
  | R_diff_0 (s3, s4) -> f s3 s4 __
  | R_diff_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_diff_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_diff_rect h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_diff_rect h f f0 f1 f2 r1 r2' res r2)
  | R_diff_3 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              res0, r0, res, r2) ->
    f2 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_diff_rect h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_diff_rect h f f0 f1 f2 r1 r2' res r2)
  
  (** val coq_R_diff_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> __ -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a1 tree -> 'a1
      coq_R_diff -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
      -> 'a1 tree -> z -> __ -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> bool -> 'a1 tree -> __ -> __ -> 'a1 tree -> 'a1 coq_R_diff ->
      'a2 -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_diff -> 'a2 **)
  
  let rec coq_R_diff_rec h f f0 f1 f2 s1 s2 t0 = function
  | R_diff_0 (s3, s4) -> f s3 s4 __
  | R_diff_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_diff_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_diff_rec h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_diff_rec h f f0 f1 f2 r1 r2' res r2)
  | R_diff_3 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', pres, r2',
              res0, r0, res, r2) ->
    f2 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' pres r2' __ __ res0 r0
      (coq_R_diff_rec h f f0 f1 f2 l1 l2' res0 r0) res r2
      (coq_R_diff_rec h f f0 f1 f2 r1 r2' res r2)
  
  type 'elt coq_R_union =
  | R_union_0 of 'elt tree * 'elt tree
  | R_union_1 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * z
  | R_union_2 of 'elt tree * 'elt tree * 'elt tree * 'elt * 'elt tree * 
     z * 'elt tree * 'elt * 'elt tree * z * 'elt tree * bool * 'elt tree
     * 'elt tree * 'elt coq_R_union * 'elt tree * 'elt coq_R_union
  
  (** val coq_R_union_rect :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> 'a1 tree -> 'a1 coq_R_union -> 'a2 -> 'a1 tree -> 'a1 coq_R_union
      -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_union
      -> 'a2 **)
  
  let rec coq_R_union_rect h f f0 f1 s1 s2 t0 = function
  | R_union_0 (s3, s4) -> f s3 s4 __
  | R_union_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_union_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', _x4, r2',
               res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' _x4 r2' __ res0 r0
      (coq_R_union_rect h f f0 f1 l1 l2' res0 r0) res r2
      (coq_R_union_rect h f f0 f1 r1 r2' res r2)
  
  (** val coq_R_union_rec :
      'a1 orderedType -> ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
      'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> __ -> 'a2) ->
      ('a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1
      tree -> 'a1 -> 'a1 tree -> z -> __ -> 'a1 tree -> bool -> 'a1 tree ->
      __ -> 'a1 tree -> 'a1 coq_R_union -> 'a2 -> 'a1 tree -> 'a1 coq_R_union
      -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_union
      -> 'a2 **)
  
  let rec coq_R_union_rec h f f0 f1 s1 s2 t0 = function
  | R_union_0 (s3, s4) -> f s3 s4 __
  | R_union_1 (s3, s4, l1, x1, r1, _x) -> f0 s3 s4 l1 x1 r1 _x __ __
  | R_union_2 (s3, s4, l1, x1, r1, _x, _x0, _x1, _x2, _x3, l2', _x4, r2',
               res0, r0, res, r2) ->
    f1 s3 s4 l1 x1 r1 _x __ _x0 _x1 _x2 _x3 __ l2' _x4 r2' __ res0 r0
      (coq_R_union_rec h f f0 f1 l1 l2' res0 r0) res r2
      (coq_R_union_rec h f f0 f1 r1 r2' res r2)
  
  (** val fold' :
      'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)
  
  let fold' helt f s =
    SetList.fold helt f (elements helt s)
  
  (** val flatten_e : 'a1 orderedType -> 'a1 enumeration -> 'a1 list **)
  
  let rec flatten_e helt = function
  | End -> []
  | More (x, t0, r) -> x :: (app (elements helt t0) (flatten_e helt r))
 end

module S = SetAVL

type 'elt set0 =
  'elt S.tree
  (* singleton inductive, whose constructor was Bst *)

(** val this : 'a1 orderedType -> 'a1 set0 -> 'a1 S.tree **)

let this helt s =
  s

(** val mem0 : 'a1 orderedType -> 'a1 -> 'a1 set0 -> bool **)

let mem0 helt x s =
  S.mem helt x (this helt s)

(** val empty0 : 'a1 orderedType -> 'a1 set0 **)

let empty0 helt =
  S.empty helt

(** val is_empty0 : 'a1 orderedType -> 'a1 set0 -> bool **)

let is_empty0 helt s =
  S.is_empty helt (this helt s)

(** val singleton0 : 'a1 orderedType -> 'a1 -> 'a1 set0 **)

let singleton0 helt x =
  S.singleton helt x

(** val add1 : 'a1 orderedType -> 'a1 -> 'a1 set0 -> 'a1 set0 **)

let add1 helt x s =
  S.add helt x (this helt s)

(** val remove0 : 'a1 orderedType -> 'a1 -> 'a1 set0 -> 'a1 set0 **)

let remove0 helt x s =
  S.remove helt x (this helt s)

(** val inter0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> 'a1 set0 **)

let inter0 helt s s' =
  S.inter helt (this helt s) (this helt s')

(** val union0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> 'a1 set0 **)

let union0 helt s s' =
  S.union helt (this helt s) (this helt s')

(** val diff0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> 'a1 set0 **)

let diff0 helt s s' =
  S.diff helt (this helt s) (this helt s')

(** val elements0 : 'a1 orderedType -> 'a1 set0 -> 'a1 list **)

let elements0 helt s =
  S.elements helt (this helt s)

(** val min_elt0 : 'a1 orderedType -> 'a1 set0 -> 'a1 option **)

let min_elt0 helt s =
  S.min_elt helt (this helt s)

(** val max_elt0 : 'a1 orderedType -> 'a1 set0 -> 'a1 option **)

let max_elt0 helt s =
  S.max_elt helt (this helt s)

(** val choose0 : 'a1 orderedType -> 'a1 set0 -> 'a1 option **)

let choose0 helt s =
  S.choose helt (this helt s)

(** val fold0 :
    'a1 orderedType -> ('a1 -> 'a2 -> 'a2) -> 'a1 set0 -> 'a2 -> 'a2 **)

let fold0 helt f s x =
  S.fold helt f (this helt s) x

(** val cardinal0 : 'a1 orderedType -> 'a1 set0 -> nat **)

let cardinal0 helt s =
  S.cardinal helt (this helt s)

(** val filter0 :
    'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> 'a1 set0 **)

let filter0 helt f s =
  S.filter helt f (this helt s)

(** val for_all0 : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> bool **)

let for_all0 helt f s =
  S.for_all helt f (this helt s)

(** val exists_0 : 'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> bool **)

let exists_0 helt f s =
  S.exists_ helt f (this helt s)

(** val partition0 :
    'a1 orderedType -> ('a1 -> bool) -> 'a1 set0 -> 'a1 set0 * 'a1 set0 **)

let partition0 helt f s =
  let p = S.partition helt f (this helt s) in ((fst p), (snd p))

(** val equal0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> bool **)

let equal0 helt s s' =
  S.equal helt (this helt s) (this helt s')

(** val subset0 : 'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> bool **)

let subset0 helt s s' =
  S.subset helt (this helt s) (this helt s')

(** val set_compare0 :
    'a1 orderedType -> 'a1 set0 -> 'a1 set0 -> comparison **)

let set_compare0 h s1 s2 =
  S.compare h (this h s1) (this h s2)

(** val set_OrderedType0 :
    'a1 orderedType -> 'a1 set0 specificOrderedType **)

let set_OrderedType0 h =
  set_compare0 h

(** val setAVL_FSet : 'a1 orderedType -> 'a1 fSet **)

let setAVL_FSet helt =
  { empty = (Obj.magic (empty0 helt)); is_empty =
    (Obj.magic (is_empty0 helt)); mem = (Obj.magic (mem0 helt)); add0 =
    (Obj.magic (add1 helt)); singleton = (Obj.magic (singleton0 helt));
    remove = (Obj.magic (remove0 helt)); union = (Obj.magic (union0 helt));
    inter = (Obj.magic (inter0 helt)); diff = (Obj.magic (diff0 helt));
    equal = (Obj.magic (equal0 helt)); subset = (Obj.magic (subset0 helt));
    fold = (Obj.magic (fun _ -> fold0 helt)); for_all =
    (Obj.magic (for_all0 helt)); exists_ = (Obj.magic (exists_0 helt));
    filter = (Obj.magic (filter0 helt)); partition =
    (Obj.magic (partition0 helt)); cardinal = (Obj.magic (cardinal0 helt));
    elements = (Obj.magic (elements0 helt)); choose =
    (Obj.magic (choose0 helt)); min_elt = (Obj.magic (min_elt0 helt));
    max_elt = (Obj.magic (max_elt0 helt)); fSet_OrderedType =
    (Obj.magic (set_OrderedType0 helt)) }

(** val map0 :
    'a1 orderedType -> 'a2 orderedType -> ('a1 -> 'a2) -> 'a1 set -> 'a2 set **)

let map0 hA hB f s =
  fold hA (setAVL_FSet hA) (fun a acc -> (setAVL_FSet hB).add0 (f a) acc) s
    (setAVL_FSet hB).empty

(** val zOrd : z orderedType **)

let zOrd =
  sOT_as_OT z_OrderedType

type word = z list

type re =
| Re0
| Re1
| Re_sy of z
| Re_union of re * re
| Re_conc of re * re
| Re_star of re

(** val c_of_re : re -> bool **)

let rec c_of_re = function
| Re1 -> true
| Re_union (x, y) -> (||) (c_of_re x) (c_of_re y)
| Re_conc (x, y) -> (&&) (c_of_re x) (c_of_re y)
| Re_star r0 -> true
| _ -> false

(** val re_cmp : re -> re -> comparison **)

let rec re_cmp x y =
  match x with
  | Re0 ->
    (match y with
     | Re0 -> Eq
     | _ -> Lt)
  | Re1 ->
    (match y with
     | Re0 -> Gt
     | Re1 -> Eq
     | _ -> Lt)
  | Re_sy x1 ->
    (match y with
     | Re0 -> Gt
     | Re1 -> Gt
     | Re_sy y1 -> compare0 zOrd x1 y1
     | _ -> Lt)
  | Re_union (x1, x2) ->
    (match y with
     | Re_union (y1, y2) ->
       (match re_cmp x1 y1 with
        | Eq -> re_cmp x2 y2
        | x0 -> x0)
     | Re_conc (r, r0) -> Lt
     | Re_star r -> Lt
     | _ -> Gt)
  | Re_conc (x1, x2) ->
    (match y with
     | Re_conc (y1, y2) ->
       (match re_cmp x1 y1 with
        | Eq -> re_cmp x2 y2
        | x0 -> x0)
     | Re_star r -> Lt
     | _ -> Gt)
  | Re_star x1 ->
    (match y with
     | Re_star y1 -> re_cmp x1 y1
     | _ -> Gt)

(** val re_ord : re orderedType **)

let re_ord =
  re_cmp

(** val c_of_re_set : re set -> bool **)

let c_of_re_set s =
  fold re_ord (setAVL_FSet re_ord) (fun x -> (||) (c_of_re x)) s false

(** val fold_conc : re set -> re -> re set **)

let fold_conc s r =
  map0 re_ord re_ord (fun x -> Re_conc (x, r)) s

(** val dsr : re set -> re -> re set **)

let dsr s r = match r with
| Re0 -> (setAVL_FSet re_ord).empty
| Re1 -> s
| _ -> fold_conc s r

(** val pdrv : re -> z -> re set **)

let rec pdrv r s =
  match r with
  | Re_sy s' ->
    (match compare0 zOrd s' s with
     | Eq -> (setAVL_FSet re_ord).singleton Re1
     | _ -> (setAVL_FSet re_ord).empty)
  | Re_union (x, y) -> (setAVL_FSet re_ord).union (pdrv x s) (pdrv y s)
  | Re_conc (x, y) ->
    if c_of_re x
    then (setAVL_FSet re_ord).union (dsr (pdrv x s) y) (pdrv y s)
    else dsr (pdrv x s) y
  | Re_star x -> dsr (pdrv x s) (Re_star x)
  | _ -> (setAVL_FSet re_ord).empty

(** val pdrv_set : re set -> z -> re set **)

let pdrv_set sre s =
  fold re_ord (setAVL_FSet re_ord) (fun x ->
    (setAVL_FSet re_ord).union (pdrv x s)) sre (setAVL_FSet re_ord).empty

(** val ss : re -> z set **)

let rec ss = function
| Re_sy a -> (setAVL_FSet zOrd).singleton a
| Re_union (z0, t0) -> (setAVL_FSet zOrd).union (ss z0) (ss t0)
| Re_conc (z0, t0) -> (setAVL_FSet zOrd).union (ss z0) (ss t0)
| Re_star z0 -> ss z0
| _ -> (setAVL_FSet zOrd).empty

(** val pdrvp : (re set * re set) -> z -> re set * re set **)

let pdrvp x a =
  ((pdrv_set (fst x) a), (pdrv_set (snd x) a))

type reW = { dp : (re set * re set); w : word }

(** val dp : re -> re -> reW -> re set * re set **)

let dp _ _ x = x.dp

(** val reW_1st : re -> re -> reW **)

let reW_1st r1 r2 =
  { dp = (((setAVL_FSet re_ord).singleton r1),
    ((setAVL_FSet re_ord).singleton r2)); w = [] }

(** val reW_ord : re -> re -> reW orderedType **)

let reW_ord r1 r2 x x0 =
  _cmp
    (prod_OrderedType (sOT_as_OT (setAVL_FSet re_ord).fSet_OrderedType)
      (sOT_as_OT (setAVL_FSet re_ord).fSet_OrderedType)) x.dp x0.dp

(** val reW_pdrv : re -> re -> reW -> z -> reW **)

let reW_pdrv r1 r2 x a =
  let { dp = k; w = w0 } = x in { dp = (pdrvp k a); w = (app w0 (a :: [])) }

(** val reW_pdrv_set : re -> re -> reW -> z set -> reW set **)

let reW_pdrv_set r1 r2 s sig1 =
  fold zOrd (setAVL_FSet zOrd) (fun x ->
    (setAVL_FSet (reW_ord r1 r2)).add0 (reW_pdrv r1 r2 s x)) sig1
    (setAVL_FSet (reW_ord r1 r2)).empty

(** val reW_pdrv_set_filtered :
    re -> re -> reW -> reW set -> z set -> reW set **)

let reW_pdrv_set_filtered r1 r2 x h sig1 =
  (setAVL_FSet (reW_ord r1 r2)).filter (fun x0 ->
    negb ((setAVL_FSet (reW_ord r1 r2)).mem x0 h))
    (reW_pdrv_set r1 r2 x sig1)

(** val c_of_rep : (re set * re set) -> bool **)

let c_of_rep x =
  eqb (c_of_re_set (fst x)) (c_of_re_set (snd x))

(** val c_of_ReW : re -> re -> reW -> bool **)

let c_of_ReW r1 r2 x =
  c_of_rep x.dp

type stepFastCase' =
| Process'
| TermTrue' of reW set
| TermFalse' of reW

(** val stepFast' :
    re -> re -> reW set -> reW set -> z set -> (reW set * reW
    set) * stepFastCase' **)

let stepFast' r1 r2 h s sig1 =
  match (setAVL_FSet (reW_ord r1 r2)).choose s with
  | Some x ->
    if c_of_ReW r1 r2 x
    then let h' = (setAVL_FSet (reW_ord r1 r2)).add0 x h in
         let s' = (setAVL_FSet (reW_ord r1 r2)).remove x s in
         let ns = reW_pdrv_set_filtered r1 r2 x h' sig1 in
         ((h', ((setAVL_FSet (reW_ord r1 r2)).union ns s')), Process')
    else ((h, s), (TermFalse' x))
  | None -> ((h, s), (TermTrue' h))

type lastCases =
| Ok of reW set
| NotOk of reW

(** val decide_re_ref' :
    re -> re -> reW set -> reW set -> z set -> lastCases **)

let rec decide_re_ref' r1 r2 x x0 x1 =
  match snd (stepFast' r1 r2 x x0 x1) with
  | Process' ->
    decide_re_ref' r1 r2 (fst (fst (stepFast' r1 r2 x x0 x1)))
      (snd (fst (stepFast' r1 r2 x x0 x1))) x1
  | TermTrue' h1 -> Ok h1
  | TermFalse' x2 -> NotOk x2

(** val equiv_re_ref_aux' :
    re -> re -> reW set -> reW set -> z set -> bool **)

let equiv_re_ref_aux' r1 r2 h s sig1 =
  let h0 = decide_re_ref' r1 r2 h s sig1 in
  (match h0 with
   | Ok s0 -> true
   | NotOk r -> false)

(** val equiv_re_ref' : re -> re -> z set -> bool **)

let equiv_re_ref' r1 r2 sig1 =
  equiv_re_ref_aux' r1 r2 (setAVL_FSet (reW_ord r1 r2)).empty
    ((setAVL_FSet (reW_ord r1 r2)).singleton (reW_1st r1 r2)) sig1

(** val equivP : re -> re -> bool **)

let equivP r1 r2 =
  equiv_re_ref' r1 r2 ((setAVL_FSet zOrd).union (ss r1) (ss r2))

(** ---- End extracted code ----- *)

open Tacmach
open Tacticals
open Tacexpr
open Tacinterp

(* A clause specifying that the [let] should not try to fold anything the goal
   matching the list of constructors (see [letin_tac] below). *)

let nowhere = { onhyps = Some []; concl_occs = Glob_term.no_occurrences_expr }

let zconv z =
  let mk_coq_xI = !!Coq_lib.Positive.coq_xI in
  let mk_coq_xO = !!Coq_lib.Positive.coq_xO in
  let mk_coq_zpos = !!Coq_lib.Z.zpos in
  let mk_coq_zneg = !!Coq_lib.Z.zneg in
  let rec posconv x =
    match (CU.cdecomp x) with
      | App(fx,argsx) when eq_constr fx mk_coq_xO = true -> XO (posconv (argsx.(0)))
      | App(fx,argsx) when eq_constr fx mk_coq_xI = true -> XI (posconv (argsx.(0)))
      | _ -> XH
  in
  let zconv_top x =
    match (CU.cdecomp x) with
    | App(fx,argsx) when eq_constr fx mk_coq_zpos = true -> Zpos (posconv (argsx.(0)))
    | App(fx,argsx) when eq_constr fx mk_coq_zneg = true -> Zneg (posconv (argsx.(0)))
    | _ -> Z0
  in zconv_top z

let rec re_conv x =
  match x with
  |Res.Re0c -> Re0
  |Res.Re1c -> Re1
  |Res.Resyc v -> Re_sy (zconv (snd v))
  |Res.RePc (x1,x2) -> Re_union (re_conv x1,re_conv x2)
  |Res.ReCc (x1,x2) -> Re_conc (re_conv x1,re_conv x2)
  |Res.ReSc x1 -> Re_star (re_conv x1)

let dec x y =
  equivP (re_conv x) (re_conv y)

let tac_re : Proof_type.tactic =
  fun goal ->
    (** Force values once and for all. *)
    let mk_coq_langeq = !!Lang.coq_lang_eq in 
    let mk_coq_re0 = !!Res.coq_re0 in 
    let mk_coq_re1 = !!Res.coq_re1 in 
    let mk_coq_resy = !!Res.coq_resy in 
    let mk_coq_replus = !!Res.coq_replus in 
    let mk_coq_reconc = !!Res.coq_reconc in 
    let mk_coq_restar = !!Res.coq_restar in 
    let mk_coq_re2rel = !!Res.coq_re2rel in
    (** Reify a regular expression into our inner datatype for regular expressions *)
    let rec reify r =
      match CU.cdecomp r with
      | Construct c when eq_constructor c (destConstruct mk_coq_re0) = true ->
	Res.Re0c
      | Construct c when eq_constructor c (destConstruct mk_coq_re1) = true ->
	Res.Re1c
      | Term.App(s,a) when eq_constr s mk_coq_resy = true -> Res.Resyc (0,(a.(0)))
      | Term.App(s,a) when eq_constr s mk_coq_replus = true ->
	let x1 = reify (a.(0)) in let x2 = reify (a.(1)) in Res.RePc (x1,x2)
      | Term.App(s,a) when eq_constr s mk_coq_reconc = true ->
	let x1 = reify (a.(0)) in let x2 = reify (a.(1)) in Res.ReCc (x1,x2)
      | Term.App(s,a) when eq_constr s mk_coq_restar = true ->
	let x1 = reify (a.(0)) in Res.ReSc x1
      | _ -> Printf.kprintf Util.error "something wrong in type reification!!!"
    in
    let concl = Tacmach.pf_concl goal in
    match CU.cdecomp concl with
      | App(c, args) when Array.length args >= 2 && eq_constr c mk_coq_langeq = true ->
	begin
      	  match CU.cdecomp (args.(0)) , CU.cdecomp (args.(1)) with
	  | App(fl,argsl),App(fr,argsr) when eq_constr fl mk_coq_re2rel = true && eq_constr fr mk_coq_re2rel = true -> 
	    begin
	      let il = reify argsl.(0) in
	      let ir = reify argsr.(0) in
	      if dec il ir then
		begin
		  Pp.message "expressões regulares equivalentes" ; Tactics.admit_as_an_axiom goal
		end
	      else 
		begin
		  Tacticals.tclFAIL 1 (Pp.str "expressões regulares não equivalentes") goal
		end
	    end
	  |  _ , _ -> 
	    Tacticals.tclFAIL 1 (Pp.str "The arguments must still be reified into regular expressions") goal
	end
      | _ -> Tacticals.tclFAIL 1 (Pp.str "The goal does not look like a language equivalence") goal

let tac_rel_aux x goal =
  tclTHENLIST [Tactics.change_in_concl None x] goal

let tac_rel : Proof_type.tactic =
  fun goal -> 
  (* Force the constructions over relations *)
    let mk_coq_eq_rel = !!ReifMap.coq_eq_rel in
    let concl = pf_concl goal in
    match CU.cdecomp concl with
    | App(head,args) when eq_constr head mk_coq_eq_rel && Array.length args = 3 ->
      begin
	(* Type where relations are defined over *)
	let tp = args.(0) in 
	(* Initialize reification table. *)
	let reif_env = Coq_lib.ReifEnv.empty () in
	(* let m = Coq_lib.ReifMap.mk_map e t in *)
	(* let f = mk_coq_f t m in *)
	let k = ReifMap.mk_rel_reif tp reif_env args.(1) args.(2) in 
	Tactics.change_in_concl None k goal
      end 
    | _ -> tclFAIL 1 (Pp.str "The goal is not an equation on relations!") goal
    

TACTIC EXTEND _reflect2_
| ["check_re"] -> [tac_re]    
END;;

TACTIC EXTEND _rel_refl_
| ["rel2re_eq"] -> [tac_rel]
END;;
