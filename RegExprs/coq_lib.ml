open Term
open Names
open Declarations
open Proof_type
(*open Extr*)

(** access to Coq constants *)
let get_const dir s = 
  lazy (Libnames.constr_of_global (Coqlib.find_reference "pdcoq" dir s))

(** Force the lazy construct to produce the actual value *)
let (!!) r =  Lazy.force r

(** * Utilities for manipulating and priting information about inductive *)
module CU =
struct
  (** Get string info from an inductive : name + number of args *)
  let get_ind_info ind =
    "The inductive "^string_of_mind (fst ind)^" has "^string_of_int (snd ind)^" args"
  (** Prepare a constructor for being pattern matched *)
  let cdecomp (c : Term.constr)  = 
    Term.kind_of_term (Term.strip_outer_cast c)
end

module Positive =
struct
  let path = ["Coq";"Numbers";"BinNums"]
  (* Integer : first comes the positive definitions *)
  let coq_pos = get_const path "positive"
  let coq_xI = get_const path "xI"
  let coq_xO = get_const path "xO"
  let coq_xH = get_const path "xH"
  (* Ocaml [int] to Coq [positive] *)
  let int2pos n =
    let rec aux n =
      begin  match n with
      | n when n < 1 -> assert false
      | 1 -> !!coq_xH
      | n -> mkApp
        (
          (if n mod 2 = 0
           then !!coq_xO
           else !!coq_xI
          ),  [| aux (n/2)|]
        )
      end
    in aux n
end

(** Access to integer numbers, i.e., Coq's [Z] type. *)
module Z =
struct
  let path = ["Coq";"Numbers";"BinNums"]
  (* Second, we obtain the full interegers *)
  let z = get_const path "Z"
  let z0 = get_const path "Z0"
  let zpos = get_const path "Zpos"
  let zneg = get_const path "Zneg"
  (* Ocaml [int] to Coq [Z] *)
  let int2Z n =
    if n < 0
    then mkApp(!!zneg,[|Positive.int2pos (-1*n)|])
    else
      if n = 0
      then mkApp(!!z0,[||])
      else mkApp(!!zpos,[|Positive.int2pos n|])
end

(** Access the type of languages. *)

module Lang =
struct
  let path = ["PDCoq";"language"]
  (* Type of languages *)
  let coq_lang = get_const path "language"
  (* Language equivalence *)
  let coq_lang_eq = get_const path "leq"
end

(** Access the type of regular expressions. *)

module Res =
struct
  (* My re type *)
  let cpath = ["PDCoq";"reg_expr"]
  let coq_re = get_const cpath "re"
  let coq_re0 = get_const cpath "re0"
  let coq_re1 = get_const cpath "re1"
  let coq_resy = get_const cpath "re_sy"
  let coq_replus = get_const cpath "re_union"
  let coq_reconc = get_const cpath "re_conc"
  let coq_restar = get_const cpath "re_star"
  let coq_re2rel = get_const cpath "re2rel"
  (* Our inner type of regular expressions. *)
  type mre =
  | Re0c
  | Re1c
  | Resyc of (int*Term.constr)
  | RePc of (mre*mre)
  | ReCc of (mre*mre)
  | ReSc of mre
  (* Debug function -- to remove once done!!! *)
  let rec mre2str r =
    match r with
    | Re0c -> "0"
    | Re1c -> "1"
    | Resyc v -> string_of_int (fst v)
    | RePc (r1,r2) -> "("^mre2str r1^" + "^mre2str r2^")"
    | ReCc (r1,r2) -> "("^mre2str r1^" * "^mre2str r2^")"
    | ReSc r1 -> "("^mre2str r1^")"
end 

module ReifEnv =
struct
  (* Structure holding the hash of terms *)
  module ConstrHashed = struct
    type t = Term.constr
    let equal = Term.eq_constr
    let hash = Term.hash_constr
  end
  (* Build the hashtable structure using the above pairs. *)
  module ConstrHashtbl = Hashtbl.Make (ConstrHashed)
    (* Type of the hashed elements : (integer,construction) *)
  type t = (int ConstrHashtbl.t * int ref)
  (* Add a new element to the hashtble. It checks for already existing ones. *)
  let add (env : t) (t : Term.constr ) =
    try ConstrHashtbl.find (fst env) t 
    with
      | Not_found -> 
	let i = !(snd env) in 
	ConstrHashtbl.add (fst env) t i ; incr (snd env); i
  (* Build  a new hashtable *)
  let empty () = (ConstrHashtbl.create 20, ref 0)
  
end

module Rels =
struct
  let path = ["PDCoq";"relational_interpretation"]
  (* Terms for relations *)
  let coq_rel_t = get_const path "relation"
  let coq_emp_rel = get_const path "EmpRel"
  let coq_id_rel = get_const path "IdRel"
  let coq_union_rel = get_const path "UnionRel"
  let coq_comp_rel = get_const path "CompRel"
  let coq_refl_trans_rel = get_const path "trans_refl"
  (* Abstract type for representing relations *)
  type abs_rel =
  | RelEmp
  | RelId
  | RelOp of (int*Term.constr)
  | RelU of (abs_rel*abs_rel)
  | RelC of (abs_rel*abs_rel)
  | RelRT of (abs_rel)
  (* Reifies a relation into the corresponding regular expression *)
  let reif_rel env c =
    let mk_coq_emp_rel = !!coq_emp_rel in
    let mk_coq_id_rel = !!coq_id_rel in
    let mk_coq_union_rel = !!coq_union_rel in
    let mk_coq_comp_rel = !!coq_comp_rel in
    let mk_coq_refl_trans_rel = !!coq_refl_trans_rel in
    let rec reifRel e r =
      match CU.cdecomp r with
      | App(head,args) when eq_constr head mk_coq_union_rel && Array.length args = 3 ->
	Res.RePc (reifRel e args.(1),reifRel e args.(2))
      | App(head,args) when eq_constr head mk_coq_comp_rel && Array.length args = 3 ->
	Res.ReCc (reifRel e args.(1),reifRel e args.(2))
      | App(head,args) when eq_constr head mk_coq_refl_trans_rel && Array.length args = 2 ->
	Res.ReSc (reifRel e args.(1))
      | App(head,args) when eq_constr head mk_coq_emp_rel && Array.length args = 2 ->
	Res.Re0c
      | App(head,args) when eq_constr head mk_coq_id_rel && Array.length args = 2 ->
	Res.Re1c
      | Var x -> let a = ReifEnv.add e r in Res.Resyc (a,Z.int2Z a)
      | _ -> Printf.kprintf Util.error "something wrong in type reification!!!"
    in reifRel env c
  
end

module ReifMap =
struct
  let path = ["PDCoq";"relational_interpretation"]
  (* Access functions to build the reification map. *)
  let coq_emp_mm = get_const path "emp_m"
  let coq_add_mm = get_const path "add_mm"
  let coq_find_mm = get_const path "find_mm"
  let coq_f = get_const path "f"
  let coq_eq_rel = get_const path "rel_eq"
  let coq_reRel = get_const path "reRel"
  (* Build an Coq [re] from a regular expression reified into a term [Res.rem]. *)
  let rec re2rel r =
    match r with
    | Res.Re0c -> !!Res.coq_re0
    | Res.Re1c -> !!Res.coq_re1
    | Res.Resyc v -> mkApp(!!Res.coq_resy,[|snd v|])
    | Res.RePc (r1,r2) -> mkApp(!!Res.coq_replus,[|re2rel r1 ; re2rel r2|])
    | Res.ReCc (r1,r2) -> mkApp(!!Res.coq_reconc,[|re2rel r1 ; re2rel r2|])
    | Res.ReSc r1 -> mkApp(!!Res.coq_restar,[|re2rel r1|])
  (* Build a reification map : will be used to build the final reified term [x:re] representing
     a relation (re2Rel T f x) *)
  let mk_coq_f t m =
    mkApp(!!coq_f,[|t;m|])
  let mk_coq_add t x y acc =
    mkApp(!!coq_add_mm,[|t;x;y;acc|])
  let mk_coq_emp t =
    mkApp(!!coq_emp_mm,[|t|])
  (* Build the reification map environment *)
  let mk_map (e:ReifEnv.t) t =
    ReifEnv.ConstrHashtbl.fold (fun constr key acc -> mk_coq_add t (Z.int2Z key) constr acc)
      (fst e) (mk_coq_emp t)
  (* Now with the reification map, we can build the arguments of the relational equation. *)
  let mk_rel_reif t e rel1 rel2 =
    let rel1re = Rels.reif_rel e rel1 in
    let rel2re = Rels.reif_rel e rel2 in
    let m = mk_map e t in
    let f = mk_coq_f t m in
    let dbg_1 = Res.mre2str rel1re in
    let dbg_2 = Res.mre2str rel2re in
    let re_rel_1 = re2rel rel1re in
    let re_rel_2 = re2rel rel2re in
    let fre1rel = mkApp(!!coq_reRel,[|t;f;re_rel_1|]) in
    let fre2rel = mkApp(!!coq_reRel,[|t;f;re_rel_2|]) in
    mkApp(!!coq_eq_rel,[|t;fre1rel;fre2rel|])
end



