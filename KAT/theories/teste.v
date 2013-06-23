Require Export kat_alph atoms gl kat kat_pdrvs wf_extra symbs kat_dec.

Module ExAlph.
  Definition ntests := 2.
End ExAlph.

Module teste1 := KATDec(ExAlph).
Export teste1.

Definition b := baV (Ord ntests 0 (refl_equal (ltb 0 (ntests)))).
Definition c := baV (Ord (ntests) 1 (refl_equal (ltb 1 (ntests)))).

(** Example 30 *)
Definition loop1 := (([b]?*`1)+[!b]?)*((([b]?*(([b]?*`1)+[!b]?)))#)*([!b]?).
Definition loop2 := ([b]?*`1)#*([!b]?).

Goal loop1 == loop2.
Time dec_re.
Qed.


(** Example 31 *)
Definition loop3 := ([b]?*`1)#*[!b]?.
Definition loop4 := (([b]?*`1)*([b]?*`1 + [!b]?))#*[!b]?.

Goal loop3 == loop4.
Time dec_re.
Qed.

(** Example 32 *)
Definition kat1 := ([b]?*[c]? + [!b]?*[!c]?)*(([b]?*`1*`2) + ([!b]?*`1*`3)).
Definition kat2 := ([b]?*[c]? + [!b]?*[!c]?)*(([c]?*`1*`2) + ([!c]?*`1*`3)).

Goal kat1 == kat2.
Time dec_re.
Qed.

(** Example 33 *)
Definition kat3 := ([b]?*`1*(([c]?*`2)#*[!c]?))#*[!b]?.
Definition kat4 := [b]?*`1*(([b]?+[c]?)*(([c]?*`2) + ([!c]?*`1)))#*[!(b `+ c)]? + [!b]?.

Goal kat3 == kat4.
Time dec_re.
Qed.