Require Export kat_alph atoms gl kat kat_pdrvs wf_extra symbs kat_dec.

Module PHL1.
  Module ExAlph.
    Definition ntests := 4.
  End ExAlph.
  
  Module teste1 := KATDec(ExAlph).
  Export teste1.
  
  Definition t0 := baV (Ord (ntests) 0 (refl_equal (ltb 0 (ntests)))).
  Definition t1 := baV (Ord (ntests) 1 (refl_equal (ltb 1 (ntests)))).
  Definition t2 := baV (Ord (ntests) 2 (refl_equal (ltb 2 (ntests)))).
  Definition t3 := baV (Ord (ntests) 3 (refl_equal (ltb 3 (ntests)))).
  
  Definition u := (`1 + `2)#.
  Definition r := ([t0]?*[!t1]? + [t1]?*`1*[!t2]? + [t2]?*`2*[!t3]?)#.
  Definition p := [t0]?*[t3]?*`1*[t1]?*`2*[!t2]?.
                                                
  Goal p + u*r*u == [ba0]? + u*r*u.
  Time dec_re.
  Qed.
End PHL1.

Module PHL2.
  Module ExAlph.
    Definition ntests := 6.
  End ExAlph.

  Module teste := KATDec(ExAlph).
  Export teste.

  Definition t0 := baV (Ord (ntests) 0 (refl_equal (ltb 0 (ntests)))).
  Definition t1 := baV (Ord (ntests) 1 (refl_equal (ltb 1 (ntests)))).
  Definition t2 := baV (Ord (ntests) 2 (refl_equal (ltb 2 (ntests)))).
  Definition t3 := baV (Ord (ntests) 3 (refl_equal (ltb 3 (ntests)))).
  Definition t4 := baV (Ord (ntests) 4 (refl_equal (ltb 4 (ntests)))).
  Definition t5 := baV (Ord (ntests) 5 (refl_equal (ltb 5 (ntests)))).

  Definition u := (`1 + `2 + `3 + `4)#.
  Definition r := ([t0]?*`1*[!t1]? + [t1]?*`2*[!t2]? + [t3]?*[t2]?*`3*[!t4]? + [t4]?*`2*[!t2]?
                   + [t2]?*[!t3]?*[!t5]?)#.         
  Definition p := [t0]?*`1*[t1]?*`2*[t2]?*([t3]?*[t2]?*`3*[t4]?*`4)#*[!(t3 `+ t5)]?.

  Goal p + u*r*u == [ba0]? + u*r*u.
  Time dec_re.
  Qed.
End PHL2.