(*Add Rec LoadPath "/Users/dpereira/Source/Containers/theories" as Containers.
Add ML Path "/Users/dpereira/Source/Containers/src".*)

Require Export base. (*Ensembles Recdef Omega.*)
(*Require Export Sets SetInterface SetProperties SetConstructs OrderedTypeEx Generate.*)

(* Generalizable All Variables.*)


(** * Parametrisation of the number of Boolean tests *)

Module Type KAT_Alph.
  
  Parameter ntests : nat.

End KAT_Alph.
