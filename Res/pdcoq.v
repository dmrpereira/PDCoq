Add LoadPath "../src".
Require Import Plug.


Goal 1=1.
Set Ltac Debug.
tester.
mytac.
Show Proof.

Module DecideRes.
  Require Export decide.
End DecideRes.

Module DecideRels.
  Require Export relational_interpretation.
End.

