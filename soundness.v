Require Import semantics typing.

Theorem fundamental_theorem {n} (Γ : context n) a A :
  Γ ⊢ a ∈ A ->
  Γ ⊨ a ∼ a ∈ A.
Proof. induction 1; eauto using ST_Var, ST_Lam, ST_App, ST_Zero, ST_Succ, ST_Rec. Qed.
