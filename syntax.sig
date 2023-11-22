ty : Type

Fun : ty -> ty -> ty
Nat : ty

tm : Type

Lam : ty -> (tm -> tm) -> tm
App : tm -> tm -> tm
Zero : tm
Succ : tm -> tm
Rec : tm -> tm -> (tm -> tm -> tm) -> tm