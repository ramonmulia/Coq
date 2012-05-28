Require Export Types.

Inductive conf : Type :=
  | conf_trust : conf
  | conf_ditrust : conf
  | conf_dontcare : conf. 

Inductive ty : Type := 
  | ty_Bool  : ty -> conf -> ty
  | ty_arrow : ty -> ty -> conf -> ty.

Inductive tm : Type :=
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm
  | tm_trust : tm -> tm
  | tm_distrust : tm -> tm
  | tm_check :  tm -> tm 
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tm_abs x T t)
  | t_true : 
      value tm_true
  | t_false : 
      value tm_false.

Fixpoint subst (s:tm) (x:id) (t:tm): tm :=
  match t with
  | tm_var x' => if beq_id x x' then s else t
  | tm_abs x' T t1 => tm_abs x' T (if beq_id x x' then t1 else (subst s x t1)) 
  | tm_app t1 t2 => tm_app (subst s x t1) (subst s x t2)
  | tm_trust t1 => tm_trust (subst s x t1 )
  | tm_distrust t1  => tm_distrust (subst s x t1 ) 
  | tm_check t1  => tm_check (subst s x t1 )
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst s x t1) (subst s x t2) (subst s x t3)
  end.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tm_app (tm_abs x T t12) v2) ==> (subst v2 x t12)
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tm_app t1 t2 ==> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tm_app v1 t2 ==> tm_app v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tm_if tm_true t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tm_if tm_false t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
  | ST_Trust : forall t1 t1',
     t1 ==> t1' ->
     tm_trust t1 ==> tm_trust t1'
  | ST_Distrust : forall t t', 
     t ==> t' ->
     tm_distrust t ==> tm_distrust t'
  | ST_Check : forall t t',
    t ==> t' ->
    tm_check t ==> tm_check t'
  | ST_TrustV : forall  t,
    value t ->
    tm_trust t ==> t
  | ST_DistrustV : forall t,
    value t ->
    tm_distrust t ==> t
   | ST_CheckV : forall t,
    value t -> 
    tm_check t ==> t
     

where "t1 '==>' t2" := (step t1 t2).

Lemma value_not_eval: forall (t:tm),
     value t ->
     ~ exists t', t ==> t'.
Proof.
Admitted.


Theorem det_sem : forall t t' t'',
    t ==> t' ->
    t ==> t'' ->
    t' = t''.
Proof.
Admitted.







