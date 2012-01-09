
                                               (* DAYS WEEK *)

Inductive day : Type :=
 | monday : day
 | tuesday : day
 | wednesday : day
 | thursday : day
 | friday : day
 | saturday : day
 | sunday : day.

Definition next_weekday (d:day) : day :=
 match d with
 | monday => tuesday
 | tuesday => wednesday
 | wednesday => thursday
 | thursday => friday
 | friday => monday
 | saturday => monday
 | sunday => monday
 end.


Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
 (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive nota : Type :=
 | do : nota
 | re : nota
 | mi : nota
 | fa : nota
 | sol : nota
 | la : nota
 | si : nota.
Definition prox_nota (n:nota) : nota :=
 match n with
 | do => re
 | re => mi
 | mi => fa
 | fa => sol
 | sol => la
 | la => si
 | si => do
end.

Eval simpl in (prox_nota si).

Example test_prox_nota:
 (prox_nota (prox_nota (prox_nota re))) = sol.

Proof. simpl. reflexivity. Qed.


Module Playground1.

Inductive nat : Type :=
 | O : nat
 | S : nat -> nat.

Definition pred (n : nat) : nat :=
 match n with
 | O => O
 | S nn => nn
end.

End Playground1.

Definition minustwo (n : nat) : nat :=
 match n with
 | O => O
 | S O => O
 | S (S nn) => nn
end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Check S.
Check pred.
Check minustwo.
Check pred 5.

Inductive bool : Type :=
 | true : bool
 | false : bool.


Definition negb (nb : bool) : bool :=
 match nb with
 | true => false
 | false => true
end.

Fixpoint evenb (n:nat) : bool :=
 match n with
 | O => true
 | S O => false
 | S (S nn) => evenb nn
end.

Check evenb.

Example pair: (evenb 5) = false.
Proof. simpl. reflexivity. Qed.

Example pair2: (evenb 6) = true.
Proof. simpl. reflexivity. Qed.

Definition oddb (n:nat) : bool := 
 negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.



                                              (* BOOL AND FUNC TYPES *)







Definition andb (ab1 : bool) (ab2 : bool) : bool :=
 match ab1 with
 | true => ab2
 | false => false
end.


Definition orb (ob1 : bool) (ob2 : bool) : bool :=
 match ob1 with
 | true => true
 | false => ob2
end.

Example t_orb: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example t_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example t_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example t_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
 match b1 with
 | true => (negb b2)
 | false => true
end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
Example t_nandb: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
 match b1 with
 | false => false
 | true => (andb b2 b3)
end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check (negb true).
(* ===> negb true : bool *)

Check negb.
(* ===> negb : bool -> bool *)


                                                      (* NUMBERS *)


Module Playground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
 match n with
 | O => m
 | S nn => S (plus nn m)
end.

Eval simpl in (plus (S (S (S O))) (S (S O))).
Eval simpl in (plus 4 7).

Fixpoint mult (n m : nat) : nat :=
 match n with
 | O => O
 | S nn => plus m (mult nn m)
end.

Eval simpl in (mult 1 2).
Eval simpl in (mult (S (S O)) (S (S (S O)))).

Fixpoint minus (n m : nat) : nat :=
 match n, m with
 | O, _ => O
 | n, O => n
 | (S n), (S m) => minus n m
end.

Eval simpl in (minus 3 9).

End Playground2.

Fixpoint exp (base power : nat) : nat :=
 match power with
 | O => S O
 | S n => mult base (exp base n)
end.

Eval simpl in (exp 2 3).

Example test_mult1: (mult 3 3) = exp 3 2.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat :=
 match n with
 | O => S O
 | S n => mult (S n) (factorial n)
end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.


Check (0 + (1 + 0)).
 

Fixpoint beq_nat (n m : nat) : bool :=
 match n with
 | O => match m with
        | O => true
        | S mm => false
        end
 | S nn => match m with
           | O => false
           | S mm => beq_nat nn mm
           end
 end.

Fixpoint ble_nat (n m : nat) : bool :=
 match n with
 | O => true
 | S nn => match m with
           | O => false
           | S mm => ble_nat nn mm
           end
 end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
 match n, m with
 | nn, mm => andb (ble_nat nn mm) (negb (beq_nat nn mm))
 end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. compute. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. compute. reflexivity. Qed.


                                         (* PROOF BY SIMPLIFICATION *)


Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n' : forall n:nat, 0 + n = n.
Proof. reflexivity. Qed.

Eval simpl in (forall n:nat, n + 0 = n).
Eval simpl in (forall n:nat, 0 + n = n).

Theorem plus_O_nnn : forall n:nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
 intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
 intros n. reflexivity. Qed.


                                      (* PROOF BY REWRITING *)


Theorem plus_id_example : forall n m:nat,
 n = m ->
 n + n = m + m.
Proof. 
  intros n m. (* move both quantifiers into the context *)
  intros H. (* move the hypothesis into the context *)
  rewrite <- H. (* or rewrite -> H. *)
  reflexivity. 
Qed.

Theorem plus_id_exercise : forall n m o : nat, 
  n = m -> m = o -> n + m = m + o.
Proof. 
  intros n m o.
  intros H.
  intros H2.
  rewrite -> H.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem mult_O_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = m + (n * m).
Proof. 
  intros n m.
  rewrite -> plus_1_l.
  simpl.
  reflexivity.
Qed.
  
                                     (* CASE ANALYSIS *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
 beq_nat (n + 1) 0 = false.
Proof.
 intros n. destruct n as [ | nn]; (* or reflexivity 2x *)
 reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
 intros b. destruct b;
 reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
 beq_nat 0 (n + 1) = false.
Proof.
 intros n.
 destruct n;
 reflexivity.
Qed.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
 match reverse goal with
 | H : _ |- _ => try move x after H
 end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
 let H := fresh in
 assert (x = v) as H by reflexivity;
 clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
 first [
   set (x := name); move_to_top x
 | assert_eq x name; move_to_top x
 | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
 intros b c H.
 destruct b.
 Case "b = true".
  reflexivity.
 Case "b = false".
  rewrite <- H. reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
 andb b c = true -> c = true.
Proof.
  intros b c.
  intros H.
  destruct c.
  reflexivity.
  rewrite <- H.
  destruct b;
  reflexivity.
Qed.
  

Theorem andb_true_elim1again : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c.
  intros H.
  destruct b.
  Case "b = true".
  reflexivity.
  Case "b = false".
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_0_r : forall n : nat, 
  n + 0 = n.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n.
  rewrite plus_0_r.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite plus_n_Sm.
  reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S nn => S ( S (double nn))
  end.

Eval simpl in (double 15).

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite plus_n_Sm.
  reflexivity.
Qed.

(* Destruct vs Induction
 Destruct analysis all cases defined for the type, and on an induction is needed
 to prove base case and then from any point N, go to the next point (N+1). *)

                                                 (*FORMAL VS INFORMAL PROOF*)

Theorem plus_assocc : forall (n m p : nat),
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem mult_0_plusn : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). (* Could be any letter, or "assert (...) as H" *)
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity. 
Qed.

Theorem plus_rearrange_firsttry : forall n m p q, 
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite plus_comm.
Admitted.

Theorem plus_rearrange : forall n m p q,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity. 
Qed.

Theorem plus_swap : forall n m p,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (n + (m + p) = (m + p) + n) as H1.
    Case "Proof of assertion 1". rewrite plus_comm. reflexivity.
  rewrite H1.
  assert (n + p = p + n) as H2.
    Case "Proof of assertion 2". rewrite plus_comm. reflexivity.
  rewrite H2.
  rewrite plus_assocc.
  reflexivity.
Qed.

(* mult_comm aux: *)
Theorem mult_2_to_plus : forall m,
    m * 2 = m + m.
    Proof.
       intros m. induction m. reflexivity. simpl. rewrite IHm. rewrite plus_n_Sm.
       reflexivity. 
    Qed. 

(* mult_comm aux 2: *)

Theorem mult_1_r : forall x,
  x * 1 = x.
Proof.
  intros x. induction x. reflexivity. simpl. rewrite IHx. reflexivity.
Qed.

Theorem mult_p_Sp : forall p q,
     p * S q = p + p * q.
     Proof.
       intros p q. 
       induction p. simpl. reflexivity. simpl. rewrite IHp. rewrite plus_swap.
       reflexivity.
Qed.

Theorem mult_comm : forall m n,
  m * n = n * m.
Proof.
  intros m n.
  induction m.
  rewrite mult_0_r.
  reflexivity.
  simpl.
  rewrite IHm.
  rewrite mult_p_Sp.
  reflexivity.
Qed.

Theorem evenb_n_oddb_Sn : forall n,
  evenb n = negb (evenb (S n)).
Proof.
  intros.
  induction n.
  Case "n = 0".
  reflexivity. simpl. destruct n.
  reflexivity. rewrite IHn. simpl.
  rewrite negb_involutive.
  reflexivity.
Qed.

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
 
Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b:bool, 
  andb b false = false.
Proof.
  intros.
  destruct b;
  reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros.
  induction p.
  simpl.
  rewrite H.
  reflexivity.
  simpl. rewrite IHp.
  reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intros.
  destruct n;
  reflexivity.
Qed.
  
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite plus_0_r.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
   (andb b c)
   (orb (negb b)
           (negb c)) = true.
Proof.
  intros.
  destruct b.
  simpl.
  destruct c; reflexivity.
  reflexivity.
Qed.

Require Import Setoid.
Require Import Arith.

Theorem mult_p_Sp2 : forall p q,
  p * S q = p * q + p.
Proof.
  intros.
  induction p. 
  reflexivity.
  simpl.
  rewrite IHp.
  repeat rewrite plus_n_Sm.
  rewrite plus_assocc.
  reflexivity.
Qed.

Lemma teste : forall n, S n = n + 1.
Proof.
   intros.
   rewrite plus_comm.
   reflexivity. 
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  rewrite mult_comm.
  induction p.
  rewrite mult_0_r ; rewrite mult_0_r.
  reflexivity.
  simpl.
  rewrite IHp.
  rewrite plus_assocc.
  repeat rewrite mult_p_Sp. 
  rewrite plus_assocc.

  ring.
Qed.

Theorem mult_plus_distr_r2 : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  rewrite mult_comm.
  induction p.
  repeat rewrite mult_0_r.
  reflexivity.
  simpl.
  rewrite IHp.
  assert (H : n * S p = S p * n). 
  rewrite mult_comm.
  reflexivity.
  assert (H1 : m * S p = S p * m).
  rewrite mult_comm.
  reflexivity.
  rewrite H.
  rewrite H1.
  simpl.
  rewrite plus_assoc.
  rewrite mult_comm.
  assert (H2 : m * p = p * m).
  rewrite mult_comm. reflexivity.
  rewrite H2.
  rewrite plus_assocc.
  assert (H3 : n + m + p * n = n + p * n + m).
    assert (H4 : p * n + m = m + p * n).
    rewrite plus_comm. reflexivity.
  rewrite <- plus_assocc.
  rewrite <- H4.
  rewrite plus_assocc.
  reflexivity.
  rewrite H3.
  reflexivity.
Qed.
  
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl. rewrite IHn.
  rewrite mult_plus_distr_r. reflexivity.
Qed.

Theorem plus_swapp : forall n m p u : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
    rewrite plus_assocc.
    rewrite plus_assocc.
    replace (n + m) with (m + n).
    reflexivity. rewrite plus_comm. reflexivity.
Qed.

(**

Inductive bin : Type :=
  | O : bin
  | D : bin -> bin
  | DM : bin -> bin.

Fixpoint sucb (b : bin) : bin :=
  match b with
  | O => DM O
  | D b => DM b
  | DM b => D (sucb b)
  end.
 

Fixpoint predb (b : bin) : bin :=
  match b with
  | O => O
  | D b => DM (predb b)
  | DM b => D b (* match b with
            | O => O
            | b => D b
            end *)
  end.

Eval simpl in (sucb O).
Eval simpl in (sucb (D O)).
Eval simpl in (sucb (DM O)).
Eval simpl in (sucb (DM (D (DM O)))).
Eval simpl in (predb (D (D (DM O)))).
Eval simpl in (sucb (DM (D (DM (DM O))))).
Eval simpl in (predb (DM (D (DM (DM O))))).

Fixpoint convb (b : bin) : nat :=
  match b with
  | O => 0
  | D bb => (convb bb) + (convb bb)
  | DM bb => 1 + (convb bb) + (convb bb)
  end.

Eval simpl in (convb (DM (D (DM O)))).
Eval simpl in (convb (D (DM (DM O)))).
Eval simpl in (convb (DM (D (DM (DM O))))).

Definition sucn (n:nat) : nat :=
  S n.
**)

Theorem plus_Sn_m : forall n m : nat,
  S (n + m) = S n + m.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn. 
  reflexivity.
Qed.
 
(**

Theorem binprove : forall b : bin, S (convb b) = convb (sucb b).
Proof.
  intros.
  induction b.
  reflexivity.
  simpl. reflexivity.
  simpl.
  rewrite plus_n_Sm. rewrite IHb. rewrite plus_Sn_m. rewrite IHb.
  reflexivity.
Qed.

**)

(* Fixpoint coq_restriction (n : nat) : nat :=
  match n with
  | 0 => 0
  | S (S x) => coq_restriction x
  | S nn => coq_restriction n
  
  end. *)



