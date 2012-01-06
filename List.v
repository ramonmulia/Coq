Require Export Basics.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition fstt (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition sndd (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairingg : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  destruct p.
  reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod), 
  p = (fst p, snd p).
Proof.
  intros p. destruct p as (n,m). simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros.
  destruct p. reflexivity.
Qed.

Theorem fst_swap_is_and : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros.
  destruct p.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition l_123' := 1 :: (2 :: (3 :: nil)).
Definition l_123'' := 1 :: 2 :: 3 :: nil.
Definition l_123''' := [1,2,3].

Notation "x + y" := (plus x y)
                    (at level 50, left associativity).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S countt => n :: (repeat n countt)
  end.

Eval simpl in (repeat 15).

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4,5] = [4,5].
Proof. reflexivity. Qed.
Example test_app3: [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tail (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1,2,3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tail: tail [1,2,3] = [2,3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeros t
  | h :: t => h :: (nonzeros t)
  end.

Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match oddb h with
              | true => h :: (oddmembers t)
              | false => oddmembers t
              end
  end.

Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => match oddb h with
              | true => S (countoddmembers t)
              | false => countoddmembers t
              end
  end.

Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example testcountoddmembers2: countoddmembers [0,2,4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, x2 => x2
  | x1, nil => x1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.

Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20,30] = [20,30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => O
  | h :: t => match beq_nat h v with
              | true => S (count v t)
              | false => count v t
              end
  end.    

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1,2,3,1,4,1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  app.

Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
  [v] ++ s.

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1,4,1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  match count v s with
  | O => false
  | S _ => true
  end.

Example test_member1: member 1 [1,4,1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1,4,1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match beq_nat v h with
              | true => t
              | false => h :: (remove_one v t)
              end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match beq_nat v h with
              | true => remove_all v t
              | false => h :: (remove_all v t)
              end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1, s2 with
  | nil, _ => true
  | h :: t, s22 => match member h s22 with
                   | true => subset t (remove_one h s22)
                   | false => false
                   end
  end.

Example test_subset1: subset [1,2] [2,1,4,1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
Proof. reflexivity. Qed.

Theorem nil_app : forall (l : natlist), 
  [] ++ l = l.
Proof.
reflexivity.
Qed.

Theorem tl_length_pred : forall (l : natlist),
  pred (length l) = length (tail l).
Proof.
  intros.
  destruct l as [ | ll].
  reflexivity. reflexivity.
Qed.

Theorem app_ass : forall (l1 l2 l3 : natlist),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros.
  induction l1.
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1".
    simpl. rewrite IHl1.
    reflexivity.
Qed.

Theorem app_length : forall (l1 l2 : natlist),
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros.
  induction l1. reflexivity.
  simpl. rewrite IHl1. reflexivity.
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
  | nil => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1: rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem length_snoc : forall (n:nat) (l:natlist),
  length (snoc l n) = S (length l).
Proof.
  intros. induction l. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_length : forall (l : natlist),
  length (rev l) = length l.
Proof.
  intros.
  induction l. reflexivity.
  simpl. rewrite length_snoc.
  rewrite IHl. reflexivity.
Qed.

(* Usar SearchAbout blablabla *)

Theorem app_nil_end : forall (l : natlist),
  l ++ [] = l.
Proof.
  intros.
  induction l. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma snoc_simpl : forall (n:nat) (l:natlist),
  snoc l n   = l ++ [n].
Proof.
  intros.
  induction l. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed. 

Theorem distr_rev : forall (l1 l2 : natlist),
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros.
  induction l1. simpl. rewrite app_nil_end. reflexivity.
  simpl. rewrite snoc_simpl.  rewrite snoc_simpl. rewrite IHl1. rewrite app_ass.
  reflexivity.
Qed.

Theorem rev_involutive : forall (l:natlist),
  rev (rev l) = l.
Proof.
  intros.
  induction l. reflexivity.
  simpl. rewrite snoc_simpl.
  rewrite distr_rev. rewrite IHl.
  reflexivity.
Qed.

Theorem app_ass4 : forall (l1 l2 l3 l4:natlist),
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros. rewrite app_ass. rewrite app_ass.
  reflexivity.
Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros.  
  induction l. reflexivity. 
  simpl. rewrite IHl. reflexivity.
Qed.


Lemma nonzeros_length : forall (l1 l2 : natlist),
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros.
  induction l1. reflexivity. assert (H : (n :: l1) ++ l2 = n :: (l1 ++ l2)).
  simpl.
  reflexivity.
  rewrite H.
  destruct n.
  simpl. apply IHl1.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed. 



Theorem count_member_nonzero : forall (s:bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  intros.
  destruct s; reflexivity.
Qed.

Theorem ble_n_Sn : forall (n:nat),
  ble_nat n (S n) = true.
Proof.
  intros. induction n. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.


Theorem remove_decreases_count : forall (s:bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros.
  induction s. reflexivity.
  destruct n.
  simpl.
  rewrite ble_n_Sn.
  reflexivity.
  simpl.
  apply IHs.
Qed.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
  | nil => 42 (* arbitrary *)
  | a :: l' => match beq_nat n 0 with
               | true => a
               | false => index_bad (pred n) l'
               end
  end.

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n 0 with
               | true => Some a
               | false => index (pred n) l'
               end
  end.

Example test_index1  : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4,5,6,7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4,5,6,7] = None.
Proof. reflexivity. Qed.

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n 0 then Some a else index' (pred n) l'
  end.

Definition option_elim (o : natoption) (d : nat) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_opt (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_opt1  : hd_opt [] = None.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt3 : hd_opt [5,6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim (hd_opt l) default.
Proof.
  intros. induction l; reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _, [] => false
  | h1 :: t1, h2 :: t2 => if beq_nat h1 h2 then beq_natlist t1 t2 else false
  end.

Example test_beq_natlist1  : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1,2,3] [1,2,3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1,2,3] [1,2,4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall (l:natlist),
  true = beq_natlist l l.
Proof.
  intros. induction l. reflexivity.
  rewrite IHl. simpl.
  replace (beq_nat n n) with (true).
  reflexivity. induction n. reflexivity. simpl. rewrite IHn. reflexivity.
Qed.

Theorem silly1 : forall (n m o p : nat),
  n = m -> [n,o] = [n,p] -> [n,o] = [m,p].
Proof.
  intros.
  rewrite <- H.
  apply H0.
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m -> (forall (q r:nat), q = r -> 
           [q,o] = [r,p]) -> [n,o] = [m,p].
Proof.
  intros.
  apply H0.
  apply H.
Qed.

(*  /\ IMPOSSÍVEL COM REWRITE?   *)

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) -> 
      (forall (q r:nat), (q,q) = (r,r) ->
             [q] = [r]) ->
                 [n] = [m].
Proof.
  intros.
  apply H0.
  apply H.
Qed.

Theorem silly_ex : (forall (n:nat), evenb n = true -> oddb (S n) = true) ->
   evenb 3 = true -> oddb 4 = true.
Proof.
  intros. apply H0. (* ou apply H0 ??? *)
Qed.

Theorem silly3_firsttry : forall (n:nat),
  true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.
Proof.
  intros.
  simpl.
  symmetry in H.
  assumption.
Qed.

Theorem sill3y3: forall (n:nat),
  true = beq_nat n 5 ->
  beq_nat (S (S n)) 7 = true.
Proof.
  intros.
  simpl. symmetry. apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : natlist),
  l = rev l' -> l' = rev l.
Proof.
  intros.
  rewrite H.
  symmetry.
  apply rev_involutive.
Qed.


Theorem app_ass' : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1. induction l1 as [ | n l1'].
  reflexivity.
  assert (H : forall l2 l3, ((n::l1') ++ l2) ++ l3 = n :: (l1' ++ l2 ++ l3)).
Admitted.







