Require Import Lists.List.

Fixpoint distinct (A : Type) (l : list A) : Prop :=
  match l with
    | nil => True
    | cons a l' => (~ In a l') /\ distinct A l'
  end.

Implicit Arguments distinct [A].


Lemma nth_error_in : forall A (l : list A) a n, nth_error l n = Some a -> In a l.
  induction l; intros; destruct n; simpl in *|-*; try discriminate.
  inversion H. auto.
  right. apply (IHl _ _ H).
Qed.


Lemma Forall2_length : forall A B (R : A -> B -> Prop) l l',
                         Forall2 R l l' -> length l = length l'.
  induction l; induction l'; intros; inversion H; subst; try reflexivity.
  simpl; auto.
Qed.


Lemma Forall2_nth_error :
  forall A B (R : A -> B -> Prop) l l',
    Forall2 R l l' ->
    (forall a n, nth_error l n = Some a ->
                 exists b, nth_error l' n = Some b /\ R a b) /\
    (forall n, nth_error l n = None -> nth_error l' n = None).
  intros A B R l l' H.
  split; induction H; intros; induction n;
  try reflexivity; try discriminate; try inversion H1; try eapply @IHForall2;
  subst; repeat eexists; eauto.
Qed.