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

