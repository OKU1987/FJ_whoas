Require Import FJ_tactics.
Require Import List.
Require Import Arith.Peano_dec.
Require Import JMeq.
Require Import EqdepFacts.

Section FJ_Definition.

  Definition C : Set := nat.
  Definition F : Set := nat.
  Definition M : Set := nat.

  Inductive CL := cl : C -> CL | Object : CL.
  
  Inductive Ty : Set :=
    ty_def : CL -> Ty.

  Inductive x_this : Set := 
  | x : x_this
  | this : x_this.

  Variable V : x_this -> Ty -> Set.
  Axiom variables_exist : forall t (P : (V x t) -> Prop),
                            (forall v : V x t, P v) -> exists v', P v'.  
  Axiom this_exists : forall t (P : (V this t) -> Prop),
                            (forall v : V this t, P v) -> exists v', P v'.  


  Inductive FD := fd : Ty -> F -> FD.

  Inductive E : Set :=
  | e_var : forall xt t, V xt t -> E
  | fd_access : E -> F -> E
  | m_call : E -> M -> list E -> E
  | new : Ty -> list E -> E.
  Implicit Arguments e_var [xt t].

  Inductive MB : x_this -> Set :=
  | mb_empty : E -> MB x
  | mb_var : forall t, (V x t -> MB x) -> MB x
  | mb_this : forall t, (V this t -> MB x) -> MB this.

  Inductive K := k : C -> list FD -> K.

  Inductive Mty := mty : list Ty -> Ty -> Mty.
  Inductive MD : Set := md : Ty -> M -> MB this -> MD.
  Inductive L : Set := cld : C -> Ty -> list FD -> K -> list MD -> L.



  Variable CT : C -> option L.
  Variable CT_self : forall c c1 cl' l k fds, CT c = Some (cld c1 cl' l k fds) -> c = c1.
  

  Inductive subtype : Ty -> Ty -> Prop :=
  | sub_refl : forall c, subtype c c
  | sub_trans : forall c d e, subtype c d -> subtype d e ->
                              subtype c e
  | sub_class : forall c d fds k' mds, CT c = Some (cld c (ty_def d) fds k' mds) ->
                                      subtype (ty_def (cl c)) (ty_def d).

  Inductive fields : Ty -> list FD -> Prop :=
  | fields_Obj : fields (ty_def Object) nil
  | fields_cl :
      forall c d c_fds d_fds k' mds,
        CT c = Some (cld c (ty_def d) c_fds k' mds) ->
        fields (ty_def d) d_fds ->
        fields (ty_def (cl c)) (d_fds ++ c_fds).

  Scheme fields_rec := Induction for fields Sort Prop.


  Inductive Extract_tys : forall xt, MB xt -> list Ty -> Prop :=
  | mb_empty_nil : forall e, Extract_tys _ (mb_empty e) nil
  | mb_var_cons : forall ty ctxt tys,
                    (forall v : V x ty, Extract_tys _ (ctxt v) tys) ->
                    Extract_tys _ (mb_var ty ctxt) (ty::tys)
  | mb_this_cons : forall ty ctxt tys,
                     (forall v : V this ty, Extract_tys x (ctxt v) tys) ->
                     Extract_tys this (mb_this ty ctxt) (ty::tys).


  Scheme Extract_tys_rec := Induction for Extract_tys Sort Prop.

  Inductive mtype : M -> Ty -> Mty -> Prop :=
  | mtype_fnd : forall m c d fds k' mds ty mb ty' tys,
                  CT c = Some (cld c d fds k' mds) ->
                  In (md ty m mb) mds ->
                  Extract_tys _ mb (ty'::tys) ->
                  mtype m (ty_def (cl c)) (mty tys ty)
  | mtype_not_fnd : forall m c d fds k' mds mty',
                      CT c = Some (cld c d fds k' mds) ->
                      (forall b mb, ~ In (md b m mb) mds) ->
                      mtype m d mty' ->
                      mtype m (ty_def (cl c)) mty'.

  Inductive mbody : M -> Ty -> MB this -> Prop :=
  | mbody_fnd : 
      forall m c d fds k' mds ty mb,
        CT c = Some (cld c d fds k' mds) ->
        In (md ty m mb) mds ->
        mbody m (ty_def (cl c)) mb
  | mbody_not_fnd :
      forall m c d fds k' mds mb',
        CT c = Some (cld c d fds k' mds) ->
        (forall b mb, ~ In (md b m mb) mds) ->
        mbody m d mb' ->
        mbody m (ty_def (cl c)) mb'.


  Inductive E_WF : E -> Ty -> Prop :=
  | T_Var : forall xt t (v:V xt t), E_WF (e_var v) t
  | T_Fields : forall e f ty fds ty' i, 
                 E_WF e ty -> 
                 fields ty fds ->
                 nth_error fds i = Some (fd ty' f) ->
                 E_WF (fd_access e f) ty'
  | T_Invk : forall e_0 ty_0 U m Us Ss es,
             E_WF e_0 ty_0 ->
             mtype m ty_0 (mty Us U) ->
             List_P2' E_WF es Ss -> List_P2' subtype Ss Us ->
             E_WF (m_call e_0 m es) U
  | T_New : forall cl Ss fds es,
              fields (ty_def cl) fds ->
              List_P2' E_WF es Ss ->
              List_P2' (fun S fd' => match fd' with fd T _ => subtype S T end) Ss fds ->
            E_WF (new (ty_def cl) es) (ty_def cl).



  Inductive E_WF_in_MB (c:Ty) : forall xt, MB xt -> Ty -> Prop :=
  | wf_e_mb_empty : forall e ty, E_WF e ty ->
                                     E_WF_in_MB c _ (mb_empty e) ty
  | wf_e_mb_var : forall t (f : V x t -> MB x) ty,
                    (forall v, E_WF_in_MB c _ (f v) ty) ->
                    E_WF_in_MB c x (mb_var _ f) ty
  | wf_e_mb_this : forall (f : V this c -> MB x) ty,
                     (forall v, E_WF_in_MB c _ (f v) ty) ->
                     E_WF_in_MB c this (mb_this _ f) ty.

  Section E_WF_recursion.
    Variable (P : forall e ty, E_WF e ty -> Prop)
      (Q : forall es tys, List_P2' (E_WF) es tys -> Prop).

    Hypothesis (H1 : forall xt t v, P _ _ (T_Var xt t v))
      (H2 : forall e f ty fds ty' i wf_e fds_ty nth_i, P _ _ wf_e ->
        P _ _ (T_Fields e f ty fds ty' i wf_e fds_ty nth_i))
      (H3 : forall e_0 ty_0 U m Us Ss es wf_e_0 mtype_m wf_es sub_Ss_Us, P _ _ wf_e_0 -> Q _ _ wf_es -> P _ _ (T_Invk e_0 ty_0 U m Us Ss es wf_e_0 mtype_m wf_es sub_Ss_Us))
      (H4 : forall cl Ss fds es fds_cl wf_es sub_Ss_fds,
        Q _ _ wf_es -> P _ _ (T_New cl Ss fds es fds_cl wf_es sub_Ss_fds))
      (H5 : Q nil nil (nil_P2' E_WF))
      (H6 : forall e es ty tys wf_e wf_es,
        P e ty wf_e -> Q es tys wf_es -> Q _ _ (cons_P2' _ _ _ _ _ wf_e wf_es)).


    Fixpoint E_WF_rec e ty (wf_e : E_WF e ty) : P _ _ wf_e :=
     match wf_e return P _ _ wf_e with
        | T_Var xt t v => H1 xt t v
        | T_Fields e f ty fds ty' i wf_e fds_ty nth_i =>
          H2 e f ty fds ty' i wf_e fds_ty nth_i (E_WF_rec _ _ wf_e)
        | T_Invk e_0 ty_0 U m Us Ss es wf_e_0 mtype_m wf_es sub_Ss_Us =>
          H3 e_0 ty_0 U m Us Ss es wf_e_0 mtype_m wf_es sub_Ss_Us (E_WF_rec _ _ wf_e_0)
             ((fix es_rect es Ss (wf_es : List_P2' (fun e ty => E_WF e ty) es Ss) : Q _ _ wf_es :=
                 match wf_es return Q _ _ wf_es with
                   | nil_P2' => H5
                   | cons_P2' e0 S0 es Ss wf_e0 wf_es =>
                     H6 e0 es S0 Ss wf_e0 wf_es (E_WF_rec _ _ wf_e0) (es_rect _ _ wf_es)
                 end) _ _ wf_es)
        | T_New cl' Ss fds es fds_cl wf_es sub_Ss_fds =>
          H4 cl' Ss fds es fds_cl wf_es sub_Ss_fds
             ((fix es_rect es Ss (wf_es : List_P2' (fun e ty => E_WF e ty) es Ss) : Q _ _ wf_es :=
                 match wf_es return Q _ _ wf_es with
                   | nil_P2' => H5
                   | cons_P2' e0 S0 es Ss wf_e0 wf_es =>
                     H6 e0 es S0 Ss wf_e0 wf_es (E_WF_rec _ _ wf_e0) (es_rect _ _ wf_es)
                 end) _ _ wf_es)
     end.
  End E_WF_recursion.

  Scheme E_WF_in_MB_rec := Induction for E_WF_in_MB Sort Prop.



  Definition override (m : M) (ty : Ty) (Ts : list Ty) (T : Ty) : Prop :=
    forall ds d, mtype m ty (mty ds d) -> T = d /\ Ts = ds.

  Inductive Meth_WF : C -> MD -> Prop :=
  | T_MD : forall (mb:MB this) (e_0 c_0 :Ty) (c:C)
                  (d:CL) (fds:list FD) (k':K) (mds:list MD) (m:M) tys,
      Extract_tys _ mb (ty_def (cl c)::tys) ->
      E_WF_in_MB (ty_def (cl c)) this mb e_0 ->
      subtype e_0 c_0 ->
      CT c = Some (cld c (ty_def d) fds k' mds) ->
      override m (ty_def d) tys c_0 ->
      Meth_WF c (md c_0 m mb).

  Inductive L_WF : L -> Prop :=
  T_cld :
    forall c d d_fds c_fds k' mds,
      k' = k c (d_fds ++ c_fds) ->
      fields (ty_def d) d_fds ->
      (forall md, In md mds -> Meth_WF c md) ->
      distinct (map (fun md' => match md' with md _ m _ => m end) mds) ->
      distinct (map (fun fd' => match fd' with fd _ f => f end) (d_fds++c_fds)) ->
      L_WF (cld c (ty_def d) c_fds k' mds).


  Inductive Sub : (forall xt t, V xt t -> E) -> E -> E -> Prop :=
  | S_var_eq : forall e, Sub e_var e e
  | S_var_neq : forall xt t (v:V xt t) e, Sub (fun _ _ _ => e_var v) e (e_var v)
  | S_fd_access : forall e0 e e0' f, 
                    Sub e0 e e0' -> 
                    Sub (fun xt t v => fd_access (e0 xt t v) f) e
                        (fd_access e0' f)
  | S_m_call : forall e0 es e e0' es' m,
                 Sub e0 e e0' ->
                 List_P2' (fun e0 e0' => Sub e0 e e0') es es' ->
                 Sub (fun xt t v => 
                        m_call (e0 xt t v) m (map (fun e0 => e0 xt t v) es)) 
                     e (m_call e0' m es')
  | S_new : forall ty es e es',
              List_P2' (fun e0 e0' => Sub e0 e e0') es es' ->
              Sub (fun xt t v => new ty (map (fun e0 => e0 xt t v) es)) e
                  (new ty es').

 Section Sub_recursion.
    Variables (P : forall e0 e e0', Sub e0 e e0' -> Prop)
              (Q : forall es e es', List_P2' (fun e0 e0' => Sub e0 e e0') es es' -> Prop).

    Hypothesis 
      (H1 : forall e, P _ _ _ (S_var_eq e))
      (H2 : forall xt t v e, P _ _ _ (S_var_neq xt t v e))
      (H3 : forall e0 e e0' f sub_e0, P _ _ _ sub_e0 -> P _ _ _ (S_fd_access e0 e e0' f sub_e0))
      (H4 : forall e0 es e e0' es' m sub_e0 sub_es, P _ _ _ sub_e0 -> Q _ _ _ sub_es -> P _ _ _ (S_m_call e0 es e e0' es' m sub_e0 sub_es))
      (H5 : forall ty es e es' sub_es, Q _ _ _ sub_es -> P _ _ _ (S_new ty es e es' sub_es))
      (H6 : forall e, Q nil e nil (nil_P2' (fun e0 e0' => Sub e0 e e0')))
      (H7 : forall e0 es e e0' es' sub_e0 sub_es, P e0 e e0' sub_e0 -> Q es e es' sub_es -> Q _ _ _ (cons_P2' _ _ _ _ _ sub_e0 sub_es)).

    Fixpoint Sub_rec e0 e e0' (sub_e0 : Sub e0 e e0') : P _ _ _ sub_e0 :=
      match sub_e0 return P _ _ _ sub_e0 with
        | S_var_eq e => H1 e
        | S_var_neq xt t v e => H2 xt t v e
        | S_fd_access e0 e e0' f sub_e0 => 
          H3 e0 e e0' f sub_e0 (Sub_rec _ _ _ sub_e0)
        | S_m_call e0 es e e0' es' m sub_e0 sub_es =>
          H4 e0 es e e0' es' m sub_e0 sub_es (Sub_rec _ _ _ sub_e0)
             ((fix es_rect es es' (sub_es : List_P2' (fun e0 e0' => Sub e0 e e0') es es') : Q _ _ _ sub_es :=
                 match sub_es return Q _ _ _ sub_es with
                   | nil_P2' => H6 e
                   | cons_P2' e0 e0' es es' sub_e0 sub_es =>
                     H7 e0 es e e0' es' sub_e0 sub_es (Sub_rec _ _ _ sub_e0) (es_rect _ _ sub_es)
                 end) _ _ sub_es)
        | S_new ty es e es' sub_es =>
          H5 ty es e es' sub_es
             ((fix es_rect es es' (sub_es : List_P2' (fun e0 e0' => Sub e0 e e0') es es') : Q _ _ _ sub_es :=
                 match sub_es return Q _ _ _ sub_es with
                   | nil_P2' => H6 e
                   | cons_P2' e0 e0' es es' sub_e0 sub_es =>
                     H7 e0 es e e0' es' sub_e0 sub_es (Sub_rec _ _ _ sub_e0) (es_rect _ _ sub_es)
                 end) _ _ sub_es)
      end.
  End Sub_recursion.


  Inductive Subst : forall xt, MB xt -> list E -> E -> Prop :=
  | Sub_empty : forall e, Subst _ (mb_empty e) nil e
  | Sub_var : forall t f es e e0 e',
                (forall v : V x t, Subst _ (f v) es (e x t v)) ->
                Sub e e0 e' ->
                Subst _ (mb_var _ f) (e0::es) e'
  | Sub_this : forall t f es e e0 e',
                 (forall v : V this t, Subst _ (f v) es (e this t v)) ->
                 Sub e e0 e' ->
                 Subst this (mb_this _ f) (e0::es) e'. 



 Inductive Reduce : E -> E -> Prop :=
  | R_Field : forall c ty fds es f e n,
                fields (ty_def c) fds -> 
                nth_error fds n = Some (fd ty f) -> nth_error es n = Some e ->
                Reduce (fd_access (new (ty_def c) es) f) e
  | R_Invk : forall m (c:CL) (mb:MB this) es ds e,
               mbody m (ty_def c) mb -> 
               Subst this mb (new (ty_def c) es::ds) e ->
               Reduce (m_call (new (ty_def c) es) m ds) e.

  Notation "e ~> d" := (Reduce e d) (at level 70).
  
  Scheme Reduce_rec := Induction for Reduce Sort Prop.

  Inductive C_Reduce : E -> E -> Prop :=
  | RC_Field :
      forall e e' f, C_Reduce e e' -> C_Reduce (fd_access e f) (fd_access e' f)
  | RC_Invk_Recv :
      forall e e' m es,
        C_Reduce e e' -> C_Reduce (m_call e m es) (m_call e' m es)
  | RC_Invk_Arg :
      forall e m es es',
        C_Reduce_List es es' -> C_Reduce (m_call e m es) (m_call e m es')
  | RC_New_Arg :
      forall ty es es',
        C_Reduce_List es es' -> C_Reduce (new ty es) (new ty es')
  with C_Reduce_List : list E -> list E -> Prop :=
       | Reduce_T : forall e e' es, 
                      C_Reduce e e' -> C_Reduce_List (e :: es) (e' :: es)
       | Reduce_P : forall e es es', 
                      C_Reduce_List es es' -> C_Reduce_List (e :: es) (e :: es').


  Scheme C_Reduce_rec :=
    Induction for C_Reduce Sort Prop
    with C_Reduce_List_rec := Induction for C_Reduce_List Sort Prop.



  Section Soundness.
    Variable (WF_CT : forall c l, CT c = Some l -> L_WF l).

    Definition Fields_eq_P c fds (fields_fds : fields c fds) :=
      forall fds', fields c fds' -> fds = fds'.

    Lemma Fields_eq_H1 : Fields_eq_P _ _ fields_Obj.
      unfold Fields_eq_P; intros.
      inversion H; subst.
      reflexivity.
    Qed.

    Lemma Fields_eq_H2 : forall c d c_fds d_fds k' mds CT_c par_fds,
                           Fields_eq_P _ _ par_fds ->
                           Fields_eq_P _ _ (fields_cl c d c_fds d_fds k' mds CT_c par_fds).
      unfold Fields_eq_P; intros.
      inversion H0; subst.
      rewrite H2 in CT_c; inversion CT_c; subst. clear CT_c H2.
      rewrite (H _ H3). reflexivity.
    Qed.

    Definition Fields_eq := fun c fds fields_fds fds' => fields_rec _ Fields_eq_H1 Fields_eq_H2 c fds fields_fds fds'. 


    Definition parent_fields_names_eq_P cl' d_fds (cl_fields : fields cl' d_fds) :=
      forall d d_fds' d_fds'', cl' = ty_def d -> d_fds'' = d_fds ->
        fields (ty_def d) d_fds' -> 
        map (fun fd' : FD => match fd' with fd _ f => f end) d_fds =
        map (fun fd' : FD => match fd' with fd _ f => f end) d_fds'.

    Lemma parent_fields_names_eq_H1 : parent_fields_names_eq_P _ _ fields_Obj.
      unfold parent_fields_names_eq_P; intros.
      inversion H; subst. inversion H1; subst.
      reflexivity.
    Qed.

    Lemma parent_fields_names_eq_H2 : 
      forall c d c_fds d_fds k' mds CT_c par_fds,
        parent_fields_names_eq_P _ _ par_fds ->
        parent_fields_names_eq_P _ _ (fields_cl c d c_fds d_fds k' mds CT_c par_fds).
      unfold parent_fields_names_eq_P; intros.
      inversion H0; subst. clear H0.
      inversion H2; subst. rewrite H1 in CT_c; inversion CT_c; subst.
      generalize (Fields_eq _ _ par_fds _ H3); intro; subst.
      reflexivity.
    Qed.

    Definition parent_fields_names_eq := fun cl' d_fds cl_fields d => fields_rec _ parent_fields_names_eq_H1 parent_fields_names_eq_H2 cl' d_fds cl_fields d.

    Definition fds_distinct_P cl' fds (fields_fds : fields cl' fds) :=
      forall c d f m n fds',
      map (fun fd' => match fd' with fd _ f => f end) fds' =
      map (fun fd' => match fd' with fd _ f => f end) fds ->
      nth_error fds' m = Some (fd c f) -> nth_error fds n = Some (fd d f) -> m = n.

    Lemma fds_distinct_H1 : fds_distinct_P _ _ fields_Obj.
      unfold fds_distinct_P; intros.
      destruct n; simpl in H1; discriminate.
    Qed.

    Lemma fds_distinct_H2 : forall c d c_fds d_fds k' mds CT_c par_fds,
                              fds_distinct_P _ _ par_fds ->
                              fds_distinct_P _ _ (fields_cl c d c_fds d_fds k' mds CT_c par_fds).
      unfold fds_distinct_P; intros.
      generalize (WF_CT _ _ CT_c); intros WF_c; inversion WF_c; subst.
      assert (distinct (map (fun fd' => match fd' with fd _ f => f end) (d_fds ++ c_fds))).
      generalize c_fds d_fds0 (parent_fields_names_eq _ _ par_fds _ _ _ (refl_equal _) (refl_equal _) H9) H12; clear.
      induction d_fds; simpl; intros c_fds d_fds0 H H0; destruct d_fds0; simpl in H, H0;
      try discriminate; auto.
      destruct a; destruct f.
      injection H; intros d_fds_eq f_eq; rewrite f_eq; destruct H0 as [NotIn_f dist_rest]; split.
      unfold not; intros In_f; apply NotIn_f; generalize d_fds0 c_fds d_fds_eq In_f; clear; 
        induction d_fds; simpl; intros; destruct d_fds0; simpl in *|-*; try discriminate; auto.
      destruct a; destruct f0; simpl in d_fds_eq; injection d_fds_eq; clear d_fds_eq; intros d_fds_eq a_eq; subst.
      destruct In_f; try tauto; right; eapply IHd_fds; eauto.
      eauto.
      assert (nth_error (map (fun fd' => match fd' with fd _ f => f end) (d_fds ++ c_fds)) n = Some f).
      generalize d_fds n H2; clear; 
        induction c_fds; simpl;
          try (induction d_fds; intros; destruct n; simpl in *|-* );
            first [discriminate | destruct a; injection H1; intros; subst; reflexivity | eauto];
              destruct a; simpl in *|-*; intros; try discriminate; try injection H2; intros;
                first [ try inversion H; reflexivity | eauto].
      rename H2 into H'.
      generalize n H'; clear; induction c_fds; simpl; intro n; destruct n; simpl; intros;
        try (simpl in H'; discriminate); eauto.
      destruct a; simpl in *|-*.
      injection H'; intros; subst; reflexivity.
      assert (nth_error (map (fun fd' : FD => match fd' with
                                                | fd _ f => f
                                              end) fds') m = Some f) by
      (generalize m H1; clear; induction fds'; simpl; intro m; destruct m; simpl; intros; 
        try discriminate; eauto; destruct a; injection H1; intros; subst; reflexivity).
      rewrite H0 in H5.
      rewrite map_app in H5; rewrite <- map_app in H5.
      generalize m n H3 H4 H5; clear;
        induction (map (fun fd' : FD => match fd' with
                                          | fd _ f => f
                                        end) (d_fds ++ c_fds)); simpl; intros;
        destruct m; destruct n; simpl in *|-*; intros; try discriminate; auto;
          destruct H3.
      inversion H5; subst.
      elimtype False; apply H; eapply nth_error_in; eauto.
      inversion H4; subst.
      elimtype False; apply H; eapply nth_error_in; eauto.
      eauto.
    Qed.

    Definition fds_distinct := fun cl' fds fields_fds c => fields_rec _ fds_distinct_H1 fds_distinct_H2 cl' fds fields_fds c.
 
    Definition m_eq_dec := eq_nat_dec.

    Lemma In_m_mds_dec : forall m mds, (exists ty, exists mb, In (md ty m mb) mds) \/ (forall ty mb, ~ In (md ty m mb) mds).
      induction mds; intros; simpl.
      tauto.
      destruct a as [ty' m' mb']; destruct (m_eq_dec m m').
      subst; left; exists ty'; exists mb'; left; try reflexivity.
      destruct IHmds as [[ty'' [mb'' In_m]] | NIn_m].
      left; exists ty''; exists mb''; tauto.
      right; unfold not; intros ty mb H; destruct H.
      congruence.
      eapply NIn_m; eauto.
    Qed.

    Lemma Extract_tys_eq : forall xt mb Ts Ts',
                             Extract_tys xt mb Ts ->
                             Extract_tys xt mb Ts' -> Ts = Ts'.
      intros xt mb Ts ? H. generalize dependent Ts'.
      induction H; intros.
      inversion H; subst. reflexivity.
      inversion H1; subst.
      apply eq_sigT_eq_dep in H3.
      apply eq_dep_JMeq in H3.
      apply JMeq_eq in H3. subst.
      destruct (variables_exist _ _ H4).
      rewrite (H0 _ _ H2). reflexivity.
      inversion H1; subst.
      apply eq_sigT_eq_dep in H3.
      apply eq_dep_JMeq in H3.
      apply JMeq_eq in H3. subst.
      destruct (this_exists _ _ H4).
      rewrite (H0 _ _ H2). reflexivity.
    Qed.


    Lemma meth_overriding S T (sub_S_T : subtype S T) : forall m Us U,
                              mtype m T (mty Us U) -> mtype m S (mty Us U).
      intros.
      induction sub_S_T; auto.
      destruct (In_m_mds_dec m mds) as [[ty [mb In_m]] | Not_In_m].
      generalize (WF_CT _ _ H0); intro WF_c. inversion WF_c. subst.
      clear CT_self.
      generalize (H8 _ In_m); intro WF_m. inversion WF_m; subst.
      rewrite H12 in H0. inversion H0. subst.
      unfold override in H13. destruct (H13 Us U H); subst.
      eapply mtype_fnd; eassumption.
      eapply mtype_not_fnd; eassumption.
    Qed.


    Lemma subclass_fields : forall S T (sub_S_T : subtype S T),
                              forall fds', 
                                fields T fds' ->
                                exists fds, fields S fds /\
                                            (forall fd' n, nth_error fds' n = Some fd' -> nth_error fds n = Some fd').
      intros S T sub_S_T.
      induction sub_S_T; intros.
      Case "sub_refl".
      exists fds'. split. assumption.
      intros. assumption.
      Case "sub_trans".
      destruct (IHsub_S_T2 _ H) as [fds'' [fields_d nth_fds']].
      destruct (IHsub_S_T1 _ fields_d) as [fds''' [fields_c nth_fds'']].
      exists fds'''. split. assumption.
      intros.
      apply (nth_fds'' _ _ (nth_fds' _ _ H0)).
      Case "sub_class".
      generalize (WF_CT _ _ H); intros.
      inversion H1; subst.
      generalize (Fields_eq _ _ H0 _ H8); intro; subst.
      eexists. split. econstructor; eassumption.
      clear. 
      induction d_fds; intros; destruct n; simpl in *|-*; try discriminate; auto.
    Qed.


    
    Definition Term_subst_pres_types_sub_P e0 d e (sub_e0 : Sub e0 d e) :=
      forall xt t (v:V xt t) D S, E_WF (e0 _ _ v) D ->
                                  E_WF d S ->
                                  subtype S t ->
                                  exists C, E_WF e C /\ subtype C D.

    Definition Term_subst_pres_types_sub_Q es d es' (sub_es : List_P2' (fun e0 e0' => Sub e0 d e0') es es') :=
      forall xt t (v:V xt t) Ds S, 
        List_P2' E_WF (map (fun e0 => e0 _ _ v) es) Ds ->
        E_WF d S ->
        subtype S t ->
        exists Cs, List_P2' E_WF es' Cs /\ List_P2' subtype Cs Ds.


    Lemma Term_subst_pres_types_sub_H1 : forall e, Term_subst_pres_types_sub_P _ _ _ (S_var_eq e).
      unfold Term_subst_pres_types_sub_P; intros.
      inversion H; repeat subst.
      exists S. split; assumption.
    Qed.

    Lemma Term_subst_pres_types_sub_H2 : forall xt t v e, Term_subst_pres_types_sub_P _ _ _ (S_var_neq xt t v e).
      unfold Term_subst_pres_types_sub_P; intros.
      exists D. split. assumption. constructor.
    Qed.

    Lemma Term_subst_pres_types_sub_H3 : forall e0 e e0' f sub_e0, Term_subst_pres_types_sub_P _ _ _ sub_e0 -> Term_subst_pres_types_sub_P _ _ _ (S_fd_access e0 e e0' f sub_e0).
      unfold Term_subst_pres_types_sub_P; intros.
      inversion H0; subst.
      destruct (H _ _ _ _ _ H5 H1 H2) as [E [wf_e0' sub_E]].
      destruct (subclass_fields _ _ sub_E _ H6) as [fds' [fields_E nth_fds]].
      generalize (nth_fds _ _ H8); intros.
      exists D. split. econstructor; eassumption. constructor.
    Qed.      

    Lemma Term_subst_pres_types_sub_H4 : forall e0 es e e0' es' m sub_e0 sub_es, Term_subst_pres_types_sub_P _ _ _ sub_e0 -> Term_subst_pres_types_sub_Q _ _ _ sub_es -> Term_subst_pres_types_sub_P _ _ _ (S_m_call e0 es e e0' es' m sub_e0 sub_es).
      unfold Term_subst_pres_types_sub_P; unfold Term_subst_pres_types_sub_Q; intros.
      inversion H1; subst.
      rename Us into Es. rename Ss into Ds. rename ty_0 into D0.
      destruct (H _ _ _ _ _ H7 H2 H3) as [C0 [wf_e0' sub_C0_D0]].
      destruct (H0 _ _ _ _ _ H10 H2 H3) as [Cs [wf_es' sub_Cs_Ds]].
      generalize (meth_overriding _ _  sub_C0_D0 _ _ _ H8); intro.
      eexists.
      split. econstructor; try eassumption.
      generalize sub_Cs_Ds H11; clear; intros.
      Prop_Ind H11; intros; inversion sub_Cs_Ds; subst; constructor.
      constructor 2 with (d:=a); assumption.
      eapply IHList_P2'; eauto.
      constructor.
    Qed.

    Lemma Term_subst_pres_types_sub_H5 : forall ty es e es' sub_es, Term_subst_pres_types_sub_Q _ _ _ sub_es -> Term_subst_pres_types_sub_P _ _ _ (S_new ty es e es' sub_es).
      unfold Term_subst_pres_types_sub_P; unfold Term_subst_pres_types_sub_Q; intros.
      inversion H0; subst.
      destruct (H _ _ _ _ _ H6 H1 H2) as [Es [wf_es' sub_Es_Ss]].
      eexists. split.
      econstructor; try eassumption.
      generalize H8 sub_Es_Ss; clear; intros.
      Prop_Ind H8; intros; inversion sub_Es_Ss; subst; constructor.
      destruct b.
      constructor 2 with (d:=a); assumption.
      eapply IHList_P2'; eauto.
      constructor.
    Qed.

    Lemma Term_subst_pres_types_sub_H6 : forall e, Term_subst_pres_types_sub_Q _ _ _ (nil_P2' (fun e0 e0' => Sub e0 e e0')).
      unfold Term_subst_pres_types_sub_Q; intros.
      inversion H; subst.
      exists nil. split; constructor.
    Qed.

    Lemma Term_subst_pres_types_sub_H7 : forall e0 es e e0' es' sub_e0 sub_es, Term_subst_pres_types_sub_P e0 e e0' sub_e0 -> Term_subst_pres_types_sub_Q es e es' sub_es -> Term_subst_pres_types_sub_Q _ _ _ (cons_P2' _ _ _ _ _ sub_e0 sub_es).
      unfold Term_subst_pres_types_sub_P; unfold Term_subst_pres_types_sub_Q; intros.
      inversion H1; subst.
      destruct (H _ _ _ _ _ H6 H2 H3). destruct H4.
      destruct (H0 _ _ _ _ _ H8 H2 H3). destruct H7.
      eexists. split. econstructor; eassumption.
      constructor; assumption.
    Qed.

    Definition Term_subst_pres_types_sub := Sub_rec _ _ Term_subst_pres_types_sub_H1 Term_subst_pres_types_sub_H2 Term_subst_pres_types_sub_H3 Term_subst_pres_types_sub_H4 Term_subst_pres_types_sub_H5 Term_subst_pres_types_sub_H6 Term_subst_pres_types_sub_H7.


    Lemma Term_subst_pres_types : forall mb D0 D,
                                   E_WF_in_MB D0 this mb D ->
                                   forall ds Ss Us e,
                                     List_P2' E_WF ds Ss -> 
                                     List_P2' subtype Ss Us ->
                                     Extract_tys this mb Us ->
                                     Subst this mb ds e ->
                                     exists E, E_WF e E /\ subtype E D.
      intros mb D0 D H.
      induction H.
      Case "wf_e_mb_empty".
      intros.
      inversion H3; subst.
      exists ty. split. assumption. constructor.
      Case "wf_e_mb_var".
      intros.
      inversion H4; subst.
      inversion H3; subst.
      assert (JMeq f1 f) by
          (change match existT (fun t => V x t -> MB x) t f1 with
                       | existT t f1 => JMeq f1 f
                   end; rewrite H6; constructor); subst; clear H6.
      assert (JMeq ctxt0 f) by
          (change match existT (fun t => V x t -> MB x) t ctxt0 with
                       | existT t ctxt0 => JMeq ctxt0 f
                   end; rewrite H9; constructor); subst; clear H9.
      inversion H1; subst.
      inversion H2; subst.
      rename e1 into d.
      destruct (variables_exist _ _ H7) as [v sub_v].
      generalize (H10 v); intro ex_tys.
      destruct (H0 _ _ _ _ _ H12 H15 ex_tys sub_v).
      generalize Term_subst_pres_types_sub; intro.
      destruct H5.
      destruct (H6 _ _ _ H8 _ _ _ _ _ H5 H9 H13).
      destruct H14.
      exists x1. split. assumption.
      constructor 2 with (d:=x0); assumption.
      Case "wf_e_mb_this".
      intros.
      inversion H4; subst.
      inversion H3; subst.
      assert (JMeq f1 f) by
          (change match existT (fun t => V _ t -> MB x) D0 f1 with
                       | existT D0 f1 => JMeq f1 f
                   end; rewrite H6; constructor); subst; clear H6.
      assert (JMeq ctxt0 f) by
          (change match existT (fun t => V _ t -> MB x) D0 ctxt0 with
                       | existT D0 ctxt0 => JMeq ctxt0 f
                   end; rewrite H9; constructor); subst; clear H9.
      inversion H1; subst.
      inversion H2; subst.
      destruct (this_exists _ _ H7) as [v sub_v].
      generalize (H10 v); intro ex_tys.
      destruct (H0 _ _ _ _ _ H12 H15 ex_tys sub_v).
      generalize Term_subst_pres_types_sub; intro.
      destruct H5.
      destruct (H6 _ _ _ H8 _ _ _ _ _ H5 H9 H13).
      destruct H14.
      exists x1. split. assumption.
      constructor 2 with (d:=x0); assumption.
    Qed.


    Lemma Lem_1_4 : 
      forall m c0 mb, 
        mbody m c0 mb -> 
        forall Ds d, mtype m c0 (mty Ds d) ->
                     exists D0, exists c, subtype c0 D0 /\ 
                                          subtype c d /\
                                          Extract_tys _ mb (D0::Ds) /\
                                          E_WF_in_MB D0 _ mb c.
      intros m c0 mb mb_c0.
      induction mb_c0.
      Case "mb_class".
      intros.
      inversion H1; subst.
      SCase "m in mds".
      rewrite H in H6. inversion H6; subst. clear H6.
      generalize (WF_CT _ _ H); intros. inversion H2; subst.
      generalize (H12 _ H0) (H12 _ H7). intros. 
      inversion H3; subst. inversion H4; subst.
      rewrite H23 in H18. inversion H18; subst. clear H18.
      rewrite H in H23. inversion H23; subst. clear H23.
      assert (mb0 = mb).
      generalize H0 H7 H13; clear; intros.
      induction mds. inversion H0.
      inversion H0; inversion H7.
      rewrite H in H1. inversion H1; subst. split; reflexivity.
      subst. inversion H13.
      contradict H.
      apply (in_map (fun md' => match md' with md _ m _ => m end) _ _ H1).
      subst. inversion H13.
      contradict H1.
      apply (in_map (fun md' => match md' with md _ m _ => m end) _ _ H).
      inversion H13.
      apply (IHmds H H1 H3).
      subst.
      generalize (Extract_tys_eq _ _ _ _ H8 H16); intro tys_eq;
      inversion tys_eq; subst; clear tys_eq.
      repeat eexists; eauto.
      constructor. 
      SCase "m not in mds".
      rewrite H in H3. inversion H3; subst. clear H3.
      destruct (H4 ty mb H0).
      Case "mb_super".
      intros.
      inversion H1; subst.
      SCase "m in mds".
      rewrite H in H6. inversion H6; subst. 
      destruct (H0 _ _ H7).
      SCase "m not in mds".
      rewrite H in H3. inversion H3; subst. clear H3.
      destruct (IHmb_c0 _ _ H6)
               as [D0' [c' [sub_d1_D0' [sub_c_d [ext_Ds wf_mb']]]]].
      repeat eexists; eauto.
      destruct d1.
      constructor 2 with (d:=ty_def c0).
      eapply sub_class; eauto. assumption.
    Qed.



    Definition pres_P e e' (red_c : Reduce e e') :=
      forall c, E_WF e c -> exists d, E_WF e' d /\ subtype d c.


    Lemma pres_H1 : forall c ty fds es f e0 n fields_fds fds_n es_n,
                      pres_P _ _ (R_Field c ty fds es f e0 n fields_fds fds_n es_n).
      unfold pres_P; intros.
      inversion H; subst.
      inversion H2; subst.
      generalize (Fields_eq _ _ H3 _ H4).
      generalize (Fields_eq _ _ H4 _ fields_fds).
      intros; subst.
      rename Ss into Cs.
      apply P2'_if_P2 in H6; unfold List_P2 in H6; destruct H6 as [fnd_es not_fnd_es].
      destruct (fnd_es _ _ es_n) as [C [Cs_n wf_e0]].
      exists C. split. eassumption.
      rewrite <- (fds_distinct _ _ H3 _ _ _ _ _ _ (refl_equal _) fds_n H5) in H5.
      apply P2'_if_P2 in H8; unfold List_P2 in H8; destruct H8 as [fnd_Cs not_fnd_Cs].
      destruct (fnd_Cs _ _ Cs_n) as [fd' [fds_n' sub_C]].
      rewrite fds_n' in H5. inversion H5. subst. 
      assumption.
    Qed.

    Lemma pres_H2 : forall m c mb es ds e mbody_m sub_mb,
                      pres_P _ _ (R_Invk m c mb es ds e mbody_m sub_mb).
      unfold pres_P; intros.
      inversion H; subst. inversion H3; subst.
      rename c0 into c1. rename c into c0. rename c1 into c.
      rename e into e'. rename Us into Ds. rename Ss into Cs.
      destruct (Lem_1_4 _ _ _ mbody_m _ _ H4)
        as [D0 [b [sub_c0_D0 [sub_b_c [ext_Ds wf_mb]]]]].
      generalize (cons_P2' _ _ _ _ _ sub_c0_D0 H7);
      generalize (cons_P2' _ _ _ _ _ H3 H6); intros.
      destruct (Term_subst_pres_types _ _ _ wf_mb _ _ _ _ H0 H1 ext_Ds sub_mb)
               as [d [wf_e' sub_d_b]].
      exists d. split.
      assumption.
      constructor 2 with (d:=b); assumption.
    Qed.


    Theorem pres : forall e e',
                     Reduce e e' ->
                     forall c, E_WF e c -> exists d, E_WF e' d /\ subtype d c.
      intros e e' red_c. induction red_c.
      intros.
      eapply pres_H1; eauto.
      eapply pres_H2; eauto.
    Qed.


    Definition C_pres_P e e' (red_e : C_Reduce e e') :=
      forall c, E_WF e c -> exists d, E_WF e' d /\ subtype d c.

    Definition Reduce_List_pres_P es es' (red_es : C_Reduce_List es es') :=
      forall cs, List_P2' E_WF es cs ->
                 exists ds, List_P2' E_WF es' ds /\ List_P2' subtype ds cs.

    Lemma C_pres_H1 : forall e e' f red_e,
                        C_pres_P _ _ red_e ->
                        C_pres_P _ _ (RC_Field e e' f red_e).
      unfold C_pres_P; intros.
      inversion H0; subst.
      destruct (H _ H3) as [d [wf_e']].
      destruct (subclass_fields _ _ H1 _ H4) as [fds' [fields_d]].
      generalize (H2 _ _ H6); intro.
      repeat eexists; try econstructor; try eassumption.
    Qed.

    Lemma C_pres_H2 : forall e e' m es red_e,
                        C_pres_P _ _ red_e ->
                        C_pres_P _ _ (RC_Invk_Recv e e' m es red_e).
      unfold C_pres_P; intros.
      inversion H0; subst.
      destruct (H _ H4) as [d [wf_e']].
      generalize (meth_overriding _ _ H1 _ _ _ H5). intro.
      repeat eexists; try econstructor; try eassumption.
    Qed.

    Lemma C_pres_H3 : forall e m es es' red_es,
                        Reduce_List_pres_P _ _ red_es ->
                        C_pres_P _ _ (RC_Invk_Arg e m es es' red_es).
      unfold Reduce_List_pres_P; unfold C_pres_P; intros.
      inversion H0; subst.
      destruct (H _ H7) as [ds [wf_es']].
      repeat eexists; try econstructor; eauto.
      generalize H1 H8; clear; intros.
      Prop_Ind H1; intros; inversion H8; subst; econstructor.
      econstructor 2; eassumption.
      eapply IHList_P2'; try eassumption; reflexivity.
    Qed.

    Lemma C_pres_H4 : forall ty es es' red_es,
                        Reduce_List_pres_P _ _ red_es ->
                        C_pres_P _ _ (RC_New_Arg ty es es' red_es).
      unfold Reduce_List_pres_P; unfold C_pres_P; intros.
      inversion H0; subst.
      destruct (H _ H4) as [ds [wf_es']].
      repeat eexists; try econstructor; eauto.
      generalize H1 H6; clear; intros.
      Prop_Ind H1; intros; inversion H6; subst; econstructor;
      try destruct b0. econstructor 2; eassumption.
      eapply IHList_P2'; try eassumption; reflexivity.
    Qed.

    Lemma Reduce_List_pres_H1 :
      forall e e' es red_e, C_pres_P _ _ red_e ->
                            Reduce_List_pres_P _ _ (Reduce_T e e' es red_e).
      unfold Reduce_List_pres_P; unfold C_pres_P; intros.
      inversion H0; subst.
      destruct (H _ H3) as [d [wf_e']].
      exists (d::Bs). split.
      constructor; assumption.
      constructor. assumption.
      clear.
      induction Bs; constructor.
      constructor.
      assumption.
    Qed.

    Lemma Reduce_List_pres_H2 :
      forall e es es' red_es, Reduce_List_pres_P _ _ red_es ->
                              Reduce_List_pres_P _ _ (Reduce_P e es es' red_es).
      unfold Reduce_List_pres_P; unfold C_pres_P; intros.
      inversion H0; subst.
      destruct (H _ H5) as [ds [wf_es]].
      exists (b::ds). split.
      constructor; assumption.
      constructor. constructor. assumption.
    Qed.

    Definition C_pres := C_Reduce_rec _ _ C_pres_H1 C_pres_H2 C_pres_H3 C_pres_H4 Reduce_List_pres_H1 Reduce_List_pres_H2.

    Definition Reduce_List_pres := C_Reduce_List_rec _ _ C_pres_H1 C_pres_H2 C_pres_H3 C_pres_H4 Reduce_List_pres_H1 Reduce_List_pres_H2.




End FJ_Definition.



