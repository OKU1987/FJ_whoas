Require Import FJ_util.
Require Import List.
Require Import Arith.Peano_dec.
Require Import JMeq.
Require Import Logic.FunctionalExtensionality.

Section FJ_Definition.

  Definition C : Set := nat.
  Definition F : Set := nat.
  Definition M : Set := nat.

  Inductive CL := cl : C -> CL | Object : CL.
  
  Variable TV : C -> option M -> nat -> Set.
  Axiom type_variables_exist :
    forall c m n (P : TV c m n -> Prop),
      (forall tv : TV c m n, P tv) -> exists tv', P tv'.
  Axiom type_variables_exist' :
    forall c m n (tv : TV c m n),
      exists tv' : TV c m n, tv <> tv'.

  Inductive Ty : Set :=
  | t_var : forall c m n, TV c m n -> Ty
  | NTy : N -> Ty
  with N : Set := N_def : CL -> list Ty -> N.

  Definition NTys := map (fun N' => NTy N').

  Definition N1 c m n := TV c m n -> N.
  Definition Ty1 c m n := TV c m n -> Ty.
  Implicit Arguments N1 [c m n].
  Implicit Arguments Ty1 [c m n].

  Definition NTy1 c m n : @N1 c m n -> @Ty1 c m n
    := fun N' (tv : TV c m n) => NTy (N' tv).
  Implicit Arguments NTy1 [c m n].

  Definition TContext := list (N * C * option M).

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
  | m_call : E -> M -> list Ty -> list E -> E
  | new : N -> list E -> E.
  Implicit Arguments e_var [xt t].

  Inductive MB : x_this -> Set :=
  | mb_empty : E -> MB x
  | mb_var : forall t, (V x t -> MB x) -> MB x
  | mb_this : forall t, (V this t -> MB x) -> MB this.

  Definition MB1 xt c m n := TV c m n -> MB xt.
  Implicit Arguments MB1 [c m n].

  Inductive K := k : C -> list FD -> K.

  Inductive Mty : Set :=
  | mty : list N -> list Ty -> Ty -> Mty
  | mty_tp : forall c m n, (TV c (Some m) n -> Mty) -> Mty.

  Inductive MD : M -> Set :=
  | md : forall m, list N -> Ty -> MB this -> MD m
  | md_tp : forall c m n , (TV c (Some m) n -> MD m) -> MD m.
  Definition MD1 c m m' n := TV c m n -> MD m'.
  Implicit Arguments MD1 [c m n].

  Inductive L : C -> Set :=
  | cld : forall c, list N -> N -> list FD -> K -> list {m : M & MD m} -> L c
  | cld_tp : forall c n, (TV c None n -> L c) -> L c.
  Definition L1 c m n := TV c m n -> L c.
  Implicit Arguments L1 [c m n].

  Inductive MD_in : forall c, L c -> M -> Prop :=
  | md_in : forall c Ns (N':N) fds k mds m,
              In m (map (@projS1 M _) mds) ->
              MD_in _ (cld c Ns N' fds k mds) m
  | md_in_tp : forall m c n f, (forall tv, MD_in _ (f tv) m) ->
                               MD_in _ (cld_tp c n f) m.

  Variable CT : forall c, option (L c).

  Inductive TSub c m n : (TV c m n -> Ty) -> Ty -> Ty -> Prop :=
  | S_tvar_eq : forall t, TSub c m n (@t_var c m n) t t
  | S_tvar_neq : forall (tv: TV c m n) t,
                   TSub c m n (fun _ => t_var tv) t (t_var tv)
  | S_NTy : forall c' tys t tys',
              Forall2 (fun ty0 ty0' => TSub c m n ty0 t ty0') tys tys' ->
              TSub c m n
                   (fun tv => (NTy (N_def c' (map (fun ty => ty tv) tys))))
                   t (NTy (N_def c' tys')).

  Section TSub_recursion.
    Variables (P : forall c m n t0 t t0', TSub c m n t0 t t0' -> Prop)
              (Q : forall c m n ts t ts', Forall2 (fun t0 t0' => TSub c m n t0 t t0') ts ts' -> Prop).

    Hypothesis
      (H1 : forall c m n t, P _ _ _ _ _ _ (S_tvar_eq c m n t))
      (H2 : forall c m n tv t, P _ _ _ _ _ _ (S_tvar_neq c m n tv t))
      (H3 : forall c m n c' tys t tys' sub_ts,
              Q _ _ _ _ _ _ sub_ts ->
              P _ _ _ _ _ _ (S_NTy c m n c' tys t tys' sub_ts))
      (H4 : forall c m n t,
              Q c m n nil t nil (Forall2_nil (fun t0 t0' => TSub c m n t0 t t0')))
      (H5 : forall c m n t0 ts t t0' ts' sub_t0 sub_ts,
              P c m n t0 t t0' sub_t0 -> Q c m n ts t ts' sub_ts ->
              Q c m n _ _ _ (Forall2_cons _ _ sub_t0 sub_ts)).


    Fixpoint TSub_rec c m n t0 t t0' (tsub_t0 : TSub c m n t0 t t0') : P c m n _ _ _ tsub_t0 :=
      match tsub_t0 return P c m n _ _ _ tsub_t0 with
        | S_tvar_eq t => H1 c m n t
        | S_tvar_neq tv t => H2 c m n tv t
        | S_NTy c' tys t tys' sub_ts =>
          H3 c m n c' tys t tys' sub_ts
             ((fix ts_rect ts ts' (sub_ts : Forall2 (fun t0 t0' => TSub c m n t0 t t0') ts ts') : Q _ _ _ _ _ _ sub_ts :=
                 match sub_ts return Q _ _ _ _ _ _ sub_ts with
                   | Forall2_nil => H4 c m n t
                   | Forall2_cons t0 t0' ts ts' sub_t0 sub_ts =>
                     H5 c m n t0 ts t t0' ts' sub_t0 sub_ts (TSub_rec _ _ _ _ _ _ sub_t0) (ts_rect _ _ sub_ts)
                 end) _ _ sub_ts)
      end.
  End TSub_recursion.


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
  | mtype_fnd : forall m c d fds k' mds ty mb tys,
                  CT c = Some (cld c d fds k' mds) ->
                  In (md ty m mb) mds ->
                  Extract_tys _ mb tys -> 
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

  Scheme E_WF_in_MB_rec := Induction for E_WF_in_MB Sort Prop.



  Definition override (m : M) (ty : Ty) (Ts : list Ty) (T : Ty) : Prop :=
    forall ds d, mtype m ty (mty ds d) -> T = d /\ Ts = ds.

  Inductive Meth_WF : C -> MD -> Prop :=
  | T_MD : forall (mb:MB this) (e_0 c_0 :Ty) (c:C)
                  (d:CL) (fds:list FD) (k':K) (mds:list MD) (m:M) tys,
      Extract_tys _ mb tys ->
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
                 Forall2 (fun e0 e0' => Sub e0 e e0') es es' ->
                 Sub (fun xt t v => 
                        m_call (e0 xt t v) m (map (fun e0 => e0 xt t v) es)) 
                     e (m_call e0' m es')
  | S_new : forall ty es e es',
              Forall2 (fun e0 e0' => Sub e0 e e0') es es' ->
              Sub (fun xt t v => new ty (map (fun e0 => e0 xt t v) es)) e
                  (new ty es').

 Section Sub_recursion.
    Variables (P : forall e0 e e0', Sub e0 e e0' -> Prop)
              (Q : forall es e es', Forall2 (fun e0 e0' => Sub e0 e e0') es es' -> Prop).

    Hypothesis 
      (H1 : forall e, P _ _ _ (S_var_eq e))
      (H2 : forall xt t v e, P _ _ _ (S_var_neq xt t v e))
      (H3 : forall e0 e e0' f sub_e0, P _ _ _ sub_e0 -> P _ _ _ (S_fd_access e0 e e0' f sub_e0))
      (H4 : forall e0 es e e0' es' m sub_e0 sub_es, P _ _ _ sub_e0 -> Q _ _ _ sub_es -> P _ _ _ (S_m_call e0 es e e0' es' m sub_e0 sub_es))
      (H5 : forall ty es e es' sub_es, Q _ _ _ sub_es -> P _ _ _ (S_new ty es e es' sub_es))
      (H6 : forall e, Q nil e nil (Forall2_nil (fun e0 e0' => Sub e0 e e0')))
      (H7 : forall e0 es e e0' es' sub_e0 sub_es, P e0 e e0' sub_e0 -> Q es e es' sub_es -> Q _ _ _ (Forall2_cons _ _ sub_e0 sub_es)).

    Fixpoint Sub_rec e0 e e0' (sub_e0 : Sub e0 e e0') : P _ _ _ sub_e0 :=
      match sub_e0 return P _ _ _ sub_e0 with
        | S_var_eq e => H1 e
        | S_var_neq xt t v e => H2 xt t v e
        | S_fd_access e0 e e0' f sub_e0 => 
          H3 e0 e e0' f sub_e0 (Sub_rec _ _ _ sub_e0)
        | S_m_call e0 es e e0' es' m Vs sub_e0 sub_es =>
          H4 e0 es e e0' es' m Vs sub_e0 sub_es (Sub_rec _ _ _ sub_e0)
             ((fix es_rect es es' (sub_es : Forall2 (fun e0 e0' => Sub e0 e e0') es es') : Q _ _ _ sub_es :=
                 match sub_es return Q _ _ _ sub_es with
                   | Forall2_nil => H6 e
                   | Forall2_cons e0 e0' es es' sub_e0 sub_es =>
                     H7 e0 es e e0' es' sub_e0 sub_es (Sub_rec _ _ _ sub_e0) (es_rect _ _ sub_es)
                 end) _ _ sub_es)
        | S_new ty es e es' sub_es =>
          H5 ty es e es' sub_es
             ((fix es_rect es es' (sub_es : Forall2 (fun e0 e0' => Sub e0 e e0') es es') : Q _ _ _ sub_es :=
                 match sub_es return Q _ _ _ sub_es with
                   | Forall2_nil => H6 e
                   | Forall2_cons e0 e0' es es' sub_e0 sub_es =>
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
               Subst this mb ds e ->
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


  Section Soundness.
    Variable (WF_CT : forall c l, CT c = Some l -> L_WF l).

    Definition TSub_eq_P c m n t0 t t0' (_ : TSub c m n t0 t t0') :=
      forall t0'', TSub c m n t0 t t0'' -> t0' = t0''.

    Definition TSub_eq_Q c m n tys t tys' (_ : Forall2 (fun t0 t0' => TSub c m n t0 t t0') tys tys') :=
      forall tys'', Forall2 (fun t0 t0' => TSub c m n t0 t t0') tys tys'' ->
                    tys' = tys''.


    Lemma TSub_eq_H1 : forall c m n t, TSub_eq_P _ _ _ _ _ _ (S_tvar_eq c m n t).
      unfold TSub_eq_P; intros.
      inversion H; subst.
      - reflexivity.
      - generalize (equal_f H1); intro.
        destruct (type_variables_exist' _ _ _ tv) as [tv'].
        generalize (H0 tv'). intro.
        inversion H3.
        existT_eq.
        contradict H2. reflexivity.
      - generalize (equal_f H0); intro.
        destruct (type_variables_exist _ _ _ _ H2).
        discriminate.
    Qed.

    Lemma TSub_eq_H2 : forall c m n tv t, TSub_eq_P _ _ _ _ _ _ (S_tvar_neq c m n tv t).
      unfold TSub_eq_P; intros.
      inversion H; subst.
      - generalize (equal_f H1); intro.
        destruct (type_variables_exist' _ _ _ tv) as [tv'].
        generalize (H0 tv'); intro.
        inversion H3. existT_eq.
        contradict H2. reflexivity.
      - generalize (equal_f H1); intro.
        destruct (type_variables_exist _ _ _ _ H0).
        rewrite H2. reflexivity.
      - generalize (equal_f H0); intro.
        destruct (type_variables_exist _ _ _ _ H2).
        discriminate.
    Qed.

    Lemma TSub_eq_H3 : forall c m n c' tys t tys' sub_tys,
                         TSub_eq_Q _ _ _ _ _ _ sub_tys ->
                         TSub_eq_P _ _ _ _ _ _ (S_NTy c m n c' tys t tys' sub_tys).
      unfold TSub_eq_P; unfold TSub_eq_Q; intros.
      inversion H0; subst;
      try (generalize (equal_f H2); intro;
           destruct (type_variables_exist _ _ _ _ H1);
           discriminate).
      assert (Forall2 (fun ty0 ty0' => TSub c m n ty0 t ty0') tys tys'0).
      generalize sub_tys H2 H1; clear; intros.
      generalize dependent H1.
      generalize dependent H2.
      generalize dependent tys'0.
      generalize dependent tys0.
      induction sub_tys; intros tys0 tys'0 H2; induction H2; intros; subst.
      - constructor.
      - generalize (equal_f H1); intro.
        destruct (type_variables_exist _ _ _ _ H0).
        inversion H3.
      - generalize (equal_f H1); intro.
        destruct (type_variables_exist _ _ _ _ H0).
        inversion H2.
      - constructor.
        + assert (x1 = x0).
          apply functional_extensionality.
          intro.
          generalize (equal_f H1); intro.
          generalize (H3 x2); intro.
          inversion H4.
          reflexivity.
          subst.
          assumption.
        + eapply IHsub_tys; try eassumption.
          apply functional_extensionality.
          intro.
          generalize (equal_f H1); intro.
          generalize (H3 x2); intro.
          inversion H4.
          reflexivity.
      - generalize (H _ H3); intro; subst.
        generalize (equal_f H1); intro.
        destruct (type_variables_exist _ _ _ _ H4).
        inversion H5.
        reflexivity.
    Qed.

    Lemma TSub_eq_H4 : forall c m n t,
                         TSub_eq_Q c m n nil t nil (@Forall2_nil _ _ _).
      unfold TSub_eq_Q. intros.
      inversion H.
      reflexivity.
    Qed.

    Lemma TSub_eq_H5 : forall c m n t0 ts t t0' ts' sub_t0 sub_ts,
                         TSub_eq_P c m n t0 t t0' sub_t0 ->
                         TSub_eq_Q c m n ts t ts' sub_ts ->
                         TSub_eq_Q _ _ _ _ _ _ (Forall2_cons t0 t0' sub_t0 sub_ts).
      unfold TSub_eq_P; unfold TSub_eq_Q; intros.
      inversion H1; subst.
      generalize (H _ H4).
      generalize (H0 _ H6).
      intros; subst.
      reflexivity.
    Qed.

    Definition TSub_eq := TSub_rec _ _ TSub_eq_H1 TSub_eq_H2 TSub_eq_H3 TSub_eq_H4 TSub_eq_H5.


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
                                          Extract_tys _ mb Ds /\
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
      destruct (Term_subst_pres_types _ _ _ wf_mb _ _ _ _ H6 H7 ext_Ds sub_mb)
               as [d [wf_e' sub_d_b]].
      exists d. split.
      assumption.
      constructor 2 with (d:=b); assumption.
    Qed.






End FJ_Definition.



