Require Import FJ_tactics.
Require Import List.
Require Import Arith.Peano_dec.

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

  Inductive FD := fd : Ty -> F -> FD.

  Inductive E : Set :=
  | e_var : forall xt t, V xt t -> E
  | fd_access : E -> F -> E
  | m_call : E -> M -> list E -> E
  | new : Ty -> list E -> E.

  Inductive MB : x_this -> Set :=
  | mb_empty : E -> MB x
  | mb_var : forall t, (V x t -> MB x) -> MB x
  | mb_this : forall t, (V this t -> MB x) -> MB this.

  Inductive K := k : C -> list FD -> K.

  Inductive Mty := mty : list Ty -> Ty -> Mty.
  Inductive MD : Set := md : Ty -> M -> MB this -> MD.
  Inductive L : Set := cld : C -> Ty -> list FD -> K -> list MD -> L.


  Inductive Context : Set :=
  | ctxt_empty : E -> Context
  | ctxt_var : forall xt t, (V xt t -> Context) -> Context.
  
  Inductive MB2Context (c:Ty) : forall xt, MB xt -> Context -> Prop :=
  | mb_ctxt_nil : forall e, MB2Context c _ (mb_empty e) (ctxt_empty e)
  | mb_ctxt_var_cons :
      forall t vars ctxt,
        (forall v : V x t, MB2Context c _ (vars v) (ctxt v)) ->
        MB2Context c _ (mb_var t vars) (ctxt_var _ t ctxt)
  | mb_ctxt_this_cons :
      forall vars ctxt,
        (forall v : V this c, MB2Context c _ (vars v) (ctxt v)) ->
        MB2Context c _ (mb_this c vars) (ctxt_var _ c ctxt).

  Scheme MB2Context_rec := Induction for MB2Context Sort Prop.

  Inductive MB2Context_with : list Ty -> Ty -> forall xt, MB xt -> Context -> Prop :=
  | mb_ctxt_nil_with : forall c e, MB2Context_with nil c _ (mb_empty e) (ctxt_empty e)
  | mb_ctxt_var_with : 
      forall d Ds c vars ctxt,
        (forall v:V x d, MB2Context_with Ds c _ (vars v) (ctxt v)) ->
        MB2Context_with (d::Ds) c _ (mb_var _ vars) (ctxt_var _ _ ctxt)
  | mb_ctxt_this_with :
      forall Ds c vars ctxt,
        (forall v : V this c, MB2Context_with Ds c _ (vars v) (ctxt v)) ->
        MB2Context_with Ds c _ (mb_this _ vars) (ctxt_var _ _ ctxt). 

  Scheme MB2_Context_with_rec := Induction for MB2Context_with Sort Prop.


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

  Inductive ctxt_e_var : Context -> Ty -> Prop :=
  | var_empty : forall t v, ctxt_e_var (ctxt_empty (e_var x t v)) t
  | var_var : forall xt t ctxt,
                (forall v : V xt t, ctxt_e_var (ctxt v) t) ->
                ctxt_e_var (ctxt_var _ _ ctxt) t.
  
  Inductive ctxt_fd_access : Context -> F -> Context -> Prop :=
  | fd_empty : forall e f, 
                 ctxt_fd_access (ctxt_empty e) f (ctxt_empty (fd_access e f))
  | fd_var : forall xt t ctxt f ctxt',
                (forall v : V xt t, ctxt_fd_access (ctxt v) f (ctxt' v)) -> 
                ctxt_fd_access (ctxt_var _ _ ctxt) f (ctxt_var _ _ ctxt').

  Scheme ctxt_fd_access_rec := Induction for ctxt_fd_access Sort Prop.
  
  Inductive ctxt_m_call : Context -> M -> list Context -> Context -> Prop :=
  | m_empty : forall e m es,
                ctxt_m_call (ctxt_empty e) m (map (fun e => ctxt_empty e) es)
                            (ctxt_empty (m_call e m es))
  | m_var : forall xt t ctxt m ctxts ctxt',
              (forall v : V xt t, 
                 ctxt_m_call (ctxt v) m (map (fun ctxt => ctxt v) ctxts)
                             (ctxt' v)) ->
              ctxt_m_call (ctxt_var _ _ ctxt) m
                          (map (fun ctxt => ctxt_var _ _ ctxt) ctxts) 
                          (ctxt_var _ _ ctxt').
  Inductive ctxt_new : Ty -> list Context -> Context -> Prop :=
  | new_empty : forall t es, 
                  ctxt_new t (map (fun e => ctxt_empty e) es)
                           (ctxt_empty (new t es))
  | new_var : forall xt t t' ctxt ctxts,
                (forall v : V xt t, 
                   ctxt_new t' (map (fun ctxt => ctxt v) ctxts) (ctxt v)) ->
                ctxt_new t' (map (fun ctxt => ctxt_var xt t ctxt) ctxts) 
                         (ctxt_var xt t ctxt).

  Inductive WF_E : Context -> Ty -> Prop :=
  | T_Var : forall ctxt t, ctxt_e_var ctxt t -> WF_E ctxt t
  | T_Fields : forall ctxt ctxt' f c fds t i, 
                 ctxt_fd_access ctxt f ctxt' ->
                 WF_E ctxt c ->
                 fields c fds -> 
                 nth_error fds i = Some (fd t f) ->
                 WF_E ctxt' t
  | T_Invk : forall ctxt ty_0 U m Us Ss ctxts ctxt',
               ctxt_m_call ctxt m ctxts ctxt' ->
               WF_E ctxt ty_0 ->
               mtype m ty_0 (mty Us U) ->
               List_P2' WF_E ctxts Ss ->
               List_P2' subtype Ss Us ->
               WF_E ctxt' U
  | T_New : forall cl Ss fds ctxts ctxt,
              ctxt_new (ty_def cl) ctxts ctxt ->
              fields (ty_def cl) fds ->
              List_P2' WF_E ctxts Ss ->
              List_P2' 
                (fun S fd' => match fd' with fd T _ => subtype S T end) Ss fds ->
              WF_E ctxt (ty_def cl).

  Scheme WF_E_rec := Induction for WF_E Sort Prop.

  Definition Weakening_P ctxt t (wf_t : WF_E ctxt t) :=
    forall xt t, WF_E (ctxt_var xt t (fun v => ctxt)) t.

  Variable Weakening : forall ctxt t wf_t, Weakening_P ctxt t wf_t. 


  Definition Inv_T_Fields_P ctxt f ctxt' (ctxt_f : ctxt_fd_access ctxt f ctxt') :=
    forall c0 fds n t f,
      WF_E ctxt' t ->
      exists d : Ty, fields (ty_def c0) fds /\
                     nth_error fds n = Some (fd t f) /\
                     WF_E ctxt d.




  Lemma Inv_T_Fields_H2 : forall xt t ctxt f ctxt' c_fd,
                            (forall v, Inv_T_Fields_P (ctxt v) f (ctxt' v) (c_fd v)) ->
                            Inv_T_Fields_P _ _ _ (fd_var xt t _ _ _ c_fd).
    unfold Inv_T_Fields_P; intros.
    inversion H0; subst.
    
    inversion H2; subst.

    exists (ty_def c0).
    
*)


(*
  Lemma Inv_T_Fields : 
    forall c0 fds n ty f xt t ctxt ctxt' c3,
      fields (ty_def c0) fds ->
      nth_error fds n = Some (fd ty f) ->
      (forall v, ctxt_fd_access (ctxt v) f (ctxt' v)) ->
      WF_E (ctxt_var xt t ctxt') c3 ->
      ctxt_fd_access (ctxt_var xt t ctxt) f (ctxt_var xt t ctxt') ->
      exists d : Ty, WF_E (ctxt_var xt t ctxt) d.
    intros.
    
  c2 : ctxt_fd_access e0 f e1
  fields_fds : fields (ty_def c0) fds
  fds_n : nth_error fds n = Some (fd ty f)
  c3 : Ty
  H : WF_E e1 c3
  ========
  exists d : Ty, WF_e e0 d                                                

  fields_fds : fields (ty_def c0) fds
  fds_n : nth_error fds n = Some (fd ty f)
  H0 : forall v : V xt t, ctxt_fd_access (ctxt v) f (ctxt' v)
  H : WF_E (ctxt_var xt t ctxt') c3
  c1 : ctxt_new (ty_def c0) es (ctxt_var xt t ctxt)
  c2 : ctxt_fd_access (ctxt_var xt t ctxt) f (ctxt_var xt t ctxt')
  ======================
  exists d : Ty, WF_E (ctxt_var xt t ctxt) d

*)
  Definition override (m : M) (ty : Ty) (Ts : list Ty) (T : Ty) : Prop :=
    forall ds d, mtype m ty (mty ds d) -> T = d /\ Ts = ds.

  Inductive Meth_WF : C -> MD -> Prop :=
  | T_MD : forall (mb:MB this) (ctxt:Context) (e_0 c_0 :Ty) (c:C)
                  (d:CL) (fds:list FD) (k':K) (mds:list MD) (m:M) tys,
      MB2Context (ty_def (cl c)) this mb ctxt ->
      Extract_tys _ mb tys ->
      WF_E ctxt e_0 ->
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
  | S_var_neq : forall xt t (v:V xt t) e, Sub (fun _ _ _ => e_var _ _ v) e (e_var _ _ v)
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

  Inductive Subst0 : Context -> Context -> Context -> Type :=
  | Sub0_empty : forall xt t e0 e e0', 
                   Sub e0 e e0' ->
                   Subst0 (ctxt_var _ _ (fun v => ctxt_empty (e0 xt t v))) 
                          (ctxt_empty e) (ctxt_empty e0')
  | Sub0_var : forall (xt:x_this) (t:Ty) (ctxt ctxt0 ctxt' : V xt t -> Context),
                 (forall (v : V xt t), Subst0 (ctxt v) (ctxt0 v) (ctxt' v)) ->
                 Subst0 (ctxt_var _ _ ctxt) (ctxt_var _ _ ctxt0) (ctxt_var _ _ ctxt').

  Section Example3.
    Variable d : E.

    Example c : forall xt t,
                  Subst0 (ctxt_var _ _ (fun x => ctxt_empty (e_var xt t x))) (ctxt_empty d)
                         (ctxt_empty d).
    intros. constructor. constructor. Qed.

    Example e : forall xt t, 
                  Subst0
                    (ctxt_var xt t (fun (y : V xt t) => ctxt_var xt t (fun x => ctxt_empty (e_var _ _ y)))) (ctxt_var xt t (fun y => ctxt_empty d)) (ctxt_var _ _ (fun y => ctxt_empty (e_var xt t y))).
    Proof.
    intros. apply Sub0_var. intros. 
    apply Sub0_empty with (e0 := (fun _ _ _ => e_var xt t v)). constructor.
    Qed.
  End Example3.

  Inductive Subst : Context -> list Context -> Context -> Type :=
  | Sub_one : forall ctxt e ctxt', Subst0 ctxt e ctxt' ->
                                   Subst ctxt (e::nil) ctxt'
  | Sub_cons : forall ctxt ctxt' ctxt'' e es,
                 Subst ctxt es ctxt' ->
                 Subst0 ctxt' e ctxt'' ->
                 Subst ctxt (e::es) ctxt''.


  
  Inductive Reduce : Context -> Context -> Prop :=
  | R_Field : forall c ty fds es f e0 n e e',
                ctxt_new (ty_def c) es e0 ->
                ctxt_fd_access e0 f e ->
                fields (ty_def c) fds ->
                nth_error fds n = Some (fd ty f) -> 
                nth_error es n = Some e' ->
                Reduce e e'
  | R_Invk : forall m (c:CL) mb ctxt es ds e0 e e',
                    ctxt_new (ty_def c) es e0 ->
                    ctxt_m_call e0 m ds e ->
                    mbody m (ty_def c) mb ->
                    MB2Context (ty_def c) _ mb ctxt ->
                    Subst ctxt (e0::ds) e' ->
                    Reduce e e'.

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
      induction sub_S_T; auto. rename c0 into c.
      destruct (In_m_mds_dec m mds) as [[ty [mb In_m]] | Not_In_m].
      generalize (WF_CT _ _ H0); intro WF_c. inversion WF_c. subst.
      clear CT_self.
      generalize (H8 _ In_m); intro WF_m. inversion WF_m; subst.
      rewrite H13 in H0. inversion H0. subst.
      unfold override in H14. destruct (H14 Us U H); subst.
      eapply mtype_fnd; eassumption.
      eapply mtype_not_fnd; eassumption.
    Qed.




    Lemma Lem_1_4 : 
      forall m c0 mb, 
        mbody m c0 mb -> 
        forall Ds d, mtype m c0 (mty Ds d) ->
                     exists d0, exists c, exists ctxt,
                                            subtype c0 d0 /\ subtype c d /\
                                            MB2Context d0 _ mb ctxt /\ 
                                            Extract_tys _ mb Ds /\
                                            WF_E ctxt c.    
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
      rewrite H25 in H19. inversion H19; subst. clear H19.
      rewrite H in H25. inversion H25; subst. clear H25.
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
      destruct H5; subst. clear H H2 H3 H11 H12 H13 H14 H20 H26.
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
        as [d0' [c [ctxt [sub_d1_d0' [sub_c_d [mb'2ctxt [ext_Ds WF_c]]]]]]].
      repeat eexists; eauto.
      destruct d1.
      constructor 2 with (d:=ty_def c1).
      eapply sub_class; eauto. assumption.
    Qed.


    Definition pres_P ctxt ctxt' (red_c : Reduce ctxt ctxt') :=
      forall c, WF_E ctxt c -> exists d, WF_E ctxt' d /\ subtype d c.

    Lemma pres_H1 : forall c ty fds es f e0 n e e' c0 c1 fields_fds fds_n es_n,
                      pres_P _ _ (R_Field c ty fds es f e0 n e e' c0 c1 fields_fds fds_n es_n).
      unfold pres_P; intros.
      inversion c2; subst.
      inversion H; inversion H0; subst.
      inversion c1; subst.
      inversion H1; inversion H4; subst.
      admit.



      inversion H. subst. inversion H1; subst.
      exists ty. split.
      econstructor 2.

    Lemma preservation : forall ctxt ctxt' c,
                           WF_E ctxt c -> Reduce_Context ctxt ctxt' ->
                           exists d, WF_E ctxt' d /\ subtype d c.
      intros.
      induction H0.
      admit.
      inversion H; subst.
      

      induction H0.
      Case "R_field".
      rename c0 into c. rename c1 into c0. rename n into i.
      inversion H; inversion H3; subst.
      rename c1 into d0.
      inversion H4; inversion H7. subst.
      rename Ss into Cs.
      generalize (Fields_eq _ _ H0 _ H8); intros.
      generalize (Fields_eq _ _ H5 _ H8); intros. subst.
      clear H5 H8.
      apply P2'_if_P2 in H9; unfold List_P2 in H9; destruct H9 as [fnd_es not_fnd_es].
      assert (nth_error (map(fun e => ctxt_empty e)es) i = Some (ctxt_empty e0)).
      generalize es i H2; clear.
      induction es; induction i; intros; inversion H2; subst; try reflexivity.
      apply (IHes _ H0).
      destruct (fnd_es _ _ H5) as [d [In_Cs WF_e]].
      exists d. split. assumption.
      rewrite <- (fds_distinct _ _ H0 _ _ _ _ _ _ (refl_equal _) H1 H6) in H6.
      apply P2'_if_P2 in H10; unfold List_P2 in H10; destruct H10 as [fnd_Cs not_fnd_Cs].      
      destruct (fnd_Cs _ _ In_Cs) as [fd' [fds_1_i sub_d_f]].
      rewrite fds_1_i in H6. inversion H6. subst.
      assumption.
      Case "R_Invk".
      inversion H; inversion H3; subst.
      rename c0 into c. rename c1 into c0. rename e0 into e'. rename Us into Ds.
      rename Ss into Cs.
      inversion H4; inversion H8; subst.
      destruct (Lem_1_4 _ _ _ H0 _ _ H5)
        as [d0 [b [ctxt' [sub_c0_d0 [sub_b_c [mb2ctxt' [extr_Ds WF_ctxt']]]]]]].
      



End FJ_Definition.



