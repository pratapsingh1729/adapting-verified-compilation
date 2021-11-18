(** A library of relation operators defining sequences of transitions
  and useful properties about them. *)

(** This file includes code drawn from the Coq development of the
    paper:
    Trace-relating compiler correctness and secure compilation. 
    Carmine Abate, Roberto Blanco, Ștefan Ciobâcă, Adrien Durier, 
    Deepak Garg, Cătălin Hriţcu, Marco Patrignani, Éric Tanter, 
    and Jérémy Thibault. ESOP 2020.
    The Coq development is available at
    https://github.com/secure-compilation/different_traces.
    We modify and adjust some definitions to match our conventions.
*)


Require Import Classical ClassicalEpsilon.
From Coq Require Import String ZArith List Streams.
Require Import Integers.
Require Import Program.Equality. 
Import ListNotations.
Set Implicit Arguments.

(* We model the external world state as containing the next input to
provide the program, the next global state to step to after providing
an input, and a function to produce the next global state after
receiving an output. *)
CoInductive global_state : Type :=
| global_state_with_input (z : Z) (n : global_state) (f : Z -> global_state).

(* Provide an input for the program to take *)
Definition take_input (g : global_state) : Z * global_state :=
  match g with
  | global_state_with_input z n _ =>
    (z, n)
  end.

(* Receive an output from the program and generate a new global state *)
Definition produce_output (g : global_state) (n : Z) : global_state :=
  match g with
  | global_state_with_input _ _ f => f n
  end.

(* events: input or output an integer, or interrupt *)
Inductive event : Type :=
| ev_input : Z -> event
| ev_output : Z -> event
| ev_intr : event.

(* trace of events during execution of program *)
Definition trace := list event.
Definition inftrace := Stream event.

Section SEQUENCES.

(* the type of states *)
Variable A: Type.                 

(* the transition relation, from one state to the next, optionally emitting an event *)
Variable R: A -> option event -> A -> Prop.       

(** ** Finite sequences of transitions *)

(** Zero, one or several transitions: reflexive, transitive closure of [R]. *)

Inductive star: A -> trace -> A -> Prop :=
  | star_refl: forall a,
      star a [] a
  | star_step: forall a b c t,
      R a None b -> star b t c -> star a t c
  | star_step_ev: forall a b c e t,
      R a (Some e) b -> star b t c -> star a (e :: t) c.

Lemma star_one:
  forall (a b: A), R a None b -> star a [] b.
Proof.
  eauto using star.
Qed.

Lemma star_one_ev:
  forall (a b: A) e, R a (Some e) b -> star a [e] b.
Proof.
  eauto using star.
Qed.

Lemma star_trans:
  forall (a b: A) t1 t2, star a t1 b -> forall c, star b t2 c -> star a (t1 ++ t2) c.
Proof.
  induction 1; eauto using star. 
Qed.

Lemma star_trans_nil:
  forall (a b: A), star a nil b -> forall c, star b nil c -> star a nil c.
Proof.
  intros.
  replace ([]:trace) with (([] ++ []):trace); eauto using star_trans.  
Qed.

Lemma star_int:
  forall a c t, star a t c -> forall t' t'', t = t' ++ t'' -> exists b, star a t' b.
Proof.
  induction 1; intros.
  - exists a. symmetry in H; destruct (app_eq_nil _ _ H). rewrite H0; econstructor. 
  - destruct (IHstar _ _ H1) as (b0 & ?). exists b0; econstructor; eauto. 
  - destruct t'.
    + exists a; econstructor. 
    + rewrite <- app_comm_cons in H1.
      inversion H1; rewrite H3 in *; rewrite H4 in *.
      destruct (IHstar t' t'') as (b0 & ?); try easy.
      exists b0; eapply star_step_ev; eauto. 
Qed.

(** One or several transitions: transitive closure of [R]. *)

Inductive plus: A -> trace -> A -> Prop :=
  | plus_left: forall a b c t,
      R a None b -> star b t c -> plus a t c
  | plus_left_ev: forall a b c e t,
      R a (Some e) b -> star b t c -> plus a (e :: t) c.

Lemma plus_one:
  forall a b, R a None b -> plus a [] b.
Proof.
  eauto using star, plus. 
Qed.

Lemma plus_one_ev:
  forall a b e, R a (Some e) b -> plus a [e] b.
Proof.
  eauto using star, plus. 
Qed.

Lemma plus_star:
  forall a b t,
  plus a t b -> star a t b.
Proof.
  intros. inversion H; eauto using star.
Qed.

Lemma plus_star_trans:
  forall a b c t1 t2, plus a t1 b -> star b t2 c -> plus a (t1 ++ t2) c.
Proof.
  intros. inversion H; eauto using plus, star_trans.
Qed.

Lemma star_plus_trans:
  forall a b c t1 t2, star a t1 b -> plus b t2 c -> plus a (t1 ++ t2) c.
Proof.
  intros. inversion H0; inversion H; eauto using plus, star, star_trans.
Qed.

Lemma plus_right:
  forall a b c t, star a t b -> R b None c -> plus a t c.
Proof.
  intros. replace t with (t ++ []) by auto using app_nil_r.
  eauto using star_plus_trans, plus_one, plus_one_ev.
Qed.

Lemma plus_right_ev:
  forall a b c t e, star a t b -> R b (Some e) c -> plus a (t ++ [e]) c.
Proof.
  eauto using star_plus_trans, plus_one, plus_one_ev.
Qed.

Lemma star_inv : forall a t b,
    star a t b ->
    (a = b /\ t = []) \/ plus a t b.
Proof.
  intros; inversion H; subst;
    try solve [left; auto];
    right; [eapply plus_left | eapply plus_left_ev]; eauto.
Qed.

(** No transitions from a state. *)

Definition irred (a: A) : Prop := forall b eo, ~(R a eo b).

(** ** Infinite sequences of transitions *)


Definition all_seq_inf (a: A) : Prop :=
  forall t b, star a t b -> exists eopt c, R b eopt c.

CoInductive infseq: A -> inftrace -> Prop :=
| infseq_step: forall a b t,
    R a None b -> infseq b t -> infseq a t
| infseq_step_ev: forall a e b t,
    R a (Some e) b -> infseq b t -> infseq a (Cons e t).

Definition cons_to_itr (eopt : option event) (t : inftrace) : inftrace :=
  match eopt with
  | Some e => Cons e t
  | None => t
  end.

Fixpoint app_to_itr (t : trace) (it : inftrace) :=
  match t with
  | nil => it
  | e :: t' => Cons e (app_to_itr t' it)
  end.

(* Adapted from different traces paper ResourceExhaustion/Sequences.v *)
CoInductive infseq_N : A -> nat -> inftrace -> Prop :=
| infseq_N_star : forall a b n1 n2 l s,
    n2 < n1 ->
    star a l b ->
    infseq_N b n2 s ->
    infseq_N a n1 (app_to_itr l s)
| infseq_N_plus : forall a b n1 n2 l s,
    plus a l b ->
    infseq_N b n2 s ->
    infseq_N a n1 (app_to_itr l s).

Lemma infseq_N_inv : forall n s a,
    infseq_N a n s ->
    exists eo, exists s', exists n', exists a',
            R a eo a' /\ infseq_N a' n' s' /\ cons_to_itr eo s' = s.
Proof.
  intros n. pattern n.
  eapply well_founded_ind with (R := lt).
  apply PeanoNat.Nat.lt_wf_0.
  intros x H s a H0.
  inversion H0; subst; clear H0.
  - inversion H2; subst; clear H2.
    + apply H with n2. now apply H1.
      apply H3.
    + exists None. exists (app_to_itr l s0). exists x. exists b0.
      repeat split; eauto.
      eapply infseq_N_star; eauto.
    + exists (Some e). exists (app_to_itr t s0). exists x. exists b0.
      repeat split; eauto.
      eapply infseq_N_star; eauto.
  - inversion H1; subst; clear H1.
    + exists None, (app_to_itr l s0), n2, b0.
      repeat split; eauto.
      inversion H3; subst; clear H3.
      assumption.
      eapply infseq_N_plus; eauto.
      econstructor; eauto.
      eapply infseq_N_plus; eauto.
      eapply plus_left_ev; eauto.
    + exists (Some e), (app_to_itr t s0), n2, b0.
      repeat split; eauto.
      inversion H3; subst; clear H3.
      assumption.
      eapply infseq_N_plus; eauto.
      econstructor; eauto.
      eapply infseq_N_plus; eauto.
      eapply plus_left_ev; eauto.
Qed.

Lemma infseq_N_infseq :
  forall a s n, infseq_N a n s -> infseq a s.
Proof.
  cofix Hfix.
  intros a s n H.
  destruct (infseq_N_inv H) as [l [s' [n' [a' [HR [Hinf Heq]]]]]].
  subst. destruct l.
  - apply infseq_step_ev with (b := a').
    eauto. eapply Hfix; eauto.
  - apply infseq_step with (b := a').
    eauto. eapply Hfix; eauto.
Qed.

Lemma infseq_infseq_N :
  forall a n s, infseq a s -> infseq_N a n s.
Proof.
  cofix Hfix.
  intros a n s H.
  inversion H; subst.
  - replace s with (app_to_itr [] s) by auto. 
    eapply infseq_N_plus with (n2 := 0).
    replace [] with ((nil:trace) ++ []) by now rewrite app_nil_r.
    econstructor. eauto. econstructor.
    eapply Hfix. eauto.
  - replace (Cons e t) with (app_to_itr [e] t) by auto.
    eapply infseq_N_plus with (n2 := 0).
    replace [] with ((nil:trace) ++ []) by now rewrite app_nil_r.
    eapply plus_left_ev. eauto. cbn; econstructor. 
    eapply Hfix. eauto.
Qed.

Lemma app_to_itr_app_distrib: forall t t' it,
    app_to_itr t (app_to_itr t' it) = app_to_itr (t ++ t') it.
Proof.
  induction t; cbn; auto. intros. now rewrite IHt. 
Qed. 

Lemma star_infseq_trans: forall a t b it,
    star a t b -> infseq b it -> infseq a (app_to_itr t it).
Proof.
  induction 1; intros.
  - now cbn.
  - eapply infseq_step; eauto.
  - eapply infseq_step_ev; eauto.
Qed. 

Lemma infseq_coinduction_principle:
  forall (X: A -> inftrace -> Prop),
  (forall a t, X a t -> exists b eo t', R a eo b /\ X b t' /\ t = cons_to_itr eo t') ->
  forall a t, X a t -> infseq a t.
Proof.
  intros X P. cofix COINDHYP; intros.
  destruct (P a t H) as [b [eo [t' [HR [HX Happ]]]]].
  destruct eo; cbn in Happ; subst t.
  - apply infseq_step_ev with b; auto.
  - apply infseq_step with b; auto. 
Qed.

Lemma infseq_coinduction_principle_2:
  forall (X: A -> inftrace -> Prop),
  (forall a t, X a t -> exists b t' t'', plus a t' b /\ X b t'' /\ t = app_to_itr t' t'') ->
  forall a t, X a t -> infseq a t.
Proof.
  intros.
  apply infseq_coinduction_principle with
      (X := fun a t => exists b t' t'', star a t' b /\ X b t'' /\ t = app_to_itr t' t'').
  - intros.
    destruct H1 as [b [t' [t'' [STAR [Xb Ht0]]]]].
    inversion STAR; subst; try solve [ eauto 20 ].
    destruct (H b t'' Xb) as [c [t'0 [t''0 [PLUS [Xc Ht'0]]]]].
    inversion PLUS; subst; eauto 20. 
  - exists a, [], t; split; auto using star_refl.
Qed.


(* Silent divergence *)
CoInductive infseq_silent : A -> Prop :=
| infseq_silent_step :
    forall a b, R a None b -> infseq_silent b -> infseq_silent a.

Remark cycle_infseq_silent:
  forall a, R a None a -> infseq_silent a.
Proof.
  intros. cofix CIH. apply infseq_silent_step with a. auto. apply CIH.
Qed.

Lemma infseq_silent_coinduction_principle:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, R a None b /\ X b) ->
  forall a, X a -> infseq_silent a.
Proof.
  intros X P. cofix COINDHYP; intros.
  destruct (P a H) as [b [HR HX]].
  econstructor; eauto. 
Qed.

Lemma infseq_silent_coinduction_principle_2:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, plus a [] b /\ X b) ->
  forall a, X a -> infseq_silent a.
Proof.
  intros.
  apply infseq_silent_coinduction_principle with
      (X := fun a => exists b, star a [] b /\ X b).
  - intros.
    destruct H1 as [b [STAR Xb]].
    inversion STAR; subst; try solve [ eauto 20 ].
    destruct (H b Xb) as [c [PLUS Xc]].
    inversion PLUS; subst; eauto 20. 
  - exists a; split; eauto using star. 
Qed.

Lemma infseq_silent_implies_infseq :
  forall a t, infseq_silent a -> infseq a t.
Proof.
  cofix CIH.
  intros a t H.
  inversion H; subst.
  replace t with (app_to_itr [] t) by reflexivity.
  econstructor; eauto.
Qed.

Lemma infseq_silent_coind :
  forall P a t, (infseq a t -> P a) ->
           (infseq_silent a -> P a).
Proof.
  auto using infseq_silent_implies_infseq.
Qed.


Lemma infseq_silent_if_all_silent_inf:
  forall a,
    (forall t b, star a t b -> exists c, R b None c) ->
    infseq_silent a.
Proof.
  cofix CIH; intros.
  destruct (H [] a) as [b H']; try constructor.
  econstructor; eauto. 
  apply CIH. eauto using star_step. 
Qed.

Definition diverges_silently (a : A) (t : trace) :=
  exists b, star a t b /\ infseq_silent b. 

(* Diverges with infinite sequence of events (i.e. reacts) *)
CoInductive infseq_with_inftrace : A -> inftrace -> Prop :=
| infseq_with_inftrace_plus: forall a t b it,
    plus a t b -> t <> [] ->
    infseq_with_inftrace b it ->
    infseq_with_inftrace a (app_to_itr t it).

Lemma infseq_with_inftrace_coinduction_principle:
  forall (X: A -> inftrace -> Prop),
  (forall a t, X a t -> exists b t' t'', plus a t' b /\ X b t'' /\ t = app_to_itr t' t'' /\ t' <> []) ->
  forall a t, X a t -> infseq_with_inftrace a t.
Proof.
  intros X P. cofix CIH; intros.
  destruct (P a t H) as (b & t' & t'' & Hplus & HX & Happ & Ht').
  rewrite Happ; econstructor; eauto.
Qed. 

Lemma star_infseq_with_inftrace: forall (a b : A) (t : trace) (it : inftrace),
    star a t b -> infseq_with_inftrace b it ->
    infseq_with_inftrace a (app_to_itr t it).
Proof.
  intros. inversion H0; subst.
  assert (plus a (t ++ t0) b0) by eauto using star_plus_trans.
  rewrite app_to_itr_app_distrib.   
  econstructor; eauto.
  intuition. destruct (app_eq_nil _ _ H5); congruence. 
Qed.

Lemma infseq_with_inftrace_implies_infseq : forall a it,
    infseq_with_inftrace a it ->
    infseq a it.
Proof.
  assert (forall a n s, infseq_with_inftrace a s -> infseq_N a n s).
  {
    cofix Hfix.
    intros a n s H.
    inversion H; subst.
    destruct t as [| e l]; try congruence.
    replace (app_to_itr (e :: l) it) with (app_to_itr ([e] ++ l) it) in H by reflexivity.
    inversion H0; subst; clear H0.
    - eapply infseq_N_plus.
      + eapply plus_left; eauto.
      + eapply Hfix; eauto.
    - eapply infseq_N_plus.
      + eapply plus_left_ev; eauto.
      + eapply Hfix; eauto. 
  }
  intros s a H0.
  eapply infseq_N_infseq.
  eapply H.
  eassumption.
  Unshelve.
  all: exact 0.
Qed.

CoInductive stream' :=
| scons' : forall (t : trace) (s : stream'), t <> [] -> stream'.

Program Definition split_inftrace' (t : trace) (s: stream') (NE: t <> []): event * stream' :=
  match t with
  | nil => _
  | e :: nil => (e, s)
  | e :: t' => (e, @scons' t' s _)
  end.
Next Obligation.
  destruct t'; congruence.
Qed.

CoFixpoint stream_of_stream' (s': stream') : inftrace :=
  match s' with
  | @scons' t T'' NOTEMPTY =>
    let (e, tl) := @split_inftrace' t T'' NOTEMPTY in
    Cons e (stream_of_stream' tl)
  end.

Remark unroll_stream':
  forall T, T = match T with @scons' t T' NE => @scons' t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma stream_stream'_app:
  forall t T NE,
    stream_of_stream' (@scons' t T NE) = app_to_itr t (stream_of_stream' T).
Proof.
  induction t.
  intros. elim NE. auto.
  intros. simpl.
  rewrite (unfold_Stream (stream_of_stream' (@scons' (a :: t) T NE))).
  simpl. destruct t. auto.
  simpl. f_equal. apply IHt.
Qed.

Section REACTS.
Variable a : A.
Hypothesis reacts:
  forall t b, star a t b ->
           exists t' c, plus b t' c /\ t' <> [].

Lemma reacts':
  forall t b, star a t b ->
           { c & { t' : trace | plus b t' c /\ t' <> [] } }.
Proof.
  intros.
  destruct (constructive_indefinite_description _ (reacts H)) as [t' H'].
  destruct (constructive_indefinite_description _ H') as [c [Hplus Ht']].
  exists c; exists t'; auto.
Qed.

Lemma not_nil_nil : (@nil event) <> [] -> False.
Proof.
  congruence.
Qed.

CoFixpoint build_stream' t b (ST: star a t b) : @stream' :=
  match (reacts' ST) with
  | existT _ s2 (exist _ t2 (conj A B)) =>
    @scons' t2 (build_stream' (plus_star (star_plus_trans ST A))) B
  end.

Lemma reacts_forever_reactive_rec:
  forall t b (ST : star a t b),
    infseq_with_inftrace b (stream_of_stream' (build_stream' ST)).
Proof.
  cofix COINDHYP; intros.
  rewrite (unroll_stream' (build_stream' ST)).
  simpl.
  destruct (reacts' ST) as [s2 [t2 [H1 H2]]].
  rewrite stream_stream'_app.
  econstructor. eassumption. auto. apply COINDHYP.
Qed.

Lemma reacts_forever_reactive:
  exists it, infseq_with_inftrace a it.
Proof.
  exists (stream_of_stream' (build_stream' (star_refl _))).
  apply reacts_forever_reactive_rec.
Qed.
End REACTS. 

(* Every state either terminates on an irreducible state, emits a
finite trace then diverges silently, or diverges with an infinite
sequence of events. *)
Lemma infseq_or_finseq: forall a,
    (exists t b, star a t b /\ irred b) \/
    (exists t, diverges_silently a t) \/
    (exists it, infseq_with_inftrace a it).
Proof.
  intros.
  destruct (classic (forall t b, star a t b -> exists eo c, R b eo c)).
  - destruct (classic (exists t b, star a t b /\ (forall t' c, star b t' c -> exists d, R c None d))).
    + right; left.  destruct H0 as (t & b & Htb & Hc).
      exists t; unfold diverges_silently; exists b; split; eauto.
      now apply infseq_silent_if_all_silent_inf.
    + right; right. eapply reacts_forever_reactive. intros.
      generalize (not_ex_all_not _ _ H0 t). intro; clear H0.
      generalize (not_ex_all_not _ _ H2 b). intro; clear H2.
      destruct (not_and_or _ _ H0); try contradiction.
      destruct (not_all_ex_not _ _ H2) as [t' C]; clear H0.
      destruct (not_all_ex_not _ _ C) as [c D]; clear C.
      destruct (imply_to_and _ _ D) as [E F]; clear D.
      destruct (H (t ++ t') c) as [eo [d G]]. eapply star_trans; eauto.
      destruct eo.
      * exists (t' ++ [e]), d; split; eauto using plus_star_trans, plus_right_ev.
        intuition. destruct (app_eq_nil _ _ H0); subst; congruence.
      * exists (t'), d; split; eauto using plus_right. 
  - left. apply not_all_ex_not in H. destruct H as (t & P).
    apply not_all_ex_not in P. destruct P as (b & P).
    generalize (imply_to_and _ _ P). intros [U V].
    exists t, b; split. auto.
    red; intros; red; intros. elim V. exists eo, b0; auto.
Qed.

(** ** Determinism properties for functional transition relations. *)

(** A transition relation is functional if every state can transition to at most
  one other state. *)

Hypothesis R_functional:
  forall a b c eo1 eo2, R a eo1 b -> R a eo2 c -> b = c /\ eo1 = eo2.

(** Uniqueness of finite transition sequences. *)

Lemma star_star_inv:
  forall a b t1, star a t1 b -> forall c t2, star a t2 c ->
                                  (exists t, star b t c /\ t2 = t1 ++ t)
                                  \/ (exists t, star c t b /\ t1 = t2 ++ t).
Proof.
  induction 1; intros.
- left. eexists; eauto.
- inversion H1; subst.
  + right. eauto using star. 
  + assert (b = b0) by (eapply R_functional; eauto). subst b0. 
    apply IHstar; auto.
  + apply (R_functional H) in H2. destruct H2. discriminate.
- inversion H1; subst.
  + right. eauto using star.
  + apply (R_functional H) in H2. destruct H2. discriminate.
  + assert (b = b0) by (eapply R_functional; eauto). subst b0.
    assert (e = e0).
    { specialize (R_functional H H2). destruct R_functional; injection H5; auto. }
    subst e0.
    apply IHstar in H3. destruct H3.
    * left. destruct H3. exists x. rewrite <- app_comm_cons.
      destruct H3. split; try easy. rewrite H4; congruence.
    * right. destruct H3. exists x. rewrite <- app_comm_cons.
      destruct H3. split; try easy. rewrite H4; congruence. 
Qed.

Lemma finseq_unique:
  forall a b b' t t',
  star a t b -> irred b ->
  star a t' b' -> irred b' ->
  b = b' /\ t = t'.
Proof.
  intros. destruct (star_star_inv H H1).
  - destruct H3. destruct H3. inversion H3; subst; try elim (H0 _ _ H5).
    split; try rewrite app_nil_r; auto.
  - destruct H3. destruct H3. inversion H3; subst; try elim (H2 _ _ H5).
    split; try rewrite app_nil_r; auto.
Qed.

(** A state cannot both diverge and terminate on an irreducible state. *)

Lemma infseq_star_inv:
  forall a b t t', star a t' b -> infseq a t -> exists t'', infseq b t'' /\ t = app_to_itr t' t''.
Proof.
  intros until 1. generalize dependent t. dependent induction H; intros.
  - eauto.
  - inversion H1; subst.
    + assert (b = b0) by (eapply R_functional; eauto). subst b0.
      apply IHstar; auto.
    + assert (None = Some e) by (eapply R_functional; eauto). inversion H4. 
  - inversion H1; subst.
    + assert (None = Some e) by (eapply R_functional; eauto). inversion H4.
    + assert (b = b0) by (eapply R_functional; eauto). subst b0.
      assert (e = e0) by (specialize (R_functional H H2); destruct R_functional; congruence). subst e0. 
      apply IHstar in H3. destruct H3 as [t'' H3]. exists t''. 
      destruct H3. split; eauto. cbn. now rewrite H4. 
Qed.

Lemma infseq_finseq_excl:
  forall a t b t',
  star a t b -> irred b -> infseq a t' -> False.
Proof.
  intros.
  assert (exists t'', infseq b t'' /\ t' = app_to_itr t t'') by (eapply infseq_star_inv; eauto).
  destruct H2 as [t'' [H2 H2']]. inversion H2; subst; now apply H0 in H3. 
Qed.

Lemma infseq_silent_star_inv:
  forall a b t, star a t b -> infseq_silent a -> infseq_silent b.
Proof.
  intros until 1. dependent induction H; intros.
  - eauto.
  - inversion H1; subst.
    assert (b = b0) by (eapply R_functional; eauto). subst b0.
    apply IHstar; auto.
  - inversion H1; subst.
    assert (None = Some e) by (eapply R_functional; eauto); congruence.
Qed.

Lemma infseq_silent_star_inv':
  forall a b t, star a t b -> infseq_silent a -> t = [].
Proof.
  intros until 1. dependent induction H; intros.
  - eauto.
  - apply IHstar. eapply infseq_silent_star_inv; eauto.
    eapply star_step. eapply H. eapply star_refl. 
  - inversion H1; subst.
    assert (None = Some e) by (eapply R_functional; eauto); congruence.
Qed.

Lemma infseq_silent_finseq_excl:
  forall a t b,
  star a t b -> irred b -> infseq_silent a -> False.
Proof.
  intros.
  assert (infseq_silent b) by (eapply infseq_silent_star_inv; eauto).
  inversion H2; subst; now apply H0 in H3. 
Qed.

Lemma diverges_silently_finseq_excl:
  forall a t b t',
    star a t b -> irred b -> diverges_silently a t' -> False.
Proof.
  intros. unfold diverges_silently in H1. destruct H1 as (b' & ? & ?).
  apply star_star_inv with (b := b) (t1 := t) in H1; auto.
  destruct H1.
  - destruct H1 as (t0 & Hstar & Happ).
    unfold irred in H0. inversion Hstar; subst; try (now apply H0 in H1).
    inversion H2; subst. now apply H0 in H1.
  - destruct H1 as (t0 & Hstar & Happ).
    assert (infseq_silent b) by (eapply infseq_silent_star_inv; eauto).
    inversion H1; subst; now apply H0 in H3. 
Qed.

Lemma infseq_with_inftrace_inv : forall a t1 b,
    star a t1 b ->
    forall c t2 it1 it2,
      star a t2 c ->
      t1 <> [] -> t2 <> [] ->
      infseq_with_inftrace b it1 ->
      infseq_with_inftrace c it2 ->
      exists a', exists t, exists it1', exists it2',
              t <> [] /\
              infseq_with_inftrace a' it1' /\ infseq_with_inftrace a' it2' /\
              app_to_itr t1 it1 = app_to_itr t it1' /\
              app_to_itr t2 it2 = app_to_itr t it2'.
Proof.
  induction 1; intros; try congruence.
  - inversion H1; subst; try congruence.
    + assert (b = b0 /\ None = None) as [? _] by eauto using R_functional; subst. 
      eapply IHstar; eauto.
    + assert (b = b0 /\ None = Some e) as [? ?] by eauto using R_functional; congruence.
  - inversion H1; subst; try congruence.
    + assert (b = b0 /\ Some e = None) as [? ?] by eauto using R_functional; congruence.
    + assert (b = b0 /\ Some e = Some e0) as [? ?] by eauto using R_functional.
      inversion H9; subst.
      exists b0. exists [e0]. exists (app_to_itr t it1). exists (app_to_itr t0 it2).
      repeat split; try congruence; eauto using star_infseq_with_inftrace.
Qed.

Lemma star_infseq_with_inftrace_inv : forall a t b,
    star a t b ->
    forall it, infseq_with_inftrace a it ->
          exists it', infseq_with_inftrace b it' /\ it = app_to_itr t it'.
Proof. 
  induction 1; intros.
  - eexists; cbn; eauto.
  - inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    + assert (b1 = b) by (now eapply R_functional; eassumption); subst.
      specialize (IHstar (app_to_itr t0 it0)).
      eapply IHstar. eapply star_inv in H5. destruct H5; try (destruct H2; congruence).
      econstructor; eauto. 
    + assert (b = b1 /\ None = Some e) as [? ?] by eauto using R_functional; congruence. 
  - inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    + assert (b = b1 /\ Some e = None) as [? ?] by eauto using R_functional; congruence. 
    + assert (b1 = b /\ Some e0 = Some e) as [? ?] by eauto using R_functional; inversion H6; subst.
      eapply star_infseq_with_inftrace in H5; eauto. apply IHstar in H5. 
      destruct H5 as (it' & ? & ?).
      exists it'; split; auto. cbn. rewrite H5; auto. 
Qed.

Lemma infseq_with_inftrace_star_inv'_oneev:
  forall a e it, infseq_with_inftrace a (Cons e it) -> exists b, star a [e] b.
Proof.
  intros. inversion H; subst. destruct t; try congruence.
  cbn in H0. inversion H0; subst.
  inversion H1; subst.
  - replace (e :: t) with ([e] ++ t) in H5 by auto.
    apply star_int with (t' := [e]) (t'' := t) in H5; auto.
    destruct H5 as (b' & ?). exists b'; eapply star_step; eauto.
  - exists b0. eapply star_step_ev; eauto. eapply star_refl.
Qed. 

Lemma infseq_with_inftrace_star_inv':
  forall t it' it, it = app_to_itr t it' -> forall a, infseq_with_inftrace a it -> exists b, star a t b.
Proof.
  induction t; intros. 
  - exists a; constructor.
  - cbn in H. pose proof H0. rewrite H in H1.
    apply infseq_with_inftrace_star_inv'_oneev in H1. destruct H1 as (b' & ?).
    pose proof H1. eapply star_infseq_with_inftrace_inv in H2; eauto.
    destruct H2 as (it'' & ? & ?). cbn in H3.
    assert (it'' = app_to_itr t it').
    { rewrite H3 in H. inversion H; now subst. } 
    specialize (IHt _ _ H4 _ H2). destruct IHt as (b & ?).
    exists b. replace (a :: t) with ([a] ++ t) by auto. eapply star_trans; eauto.     
Qed.

Lemma infseq_with_inftrace_star_inv:
  forall a it, infseq_with_inftrace a it -> forall t it', it = app_to_itr t it' -> exists b, star a t b.
Proof.
  eauto using infseq_with_inftrace_star_inv'. 
Qed. 

Lemma diverges_with_inftrace_finseq_excl:
  forall a t b it,
    star a t b -> irred b -> infseq_with_inftrace a it -> False.
Proof.
  intros. 
  eapply infseq_with_inftrace_implies_infseq in H1.
  eapply infseq_finseq_excl; eauto. 
Qed.

Lemma infseq_silent_with_inftrace_excl:
  forall a : A, infseq_silent a -> forall it' : inftrace, infseq_with_inftrace a it' -> False.
Proof.
  intros. inversion H0; subst.
  apply plus_star in H1.
  apply infseq_silent_star_inv' in H1; eauto. 
Qed.
  
Lemma diverges_silently_with_inftrace_excl:
  forall a t it,
    diverges_silently a t -> infseq_with_inftrace a it -> False. 
Proof.
  intros. unfold diverges_silently in *. destruct H as (b & ? & ?).
  inversion H0; subst.
  eapply star_infseq_with_inftrace_inv in H; eauto.
  destruct H as (b'' & ? & ?).
  eapply infseq_silent_with_inftrace_excl; eauto. 
Qed.

CoInductive stream_eq' : inftrace -> inftrace -> Prop :=
  eq'_scons : forall l s1 s2,
    l <> [] -> stream_eq' s1 s2 ->
    stream_eq' (app_to_itr l s1) (app_to_itr l s2).

Lemma deterministic_infseq_with_inftrace': forall a t t',
    infseq_with_inftrace a t -> infseq_with_inftrace a t' -> stream_eq' t t'.
Proof.
  cofix CIH; intros.
  inversion H; inversion H0; subst.
  pose proof (infseq_with_inftrace_inv).
  apply plus_star in H1. apply plus_star in H6. 
  specialize (H4 _ _ _ H1 _ _ _ _ H6 H2 H7 H3 H8). 
  destruct H4 as [a' [l1 [s1' [s2' [H11 [H12 [H13 [H14 H15]]]]]]]]; auto.
  rewrite H14; rewrite H15.
  econstructor; eauto.
Qed.

Lemma stream_eq'_EqSt : forall it1 it2, stream_eq' it1 it2 -> EqSt it1 it2.
Proof. 
  cofix Hfix; intros. 
  inversion H; subst; clear H.
  destruct l. congruence.
  simpl.
  destruct l. simpl. constructor. cbn; auto. apply Hfix; auto.
  constructor. cbn; auto.  apply Hfix. constructor. congruence.
  assumption.
Qed.

Lemma deterministic_infseq_with_inftrace:
  forall a t,
    infseq_with_inftrace a t ->
    forall t',
      infseq_with_inftrace a t' ->
      EqSt t t'.
Proof.
  eauto using deterministic_infseq_with_inftrace', stream_eq'_EqSt.
Qed.

End SEQUENCES.
