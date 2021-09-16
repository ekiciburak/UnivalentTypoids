Require Import Setoid CMorphisms.
(* Require Import Relations Morphisms. *)
Require Import Coq.Classes.CRelationClasses.
Require Import FunctionalExtensionality.

(* Local Unset Elimination Schemes. *)

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Record total2 { T: Type } ( P: T -> Type ): Type := 
  tpair 
  { pr1 : T;
    pr2 : P pr1 
  }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "{ x ; .. ; y ; z }" := (tpair _ x .. (tpair _ y z) ..). 

Notation "'∑'  x .. y , P" := (total2 (fun x => .. (total2 (fun y => P)) ..))
(at level 200, x binder, y binder, right associativity) : type_scope.


Inductive Id {A: Type}: A -> A -> Type :=
  refl: forall a, Id a a.

Arguments refl {A a} , [A] a.

(* Scheme Id_ind := Induction for Id Sort Type.
Arguments Id_ind [A] P f y y0 i.
Scheme Id_rec := Minimality for Id Sort Type.
Arguments Id_rec [A] P f y y0 i.
Definition Id_rect := Id_ind. 
 *)

Notation " R ===> R' " := (@CMorphisms.respectful _ _ (R%signature) (R'%signature))
(right associativity, at level 70) : signature_scope.

(*
Instance all_iff_morphism (A : Type) (x y: A) :
         CMorphisms.Proper (@Id A ===> @Id A) (@Id A).
 *)
Lemma is_refl_id: forall {A: Type} {a: A}, Id a a.
Proof. intros. easy. Defined.

Lemma is_sym_id: forall {A: Type} {a b: A}, Id a b -> Id b a.
Proof. intros. now induction X. Defined.

Lemma is_trans_id: forall {A: Type} {a b c: A}, Id a b -> Id b c -> Id a c.
Proof. intros. now induction X. Defined.

Global Instance transitive_paths {A} : Transitive (@Id A).
Proof. unfold Transitive. intros. exact( @is_trans_id A x y z X X0). Defined.



Definition dirprod (A B : Type): Type := ∑ a: A, B.
Definition dppr1 {A B : Type} := pr1: dirprod A B -> A.
Definition dppr2 {A B : Type} := pr2: dirprod A B -> B.

Notation "C × D ":= (@dirprod C D) (at level 40, left associativity).

Reserved Notation "x '~>' y" (at level 70, y at next level).
Reserved Notation "x '==' y" (at level 70).
Reserved Notation "x 'o' y" (at level 69).


Definition compose {A B C: Type} (f: A -> B) (g: B -> C): (A -> C).
Proof. intro a. now apply g, f. Defined.

Definition ap {A B: Type} {a b: A} (f: A -> B): Id a b -> Id (f a) (f b).
Proof. intro p. now induction p. Defined.

Definition concat {A: Type} {a b c: A}: Id a b -> Id b c -> Id a c.
Proof. intros p q. now induction p. Defined.

Definition homotopy {A: Type} {P: A -> Type} (f g: (∏ a: A, P a)): Type :=
  ∏ a: A, Id (f a) (g a).

Definition qinv {A B: Type} (f: A -> B): Type :=
  ∑ (g: B -> A), (dirprod (homotopy (compose g f) (@id B))
                          (homotopy (compose f g) (@id A))).

Definition isequiv {A B: Type} (f: A -> B): Type :=
  dirprod (∑ (g: B -> A),(homotopy (compose g f) (@id B))) 
          (∑ (h: B -> A),(homotopy (compose f h) (@id A))).

Definition ishae {A B: Type} (f: A -> B) :=
  ∑ g: B -> A, 
    ∑ eta: (homotopy (compose f g) (@id A)),
    ∑ eps: (homotopy (compose g f) (@id B)),
      ∏ x: A, Id (ap f (eta x)) (eps (f x)).


Definition Id_eql: ∏ {A: Type} (a b: A), Id a b -> a = b.
Proof. intros A a b p. now induction p. Defined.

Definition Id_eqr: ∏ {A: Type} (a b: A), a = b -> Id a b.
Proof. intros A a b p. now rewrite p. Defined.

Example h249_i: ∏ {A B: Type} {f: A -> B}, qinv f -> isequiv f.
Proof. intros A B f eq.
       destruct eq as (g, (pd1, pd2)).
       unshelve econstructor.
       - exists g. exact pd1.
       - exists g. exact pd2.
Defined.

Example h249_ii: ∏  {A B: Type} {f: A -> B}, isequiv f -> qinv f.
Proof. intros A B f eq.
       destruct eq as ((g, alpha), (h, beta)).
       unshelve econstructor.
       - exact g.
       - unshelve econstructor.
         + exact alpha.
         + intro a. compute in *.
           pose proof beta as beta'.
           specialize (beta (g (f a))).
           apply Id_eql in beta.
           specialize (alpha (f a)).
           apply Id_eql in alpha. 
           rewrite alpha in beta.
           now rewrite <- beta.
Defined.



Definition inverse {A: Type} {a b: A}: Id a b -> Id b a.
Proof. intro p. now induction p. Defined.

Lemma ap_refl: ∏ {A B: Type} {a: A} (f: A -> B), Id (ap f (refl a)) (refl (f a)).
Proof. intros. now cbn. Defined.


Lemma app_id: ∏ {A: Type} {a b: A} (p: Id a b), Id (ap id p) p.
Proof. intros. now induction p. Defined.


Lemma l_concat_refl: ∏ {A: Type} (a b: A) (p: Id a b),
  Id (concat (refl a) p) p.
Proof. intros. now induction p. Defined.

Lemma r_concat_refl: ∏ {A: Type} (a b: A) (p: Id a b),
  Id (concat p (refl b)) p.
Proof. intros. now induction p. Defined.

(* Lemma concat_assoc: ∏ {A: Type} {a b c d: A} (p: Id a b) (q: Id b c) (r: Id c d),
  Id (concat p (concat q r)) (concat (concat p q) r).
Proof. intros.
       induction p; induction q; induction r.
       simpl.
       apply refl.
Qed. *)

Lemma l_concat_remove: ∏ {A: Type} {a b c: A} (p: Id a b) (q r: Id b c),
  Id (concat p q) (concat p r) -> Id q r.
Proof. intros until r. intro H.
       apply Id_eql in H.
       induction p.
       specialize (@l_concat_refl A a c q); intros H0.
       apply Id_eql in H0. rewrite H0 in H.
       specialize (@l_concat_refl A a c r); intros H1.
       apply Id_eql in H1. rewrite H1 in H.
       now subst.
Defined.

Lemma r_concat_remove: ∏ {A: Type} {a b c: A} (p q: Id a b) (r: Id b c),
  Id (concat p r) (concat q r) -> Id p q.
Proof. intros until r. intro H.
       apply Id_eql in H.
       induction r.
       specialize (@r_concat_refl A a a0 p); intros H0.
       apply Id_eql in H0. rewrite H0 in H.
       specialize (@r_concat_refl A a a0 q); intros H1.
       apply Id_eql in H1. rewrite H1 in H.
       now subst.
Defined.


Lemma h243: ∏ {A B: Type} {a b: A} (f g: A -> B) (p: Id a b) (H: homotopy f g),
  Id (concat (H a) (ap g p)) (concat (ap f p) (H b)).
Proof. intros until p. induction p. intro H.
       specialize (@ap_refl A B a f); intros H0.
       apply Id_eql in H0. rewrite H0.
       specialize (@ap_refl A B a g); intros H1.
       apply Id_eql in H1. rewrite H1.
       now destruct H.
Defined.




Corollary h244: ∏ {A: Type} {a: A} (f: A -> A) (H: homotopy f (@id A)),
  Id (H (f a)) (ap f (H a)).
Proof. intros.
       specialize (@h243 _ A  _ _ f id (H a) H); intros Hk.
       pose proof Hk as Hkk.
       apply Id_eql in Hk. unfold id in *.
       assert ((ap (λ a : A, a) (H a) = (H a))).
       {  specialize (@app_id A _ _ (H a)); intros.
          now apply Id_eql in X.  }
       rewrite H0 in Hk. unfold homotopy in H.
       apply Id_eqr in Hk.
       apply (@r_concat_remove A (f (f a)) (f a) a (H (f a)) (ap f (H a)) (H a) Hk).
Defined.

Lemma concat_assoc: ∏ {A: Type} (a b c d: A) (p: Id a b) (q: Id b c)
  (r: Id c d), Id (concat p (concat q r)) (concat (concat p q) r).
Proof. intros. now induction p, q, r. Defined.

Lemma concat_inverse_l: ∏ {A: Type} (a b: A) (p: Id a b), Id (concat (inverse p) p) refl.
Proof. intros. now induction p. Defined.

Lemma concat_inverse_r: ∏ {A: Type} (a b: A) (p: Id a b), Id (concat p (inverse p)) refl.
Proof. intros. now induction p. Defined.


Lemma help: ∏ {A B: Type} (a: A) (f: A -> B) (g: B -> A) (p: Id (g (f a)) a),
Id (ap f (ap (λ a0 : A, g (f a0)) p)) (ap (λ a0 : A, f (g (f a0))) p).
Proof. intros. induction p. now cbn. Defined.

Lemma h243_2: ∏ {A B: Type} (x y: A) (p: Id x y) (f g: A -> B) (H: ∏a: A, Id (f a) (g a)),
  Id  (concat (ap f p) (H y)) (concat (H x) (ap g p)).
Proof. intros. apply inverse. apply h243. Defined.

Lemma qinv_ishae: ∏ {A B: Type} (f: A -> B), qinv f -> ishae f.
Proof. intros A B f e.
       destruct e as (g, (eps, eta)).
       unshelve econstructor.
       - exact g.
       - exists eta.
         unshelve econstructor.
         unfold homotopy, compose, id in *.
         intro b.
         exact ( concat (inverse (eps (f (g b)))) (concat (ap f (eta (g b))) (eps b)) ).
         intro a.
         cbn.
         specialize (@h244 ); intro Hc.
         unfold homotopy, compose, id in *.
         specialize (@Hc A a (compose f g) eta). cbn in *.
         unfold compose in *.

         assert (Hd: Id (ap f (eta (g (f a)))) (ap f (ap (compose f g) (eta a))) ).
         { unfold compose. now induction Hc. }
         assert (He: Id (concat (ap f (eta (g (f a)))) (eps (f a)))
                        (concat (ap f (ap (compose f g) (eta a))) (eps (f a))) ).
         { now induction Hd. }
         assert (Hf: Id (concat (ap f (ap (compose f g) (eta a))) (eps (f a))) 
                        (concat (eps (f (g (f a)))) (ap f (eta a)) )).

         { specialize (@h243_2 A B _ _ ( (eta a)) (compose f (compose g f)) f ); intro HH.
           unfold compose in *.
           specialize (HH (fun a => eps (f a))). cbn in *.
           apply Id_eql in HH. rewrite <- HH.
           apply Id_eqr. f_equal.
           specialize (@help A B a f g (eta a)); intro HHH.
           apply Id_eql in HHH. now rewrite HHH.
         }
         unfold compose in *.
         apply Id_eql in He. rewrite He.
         apply Id_eql in Hf. rewrite Hf.
         specialize (@concat_assoc _ _ _ _ _ (inverse (eps (f (g (f a))))) 
           (eps (f (g (f a))))  (ap f (eta a))); intro Hca.
         apply Id_eql in Hca. rewrite Hca.
         specialize (@concat_inverse_l _ _ _ (eps (f (g (f a))))); intros Hci.
         apply Id_eql in Hci. rewrite Hci.
         specialize (@l_concat_refl _ _ _ (ap f (eta a))); intro Hcl.
         apply Id_eql in Hcl.
         now rewrite Hcl.
Defined.

Lemma ishae_qinv: ∏ {A B: Type} {f: A -> B}, ishae f -> qinv f.
Proof. intros A B f e.
       destruct e as (finv, (eta, (eps, cc))).
       unshelve econstructor.
       - exact finv.
       - split; easy.
Defined.

Lemma isequiv_ishae: ∏ {A B: Type} (f: A -> B), isequiv f -> ishae f.
Proof. intros A B f e.
       apply h249_ii in e.
       now apply qinv_ishae.
Defined.

Lemma ishae_isequiv: ∏ {A B: Type} (f: A -> B), ishae f -> isequiv f.
Proof. intros A B f e.
       apply ishae_qinv in e.
       now apply h249_i.
Defined.

Definition transport {A: Type} (P: A -> Type) {a b: A} (p: Id a b): P a -> P b.
Proof. now induction p. Defined.

Definition Equiv (A B: Type): Type := (∑ f: A -> B, isequiv f).

Definition idtoeqv: ∏ {A B: Type}, Id A B -> Equiv A B.
Proof. intros A B p.
       exists (transport (@id Type) p).
       apply h249_i.
       unshelve econstructor.
       + exact (transport _ (inverse p)).
       + now induction p.
Defined.


Definition happly {A: Type} {B: A -> Type} (f g: ∏x: A, B x): (Id f g) -> homotopy f g.
Proof. intros p a. now induction p. Defined.

Definition funext_def_qinv:= ∏  (A: Type) (B: A -> Type) (f g: ∏ x: A, B x),
  qinv (@happly A B f g).
Axiom FE: funext_def_qinv.

Definition funext {A: Type} {B: A -> Type} {f g: ∏ x: A, B x}: (∏ x: A, Id (f x) (g x)) -> Id f g.
Proof. destruct (FE A B f g) as (inv_happly, cc2).
       exact inv_happly.
Defined.


Definition funext_happly {A: Type} {B: A -> Type} {f g: ∏ x: A, B x} 
                         (p: Id f g): Id (funext (happly _ _ p)) p.
Proof. unfold funext.
       destruct (FE A B f g) as (inv_happly, cc).
       destruct cc as (cc1, cc2).
       unfold homotopy, compose, id in cc2.
       exact (cc2 p).
Defined.

Definition happly_funext {A: Type} {B: A -> Type} {f g: ∏ x:A, B x} 
                         (h: ∏ x:A, Id (f x) (g x)): Id (happly _ _ (funext h)) h.
Proof. unfold funext.
       destruct (FE A B f g) as (inv_happly, cc).
       destruct cc as (cc1, cc2).
       unfold homotopy, compose, id in cc2.
       exact (cc1 h).
Defined.

Definition Equiv_ishae (A B: Type): Type := (∑ f: A -> B, ishae f).

Definition idtoeqv_ishae: ∏ {A B: Type}, Id A B -> Equiv_ishae A B.
Proof. intros A B p.
       exists (transport (@id Type) p).
       apply qinv_ishae.
       unshelve econstructor.
       + exact (transport _ (inverse p)).
       + now induction p.
Defined.

Definition UA_def_ishae: Type := ∏ (A B: Type), ishae (@idtoeqv_ishae A B).
Axiom UA_ishae: UA_def_ishae.

Definition ua_ishae {A B : Type}: (Equiv_ishae A B) -> (Id A B).
Proof. destruct (UA_ishae A B) as (eqvtoid, cc).
        exact eqvtoid.
Defined.


Definition UA_def: Type := ∏ (A B: Type), isequiv (@idtoeqv A B).
Axiom UA: UA_def.

Definition isContr  (A: Type): Type := ∑ a: A, ∏ x: A, Id a x.

Definition linv {A B: Type} (f: A -> B) :=
  ∑ g: B -> A, homotopy (compose f g) (@id A).

Definition rinv {A B: Type} (f: A -> B) :=
  ∑ g: B -> A, homotopy (compose g f) (@id B).

Definition lcoh {A B: Type} (f: A -> B) (l: linv f) :=
  let (g, eta) := l in
  ∑ eps: homotopy (compose g f) (@id B), ∏y: B, Id (ap g (eps y)) (eta (g y)).

Definition rcoh {A B: Type} (f: A -> B) (r: rinv f) :=
  let (g, eps) := r in
  ∑ eta: homotopy (compose f g) (@id A), ∏x: A, Id (ap f (eta x)) (eps (f x)).


Definition fiber  {A B: Type} (f: A -> B) (y: B): Type := ∑ x: A, Id (f x) y.
Definition isContrf {A B: Type} (f: A -> B): Type := ∏ y: B, isContr (fiber f y).

Lemma h428_i: ∏ {A B C: Type} (f: A -> B), qinv f -> 
  qinv (λ g: B -> C, compose f g).
Proof. intros A B C f e.
        destruct e as (g, (p, q)).
        unshelve econstructor.
          exact (λ (h: A -> C) (b: B), h (g b)).
        - split.
          + intro h. compute.
            unfold homotopy, compose, id in *.
            apply funext.
            intro x. 
            specialize (q x).
            now induction q.
          + intro h. compute.
            unfold homotopy, compose, id in *.
            apply funext.
            intro x.
            specialize (p x).
            now induction p.
Defined.

Lemma h428_ii: ∏ {A B C: Type} (f: A -> B), qinv f -> 
  qinv (λ g: C -> A, compose g f).
Proof. intros A B C f e.
        destruct e as (g, (p, q)).
        unshelve econstructor.
          exact (λ (h: C -> B) (c: C), g (h c)).
        - split;
            intro h; compute;
            unfold homotopy, compose, id in *;
            apply funext;
            intro x; easy.
Defined.

Lemma h429_l_i: ∏ {A B: Type} (f: A -> B), 
  (linv f) -> (∑ g: B -> A, Id (compose f g) (@id A)).
Proof. intros A B f (g, p).
        unshelve econstructor.
        - exact g.
        - now apply funext in p.
Defined.

Lemma h429_l_ii: ∏ {A B: Type} (f: A -> B), 
  (∑ g: B -> A, Id (compose f g) (@id A)) -> (linv f).
Proof. intros A B f (g, p).
        unshelve econstructor.
        - exact g.
        - now apply happly in p.
Defined.

Lemma h429_l: ∏ {A B: Type} (f: A -> B), 
  Equiv (linv f) (∑ g: B -> A, Id (compose f g) (@id A)).
Proof. intros.
        unshelve econstructor.
        - apply h429_l_i.
        - unshelve econstructor.
          + unshelve econstructor.
            ++ apply h429_l_ii.
            ++ cbn.
                unfold h429_l_i, h429_l_ii in *.
                intros (g, p).
                specialize (@funext_happly _ _ _ _ p); intro H.
                unfold compose, homotopy, id in *. 
                apply Id_eql in H. now rewrite H.
           + unshelve econstructor.
             ++ intros (g, p).
                unfold linv.
                exists g.
                now apply happly in p.
             ++ cbn.
                intros (g, p).
                specialize (@happly_funext _ _ _ _ p); intro H.
                apply Id_eql in H.
                unfold compose, homotopy, id, h429_l_i in *.
                cbn in *. apply Id_eqr. f_equal. easy.
Defined.

Require Import Equality. 

Lemma h425_i: ∏ {A B: Type} (f: A -> B) (y: B) (a b: fiber f y),
  (Id a b) ->
  (∑ gamma: Id (pr1 a) (pr1 b), Id (concat (ap f gamma) (pr2 b)) (pr2 a)).
Proof. intros A B f y (x, p) (x', p') q.
        cbn.
        unshelve econstructor.
        - now inversion q.
        - cbn. inversion q.
          subst. apply Eqdep.EqdepTheory.inj_pair2 in H2.
          subst. dependent destruction q.
          cbn.  now destruct p'.
Defined.


Lemma h425_ii: ∏ {A B: Type} (f: A -> B) (y: B) (a b: fiber f y),
  (∑ gamma: Id (pr1 a) (pr1 b), Id (concat (ap f gamma) (pr2 b)) (pr2 a)) ->
  (Id a b).
Proof. intros A B f y (x, p) (x', p') (gamma, q).
        inversion q. cbn in *.
        induction gamma.
        specialize (@ap_refl A B a1 f); intros.
        apply Id_eql in X.
        rewrite X in H0.
        specialize (@l_concat_refl _ _ _ p'); intros.
        apply Id_eql in X0.
        rewrite X0 in H0.
        now rewrite H0.
Defined.


Lemma h426: ∏ {A B: Type} (f: A -> B), ishae f -> isContrf f.
Proof. intros A B f e.
        unfold isContrf.
        intro y.
        destruct e as (g, (eta, (eps, tau))).
        unshelve econstructor.
        - unfold fiber.
          exists (g y). apply eps.
        - intros (x, p).
           unfold compose, homotopy, id in *.
           apply h425_ii.
           cbn.
           unshelve econstructor.
           + clear tau. specialize (eta x).
             now induction p.
           + dependent destruction p. cbn.
             specialize (@r_concat_refl _ _ _ (ap f (eta x))); intros.
             apply Id_eql in X. rewrite X.
             apply tau.
Defined.

Lemma h436_ii: ∏ {A B: Type} (e: Equiv A B), isContr B -> isContr A.
Proof. intros A B e alpha.
        destruct alpha as (b, P).
        destruct e as (f, iseqf).
        unshelve econstructor.
        + exact (pr1 (pr2 iseqf) b).
        + intro a.
          destruct iseqf as ((g, Hg), (h, Hh)).
          cbn.
          unfold homotopy, compose, id in *.
          specialize (P (f a)).
          specialize (Hh a).
          apply Id_eql in P. 
          now rewrite P in *.
Defined.

Lemma h429_linv: ∏ {A B: Type} (f: A -> B), qinv f -> isContr (linv f).
Proof. intros A B f e.
        specialize (@h429_l A B f); intros e2.
        specialize (@h428_i A B A f e); intros e3.
        apply qinv_ishae in e3.
        apply h426 in e3.
        unfold isContrf, fiber in e3.
        specialize (e3 id). 
        apply h436_ii in e2; easy.
Defined.

Lemma h429_r_i: ∏ {A B: Type} (f: A -> B), 
  (rinv f) -> (∑ g: B -> A, Id (compose g f) (@id B)).
Proof. intros A B f (g, p).
        unshelve econstructor.
        - exact g.
        - now apply funext in p.
Defined.

Lemma h429_r_ii: ∏ {A B: Type} (f: A -> B), 
  (∑ g: B -> A, Id (compose g f) (@id B)) -> (rinv f).
Proof. intros A B f (g, p).
        unshelve econstructor.
        - exact g.
        - now apply happly in p.
Defined.

Lemma h429_r: ∏ {A B: Type} (f: A -> B), 
  Equiv (rinv f) (∑ g: B -> A, Id (compose g f) (@id B)).
Proof. intros.
        unshelve econstructor.
        - apply h429_r_i.
        - unshelve econstructor.
          + unshelve econstructor.
            ++ apply h429_r_ii.
            ++ cbn.
                unfold h429_r_i, h429_r_ii in *.
                intros (g, p).
                specialize (@funext_happly _ _ _ _ p); intro H.
                unfold compose, homotopy, id in *. 
                apply Id_eql in H. now rewrite H.
           + unshelve econstructor.
             ++ intros (g, p).
                unfold linv.
                exists g.
                now apply happly in p.
             ++ cbn.
                intros (g, p).
                specialize (@happly_funext _ _ _ _ p); intro H.
                apply Id_eql in H.
                unfold compose, homotopy, id, h429_r_i in *.
                cbn in *. apply Id_eqr. f_equal. easy.
Defined.

Lemma h429_rinv: ∏ {A B: Type} (f: A -> B), qinv f -> isContr (rinv f).
Proof. intros A B f e.
        specialize (@h429_r A B f); intros e2.
        specialize (@h428_ii A B B f e); intros e3.
        apply qinv_ishae in e3.
        apply h426 in e3.
        unfold isContrf, fiber in e3.
        specialize (e3 id).
        apply h436_ii in e2; easy.
Defined.

Lemma ishae_rcoh: ∏ {A B: Type} (f: A -> B), 
  Equiv (ishae f) (∑u: rinv f, rcoh f {pr1 u; pr2 u}).
Proof. intros.
        unshelve econstructor.
        - intro e. destruct e as (g, (eps, (eta, p))).
          unshelve econstructor.
          + unfold rinv. exists g.
            easy.
          + cbn. exists eps. easy.
        - apply h249_i.
          unshelve econstructor.
          + intros ((g, Hg), H).
            unshelve econstructor.
            * exact g.
            * cbn in *.
              unfold homotopy, compose, id in *.
              unshelve econstructor.
              ++ intro a. now destruct H.
              ++ cbn. destruct H as (p, q).
                  exists Hg. easy.
          + split.
            * cbn. unfold compose, homotopy, id.
              intro H. destruct H as ((r, Hr), (eta, H)). cbn in *.
              easy.
            * cbn. unfold compose, homotopy, id.
              intro H. destruct H as (g, (eta, (eps, p))).
              easy.
Defined.




Definition ua_f {A B : Type} (f: A-> B): (isequiv f) -> (Id A B).
Proof. intro e.
       destruct (h249_ii (UA A B)) as (eqvtoid, cc).
       apply eqvtoid.
       exists f. exact e.
Defined.

Lemma h442: ∏ {A B X: Type} (e: Equiv A B), Equiv (X -> A) (X -> B).
Proof. intros A B X (f, e).
        unshelve econstructor.
        - exact (λ (a: (X -> A)) (x: X), f (a x)).
        - assert (H: ∑p: Id A B, Id {f; e} (idtoeqv p)).
          { unshelve econstructor.
             + apply ua_f in e. exact e.
             + cbn. unfold ua_f.
               destruct (h249_ii (UA A B)).
               destruct pr4 as (c, d).
               unfold compose, homotopy, id in *.
               specialize (c ({f; e})). easy.
          }
         destruct H as (p, q).
         induction p. apply Id_eql in q.
         inversion q. rewrite H0.
         unshelve econstructor.
         + exists id. now compute.
         + exists id. now compute.
Defined.

Corollary h432c: ∏ {A B: Type} (f: A -> B) (e: isequiv f) (x x':A) (y: B),
  dirprod (Id (f x) y) (Id (f x') y) -> Id x x'.
Proof. intros A B f e x x' y (p, q).
        apply h249_ii in e.
        destruct e as (g, (cc0, cc1)).
        unfold homotopy, compose, id in *.
        apply Id_eql in p. apply Id_eql in q.
        pose proof cc1 as cc2.
        specialize (cc1 x).
        specialize (cc2 x').
        assert (g (f x)  = g y) by now rewrite p.
        assert (g (f x') = g y) by now rewrite q.
        apply Id_eql in cc1. apply Id_eql in cc2.
        rewrite cc2 in H0.
        rewrite cc1 in H.
        rewrite <- H in H0.
        now rewrite H0.
Qed.


Corollary h432d: ∏ {A B: Type} (f: A -> B) (e: isequiv f) (y: B)
  (a b: ∑x: A, Id (f x) y), Id a b.
Proof. intros.
        destruct a as (a, p).
        destruct b as (b, q).
        specialize (@h432c A B f e a b y); intro H.
        assert (H0: dirprod (Id (f a) y) (Id (f b) y) ) by easy.
        specialize (H H0). induction H.
        dependent destruction p.
        dependent destruction q. easy.
Defined.


Lemma h432_i: ∏ {A B: Type} (f: A -> B), isequiv f -> isContrf f.
Proof. intros A B f e.
        unfold isContrf. intro y.
        specialize (@h432d A B f e y); intro H.
        unshelve econstructor.
        - unfold fiber.
          apply h249_ii in e.
          destruct e as (g, (cc0, cc1)).
          unfold homotopy, compose, id in *.
          exists (g y). easy.
        - cbn. destruct (h249_ii e), pr4. cbn. 
          intro a. specialize (H a).
          specialize (H {pr3 y; pr4 y}). easy.
Defined.

Lemma h432_ii: ∏ {A B: Type} (f: A -> B), isContrf f -> isequiv f.
Proof. unfold isContrf.
        intros A B f e.
        apply h249_i.
        unshelve econstructor.
        - intro y.
          specialize (e y).
          destruct e as (fib, cc).
          destruct fib as (x, p).
          exact x.
        - compute. unshelve econstructor.
          + intro a. destruct (e a).
            destruct pr3. easy.
          + intro a. destruct (e (f a)) as ((x, p), cc).
            specialize (e (f a)).
            destruct e as (g, cc0).
            destruct g as (b, q). 
            specialize (cc {a; refl}).
            apply Id_eql in cc.
            now inversion cc. 
Defined.



Lemma h432: ∏ {A B: Type} (f: A -> B),
  dirprod ((isContrf f) -> (isequiv f))
          ((isequiv f) -> (isContrf f)) .
Proof. intros. split. apply h432_ii. apply h432_i. Defined.

Lemma h434: ∏ {A: Type} (P: A -> Type) {a: A},
  Equiv (fiber (@pr1 A P) a) (P a).
Proof. intros.
       unshelve econstructor.
       - intros Hf. destruct Hf as ((y, t), q).
         inversion q. subst. cbn. exact t.
       - apply h249_i.
         unshelve econstructor.
         + intro p.
           unfold fiber.
           unshelve econstructor.
           exists a. exact p.
           now cbn.
         + split.
           * unfold homotopy, compose, id.
             intro p. now cbn.
           * unfold homotopy, compose, id.
             intro p. destruct p as ((y, t), q).
             compute in *. now induction q.
Qed.


Corollary h443: ∏ {A: Type} (P: A -> Type) (p: ∏ x : A, isContr (P x)), 
  Equiv (A -> ∑ x: A, P x) (A -> A).
Proof. intros A P p.
        apply h442.
        unshelve econstructor.
        + exact pr1.
        + apply h432. unfold isContrf.
          specialize (@h434 A P); intro H.
          intro a.
          specialize (@h436_ii _ _ (H a)); intro HH.
          apply HH. easy.
Defined.

Definition wfunext_def: Type := ∏  (A: Type) (P: A -> Type),
  (∏x: A, isContr (P x)) -> isContr (∏x: A, P x).

Definition retract (A B: Type) := ∑ r: A -> B, ∑ s: B -> A, ∏ y: B, Id (r (s y)) y.

Lemma h437: ∏ {A B: Type} (re: retract A B), isContr A -> isContr B.
Proof. intros A B e alpha.
        destruct alpha as (a, P).
        destruct e as (r, (s, eps)).
        unshelve econstructor.
        - exact (r a).
        - intro y.
          specialize (P (s y)).
          apply Id_eql in P. rewrite P. easy.
Defined.


Theorem h444: wfunext_def.
Proof. unfold wfunext_def.
        intros A P p.
        specialize (pr2 (h443 P p)); intros uf_equiv; cbn in uf_equiv.
        apply h432 in uf_equiv.
        unfold isContrf in uf_equiv; cbn in uf_equiv.
        specialize (uf_equiv id).
        assert (R: retract (fiber (λ (a : A -> ∑ x : A, P x) (x : A), pr1 (a x)) id) 
                           (∏ x : A, P x)).
        { unshelve econstructor.
          - intro X.
            destruct X as (g, q).
            exact (λ x, @transport A P _ _ ((@happly _ _ _ _ q) x) (pr2 (g x))).
          - cbn. unshelve econstructor.
            + intro f. cbn in *.
              exact ({λ x: A, {x; (f x)}; refl}).
            + intros. cbn. easy.
        }
        specialize (@h437 _ _ R); intros HH. apply HH.
        easy.
Defined.


Lemma rcoh_r_contr: ∏ {A B: Type} (f: A -> B) (a: rinv f)
 (e: ishae f)
 (eta : homotopy (compose f (pr1 a)) id), isContr (∏ x : A, Id (ap f (eta x)) (pr2 a (f x))).
Proof. intros. apply h444.
       intro x. destruct a as (g, eps). cbn in *.
       pose proof e as d.
       pose proof e as c.
       apply ishae_rcoh in e.
       destruct e as (u, Hu). cbn in Hu.
       pose proof u as v.
       destruct u as (u, eps_u). cbn in Hu.
       destruct Hu as (eta_u, Hu).
       apply ishae_qinv in d.
       apply ishae_qinv in c.
       apply h429_rinv in d.
       apply h429_linv in c.

       destruct d as (d, Hd).
       pose proof Hd as Hd2.
       specialize (Hd  {u; eps_u}).
       specialize (Hd2  {g; eps}).
       assert (u = g).
       { apply Id_eql in Hd.
         apply Id_eql in Hd2.
         rewrite Hd in Hd2.
         now inversion Hd2.
       } subst.
       assert (eps = eps_u).
       { apply Id_eql in Hd.
         apply Id_eql in Hd2.
         rewrite Hd in Hd2.
         inversion Hd2.
         now apply Eqdep.EqdepTheory.inj_pair2 in H0.
       } subst.

       destruct c as (c, Hc).
       pose proof Hc as Hc2.
       specialize (Hc  {g; eta_u}).
       specialize (Hc2  {g; eta}).
       assert (eta = eta_u).
       { apply Id_eql in Hc.
         apply Id_eql in Hc2.
         rewrite Hc in Hc2.
         inversion Hc2.
         now apply Eqdep.EqdepTheory.inj_pair2 in H0.
       } subst.
       specialize (Hu x).
       induction Hu. 
       unshelve econstructor.
       - easy.
       - intro x0. dependent destruction x0. easy.
Defined.


Lemma rcoh_contr: ∏ {A B: Type} (f: A -> B),
  ishae f ->  isContr (∑ u : rinv f, rcoh f {pr1 u; pr2 u}).
Proof. intros A B f e.
       
       pose proof e as d.
       pose proof e as c.
       pose proof e as b.
       apply ishae_rcoh in e.
       destruct e as (u, Hu).
       unshelve econstructor.
       exists u. easy.
       intro x.
       destruct x as (v, Hv). cbn in *.
       apply ishae_qinv in d.
       apply h429_rinv in d.
       assert (Id u v).
       { destruct d as (d, Hd).
         pose proof Hd as Hd2.
         specialize (Hd u).
         specialize (Hd2 v).
         now induction Hd.
       } induction X.

       apply ishae_qinv in c.
       apply h429_linv in c.
       destruct Hu as (eta_u, Hu).
       destruct Hv as (eta_v, Hv).
       destruct c as (c, Hc).
       unfold linv in c.
       pose proof Hc as Hc2.
       specialize (Hc  {pr1 a; eta_u}).
       specialize (Hc2 {pr1 a; eta_v}).
       assert (Id eta_u eta_v).
       { apply Id_eql in Hc.
         apply Id_eql in Hc2.
         rewrite Hc in Hc2.
         inversion Hc2.
         apply Eqdep.EqdepTheory.inj_pair2 in H0.
         rewrite H0. easy.
       } induction X.
       specialize (@rcoh_r_contr A B f a b a0); intros.
       destruct X as (p, q).
       pose proof q as k.
       specialize (q Hu).
       specialize (k Hv).
       induction q, k. easy.
Defined.

Lemma rcoh_contr_isequiv: ∏ {A B: Type} (f: A -> B),
  isequiv f ->  isContr (∑ u : rinv f, rcoh f {pr1 u; pr2 u}).
Proof. intros A B f e.
       apply isequiv_ishae in e.
       apply rcoh_contr. easy.
Defined.

Lemma ishae_contr: ∏ {A B: Type} (f: A -> B), ishae f -> isContr (ishae f). 
Proof. intros A B f e.
       specialize (@ishae_rcoh A B f); intro H.
       apply h436_ii in H. easy.
       apply rcoh_contr. easy.
Defined.

Definition isProp (A: Type): Type :=  ∏ (x y: A), Id x y.

Lemma h35_i:∏ {A: Type}, (isProp A) -> (A -> isContr A).
Proof. intros A p a.
        unshelve econstructor.
        - exact a.
        - intro x. now specialize (p a x).
Defined.

Lemma h35_ii:∏ {A: Type}, (A -> isContr A) -> (isProp A).
Proof. intros A p a b.
        specialize (p a). 
        destruct p as (c, p).
        pose proof p as q.
        specialize (p a).
        now induction p.
Defined.

Lemma h35: ∏ {A: Type}, Equiv (isProp A) (A -> isContr A).
Proof. intros.
        unshelve econstructor.
        - exact h35_i.
        - apply h249_i.
          unshelve econstructor.
          + exact h35_ii.
          + split.
            * unfold h35_i, h35_ii.
              unfold homotopy, compose, id.
              intro a. compute.
              apply funext.
              intro x.
              destruct (a x) as (b, p).
              destruct (p x). cbn.
              easy.
           * unfold homotopy, compose, id.
              intro a.
              apply funext.
              intro x.
              compute.
              induction (a x x).
              easy.
Defined.

Lemma ishae_isProp: ∏ {A B: Type} (f: A -> B), isProp (ishae f).
Proof. intros.
        specialize @h35; intros.
        specialize @ishae_contr; intros.
        specialize (X0 A B f). unfold isContr in X0.
        unfold isProp. intros.
        specialize (X0 x). destruct X0.
        pose proof pr4 as pr5.
        specialize (pr4 x).
        specialize (pr5 y). 
        now induction pr4.
Defined.

