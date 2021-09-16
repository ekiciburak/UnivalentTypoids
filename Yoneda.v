From UT Require Import Prelims Setoid Typoid TypoidFunction TypoidNT ExponentialTypoid.
Require Import Coq.Classes.CRelationClasses.
Require Import FunctionalExtensionality.
Set Universe Polymorphism.

Definition idtoeqvT: ∏ {A: Type} {x y: A} {T: Typoid A} (p: Id x y), @et A (@st A T) x y.
Proof. intros A x y T p.
        exact (transport (fun z => x ~> z) p (eqv x)).
Defined.

Definition idtoeqvTT: ∏ {A: Type} {x y: A} {T: Typoid A} {f g: x ~> y} (p: Id f g), f == g.
Proof. intros A x y T f g p.
       now induction p.
Defined.

Definition UA_defT: Type := ∏ (A: Type) (x y: A) (T: Typoid A), isequiv (@idtoeqvT A x y T).
Axiom UAT: UA_defT.

Definition UA_defTT: Type := ∏ (A: Type) (x y: A) (T: Typoid A) (f g: x ~> y), isequiv (@idtoeqvTT A x y T f g).
Axiom UATT: UA_defTT.

Definition YaOp {A: Type} (a: A) (TA: Typoid A): TypoidFunction (OppositeT TA) Uni.
Proof. unshelve econstructor.
       - intro x.
         exact (et (@st A TA) x a).
       - simpl. intros x y f.
         unshelve econstructor.
         + intro g.
           exact (f o g).
         + apply qinv_ishae.
           unshelve econstructor.
           ++ intros g.
              exact (inv f o g).
           ++ unfold homotopy, compose.
              split.
              * intros g.
                apply UATT.
                rewrite <- Typ3.
                rewrite Typ2_i.
                rewrite Typ1_i.
                unfold id.
                reflexivity.
              * intros g.
                apply UATT.
                rewrite <- Typ3.
                rewrite Typ2_ii.
                rewrite Typ1_i.
                unfold id.
                reflexivity.
       - simpl. unfold homotopy, id.
         intros x f.
         apply UATT.
         unfold Setoid.OppositeS_obligation_1.
         rewrite Typ1_i.
         reflexivity.
       - simpl. intros x y z f g.
         unfold homotopy, id, compose.
         intros h.
         apply UATT.
         unfold Setoid.OppositeS_obligation_2.
         rewrite Typ3.
         reflexivity.
       - simpl. intros x y f g H.
         unfold homotopy.
         intro h.
         apply UATT.
         rewrite H.
         reflexivity.
       - repeat intro.
         apply UATT.
         rewrite X.
         reflexivity.
Defined.

Definition PiTypoidAppOpp: forall {A: Type} (TA: Typoid A) (P: TypoidFunction (OppositeT TA) Uni) (a: A), 
  Typoid (fobj P a).
Proof. intros A TA P a.
       simpl.
       unshelve econstructor.
       - unshelve econstructor.
         + unfold crelation.
           intros phi Q.
(*         exact (forall x: A, (et (@st _ Uni) (phi x) (Q x))). *)
           exact (Id phi Q).
         + simpl. intros px.
           apply refl.
         + simpl. intros p q r Ha Hb.
           specialize (@concat _ p q r Ha Hb); intro C.
           exact C.
         + simpl. intros p q H.
           exact (inverse H).
       - simpl. intros p q.
         unfold crelation.
         intros Hp Hq.
         exact (Id Hp Hq).
       - simpl. intros p q H.
         apply refl.
       - simpl. intros p q Hp Hq H.
         exact (inverse H).
       - simpl. intros p q Hp Hq Hr Ha Hb.
         specialize (@concat _ Hp Hq Hr Ha Hb); 
         intro C.
         exact C.
       - simpl. intros p q Hp.
         induction (Hp).
         simpl.
         apply refl.
       - simpl. intros p q Hp.
         induction (Hp).
         simpl.
         apply refl.
       - simpl. intros p q Hp.
         induction (Hp).
         simpl.
         apply refl.
       - simpl. intros p q Hp.
         induction (Hp).
         simpl.
         apply refl.
       - simpl. intros p q r s Hp Hq Hs.
         simpl in *.
         specialize (@concat_assoc _ p q r s
                                  Hp Hq Hs ); intros C.
         exact (inverse C).
       - simpl. intros p q r Hp Hq Hr Hs Ht Hi.
         induction (Ht).
         induction (Hi).
         apply refl.
       - repeat intro.
         simpl in *.
         induction (X).
         induction (X0).
         apply refl.
       - repeat intro.
         apply refl.
       - repeat intro.
         simpl in *.
         induction (X).
         apply refl.
Defined.

Definition PiTypoidOpp: forall {A: Type} (TA: Typoid A) (P: TypoidFunction (OppositeT TA) Uni), 
  Typoid (forall x: A, fobj P x).
Proof. intros A TA P.
       simpl.
       unshelve econstructor.
       - unshelve econstructor.
         + unfold crelation.
           intros phi Q.
           exact (forall x: A, (et (@st _ (PiTypoidAppOpp TA P x)) (phi x) (Q x))). 
(*            exact (forall x: A, (Id (phi x) (Q x))). *)
         + simpl. intros p x.
           apply refl.
         + simpl. intros p q r Ha Hb x.
           specialize (@concat _ (p x) (q x) (r x) (Ha x) (Hb x)); intro C.
           exact C.
         + simpl. intros p q H x.
           exact (inverse (H x)).
       - simpl. intros p q.
         unfold crelation.
         intros Hp Hq.
         exact (forall x: A, Id (Hp x) (Hq x)).
       - simpl. intros p q H x.
         apply refl.
       - simpl. intros p q Hp Hq H x.
         exact (inverse (H x)).
       - simpl. intros p q Hp Hq Hr Ha Hb x.
         specialize (@concat _ (Hp x) (Hq x) (Hr x) (Ha x) (Hb x)); 
         intro C.
         exact C.
       - simpl. intros p q Hp x.
         induction (Hp x).
         simpl.
         apply refl.
       - simpl. intros p q Hp x.
         induction (Hp x).
         simpl.
         apply refl.
       - simpl. intros p q Hp x.
         induction (Hp x).
         simpl.
         apply refl.
       - simpl. intros p q Hp x.
         induction (Hp x).
         simpl.
         apply refl.
       - simpl. intros p q r s Hp Hq Hs x.
         simpl in *.
         specialize (@concat_assoc _ (p x) (q x) (r x) (s x)
                                  (Hp x) (Hq x) (Hs x)); intros C.
         exact (inverse C).
       - simpl. intros p q r Hp Hq Hr Hs Ht Hi x.
         induction (Ht x).
         induction (Hi x).
         apply refl.
       - repeat intro.
         simpl in *.
         induction (X x2).
         induction (X0 x2).
         apply refl.
       - repeat intro.
         apply refl.
       - repeat intro.
         simpl in *.
         induction (X x1).
         apply refl.
Defined.

Definition HomOp: forall {A: Type} (TA: Typoid A) (P Q: TypoidFunction (OppositeT TA) Uni),
  Typoid (∏ (x: A), ∏ (p: fobj P x), fobj Q x).
Proof. intros A TA P Q.
       unshelve econstructor.
       - unshelve econstructor.
         + unfold crelation.
           intros phi psi.
           exact (∏ (x: A) (p: fobj P x), (Id (phi x p) (psi x p))).
         + simpl. intros p x q.
           apply refl.
         + simpl. intros p q r Hp Hq x px.
           specialize (@concat _ (p x px) (q x px) (r x px) (Hp x px) (Hq x px)); intro C.
           exact C.
         + simpl. intros p q Hp x px.
           exact (inverse (Hp x px)).
       - simpl. intros p q.
         unfold crelation.
         intros Hp Hq.
         exact (forall (x: A) (p: fobj P x), Id (Hp x p) (Hq x p)).
       - simpl. intros p q H x px.
         apply refl.
       - simpl. intros p q Hp Hq H x px.
         exact (inverse (H x px)).
       - simpl. intros p q Hp Hq Hr Ha Hb x px.
         specialize (@concat _ (Hp x px) (Hq x px) (Hr x px) (Ha x px) (Hb x px)); 
         intro C.
         exact C.
       - simpl. intros p q Hp x px.
         induction (Hp x px).
         simpl.
         apply refl.
       - simpl. intros p q Hp x px.
         induction (Hp x px).
         simpl.
         apply refl.
       - simpl. intros p q Hp x px.
         induction (Hp x px).
         simpl.
         apply refl.
       - simpl. intros p q Hp x px.
         induction (Hp x px).
         simpl.
         apply refl.
       - simpl. intros p q r s Hp Hq Hs x px.
         simpl in *.
         specialize (@concat_assoc _ (p x px) (q x px) (r x px) (s x px)
                                  (Hp x px) (Hq x px) (Hs x px)); intros C.
         exact (inverse C).
       - simpl. intros p q r Hp Hq Hr Hs Ht Hi x px.
         induction (Ht x px).
         induction (Hi x px).
         apply refl.
       - repeat intro.
         simpl in *.
         induction (X x2 p).
         induction (X0 x2 p).
         apply refl.
       - repeat intro.
         apply refl.
       - repeat intro.
         simpl in *.
         induction (X x1 p).
         apply refl.
Defined.

Lemma app_concat: ∏ {A B: Type} {a b c: A} (f: A -> B) (p: Id a b) (q: Id b c),
Id (ap f (concat p q)) (concat (ap f p) (ap f q)).
Proof. intros. now induction p, q. Defined.

Definition apD {A C: Type} {B: A -> Type} (f: forall a:A, B a) {x y: A} (p: Id x y):
  Id (transport _  p (f x)) (f y).
Proof. unfold transport.
       induction p.
       simpl.
       apply refl.
Defined.

(** j *)
Definition HomYaOpPNTl: forall {A: Type} (a: A) (TA: Typoid A) (P: TypoidFunction (OppositeT TA) Uni),
  TypoidFunction (HomOp TA (YaOp a TA) P) (PiTypoidAppOpp TA P a).
Proof. intros A a TA P.
       unshelve econstructor.
       - simpl. intro v.
         exact (v a (eqv a)).
       - simpl. intros p q Hp.
         specialize (Hp a (eqv a)).
         exact Hp.
       - simpl. intros p.
         apply refl.
       - simpl. intros p q r Hp Hq.
         apply refl.
       - simpl. intros p q Hp Hq H.
         induction (H a (eqv a)).
         apply refl.
       - simpl. repeat intro.
         induction (X a (eqv a)).
         apply refl.
Defined.

(** i *)
Definition HomYaOpPNTr: forall {A: Type} (a: A) (TA: Typoid A) (P: TypoidFunction (OppositeT TA) Uni),
  TypoidFunction (PiTypoidAppOpp TA P a) (HomOp TA (YaOp a TA) P).
Proof. intros A a TA P.
       unshelve econstructor.
       - simpl.
         intros u x f.
         exact ((pr1 (fmap P f)) u).
       - simpl. intros px py q x f.
         induction q.
         apply refl.
       - simpl. intros px x f.
         apply refl.
       - simpl. intros px py pz p q x f.
         induction p.
         induction q.
         apply refl.
       - simpl. intros px py p q r x f.
         induction p.
         induction r.
         apply refl.
       - repeat intro.
         simpl in X.
         induction X.
         apply refl.
Defined.

(** (j o i)(u) = u *)
Lemma HomYaOpPNTEql: forall {A: Type} (a: A) (TA: Typoid A) (P: TypoidFunction (OppositeT TA) Uni) 
                            (u: fobj P a),
  et (@st _ (PiTypoidAppOpp TA P a)) (fobj (TFCompose (HomYaOpPNTr a TA P) (HomYaOpPNTl a TA P)) u) u.
Proof. intros.
       cbn.
       unfold compose.
       simpl.
       destruct P.
       simpl in u, fmap, fmap_pid.
       unfold Setoid.OppositeS_obligation_1 in *.
       simpl.
       specialize (fmap_pid a).
       simpl in fmap_pid.
       destruct (fmap a a (@eqv A (@st A TA) a)).
       simpl in fmap_pid.
       simpl.
       unfold homotopy in fmap_pid.
       specialize (fmap_pid u).
       unfold id in *.
       exact fmap_pid.
Qed.

(** (i o j)(u) = u ??? *)
Lemma HomYaOpPNTEqr: forall {A: Type} (a: A) (TA: Typoid A) (P: TypoidFunction (OppositeT TA) Uni)
                            (sigma: ∏ x : A, ∏ e: x ~> a, fobj P x),
  et (@st _ (HomOp TA (YaOp a TA) P)) (fobj (TFCompose (HomYaOpPNTl a TA P) (HomYaOpPNTr a TA P)) sigma) sigma.
Proof. intros.
       simpl.
       intros x e.
       unfold compose.
       simpl in sigma.
       destruct P.
       simpl in sigma, fmap, e.
       destruct (fmap a x e) as (g, R).
       destruct R as (ginv, (ob1, (ob2, ob3))).
       unfold homotopy, compose, id in *.
       simpl.
Admitted.
