From UT Require Import Prelims Setoid Typoid TypoidFunction TypoidNT ExponentialTypoid.
Require Import Coq.Classes.CRelationClasses.
Require Import FunctionalExtensionality.
Set Universe Polymorphism.


(*
(** the setoid of Coq types *)
Definition CoqSetoidT: Setoid Type.
Proof. unshelve econstructor.
        - exact iffT.
        - intro x. easy.
        - intros x y z (f, invf) (g, invg).
          split.
          + exact (compose f g).
          + exact (compose invg invf).
        - intros x y (f, invf).
          split.
          + exact invf.
          + exact f.
Defined.

(** the typoid of Coq types *)
Definition CoqTypoidT: Typoid Type.
Proof. unshelve econstructor.
        - exact CoqSetoidT.
        - cbn. intros x y (f, invf) (g, invg).
          exact (forall a: x, Id (f a) (g a)).
        - intros x y (f, invf) a. easy.
        - intros x y (f, invf) (g, invg) H. easy.
        - intros x y (f, invf) (g, invg) (h, invh) F G a.
          exact (concat (F a) (G a)).
        - intros x y (f, invf) a. easy.
        - intros x y (f, invf) a. easy.
        - intros x y (f, invf) a.
 *)

(* 
Class invertible (A B: Type) :=
  mk_invertible
  {
     fun_f    : A -> B;
     inverse_f: B -> A;
     inv_cc1  : forall a: A, Id (inverse_f (fun_f a)) a;
     inv_cc2  : forall b: B, Id (fun_f (inverse_f b)) b
  }.

(** the setoid of Coq types *)
Definition CoqST: Setoid Type.
Proof. unshelve econstructor.
        - exact (fun A B => invertible A B).
        - cbn. intro A.
          unshelve econstructor.
          + exact (@id A).
          + exact (@id A).
          + easy.
          + easy.
        - cbn. intros x y z i1 i2.
          unshelve econstructor. 
          + exact (compose (@fun_f x y i1) (@fun_f y z i2)).
          + exact (compose (@inverse_f y z i2) (@inverse_f x y i1)).
          + intro a.
            destruct i1, i2. cbn.
            specialize (inv_cc5 (fun_f0 a)).
            specialize (ap inverse_f0 inv_cc5); intros.
            now induction (inv_cc3 a).
          + intro b.
            destruct i1, i2. cbn.
            specialize (inv_cc4 (inverse_f1 b)).
            specialize (ap fun_f1 inv_cc4); intros.
            now induction (inv_cc6 b).
        - cbn. intros x y i.
          destruct i.
          unshelve econstructor.
          + exact inverse_f0.
          + exact fun_f0.
          + easy.
          + easy.
Defined.

(** the typoid of Coq types *)
Definition CoqTT: Typoid Type.
Proof. unshelve econstructor.
        - exact CoqST.
        - intros x y f g.
          exact (forall a: x, Id (@fun_f x y f a) (@fun_f x y g a)).
        - cbn. easy.
        - cbn. easy.
        - cbn. intros.
          exact (concat (X a) (X0 a)).
        - cbn. easy.
        - cbn. easy.
        - intros.
          destruct e. cbn in *. easy.
        - intros. 
          destruct e. cbn in *. easy.
        - easy.
        - cbn. intros.
          destruct e1, e2, d1, d2. cbn in *.
          specialize (X a).
          now induction X.
        - repeat intro.
          destruct x0, y0, x1, y1.
          cbn in *. 
          specialize (X a).
          now induction X.
        - easy.
        - do 5 intro. destruct x0, y0.
          cbn in *. intro b.
          specialize (X  (inverse_f1 b)).
          assert (Id (fun_f0 (inverse_f1 b)) (fun_f0 (inverse_f0 b))).
          { specialize (inv_cc4 b).
            induction inv_cc4.
            specialize (inv_cc6 a).
            now induction inv_cc6.
          }
          specialize (inv_cc4 b).
          induction inv_cc4.
          pose proof inv_cc3 as BB.
          specialize (inv_cc3 (inverse_f1 a)).
          induction inv_cc3.
          specialize (BB a0).
          induction X0. easy.
Defined.
 *)




(*
Definition ProductSetoid {A B: Type} (SA: Setoid A) (SB: Setoid B): Setoid (dirprod A B).
Proof. unshelve econstructor.
       - intros a b.
         exact (dirprod (@et A SA (pr1 a) (pr1 b)) (@et B SB (pr2 a) (pr2 b))).
       - cbn. intro z. 
         exact ({ eqv(pr1 z) ; eqv(pr2 z) }).
       - cbn. intros z w u (e1, e2) (d1, d2).
         exact ({ (e1 o d1) ; (e2 o d2) }).
       - cbn. intros z w (e1, e2).
         exact ({ (inv e1) ; (inv e2) }).
Defined.

Definition ProductTypoid: ∏ {A B: Type} (TA: Typoid A) (TB: Typoid B), Typoid (dirprod A B).
Proof. intros.
       unshelve econstructor.
       - exact (ProductSetoid (@st A TA) (@st B TB)).
       - unfold relation. cbn. intros z w (e1, e2) (e1', e2').
         exact (dirprod (e1 == e1') (e2 == e2')).
       - cbn. intros. destruct e.
         split; apply ett_refl.
       - cbn. intros. destruct e, d.
         destruct X. split. now rewrite pr7. now rewrite pr8.
       - cbn. intros. destruct e, d, f, X, X0.
         split. now rewrite pr9, pr11. now rewrite pr10, pr12.
       - cbn. intros. destruct e.
         split; now rewrite Typ1_i.
       - cbn. intros. destruct e. cbn in *.
         split; now rewrite Typ1_ii.
       - cbn. intros. destruct e. cbn in *.
         split; now rewrite Typ2_i.
       - cbn. intros. destruct e. cbn in *.
         split; now rewrite Typ2_ii.
       - cbn. intros. destruct e1, e2, e3. cbn in *.
         split; now rewrite Typ3.
       - cbn. intros. destruct e1, e2, d1, d2, X, X0. cbn in *.
         split; now rewrite Typ4.
        - cbn. repeat intro. destruct x0, y0, x1, y1, X, X0. cbn in *.
         split; apply Typ4; easy. 
       - cbn. repeat intro. easy.
       - cbn. repeat intro. destruct x0, y0, X. cbn in *.
         split. now rewrite pr7. now rewrite pr8.
Defined.

*)







(* Parameters (A: Type) (x y: A) (T: Typoid A) (p: Id x y) (f: @et _ (@st _ T) x y).
Check @et A (@st A T) x y.

Check @ett A T x y f f.

Definition idtoeqvT2: ∏ {A: Type} {x y: A} {T: Typoid A} (p: Id x y), @ett A T x y.
Proof. intros A x y T p.
        exact (transport (fun z => x ~> z) p (eqv x)).
Defined.
 *)

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

(*
Definition PresheafTypoidT {A: Type} (TA : Typoid A) := 
  ExponentialTypoid (OppositeT TA) UniT.

Definition YonedaTypoidT {A: Type} (TA : Typoid A): 
  TypoidFunction TA (PresheafTypoidT TA).
Proof. unshelve econstructor.
       - intro X.
         unshelve econstructor.
         + intro Z. simpl in *.
           exact (Id Z X).
         + simpl. 
           intros Y Z f.
           
           apply UATT.
           exists (fun p: Y ~> X => f o p).
           apply qinv_ishae.
           unshelve econstructor.
           ++ exact (fun p => inv f o p).
           ++ split.
              * red. intro g.
                unfold compose, id.
                apply UATT.
                rewrite <- Typ3, Typ2_i, Typ1_i.
                reflexivity.
              * red. intro g.
                unfold compose, id.
                apply UATT.
                rewrite <- Typ3, Typ2_ii, Typ1_i.
                reflexivity.
         + simpl. intro Y.
           red. intro g.
           unfold id.
           apply UATT.
           unfold Setoid.OppositeS_obligation_1.
           rewrite Typ1_i.
           reflexivity.
         + simpl. intros Y Z W f g h.
           apply UATT.
           unfold compose, Setoid.OppositeS_obligation_2.
           rewrite Typ3.
           reflexivity.
         + simpl. intros Y Z f g H.
           red. intro h.
           apply UATT.
           rewrite H.
           reflexivity.
         + repeat intro. apply UATT in X0.
           now induction X0.
       - intros X Y f.
         unshelve econstructor.
         + intro Z. simpl.
           exists (fun p: Z ~> X => p o f).
           apply qinv_ishae.
           unshelve econstructor.
           ++ exact (fun p: Z ~> Y => p o (inv f)).
           ++ red. unfold homotopy, compose, id.
              split.
              * intro g.
                apply UATT.
                rewrite Typ3.
                rewrite Typ2_ii.
                rewrite Typ1_ii.
                reflexivity.
              * intro g.
                apply UATT.
                rewrite Typ3, Typ2_i.
                rewrite Typ1_ii.
                reflexivity.
         + intros Z W g.
           simpl.
           unfold homotopy, compose, id.
           intro h.
           apply UATT.
           rewrite Typ3.
           reflexivity.
         + repeat intro.
           apply refl.
       - intro X.
         simpl.
         intro Y.
         unfold homotopy, Setoid.OppositeS_obligation_1.
         intro f.
         apply UATT.
         rewrite Typ1_ii.
         reflexivity.
       - intros X Y Z f g.
         simpl.
         intros W h.
         apply UATT.
         unfold compose.
         rewrite Typ3.
         reflexivity.
       - intros X Y f g H.
         simpl.
         intro Z.
         unfold homotopy.
         intro h.
         apply UATT.
         rewrite H.
         reflexivity.
       - repeat intro.
         simpl in a0.
         apply UATT.
         rewrite X.
         reflexivity.
Defined. *)


Definition Ya {A: Type} (a: A) (TA: Typoid A): TypoidFunction TA Uni.
Proof. unshelve econstructor.
       - intro x.
         exact (et (@st A TA) x a).
       - simpl. intros x y f.
         unshelve econstructor.
         + intro g.
           exact (inv f o g).
         + apply qinv_ishae.
           unshelve econstructor.
           ++ intros g.
              exact (f o g).
           ++ unfold homotopy, compose.
              split.
              * intros g.
                apply UATT.
                rewrite <- Typ3.
                rewrite Typ2_ii.
                rewrite Typ1_i.
                unfold id.
                reflexivity.
              * intros g.
                apply UATT.
                rewrite <- Typ3.
                rewrite Typ2_i.
                rewrite Typ1_i.
                unfold id.
                reflexivity.
       - simpl. unfold homotopy, id.
         intros x f.
         apply UATT.
         rewrite Typ9.
         reflexivity.
       - simpl. intros x y z f g.
         unfold homotopy, id, compose.
         intros h.
         apply UATT.
         rewrite Typ5.
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

Definition PiTypoid: forall {A: Type} (TA: Typoid A) (P: TypoidFunction TA Uni), 
  Typoid (forall x: A, fobj P x).
Proof. intros A TA P.
       simpl.
       unshelve econstructor.
       - unshelve econstructor.
         + unfold crelation.
           intros phi Q.
(*            exact (forall x: A, (et (@st _ Uni) (phi x) (Q x))). *)
           exact (forall x: A, (Id (phi x) (Q x))).
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

Definition PiTypoidA: forall {A: Type} (a: A) (TA: Typoid A) (P: TypoidFunction TA Uni), 
  Typoid (fobj P a).
Proof. intros A a TA P.
       simpl.
       unshelve econstructor.
       - unshelve econstructor.
         + unfold crelation.
           intros phi Q.
(*            exact (forall x: A, (et (@st _ Uni) (phi x) (Q x))). *)
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

Definition PQNT: forall {A: Type} (TA: Typoid A) (P Q: TypoidFunction TA Uni),
  Typoid (forall x: A, fobj P x -> fobj Q x).
Proof. intros A TA P Q.
       unshelve econstructor.
       - unshelve econstructor.
         + unfold crelation.
           intros phi psi.
           exact (forall x: A, (Id (phi x) (psi x))).
         + simpl. intros p q.
           apply refl. 
         + simpl. intros p q r Hp Hq x.
           specialize (@concat _ (p x) (q x) (r x) (Hp x) (Hq x)); intro C.
           exact C.
         + simpl. intros p q Hp x.
           exact (inverse (Hp x)).
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

Definition YaPNTr: forall {A: Type} (a: A) (TA: Typoid A) (P: TypoidFunction TA Uni),
  TypoidFunction (PiTypoidA a TA P) (PQNT TA (Ya a TA) P).
Proof. intros A a TA P.
       unshelve econstructor.
       - simpl. intros fp x f.
         destruct P.
         destruct (fmap a x (inv f)) as (g, geq).
         exact (g fp).
       - simpl. intros px py q x.
         induction q.
         apply refl.
       - simpl. intros px x.
         apply refl.
       - simpl. intros px py pz p q x.
         induction p.
         induction q.
         apply refl.
       - simpl. intros px py p q r x.
         induction p.
         induction r.
         apply refl.
       - repeat intro.
         simpl in X.
         induction X.
         apply refl.
Defined.

Definition YaPNTl: forall {A: Type} (a: A) (TA: Typoid A) (P: TypoidFunction TA Uni),
  TypoidFunction (PQNT TA (Ya a TA) P) (PiTypoidA a TA P).
Proof. intros A a TA P.
       unshelve econstructor.
       - intro v.
         exact (v a (eqv a)).
       - simpl. intros p q Hp.
(*          assert (pp: Id p q).
         { apply funext. easy. } *)
         specialize (Hp a).
         induction Hp.
         apply refl.
       - simpl. intros p.
         apply refl.
       - simpl. intros p q r Hp Hq.
         unfold Id_rect.
Admitted.

(* Lemma YaPNTEq: forall {A: Type} (a: A) (TA: Typoid A) (P: TypoidFunction TA Uni),
  Id (TFCompose (YaPNTl a TA P) (YaPNTr a TA P)) (IdTF (PQNT TA (Ya a TA) P) ). *)

Definition PresheafTypoid {A: Type} (TA : Typoid A) := 
  ExponentialTypoid (OppositeT TA) Uni.

Definition YonedaTypoid {A: Type} (TA : Typoid A): 
  TypoidFunction TA (PresheafTypoid TA).
Proof. unshelve econstructor.
       - intro X.
         unshelve econstructor.
         + intro Z.
           exact (et (@st _ TA) Z X).
         + simpl. 
           intros Y Z f.
           exists (fun p: Y ~> X => f o p).
           apply qinv_ishae.
           unshelve econstructor.
           ++ exact (fun p => inv f o p).
           ++ split.
              * red. intro g.
                unfold compose, id.
                apply UATT.
                rewrite <- Typ3, Typ2_i, Typ1_i.
                reflexivity.
              * red. intro g.
                unfold compose, id.
                apply UATT.
                rewrite <- Typ3, Typ2_ii, Typ1_i.
                reflexivity.
         + simpl. intro Y.
           red. intro g.
           unfold id.
           apply UATT.
           unfold Setoid.OppositeS_obligation_1.
           rewrite Typ1_i.
           reflexivity.
         + simpl. intros Y Z W f g h.
           apply UATT.
           unfold compose, Setoid.OppositeS_obligation_2.
           rewrite Typ3.
           reflexivity.
         + simpl. intros Y Z f g H.
           red. intro h.
           apply UATT.
           rewrite H.
           reflexivity.
         + repeat intro. apply UATT in X0.
           now induction X0.
       - intros X Y f.
         unshelve econstructor.
         + intro Z. simpl.
           exists (fun p: Z ~> X => p o f).
           apply qinv_ishae.
           unshelve econstructor.
           ++ exact (fun p: Z ~> Y => p o (inv f)).
           ++ red. unfold homotopy, compose, id.
              split.
              * intro g.
                apply UATT.
                rewrite Typ3.
                rewrite Typ2_ii.
                rewrite Typ1_ii.
                reflexivity.
              * intro g.
                apply UATT.
                rewrite Typ3, Typ2_i.
                rewrite Typ1_ii.
                reflexivity.
         + intros Z W g.
           simpl.
           unfold homotopy, compose, id.
           intro h.
           apply UATT.
           rewrite Typ3.
           reflexivity.
         + repeat intro.
           apply refl.
       - intro X.
         simpl.
         intro Y.
         unfold homotopy, Setoid.OppositeS_obligation_1.
         intro f.
         apply UATT.
         rewrite Typ1_ii.
         reflexivity.
       - intros X Y Z f g.
         simpl.
         intros W h.
         apply UATT.
         unfold compose.
         rewrite Typ3.
         reflexivity.
       - intros X Y f g H.
         simpl.
         intro Z.
         unfold homotopy.
         intro h.
         apply UATT.
         rewrite H.
         reflexivity.
       - repeat intro.
         simpl in a0.
         apply UATT.
         rewrite X.
         reflexivity.
Defined.

Class UnivalentTypoid (A: Type): Type :=
   mkUnivalentTypoid
   {
      TT         :  Typoid A;
      Ua         :  ∏ {x y: A} (e: x ~> y), Id x y;
      Ua2        :  ∏ {x y: A} {e d: x ~> y} (i: e == d), Id (Ua e) (Ua d);
      UT_ob1     :  ∏ {x y: A} (p: Id x y), Id (Ua (@idtoeqvT A x y TT p)) p;
      UT_ob2     :  ∏ {x y: A} (e: x ~> y), @idtoeqvT A x y TT (Ua e) == e;
   }.

Lemma YonedaEmbedding {A: Type} (TA: Typoid A) (X: A) (F: TypoidFunction (OppositeT TA) Uni):
  Equiv (et (@st _ (PresheafTypoid TA)) (fobj (YonedaTypoid TA) X) F)
        (fobj F X).
Proof. unfold Equiv.
       unshelve econstructor.
       - intros (phi, cc1, cc2).
         destruct (phi X) as (phiX, R).
         exact (phiX (eqv X)).
       - apply h249_i.
         unshelve econstructor.
         + intros fx.
           unshelve econstructor.
           simpl.
           ++ intros Y.
              unshelve econstructor.
              +++ simpl. intro f.
                  destruct (fmap F f) as (fmapf, R).
                  exact (fmapf fx).
              +++ apply qinv_ishae.
                  destruct F.
                  simpl in fx, fmap.
                  simpl.
                  unshelve econstructor.
                  * intros fy.
                    clear fmap_pid fmap_pcomp fmap_p TP.
                    specialize (fmap  X Y).
                    simpl in fmap.
                    admit.
                  * unshelve econstructor.
Admitted.


Definition Yoneda {A: Type} {a: A} (TA: Typoid A): TypoidFunction TA Uni.
Proof. unshelve econstructor.
       - intro x. exact (et (@st _ TA) x a).
       - cbn. intros x y e.
         exists (fun p: x ~> a => (inv e) o p).
         apply qinv_ishae.
         unshelve econstructor.
         + exact (fun p => e o p).
         + split.
           ++ red. intro f. unfold compose, id.
              eapply UATT.
              now rewrite <- Typ3, Typ2_ii, Typ1_i.
           ++ red. intro f. unfold compose, id.
              eapply UATT.
              now rewrite <- Typ3, Typ2_i, Typ1_i.
       - cbn. intro x. red. intro e. unfold id.
         eapply UATT. now rewrite Typ9.
       - cbn. intros x y z e d f.
         unfold compose.
         apply UATT. now rewrite Typ5, Typ3.
       - cbn. intros x y e d i. red. intro p.
         apply UATT in i. now induction i.
       - repeat intro. apply UATT in X.
         now induction X.
Defined.

Definition CurHomT {A: Type} (TA: Typoid A): 
  TypoidFunction (ProductTypoid (OppositeT TA) TA) TypoidUni.
Proof. unshelve econstructor.
       intros.
       - exact (et (@st _ TA) (fst X) (snd X)). 
       - cbn. intros x y f.
         destruct f as (e, p). cbn in *.
         destruct x, y. cbn in *.
         exists (fun f: a ~> a0 => e o f o p).
         apply qinv_ishae.
         unshelve econstructor.
         + intro f. exact ((inv e) o f o (inv p)).
         + split.
           ++ red. cbn. unfold compose, id. intro f.
              eapply UATT. repeat rewrite Typ3.
              now rewrite Typ2_ii, Typ1_ii, <- Typ3, Typ2_i, Typ1_i.
           ++ red. intro f. unfold compose, id.
              apply UATT. repeat rewrite Typ3.
              now rewrite Typ2_i, Typ1_ii, <- Typ3, Typ2_ii, Typ1_i.
       - intros. destruct x. cbn. red. intro f.
         apply UATT. unfold Setoid.OppositeS_obligation_1, id.
         now rewrite Typ1_i, Typ1_ii.
       - intros. destruct x. destruct y. destruct z.
         destruct e1, e2. cbn in *.
         red. intro f.
         apply UATT. unfold compose, Setoid.OppositeS_obligation_2.
         now repeat rewrite Typ3.
       - intros. destruct x, y. destruct e, d.
         cbn in *. red. 
         intro f. apply UATT.
         destruct i as (i, j).
         now rewrite i, j.
       - repeat intro. destruct x, y.
         destruct x0, y0. cbn in *.
         red. intro f.
         apply UATT. destruct X as (i, j).
         now rewrite i, j.
Defined.

Definition Flatten {A: Type} {TA: Typoid A}
                   (F: TypoidFunction (ProductTypoid (OppositeT (OppositeT TA)) (OppositeT TA)) TypoidUni): 
                   TypoidFunction (ProductTypoid TA (OppositeT TA)) TypoidUni.
Proof. destruct F.
       unshelve econstructor.
       - exact fobj.
       - exact fmap.
       - intros. now rewrite fmap_pid.
       - intros. now rewrite fmap_pcomp.
       - easy.
       - repeat intro. now rewrite X.
Defined.

Definition Twist {A B: Type} (TA: Typoid A) (TB: Typoid B): 
  TypoidFunction (ProductTypoid TA TB) (ProductTypoid TB TA).
Proof. unshelve econstructor.
      - intro a. exact (snd a, fst a).
      - intros x y f. exact (snd f, fst f).
      - easy.
      - intros (a, b) (c, d) (e, f) (e1, e2) (e3, e4). cbn in *. easy.
      - intros (a, b) (c, d) (e1, e2) (d1, d2) (i, j). cbn. easy.
      - repeat intro. destruct x0, y0. cbn in *.
        destruct X as (i, j). split. now rewrite j. now rewrite i.
Defined.


Definition YonedaEmbeddingA {A: Type} (TA: Typoid A): 
  TypoidFunction TA (ExponentialTypoid (OppositeT TA) (TypoidUni)) :=
  CurryF (@Flatten A TA (@CurHomT A (OppositeT TA))).

Definition YonedaL {A: Type} (TA: Typoid A):
  TypoidFunction (ProductTypoid (OppositeT TA) (ExponentialTypoid (OppositeT TA) (TypoidUni))) (TypoidUni) :=
  ComposeTF (ProductTypoidFunction (OppositeTF (YonedaEmbeddingA TA)) (IdTF (ExponentialTypoid (OppositeT TA) (TypoidUni))))
            (@CurHomT _ (ExponentialTypoid (OppositeT TA) (TypoidUni))).

Definition YonedaR {A: Type} (TA: Typoid A): 
  TypoidFunction (ProductTypoid (OppositeT TA) (ExponentialTypoid (OppositeT TA) TypoidUni)) TypoidUni :=
  ComposeTF (Twist _ _ ) (EvalF (OppositeT TA) TypoidUni).

Definition YonedaLR {A: Type} (TA: Typoid A): TypoidNT (YonedaL TA) (YonedaR TA).
Proof. unshelve econstructor.
       - intros (X, F).
         unshelve econstructor.
         + intros (f, ob1, ob2).
           simpl.
           simpl in f.
           clear ob1 ob2.
           specialize (f X ).
           destruct f as (fx, R).
           exact (fx (eqv X)).
         + unshelve econstructor.
           ++ intros f.
              simpl in f.
              unshelve econstructor.
              * simpl. intro Y.
                destruct F.
                simpl in f.
                simpl.
                destruct TA, st.
                simpl.
Admitted.

Definition YonedaRL {A: Type} (TA: Typoid A): TypoidNT (YonedaR TA) (YonedaL TA).
Admitted.



(* Definition TypeUni: UnivalentTypoid Type.
Proof. unshelve econstructor.
       - exact Uni.
       - unfold et. cbn.
         intros x y e.
         destruct e as (f, e).
         exact (ua_ishae {f; e}).
       - cbn. intros.
         destruct e as (f, u).
         destruct d as (g, w).
         unfold ua_ishae.
         apply funext in i.
         induction i.
         now induction (ishae_isProp a u w).
       - cbn. intros.
         unfold idtoeqvT, transport, Id_rect.
         induction p. cbn.
         unfold ua_ishae.
         destruct (UA_ishae a a) as (p, q).
         destruct q as (eta, (eps, r)).
         unfold homotopy, compose, id in *.
         clear r.
         specialize (eta refl).
         unfold idtoeqv_ishae in eta. cbn in eta.
         easy.
       - cbn. intros.
         unfold idtoeqvT, transport, Id_rect, ua_ishae.
         destruct e as (f, p). cbn.
         remember @ua_ishae.
         clear Heqi.
         specialize (@i  x y {f; p}).
         induction i. 
         destruct (UA_ishae a a) as (q, cc).
         destruct cc as (eta, (eps, r)).
         unfold homotopy, compose, id in *.
         specialize (r (q {f; p})). cbn in r.
         clear r. cbn in *.
         specialize (eps {f; p}).
         cbn in eps. dependent destruction eps.
         clear H.
         specialize (eta (q {f; p})).
         cbn. dependent destruction eta.
         unfold transport, Id_rect in x0. cbn in x0.
         clear x1 x.
         destruct (q {f; p} ). intro x.
         rewrite <- x0. easy.
Defined.

(** Universe of Typoids [correspondingly Category of Sets] *)
Definition UniTypoidUni: UnivalentTypoid Type.
Proof. unshelve econstructor.
       - exact TypoidUni.
       - cbn. intros. destruct e as (e, He).
         eapply UA_ishae.
         unshelve econstructor. 
         + exact e.
         + easy.
       - cbn. intros.
         destruct e, d. red in i.
         apply FE in i. induction i. 
         now induction (ishae_isProp a pr4 pr6).
       - cbn. intros.
         unfold idtoeqvT, transport, Id_rect, Id_ind.
         induction p. cbn. unfold id.
         destruct (UA_ishae a a) as (p, q).
         destruct q as (eta, (eps, r)).
         unfold homotopy, compose, id in *. cbn.
         clear r.
         specialize (eta refl).
         unfold idtoeqv_ishae in eta. cbn in eta.
         easy.
       - cbn. intros.
         unfold idtoeqvT, transport, Id_rect, Id_ind.
         destruct e as (f, p). cbn.
         remember @ua_ishae.
         clear Heqi.
         specialize (@i  x y {f; p}).
         induction i. 
         destruct (UA_ishae a a) as (q, cc).
         destruct cc as (eta, (eps, r)).
         unfold homotopy, compose, id in *. cbn.
         specialize (r (q {f; p})). cbn in r.
         clear r. cbn in *.
         specialize (eps {f; p}).
         cbn in eps. dependent destruction eps.
         clear H.
         specialize (eta (q {f; p})).
         cbn. dependent destruction eta.
         unfold transport, Id_rect in x0. cbn in x0.
         clear x1 x.
         destruct (q {f; p} ). intro x.
         rewrite <- x0. easy.
Defined.  *)



