From UT Require Import Prelims Setoid Typoid TypoidFunction TypoidNT ExponentialTypoid Yoneda.
Require Import Coq.Classes.CRelationClasses.
Require Import FunctionalExtensionality.
Set Universe Polymorphism.


Require Import Coq.Program.Equality.


Class UnivalentTypoid (A: Type): Type :=
   mkUnivalentTypoid
   {
      TT         :  Typoid A;
      Ua         :  ∏ {x y: A} (e: x ~> y), Id x y;
      Ua2        :  ∏ {x y: A} {e d: x ~> y} (i: e == d), Id (Ua e) (Ua d);
      UT_ob1     :  ∏ {x y: A} (p: Id x y), Id (Ua (@idtoeqvT A x y TT p)) p;
      UT_ob2     :  ∏ {x y: A} (e: x ~> y), @idtoeqvT A x y TT (Ua e) == e;
   }.

Proposition h18 {A: Type} (UT: UnivalentTypoid A): (@TT A UT) ~~> (e3 A).
Proof. unshelve econstructor.
       - exact id.
       - intros x y e. unfold id. cbn in *.
         exact (@Ua A UT x y e).
       - cbn. intros.
         exact (@UT_ob1 A UT x x refl).
       - cbn. intros.
         specialize (@UT_ob2 A UT x y e1); intros He1. 
         specialize (@UT_ob2 A UT y z e2); intros He2.
         assert (idtoeqvT (Ua e1) o idtoeqvT (Ua e2) == e1 o e2).
         { now rewrite He1, He2. }
         assert (idtoeqvT (Ua e1) o idtoeqvT (Ua e2) == 
                (@idtoeqvT A x z (@TT A UT) (concat (Ua e1) (Ua e2)) )).
         { specialize (@UT_ob2 A UT _ _ (e1 o e2)); intro HH.
           rewrite He1, He2, <- HH.
           specialize (@UT_ob1 A UT _ _ (concat (Ua e1) (Ua e2))); intro p.
           specialize (@UT_ob1 A UT _ _ (Ua (e1 o e2))); intro q.
           unfold idtoeqvT in *.
           simpl in *.
           induction q, p, a.
           dependent destruction a0. easy.
         }
         rewrite X in X0.
         specialize (@Ua2 A UT _ _ _ _ X0); intros HH.
         specialize (@UT_ob1 A UT _ _ (concat (Ua e1) (Ua e2))); intro HHH.
         apply Id_eql in HH. apply Id_eql in HHH.
         rewrite <- HH in HHH.
         now rewrite HHH.
       - intros. cbn in *.
         exact (@Ua2 A UT x y e d i).
       - repeat intro. 
         specialize (@Ua2 A UT x y x0 y0 X); intro HH.
         apply Id_eql in HH. now rewrite HH.
Defined.

Definition ap2: ∏ {A B: Type} {x y: A} {p q: Id x y} (f: A -> B) (r: Id p q),
  Id (ap f p) (ap f q). 
Proof. intros. now induction r. Defined.

Definition idtoeqvT2: ∏ {A: Type} {T: Typoid A} {x y: A} {p q: Id x y} (r: Id p q),
  @ett A T x y (idtoeqvT p) (idtoeqvT q).
Proof. intros A x y T p q r.
       unfold idtoeqvT. now induction r.
Defined.

Theorem h19_i {A B: Type} (f: A -> B) (U: UnivalentTypoid A) (W: Typoid B): (@TT A U) ~~> W.
Proof. unshelve econstructor.
       - exact f.
       - intros x y e.
         exact (@idtoeqvT B (f x) (f y) W (ap f (Ua e))).
       - cbn. intro a.
         specialize (@UT_ob2 A U _ _ (eqv a)); intro H.
         assert (p: Id (ap f (@fmap A A (@TT A U) (e3 A) (h18 U) a a (eqv a))) (ap f (Ua (eqv a)))).
         { now cbn. }
         induction p. dependent destruction a0. now cbn.
       - cbn. intros.
         specialize (@UT_ob1 A U _ _ (Ua e1)); intro p.
         specialize (@UT_ob1 A U _ _ (Ua e2)); intro q.
         specialize (@UT_ob1 A U _ _ (Ua (e1 o e2))); intro r.
         induction p, q, r, a, a0. dependent destruction a1. cbn.
         now rewrite Typ1_i.
       - intros. cbn.
         unfold idtoeqvT, transport.
         exact (@idtoeqvT2 B W (f x) (f y) (ap f (Ua e)) (ap f (Ua d)) 
                  (@ap2 A B x y (Ua e) (Ua d) f (Ua2 i))).
       - repeat intro. 
         specialize (@Ua2 A U x y x0 y0 X); intro HH.
         apply Id_eql in HH. now rewrite HH.
Defined.

Definition FUni: ∏ {A B: Type}, UnivalentTypoid (A -> B).
Proof. intros.
       unshelve econstructor.
       - exact (e4 A B).
       - unfold et. unfold e4.
         intros. cbn in *.
         apply funext in e. exact e.
       - intros. cbn.
         apply funext in i. now induction i.
       - cbn. intros.
         unfold funext.
         destruct (FE A (λ _ : A, B) x y).
         unfold idtoeqvT, transport, Id_rect. cbn.
         destruct p. cbn in *. destruct pr2 as (pr4, pr5).
         unfold homotopy, compose, id in *. cbn in *.
         specialize (pr5 refl). unfold happly in pr5.
         cbn in *. easy.
       - cbn. intros.
         unfold funext.
         destruct (FE A (λ _ : A, B) x y).
         unfold idtoeqvT, transport, Id_rect. cbn.
         unfold homotopy, compose, id in *. cbn in *. 
         destruct pr2 as (pr4, pr5).
         specialize (pr4 e).
         destruct (pr1 e). cbn in *.
         unfold happly in pr4. cbn in *.
         apply Id_eql in pr4. now rewrite <- pr4.
Defined.

Definition eqUni: ∏ {A: Type}, UnivalentTypoid A.
Proof. intros.
       unshelve econstructor.
       - exact (e3 A).
       - cbn. intros. exact (id e).
       - cbn. intros. unfold id. exact (id i).
       - cbn. intros.
         induction p. cbn. easy.
       - cbn. intros.
         induction e. easy.
Defined.

Definition ua {A B : Type}: (Equiv A B) -> (Id A B).
Proof. destruct (h249_ii (UA A B)) as (eqvtoid, cc).
        exact eqvtoid.
Defined.

Definition ua_ih: ∏ {A B: Type} {f: A -> B} (e : ishae f), Id A B.
Proof. intros.
        apply ishae_isequiv in e.
        exact (ua {f; e}).
Defined.

Definition TypeUni: UnivalentTypoid Type.
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
         unfold idtoeqvT, transport, Id_rect, ua_ih.
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

Proposition h20: ∏ (A B: Type) (x y: A) (p: Id x y) (TA: Typoid A) (TB: UnivalentTypoid B) (f: TA ~~> (@TT B TB))
 (** why i? ― strict typoid function ― how to get that? *) 
               (i: (@fmap _ _ _ _ f x x (eqv x)) == (eqv (@fobj A B TA (@TT B TB) f x)))
 (** why ii ― strict univalence? ― how to get that?  *)  
               (ii: Id (@Ua B TB (@fobj A B TA (@TT B TB) f x) (@fobj A B TA (@TT B TB) f x) (eqv (@fobj A B TA (@TT B TB) f x))) 
                       (refl (@fobj A B TA (@TT B TB) f x))),
  Id (Ua (@fmap _ _ _ _ f x y (@idtoeqvT _ _ _ _ p))) (ap (@fobj A B TA (@TT B TB) f) p).
Proof. intros.
       specialize (@Ua2 B TB _ _ _ _ i); intro HH.
       induction p. cbn in *.
       induction ii.
       exact HH.
Defined.


