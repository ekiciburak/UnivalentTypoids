From UT Require Import Prelims Setoid Typoid.
Require Import Coq.Classes.CRelationClasses.
Require Import FunctionalExtensionality.

(** functors *)
Class TypoidFunction {A B: Type} (X: Typoid A) (Y: Typoid B): Type :=
   mkTypoidFunction 
   {
      fobj      :  A -> B;
      fmap      :  ∏ {x y: A}, x ~> y -> (fobj x ~> fobj y);
      fmap_pid  :  ∏ (x: A), fmap (eqv x) == eqv (fobj x);
      fmap_pcomp:  ∏ (x y z: A) (e1: x ~> y) (e2: y ~> z), fmap (e1 o e2) == fmap e1 o fmap e2;
      fmap_p    :  ∏ {x y: A} (e d: x ~> y) (i: e == d), fmap e == fmap d;
      TP        :> ∏ {x y}, CMorphisms.Proper (@CMorphisms.respectful _ _ (@ett A X x y) (@ett B Y (fobj x) (fobj y))) (@fmap x y); 
   }.

(* Notation "x '~~>' y"  := (TypoidFunction x y) : type_scope.*)
Arguments fobj {_ _ _ _} _ _ . 
Arguments fmap {_ _ _ _ } _ {_ _}  _ .
Arguments fmap_p {_ _} _ {_ _ _ _}  _ .

Definition TFCompose {A B C: Type} {TA: Typoid A} {TB: Typoid B} {TC: Typoid C}
                     (F: TypoidFunction TA TB) (G: TypoidFunction TB TC): TypoidFunction TA TC.
Proof. unshelve econstructor.
       + destruct F, G.
         exact (compose fobj0 fobj1).
       + destruct F, G. cbn in *. intros. unfold compose.
         exact (fmap1 _ _ (fmap0 x y X)).
       + destruct F, G. cbn in *. intros. unfold compose.
         now rewrite fmap_pid0, fmap_pid1.
       + destruct F, G. cbn in *. intros. unfold compose.
         now rewrite fmap_pcomp0, fmap_pcomp1.
       + destruct F, G. cbn in *. intros. unfold compose.
         now rewrite (fmap_p0 x y e d i).
       + destruct F, G. repeat intro. now rewrite X.
Defined.

Lemma fmap_pinv {A B: Type} {C: Typoid A} {D: Typoid B} (F: TypoidFunction C D):
   ∏ (x y: A) (e: x ~> y), fmap F (inv e) == inv (fmap F e). 
Proof. intros.
       assert (fmap F (inv e) o (fmap F e) == inv (fmap F e) o (fmap F e)).
       { setoid_rewrite Typ2_ii.
         setoid_rewrite <- fmap_pcomp.
         rewrite Typ2_ii.
         now setoid_rewrite fmap_pid. }
       assert (fmap F (inv e) o (fmap F e) o inv (fmap F e) == 
               inv (fmap F e) o (fmap F e) o inv (fmap F e)).
       { now setoid_rewrite X. }
       now rewrite !Typ3, !Typ2_i, !Typ1_ii in X0.
Qed.

Definition Typfun {A B: Type} (TA: Typoid A) (TB: Typoid B) (f: A -> B) :=
    ∑ thef: ∏ (x y: A) (e: x ~> y), (f x) ~> (f y),
    dirprod 
    (∏ (x y z: A) (e: x ~> y) (d: y ~> z), 
      dirprod ((thef x x (eqv x)) == (eqv (f x))) 
              ((thef x z (e o d)) == ((thef x y e) o (thef y z d)))
    )
    (∏ (x y: A) (e d: x ~> y) (i: e == d), (thef x y e) == (thef x y d)
    ).

Definition product {A B C D: Type} (f: A -> B) (g: C -> D): A * C -> B * D.
Proof. intros (a, c). exact (f a, g c). Defined.

Definition IdTF {A: Type} (TA: Typoid A): TypoidFunction TA TA.
Proof. unshelve econstructor.
       - exact id.
       - intros. exact X.
       - now unfold id.
       - easy.
       - easy.
       - easy.
Defined.

Definition ComposeTF {A B C: Type} {TA: Typoid A} {TB: Typoid B} {TC: Typoid C}
                     (f: TypoidFunction TA TB) (g: TypoidFunction TB TC): TypoidFunction TA TC.
Proof. unshelve econstructor.
       - exact (fun a => (fobj g (fobj f a))).
       - intros x y e. unfold compose.
         exact (fmap g (fmap f e)).
       - cbn. intros. unfold compose.
         now do 2 rewrite <- fmap_pid.
       - cbn. intros.
         now do 2 rewrite fmap_pcomp.
       - cbn. intros. now rewrite i.
       - repeat intro. now rewrite X.
Defined.

Definition OppositeTF {A B: Type} {TA: Typoid A} {TB: Typoid B} (F: TypoidFunction TA TB): 
  TypoidFunction (OppositeT TA) (OppositeT TB).
Proof. unshelve econstructor.
       - exact (fobj F).
       - intros x y f. exact (fmap F f).
       - cbn. intros.
         unfold Setoid.OppositeS_obligation_1.
         now rewrite fmap_pid.
       - cbn. intros. unfold Setoid.OppositeS_obligation_2.
         now rewrite fmap_pcomp.
       - cbn. intros. now rewrite i.
       - repeat intro. now rewrite X.
Defined.

(* 
Class product {A B C D: Type} (f: A -> B) (g: C -> D): Type :=
  mk_product 
  {
     prod_fg    : A * C -> B * D;
     prod_cc1   : forall x: A * C, Id (f (fst x)) (fst (prod_fg x));
     prod_cc2   : forall x: A * C, Id (g (snd x)) (snd (prod_fg x));
     prod_unique: forall (ap: A * C -> B * D) (x: A * C),
                  (Id (f (fst x)) (fst (ap x)) *
                   Id (g (snd x)) (snd (ap x)))%type -> Id (ap x) (prod_fg x)
  }.

*)

Definition ProductTypoidFunction {A B C D: Type}
                                  {TA: Typoid A}
                                  {TB: Typoid B}
                                  {TC: Typoid C}
                                  {TD: Typoid D}
                                  (F: TypoidFunction TA TC)
                                  (G: TypoidFunction TB TD):
  TypoidFunction (ProductTypoid TA TB) (ProductTypoid TC TD).
Proof. unshelve econstructor.
        - exact (product (fobj F) (fobj G)).
        - intros (a1, b1) (a2, b2) (e1, e2).
          exact ((fmap F e1), (fmap G e2)).
        - intros (a, b).
          split; now rewrite fmap_pid.
        - intros (a1, b1) (a2, b2) (a3, b3) (e1, e2) (d1, d2).
          split; now rewrite fmap_pcomp.
        - intros (a1, b1) (a2, b2) (a3, b3) (e1, e2) (p, q).
          split.
          + now rewrite p.
          + now rewrite q.
        - repeat intro. 
          destruct x as (a1, b1).
          destruct y as (a2, b2).
          destruct x0 as (e1, e2).
          destruct y0 as (e3, e4).
          destruct X as (p, q).
          split.
          + now rewrite p.
          + now rewrite q.
Defined.

(* Example TypoidTypoids (A: Type): Typoid (Typoid A).
Proof. unshelve econstructor.
       - unshelve econstructor.
         + unfold crelation.
           intros F G.
           exact (TypoidFunction F G).
         + intros TA. simpl.
           exact (IdTF TA).
         + simpl. intros T1 T2 T3 F G.
           exact (ComposeTF F G).
         + simpl. intros T1 T2 F.
           destruct F.
           unshelve econstructor.
           ++ exact id.
           ++  *)

Definition FixBiF1 {A B C: Type} 
                    {TA: Typoid A}
                    {TB: Typoid B}
                    {TC: Typoid C}
                    (x: A)
                    (F: TypoidFunction (ProductTypoid TA TB) TC):
  TypoidFunction TB TC.
Proof. unshelve econstructor.
        - intro y. exact (fobj F (x, y)).
        - cbn. intros a b f.
          exact (@fmap _ _ _ _ F (x, a) (x, b) ((eqv x), f)).
        - intro b. now rewrite fmap_pid.
        - intros a b c e1 e2.
          rewrite <- fmap_pcomp.
          destruct F. rewrite fmap_p0. easy.
          split.
          + now rewrite Typ1_i.
          + easy.
        - intros a b e d p. cbn.
          destruct F. rewrite fmap_p0. easy.
          split.
          + easy.
          + now rewrite p.
        - repeat intro. cbn. destruct F. cbn in *.
          rewrite fmap_p0. easy.
          split; easy.
Defined.

