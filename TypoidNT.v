From UT Require Import Prelims Setoid Typoid TypoidFunction.
Require Import Coq.Classes.CRelationClasses.
Require Import FunctionalExtensionality.

(** natural transformations *)
Class TypoidNT {A B: Type} {TA: Typoid A} {TB: Typoid B} 
                (F: TypoidFunction TA TB) (G: TypoidFunction TA TB): Type :=
  mkTypoidNT
  {
     trans   : ∏ (x: A), (fobj F x) ~> (fobj G x);
     trans_cc: ∏ {x y: A} (e: x ~> y), fmap F e o trans y == trans x o fmap G e;
     TRP     :> ∏ {x: A}, CMorphisms.Proper (@ett B TB (fobj F x) (fobj G x)) (trans x)
  }.

Arguments trans {_ _ _ _ _ _  } _ _ . 

Definition IdNT: forall {A B: Type} {TA: Typoid A} {TB: Typoid B} 
  (F : TypoidFunction TA TB), TypoidNT F F.
Proof. intros A B TA TB (fobj, fmap, cc1, cc2, cc3, cc4).
       unshelve econstructor.
       - simpl. intro X. exact (eqv (fobj X)).
       - simpl. intros X Y f. rewrite Typ1_i, Typ1_ii.
         reflexivity.
       - repeat intro. simpl.
         unfold CMorphisms.Proper.
         easy.
Defined.

Definition ComposeNT
                      (A B: Type)
                      (TA: Typoid A) 
                      (TB: Typoid B)
                      (F  : TypoidFunction TA TB)
                      (G  : TypoidFunction TA TB)
                      (H  : TypoidFunction TA TB)
                      (nt1: TypoidNT F G)
                      (nt2: TypoidNT G H): (TypoidNT F H).
Proof. unshelve econstructor. 
        - intro a. exact (trans nt1 a o trans nt2 a).
        - cbn. intros x y e.
          rewrite <- Typ3. rewrite trans_cc.
          rewrite Typ3. rewrite trans_cc.
          now rewrite Typ3.
        - repeat intro. cbn.
          destruct F, G, H, nt1, nt2.
          cbn. unfold CMorphisms.Proper. easy.
Defined.

Definition FixBiNT1 {A B C: Type}
                     {TA: Typoid A}
                     {TB: Typoid B}
                     {TC: Typoid C}
                     (F: TypoidFunction (ProductTypoid TC TA) TB)
                     (a b: C)
                     (h: et (@st C TC) a b):
  TypoidNT (FixBiF1 a F) (FixBiF1 b F).
Proof. unshelve econstructor.
        - intro x.
          exact (@fmap _ _ _ _ F (a, x) (b, x) (h, (eqv x))).
        - cbn. intros x y e.
          rewrite <- fmap_pcomp.
          destruct F. cbn in *.
          rewrite fmap_p. easy.
          split; now rewrite Typ1_i, Typ1_ii.
        - repeat intros.
          now unfold CMorphisms.Proper.
Defined.


(* Lemma NT_split: forall (A B: Type)
                       (TA: Typoid A)
                       (TB: Typoid B)
                       (F G  : TypoidFunction TA TB) 
                       (nt1 nt2: TypoidNT F G), trans nt1 == trans nt2 -> nt1 = nt2.
Proof. intros. split. intros. destruct nt1, nt2, F, G.
       simpl in *. subst.
       f_equal.
       destruct (proof_irrelevance _ trans_cc0 trans_cc1).
        rewrite H. intros.
       specialize (proof_irrelevance (forall (a b : @obj C) (f : arrow b a),
             fmap0 a b f o trans1 a = trans1 b o fmap a b f) comm_diag0 comm_diag1).
       now destruct (proof_irrelevance _ comm_diag0 comm_diag1).
       intros. rewrite H. easy.
Qed.
 *)


