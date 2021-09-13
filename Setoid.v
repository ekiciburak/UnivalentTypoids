From UT Require Import Prelims.

Require Import Coq.Classes.CRelationClasses.
Require Import FunctionalExtensionality.

Class Setoid (A: Type): Type :=
   mkSetoid
   {
      et         :  crelation A where "a ~> b" := (et a b);
      eqv        :  ∏ x: A, x ~> x;
      star       :  ∏ {x y z: A}, x ~> y -> y ~> z -> x ~> z where "a 'o' b" := (star a b);
      inv        :  ∏ {x y: A}, x ~> y -> y ~> x;
   }.

Arguments et {_ _} _ _.
Arguments eqv {_ _} _.
Arguments star {_ _ _ _ _} _ _.
Notation "x 'o' y"   := (star x y): type_scope.
Notation "x '~>' y"  := (et x y) : type_scope.

Instance EqRel_et: ∏ {A} {S: Setoid A}, Equivalence (@et A S).
  constructor; intro.
        apply eqv.
        apply (@inv A).
        apply (@star A).
Defined.


Definition OppositeSetoid {A: Type} (S: Setoid A): Setoid A.
Proof. destruct S as (et, cc1, cc2, cc3).
        unshelve econstructor.
        - exact (flip et).
        - exact cc1.
        - intros x y z i1 i2.
          exact (cc2 z y x i2 i1).
        - intros x y.
          exact (cc3 y x).
Defined.

Program Definition OppositeS {A: Type} (S: Setoid A): Setoid A := {|
  et   := fun x y => y ~> x
  |}.
Next Obligation. exact (eqv x). Defined.
Next Obligation. exact (X0 o X). Defined.
Next Obligation. exact (inv X). Defined.

Definition ProductSetoid {A B: Type} (SA: Setoid A) (SB: Setoid B): Setoid (A * B).
Proof. unshelve econstructor.
       - intros a b.
         exact ((@et A SA (fst a) (fst b)) * (@et B SB (snd a) (snd b)))%type.
       - easy.
       - intros x y z Hx Hy.
         destruct Hx, Hy.
         split.
         + exact (e o e1).
         + exact (e0 o e2).
       - cbn. intros x y H.
         destruct H.
         split.
         + exact (inv e).
         + exact (inv e0).
Defined.
