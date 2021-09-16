From UT Require Import Prelims Setoid Typoid TypoidFunction TypoidNT ExponentialTypoid Yoneda.
Require Import Coq.Classes.CRelationClasses.
Require Import FunctionalExtensionality.
Set Universe Polymorphism.


Class UnivalentTypoid (A: Type): Type :=
   mkUnivalentTypoid
   {
      TT         :  Typoid A;
      Ua         :  ∏ {x y: A} (e: x ~> y), Id x y;
      Ua2        :  ∏ {x y: A} {e d: x ~> y} (i: e == d), Id (Ua e) (Ua d);
      UT_ob1     :  ∏ {x y: A} (p: Id x y), Id (Ua (@idtoeqvT A x y TT p)) p;
      UT_ob2     :  ∏ {x y: A} (e: x ~> y), @idtoeqvT A x y TT (Ua e) == e;
   }.

