Require Import Setoid.
Require Import Relations Morphisms.
Require Import Coq.Classes.CRelationClasses.
Require Import FunctionalExtensionality.

Local Unset Elimination Schemes.

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

(* Notation "{ x ; .. ; y ; z }" := (tpair _ x .. (tpair _ y z) ..). *)

Notation "'∑'  x .. y , P" := (total2 (fun x => .. (total2 (fun y => P)) ..))
(at level 200, x binder, y binder, right associativity) : type_scope.


Inductive Id {A: Type}: A -> A -> Type :=
  refl: forall a, Id a a.

Arguments refl {A a} , [A] a.

Scheme Id_ind := Induction for Id Sort Type.
Arguments Id_ind [A] P f y y0 i.
Scheme Id_rec := Minimality for Id Sort Type.
Arguments Id_rec [A] P f y y0 i.
Definition Id_rect := Id_ind.


Definition dirprod (A B : Type): Type := ∑ a: A, B.
Definition dppr1 {A B : Type} := pr1: dirprod A B -> A.
Definition dppr2 {A B : Type} := pr2: dirprod A B -> B.

Notation "C × D ":= (@dirprod C D) (at level 40, left associativity).

Reserved Notation "x '~>' y" (at level 70, y at next level).
Reserved Notation "x '==' y" (at level 70).
Reserved Notation "x 'o' y" (at level 69).

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

Notation " R ===> R' " := (@CMorphisms.respectful _ _ (R%signature) (R'%signature))
(right associativity, at level 70) : signature_scope.

Class Typoid (A: Type): Type :=
   mkTypoid
   {
      st         :  Setoid A;
      ett        :  ∏ {x y: A}, crelation (@et A st x y) where "a == b" := (ett a b);
      ett_refl   :  ∏ {x y: A} (e: x ~> y), e == e;
      ett_sym    :  ∏ {x y: A} (e d: x ~> y), e == d -> d == e;
      ett_trans  :  ∏ {x y: A} (e d f: x ~> y), e == d -> d == f -> e == f;
      Typ1_i     :  ∏ {x y: A} (e: x ~> y), (eqv x) o e == e;
      Typ1_ii    :  ∏ {x y: A} (e: x ~> y), e o (eqv y) == e;
      Typ2_i     :  ∏ {x y: A} (e: x ~> y), e o (inv e) == eqv x;
      Typ2_ii    :  ∏ {x y: A} (e: x ~> y), (inv e) o e == eqv y;
      Typ3       :  ∏ {x y z t: A} (e1: x ~> y) (e2: y ~> z) (e3: z ~> t), ((e1 o e2) o e3) == (e1 o (e2 o e3));
      Typ4       :  ∏ {x y z: A} (e1 d1: x ~> y) (e2 d2: y ~> z), e1 == d1 -> e2 == d2 -> (e1 o e2) == (d1 o d2);
      SP         :> ∏ {x y z: A}, CMorphisms.Proper ((@ett x y) ===> (@ett y z) ===> (@ett x z)) (star); 
      EP         :> ∏ {x: A}, CMorphisms.Proper (@ett x x) (eqv x);
      IP         :> ∏ {x y: A}, CMorphisms.Proper (@ett x y ===> @ett y x) (inv)
   }.

Notation "x '==' y" := (ett x y) : type_scope.

(* Instance EqRRel_ett: ∏ {A T} x y, RewriteRelation (@ett A T x y). *)

Instance EqRel_ett: ∏ {A T} x y, Equivalence (@ett A T x y).
   constructor; intro.
        apply ett_refl.
        apply ett_sym.
        apply ett_trans.
Defined.

Arguments et {_} _ _ _ .

Lemma Typ5: forall {A: Type} {x y z: A} {T: Typoid A} (f: x ~> y) (g: y ~> z),
  inv (f o g) == inv g o inv f.
Proof. intros.
        assert (inv (f o g) o (f o g) == eqv z).
        { now rewrite Typ2_ii. }
        assert (inv (f o g) o (f o g) o inv g o inv f == inv g o inv f).
        { now rewrite X, Typ1_i. }
        setoid_rewrite <- Typ3 at 1 in X0.
        setoid_rewrite Typ3 at 2 in X0.
        rewrite Typ2_i in X0.
        setoid_rewrite Typ3 at 1 in X0.
        rewrite Typ1_i in X0.
        setoid_rewrite Typ3 at 1 in X0.
        rewrite Typ2_i, Typ1_ii in X0. easy.
Qed.

Lemma Typ6: forall {A: Type} {x y: A} {T: Typoid A} (f: x ~> y),
  inv (inv f) == f.
Proof. intros.
        assert (inv (inv f) o (inv f) == eqv x).
        { now rewrite Typ2_ii. }
        assert (inv (inv f) o inv f o f == f).
        { now rewrite X, Typ1_i. }
        now rewrite Typ3, Typ2_ii, Typ1_ii in X0.
Qed.


Reserved Notation "x '~~>' y" (at level 70, y at next level).

(** functors *)
Class TypoidFunction {A B: Type} (X: Typoid A) (Y: Typoid B) (fobj: A -> B): Type :=
   mkTypoidFunction 
   {
(*       fobj      :  A -> B; *)
      fmap      :  ∏ {x y: A}, x ~> y -> (fobj x ~> fobj y);
      fmap_pid  :  ∏ (x: A), fmap (eqv x) == eqv (fobj x);
      fmap_pcomp:  ∏ (x y z: A) (e1: x ~> y) (e2: y ~> z), fmap (e1 o e2) == fmap e1 o fmap e2;
      fmap_p    :  ∏ {x y: A} (e d: x ~> y) (i: e == d), fmap e == fmap d;
      TP        :> ∏ {x y}, CMorphisms.Proper (@CMorphisms.respectful _ _ (@ett A X x y) (@ett B Y (fobj x) (fobj y))) (@fmap x y); 
   }.

(* Notation "x '~~>' y"  := (TypoidFunction x y) : type_scope.

Arguments fobj {_ _ _ _} _ _ . *)
Arguments fmap {_ _ _ _ _} _ {_ _}  _ .
Arguments fmap_p {_ _} _ {_ _ _ _}  _ .

Lemma fmap_pinv {A B: Type} {f: A -> B} {C: Typoid A} {D: Typoid B} (F: TypoidFunction C D f):
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

(** natural transformations *)
Class TypoidNT {A B: Type} {TA: Typoid A} {TB: Typoid B} {f g: A -> B} 
                (F: TypoidFunction TA TB f) (G: TypoidFunction TA TB g): Type :=
  mkTypoidNT
  {
     trans   : ∏ (x: A), (f x) ~> (g x);
     trans_cc: ∏ {x y: A} (e: x ~> y), fmap F e o trans y == trans x o fmap G e;
     TRP     :> ∏ {x: A}, CMorphisms.Proper (@ett B TB (f x) (g x)) (trans x)
  }.

Arguments trans {_ _ _ _ _ _ _ _ } _ _ .


(** typoid of typoid functions *)
Definition ExponentialTypoid {A B: Type} (TA: Typoid A) (TB: Typoid B): 
  Typoid (∑ f: A -> B, TypoidFunction TA TB f).
Proof. unshelve econstructor.
       - unshelve econstructor.
         + intros F G.
           destruct F as (f, F).
           destruct G as (g, G).
           exact (TypoidNT F G).
         + intro f. cbn in *.
           destruct f as (f, s). destruct s as (phif, fid, fcomp, fp, fR).
           unshelve econstructor.
           ++ intro x.
              exact (phif x x (eqv x)).
           ++ cbn. intros.
              now rewrite <- !fcomp, Typ1_i, Typ1_ii.
           ++ repeat intro. cbn. unfold CMorphisms.Proper.
              easy.
         + cbn. intros f g h F G.
           destruct f as (f, s). destruct s as (phif, fid, fcomp, fp, fR).
           destruct g as (g, s). destruct s as (phig, gid, gcomp, gp, gR).
           destruct h as (h, s). destruct s as (phih, hid, hcomp, hp, hR).
           destruct F as (t1, nt1, FP).
           destruct G as (t2, nt2, GP).
           unshelve econstructor.
           ++ intro x.
               exact (t1 x o t2 x).
           ++ cbn. intros.
              now rewrite Typ3, <- nt2, <- Typ3, nt1, Typ3.
           ++ repeat intro. cbn. unfold CMorphisms.Proper.
              easy.
         + cbn. intros f g F.
           destruct f as (f, s).
           specialize (fmap_pinv s); intros finv.
           destruct s as (fmapf, fid, fcomp, fp, fR).
           destruct g as (g, s).
           specialize (fmap_pinv s); intros ginv.
           destruct s as (fmapg, gid, gcomp, gp, gR).
           destruct F as (trans, nt, FP).
           unshelve econstructor.
           ++ intro x.
              exact (inv (trans x)).
           ++ cbn. intros.
              pose proof nt as nt'.
              cbn in *.
              specialize (nt _ _  (inv e)).
              rewrite finv, ginv in nt.
              assert (fmapf x y e o inv (fmapf x y e) o trans x ==
                      fmapf x y e o trans y o inv (fmapg x y e)).
              { rewrite !Typ3, nt. easy. }
              rewrite Typ2_i, Typ1_i in X.
              rewrite X.
              rewrite !Typ5.
              do 2 rewrite Typ3.
              now rewrite Typ2_ii, Typ1_ii, Typ6.
           ++ repeat intro. unfold CMorphisms.Proper.
              easy.
       - unfold crelation. intros F G nt1 nt2.
         destruct F as (f, F). cbn in *.
         destruct G as (g, G). cbn in *.
         exact (forall a, trans nt1 a == trans nt2 a).
       - intros F G e.
         destruct F as (f, F).
         destruct G as (g, G). cbn in *.
         easy.
       - intros F G e d.
         destruct F as (f, F).
         destruct G as (g, G). cbn in *.
         intros p a. now rewrite p.
       - intros F G e d r.
         destruct F as (f, F).
         destruct G as (g, G). cbn in *.
         intros p q a. now rewrite p, q.
       - intros F G e.
         destruct F as (f, F).
         destruct G as (g, G).
         intro a.
         destruct F, G, e. cbn.
         now rewrite fmap_pid0, Typ1_i.
       - intros F G e.
         destruct F as (f, F).
         destruct G as (g, G).
         intro a.
         destruct F, G, e. cbn.
         now rewrite fmap_pid1, Typ1_ii.
       - intros F G e.
         destruct F as (f, F).
         destruct G as (g, G).
         intro a.
         destruct F, G, e. cbn.
         now rewrite fmap_pid0, Typ2_i.
       - intros F G e.
         destruct F as (f, F).
         destruct G as (g, G).
         intro a.
         destruct F, G, e. cbn.
         now rewrite fmap_pid1, Typ2_ii.
       - intros F G H I e1 e2 e3.
         destruct F as (f, F).
         destruct G as (g, G).
         destruct H as (h, H).
         destruct I as (i, I).
         intro a.
         destruct F, G, H, I, e1, e2, e3. cbn.
         now rewrite Typ3.
       - intros F G H e1 d1 e2 d2.
         destruct F as (f, F).
         destruct G as (g, G).
         destruct H as (h, H).
         intros p q a.
         destruct F, G, H, I, e1, d1, e2, d2. cbn.
         specialize (p a). cbn in p.
         specialize (q a). cbn in q.
         now rewrite p, q.
       - repeat intro. destruct x, y, z.
         intro a.
         cbn in x0, x1, y0, y1.
         destruct x0, y0, x1, y1.
         destruct pr4, pr6, pr8.
         cbn in *.
         now rewrite (X a), (X0 a).
       - repeat intro. destruct x.
         intro a. destruct pr4. now cbn.
       - repeat intro. destruct y, x.
         intro a.
         destruct x0, y0, pr4, pr6.
         cbn in *.
         now rewrite (X a).
Defined.

Definition ComposeTF 
                      (A B: Type)
                      (f g h: A -> B)
                      (TA: Typoid A) 
                      (TB: Typoid B)
                      (F  : TypoidFunction TA TB f)
                      (G  : TypoidFunction TA TB g)
                      (H  : TypoidFunction TA TB h)
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













