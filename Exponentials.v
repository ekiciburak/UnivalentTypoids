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


(** typoid of typoid functions *)
Definition ExponentialTypoid {A B: Type} (TA: Typoid A) (TB: Typoid B): 
  Typoid (TypoidFunction TA TB).
Proof. unshelve econstructor.
       - unshelve econstructor.
         + intros F G.
           exact (TypoidNT F G).
         + intro f. cbn in *.
           destruct f as (f, phif, fid, fcomp, fp, fR).
           unshelve econstructor.
           ++ intro x.
              exact (phif x x (eqv x)).
           ++ cbn. intros.
              now rewrite <- !fcomp, Typ1_i, Typ1_ii.
           ++ repeat intro. cbn. unfold CMorphisms.Proper.
              easy.
         + cbn. intros f g h F G.
           destruct f as (f, phif, fid, fcomp, fp, fR).
           destruct g as (g, phig, gid, gcomp, gp, gR).
           destruct h as (h, phih, hid, hcomp, hp, hR).
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
           specialize (fmap_pinv f); intros finv.
           destruct f as (f, fmapf, fid, fcomp, fp, fR).
           specialize (fmap_pinv g); intros ginv.
           destruct g as (g, fmapg, gid, gcomp, gp, gR).
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
         exact (forall a, trans nt1 a == trans nt2 a).
       - intros F G e.
         easy.
       - intros F G e d.
         intros p a. cbn in p. now rewrite p.
       - intros F G e d r. 
         intros p q a. cbn in p, q.
         now rewrite p, q.
       - intros F G e.
         intro a.
         destruct F, G, e. cbn.
         now rewrite fmap_pid0, Typ1_i.
       - intros F G e.
         intro a.
         destruct F, G, e. cbn.
         now rewrite fmap_pid1, Typ1_ii.
       - intros F G e.
         intro a.
         destruct F, G, e. cbn.
         now rewrite fmap_pid0, Typ2_i.
       - intros F G e.
         intro a.
         destruct F, G, e. cbn.
         now rewrite fmap_pid1, Typ2_ii.
       - intros F G H I e1 e2 e3.
         intro a.
         destruct F, G, H, I, e1, e2, e3. cbn.
         now rewrite Typ3.
       - intros F G H e1 d1 e2 d2.
         intros p q a.
         destruct F, G, H, I, e1, d1, e2, d2. cbn.
         specialize (p a). cbn in p.
         specialize (q a). cbn in q.
         now rewrite p, q.
       - repeat intro. destruct x, y, z.
         cbn in x0, x1, y0, y1.
         destruct x0, y0, x1, y1.
         cbn in *.
         now rewrite (X a), (X0 a).
       - repeat intro. destruct x.
         now cbn.
       - repeat intro. destruct y, x.
         destruct x0, y0.
         cbn in *.
         now rewrite (X a).
Defined.

Definition ComposeTF 
                      (A B: Type)
                      (f g h: A -> B)
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

Definition flip {A B C : Type} (f : A -> B -> C) := fun x y => f y x.

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

Definition OppositeTypoid {A: Type} (T: Typoid A): Typoid A.
Proof. destruct T, st0.
        unshelve econstructor.
        - exact (OppositeSetoid (mkSetoid A et0 eqv0 star0 inv0)).
        - unfold crelation in *.
          intros x y.
(*        exact (flip (ett0 y x)). *)
          exact (ett0 y x).
        - unfold flip.
          intros x y e.
          exact (ett_refl0 y x e).
        - unfold flip.
          intros x y e d eq.
          exact (ett_sym0 y x e d eq).
        - intros x y d e f eq1 eq2.
          unfold flip in *.
          exact (ett_trans0 y x d e f eq1 eq2).
        - cbn in *. unfold flip.
          intros x y e.
(*        exact (ett_sym0 _ _ _ _ (Typ1_ii0 y x e)). *)
          exact (Typ1_ii0 y x e).
        - intros x y e.
          exact (Typ1_i0 y x e).
        - intros x y e.
          exact (Typ2_ii0 y x e).
        - intros x y e.
          exact (Typ2_i0 y x e).
        - intros x y z t e1 e2 e3.
          exact (ett_sym0 _ _ _ _ (Typ7 t z y x e3 e2 e1)).
        - intros x y z e1 d1 e2 d2 eq1 eq2. 
          exact (Typ8 z y x e2 d2 e1 d1 eq2 eq1).
        - repeat intro.
          exact (SP0 z y x x1 y1 X0 x0 y0 X).
        - repeat intro. exact (EP0 x).
        - repeat intro. exact (IP0 y x x0 y0 X).
Defined.

Class invertible (A B: Type) :=
  mk_invertible
  {
     fun_f    : A -> B;
     inverse_f: B -> A;
     inv_cc1  : forall a: A, Id (inverse_f (fun_f a)) a;
     inv_cc2  : forall b: B, Id (fun_f (inverse_f b)) b
  }.

Definition compose {A B C: Type} (f: A -> B) (g: B -> C): (A -> C).
Proof. intro a. now apply g, f. Defined.

Definition ap {A B: Type} {a b: A} (f: A -> B): Id a b -> Id (f a) (f b).
Proof. intro p. now induction p. Defined.

Definition concat {A: Type} {a b c: A}: Id a b -> Id b c -> Id a c.
Proof. intros p q. now induction p; induction q. Defined.

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

Definition ProductSetoid {A B: Type} (SA: Setoid A) (SB: Setoid B): Setoid (A * B).
Proof. unshelve econstructor.
       - intros a b.
         exact ( ((et SA (fst a) (fst b)) * (et SB (snd a) (snd b)))%type ).
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

Definition ProductTypoid: ∏ {A B: Type} (TA: Typoid A) (TB: Typoid B), Typoid (A * B).
Proof. intros.
        unshelve econstructor.
        - exact (ProductSetoid (@st A TA) (@st B TB)).
        - intros x y (e1, e2) (e1', e2').
          exact (((e1 == e1') * (e2 == e2'))%type).
        - intros x y (e1, e2).
          easy.
        - intros x y (e1, e2) (d1, d2) (p, q).
          split; easy.
        - intros x y (e1, e2) (d1, d2) (f1, f2) (p, q) (r, s).
          split.
          + now rewrite p, r.
          + now rewrite q, s.
        - intros x y (e1, d1).
          split; now rewrite Typ1_i.
        - intros x y (e1, d1).
          split; now rewrite Typ1_ii.
        - intros x y (e1, d1).
          split; now rewrite Typ2_i.
        - intros x y (e1, d1).
          split; now rewrite Typ2_ii.
        - intros x y z t (e1, e2) (d1, d2) (f1, f2).
          split; now rewrite Typ3.
        - intros x y z (e1, e2) (d1, d2) (f1, f2) (h1, h2) (p, q) (r, s).
          split.
          + now rewrite p, r.
          + now rewrite q, s.
        - repeat intro.
          destruct x0 as (e1, e2).
          destruct y0 as (d1, d2).
          destruct x1 as (f1, f2).
          destruct y1 as (h1, h2).
          destruct X as (p, q).
          destruct X0 as (r, s).
          split.
          + now rewrite p, r.
          + now rewrite q, s.
        - repeat intro. easy.
        - repeat intro.
          destruct x0 as (e1, e2).
          destruct y0 as (d1, d2).
          destruct X as (p, q).
          split.
          + now rewrite p.
          + now rewrite q.
Defined.


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


Definition product {A B C D: Type} (f: A -> B) (g: C -> D): A * C -> B * D.
Proof. intros (a, c). exact (f a, g c). Defined.

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
                                  {f: A -> C}
                                  {g: B -> D}
                                  (TA: Typoid A)
                                  (TB: Typoid B)
                                  (TC: Typoid C)
                                  (TD: Typoid D)
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

(** The Curry functor *)
Definition CurryF {A B C: Type} 
                   (TA: Typoid A)
                   (TB: Typoid B)
                   (TC: Typoid C)
                   (F: TypoidFunction (ProductTypoid TC TA) TB): 
  TypoidFunction TC (ExponentialTypoid TA TB).
Proof. unshelve econstructor.
        - intro c. exact (FixBiF1 c F).
Admitted.



