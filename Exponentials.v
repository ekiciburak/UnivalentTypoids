Require Import Setoid CMorphisms.
(* Require Import Relations Morphisms. *)
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

Notation "{ x ; .. ; y ; z }" := (tpair _ x .. (tpair _ y z) ..). 

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

Definition flip {A B C : Type} (f : A -> B -> C) := fun x y => f y x.



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
      IP         :> ∏ {x y: A}, CMorphisms.Proper (@ett x y ===> @ett y x) (inv);
(*       IdP        :> ∏ {x y: A}, CMorphisms.Proper (@ett x y ===> @ett x y) (Id)  *)
   }.

(* Instance all_iff_morphism (A : Type) (x y: A) (T: Typoid A) :
         CMorphisms.Proper (@ett A T x y ===> @ett A T x y ===> @ett A T x y) (Id).

Add Parametric Morphism A (x y: A) (T: Typoid A): (Id) 
  with signature (@ett A T x y) ===> (@ett A T x y) as www. *)

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

Definition ComposeNT
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

Definition OppositeT {A: Type} (T: Typoid A): Typoid A.
Proof. unshelve econstructor.
        - exact (OppositeS (@st A T)).
        - intros x y.
          exact (@ett A T y x).
        - intros.
          exact (ett_refl e).
        - intros x y e d p.
          exact (ett_sym e d p).
        - intros x y e d f p q.
          exact (ett_trans e d f p q).
        - intros x y e.
          exact (Typ1_ii e).
        - intros x y e.
          exact (Typ1_i e).
        - intros x y e.
          exact (Typ2_ii e).
        - intros x y e.
          exact (Typ2_i e).
        - intros x y z t e1 e2 e3.
          exact (ett_sym _ _ (Typ3 e3 e2 e1)).
        - intros x y z e1 d1 e2 d2 p q.
          exact (Typ4 _ _ _ _ q p).
        - repeat intro.
          exact (SP x1 y1 X0 x0 y0 X).
        - repeat intro. exact (EP).
        - repeat intro. exact (IP x0 y0 X).
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

Definition compose {A B C: Type} (f: A -> B) (g: B -> C): (A -> C).
Proof. intro a. now apply g, f. Defined.

Definition ap {A B: Type} {a b: A} (f: A -> B): Id a b -> Id (f a) (f b).
Proof. intro p. now induction p. Defined.

Definition concat {A: Type} {a b c: A}: Id a b -> Id b c -> Id a c.
Proof. intros p q. now induction p; induction q. Defined.

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

Example Uni: Typoid Type.
Proof. unshelve econstructor.
       - unshelve econstructor.
         + exact (fun A B: Type => ∑ f: A -> B, ishae f).
         + intros. cbn.
           exists id. apply isequiv_ishae.
           unshelve econstructor.
           * exists id. easy.
           * exists id. easy.
         + cbn. intros.
           destruct X as (f, cc1).
           destruct X0 as (g, cc2).
           apply ishae_isequiv, h249_ii in cc1.
           apply ishae_isequiv, h249_ii in cc2.
           destruct cc1 as (invf, (cc1a, cc1b)).
           destruct cc2 as (invg, (cc2a, cc2b)).
           unfold compose, homotopy, id in *. cbn.
           exists (compose f g).
           apply isequiv_ishae, h249_i.
           unshelve econstructor.
           exact (compose invg invf).
           split.
           ++ unfold compose, homotopy, id in *. cbn.
              intro c.
              specialize (cc1a (invg c)).
              apply Id_eql in cc1a. rewrite cc1a.
              easy.
           ++ unfold compose, homotopy, id in *. cbn.
              intro a.
              specialize (cc2b (f a)).
              apply Id_eql in cc2b. rewrite cc2b.
              easy.
         + cbn. intros.
           destruct X as (f, cc1).
           apply ishae_isequiv, h249_ii in cc1.
           destruct cc1 as (invf, (cc1, cc2)).
           exists invf.
           apply isequiv_ishae, h249_i.
           unshelve econstructor.
           ++ exact f.
           ++ split; easy.
       - cbn. intros A B (f, u) (f', v).
(*  (f, u) (f', u'). *)
         exact (homotopy f f'). 
(*          exact (fun (e1 e2: ∑ f: A -> B, ishae f) => ∏x: A, Id ((pr1 e1) x) ((pr1 e2) x)). *)
       - cbn. intros. now destruct e.
       - cbn. intros. destruct d, e.
         intro a. 
         specialize (X a).
         now apply inverse in X.
       - cbn. intros.
         destruct e, f, d.
         intro a.
         exact (concat (X a) (X0 a)).
      - cbn. intros.
         destruct e, (h249_ii (ishae_isequiv pr3 pr4)), pr6.
         easy.
       - cbn. intros.
         destruct e, (h249_ii (ishae_isequiv pr3 pr4)), pr6.
         easy.
       - cbn. intros. destruct e.
         cbn. destruct ( h249_ii (ishae_isequiv pr3 pr4)), pr6.
         cbn.
         unfold homotopy, compose, id in *.
         intro x0.
         now specialize (pr7 x0).
       - cbn. intros. destruct e.
         cbn. destruct ( h249_ii (ishae_isequiv pr3 pr4)), pr6.
         cbn.
         unfold homotopy, compose, id in *.
         intro x0.
         now specialize (pr6 x0).
       - cbn. intros.
         destruct e1, e2, e3, (h249_ii (ishae_isequiv pr3 pr4)),
         (h249_ii (ishae_isequiv pr5 pr6)), pr8, pr10, pr12. cbn.
         destruct (h249_ii (ishae_isequiv pr7 {pr8; pr13})).
         destruct pr17. now cbn.
       - cbn. intros.
         destruct e1, e2, d1, d2, (h249_ii (ishae_isequiv pr3 pr4)), (h249_ii (ishae_isequiv pr7 pr8)),
         pr12, (h249_ii (ishae_isequiv pr5 pr6)), pr14, pr17, (h249_ii (ishae_isequiv pr9 pr10)), pr21.
         intro x0.
         specialize (X0 (pr3 x0)).
         specialize (X x0).
         apply Id_eql in X.
         unfold compose, homotopy in *.
         now rewrite X in X0 at 2.
       - repeat intro. cbn.
         destruct x0, x1, y0, y1, (h249_ii (ishae_isequiv pr3 pr4)), 
         (h249_ii (ishae_isequiv pr7 pr8)), pr12, (h249_ii (ishae_isequiv pr5 pr6)), pr17,
         pr14, (h249_ii (ishae_isequiv pr9 pr10)), pr21.
         cbn in *.
         unfold compose.
         intro x0.
         specialize (X0 (pr3 x0)).
         specialize (X x0).
         now induction X, X0.
       - repeat intro. now cbn.
       - repeat intro.
         destruct x0, y0, (h249_ii (ishae_isequiv pr3 pr4)), pr8, (h249_ii (ishae_isequiv pr5 pr6)), pr11
         . cbn. destruct (h249_ii (ishae_isequiv pr3 pr4)),  pr14, (h249_ii (ishae_isequiv pr5 pr6)).
           cbn. destruct pr17.
         unfold homotopy, compose, id in *.
         intro b.
         pose proof X as HH.
         specialize (pr15 (pr10 (pr5 (pr16 b)))).
         specialize (pr12 (pr16 b)).
         apply Id_eql in pr12.
         rewrite pr12 in pr15.
         specialize (X (pr16 b)).
         apply Id_eql in X.
         rewrite X in pr15.
         specialize (pr17 b).
         apply Id_eql in pr17.
         now rewrite pr17 in pr15.
Defined.


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
          rewrite fmap_p0. easy.
          split; now rewrite Typ1_i, Typ1_ii.
        - repeat intros.
          now unfold CMorphisms.Proper.
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
        - intros a b h. 
          exact (FixBiNT1 F a b h).
        - easy.
        - cbn. intros.
          rewrite <- fmap_pcomp.
          destruct F. cbn in *.
          rewrite fmap_p0. easy.
          split.
          + easy.
          + now rewrite Typ1_i.
        - intros x y e d p.
          cbn. destruct F. cbn in *.
          intro a. rewrite fmap_p0. easy.
          split; easy.
        - repeat intro.
          destruct F. cbn in *.
          rewrite fmap_p0. easy.
          split.
          + now rewrite X.
          + easy.
Defined.

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


(** Universe of Typoids [correspondingly Category of Sets] *)
Definition TypoidUni: Typoid Type.
Proof. unshelve econstructor.
        - unshelve econstructor.
          + exact (et (@st _ Uni)).
          + cbn. intros. exists id.
            apply qinv_ishae.
            unshelve econstructor.
            ++ exact id.
            ++ easy.
          + cbn. intros.
            destruct X as (f, Hf).
            destruct X0 as (g, Hg).
            exists (compose f g).
            unfold compose. apply qinv_ishae.
            unshelve econstructor.
            destruct Hf as (finv, Hf).
            destruct Hg as (ginv, Hg).
            exact (compose ginv finv).
            destruct Hf as (finv, (f_eta, (f_eps, Hf))).
            destruct Hg as (ginv, (g_eta, (g_eps, Hg))).
            split. 
            ++ unfold compose, homotopy, id in *.
               intro a. clear Hf.
               specialize (f_eps (ginv a)).
               specialize (ap g f_eps); intro H.
               clear Hg.
               specialize (g_eps a).
               now induction g_eps.
            ++ unfold compose, homotopy, id in *.
               intro a. clear Hg.
               specialize (g_eta (f a)).
               specialize (ap finv g_eta); intro H.
               clear Hf.
               specialize (f_eta a).
               now induction f_eta.
          + cbn. intros. destruct X as (f, Hf).
            destruct Hf as (finv, (eta, (eps, Hfinv))). exists finv.
            apply qinv_ishae.
            unshelve econstructor.
            exact f.
            split; [exact eta | exact eps].
        - unfold crelation. cbn. intros X Y (f, x) (f', x').
          exact (homotopy f f').
        - cbn. intros. destruct e. easy.
        - cbn. intros. destruct e, d. easy.
        - cbn. intros. destruct e, d, f. 
          unfold homotopy in *.
          intro a. 
          specialize (X a).
          specialize (X0 a).
          now induction X.
        - intros. destruct e. easy.
        - intros. destruct e. easy.
        - intros. destruct e, pr4, pr5, pr6. easy.
        - intros. destruct e, pr4, pr5, pr6. easy.
        - intros. destruct e1. destruct e2. destruct e3.
          easy.
        - intros. destruct e1. destruct e2. destruct d1.
          destruct d2. unfold compose, homotopy, id in *.
          intro a.
          specialize (X a).
          specialize (ap pr5 X); intro H.
          specialize (X0 (pr7 a)). 
          now induction H.
        - repeat intro.
          destruct x0, y0.
          destruct x1. destruct y1.
          unfold homotopy, compose, id in *.
          intro a.
          specialize (X a).
          specialize (ap pr7 X); intro H.
          specialize (X0 (pr5 a)).
          now induction H.
        - repeat intro. easy.
        - repeat intro.
          destruct x0, y0. destruct pr4, pr7, pr8, pr6, pr10.
          destruct pr11.
          unfold homotopy, compose, id in *.
          intro a.
          pose proof X as HX.
          pose proof HX as HXX.
          specialize (X (pr4 a)).
          specialize (HX (pr6 a)).
          clear pr12.
          specialize (pr11 a). induction pr11.
          clear pr9.
          specialize (pr8 a). induction pr8.
          specialize (pr7 (pr6 a)).
          now induction HX.
Defined.


(* Parameters (A: Type) (x y: A) (T: Typoid A) (p: Id x y) (f: @et _ (@st _ T) x y).
Check @et A (@st A T) x y.

Check @ett A T x y f f.

Definition idtoeqvT2: ∏ {A: Type} {x y: A} {T: Typoid A} (p: Id x y), @ett A T x y.
Proof. intros A x y T p.
        exact (transport (fun z => x ~> z) p (eqv x)).
Defined.
 *)


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

Definition idtoeqvT: ∏ {A: Type} {x y: A} {T: Typoid A} (p: Id x y), @et A (@st A T) x y.
Proof. intros A x y T p.
        exact (transport (fun z => x ~> z) p (eqv x)).
Defined.

Definition UA_def: Type := ∏ (A B: Type), isequiv (@idtoeqv A B).
Axiom UA: UA_def.

Definition UA_defT: Type := ∏ (A: Type) (x y: A) (T: Typoid A), isequiv (@idtoeqvT A x y T).
Axiom UAT: UA_defT.

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


Class UnivalentTypoid (A: Type): Type :=
   mkUnivalentTypoid
   {
      TT         :  Typoid A;
      Ua         :  ∏ {x y: A} (e: x ~> y), Id x y;
      Ua2        :  ∏ {x y: A} {e d: x ~> y} (i: e == d), Id (Ua e) (Ua d);
      UT_ob1     :  ∏ {x y: A} (p: Id x y), Id (Ua (@idtoeqvT A x y TT p)) p;
      UT_ob2     :  ∏ {x y: A} (e: x ~> y), @idtoeqvT A x y TT (Ua e) == e;
   }.



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
Defined.

 
(* Fixpoint Yoneda {A: Type} {a: A} (TA: Typoid A): TypoidFunction TA Uni.
Proof. unshelve econstructor.
       - intro x. exact (et (@st _ TA) x a).
       - cbn. intros x y e.
         exists (fun p: x ~> a => (inv e) o p).
         apply qinv_ishae. 
         unshelve econstructor.
         + intro f. exact (e o f).
         + split.
           ++ red. intro f. unfold compose, id.
              specialize (Yoneda A a TA).
              destruct Yoneda.
              apply UA.
              rewrite <- Typ3.
              rewrite Typ2_i. *)

(* 
Definition CurHomT {A: Type} {TA: Typoid A}: 
  TypoidFunction (ProductTypoid (OppositeT TA) TA) (@TT _ UniTypoidUni).
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
              eapply UAT.
 
Admitted.


 *)




