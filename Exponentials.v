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
Definition TypoidUni {A: Type}: Typoid Type.
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
        - intros. cbn in *. destruct e. easy.
        - intros. cbn in *. destruct e. easy.
        - intros. cbn in *. destruct e, pr4, pr5, pr6. easy.
        - intros. cbn in *. destruct e, pr4, pr5, pr6. easy.
        - intros. cbn in *. destruct e1. destruct e2. destruct e3.
          easy.
        - intros. cbn in *. destruct e1. destruct e2. destruct d1.
          destruct d2. unfold compose, homotopy, id in *.
          intro a.
          specialize (X a).
          specialize (ap pr5 X); intro H.
          specialize (X0 (pr7 a)). 
          now induction H.
        - repeat intro. cbn in *.
          destruct x0, y0.
          destruct x1. destruct y1.
          unfold homotopy, compose, id in *.
          intro a.
          specialize (X a).
          specialize (ap pr7 X); intro H.
          specialize (X0 (pr5 a)).
          now induction H.
        - repeat intro. cbn in *. easy.
        - repeat intro. cbn in *.
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

Definition transport {A: Type} (P: A -> Type) {a b: A} (p: Id a b): P a -> P b.
Proof. now induction p. Defined.


Definition idtoeqvT: ∏ {A: Type} {x y: A} {T: Typoid A} (p: Id x y), @et A (@st A T) x y.
Proof. intros A x y T p.
        exact (transport (fun z => x ~> z) p (eqv x)).
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


Definition CurHomT {A: Type} (TA: Typoid A) (a: A): 
  TypoidFunction TA TypoidUni.
Admitted.






