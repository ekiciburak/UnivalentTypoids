From UT Require Import Prelims Setoid.
Require Import Coq.Classes.CRelationClasses.
Require Import FunctionalExtensionality.

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


Lemma Typ9: forall {A: Type} {x y: A} {T: Typoid A} (f: x ~> y),
  inv (eqv x) o f == f.
Proof. intros. specialize (@Typ2_i _ T x y f); intro H.
       now rewrite <- H, Typ5, Typ3, Typ6, Typ2_ii, Typ1_ii.
Defined.

Reserved Notation "x '~~>' y" (at level 70, y at next level).

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

(* 
Definition OppositeTypoid {A: Type} (T: Typoid A): Typoid A.
Proof. destruct T, st0.
        unshelve econstructor.
        - exact (OppositeSetoid (mkSetoid A et eqv star inv)).
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
Defined. *)

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

Example UniT: Typoid Type.
Proof. unshelve econstructor.
       - unshelve econstructor.
         + exact (fun A B: Type => Id A B).
         + intros. cbn. apply refl.
         + simpl. intros. apply @concat with (b := y); easy.
         + simpl. intros. induction X. apply refl.
       - intros A B. simpl.
         intros p q.
         exact (Id p q).
       - simpl. intros X Y p. apply refl.
       - simpl. intros X Y p q H. induction H. apply refl.
       - simpl. intros X Y p q r Ha Hb.
         induction Ha; induction Hb. apply refl.
       - simpl. intros X Y p. induction p. simpl. apply refl.
       - simpl. intros X Y p. induction p. simpl. apply refl.
       - simpl. intros X Y p. induction p. simpl. apply refl.
       - simpl. intros X Y p. induction p. simpl. apply refl.
       - simpl. intros X Y Z T p q r. induction p; induction q; induction r. simpl. apply refl.
       - simpl. intros X Y Z p q r t Ha Hb. induction Ha; induction Hb. apply refl.
       - repeat intro. induction X; induction X0. apply refl.
       - repeat intro. simpl. unfold CMorphisms.Proper. apply refl.
       - repeat intro. simpl. induction X. simpl. apply refl.
Defined.

Example UniS: Typoid Set.
Proof. unshelve econstructor.
       - unshelve econstructor.
         + exact (fun A B: Set => Id A B).
         + intros. cbn. apply refl.
         + simpl. intros. apply @concat with (b := y); easy.
         + simpl. intros. induction X. apply refl.
       - intros A B. simpl.
         intros p q.
         exact (Id p q).
       - simpl. intros X Y p. apply refl.
       - simpl. intros X Y p q H. induction H. apply refl.
       - simpl. intros X Y p q r Ha Hb.
         induction Ha; induction Hb. apply refl.
       - simpl. intros X Y p. induction p. simpl. apply refl.
       - simpl. intros X Y p. induction p. simpl. apply refl.
       - simpl. intros X Y p. induction p. simpl. apply refl.
       - simpl. intros X Y p. induction p. simpl. apply refl.
       - simpl. intros X Y Z T p q r. induction p; induction q; induction r. simpl. apply refl.
       - simpl. intros X Y Z p q r t Ha Hb. induction Ha; induction Hb. apply refl.
       - repeat intro. induction X; induction X0. apply refl.
       - repeat intro. simpl. unfold CMorphisms.Proper. apply refl.
       - repeat intro. simpl. induction X. simpl. apply refl.
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
         destruct e, (h249_ii (ishae_isequiv pr1 pr2)), pr3.
         easy.
       - cbn. intros.
         destruct e, (h249_ii (ishae_isequiv pr1 pr2)), pr3.
         easy.
       - cbn. intros. destruct e.
         cbn. destruct ( h249_ii (ishae_isequiv pr1 pr2)), pr3.
         cbn.
         unfold homotopy, compose, id in *.
         intro x0.
         now specialize (pr4 x0).
       - cbn. intros. destruct e.
         cbn. destruct ( h249_ii (ishae_isequiv pr1 pr2)), pr3.
         cbn.
         unfold homotopy, compose, id in *.
         intro x0.
         now specialize (pr3 x0).
       - cbn. intros.
         destruct e1, e2, e3, (h249_ii (ishae_isequiv pr1 pr2)), pr7,
         (h249_ii (ishae_isequiv pr0 pr3)).
         destruct pr10. cbn.
         destruct (h249_ii (ishae_isequiv pr4 pr5)).
         destruct pr13. now cbn.
       - cbn. intros.
         destruct e1, e2, d1, d2, (h249_ii (ishae_isequiv pr1 pr2)).
         destruct pr9.
         destruct (h249_ii (ishae_isequiv pr0 pr3)).
         destruct pr12.
         destruct (h249_ii (ishae_isequiv pr4 pr5)).
         destruct pr15.
         destruct (h249_ii (ishae_isequiv pr6 pr7)).
         destruct pr18.
         unfold homotopy in *.
         intro x0.
         specialize (X0 (pr1 x0)).
         specialize (X x0).
         apply Id_eql in X.
         rewrite X in X0 at 2.
         unfold compose.
         exact X0.
       - repeat intro. cbn.
         destruct x0, x1, y0, y1, (h249_ii (ishae_isequiv pr1 pr2)).
         destruct pr9.
         destruct (h249_ii (ishae_isequiv pr0 pr3)).
         destruct pr12.
         destruct (h249_ii (ishae_isequiv pr4 pr5)).
         destruct pr15.
         destruct( h249_ii (ishae_isequiv pr6 pr7)).
         destruct pr18.
         unfold homotopy, compose in *.
         intro x0.
         specialize (X0 (pr1 x0)).
         specialize (X x0).
         now induction X, X0.
       - repeat intro. now cbn.
       - repeat intro.
         destruct x0, y0 as (pr3, pr4).
         rename pr4 into pr6.
         rename pr3 into pr5.
         rename pr1 into pr3.
         rename pr2 into pr4.
         destruct (h249_ii (ishae_isequiv pr3 pr4)) as (pr7, pr8).
         destruct pr8 as (pr8, pr9).
         destruct (h249_ii (ishae_isequiv pr5 pr6)) as (pr10, pr11).
         destruct pr11 as (pr11, pr12).
         cbn.
         destruct (h249_ii (ishae_isequiv pr3 pr4)) as (pr13, pr14).
         destruct pr14 as (pr14, pr15).
         destruct (h249_ii (ishae_isequiv pr5 pr6)) as (pr16, pr17).
         destruct pr17 as (pr17, pr18).
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
        - intros. destruct e, pr2, pr2, pr3. easy.
        - intros. destruct e, pr2, pr2, pr3. easy.
        - intros. destruct e1. destruct e2. destruct e3.
          easy.
        - intros.
          destruct e1 as (pr3, pr4). 
          destruct e2 as (pr5, pr6). 
          destruct d1 as (pr7, pr8).
          destruct d2 as (pr9, pr10).
          unfold compose, homotopy, id in *.
          intro a.
          specialize (X a).
          specialize (ap pr5 X); intro H.
          specialize (X0 (pr7 a)).
          now induction H.
        - repeat intro.
          destruct x0 as (pr3, pr4).
          destruct y0 as (pr5, pr6).
          destruct x1 as (pr7, pr8).
          destruct y1 as (pr9, pr10).
          unfold homotopy, compose, id in *.
          intro a.
          specialize (X a).
          specialize (ap pr7 X); intro H.
          specialize (X0 (pr5 a)).
          now induction H.
        - repeat intro. easy.
        - repeat intro.
          destruct x0 as (pr3, pr4).
          destruct y0 as (pr5, pr6).
          destruct pr4 as (pr4, pr7).
          destruct pr7 as (pr7, pr8).
          destruct pr8 as (pr8, pr9).
          destruct pr6 as (pr6, pr10).
          destruct pr10 as (pr10, pr11).
          destruct pr11 as (pr11, pr12).
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
*)
