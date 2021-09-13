From UT Require Import Prelims Setoid Typoid TypoidFunction TypoidNT.
Require Import Coq.Classes.CRelationClasses.
Require Import FunctionalExtensionality.

(** typoid of typoid functions *)
Definition ExponentialTypoid {A B: Type} (TA: Typoid A) (TB: Typoid B): 
  Typoid (TypoidFunction TA TB).
Proof. unshelve econstructor.
       - unshelve econstructor.
         + intros F G.
           exact (TypoidNT F G).
         + intro f. 
           exact (IdNT f).
         + cbn. intros f g h F G.
           exact (ComposeNT A B TA TB f g h F G).
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
         now rewrite Typ1_i.
       - intros F G e.
         intro a.
         destruct F, G, e. cbn.
         now rewrite Typ1_ii.
       - intros F G e.
         intro a.
         destruct F, G, e. cbn.
         now rewrite Typ2_i.
       - intros F G e.
         intro a.
         destruct F, G, e. cbn.
         now rewrite Typ2_ii.
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


(** The Evaluation functor *)
Definition EvalF {A B: Type}
                 (TA: Typoid A)
                 (TB: Typoid B): TypoidFunction (ProductTypoid (ExponentialTypoid TA TB) TA) TB.
Proof. unshelve econstructor.
       - intros (F, a). exact (fobj F a).
       - intros (F, a) (G, b) (nt1, f).
         cbn in *.
         exact ((fmap F f) o (trans nt1 b)).
       - intros (F, a). destruct F. cbn.
         now rewrite fmap_pid, Typ1_i.
       - intros (F, a) (G, b) (H, c) e1 e2. cbn in e1, e2.
         destruct e1 as (nt1, f).
         destruct e2 as (nt2, g). cbn. destruct F, G, H. cbn.
         destruct nt1, nt2. cbn in *.
         rewrite fmap_pcomp. rewrite Typ3. setoid_rewrite <- Typ3 at 2.
         rewrite trans_cc. now do 2 rewrite Typ3. 
       - intros (F, a) (G, b) e d i.
         cbn in e, d.
         destruct e as (nt1, f).
         destruct d as (nt2, g).
         destruct i as (i, j).
         rewrite j. destruct nt1, nt2. cbn in *.
         now rewrite (i b).
       - repeat intro. 
         destruct x as (F, a).
         destruct y as (G, b).
         destruct x0, y0.
         destruct X. cbn in *. now rewrite (e3 b), e4.
Defined.

(** The Curry functor *)
Definition CurryF {A B C: Type} 
                   {TA: Typoid A}
                   {TB: Typoid B}
                   {TC: Typoid C}
                   (F: TypoidFunction (ProductTypoid TC TA) TB): 
  TypoidFunction TC (ExponentialTypoid TA TB).
Proof. unshelve econstructor.
        - intro c. exact (FixBiF1 c F).
        - intros a b h. 
          exact (FixBiNT1 F a b h).
        - simpl. intros. rewrite fmap_pid. easy.
        - cbn. intros.
          rewrite <- fmap_pcomp.
          destruct F. cbn in *.
          rewrite fmap_p. easy.
          split.
          + easy.
          + now rewrite Typ1_i.
        - intros x y e d p.
          cbn. destruct F. cbn in *.
          intro a. rewrite fmap_p. easy.
          split; easy.
        - repeat intro.
          destruct F. cbn in *.
          rewrite fmap_p. easy.
          split.
          + now rewrite X.
          + easy.
Defined.
