Require Import Setoid.
Require Import Coq.Classes.CRelationClasses Coq.Classes.RelationClasses.
Require Import Relations Morphisms.
Require Import  Coq.Program.Equality.

Definition UU := Type.

Identity Coercion fromUUtoType : UU >-> Sortclass.

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Record total2 { T: UU } ( P: T -> UU ): UU := 
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


Inductive Id {A: UU}: A -> A -> UU: UU :=
  refl: forall a, Id a a.

Arguments refl {A a} , [A] a.
Check Id_ind.
Arguments Id_ind [A] P f y y0 i.
Arguments Id_rec [A] P f y y0 i.

Definition compose {A B C: UU} (f: A -> B) (g: B -> C): A -> C.
Proof. intro a. now apply g, f. Defined.

Definition funcomp {X Y: UU} {Z: Y -> UU} (f: X -> Y) (g: ∏ y:Y, Z y) := λ x, g (f x).
Check funcomp.

Lemma comp_eq: ∏ {X Y Z: UU} (f: X -> Y) (g: Y -> Z), Id (compose f g) (funcomp f g).
Proof. intros. now compute. Defined.

Definition inverse {A: UU} {a b: A}: Id a b -> Id b a.
Proof. intro p. now induction p. Defined.

Definition concat {A: UU} {a b c: A}: Id a b -> Id b c -> Id a c.
Proof. intros p q. now induction p; induction q. Defined.

Definition symm {A: UU} {a b: A}: Id a b -> Id b a.
Proof. intro p. now induction p. Defined.

Definition id {A: UU} (a: A) := a.

Definition Id_eql: ∏ {A: UU} (a b: A), Id a b -> a = b.
Proof. intros A a b p. now induction p. Defined.

Definition Id_eqr: ∏ {A: UU} (a b: A), a = b -> Id a b.
Proof. intros A a b p. now rewrite p. Defined.

Lemma concat_assoc: ∏ {A: UU} (a b c d: A) (p: Id a b) (q: Id b c)
  (r: Id c d), Id (concat p (concat q r)) (concat (concat p q) r).
Proof. intros. now induction p, q, r. Defined.

Lemma l_concat_refl: ∏ {A: UU} (a b: A) (p: Id a b),
  Id (concat (refl a) p) p.
Proof. intros. now induction p. Defined.

Lemma r_concat_refl: ∏ {A: UU} (a b: A) (p: Id a b),
  Id (concat p (refl b)) p.
Proof. intros. now induction p. Defined.

Definition ap {A B: UU} {a b: A} (f: A -> B): Id a b -> Id (f a) (f b).
Proof. intro p. now induction p. Defined.

Lemma ap_refl: ∏ {A B: UU} {a: A} (f: A -> B), Id (ap f (refl a)) (refl (f a)).
Proof. intros. now cbn. Defined.

Lemma app_concat: ∏ {A B: UU} {a b c: A} (f: A -> B) (p: Id a b) (q: Id b c),
Id (ap f (concat p q)) (concat (ap f p) (ap f q)).
Proof. intros. now induction p, q. Defined.

Lemma concat_inverse_l: ∏ {A: UU} (a b: A) (p: Id a b), Id (concat (inverse p) p) refl.
Proof. intros. now induction p. Defined.

Lemma concat_inverse_r: ∏ {A: UU} (a b: A) (p: Id a b), Id (concat p (inverse p)) refl.
Proof. intros. now induction p. Defined.

Lemma app_id: ∏ {A: UU} {a b: A} (p: Id a b), Id (ap id p) p.
Proof. intros. now induction p. Defined.

Lemma l_concat_remove: ∏ {A: UU} {a b c: A} (p: Id a b) (q r: Id b c),
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

Lemma r_concat_remove: ∏ {A: UU} {a b c: A} (p q: Id a b) (r: Id b c),
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

Definition transport {A: UU} (P: A -> UU) {a b: A} (p: Id a b): P a -> P b.
Proof. now induction p. Defined.

Definition apd {A: UU} {P: A -> UU} (f: ∏ a: A, P a) {a b: A} (p: Id a b): 
  Id (transport P p (f a)) (f b).
Proof. now induction p. Defined.

(** h235 *)
Definition transportconst {A: UU} (B: UU) {a b: A} (p: Id a b) (c: B):
  Id (@transport A (λ a, B) a b p c) c.
Proof. now induction p. Defined.  

Definition constr1 {X : UU} (P : X -> UU) {x x' : X} (e : Id x x') :
  ∑ (f : P x -> P x'),
  ∑ (ee : ∏ p : P x, (Id (tpair _ x p) (tpair _ x' (f p)))), ∏ (pp : P x), Id (ap pr1 (ee pp)) e.
Proof. induction e. 
       unshelve econstructor.
       - exact id.
       - unshelve econstructor; easy.
Defined.

Definition transportf {X : UU} (P : X -> UU) {x x' : X} (e: Id x x'): 
  P x -> P x' := pr1 (constr1 P e).

Definition transportD {A: UU} (B: A -> UU) (C: ∏ a : A, B a -> UU)
           {x1 x2: A} (p: Id x1 x2) (y: B x1) (z: C x1 y): C x2 (transportf _ p y).
Proof. now induction p. Defined.

Lemma transport_eq: ∏ {X : UU} (P : X -> UU) {x x' : X} (e: Id x x'),
  Id (transport P e) (transportf P e).
Proof. intros. now induction e. Defined.

Lemma h1167: ∏ {A: UU} (P: A -> UU) {x y: A} (u: P x) (p: Id x y), 
  Id (tpair _ x u) (tpair _ y (transport P p u)).
Proof. intros. now induction p. Defined.

Definition apdconst {A B: UU} (f: A -> B) {a b: A} (p: Id a b):
  Id (apd f p) (concat (transportconst B p (f a)) (ap f p)).
Proof. now induction p. Defined.

Lemma transport_refl: ∏ {A: UU} {P: A -> UU} {a b: A} (p: Id a b) (u: P a),
  Id (transport P refl u) u.
Proof. intros. now induction p. Defined.

Lemma h239: ∏ {A: UU} {P: A -> UU} {a b c: A} (p: Id a b) (q: Id b c) (u: P a),
  Id (transport P q (transport P p u)) (transport P (concat p q) u).
Proof. intros. now induction p; induction q. Defined.

Lemma h2310: ∏ {A B: UU} (f: A -> B) {P: B -> UU} {a b: A} (p: Id a b) (u: P (f a)),
  Id (@transport _ (compose f P) _ _ p u) (transport P (ap f p) u).
Proof. intros. now induction p. Defined.

Lemma h2311: ∏ {A: UU} {P Q: A -> UU} (f: ∏ a: A, P a -> Q a) {a b: A} (p: Id a b) (u: P a),
  Id (@transport _ Q _ _ p (f a u)) (f b (@transport _ P _ _ p u)).
Proof. intros. now induction p. Defined.

Lemma totalspace_paths: ∏ {A: UU} {P: A -> UU} (w w': (∑ a: A, P a)),
  Id w w' -> ∑ p: Id (pr1 w) (pr1 w'), Id (transport P p (pr2 w)) (pr2 w').
Proof. intros A P w w' q. induction q. destruct a. cbn.
       exists (refl pr3). easy.
Defined.

Lemma totalspace_paths_inv: ∏ {A: UU} {P: A -> UU} (w w': (∑ a: A, P a)),
  (∑ p: Id (pr1 w) (pr1 w'), Id (transport P p (pr2 w)) (pr2 w')) ->  Id w w'.
Proof. intros A P w w'.
       induction w as (w1, w2); induction w' as (w1', w2'). cbn in *.
       intro q. induction q as (p, q). induction p. cbn in *.
       induction q. easy.
Defined.

Definition concat2_hor {A: UU} {a b c: A} {p p': Id a b} {q q': Id b c} (r: Id p p') (s: Id q q'):
  Id (concat p q) (concat p' q').
Proof. now induction r, s. Defined.

Definition dirprod (A B : UU): UU := ∑ a: A, B.
Definition dppr1 {A B : UU} := pr1: dirprod A B -> A.
Definition dppr2 {A B : UU} := pr2: dirprod A B -> B.
Definition dirprodpair {A B : UU} (a: A) (b: B) : dirprod A B := tpair _ a b.

Definition paireq {A B: UU} {x y: dirprod A B} 
  (pq: dirprod (Id (pr1 x) (pr1 y)) (Id (pr2 x) (pr2 y))): Id x y.
Proof. destruct pq as (p, q).
       destruct x as (a, b);
       destruct y as (c, d). cbn in *.
       now induction p, q.
Defined.

Definition dirprodf {X Y X' Y' : UU}  (f : X -> Y) (f' : X' -> Y') 
  (xx' : dirprod X X'): dirprod Y Y' := dirprodpair (f (pr1 xx')) (f' (pr2 xx')).

Definition pathsdirprod {A B: UU} {a1 a2: A} {b1 b2: B} (id1: Id a1 a2) (id2: Id b1 b2):
  Id (dirprodpair a1 b1) (dirprodpair a2 b2).
Proof. now induction id1, id2. Defined.

Definition homotopy {A: UU} {P: A -> UU} (f g: (∏ a: A, P a)): UU :=
  ∏ a: A, Id (f a) (g a).

Lemma h243: ∏ {A B: UU} {a b: A} (f g: A -> B) (p: Id a b) (H: homotopy f g),
  Id (concat (H a) (ap g p)) (concat (ap f p) (H b)).
Proof. intros until p. induction p. intro H.
       specialize (@ap_refl A B a f); intros H0.
       apply Id_eql in H0. rewrite H0.
       specialize (@ap_refl A B a g); intros H1.
       apply Id_eql in H1. rewrite H1.
       now destruct H.
Defined.

Corollary h244: ∏ {A: UU} {a: A} (f: A -> A) (H: homotopy f (@id A)),
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

Lemma transport_ap_refl_H: ∏ {A: UU} {P: A -> UU} {a b: A} 
  (f g: forall a: A, P a) (p: Id a b) (H: homotopy f g),
  Id ((ap (transport P refl) (H a))) (H a).
Proof. intros. induction p. now apply app_id. Defined.

Lemma apd_f_refl: ∏ {A: UU} {P: A -> UU} {a b: A} (f: ∏ a: A, P a) (p: Id a b),
  Id (apd f refl) (refl (f a)).
Proof. intros. now cbn. Qed.

Lemma apd_naturality: ∏ {A B: UU} {P: A -> UU} {a b: A} 
  (f g: forall a: A, P a) (p: Id a b) (H: homotopy f g),
  Id (concat (apd f p) (H b)) (concat (ap (transport P p) (H a)) (apd g p)).
Proof. intros. induction p.
       specialize (@transport_ap_refl_H A P a a f g refl H); intros H0.
       apply Id_eql in H0. rewrite H0.
       specialize (@apd_f_refl A P a a f refl); intro H1.
       apply Id_eql in H1. rewrite H1.
       specialize (@apd_f_refl A P a a g refl); intro H2.
       apply Id_eql in H2. rewrite H2.
       specialize (@l_concat_refl (P a) (f a) (g a) (H a)); intro H3.
       apply Id_eql in H3. 
       now destruct H.
Defined.

Definition qinv {A B: UU} (f: A -> B): UU :=
  ∑ (g: B -> A), (dirprod (homotopy (compose g f) (@id B))
                          (homotopy (compose f g) (@id A))).

Definition isequiv {A B: UU} (f: A -> B): UU :=
  dirprod (∑ (g: B -> A),(homotopy (compose g f) (@id B))) 
          (∑ (h: B -> A),(homotopy (compose f h) (@id A))).

(** ~= *)
Definition Equiv (A B: UU): UU := (∑ f: A -> B, isequiv f).

Example h249_i: ∏ {A B: UU} {f: A -> B}, qinv f -> isequiv f.
Proof. intros A B f eq.
       destruct eq as (g, (pd1, pd2)).
       unshelve econstructor.
       - exists g. exact pd1.
       - exists g. exact pd2.
Defined.

Example h249_ii: ∏  {A B: UU} {f: A -> B}, isequiv f -> qinv f.
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

Lemma h2412_i: ∏ {A: UU}, Equiv A A.
Proof. intro A.
       unshelve econstructor.
       - exact id.
       - unshelve econstructor.
         + exists id. now compute.
         + exists id. now compute.
Defined.

Lemma h2412_ii: ∏ {A B: UU} (f: Equiv A B), Equiv B A.
Proof. intros.
       destruct f as (f, equivf).
       apply h249_ii in equivf.
       destruct equivf as (invf, (alpha, beta)).
       unshelve econstructor.
       - exact invf.
       - unshelve econstructor.
         + exists f. exact beta.
         + exists f. exact alpha.
Defined.

Lemma h2412_iii: ∏ {A B C: UU} (f: Equiv A B) (g: Equiv B C), Equiv A C.
Proof. intros.
       destruct f as (f, iseqf).
       destruct g as (g, iseqg).
       unshelve econstructor.
       - exact (compose f g).
       - apply h249_ii in iseqf.
         apply h249_ii in iseqg.
         destruct iseqf as (finv, (alpha_f, beta_f)).
         destruct iseqg as (ginv, (alpha_g, beta_g)).
         unshelve econstructor.
         + exists (compose ginv finv).
           compute in *.
           intro c.
           assert (g (f (finv (ginv c))) = c).
           { specialize (alpha_f (ginv c)).
             apply Id_eql in alpha_f.
             rewrite alpha_f. 
             specialize (alpha_g c).
             now apply Id_eql in alpha_g.
           }
           now rewrite H.
         + exists (compose ginv finv).
           compute in *.
           intro a.
           assert ((finv (ginv (g (f a)))) = a).
           { specialize (beta_g (f a)).
             apply Id_eql in beta_g.
             rewrite beta_g. 
             specialize (beta_f a).
             now apply Id_eql in beta_f.
           }
           now rewrite H.
Defined.

Definition happly {A: UU} {B: A -> UU} (f g: ∏x: A, B x): (Id f g) -> homotopy f g.
Proof. intros p a. now induction p. Defined.

Definition funext_def_qinv: UU := ∏  (A: UU) (B: A -> UU) (f g: ∏x:A, B x),
  qinv (@happly A B f g).
Axiom FE: funext_def_qinv.

Definition funext_def_isequiv : ∏  (A: UU) (B: A -> UU) (f g: ∏x:A, B x),
  isequiv (@happly A B f g).
Proof. intros. apply h249_i.
       exact (FE A B f g).
Defined.

Definition funext {A: UU} {B: A -> UU} {f g: ∏ x: A, B x}: (∏ x: A, Id (f x) (g x)) -> Id f g.
Proof. destruct (FE A B f g) as (inv_happly, cc2).
       exact inv_happly.
Defined.

Definition happly_funext {A: UU} {B: A -> UU} {f g: ∏ x:A, B x} 
                         (h: ∏ x:A, Id (f x) (g x)): Id (happly _ _ (funext h)) h.
Proof. unfold funext.
       destruct (FE A B f g) as (inv_happly, cc).
       destruct cc as (cc1, cc2).
       unfold homotopy, compose, id in cc2.
       exact (cc1 h).
Defined.

Definition funext_happly {A: UU} {B: A -> UU} {f g: ∏ x: A, B x} 
                         (p: Id f g): Id (funext (happly _ _ p)) p.
Proof. unfold funext.
       destruct (FE A B f g) as (inv_happly, cc).
       destruct cc as (cc1, cc2).
       unfold homotopy, compose, id in cc2.
       exact (cc2 p).
Defined.

Remark transport_isequiv {X : UU} (P : X -> UU) {x y : X} (p: Id x y): isequiv (transport P p).
Proof. apply h249_i.
       exists (transport P (inverse p)).
       now induction p.
Defined.

Definition idtoeqv: ∏ {A B: UU}, Id A B -> Equiv A B.
Proof. intros A B p.
       exists (transport (@id UU) p).
       apply h249_i.
       unshelve econstructor.
       + exact (transport _ (inverse p)).
       + now induction p.
Defined.

Definition UA_def: UU := ∏ (A B: UU), isequiv (@idtoeqv A B).
Axiom UA: UA_def.

Definition ua {A B : UU}: (Equiv A B) -> (Id A B).
Proof. destruct (h249_ii (UA A B)) as (eqvtoid, cc).
        exact eqvtoid.
Defined.

Definition ua_f {A B : UU} (f: A-> B): (isequiv f) -> (Id A B).
Proof. intro e.
       destruct (h249_ii (UA A B)) as (eqvtoid, cc).
       apply eqvtoid.
       exists f. exact e.
Defined.

Definition idtoeqv_ua {A B : UU} (e : Equiv A B): Id (idtoeqv (ua e)) e.
Proof. unfold ua.
       destruct (h249_ii (UA A B)) as (ua, cc).
       destruct cc as (cc1, cc2). cbn.
       unfold homotopy, id, compose in cc1.
       exact (cc1 e).
Defined.

Definition ua_idtoeqv {A B : UU} {p : Id A B}: Id (ua (idtoeqv p)) p.
Proof. unfold ua.
       destruct (h249_ii (UA A B)) as (ua, cc).
       destruct cc as (cc1, cc2). cbn.
       unfold homotopy, id, compose in cc2.
       exact (cc2 p).
Defined.

Definition isSet  (A: UU): UU :=  ∏ (x y: A), ∏ (p q: Id x y), Id p q.
Definition isProp (A: UU): UU :=  ∏ (x y: A), Id x y.

Definition ishae {A B: UU} (f: A -> B) :=
  ∑ g: B -> A, 
    ∑ eta: (homotopy (compose f g) (@id A)),
    ∑ eps: (homotopy (compose g f) (@id B)),
      ∏ x: A, Id (ap f (eta x)) (eps (f x)).

Lemma ishae_qinv: ∏ {A B: UU} (f: A -> B), ishae f -> qinv f.
Proof. intros A B f e.
       destruct e as (finv, (eta, (eps, cc))).
       unshelve econstructor.
       - exact finv.
       - split; easy.
Defined.

Lemma h243_2: ∏ {A B: UU} (x y: A) (p: Id x y) (f g: A -> B) (H: ∏a: A, Id (f a) (g a)),
  Id  (concat (ap f p) (H y)) (concat (H x) (ap g p)).
Proof. intros. apply inverse. apply h243. Defined.

Lemma help: ∏ {A B: UU} (a: A) (f: A -> B) (g: B -> A) (p: Id (g (f a)) a),
Id (ap f (ap (λ a0 : A, g (f a0)) p)) (ap (λ a0 : A, f (g (f a0))) p).
Proof. intros. induction p. now cbn. Defined.

Lemma qinv_ishae: ∏ {A B: UU} (f: A -> B), qinv f -> ishae f.
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
         specialize (@Hc A a (funcomp f g) eta). cbn in *.
         unfold funcomp in *.

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

Lemma isequiv_ishae: ∏ {A B: UU} (f: A -> B), isequiv f -> ishae f.
Proof. intros A B f e.
       apply h249_ii in e.
       now apply qinv_ishae.
Defined.

Lemma ishae_isequiv: ∏ {A B: UU} (f: A -> B), ishae f -> isequiv f.
Proof. intros A B f e.
       apply ishae_qinv in e.
       now apply h249_i.
Defined.

Definition fiber  {A B: UU} (f: A -> B) (y: B): UU := ∑ x: A, Id (f x) y.
Definition isSurj {A B: UU} (f: A -> B): UU := ∏ (y: B), fiber f y.
(** total *)
Definition totalA {A: UU} (P Q: A -> UU) (f: ∏ x: A, P x -> Q x): 
  (∑ x: A, P x) -> (∑ x: A, Q x).
Proof. intro w. exact { (pr1 w); (f (pr1 w) (pr2 w)) }. Defined.

Definition isContr  (A: UU): UU := ∑ a: A, ∏ x: A, Id a x.
Definition isContrP {A: UU} (P: A -> UU): UU :=  ∏ x: A, isContr (P x).
Definition isContrf {A B: UU} (f: A -> B): UU := ∏ y: B, isContr (fiber f y).
Definition fibration (X: UU) := X -> UU.
Definition total   {X: UU} (P: fibration X):= ∑ x: X, P x.
Definition section {X: UU} (P: fibration X):= ∏ x: X, P x.
Definition retract (A B: UU) := ∑ r: A -> B, ∑ s: B -> A, ∏ y: B, Id (r (s y)) y.

Definition wfunext_def: UU := ∏  (A: UU) (P: A -> UU),
  (∏x: A, isContr (P x)) -> isContr (∏x: A, P x).

Corollary h432c: ∏ {A B: UU} (f: A -> B) (e: isequiv f) (x x':A) (y: B),
  Id (f x) y /\ Id (f x') y -> Id x x'.
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

Corollary h432d: ∏ {A B: UU} (f: A -> B) (e: isequiv f) (y: B)
  (a b: ∑x: A, Id (f x) y), Id a b.
Proof. intros.
        destruct a as (a, p).
        destruct b as (b, q).
        specialize (@h432c A B f e a b y); intro H.
        assert (H0: Id (f a) y /\ Id (f b) y ) by easy.
        specialize (H H0).
        induction H. dependent induction p.
        dependent induction q. easy.
Defined.

Lemma h432_i: ∏ {A B: UU} (f: A -> B), isequiv f -> isContrf f.
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

Lemma h432_ii: ∏ {A B: UU} (f: A -> B), isContrf f -> isequiv f.
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

Lemma h432: ∏ {A B: UU} (f: A -> B), (isContrf f) <-> (isequiv f).
Proof. intros. split. apply h432_ii. apply h432_i. Defined.

(** Typoids due to Petrakis *)

Reserved Notation "x '~*' y" (at level 70, y at next level).
Reserved Notation "x '~==' y" (at level 70).
Reserved Notation "x 'o' y" (at level 69). 

Class Setoid (A: UU): UU :=
   mkSetoid
   {
      et         :  relation A where "a ~* b" := (et a b);
      eqv        :  ∏ x: A, x ~* x;
      star       :  ∏ {x y z: A}, x ~* y -> y ~* z -> x ~* z where "a 'o' b" := (star a b);
      inv        :  ∏ {x y: A}, x ~* y -> y ~* x;
   }.

Arguments et {_ _} _ _.
Arguments eqv {_ _} _.
Arguments star {_ _ _ _ _} _ _.
Notation "x 'o' y"   := (star x y): type_scope.
Notation "x '~*' y"  := (et x y) : type_scope.

Instance EqRel_et: ∏ {A} {S: Setoid A}, Equivalence (@et A S).
  constructor; intro.
        apply eqv.
        apply (@inv A).
        apply (@star A).
Defined.

Definition dirprodSetoid {A B: UU} (SA: Setoid A) (SB: Setoid B): Setoid (dirprod A B).
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

Proposition p11T: ∏ {A B: UU} (SA: Setoid A) (SB: Setoid B),
  ∏ (z w: dirprod A B), (dirprod (@et A SA (pr1 z) (pr1 w)) (@et B SB (pr2 z) (pr2 w)) ->
    @et (dirprod A B) (dirprodSetoid SA SB) z w).
Proof. cbn. intros A B SA SB z w (e1, e2). split; easy. Defined.

Proposition p11G: ∏ {A B: UU} (SA: Setoid A) (SB: Setoid B),
  ∏ (z w: dirprod A B), (@et (dirprod A B) (dirprodSetoid SA SB) z w ->
     dirprod (@et A SA (pr1 z) (pr1 w)) (@et B SB (pr2 z) (pr2 w))).
Proof. cbn. intros A B SA SB z w (e1, e2). split; easy. Defined.

Class Typoid (A: UU): UU :=
   mkTypoid
   {
      st         :  Setoid A;
      ett        :  ∏ {x y: A}, relation (@et A st x y) where "a ~== b" := (ett a b);
      ett_refl   :  ∏ {x y: A} (e: x ~* y), e ~== e;
      ett_sym    :  ∏ {x y: A} (e d: x ~* y), e ~== d -> d ~== e;
      ett_trans  :  ∏ {x y: A} (e d f: x ~* y), e ~== d -> d ~== f -> e ~== f;
      Typ1_i     :  ∏ {x y: A} (e: x ~* y), (eqv x) o e ~== e;
      Typ1_ii    :  ∏ {x y: A} (e: x ~* y), e o (eqv y) ~== e;
      Typ2_i     :  ∏ {x y: A} (e: x ~* y), e o (inv e) ~== eqv x;
      Typ2_ii    :  ∏ {x y: A} (e: x ~* y), (inv e) o e ~== eqv y;
      Typ3       :  ∏ {x y z t: A} (e1: x ~* y) (e2: y ~* z) (e3: z ~* t), ((e1 o e2) o e3) ~== (e1 o (e2 o e3));
      Typ4       :  ∏ {x y z: A} (e1 d1: x ~* y) (e2 d2: y ~* z), e1 ~== d1 -> e2 ~== d2 -> (e1 o e2) ~== (d1 o d2);
      SP         :> ∏ {x y z: A}, Proper (@ett x y ==> @ett y z ==> @ett x z) (star);
      EP         :> ∏ {x: A}, Proper (@ett x x) (eqv x);
      IP         :> ∏ {x y: A}, Proper (@ett x y ==> @ett y x) (inv)
   }.

Notation "x '~==' y" := (ett x y) : type_scope.

Instance EqRel_ett: ∏ {A T} x y, Equivalence (@ett A T x y).
  constructor; intro.
        apply ett_refl.
        apply ett_sym.
        apply ett_trans.
Defined.

Proposition p11_pr1: ∏ {A B: UU} (TA: Typoid A) (TB: Typoid B),
   ∏ (z w: dirprod A B) (e1: (@et A (@st A TA) (pr1 z) (pr1 w))) (e2: @et B (@st B TB) (pr2 z) (pr2 w)), 
    (@ett A TA _ _  (pr1 ( (p11G (@st A TA) (@st B TB) z w (p11T (@st A TA) (@st B TB) z w {e1; e2})))) e1).
Proof. cbn. intros A B TA TB z w e1 e2.
       easy. Defined.

Proposition p11_pr2: ∏ {A B: UU} (TA: Typoid A) (TB: Typoid B),
   ∏ (z w: dirprod A B) (e1: (@et A (@st A TA) (pr1 z) (pr1 w))) (e2: @et B (@st B TB) (pr2 z) (pr2 w)), 
    (@ett B TB _ _  (pr2 ( (p11G (@st A TA) (@st B TB) z w (p11T (@st A TA) (@st B TB) z w {e1; e2})))) e2).
Proof. cbn. intros A B TA TB z w e1 e2. easy. Defined.

Proposition h13: ∏ {A B: UU} (TA: Typoid A) (TB: Typoid B), Typoid (dirprod A B).
Proof. intros.
       unshelve econstructor.
       - exact (dirprodSetoid (@st A TA) (@st B TB)).
       - unfold relation. cbn. intros z w (e1, e2) (e1', e2').
         exact (dirprod (e1 ~== e1') (e2 ~== e2')).
       - cbn. intros. destruct e.
         split; easy.
       - cbn. intros. destruct e, d.
         destruct H. split. now rewrite pr7. now rewrite pr8.
       - cbn. intros. destruct e, d, f, H, H0.
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
       - cbn. intros. destruct e1, e2, d1, d2, H, H0. cbn in *.
         split; now rewrite Typ4.
       - cbn. repeat intro. destruct x0, y0, x1, y1, H, H0. cbn in *.
         split; apply Typ4; easy.
       - cbn. repeat intro. easy.
       - cbn. repeat intro. destruct x0, y0, H. cbn in *.
         split. now rewrite pr7. now rewrite pr8.
Defined.

Definition e3 A: Typoid A.
Proof. unshelve econstructor.
        - unshelve econstructor.
          + exact Id.
          + intro x. exact (refl x).
          + intros x y z p q.
            exact (concat p q).
          + intros x y p.
          exact (inverse p).
        - intros x y.
          exact (fun e e': Id x y => Id e e').
        - intros. now cbn.
        - cbn. intros. exact (inverse X).
        - cbn. intros. now induction X, X0.
        - cbn. intros. now induction e.
        - intros. now destruct e.
        - intros. cbn. now destruct e.
        - intros. cbn. now destruct e.
        - intros. cbn. now destruct e1, e2, e3.
        - intros. cbn in *. now induction X, X0.
        - repeat intro. cbn. now induction X, X0.
        - repeat intro. now cbn.
        - repeat intro. cbn. now induction X.
Defined.

Definition e4 (A B: UU): Typoid (A -> B).
Proof. unshelve econstructor.
       - unshelve econstructor.
         + intros f g.
           exact (∏x: A, Id (f x) (g x)). 
         + intro f. cbn.
           exact (fun x: A => refl (f x)).
         + cbn. intros f g h H G.
           exact (fun x => concat (H x) (G x)).
         + cbn. intros f g H.
           exact (fun x => inverse (H x)).
       - intros f g H H'. cbn in *.
         exact (∏x: A, Id (H x) (H' x)).
       - cbn. intros. easy.
       - cbn. intros.
         exact (inverse (X x0)).
       - cbn. intros.
         exact (concat (X x0) (X0 x0)).
       - cbn. intros.
         now destruct (e x0).
       - cbn. intros.
         now destruct (e x0).
       - cbn. intros.
         now destruct (e x0).
       - cbn. intros.
         now destruct (e x0).
       - cbn. intros.
         apply inverse, concat_assoc.
       - cbn. intros.
         now induction (X x0), (X0 x0).
        - repeat intro. cbn. now induction (X x2), (X0 x2).
        - repeat intro. now cbn.
        - repeat intro. cbn. now induction (X x1).
Defined.

Example e5_isequiv: Typoid (UU).
Proof. unshelve econstructor.
       - unshelve econstructor. 
         + intros A B.
           exact (∑ f: A -> B, isequiv f).
         + intros. cbn.
           exists id. apply h249_i.
           unshelve econstructor.
           * exact id.
           * easy.
         + cbn. intros.
           destruct X as (f, cc1).
           destruct X0 as (g, cc2).
           apply h249_ii in cc1.
           apply h249_ii in cc2.
           destruct cc1 as (invf, (cc1a, cc1b)).
           destruct cc2 as (invg, (cc2a, cc2b)).
           unfold compose, homotopy, id in *. cbn.
           exists (compose f g).
           apply h249_i.
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
           apply h249_ii in cc1.
           destruct cc1 as (invf, (cc1, cc2)).
           exists invf.
           apply h249_i.
           unshelve econstructor.
           ++ exact f.
           ++ split; easy.
       - cbn. intros A B (f, u) (f', u').
         exact (∏x: A, Id (f x) (f' x)).
       - cbn. intros. now destruct e.
       - cbn. intros. destruct d, e.
         intro a.
         specialize (H a).
         now apply inverse in H.
       - cbn. intros.
         destruct e, f, d.
         intro a.
         exact (concat (H a) (H0 a)).
       - cbn. intros.
         destruct e, (h249_ii pr4), pr6.
         easy.
       - cbn. intros.
         destruct e, (h249_ii pr4), pr6.
         easy.
       - cbn. intros. destruct e.
         cbn. destruct ( h249_ii pr4), pr6.
         cbn.
         unfold homotopy, compose, id in *.
         intro x0.
         now specialize (pr7 x0).
       - cbn. intros. destruct e.
         cbn. destruct ( h249_ii pr4), pr6.
         cbn.
         unfold homotopy, compose, id in *.
         intro x0.
         now specialize (pr6 x0).
       - cbn. intros.
         destruct e1, e2, e5, (h249_ii pr4), pr10,
         (h249_ii pr6), pr13. cbn. 
         destruct (h249_ii pr8), pr16. now cbn.
       - cbn. intros.
         destruct e1, e2, d1, d2, (h249_ii pr4), (h249_ii pr8),
         pr12, (h249_ii pr6), pr14, pr17, (h249_ii pr10), pr21.
         intro x0.
         specialize (H0 (pr3 x0)).
         specialize (H x0).
         apply Id_eql in H.
         unfold compose.
         now rewrite H in H0 at 2.
       - repeat intro. cbn.
         destruct x0, x1, y0, y1, (h249_ii pr4), 
         (h249_ii pr8), pr12, (h249_ii pr6), pr17,
         pr14, (h249_ii pr10), pr21.
         cbn in *.
         intro x0. unfold compose.
         specialize (H0 (pr3 x0)).
         specialize (H x0).
         now induction H, H0.
       - repeat intro. now cbn.
       - repeat intro.
         destruct x0, y0, (h249_ii pr4), pr8, ( h249_ii pr6 ), pr11,
         ( h249_ii pr4 ). cbn.
         destruct ( h249_ii pr4 ), ( h249_ii pr6 ), pr16, pr18, pr14.
         unfold homotopy, compose, id in *.
         intro b.
         pose proof H as HH.
         specialize (pr20 (pr15 (pr5 (pr17 b)))).
         specialize (pr18 b).
         apply Id_eql in pr18.
         rewrite pr18 in pr20.
         specialize (H (pr15 b)).
         apply Id_eql in H.
         rewrite <- H in pr20.
         specialize (pr16 b).
         apply Id_eql in pr16.
         rewrite pr16 in pr20.
         exact (inverse pr20).
Defined.

Example e5_ishae: Typoid (UU).
Proof. unshelve econstructor.
       - unshelve econstructor.
         + intros A B.
           exact (∑ f: A -> B, ishae f).
         + intros. cbn.
           exists id. apply isequiv_ishae, h249_i.
           unshelve econstructor.
           * exact id.
           * easy.
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
       - cbn. intros A B (f, u) (f', u').
         exact (∏x: A, Id (f x) (f' x)).
       - cbn. intros. now destruct e.
       - cbn. intros. destruct d, e.
         intro a.
         specialize (H a).
         now apply inverse in H.
       - cbn. intros.
         destruct e, f, d.
         intro a.
         exact (concat (H a) (H0 a)).
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
         destruct e1, e2, e5, (h249_ii (ishae_isequiv pr3 pr4)),
         (h249_ii (ishae_isequiv pr5 pr6)), pr8, pr10, pr12. cbn.
         destruct (h249_ii (ishae_isequiv pr7 {pr8; pr13})).
         destruct pr17. now cbn.
       - cbn. intros.
         destruct e1, e2, d1, d2, (h249_ii (ishae_isequiv pr3 pr4)), (h249_ii (ishae_isequiv pr7 pr8)),
         pr12, (h249_ii (ishae_isequiv pr5 pr6)), pr14, pr17, (h249_ii (ishae_isequiv pr9 pr10)), pr21.
         intro x0.
         specialize (H0 (pr3 x0)).
         specialize (H x0).
         apply Id_eql in H.
         unfold compose.
         now rewrite H in H0 at 2.
       - repeat intro. cbn.
         destruct x0, x1, y0, y1, (h249_ii (ishae_isequiv pr3 pr4)), 
         (h249_ii (ishae_isequiv pr7 pr8)), pr12, (h249_ii (ishae_isequiv pr5 pr6)), pr17,
         pr14, (h249_ii (ishae_isequiv pr9 pr10)), pr21.
         cbn in *.
         intro x0. unfold compose.
         specialize (H0 (pr3 x0)).
         specialize (H x0).
         now induction H, H0.
       - repeat intro. now cbn.
       - repeat intro.
         destruct x0, y0, (h249_ii (ishae_isequiv pr3 pr4)), pr8, (h249_ii (ishae_isequiv pr5 pr6)), pr11
         . cbn. destruct (h249_ii (ishae_isequiv pr3 pr4)),  pr14, (h249_ii (ishae_isequiv pr5 pr6)).
           cbn. destruct pr17.
         unfold homotopy, compose, id in *.
         intro b.
         pose proof H as HH.
         specialize (pr15 (pr10 (pr5 (pr16 b)))).
         specialize (pr12 (pr16 b)).
         apply Id_eql in pr12.
         rewrite pr12 in pr15.
         specialize (H (pr16 b)).
         apply Id_eql in H.
         rewrite H in pr15.
         specialize (pr17 b).
         apply Id_eql in pr17.
         now rewrite pr17 in pr15.
Defined.

Arguments et {_} _ _ _ .

Reserved Notation "x '~>' y" (at level 70, y at next level).

Class TypoidFunction {A B: UU} (X: Typoid A) (Y: Typoid B): UU :=
   mkTypoidFunction 
   {
      typof    :  A -> B;
      theta    :  ∏ (x y: A), (@et A (@st A X) x y) -> (@et B (@st B Y)  (typof x) (typof y));
      theta2nd :  ∏ (x y: A) (e d: @et A (@st A X)  x y) (i: @ett A X x y e d), (@ett B Y _ _ (theta x y e) (theta x y d));
      d6i      :  ∏ (x: A), @ett B Y _ _ (theta x x (eqv x)) (eqv (typof x));
      d6ii     :  ∏ (x y z: A) (e1: @et A (@st A X)  x y) (e2: @et A (@st A X)  y z), @ett B Y _ _ (theta x z (@star A (@st A X)  _ _ _ e1 e2)) 
                                                                                      (@star B (@st B Y)  _ _ _ (theta x y e1) (theta y z e2));
      TP       :> ∏ {x y}, Proper (@ett A X  x y ==> @ett B Y(typof x) (typof y)) (theta x y);
   }.

Notation "x '~>' y"  := (TypoidFunction x y) : type_scope.

Arguments theta {_ _} _ {_ _ _ _}  _ .
Arguments theta2nd {_ _} _ {_ _ _ _}  _ .

Corollary h14_pr1 {A B: UU} (TA: Typoid A) (TB: Typoid B): (h13 TA TB ~> TA).
Proof. unshelve econstructor.
       - exact pr1.
       - cbn. intros u w (e1, e2).
         exact e1.
       - cbn. intros. destruct e, d, i.
         exact pr7.
       - now cbn.
       - cbn. intros. now destruct e1, e2.
       - cbn. repeat intro. destruct x0, y0, H.
         exact pr7.
Defined.

Corollary h14_pr2 {A B: UU} (TA: Typoid A) (TB: Typoid B): (h13 TA TB ~> TB).
Proof. unshelve econstructor.
       - exact pr2.
       - cbn. intros u w (e1, e2).
         exact e2.
       - cbn. intros. destruct e, d, i.
         exact pr8.
       - now cbn.
       - cbn. intros. now destruct e1, e2.
       - cbn. repeat intro. destruct x0, y0, H.
         exact pr8.
Defined.

Corollary h15: ∏ {A B: UU} (TA: Typoid A) (TB: Typoid B) (z w: dirprod A B) 
  (e: @et (dirprod A B) (dirprodSetoid (@st A TA) (@st B TB)) z w), 
  (@ett (dirprod A B) (h13 TA TB)  z w (@p11T _ _  _ _ z w {pr1 e; pr2 e}) e).
Proof. intros. cbn. destruct e. split; now cbn in *. Defined.

Corollary h16: ∏ {A B: UU} (TA: Typoid A) (TB: Typoid B) (z w: dirprod A B)
  (e1 d1: @et A (@st A TA) (pr1 z) (pr1 w)) (e2 d2: @et B (@st B TB) (pr2 z) (pr2 w)),
  (e1 ~== d1) -> (e2 ~== d2) -> (@ett  (dirprod A B) (h13 TA TB)  z w (@p11T _ _ _ _ z w {e1; e2})
                                                                      (@p11T _ _ _ _ z w {d1; d2})).
Proof. cbn. intros. split; easy. Defined.

Proposition p7 {A B: UU} (C: Typoid A) (D: Typoid B) (F: C ~> D): 
   ∏ (x y: A) (e: x ~* y), theta C (inv e) ~== inv (theta C e). 
Proof. intros.
       assert (theta C (inv e) o (theta C e) ~== inv (theta C e) o (theta C e)).
       { now rewrite Typ2_ii, <- d6ii, Typ2_ii, d6i. }
       assert (theta C (inv e) o (theta C e) o inv (theta C e) ~== 
               inv (theta C e) o (theta C e) o inv (theta C e)).
       { now rewrite H. }
       now rewrite !Typ3, !Typ2_i, !Typ1_ii in H0.
Qed.

Example apf_eq {A B: UU}:
   let A0 := e3 A in
   let B0 := e3 B in
   ∏ (f: A0 ~> B0) (x y: A), ∏ p: Id x y, Id (@typof A B A0 B0 f x) (@typof A B A0 B0 f y).
Proof. intros. now induction p. Defined.

Example apf2_eq {A B: UU}:
   let A0 := e3 A in
   let B0 := e3 B in
   ∏ (f: A0 ~> B0) (x y: A), ∏ p q: Id x y, ∏ r: Id p q, Id (apf_eq f x y p) (apf_eq f x y q).
Proof. intros. now induction r. Defined.

Example e8_i {A B: UU}:
   let A0 := e3 A in
   let B0 := e3 B in   
   ∏ (f: A0 ~> B0) (x y z: A), ∏ (p: Id x y) (q: Id y z), 
   Id (apf_eq f x z (concat p q)) (concat (apf_eq f x y p) (apf_eq f y z q)).
Proof. intros. now induction p, q. Defined.

Proposition p9 {A B C: UU} (X: Typoid A) (Y: Typoid B) (Z: Typoid C) (f: X ~> Y) (g: Y ~> Z): X ~> Z.
Proof. intros.
       unshelve econstructor.
       - exact (compose (@typof A B X Y f) (@typof B C Y Z g)).
       - intros x y e. exact (theta Y (theta X e)).
       - intros. cbn. exact (theta2nd Y _ _ (theta2nd X e d i)).
       - intros. cbn. unfold compose. now do 2 rewrite d6i.
       - intros. cbn. now do 2 rewrite d6ii.
       - repeat intro.
         now rewrite H.
Defined.

Definition idtoeqvT: ∏ {A: UU} {x y: A} {T: Typoid A} (p: Id x y), @et A (@st A T) x y.
Proof. intros A x y T p.
       exact (transport (fun z => @et A (@st A T) x z) p (eqv x)).
Defined.

Definition idtoeqvT2: ∏ {A: UU} {T: Typoid A} {x y: A} {p q: Id x y} (r: Id p q),
  @ett A T x y (idtoeqvT p) (idtoeqvT q).
Proof. intros A x y T p q r.
       unfold idtoeqvT. now induction r.
Defined.

Proposition h10: ∏ {A: UU} (TA: Typoid A), (e3 A) ~> TA.
Proof. intros.
       unshelve econstructor.
       - exact id.
       - cbn. intros x y e. exact (idtoeqvT e).
       - cbn. intros. now induction i.
       - cbn. intro a. now unfold id.
       - cbn. intros. induction e1, e2. cbn.
         now rewrite Typ1_i.
       - cbn. repeat intro. now induction X.
Defined.

Class UnivalentTypoid (A: UU): UU :=
   mkUnivalentTypoid
   {
      TT         :  Typoid A;
      Ua         :  ∏ {x y: A} (e: @et A (@st A TT) x y), Id x y;
      Ua2        :  ∏ {x y: A} {e d: @et A (@st A TT) x y} (i: @ett A TT x y e d), Id (Ua e) (Ua d);
      UT_ob1     :  ∏ {x y: A} (p: Id x y), Id (Ua (@idtoeqvT A x y TT p)) p;
      UT_ob2     :  ∏ {x y: A} (e: @et A (@st A TT) x y), (@ett A TT x y (@idtoeqvT A x y TT (Ua e)) e);
   }. 

Definition ap2: ∏ {A B: UU} {x y: A} {p q: Id x y} (f: A -> B) (r: Id p q),
  Id (ap f p) (ap f q). 
Proof. intros. now induction r. Defined.

Example h8: ∏ {A B: UU} (f: A -> B), (e3 A) ~> (e3 B).
Proof. intros. 
       unshelve econstructor.
       - exact f.
       - cbn. intros x y p.
         exact (ap f p).
       - cbn. intros.
         exact (ap2 f i).
       - cbn. easy.
       - cbn. intros. now induction e1, e2.
       - cbn. repeat intro. now induction X.
Defined.

Proposition h18 {A: UU} (UT: UnivalentTypoid A): (@TT A UT) ~> (e3 A).
Proof. unshelve econstructor.
       - exact id.
       - intros x y e. unfold id. cbn in *.
         exact (@Ua A UT x y e).
       - intros. cbn in *.
         exact (@Ua2 A UT x y e d i).
       - cbn. intros.
         exact (@UT_ob1 A UT x x refl).
       - cbn. intros.
         specialize (@UT_ob2 A UT x y e1); intros He1. 
         specialize (@UT_ob2 A UT y z e2); intros He2.
         assert (idtoeqvT (Ua e1) o idtoeqvT (Ua e2) ~== e1 o e2).
         { now rewrite He1, He2. }
         assert (idtoeqvT (Ua e1) o idtoeqvT (Ua e2) ~== 
                (@idtoeqvT A x z (@TT A UT) (concat (Ua e1) (Ua e2)) )).
         { specialize (@UT_ob2 A UT _ _ (e1 o e2)); intro HH.
           rewrite He1, He2, <- HH.
           specialize (@UT_ob1 A UT _ _ (concat (Ua e1) (Ua e2))); intro p.
           specialize (@UT_ob1 A UT _ _ (Ua (e1 o e2))); intro q.
           induction p, q, a. dependent induction a0. easy.
         }
         rewrite H in H0.
         specialize (@Ua2 A UT _ _ _ _ H0); intros HH.
         specialize (@UT_ob1 A UT _ _ (concat (Ua e1) (Ua e2))); intro HHH.
         apply Id_eql in HH. apply Id_eql in HHH.
         rewrite <- HH in HHH.
         now rewrite HHH.
       - repeat intro. 
         specialize (@Ua2 A UT x y x0 y0 H); intro HH.
         apply Id_eql in HH. now rewrite HH.
Defined.

Theorem h19_i {A B: UU} (f: A -> B) (U: UnivalentTypoid A) (W: Typoid B): (@TT A U) ~> W.
Proof. unshelve econstructor.
       - exact f.
       - intros x y e.
         exact (@idtoeqvT B (f x) (f y) W (ap f (Ua e))).
       - intros. cbn.
         exact (@idtoeqvT2 B W (f x) (f y) (ap f (Ua e)) (ap f (Ua d)) 
                  (@ap2 A B x y (Ua e) (Ua d) f (Ua2 i))).
       - cbn. intro a.
         specialize (@UT_ob2 A U _ _ (eqv a)); intro H.
         assert (p: Id (ap f (@theta A A (@TT A U) (e3 A) (h18 U) a a (eqv a))) (ap f (Ua (eqv a)))).
         { now cbn. }
         induction p. dependent induction a0. now cbn.
       - cbn. intros.
         specialize (@UT_ob1 A U _ _ (Ua e1)); intro p.
         specialize (@UT_ob1 A U _ _ (Ua e2)); intro q.
         specialize (@UT_ob1 A U _ _ (Ua (e1 o e2))); intro r.
         induction p, q, r, a, a0. dependent induction a1. cbn.
         now rewrite Typ1_i.
       - repeat intro. 
         specialize (@Ua2 A U x y x0 y0 H); intro HH.
         apply Id_eql in HH. now rewrite HH.
Defined.

Definition FUni: ∏ {A B: UU}, UnivalentTypoid (A -> B).
Proof. intros.
       unshelve econstructor.
       - exact (e4 A B).
       - unfold et. unfold e4.
         intros. cbn in *.
         apply funext in e. exact e.
       - intros. cbn.
         apply funext in i. now induction i.
       - cbn. intros.
         unfold funext.
         destruct (FE A (λ _ : A, B) x y).
         unfold idtoeqvT, transport, Id_rect. cbn.
         destruct p. cbn in *. destruct pr4.
         unfold homotopy, compose, id in *. cbn in *.
         specialize (pr5 refl). unfold happly in pr5.
         cbn in *. easy.
       - cbn. intros.
         unfold funext.
         destruct (FE A (λ _ : A, B) x y).
         unfold idtoeqvT, transport, Id_rect. cbn.
         unfold homotopy, compose, id in *. cbn in *. 
         destruct pr4.
         specialize (pr4 e).
         destruct (pr3 e). cbn in *.
         unfold happly in pr4. cbn in *.
         apply Id_eql in pr4. now rewrite <- pr4.
Defined.

Definition UUUni: UnivalentTypoid UU.
Proof. unshelve econstructor.
       - exact e5_isequiv.
       - unfold et. unfold e5_isequiv.
         intros A B e. cbn in *.
         now apply ua in e.
       - intros A B e d p. cbn in *.
         destruct e as (f, u).
         destruct d as (g, w). cbn in *.
         apply funext in p.
         assert (H: Id (transport (fun f => isequiv f) p u) w).
         { induction p. cbn. admit. } compute in H.
         now induction p, H.
Admitted.


Proposition h20: ∏ (A B: UU) (x y: A) (p: Id x y) (TA: Typoid A) (TB: UnivalentTypoid B) (f: TA ~> (@TT B TB))
 (** why i? ― strict typoid function ― how to get that? *) 
               (i: (@theta _ _ _ _ f x x (eqv x)) ~== (eqv (@typof A B TA (@TT B TB) f x)))
 (** why ii ― strict univalence? ― how to get that?  *)  
               (ii: Id (@Ua B TB (@typof A B TA (@TT B TB) f x) (@typof A B TA (@TT B TB) f x) (eqv (@typof A B TA (@TT B TB) f x))) 
                       (refl (@typof A B TA (@TT B TB) f x))),
  Id (Ua (@theta _ _ _ _ f x y (@idtoeqvT _ _ _ _ p))) (ap (@typof A B TA (@TT B TB) f) p).
Proof. intros.
       specialize (@Ua2 B TB _ _ _ _ i); intro HH.
       induction p. cbn in *.
       induction ii.
       exact HH.
Defined.

Definition eqpairT (A B: UU): ∏ (z w: dirprod A B),
  (Id z w -> dirprod (Id (pr1 z) (pr1 w)) (Id (pr2 z) (pr2 w))).
Proof. intros z w p.
        induction p. exact ({ refl (pr1 a); refl (pr2 a) } ).
Defined.

Definition paireqT (A B: UU): ∏ (z w: dirprod A B),
  (dirprod (Id (pr1 z) (pr1 w)) (Id (pr2 z) (pr2 w)) -> Id z w).
Proof. intros z w p.
        destruct p as (p, q).
        destruct z as (z1, z2).
        destruct w as (w1, w2).
        cbn in *.
        now induction p, q.
Defined.

Lemma eqpair_paireqT: ∏  {A B: UU} (z w: dirprod A B) (p1 q1: Id (pr1 z) (pr1 w)) (p2 q2: Id (pr2 z) (pr2 w)),
  Id (pr1 (@eqpairT _ _ z w (@paireqT _ _ z w {p1; p2}))) p1.
Proof. cbn. intros. destruct z, w. cbn in *.
        now induction p1, p2.
Defined.

Definition appaireqT {A B: UU} (z w: dirprod A B) 
                      (p1 q1: Id (pr1 z) (pr1 w))  (p2 q2:  Id (pr2 z) (pr2 w)):
  dirprod (Id p1 q1) (Id p2 q2) -> Id (paireqT A B z w {p1; p2}) (paireqT A B z w {q1; q2}).
Proof. intros p.
        destruct p as (p, q).
        induction p, q. easy.
Defined.

Lemma h22: ∏ (A B: UU) (TA: Typoid A) (TB: Typoid B) (idA: (e3 A) ~> TA) (idB: (e3 B) ~> TB),
  e3 (dirprod A  B) ~> h13 TA TB.
Proof. intros.
        unshelve econstructor.
        - exact (@id (dirprod A B)).
        - cbn. intros z w p.
          specialize (pr1 (@eqpairT _ _ z w p)); intro p1.
          specialize (pr2 (@eqpairT _ _ z w p)); intro p2.
          specialize (@idtoeqvT A (pr1 z) (pr1 w) TA p1); intro e1.
          specialize (@idtoeqvT B (pr2 z) (pr2 w) TB p2); intro e2.
          now apply p11T. 
        - cbn. intros z w p q i.
          induction p. cbn. dependent induction q. cbn. split; easy.
        - cbn. intros z. unfold id. split; easy.
        - cbn. intros x y z e d. induction e. cbn. dependent induction d. cbn.
          split; destruct a; cbn; now rewrite Typ1_ii.
        - cbn. repeat intro. induction X. split; easy.
Defined.

Lemma h23: ∏ (A B: UU) (TA: UnivalentTypoid A) (TB: UnivalentTypoid B), 
  UnivalentTypoid (dirprod A B).
Proof. intros.
        unshelve econstructor.
        - exact (h13 (@TT A TA) (@TT B TB)).
        - intros z w e.
           assert (e1': (@et A (@st A (@TT A TA)) (pr1 z) (pr1 w))).
           { exact (pr1 (@p11G A B (@st A (@TT A TA)) (@st B (@TT B TB)) z w e)). }
           assert (e2': (@et B (@st B (@TT B TB)) (pr2 z) (pr2 w))).
           { exact (pr2 (@p11G A B (@st A (@TT A TA)) (@st B (@TT B TB)) z w e)). }
           assert (p1': Id (pr1 z) (pr1 w)).
           { exact (@Ua A TA (pr1 z) (pr1 w) e1'). }
           assert (p2': Id (pr2 z) (pr2 w)).
           { exact (@Ua B TB (pr2 z) (pr2 w) e2'). }
           exact (@paireqT _ _ z w {p1'; p2'}).
         - intros z w e d i.
           specialize (@appaireqT _ _ z w (Ua (pr1 (p11G st st z w e))) (Ua (pr1 (p11G st st z w d)))
           (Ua (pr2 (p11G st st z w e))) (Ua (pr2 (p11G st st z w d))) 
           ); intros H.
           cbn in *.
           apply H. 
           destruct e as (e1, e2).
           destruct d as (d1, d2).
           destruct i as (i1, i2). cbn in *.
           specialize (@Ua2 A TA _ _ e1 d1 i1); intro H1.
           specialize (@Ua2 B TB _ _ e2 d2 i2); intro H2.
           split; easy.
         - intros z w p.
           cbn. destruct z, w. dependent induction p. cbn.
           unfold Id_rect. 
           specialize (@Ua2 A TA _ _ (eqv pr5) (eqv pr5) (ett_refl (eqv pr5))); intro p.
           induction p. dependent induction a.
           specialize (@Ua2 B TB _ _ (eqv pr6) (eqv pr6) (ett_refl (eqv pr6))); intro p.
           induction p. dependent induction a0. easy.
         - intros z w e. cbn.
           destruct z as (z1, z2).
           destruct w as (w1, w2).
           destruct e as (e1, e2). cbn in *.
           unfold Id_rect.
           specialize (@UT_ob2 A TA z1 w1 e1); intros.
           specialize (@UT_ob2 B TB z2 w2 e2); intros. 
           destruct (Ua e1), (Ua e2). cbn.
           split. rewrite <- H. now cbn.
           rewrite <- H0. now cbn.
Defined.

Definition Typfun {A B: UU} (TA: Typoid A) (TB: Typoid B) (f: A -> B) :=
    ∑ thef: ∏ (x y: A) (e: @et A (@st A TA) x y), (@et B (@st B TB) (f x) (f y)),
    dirprod 
    (∏ (x y z: A) (e: @et A (@st A TA) x y) (d: @et A (@st A TA) y z), 
      dirprod (@ett B TB _ _ (thef x x (eqv x)) (eqv (f x))) 
              (@ett B TB _ _ (thef x z (@star A (@st A TA)  _ _ _ e d)) (@star B (@st B TB) _ _ _ (thef x y e) (thef y z d)))
    )
    (∏ (x y: A) (e d: @et A (@st A TA) x y) (i: @ett A TA _ _ e d), 
      (@ett B TB _ _ (thef x y e) (thef x y d))
    ).

Definition ExponentialTypoid {A B: UU} (TA: Typoid A) (TB: Typoid B): Typoid (TypoidFunction TA TB).
Proof. unshelve econstructor.
       - unshelve econstructor.
         + intros e f.
           exact (∑ f: A -> B, Typfun TA TB f).
         + intro f. cbn in *.
           exists (@typof A B TA TB f).
           exists (@theta A B TA TB f).
           split. intros. split.
           now rewrite d6i.
           now rewrite d6ii.
           intros. now rewrite i.
         + cbn. intros theta gam eta.
           destruct theta as (f, phif, phif2, U1, U2, rt).
           destruct gam as (g, phig, phig2, W1, W2, rg).
           destruct eta as (h, phih, phih2, V1, V2, re). cbn in *.
           intros e d.
           destruct e as (gam_fg, gam2_fg). cbn in *.
           destruct d as (gam_gh, gam2_gh). cbn in *.
           exists f.
           unshelve econstructor.
Admitted.

 