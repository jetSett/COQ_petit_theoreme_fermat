(* Addition *)
Lemma null:
forall x , x + 0 = x.
Proof.
induction x. trivial.
simpl. rewrite IHx. reflexivity.
Qed.
Lemma next:
forall x y, x = y <-> S x = S y.
Proof.
split.
intros. rewrite H. reflexivity.
intros. injection H. trivial.
Qed.
Lemma s:
forall x, x+1 = S x.
Proof.
induction x. trivial. simpl. rewrite IHx. reflexivity.
Qed.
Lemma switch:
forall x y, x + S y = S x + y.
Proof.
intros. induction x. trivial.
simpl. rewrite IHx. trivial.
Qed.
Lemma simplif:
forall x y z, x = y <-> x+z = y+z.
Proof.
induction z.
rewrite ?null. split. auto. auto.
rewrite ?switch. simpl. split.
intros. apply IHz, next in H. assumption.
intros. injection H. apply IHz.
Qed.
Lemma plus:
forall x y, x+y = y+x.
Proof.
induction x.
symmetry. apply null.
intros. rewrite switch. simpl. rewrite IHx. reflexivity.
Qed.
Lemma parenth:
forall x y z, x+y+z = x+(y+z).
Proof.
intros. induction x. trivial.
simpl. rewrite IHx. reflexivity.
Qed.
 
 
(* Soustraction *)
Lemma minus:
forall x, x-0 = x.
Proof.
induction x. trivial. trivial.
Qed.
Lemma unchange:
forall x y, x<=y -> y-x+x = y.
Proof.
induction x. intros. rewrite null. apply minus.
intros. destruct y. inversion H.
rewrite switch. simpl. rewrite IHx. reflexivity. apply le_S_n. assumption.
Qed.
Lemma unchangebis:
forall x y, y+x-x = y.
Proof.
induction x. intros. rewrite minus. apply null.
intros. rewrite switch. simpl. apply IHx.
Qed.
 
 
(* Multiplication *)
Lemma zero:
forall x, x*0 = 0.
Proof.
induction x. trivial. trivial.
Qed.
Lemma one:
forall x, x*1 = x.
Proof.
induction x. trivial. simpl. apply -> next. assumption.
Qed.
Lemma uno:
forall x, 1*x = x.
Proof.
simpl. apply null.
Qed.
Lemma assofront:
forall x y a, a*(x+y) = a*x+a*y.
Proof.
induction a. trivial.
simpl. rewrite IHa, <- ?parenth. apply simplif.
rewrite plus, <-parenth. apply simplif, plus.
Qed.
Lemma assoback:
forall x y a, (x+y)*a = x*a+y*a.
Proof.
induction x. trivial.
intros. simpl. rewrite IHx, parenth. reflexivity.
Qed.
Lemma mult:
forall x y, x*y = y*x.
Proof.
induction x. symmetry. apply zero.
induction y. apply zero.
simpl. rewrite <- IHy, IHx. simpl. rewrite IHx, <- ?parenth.
apply -> next. apply simplif, plus.
Qed.
Lemma mparenth:
forall x y z, x*y*z = x*(y*z).
Proof.
intros. induction x. trivial.
simpl. rewrite assoback. rewrite IHx. reflexivity.
Qed.
Lemma prodzero:
forall x y, 0<y -> x*y=0 -> x=0.
Proof.
destruct x. trivial. intros. destruct H. rewrite one in H0. assumption.
inversion H0.
Qed.
Lemma prodone:
forall x y, x*y=1 -> y=1.
Proof.
destruct y. rewrite zero. trivial.
destruct y. trivial.
intros. destruct x. inversion H. inversion H.
Qed.
Lemma msimplif:
forall a x y, 0<a -> x*a = y*a -> x=y.
Proof.
induction x. symmetry. apply prodzero with a. assumption. rewrite <-H0. trivial.
induction y. simpl (0*a). apply prodzero.
intros. apply->next. apply IHx. assumption. simpl in H0.
rewrite plus in H0. symmetry in H0. rewrite plus in H0. symmetry in H0.
apply simplif in H0. assumption.
Qed.
Lemma mcomplic:
forall a x y, x=y -> x*a=y*a.
Proof.
intros. rewrite H. reflexivity.
Qed.
(*Lemma assominus:
forall x y a, (x-y)*a = x*a - y*a.
Proof.
intros. rewrite mult. rewrite mult with x a. rewrite mult with y a.
induction a. trivial. simpl. rewrite IHa.
induction y. rewrite ?zero. rewrite ?minus. reflexivity.
a-b+(c-d)=a+c-(b+d)

(*induction a. intros. rewrite ?zero. trivial.*)
induction x. trivial.
destruct y. simpl. symmetry. apply minus.
simpl. induction a. rewrite ?zero. trivial.
rewrite IHx. simpl.
Qed.*)
 
 
(* Puissances *)
Function pow (n m:nat) : nat :=
  match m with
  | 0 => 1
  | S k => n * (pow n k)
end.
Notation "n ** m" := (pow n m) (at level 39).
 
 
(* Infériorité *)
Lemma inf:
forall m n, S n <= m -> n <= m.
Proof.
induction m. intros. inversion H.
intros. apply le_S_n, le_S. assumption.
Qed.
Lemma disjonction:
forall n m, n <= m \/ m < n.
Proof.
induction n. left. apply le_0_n.
destruct m. right. apply le_n_S, le_0_n.
destruct IHn with m.
left. apply le_n_S. assumption.
right. apply le_n_S. assumption.
Qed.
Lemma le_transit:
forall z x y, x<=y -> y<=z -> x<=z.
Proof.
induction z. intros. inversion H0. rewrite H1 in H. assumption.
destruct x. intros. apply le_0_n.
destruct y. intros. inversion H.
intros. apply le_n_S. apply IHz with y. apply le_S_n. assumption. apply le_S_n. assumption.
Qed.
(*Lemma le_add:
forall a b x y, a<=b -> x<=y -> a+x<=b+y.
Proof.
induction a. induction b. trivial.
intros. rewrite<-switch. apply IHb. apply le_0_n. apply le_S. assumption.
induction b. intros. inversion H.
intros. simpl. apply le_n_S. apply IHa. apply le_S_n. assumption. assumption.
Qed.*)
Lemma le_const:
forall k a b, k+a<=k+b -> a<=b.
Proof.
induction k. trivial. intros. apply IHk. apply le_S_n. simpl in H. assumption.
Qed.
Lemma le_coef:
forall n m a, n*(S a)<=m*(S a) -> n<=m.
Proof.
induction n. intros. apply le_0_n.
destruct m. simpl. intros. inversion H.
intros. apply le_n_S, IHn with a. apply le_const with (S a). simpl. simpl in H. assumption.
Qed.
Lemma le_diff:
forall k a b, a+k=b -> a<=b.
Proof.
induction k. intros. rewrite<-H, null. apply le_n.
intros. apply inf. apply IHk. rewrite<-switch. assumption.
Qed.
(*Lemma le_mult:
forall a n, n<=S a*n.
Proof.
intros. induction a. rewrite uno. apply le_n.
apply le_transit with (S a*n). assumption. apply le_diff with n. rewrite plus. trivial.
Qed.*)
Lemma le_pow:
forall n a, a<=a**S n.
Proof.
destruct a. apply le_0_n. induction n. simpl. rewrite one. apply le_n.
apply le_transit with (S a**S n). assumption. apply le_diff with (a*(S a**n+a*S a**n)). trivial.
Qed.
 
 
(* Récurrence forte *)
Definition upto (P:nat ->Prop) n := (forall m, (S m)<=n -> P m).
Lemma upto_valid:
forall P, (forall a, upto P a) -> (forall n, P n).
Proof.
intros. apply H with (S n). apply le_n.
Qed.
Lemma upto_build:
forall P, (forall n, upto P n -> P n) -> (forall a, upto P a).
Proof.
unfold upto. induction a. intros. inversion H0.
intros. apply H. intros. apply IHa. apply le_transit with m. assumption. apply le_S_n. assumption.
Qed.
Lemma upto_proof:
forall P, (forall n, upto P n -> P n) -> (forall n, P n).
Proof.
intros P H. apply upto_valid, upto_build. assumption.
Qed.
 
 
(* Division *)
Definition divide x y := exists z, y=z*x.
Notation "x <| y" := (divide x y) (at level 0).
Lemma dsimplif:
forall x y k, 0<k -> (x*k)<|(y*k) -> x<|y.
Proof.
intros. destruct k. inversion H.
intros. destruct H0. exists x0. apply msimplif with (S k). assumption. rewrite mparenth. assumption.
Qed.
Lemma dcomplic:
forall x y k, x<|y -> (x*k)<|(y*k).
Proof.
intros. destruct H. exists x0. rewrite H. apply mparenth.
Qed.
Lemma divmutuel:
forall x y, x<|y -> y<|x -> x=y.
Proof.
intros. destruct y.
destruct H0. rewrite H0. apply zero.
destruct H, H0. symmetry in H. rewrite H0,<-mparenth,<-uno in H. apply msimplif, prodone in H.
rewrite H0, H. apply uno.
apply le_n_S, le_0_n.
Qed.
Definition prime (p:nat) : Prop :=
forall k, k <| p -> k = p \/ k = 1.
Lemma zero_not_prime:
prime 0 -> False.
Proof.
intros. destruct H with 2. exists 0. trivial. inversion H0. inversion H0.
Qed.
 
 
(* Gcd *)
Inductive is_gcd (a b g:nat) : Prop :=
  is_gcd_intro :
    (g <| a) ->
    (g <| b) ->
    (forall x, (x <| a) -> (x <| b) -> (x <| g)) ->
    is_gcd a b g.
Lemma gcd_greatest:
forall a b c g, c<|a -> c<|b -> is_gcd a b g -> c<|g.
Proof.
intros. inversion H1. apply H4. assumption. assumption.
Qed.
Lemma gcd_0:
forall a b, is_gcd a b 0 -> a=0 /\ b=0.
Proof.
intros. destruct H. destruct H. destruct H0.
split. rewrite H. apply zero. rewrite H0. apply zero.
Qed.
Lemma gcd_zero:
forall b, is_gcd 0 b b.
Proof.
intro. apply is_gcd_intro. exists 0. trivial. exists 1. symmetry. apply uno. trivial.
Qed.
Lemma gcd_unique:
forall a b g g', is_gcd a b g -> is_gcd a b g' -> g'=g.
Proof.
intros. destruct H. destruct H0. apply divmutuel.
apply H2. assumption. assumption.
apply H4. assumption. assumption.
Qed.
Lemma gcd_symmetry:
forall a b g, is_gcd a b g -> is_gcd b a g.
Proof.
intros. destruct H. apply is_gcd_intro. assumption. assumption.
intros. apply H1. assumption. assumption.
Qed.
(*Lemma gcd_decrease:
forall a b g, a<=b -> is_gcd a b g -> is_gcd a (b-a) g.
Proof.
destruct g. intros. apply gcd_0 in H0. destruct H0. rewrite H0, H1. apply gcd_zero.
intros. destruct H0. apply is_gcd_intro. assumption. destruct H0. destruct H1.
assert (x0=x0-x+x). symmetry. apply unchange. apply le_coef with g. rewrite<-H0,<-H1. assumption.
rewrite H0, H1. rewrite H3. exists (x0-x). rewrite assoback. apply unchangebis.
intros. apply H2. assumption. destruct H3. destruct H4. exists (x1+x0).
rewrite <-unchange with a b. rewrite H4, H3. symmetry. apply assoback. assumption.
Qed.*)
Lemma gcd_increase:
forall a b g, a<=b -> is_gcd a (b-a) g -> is_gcd a b g.
Proof.
destruct g. intros. apply gcd_0 in H0. destruct H0.
rewrite H0, minus in H1. rewrite H0, H1. apply gcd_zero.
intros. inversion H0. apply is_gcd_intro. assumption. destruct H1. destruct H2.
exists (x0+x). rewrite assoback,<-H1,<-H2. symmetry. apply unchange. assumption.
intros. destruct x. destruct H4, H5. rewrite H4, H5, ?zero, minus in H0.
apply gcd_unique with 0 0 0 (S g) in H0. inversion H0. apply gcd_zero.
apply H3. assumption. destruct H4, H5. rewrite H4, H5.
assert (x1=x1-x0+x0). symmetry. apply unchange. apply le_coef with x. rewrite<-H4,<-H5. assumption.
rewrite H6. exists (x1-x0). rewrite assoback. apply unchangebis.
Qed.
Lemma gcd_exists:
forall a b, (exists g, is_gcd a b g).
Proof.
intro a. apply upto_proof with (P:=fun x => forall b, exists g, is_gcd x b g). intros a' Ha.
destruct a'. intros. exists b. apply gcd_zero. remember (S a') as a0.
apply upto_proof with (P:=fun y => exists g, is_gcd a0 y g). intros b' Hb.
assert (a0<=b'\/b'<a0). apply disjonction. destruct H.
assert (exists g, is_gcd a0 (b'-a0) g). apply Hb. apply le_diff with a'.
rewrite<-switch, Heqa0. apply unchange. rewrite<-Heqa0. assumption.
destruct H0. exists x. apply gcd_increase. assumption. assumption.
assert (exists g, is_gcd b' a0 g). apply Ha. assumption.
destruct H0. exists x. apply gcd_symmetry. assumption.
Qed.
Lemma gcd_coef:
forall a b g g' k, is_gcd a b g -> is_gcd (a*k) (b*k) g' -> g'=g*k.
Proof.
destruct k. intro. apply gcd_unique. rewrite ?zero. apply gcd_zero. remember (S k) as h.
intros. assert (h<|g'). apply gcd_greatest with (a*h) (b*h).
exists a. reflexivity. exists b. reflexivity. assumption. destruct H1. rewrite H1 in H0.
rewrite H1. apply mcomplic, gcd_unique with a b. assumption.
inversion H0. apply is_gcd_intro.
apply dsimplif in H2. assumption. rewrite Heqh. apply le_n_S, le_0_n.
apply dsimplif in H3. assumption. rewrite Heqh. apply le_n_S, le_0_n.
intros. apply dsimplif with h. rewrite Heqh. apply le_n_S, le_0_n. apply H4.
apply dcomplic. assumption. apply dcomplic. assumption.
Qed.
Lemma gauss:
forall p a b, is_gcd p a 1 -> p<|(a*b) -> p<|b.
Proof.
intros. assert (exists g, is_gcd (p*b) (a*b) g). apply gcd_exists. destruct H1. inversion H1.
apply gcd_coef with p a 1 x b in H. rewrite uno in H. rewrite<-H. apply H4.
exists b. apply mult. assumption. assumption.
Qed.
Lemma gcd_prime:
forall k p, 0<k -> k<p -> prime p -> is_gcd p k 1.
Proof.
intros. apply is_gcd_intro. exists p. symmetry. apply one. exists k. symmetry. apply one.
destruct p. inversion H0.
intros. destruct H3. destruct x0. rewrite H3 in H. inversion H.
destruct H1 with x. assumption. destruct x0. assert (S p=S p+0). rewrite null. reflexivity.
rewrite H3, H4, uno in H0. apply le_S_n in H0.
rewrite H5, <-null, <-switch in H0. apply le_const in H0. inversion H0.
rewrite H3, H4,<-uno in H0. apply inf, le_coef, le_S_n in H0. inversion H0.
exists 1. rewrite H4. trivial.
Qed.
 
 
(* Combinaison *)
Function combi (k n:nat) {struct n} : nat :=
  match k,n with
  | 0,_ => 1
  | S k',0 => 0
  | S k',S n' => (combi k' n') + (combi (S k') n')
  end.
Lemma indefini:
forall n k, S n <= k -> combi k n = 0.
Proof.
induction n.
intros. inversion H. trivial. trivial.
intros. destruct H.
simpl. rewrite ?IHn. trivial. apply le_S, le_n. apply le_n.
simpl. rewrite ?IHn. trivial. apply le_S, inf. assumption. apply inf. assumption.
Qed.
Lemma rien:
forall n, combi 0 n = 1.
Proof.
induction n. trivial. trivial.
Qed.
Lemma seul:
forall n, combi 1 n = n.
Proof.
induction n. trivial. simpl. rewrite rien, IHn. trivial.
Qed.
Lemma tout:
forall n, combi n n = 1.
Proof.
induction n. trivial.
simpl. rewrite IHn, indefini. trivial. apply le_n.
Qed.
Lemma special:
forall n k, (S k)*combi (S k) (S n) = (S n)*combi k n.
Proof.
induction n. destruct k. trivial. simpl. apply zero.
destruct k. simpl. rewrite rien, seul, one, null. trivial.
remember (S n) as m. remember (S k) as i.
simpl(combi _ _). rewrite assofront. simpl (S i*combi i m). rewrite Heqi. rewrite ?IHn.
rewrite parenth,<-assofront. rewrite Heqm. trivial.
Qed.
Lemma combi_prime:
forall p k, 0<k -> k<p -> prime p -> p <| (combi k p).
Proof.
intros. apply gauss with k. apply gcd_prime. assumption. assumption. assumption.
destruct p. inversion H0. destruct k. inversion H.
rewrite special. exists (combi k p). apply mult.
Qed.
 
 
(* Sommation *)
Function somme (init long:nat) (f:nat -> nat) : nat :=
  match long with
  | 0 => f init
  | S k => (f init) + (somme (S init) k f)
end.
Lemma pop:
forall long f init, somme init (S long) f = somme init long f + f (init+(S long)).
Proof.
induction long. intros. simpl. rewrite s. trivial.
intros. simpl (somme init (S long) f). rewrite parenth, switch,<-IHlong. trivial.
Qed.
Lemma popbis:
forall long f init, somme init (S long) f = f (init+(S long)) + somme init long f.
Proof.
intros. rewrite plus. apply pop.
Qed.
Lemma bottom0:
forall n f, somme 0 (S n) f = somme 1 n f + f 0.
Proof.
intros. simpl. apply plus.
Qed.
Lemma coefsomme:
forall long f a init, a*(somme init long f) = somme init long (fun k => a*(f k)).
Proof.
intros long f a. induction long. trivial.
intros. simpl. rewrite assofront. rewrite IHlong. reflexivity.
Qed.
Lemma eqsomme:
forall (f1 f2:nat -> nat) long init,
(forall k, f1 k = f2 k) -> somme init long f1 = somme init long f2.
Proof.
induction long.
intros. simpl. apply H.
intros. simpl. rewrite IHlong. apply simplif, H. assumption.
Qed.
Lemma indice:
forall (f1 f2:nat -> nat) long init,
(forall k, f1 (S k) = f2 k) -> somme (S init) long f1 = somme init long f2.
Proof.
induction long.
intros. simpl. apply H.
intros. simpl. rewrite IHlong. apply simplif, H. assumption.
Qed.
Lemma merge:
forall (f1 f2:nat -> nat) long init,
somme init long f1 + somme init long f2 = somme init long (fun k => f1 k + f2 k).
Proof.
induction long. trivial.
intros. simpl. rewrite parenth, plus,<-parenth.
symmetry. rewrite parenth, plus. apply simplif. rewrite plus.
symmetry. rewrite plus,<-parenth. apply simplif. rewrite plus. apply IHlong.
Qed.
 
 
(* Binome de newton *)
Lemma newton:
forall a n, (a+1)**n = somme 0 n (fun k => (combi k n)*a**k).
Proof.
induction n. trivial.
simpl ((a + 1) ** _). rewrite IHn. rewrite assoback, uno. rewrite ?coefsomme.
destruct n. simpl. rewrite ?one, null. apply s. remember (S n) as m.
rewrite eqsomme with (fun k=>a*(combi k m*a**k)) (fun k=>combi k m*a**S k) m 0.
rewrite<-indice with (fun k=>combi (k-1) m*a**k) (fun k=>combi k m*a**S k) m 0.
rewrite pop.
rewrite Heqm. rewrite popbis, parenth, plus, ?bottom0, <-Heqm,<-parenth. rewrite merge.
assert(combi 0 m*a**0+combi(1+m-1)m*a**(1+m)=
combi 0(S m)*a**0+combi(0+S m)(S m)*a**(0+S m)).
simpl (0+_). simpl (1+m-1). rewrite minus, ?rien, ?tout. trivial.
rewrite ?parenth, H. apply simplif.
rewrite indice with (fun k=>combi(k-1)m*a**k+combi k m*a**k)
(fun k=>combi k m*a**(S k)+combi(S k)m*a**S k) n 0. symmetry. apply indice.
intros. rewrite<-assoback. trivial.
intros. simpl. rewrite minus. reflexivity.
intros. simpl. rewrite minus. reflexivity.
intros. simpl. rewrite mult. assert (a**k*a=a*a**k). apply mult.
rewrite mparenth, H. reflexivity.
Qed.
Lemma newton_prime:
forall a p n, prime p -> (S n)<p -> p <| (somme 1 n (fun k => (combi k p)*a**k)).
Proof.
intros. induction n. simpl. rewrite seul. exists (a*1). apply mult.
assert (p<|(combi (1+S n) p)). apply combi_prime. apply le_n_S, le_0_n. trivial. assumption.
assert (S(S n)<p). assumption. apply inf, IHn in H2.
destruct H1, H2. rewrite mult in H1. rewrite mult in H2.
rewrite pop, H1, H2, mparenth, <-assofront. exists (x0 + x * a ** (1 + S n)). apply mult.
Qed.
Lemma fermat:
forall a p, prime p -> p <| (a**p-a).
Proof.
destruct p. intros. apply zero_not_prime in H. inversion H.
destruct p. exists (a ** 1 - a). symmetry. apply one.
induction a. exists 0. trivial.
intros. assert (S a**S(S p)=(a+1)**S(S p)). rewrite plus. trivial. rewrite H0. clear H0.
rewrite newton. rewrite bottom0, plus, popbis, <-parenth. simpl (1+_).
remember (S(S p)) as p'. rewrite rien, tout, one, uno. simpl. rewrite plus.
assert (p' <| (somme 1 p (fun k => (combi k p')*a**k))). apply newton_prime.
assumption. rewrite Heqp'. apply le_n.
apply IHa in H. destruct H, H0. rewrite H0. exists (x0+x). rewrite assoback, <-H.
cut (x0* p'+a**p'-a+a=x0*p'+(a**p'-a)+a). apply simplif.
assert (a <= a ** p'). rewrite Heqp'. apply le_pow.
rewrite unchange. rewrite plus. symmetry. rewrite parenth, plus. apply simplif, unchange.
assumption. apply le_transit with (a**p'). assumption. apply le_diff with (x0*p'). apply plus.
Qed.
