import YM.Next.RANK.Ample

/-!
# Capital of one polynomial step
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Lattice Wilson RG Marker Rise Normal MvPolynomial Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {S T U V Z : Type*}

structure Valve (S T : Type*) where
  H : S → T →₀ ℂ
  Q : Normal.Symmetric S

def Valve.read (R : Valve S T) := Normal.pipe R.H R.Q

structure Valve.Fair (R : Valve S T) (C : ℝ) : Prop where
  positive : 1≤C
  charge i : coin (glyph (R.H i)) ≤ C
  tide i j : ‖R.Q.cov i j‖ ≤ C
structure Awake (R R' : Valve S T) (C ε : ℝ) : Prop where
  pay : R.Fair C
  cut : R'.Fair C
  epsilon : 0 ≤ ε
  path i : coin (glyph (R.H i)-glyph (R'.H i)) ≤ ε
  covariance i j : ‖R.Q.cov i j - R'.Q.cov i j‖ ≤ ε

variable {R R' : Valve S T} {C E : ℝ}
private lemma inducts (F : Valve S T) (f : U → S) [DecidableEq U] (s : Finset U) (i : U) (h : i∉s) : F.read (glyphs f (insert i s))=
    glyph (F.H (f i))* F.read (glyphs f s) + ∑ j∈s,F.Q.cov (f i) (f j) • F.read (glyphs f (s.erase j)) := by
  rw [Valve.read,pipes, show glyphs f (insert i s)=X _*glyphs f s from prod_insert h, feeds, skims, renew, map_sum,_root_.map_add,map_mul,map_sum,exchange_x]; simp_rw [map_smul]; rfl

private def C₀ (c : ℝ) (i : ℕ) := 2*(i+2)*c
def crest (c : ℝ) (i : ℕ) := C₀ c i ^ i
lemma pay_crest {c : ℝ} (h : 1 ≤ c) (i) : 1 ≤ crest c i := one_le_pow₀ (by dsimp only [C₀]; nlinarith [Nat.cast_nonneg (α:=ℝ) i])

private lemma total (A : Valve S T) (h : A.Fair C) {V : Type*} [DecidableEq V] (p : V → S) (D d : ℕ) (he : d ≤ D) (s : Finset V) (hs : s.card ≤ d) :
    coin (A.read (glyphs p s)) ≤ C₀ C D ^ d ∧ (A.read (glyphs p s)).totalDegree ≤ d := by
  let x := C₀ C D
  have hp := h.positive; have hz : 1 ≤ C₀ C D := by unfold C₀; nlinarith
  induction d generalizing s with
  | zero=> obtain rfl:= card_eq_zero.mp (show s.card=0 by omega); simp only [Valve.read,pipes,glyphs,prod_empty,Normal.pure, _root_.map_one, coin,pay_one,totalDegree_one,pow_zero,le_refl,and_self]
  | succ d ih=>
    obtain rfl|⟨j,hj⟩:= s.eq_empty_or_nonempty
    · refine ⟨?_,?_⟩ <;> simp only [Valve.read,pipes,glyphs,prod_empty,Normal.pure,map_one,coin,pay_one,totalDegree_one]
      · exact one_le_pow₀ hz
      exact Nat.zero_le _
    let a:= s.erase j
    have ha : a.card≤d := by dsimp [a]; rw [card_erase_of_mem hj]; omega
    have he (q) (h:q⊆a) := ih (Nat.le_trans (Nat.le_succ d) he) q ((card_le_card h).trans ha)
    let v:= glyph (A.H (p j))
    have hf : v.totalDegree ≤ 1 := by simpa only [Normal.exchange_x,MvPolynomial.totalDegree_X] using ascent A.H (X (p j))
    let L:= A.read (glyphs p a)
    have hx (b : ℕ) : 0≤ x^b := pow_nonneg (zero_le_one.trans hz) _
    rw [show s=insert j a from (insert_erase hj).symm, inducts _ p _ _ (notMem_erase j s)]
    constructor
    · apply (taller _ zero_le_one ..).trans (le_trans (b:= C*x^d+(D:ℝ)*(C*x^d)) ?_ ?_)
      · apply add_le_add (le_trans (funds _ zero_le_one ..) (mul_le_mul (h.charge _) (he a le_rfl).1 (Rise.sign _ _ zero_le_one) (zero_le_one.trans hp)))
        apply (Rise.collect _ zero_le_one ..).trans
        calc
          _ ≤ ∑ _∈a,C*x^d:= sum_le_sum fun i _=> (LiftMark.peak_cost _ _ _ _ zero_le_one).trans (mul_le_mul (h.tide ..) (he _ (erase_subset i a)).1 (Rise.sign _ _ zero_le_one) (zero_le_one.trans hp))
          _ ≤ _:= by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (ha.trans (by omega))) (mul_nonneg (zero_le_one.trans hp) (hx _))
      change _≤ x^(d+1); rw [pow_succ]; dsimp only [x,C₀]; unfold x C₀ at hx
      nlinarith only [mul_nonneg (mul_nonneg (zero_le_one.trans hp) (hx d)) (Nat.cast_nonneg D),mul_nonneg (zero_le_one.trans hp) (hx d)]
    apply (totalDegree_add ..).trans; apply max_le
    · exact (totalDegree_mul ..).trans ((add_le_add hf (he _ le_rfl).2).trans (by omega))
    apply (totalDegree_finsetSum ..).trans; exact Finset.sup_le fun i _ => (totalDegree_smul_le ..).trans ((he _ (erase_subset i a)).2.trans (Nat.le_succ d))

lemma tricolor (p q : poly V) : coin (p-q) ≤ coin p+coin q := by
  rw [sub_eq_add_neg,show -q=(-1:ℂ)•q by simp]
  apply (taller _ zero_le_one ..).trans
  gcongr
  exact (LiftMark.peak_cost 1 0 (-1:ℂ) q zero_le_one).trans_eq (by simp)
lemma minus_mul {p q r t : poly V} (p' r' δ δ' : ℝ) (h : coin (p-q) ≤ δ) (he : coin (r-t) ≤ δ') (hx : coin p ≤ p') (hy : coin t ≤ r') :
    coin (p*r-q*t) ≤ p'*δ' + δ*r' := by
  rw [show p*r-q*t=p*(r-t)+(p-q)*t by ring]
  refine (taller _ zero_le_one ..).trans (add_le_add ((funds _ zero_le_one ..).trans ?_) ((funds _ zero_le_one ..).trans ?_))
  · exact mul_le_mul hx he (Rise.sign _ _ zero_le_one) ((Rise.sign _ _ zero_le_one).trans hx)
  exact mul_le_mul h hy (Rise.sign _ _ zero_le_one) ((Rise.sign _ _ zero_le_one).trans h)
lemma minus_scale (u v : ℂ) (a b : poly V) {c δ ε e : ℝ} (h : ‖u‖ ≤ c) (he : ‖u-v‖≤ ε) (hf : coin b≤ δ) (hp : coin (a-b) ≤ e) :
    coin (u•a-v•b) ≤ c*e+ε*δ := by
  rw [show u•a-v•b=u•(a-b)+(u-v)•b by rw [smul_sub,sub_smul]; abel]
  exact (taller _ zero_le_one ..).trans (add_le_add (le_trans (LiftMark.peak_cost _ _ _ _ zero_le_one) (mul_le_mul h hp (Rise.sign _ _ zero_le_one) ((norm_nonneg _).trans h)))
    (le_trans (LiftMark.peak_cost _ _ _ _ zero_le_one) (mul_le_mul he hf (Rise.sign _ _ zero_le_one) ((norm_nonneg _).trans he))))

private lemma fray (h : Awake R R' C E) [DecidableEq U] (p : U→S) (s : Finset U) (d D : ℕ) (hp : s.card ≤ d) (hi : d ≤ D) :
    coin (R.read (glyphs p s)-R'.read (glyphs p s)) ≤ E*C₀ C D ^d:= by
  let x:= C₀ C D
  have hx:=h.pay.positive; have hX : 1≤ x:= by unfold x C₀; nlinarith
  have hz : 0≤E:= h.epsilon
  induction d generalizing s with
  | zero=> obtain rfl:= card_eq_zero.mp (show s.card=0 by omega); simpa only [Valve.read,pipes,glyphs,prod_empty,Normal.pure,map_one,sub_self,coin,pay_nothing,pow_zero,mul_one] using hz
  | succ d ih=>
    obtain rfl|⟨j,hj⟩:= s.eq_empty_or_nonempty
    · simp only [Valve.read,pipes,glyphs,prod_empty,Normal.pure,map_one,sub_self,coin,pay_nothing]; exact mul_nonneg hz (pow_nonneg (zero_le_one.trans hX) _)
    let a:= s.erase j
    have ha : a.card≤d := by dsimp only [a]; rw [card_erase_of_mem hj]; omega
    have h1 : d≤D := by omega
    have he (i) (hv : i⊆a):= ih i ((card_le_card hv).trans ha) h1
    have h2 (i) (hv:i⊆a) := (total _ h.cut p D d h1 i ((card_le_card hv).trans ha)).1
    let v:= E*x^d;have hv : 0 ≤ v:= mul_nonneg hz (pow_nonneg (zero_le_one.trans hX) d)
    have hx':0 ≤ C*v:= mul_nonneg (zero_le_one.trans hx) hv
    rw [show s=insert j a from (insert_erase hj).symm,inducts _ p _ _ (notMem_erase j s),inducts _ p _ _ (notMem_erase j s),add_sub_add_comm,← Finset.sum_sub_distrib]
    apply (taller _ zero_le_one ..).trans
    apply le_trans (b:= (C*v+v)+(D:ℝ)*(C*v+v))
    · apply add_le_add (minus_mul _ _ _ _ (h.path _) (he a le_rfl) (h.pay.charge _) (h2 a le_rfl)); apply (Rise.collect _ zero_le_one ..).trans
      apply le_trans (b:=∑ _∈a,(C*v+v)) (sum_le_sum (fun i _ => minus_scale _ _ _ _ (h.pay.tide ..) (h.covariance ..) (h2 _ (erase_subset i a)) (he _ (erase_subset i a))))
      rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast ha.trans h1) (add_nonneg hx' hv)
    change _ ≤ E*x^(d+1); rw [pow_succ,← mul_assoc E (x^d)]; have hh : v ≤ C*v:= le_mul_of_one_le_left hv hx
    change _ ≤ v * x; unfold x C₀; nlinarith only [hh,mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) D),hx']

lemma paid_L (L : poly S →ₗ[ℂ] poly T) (p : poly S) {c : ℝ} (h : ∀ i∈p.support, coin (L (monomial i 1)) ≤ c) : coin (L p) ≤ coin p*c:= by
  nth_rw 1 [MvPolynomial.as_sum p]; rw [map_sum,metal p,Finset.sum_mul]
  apply (Rise.collect _ zero_le_one ..).trans; apply sum_le_sum; intro i hi
  let z := coeff i p; rw [show monomial i (coeff i p)= z • monomial i 1 by rw [← map_smul,smul_eq_mul,mul_one],map_smul (f:=L)]; exact (LiftMark.peak_cost _ _ _ _ zero_le_one).trans (mul_le_mul_of_nonneg_left (h i hi) (norm_nonneg z))
lemma crux (h : R.Fair C) (p : poly S) (d : ℕ) (hv : p.totalDegree ≤ d) : coin (R.read p) ≤ coin p*crest C d ∧ totalDegree (R.read p)≤d:= by
  have ht i (hi : i∈p.support) : coin (R.read (monomial i 1))≤ crest C d ∧ totalDegree (R.read (monomial i 1)) ≤ d := by
    obtain ⟨v,hv'⟩:= Common.letter i; rw [hv']; exact total R h v d d le_rfl _ (by simpa using (le_totalDegree hi).trans hv)
  refine ⟨paid_L _ _ fun i hi=> (ht i hi).1, ?_⟩
  nth_rw 1 [p.as_sum]; rw [map_sum]; apply (totalDegree_finsetSum ..).trans; apply Finset.sup_le; intro i hi
  rw [show monomial i (coeff i p)=coeff i p • monomial i 1 by rw [← map_smul,smul_eq_mul,mul_one], map_smul (f:=R.read)]; exact (totalDegree_smul_le ..).trans (ht i hi).2
lemma crossing (h : Awake R R' C E) (p : poly S) (d : ℕ) (H : p.totalDegree≤d) : coin (R.read p-R'.read p)≤ coin p*(E*crest C d):= by
  refine paid_L (R.read-R'.read) p fun i hi=> ?_; obtain ⟨v,hv⟩:= Common.letter i; rw [hv]; exact fray h v _ d d (by simpa using (le_totalDegree hi).trans H) le_rfl
end YM.Next.Rank.Tapes
