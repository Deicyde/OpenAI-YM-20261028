import Mathlib.Analysis.Calculus.Taylor
import YM.Next.RANK.Ray
import YM.Next.RANK.SpectrumReal
import YM.PREC.Derivative



/-! # Build and pay origin Taylor polynomials without changing link norm data

Use only charged cube directions scaled by the *old* threshold t.
On a step of a ray in such directions, the derivatives needed for Taylor
are precisely the single-link-left increment derivatives with that direction,
without lossy BV or smooth-bound replacements. Evaluations of M.pol counted
at this threshold for calibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open RG Lattice Wilson Source Labels MvPolynomial Rise Normal Finset Filter Set Asymptotics
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def act (x : E) := (ContinuousLinearMap.id ℝ ℝ).smulRight x
lemma upon (x : E) (f : E → ℂ) (n : ℕ) (hf : ContDiffAt ℝ n f 0) : iteratedDeriv n (fun t : ℝ => f (t • x)) 0 =
    (iteratedFDeriv ℝ n f 0) (fun _ => x) := by
  let L:= act x
  obtain ⟨r,hr,H⟩ := Metric.mem_nhds_iff.mp (hf.eventually (by simp))
  let B:= Metric.ball (0:E) r
  have ho : IsOpen (L ⁻¹' B) := Metric.isOpen_ball.preimage L.continuous
  have hz : L 0∈B := map_zero L ▸ Metric.mem_ball_self hr
  have h : ContDiffOn ℝ n f B := fun y hy => (show ContDiffAt ℝ n f y from H hy).contDiffWithinAt
  have he := L.iteratedFDerivWithin_comp_right h Metric.isOpen_ball.uniqueDiffOn ho.uniqueDiffOn hz (i:=n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen _ ho (show 0∈L ⁻¹' B from hz),iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hz,map_zero] at he
  change iteratedDeriv n (f ∘ L) 0=_; rw [iteratedDeriv_eq_iteratedFDeriv,he]
  change (iteratedFDeriv ℝ n f 0) (fun _=> (1:ℝ) • x)=_; simp

/-- D reasonably fixed. -/
lemma explicit {V : Type*} [Fintype V] (d : ℕ)
    (M : V → E) (A : E → ℂ) (W : E → V → ℝ) (h : ∀ x : E,x=∑ i,(W x i) • M i)
    (H : ContDiffAt ℝ d A 0) : ∃ P : poly V, totalDegree P≤d ∧ ∀ x : E, ∀ t : ℝ,
      text (fun i => t*(W x i)) P=∑ i ∈ range (d+1), ((i.factorial:ℝ)⁻¹*t^i) • iteratedDeriv i (fun t : ℝ => A (t • x)) 0 := by
  let f (i : ℕ) (p : Fin i → E) := (iteratedFDeriv ℝ i A 0) p
  let F (i : ℕ) := (iteratedFDeriv ℝ i A 0).toMultilinearMap
  let C (i : ℕ) (w : Fin i → V) := (i.factorial:ℝ)⁻¹ • f i (fun j => M (w j))
  let p (i : ℕ) := ∑ w : Fin i → V, MvPolynomial.C (C i w)* ∏ j, MvPolynomial.X (w j)
  let P :=∑ i∈range (d+1),p i
  refine ⟨P,(totalDegree_finsetSum ..).trans (Finset.sup_le ?_),fun x t => ?_⟩
  · intro i hi; apply (totalDegree_finsetSum ..).trans; apply Finset.sup_le; intro w _
    apply (totalDegree_mul ..).trans; rw [totalDegree_C,zero_add]
    apply (totalDegree_finsetProd ..).trans; simp only [totalDegree_X,sum_const, card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    exact Nat.le_of_lt_succ (mem_range.mp hi)
  unfold text P; rw [map_sum]; apply sum_congr rfl; intro i hi
  let b:= (i.factorial:ℝ)⁻¹
  have he : i≤d := Nat.le_of_lt_succ (mem_range.mp hi)
  rw [upon ..]; rotate_left; exact H.of_le (by exact_mod_cast he)
  have ha : f i (fun _=>x) = ∑ w : Fin i→V,(∏ j, W x (w j)) • f i (fun j => M (w j)) := by
    change F i (fun _=>x)=_
    conv_lhs => rw [show (fun _ : Fin i=>x)=(fun _=>∑ j,(W x j) • M j) from funext (fun _ => h x)]
    rw [(F i).map_sum]; apply Finset.sum_congr rfl; intro z _
    exact (F i).map_smul_univ _ _
  dsimp only [p]; rw [map_sum,show (iteratedFDeriv ℝ i A 0) (fun _=>x) = _ from ha, Finset.smul_sum]; apply Finset.sum_congr rfl; intro w _
  simp only [map_mul,aeval_C
           ,Algebra.algebraMap_self,RingHom.id_apply,map_prod,aeval_X,Complex.ofReal_mul,Complex.real_smul,C,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin, Complex.ofReal_prod, Complex.ofReal_inv,Complex.ofReal_pow]; ring

variable {G : Gauge} {n : Side} {b d : ℕ} {o : Site n}

def rollin (p : RG.BudgetPoint) (o : Site n) (b : ℕ) : Space G o b→L[ℝ] Directions G n :=
    let F : Space G o b→ₗ[ℝ] Directions G n := {
      toFun x i := if h : i∈ Room o b then p.threshold • x ⟨i,h⟩ else 0
      map_add' x y := by funext i; dsimp only [Pi.add_apply]; split <;> simp [*]
      map_smul' x y := by funext i; dsimp only [Pi.smul_apply]; split <;> simp only [*,RingHom.id_apply,smul_zero]; exact smul_comm _ _ _ }
    F.toContinuousLinearMap

def net (p : RG.BudgetPoint) (o : Site n) (b) (x : Space G o b) := increment 1 (rollin p o b x)

lemma net_in (p : RG.BudgetPoint) (x : Space G o b) (i : Dim o b) : net p o b x i.val=G.lieExp (p.threshold • x i) := by
  change G.lieExp (if h : i.val∈Room o b then p.threshold • x ⟨_,h⟩ else 0)*1= _; rw [dif_pos i.property,mul_one]
lemma net_out (p : RG.BudgetPoint) (x : Space G o b) (i : Edge (Site n)) (hi : i∉ Room o b) : net p o b x i = 1 := by
  change G.lieExp (if h : i∈ Room o b then p.threshold • x ⟨_,h⟩ else 0)*1=_; rw [dif_neg hi,mul_one,G.mat_lieExp_zero]
lemma encloses (p : RG.BudgetPoint) (x : Space G o b) (h : ‖x‖ ≤ 1) : p.dirBound o (rollin p o b x) := by
  intro i
  have he:= p.threshold_pos; change ‖(if h : i∈Room o b then p.threshold • x _ else 0)‖≤ _
  split
  · rw [norm_smul,Real.norm_of_nonneg he.le]; apply mul_le_mul_of_nonneg_left _ he.le; exact ((pi_norm_le_iff_of_nonneg zero_le_one).1 h _).trans (one_le_pow₀ (by simp))
  rw [norm_zero]; positivity
lemma occupied (p : RG.BudgetPoint) (x : Space G o b) (t : Rules G) (h : ‖x‖≤min t.c (1/8)) : net p o b x ∈ RG.calm G n p.threshold := by
  intro i hi; change G.chord (net p o b x i) ≤ _
  have he := p.threshold_pos
  by_cases hv : i∈Room o b
  · rw [net_in p x (⟨i,hv⟩: Dim o b)]
    let j : Dim o b := ⟨i,hv⟩
    obtain ⟨h₁,h₂⟩ := le_min_iff.mp ((norm_le_pi_norm x j).trans h)
    have hx : ‖p.threshold • x j‖ ≤ t.c := by rw [norm_smul,Real.norm_of_nonneg he.le]; exact (mul_le_of_le_one_left (norm_nonneg _) p.threshold_le).trans h₁
    refine (t.light _ hx).trans ?_
    rw [norm_smul,Real.norm_of_nonneg he.le]; linarith only [mul_le_mul_of_nonneg_left h₂ he.le]
  rw [net_out _ x i hv,G.chord_one]; positivity

section derivative
variable {X : Support n} {F : Config G n → ℂ} {p : RG.BudgetPoint}

lemma together (A : G.Color) (s t : ℝ) : G.lieExp ((s+t) • A)= G.lieExp (t • A) * G.lieExp (s • A) := by
  apply G.mat_injective; rw [G.mat_lieExp,G.mat_mul,G.mat_lieExp,G.mat_lieExp, map_smul,map_smul,map_smul,add_comm s t, add_smul]; apply NormedSpace.exp_add_of_commute
  exact ((Commute.refl _).smul_right s).smul_left t

lemma progress (U : Config G n) (A : Directions G n) (s t : ℝ) : increment U ((s+t) • A)=increment (increment U (s • A)) (t • A) := by
  ext1 i; simp only [increment,Pi.smul_apply,together,mul_assoc]
lemma repeated (p : BudgetPoint) (o : Site n) (x : Space G o b) (s t : ℝ) : net p o b ((s+t) • x) = increment (net p o b (s • x)) (t • rollin p o b x) := by
  rw [net,net,map_smul,map_smul, progress]
lemma net_metric (t : ℝ) (s : Space G o b) (n : ℕ) : iteratedDeriv n (fun t : ℝ => F (net p o b (t • s))) t = leftDerivs F (List.replicate n (rollin p o b s)) (net p o b (t • s)) := by
  let f := fun t : ℝ => F (net p o b (t • s))
  induction n generalizing t with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ n H =>
    change iteratedDeriv _ f t= _; rw [iteratedDeriv_succ,List.replicate_succ,leftDerivs]; symm
    have hp (x : ℝ) : leftDerivs F (List.replicate n (rollin p o b s)) (increment (net p o b (t • s)) (x • rollin p o b s)) = iteratedDeriv n f (t+x) := by rw [← repeated, ← H]
    rw [funext hp, deriv_comp_const_add,add_zero]
lemma net_diff {s : ℝ} {x : Space G o b} (H : p.Regular X F) (h : Healthy p.threshold X (net p o b (s • x))) {m : ℕ} (hp : m ≤ p.order) :
    ContDiffAt ℝ m (fun t : ℝ => F (net p o b (t • x))) s := by
  let g:= Function.comp F (fun i => increment (net p o b (s • x)) i)
  let W := fun y : ℝ => (y-s) • rollin p o b x
  have he : g∘W=(fun t : ℝ => F (net p o b (t • x))) := by
    funext t; dsimp only [Function.comp_apply,g,W]; rw [← repeated,add_sub_cancel]
  have hA : W s=0 := by simp [W]
  rw [← he]; apply ContDiffAt.comp _ _ (show ContDiffAt ℝ m W s from ?_)
  · exact hA ▸ (H.smooth _ h).of_le (by exact_mod_cast hp)
  unfold W; fun_prop

abbrev links (G : Gauge) {n : Side} (o : Site n) (b : ℕ) := Dim o b × G.ColorIndex

def scan (x : Space G o b) (y : links G o b) : ℝ := x y.1 y.2
def report (y : links G o b) : Space G o b := Pi.single y.1 (EuclideanSpace.single y.2 1)
lemma marked_sum (x : Space G o b) : x=∑ i, scan x i • report i := by
  rw [Fintype.sum_prod_type]; funext i; apply PiLp.ext; intro j; simp [scan,report,Pi.single_apply]

private lemma cultivate (d : ℕ) (A : Config G n→ ℂ) (X : Support n) (p : RG.BudgetPoint) (hb : d≤p.order) (h : p.Regular X A) :
    ∃ P : poly (links G o b), totalDegree P≤d ∧ ∀ x : Space G o b, ∀ t : ℝ,text (fun i => t* scan x i) P=
    ∑ i∈range (d+1), ((i.factorial:ℝ)⁻¹*t^i) • iteratedDeriv i (fun t : ℝ => A (net p o b (t • x))) 0 := by
  apply explicit d (A:=fun x => A (net p o b x)) (W:=scan) report marked_sum
  have hg : flags p.threshold (1:Config G n)=∅ := voids (show (1:Config G n) ∈ calm G n p.threshold from fun i _ => (by change G.chord 1≤_; rw [G.chord_one]; have ht:= p.threshold_pos; positivity)) le_rfl
  have hd : Healthy p.threshold X (1:Config G n) := by simp [Healthy,hg]
  apply (show ContDiffAt ℝ d (fun x => A (increment 1 x)) (rollin p o b (0 : Space G o b)) from (rollin _ _ _).map_zero ▸ (h.smooth 1 hd).of_le (by exact_mod_cast hb)).comp
    (0 : Space G o b) (rollin p o b).contDiff.contDiffAt

lemma reads_back (y : links G o b → ℝ) (r : ℝ) (hr : 0≤r) (hx : ∀ i,|y i| ≤ r) :
    ∃ x : Space G o b, scan x=y ∧ ‖x‖ ≤ (Fintype.card G.ColorIndex)*r := by
  let x : Space G o b := fun i => WithLp.toLp 2 fun j => y (i,j)
  refine ⟨x,rfl, (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_⟩
  let F (j : G.ColorIndex) := EuclideanSpace.single j (y (i,j)); have he : x i= ∑ i,F i := by apply PiLp.ext; intro j; simp [F,x]
  rw [he]; apply (norm_sum_le ..).trans
  rw [show (Fintype.card G.ColorIndex:ℝ)*r=∑ _ : G.ColorIndex,r by simp]; refine sum_le_sum fun j _ => ?_
  simpa only [F,EuclideanSpace.single,PiLp.norm_single, Real.norm_eq_abs] using hx (i,j)

@[simp] lemma scan_smul (x : Space G o b) (q : ℝ) : scan (q • x)=fun i => q*scan x i := rfl

def pane (S : Rules G) := min S.c (1/8)
lemma pane_pos (S : Rules G) : 0 < pane S := lt_min S.radius (by norm_num)
lemma pane_le (S : Rules G) : pane S≤ 1/8 := min_le_right ..

private lemma ray_bound {o : Site n} {b : ℕ} {X : Support n} {A : Config G n → ℂ} {p : RG.BudgetPoint} (S : Rules G) (x : Space G o b) (hx : ‖x‖≤1) (r : ℝ) (hr : r ∈ Set.Icc 0 (pane S)) {c : ℝ}
    (h : p.supBounds o X A c) {k : ℕ} (hk : k ≤ p.order) (P : p.Regular X A) :
    ContDiffAt ℝ k (fun t : ℝ => A (net p o b (t • x))) r ∧
      ‖iteratedDeriv k (fun t : ℝ => A (net p o b (t • x))) r‖≤c := by
  have hg : ‖r • x‖≤pane S := by rw [norm_smul,Real.norm_of_nonneg hr.1]; exact (mul_le_of_le_one_right hr.1 hx).trans hr.2
  have hv : Healthy p.threshold X (net p o b (r • x)) := by simp only [Healthy,voids (occupied p _ S hg) le_rfl,Finset.disjoint_empty_right]
  refine ⟨net_diff P hv hk,?_⟩; rw [net_metric]; apply h.2 _ hv _ (by simpa using hk); intro i hi
  rw [(List.eq_of_mem_replicate hi)]; exact encloses p x hx

lemma minted (S : Rules G) (d : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ (n : Side) (o : Site n) (b : ℕ) (X : Support n) (A : Config G n → ℂ)
    (p : RG.BudgetPoint), d+1≤p.order → p.Regular X A → ∀ c : ℝ, p.supBounds o X A c → ∃ P : poly (links G o b),
      totalDegree P≤d ∧ coin P ≤ c * ((Fintype.card (links G o b):ℝ)+1)^d*C ∧
        (∀ x : Space G o b, ∀ t : ℝ, text (scan (t • x)) P=∑ i∈range (d+1), ((i.factorial:ℝ)⁻¹*t^i) • iteratedDeriv i (fun t : ℝ => A (net p o b (t • x))) 0) ∧
          ∀ x : Space G o b, ‖x‖≤pane S→ ‖A (net p o b x)-text (scan x) P‖ ≤ c * ‖x‖^(d+1) := by
  let e := Fintype.card G.ColorIndex
  obtain ⟨C,hC,H⟩ := ball_count d ((1+e:ℝ)⁻¹) (by positivity)
  refine ⟨C*(d+1:ℝ),by positivity,fun n o b X A p hb ha c hc => ?_⟩
  have hd := hc.1; obtain ⟨P,hp,h⟩ := cultivate (o:=o) (b:=b) d A X p (by omega) ha
  have hz := pane_pos S
  refine ⟨P,hp, ?_,h,fun x hx => ?_⟩
  · refine le_trans (H (links G o b) P hp ((d+1:ℝ)*c) (by positivity) fun t ht => ?_) (le_of_eq (by ring))
    obtain ⟨x,hF,hx⟩ := reads_back t _ (by positivity) ht
    have hs : ‖x‖≤1 := hx.trans (show (e:ℝ)*_≤1 by rw [← div_eq_mul_inv]; apply div_le_one_of_le₀ _ (by positivity); linarith only)
    rw [← hF,show scan x=(fun i => (1:ℝ)*scan x i) from funext (fun i => (one_mul _).symm),h]
    apply (norm_sum_le ..).trans; rw [show (d+1:ℝ)*c=∑ i∈range (d+1), c by simp]; refine sum_le_sum fun i hi => ?_; rw [one_pow, mul_one,norm_smul]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
    · exact (ray_bound S x hs 0 ⟨le_rfl,hz.le⟩ hc ((Nat.le_of_lt (mem_range.mp hi)).trans hb) ha).2
    rw [norm_inv,Real.norm_natCast]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (i.factorial_pos))
  let v:= ‖x‖; let y:= v⁻¹ • x; have hv : v∈ Set.Icc 0 (pane S) := ⟨norm_nonneg _,hx⟩
  have he : x=v • y ∧ ‖y‖ ≤ 1 := by
    rcases eq_or_ne x 0 with hh|hh
    · subst x; simp [y]
    have hx : 0<v := norm_pos_iff.mpr hh; unfold y
    rw [smul_smul,mul_inv_cancel₀ hx.ne',one_smul,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hx).le,show ‖x‖=v from rfl,inv_mul_cancel₀ hx.ne']
    exact ⟨rfl,le_rfl⟩
  let f := fun t : ℝ => A (net p o b (t • y));let B:=Set.Icc (0:ℝ) (pane S)
  have hf (i j) (hp : i∈B) (he' : j≤p.order) := ray_bound S y he.2 i hp hc he' ha
  have h0 : 0∈B := ⟨le_rfl,hz.le⟩
  have hg (z i) (hp : z∈B) (hi : i≤p.order) : iteratedDerivWithin i f B z=iteratedDeriv i f z := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hz) (hf z i hp hi).1 hp
  have ht := taylor_mean_remainder_bound (n:=d) (f:=f) hz.le (fun i hi => ContDiffWithinAt.of_le (hf i (d+1) hi hb).1.contDiffWithinAt (by simp)) hv (C:=c)
    fun q h => (by rw [hg _ _ h hb]; exact (hf q _ h hb).2)
  have hy : text (scan x) P=taylorWithinEval f d B 0 v := by
    rw [he.1,scan_smul,show text _ P= _ from h y v,taylor_within_apply]; refine sum_congr rfl fun i hi => ?_
    rw [sub_zero,hg _ _ h0 ((Nat.le_of_lt (mem_range.mp hi)).trans hb)]
  rw [hy, show A (net p o b x)=f v from congr_arg (fun u => A (net p o b u)) he.1]
  rw [sub_zero] at ht
  exact ht.trans (div_le_self (by positivity) (by exact_mod_cast d.factorial_pos))
end derivative
end YM.Next.Rank.Spindle
