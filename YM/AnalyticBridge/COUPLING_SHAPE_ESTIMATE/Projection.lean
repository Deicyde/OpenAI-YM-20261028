import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Plane

/-! # The subtracted affine-curl form really uses the normalized directions

Pay one flat exposure from each old E; no division by the size of an actual tested curl,
which can vanish. In particular, no positivity assumption on the bilinear form.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice Wilson RG ProjectorNext.Equivariance
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {o : Site n} {p : BudgetPoint} {X : Support n} {f : Config G n → ℝ}

abbrev Form (G : Gauge) := Flux G →L[ℝ] Flux G →L[ℝ] ℝ

def entire (f : Config G n→ℝ) (o : Site n) : Form G := (((H f ∘L rise G o).flip) ∘L rise G o).flip

open scoped Classical in
def stripJet (f : Config G n→ℝ) (o : Site n) (X : Support n) : Form G := if Nonwrapping X o then entire f o else 0

lemma strip_on (hx : Nonwrapping X o) (A B) : stripJet f o X A B=H f (rise G o A) (rise G o B) := by
  rw [stripJet,if_pos hx]; rfl

lemma strip_affine (hn : 2≤n.val) (hx : Nonwrapping X o) (hs : G.Simple) (h : p.Regular X f)
    {A B : Directions G n} {c d e u} (hA : OnStencil o X c d A) (hB : OnStencil o X e u B) :
    H f A B=stripJet f o X (skew d) (skew u) := by
  rw [via_skew hs hn hx hA h,symmetric h,via_skew hs hn hx hB h,symmetric h,strip_on hx]

lemma strip_symm (h : p.Regular X f) (o) (A B) : stripJet f o X A B=stripJet f o X B A := by
  unfold stripJet; split_ifs
  · exact symmetric h _ _
  simp

def dye (u : G.El) (v : Flux G) : Flux G := fun i => G.adjoint u (v i)
private lemma rise_colored (u : G.El) (v : Flux G) (o : Site n) : rise G o (dye u v)=globalAd u (rise G o v) := by
  funext i; simp only [rise_apply,slide,globalAd,map_sum,map_zsmul]; apply Finset.sum_congr rfl; intro j _; by_cases h : j < i.2 <;> simp [h,dye,lower]

lemma strip_color (hs : G.Simple) (h : p.Regular X f) (u : G.El) (o : Site n) (A B) :
    stripJet f o X (dye u A) (dye u B)=stripJet f o X A B := by
  by_cases hh : Nonwrapping X o
  · rw [strip_on hh,strip_on hh, rise_colored,rise_colored]
    have he (v : Directions G n) : H f (globalAd u v) (globalAd u v)=H f v v := by
      rw [diagonal hs h, diagonal hs h]; simp_rw [overall, fun t : ℝ => h.symmetry (fun _ => u) (increment 1 (t • v))]
    let a:=rise G o A; let b:=rise G o B
    have ht := he (a+b); rw [show globalAd u (a+b)=globalAd u a+globalAd u b by ext1; simp [globalAd],polar h, he, he,polar h] at ht
    change H f (globalAd u a) (globalAd u b)=H f a b; linarith
  simp [stripJet,hh]

private lemma dyadic (A : Directions G n) (s t : ℝ) :
    increment (increment 1 (t • A)) (s • A) = increment 1 ((s+t) • A) := by
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  ext1 i
  apply G.mat_injective
  simp only [increment,Pi.smul_apply,Pi.one_apply,mul_one, G.mat_mul,G.mat_lieExp,add_smul,map_add,map_smul]
  exact (NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat (A i))).smul_left s).smul_right t)).symm

lemma left_quote (hs : G.Simple) (h : p.Regular X f) (A : Directions G n) : H f A A=leftDerivs f [A,A] 1 := by
  let F := fun t : ℝ => f (increment 1 (t • A))
  have he (t : ℝ) : leftDerivs f [A] (increment 1 (t • A)) = deriv F t := by
    change deriv (fun s : ℝ => f (increment (increment 1 _) (s • A))) 0 = _
    simp_rw [dyadic]; simpa only [zero_add] using deriv_comp_add_const F t (0:ℝ)
  rw [diagonal hs h]; change iteratedDeriv (1+1) F 0=deriv _ 0
  simp_rw [he]; rw [iteratedDeriv_succ]; simp [iteratedDeriv_one]

lemma rise_size (w : Flux G) (e : Edge (Site n)) (o) : ‖rise G o w e‖ ≤ (4*(separation e.1 o):ℝ)*‖w‖ := by
  rw [rise_apply,slide]; apply (norm_sum_le ..).trans
  have hv (i) : ‖lower w e.2 i‖ ≤ ‖w‖ := by
    unfold lower; split
    · exact norm_le_pi_norm ..
    simp
  have he (i:Axis) : ‖lift (e.1-o) i • lower w e.2 i‖ ≤ (separation e.1 o : ℝ)*‖w‖ := by
    rw [← Int.cast_smul_eq_zsmul ℝ,norm_smul,Real.norm_eq_abs,← Int.cast_abs,← Nat.cast_natAbs]
    exact mul_le_mul (by exact_mod_cast component_le (e.1-o) i) (hv i) (norm_nonneg _) (by positivity)
  apply (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => he i)).trans; simp [Axis,mul_assoc]

lemma charges_rise (p : BudgetPoint) (w : Flux G) (o : Site n) (hw : ‖w‖ ≤ 2) :
    p.dirBound o ((p.threshold / 8) • rise G o w) := by
  intro e; rw [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg p.threshold_pos.le (by norm_num))]
  refine (mul_le_mul_of_nonneg_left (rise_size w e o) (by positivity [p.threshold_pos])).trans ?_
  let d : ℝ := separation e.1 o
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hc : 1 ≤ p.power := (by have H:=p.power_ge; omega)
  have hk : d ≤ (1+d)^p.power := by
    have hj := pow_le_pow_right₀ (show 1 ≤ 1+d by linarith) hc; rw [pow_one] at hj; linarith
  change _ ≤ p.threshold * (1+d)^p.power
  apply le_trans _ (mul_le_mul_of_nonneg_left hk p.threshold_pos.le)
  change p.threshold/8*(4*d*_) ≤ _
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by positivity : 0≤4*d)) (by positivity [p.threshold_pos] : 0≤p.threshold/8)).trans
  apply le_of_eq; ring

lemma strip_bill (hs : G.Simple) (h : p.Regular X f) (o : Site n) {a : ℝ} (hh : p.supBounds o X f a) :
    ‖stripJet f o X‖ ≤ 96 / p.threshold^2 * a := by
  have ha:= hh.1; have ht:=p.threshold_pos
  by_cases hv : Nonwrapping X o
  · have hn : 0 ≤ 96/p.threshold^2*a := by positivity
    refine ContinuousLinearMap.opNorm_le_of_unit_norm hn fun x hx => ContinuousLinearMap.opNorm_le_of_unit_norm hn fun y hy => ?_
    rw [Real.norm_eq_abs,strip_on hv]
    let t:=p.threshold
    let A : ℝ := 64/t^2*a
    have he (w : Flux G) (hp : ‖w‖ ≤ 2) : |H f (rise G o w) (rise G o w)| ≤ A := by
      let e:=rise G o w; let B:=(t/8) • e
      have hl := hh.2 1 (clear_one p X) [B,B] (by have:=p.order_ge; simpa using Nat.le_trans (by decide : 2 ≤ 6) p.order_ge)
        (by simpa using! charges_rise p w o hp)
      rw [← left_quote hs h, Real.norm_eq_abs] at hl
      dsimp only [B] at hl
      simp only [map_smul, smul_apply,smul_eq_mul, abs_mul, abs_of_nonneg (show 0 ≤ t/8 from div_nonneg ht.le (by norm_num))] at hl
      unfold A; rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos ht)]; change |H f e e| * t^2 ≤ _; linarith
    have hp : ‖x+y‖ ≤ 2 := (norm_add_le x y).trans (by rw [hx,hy]; norm_num)
    have hxy := he (x+y) hp; rw [map_add,polar h] at hxy
    obtain ⟨h1,h2⟩:=abs_le.mp hxy
    obtain ⟨h3,h4⟩:=abs_le.mp (he x (by linarith))
    obtain ⟨h5,h6⟩:=abs_le.mp (he y (by linarith))
    have h₀ : 3*A=2*(96/p.threshold^2*a) := by unfold A t; ring
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [stripJet, if_neg hv, show ‖(0 : Form G)‖ = 0 from @norm_zero (Form G) _]; positivity

end YM.AnalyticBridge.CouplingShape
