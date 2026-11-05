import YM.Next.MAXWELL.Triangle

/-! # Real scaling at the triangular collision -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {j l d : ℕ}

lemma cell_test (p : Flavor 0) (i l : Axis) (c : G.ColorIndex) {z} (hz : z≠0) : fare c p (cell i l) z =
    4*normal*(‖z‖^2)⁻¹^2 * p (solutionTurn (house z) (blade i l (1:ℝ))) := by
  let P := flavor 0 c p
  rw [show fare c p (cell i l) z=K P (omegaLeg c i l) z 0 by rw [K,sub_zero]; rfl, probe_formula _ _ _ _ hz,sub_zero]
  congr 1; apply congr_arg p
  apply Subtype.ext; funext a b; apply ContinuousMultilinearMap.ext; intro v
  change cp (G:=G) c ((solutionTurn (house z) (blade _ _ _)).val a b v) = _
  change cp _ ((solutionTurn (house z) (blade _ _ _)).val a b v) = (solutionTurn (house z) (blade _ _ _)).val a b v
  simp only [blade_rot,map_smul, smul_eq_mul,mul_one];
  change _*unitColor G c c=_; simp only [unitPaint,↓reduceIte,mul_one]

lemma cell_change (x : Sheet 0) (a b : Axis) : cell a b x= -cell b a x := (wavePoly x).form _ _ 0 (mem_univ 0)

lemma stock_floor (q : Sheet 0) : q=∑ i : Axis, ∑ j : Axis, (1/2*cell i j q) • blade i j (1:ℝ) := by
  apply flavor_ext; intro u a b
  have ht : stay u a b=cell a b := congr_arg (fun u => stay (j:=0) u a b) (Subsingleton.elim ..)
  rw [ht]; simp only [map_sum,map_smul,cell_price,mul_one,wedge,smul_eq_mul]
  simp [Matrix.one_apply,mul_ite,mul_sub,Finset.sum_sub_distrib];
  nth_rw 3 [cell_change]; ring

lemma point_fares (c : G.ColorIndex) (X : Sheet 0) {z : E4} (hz : z ≠ 0) : ∃ w : Flavor 0,∀ q, fare c q w z=q X := by
  let s := house z
  let W := solutionTurn s⁻¹ X
  have ht : X=solutionTurn s W := by unfold W; rw [← solution_rep,mul_inv_cancel,solution_id]
  let k := 4*normal*(‖z‖^2)⁻¹^2
  have hK : k ≠ 0 := by
    have h := norm_pos_iff.mpr hz
    unfold k normal; positivity
  refine ⟨k⁻¹ • ∑ a : Axis, ∑ b : Axis, (1/2*cell a b W) • cell a b, fun q => ?_⟩
  rw [← fare_pair c q _ hz,map_smul]; simp_rw [map_sum,map_smul,fare_pair c q _ hz,cell_test q _ _ c hz,smul_eq_mul]
  conv_rhs => rw [ht]; arg 2; rw [stock_floor W]
  simp only [map_sum,map_smul,smul_eq_mul, Finset.mul_sum];
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  change k⁻¹*(_*(k*q _))=_
  field_simp; rfl

lemma upside_one (p : Probe G 1) : probeTurn oppositeFrame.ortho p = -p := by
  ext x; change p (solutionTurn oppositeFrame.ortho⁻¹ _) = _
  rw [show oppositeFrame.ortho⁻¹ = oppositeFrame.ortho from (map_inv Signed.inclusionO _).symm,upside_form,map_smul]; simp
lemma upside_zero (p : Probe G 0) : probeTurn oppositeFrame.ortho p=p := by
  ext x; change p (solutionTurn oppositeFrame.ortho⁻¹ _) = _
  rw [show oppositeFrame.ortho⁻¹ = oppositeFrame.ortho from (map_inv Signed.inclusionO _).symm,upside_form]; simp
lemma fare_sign (c : G.ColorIndex) (v : Flavor 1) (p : Flavor 0) {u : E4} (hu : u≠0) : fare c v p (-u)= -fare c v p u := by
  have h := K_orientation oppositeFrame.ortho (flavor 1 c v) (flavor 0 c p) hu
  rw [whole_axis,whole_axis,upside_one,upside_zero,neg_zero,K_pairing _ _ (neg_ne_zero.mpr hu),map_neg,LinearMap.neg_apply] at h
  apply neg_injective
  rw [neg_neg];
  change -fare c v p (-u - 0)=fare c v p (u-0) at h
  simpa only [sub_zero] using h

section path
abbrev little := nhdsWithin (0:ℝ) (Ioi 0)
variable {x y : ℝ → E4} {u z : E4}

lemma tri_path (c : G.ColorIndex) (hx : Tendsto x little (𝓝 0)) (hy : Tendsto y little (𝓝 0))
    (hz : z≠0) (he : u≠0) (hh : ∀ (t : ℝ), x t-y t=t • u)
    (a : Flavor 0) (v : Flavor 1) (p q : Flavor 0) :
    Tendsto (fun t : ℝ => (↑(t^5):ℂ)*triangle G (x t) (y t) z (team G a v) (team G p p) (team G q q)) little
      (𝓝 (↑((G.lieDim:ℝ)*4*(fare c a q (0-z) * fare c v p u)*fare c p q (0-z)):ℂ)) := by
  let A := fare c a p u
  let W := fare c v p u
  let C' := (G.lieDim : ℝ) * 4
  let L t := fare c a q (x t-z)
  let B t := fare c v q (x t-z)
  let K t := fare c p q (y t-z)
  have hp {i : ℕ} (b : Flavor i) {x : ℝ → E4} (he : Tendsto x little (𝓝 0)) :
      Tendsto (fun t => fare c b q (x t - z)) little (𝓝 (fare c b q (0-z))) :=
    (((kernel_pole (flavor i c b) (flavor 0 c q)).diff _ (sub_ne_zero.mpr hz.symm)).continuousAt.tendsto).comp (he.sub tendsto_const_nhds)
  have ht : Tendsto id little (𝓝 (0:ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  let J t := C' * (t*A*B t + L t*W) * K t
  apply Tendsto.congr' (f₁:=fun t => (J t:ℂ)) ?_
  · have hr := (Tendsto.const_mul C' (((ht.mul_const A).mul (hp v hx)).add ((hp a hx).mul_const W))).mul (hp p hy)
    convert! Complex.continuous_ofReal.continuousAt.tendsto.comp hr using 1
    simp [C',W]
  filter_upwards [hx.eventually (isOpen_ne.mem_nhds (show (0:E4)≠z from hz.symm)),
    hy.eventually (isOpen_ne.mem_nhds (show (0:E4)≠z from hz.symm)),self_mem_nhdsWithin (a:= (0:ℝ)) (s := Ioi 0)] with t hx' hy' ht
  have hv : 0 < t := ht
  have ht₁ : x t≠y t := sub_ne_zero.mp (by rw [hh]; exact smul_ne_zero hv.ne' he)
  rw [tri_fares ht₁ hx' hy' a v p q c,hh]
  have ht₂ {i} (b : Flavor i) : fare c b p (t • u)=t⁻¹^(4+i)*fare c b p u :=
    (kernel_pole _ _).degree t hv u he
  rw [ht₂,ht₂];
  rw [← Complex.ofReal_mul]; apply congr_arg ((↑) : ℝ → ℂ)
  change C' * (t*A*B t+L t*W)* K t=_*(C'*(_^4*A*B t + L t*(t⁻¹^5*W))* K t)
  field_simp

lemma tri_path_far (c : G.ColorIndex) (hx : Tendsto x little (𝓝 0)) (hy : Tendsto y little (𝓝 0))
    (hz : z≠0) (he : u≠0) (hh : ∀ (t : ℝ), x t-y t=t • u)
    (a : Flavor 0) (v : Flavor 1) (p q : Flavor 0) :
    Tendsto (fun t : ℝ => (↑(t^5):ℂ)*triangle G z (x t) (y t) (team G a v) (team G p p) (team G q q)) little
      (𝓝 0) := by
  have hp {i : ℕ} (b : Flavor i) (q : Flavor 0) {x : ℝ → E4} (he : Tendsto x little (𝓝 0)) :
      Tendsto (fun t => fare c b q (z-x t)) little (𝓝 (fare c b q (z-0))) :=
    (((kernel_pole (flavor i c b) (flavor 0 c q)).diff _ (sub_ne_zero.mpr hz)).continuousAt.tendsto).comp (tendsto_const_nhds.sub he)
  have ht : Tendsto id little (𝓝 (0:ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  let C' := (G.lieDim : ℝ)*4
  have hr := ht.mul (((((hp a p hx).mul (hp v q hy)).add ((hp a q hy).mul (hp v p hx))).const_mul C').mul_const (fare c p q u))
  let V t := C' * (fare c a p (z-x t)*fare c v q (z-y t) + fare c a q (z-y t)*fare c v p (z-x t))
  have hr : Tendsto (fun t => t*(V t*fare c p q u)) little (𝓝 0) := by rw [zero_mul] at hr; exact hr
  apply Tendsto.congr' (f₁:=fun t => ((↑(t*(V t*fare c p q u)):ℂ))) ?_
  · rw [← Complex.ofReal_zero]; exact Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  filter_upwards [hx.eventually (isOpen_ne.mem_nhds (show (0:E4)≠z from hz.symm)),
    hy.eventually (isOpen_ne.mem_nhds (show (0:E4)≠z from hz.symm)),self_mem_nhdsWithin (a:= (0:ℝ)) (s := Ioi 0)] with t hx' hy' ht
  have hv : 0 < t := ht
  have ht₁ : x t≠y t := sub_ne_zero.mp (by rw [hh]; exact smul_ne_zero hv.ne' he)
  rw [tri_fares (Ne.symm hx') (Ne.symm hy') ht₁ a v p q c,hh,
    show fare c p q (t • u)=t⁻¹^4*fare c p q u from (kernel_pole _ _).degree t hv u he, ← Complex.ofReal_mul]
  apply congr_arg ((↑) : ℝ → ℂ)
  change _ = t^5*(V t* _)
  field_simp
end path
end YM.Maxwell.Free
