import YM.Pert.Fourier.Mix
/-! Fixed compact momentum annuli as the independently growing box and top lattice are removed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open YM.Next.Rank.Radian MeasureTheory Filter Lattice Topology Set Function Metric Full
open scoped ContDiff BigOperators RealInnerProductSpace ENNReal
variable {n c : Side}
lemma reads_wrap (c : Side) (v : Cover) (i : Axis) : addr c v i = (v i:ℝ)/c.val := by unfold addr; exact (div_eq_inv_mul ..).symm
lemma stretch_sample (D : List Axis) (s h : ℝ) (hh : 0<h) (hs : 0<s) (hn : c.val = (n.val:ℝ)*h) (p : Site n) : radial D s (addr c (Lattice.lift p))=stretch (h*s) p := by
  ext i; rw [radial_apply,reads_wrap]; unfold stretch; simp only [PiLp.smul_apply,moment_apply,smul_eq_mul]; rw [hn,mesh,factor]; field_simp
lemma char_sample (h : ℝ) (hh : 0<h) (hn : c.val=(n.val:ℝ)*h) (p x : Site n) : YM.Next.Rank.Radian.wave (incVec h (Lattice.lift x)) (addr c (Lattice.lift p)) = char p x := by
  rw [← show wrap n (Lattice.lift x)=x from wrap_lift x,char_wrapped,wrap_lift]
  rw [YM.Next.Rank.Radian.wave, Real.fourierChar_apply,inner_neg_right,neg_neg]
  have e : 2*Real.pi*inner ℝ (addr c (Lattice.lift p)) (incVec h (Lattice.lift x))=corner (Lattice.lift x) (moment p) := by
    unfold corner; rw [PiLp.inner_apply,Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _=>?_)
    simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial,incVec_apply,reads_wrap,moment_apply,hn,mesh]
    field_simp
  have ht := congrArg Complex.ofReal e
  congr 1; push_cast at *; rw [←ht]
lemma centered_sample (v : Cover) (R : ℕ) (hv : v∈room c R) (hn : 2*(R*c.val)<n.val) : Lattice.lift (wrap n v)=v := lift_eq_iff.mpr ⟨rfl,fun i => by
  have e:=Finset.mem_Icc.mp hv; have hh₁ := e.1 i; have hh₂ := e.2 i
  change -(↑(R*c.val):ℤ) ≤ _ at hh₁; change _ ≤ (↑(R*c.val):ℤ) at hh₂
  omega⟩
lemma frame {Φ : E4→ℂ} {R : ℕ} (hn : 2*(R*c.val)<n.val) (hF : eventP R Φ) :
    ∑ p : Site n, Φ (addr c (Lattice.lift p)) = ∑ v ∈ room c R, Φ (addr c v) := by
  let S := (Finset.univ (α:=Site n)).image Lattice.lift
  have h : room c R ⊆ S := fun v hv => Finset.mem_image.mpr ⟨wrap n v, Finset.mem_univ _,centered_sample v _ hv hn⟩
  have e : Function.Injective (Lattice.lift (n:=n)) := fun a b h => by rw [←wrap_lift a,←wrap_lift b,h]
  rw [Finset.sum_subset h (fun v _ hv => hF _ (lt_of_not_ge (fun he=>hv (addressBW _ _ he))))]; dsimp only [S]; rw [Finset.sum_image (s:=Finset.univ) e.injOn]; -- injOn type univ within finset
lemma scans_corona (D : List Axis) (s h : ℝ) (hh : h>0) (hs : s>0) (hn : c.val=(n.val:ℝ)*h) (x : Site n) (R : ℕ) (hR : 2*s/turn≤R) (ht : h*s≤1) (hN : 2*(R*c.val)<n.val) :
    corona h s D x = scansP c (carrier D s (h*s) 0 (incVec h (Lattice.lift x))) R := by
  let f:=carrier D s (h*s) 0 (incVec h (Lattice.lift x))
  rw [corona_expand _ _ hh hs,scansP,← frame (c:=c) (n:=n) (Φ:=f) hN (fun y hy=> together D s hs R (mul_pos hh hs).le ht _ _ _ hR hy)]
  rw [hn,Complex.real_smul]; push_cast; rw [Finset.mul_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; unfold f carrier -- check unfold f dependence
  rw [stretch_sample _ _ _ hh hs hn, char_sample _ hh hn]; have ht (k : E4) : YM.Next.Rank.Radian.major 0 k=1 := by simp [YM.Next.Rank.Radian.major]
  rw [ht]; unfold amp ringM; ring

def precious (D : List Axis) (s b : ℝ) (a : E4) := ∫ k, carrier D s 0 b a k
lemma carrier_joint (D : List Axis) (s : ℝ) {t : ℝ} (ht : |t|≤1) (b z x) : ContinuousAt (fun p : ℝ×(E4×E4)=> carrier D s p.1 b p.2.1 p.2.2) (t,z,x) := by
  have he := (middle_diff D t ht (radial D s x)).continuousAt.comp (f:=fun (p : ℝ×(E4×E4)) => (p.1,radial D s p.2.2)) (show ContinuousAt (fun p : ℝ×(E4×E4) => (p.1,radial D s p.2.2)) (t,z,x) from continuousAt_fst.prodMk ((by unfold radial; fun_prop)))
  refine ((continuousAt_const.mul (by unfold YM.Next.Rank.Radian.wave; fun_prop): ContinuousAt (fun p : ℝ×(E4×E4) => amp D s * YM.Next.Rank.Radian.wave p.2.1 p.2.2) (t,z,x)).mul ?_).mul he
  exact major_cont.continuous.continuousAt.comp (show ContinuousAt (fun p : ℝ×(E4×E4) => ((b,p.2.2) : ℝ×E4)) ((t,z,x):ℝ×E4×E4) by fun_prop)

lemma moving_grid (c : ℕ→Side) (hc : Tendsto (fun i=>(c i).val) atTop atTop) (R : ℕ)
    {F : ℕ→E4→ℂ} {g : E4→ℂ} (ev : ∀ᶠ i in atTop,eventP R (F i)) (hb' : ∃ C : ℝ,0≤C∧∀ᶠ i in atTop, ∀ k, ‖F i k‖≤C)
    (he : ∀ y : E4, ∀ σ : ℕ → E4, Tendsto σ atTop (𝓝 y) → Tendsto (fun i=>F i (σ i)) atTop (𝓝 (g y))) :
    Tendsto (fun i=>scansP (c i) (F i) R) atTop (𝓝 (∫ k,g k)) := by
  obtain ⟨C,hC,H⟩ := hb'
  let S:= closedBall (0:E4) ((R:ℝ)+5)
  have gi : Integrable (S.indicator fun (y:E4)=>C) volume := (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  have hy (i : ℕ) (y : E4) : dist (addr (c i) (mark (c i) y)) y ≤ 4*((c i).val:ℝ)⁻¹ := rock y
  have hv (i : ℕ) : ((c i).val:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (c i).pos)
  have HC : Tendsto (fun i=> ((c i).val:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hc)
  have hmove (y : E4) : Tendsto (fun i=>addr (c i) (mark (c i) y)) atTop (𝓝 y) := Metric.tendsto_atTop.mpr (fun ε hε => Filter.eventually_atTop.mp (by filter_upwards [(HC.const_mul 4).eventually (gt_mem_nhds (by simpa)) ] with i hi; exact lt_of_le_of_lt (hy i y) hi))
  let G (i : ℕ) (k : E4):= F i (addr (c i) (mark (c i) k))
  have eq (i : ℕ) (ht' : eventP R (F i)) : Integrable (G i) ∧ (∫ k, G i k) = scansP (c i) (F i) R := grid_born (c i) (F i) R ht'
  have bound : ∀ᶠ i in atTop, ∀ᵐ (k:E4) ∂volume, ‖G i k‖ ≤ S.indicator (fun _=>C) k := by
    refine (ev.and H).mono fun i hi => Eventually.of_forall fun y => ?_
    by_cases h : y∈S
    · rw [indicator_of_mem h]; exact hi.2 _
    unfold G; generalize hp : addr (c i) (mark (c i) y)=p
    have ha : ‖y-p‖≤4 := by rw [←dist_eq_norm,dist_comm,← hp]; exact (rock y).trans (mul_le_of_le_one_right (by norm_num : (0:ℝ)≤4) (hv _))
    have hn' : ‖y‖≤‖y-p‖ + ‖p‖ := by simpa only [sub_add_cancel] using norm_add_le (y-p) p
    have hg : (R:ℝ)+5 < ‖y‖ := not_le.mp (by simpa [S] using! h)
    rw [indicator_of_notMem h,hi.1 p (by linarith only [hg,ha,hn'])]; simp
  apply (tendsto_integral_filter_of_dominated_convergence _ (ev.mono fun i hi=> (eq i hi).1.aestronglyMeasurable) bound gi (Eventually.of_forall fun k:E4=> he k _ (hmove k))).congr'
  exact ev.mono (fun i hi=> (eq i hi).2)
section
variable (n c : ℕ → Side) (D : List Axis) (s : ℝ) (hs : s>0) (t : ℕ→ℝ) (b : ℝ) (hb : 0≤b)
include hs hb in
lemma scan_limit (hc : Tendsto (fun i=>(c i).val) atTop atTop) {z : E4} {x : ℕ→E4} (hz : Tendsto x atTop (𝓝 z)) {R : ℕ} (hR : 2*s/turn ≤ R) (ht : ∀ i, 0≤t i) (he : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun i=>scansP (c i) (carrier D s (t i) b (x i)) R) atTop (𝓝 (precious D s b z)) := by
  have he' : ∀ᶠ i in atTop, t i≤1 := he.eventually (ge_mem_nhds zero_lt_one)
  obtain ⟨C,hCp,H⟩ := wide_bound D s hs
  let F (i:ℕ):=carrier D s (t i) b (x i)
  have hev : ∀ᶠ i in atTop,eventP R (F i) := he'.mono (fun i hi y hy=>together D s hs R (ht i) hi _ _ _ hR hy)
  have ht' (i : ℕ) (hi : t i≤1) (y : E4) := H (ht i) hi hb (x i) y
  refine moving_grid c hc R (g:=carrier D s 0 b z) hev ⟨C,hCp.le,he'.mono ht'⟩ ?_
  intro y σ hy
  have ev := (carrier_joint D s (t:=0) (by norm_num) b z y).tendsto
  let T := fun i:ℕ=> (t i, x i, σ i)
  let A (p:ℝ×(E4×E4)):=carrier D s p.1 b p.2.1 p.2.2
  have hT : Tendsto T atTop (𝓝 ((0,z,y) : ℝ×E4×E4)) := he.prodMk_nhds (hz.prodMk_nhds hy)
  change Tendsto (A ∘ T) atTop (𝓝 (A (0,z,y)))
  exact ev.comp hT
end
lemma corona_limit (n c : ℕ→Side) {z : E4} (h : ℕ→ℝ) (x : ∀ i, Site (n i)) (hc : ∀ i, (c i).val=((n i).val:ℝ)* h i) (hh : ∀ i, 0<h i) (hv : Tendsto (fun i=>(c i).val) atTop atTop) (he : Tendsto h atTop (𝓝 0)) (hz : Tendsto (fun i=>incVec (h i) (Lattice.lift (x i))) atTop (𝓝 z)) (D : List Axis) (s : ℝ) (hs : 0<s) :
    Tendsto (fun i=>corona (h i) s D (x i)) atTop (𝓝 (precious D s 0 z)) := by
  have ht (S : ℝ) : ∀ᶠ i in atTop, S*h i<1 := (he.const_mul S).eventually (gt_mem_nhds (by rw [mul_zero]; exact zero_lt_one))
  obtain ⟨R,hR⟩ : ∃ R : ℕ, 2*s/turn≤R := exists_nat_ge _
  apply (scan_limit c _ _ hs (fun i=>(h i)*s) _ (by simp : (0:ℝ)≤0) hv hz hR (fun i=>(mul_pos (hh i) hs).le) (by simpa using he.mul_const s)).congr'
  filter_upwards [ht s, ht (2*(R:ℝ))] with i h1 h2
  have hx := mul_lt_mul_of_pos_left h2 (Full.val_pos (n i))
  have he : (2:ℝ) * ((R:ℝ)*(c i).val)<(n i).val := by rw [hc]; linarith only [hx]
  have hhN : 2*(R*(c i).val)<(n i).val := by exact_mod_cast he
  exact (scans_corona D s _ (hh i) hs (hc i) _ _ hR (by linarith only [h1]) hhN).symm
end YM.Pert.Band
