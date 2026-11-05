import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brushhold

/-!
# L² feasibility for every tilt-increment circle

 All **ranks** shared. No need product char independence.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets  Silica Poll Pond  Eider ProbabilityTheory
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal NNReal
variable {G : Gauge} {ι : Type} {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} (I : Finset (Bond f)) {η r Q q Y A a β b p v d t σ : ℝ} {w : Air f G}
section mgf
variable [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
-- simple budget from both directions' exponential
lemma reining (B : ℝ) (t : ℝ) (h : A.PosSemidef) (hp : ∀ i, |A i i| ≤ B) (i : ι) :
    let f (x : Body ι) := Real.exp (t*x i)
    Integrable f (Poll.sweep A) ∧ ∫ x, f x ∂(Poll.sweep A)≤Real.exp (B*t^2/2) := by
  intro f
  let g (x:Body ι):= x i; let v:= (A i i).toNNReal
  have hf := measurePreserving_eval_multivariateGaussian (μ:=0) (i:=i) h
  have hv : mgf g (sweep A) t=Real.exp ((v:ℝ)*t^2/2) := by rw [mgf_gaussianReal (by exact hf.map_eq)]; simp [v]
  have hp' : (v:ℝ)≤ B := by unfold v; rw [Real.coe_toNNReal']; exact max_le ((le_abs_self _).trans (hp i)) ((abs_nonneg _).trans (hp i))
  exact ⟨mgf_pos_iff.mp (hv.symm ▸ Real.exp_pos _), hv.trans_le (Real.exp_monotone (by gcongr))⟩

lemma salience (I : Finset ι) (h : A.PosSemidef) (hp : ∀ i,|A i i| ≤ b) (j : ℕ) :
    let f (x:Body ι) := ∑ i∈I, (1+|x i|)^j
    Integrable f (sweep A) ∧ ∫ x,f x ∂(sweep A)≤ I.card*(2*Real.exp (b*(j:ℝ)^2/2)) := by
  intro f; let g (i:ι) (x:Body ι):=(1+|x i|)^j
  have hx i : Integrable (g i) (sweep A) ∧ ∫ x,g i x ∂(sweep A)≤ 2*Real.exp (b*(j:ℝ)^2/2) := by
    let z (s:ℝ) (x:Body ι):= Real.exp (s*x i)
    let t:ℝ:= j; obtain ⟨hp',hk⟩:= reining b j h hp i; obtain ⟨hF,hG⟩:= reining b (-t) h hp i
    have hu x : g i x≤z t x+z (-t) x := by
      unfold g z
      refine ((pow_le_pow_left₀ (add_nonneg zero_le_one (abs_nonneg _)) (show 1+|x i|≤Real.exp |x i| by rw [add_comm]; exact Real.add_one_le_exp _) j).trans_eq (Real.exp_nat_mul ..).symm).trans ?_
      by_cases hg : 0≤ x i
      · rw [abs_of_nonneg hg]; exact le_add_of_nonneg_right (Real.exp_pos _).le
      rw [abs_of_neg (lt_of_not_ge hg),mul_neg,neg_mul]; exact le_add_of_nonneg_left (Real.exp_pos _).le
    have hv : Integrable (g i) (sweep A) := (hp'.add hF).mono' (by unfold g; fun_prop)
      (ae_of_all _ (fun x=> by rw [Real.norm_of_nonneg (show 0 ≤ g i x by unfold g; positivity)]; exact hu x))
    refine ⟨hv,(integral_mono hv ((hp'.add hF) : Integrable (z t + z (-t)) _) hu).trans ?_⟩
    rw [integral_add' hp' hF]; rw [two_mul]; unfold t at *; rw [neg_sq] at hG; exact add_le_add hk hG
  have hh := integrable_finsetSum I fun i _ => (hx i).1
  refine ⟨hh,?_⟩; unfold f; rw [integral_finsetSum]; swap; · exact fun i _=> (hx i).1
  exact (Finset.sum_le_sum (g:=fun _=> 2*Real.exp (b*(j:ℝ)^2/2)) (fun i _=> (hx i).2)).trans_eq (by rw [sum_const,nsmul_eq_mul])
end mgf
lemma globes (p : Rotator P L η r Q Y X) (j : ℕ) : let v:= lensS I G; let f (z:Air f G):=facescale I z^j
    let c:=↑v.card; let Y:=1+(I.card:ℝ)+c+c; let B:= payE η r Q (tubularPrice G L)
    Integrable f X.dice ∧ ∫ z,f z ∂X.dice ≤ Y^j*(1+c*(2*Real.exp (B*(j:ℝ)^2/2))) := by
  intro v f' c Y B; let b (z:Air f G):= 1+∑ i∈v,(1+|z i|)^j
  obtain ⟨hr,hQ⟩:= salience v p.fullC.posSemidef (fun i=> only_price ((p.scale.mate _).1) p.full.prices.le i i) j
  have hp p : f' p ≤ Y^j*b p := by
    by_cases hv:v.Nonempty
    swap
    · have hv : v=∅:= not_nonempty_iff_eq_empty.mp hv
      unfold f' Y b facescale c; rw [show lensS I G=v from rfl]; simp [hv]
    obtain ⟨z,hz,h⟩:= exists_max_image v (fun i:Tubular _ G=>|p i|) hv
    have hs : facescale I p ≤ Y*(1+|p z|) := by
      unfold facescale Y; have hk := sum_le_sum (s:=v) (f:=fun i=> |p i|) (g:=fun i=> |p z|) h
      rw [sum_const,nsmul_eq_mul] at hk; unfold c v at *; nlinarith [Nat.cast_nonneg (α:=ℝ) (I.card), abs_nonneg (p z),Nat.cast_nonneg (α:=ℝ) (lensS I G).card]
    unfold f'; apply (pow_le_pow_left₀ (zero_le_one.trans (expenses I p).1) hs j).trans
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left ((Finset.single_le_sum (f:=fun i=> (1+|p i|)^j) (fun i _=> by positivity) hz).trans
      (le_add_of_nonneg_left zero_le_one)) (by unfold Y c; positivity)
  have hY : Integrable b X.dice := (integrable_const 1).add hr
  have hf : Integrable f' X.dice := (hY.const_mul (Y^j)).mono' (by unfold f' facescale; fun_prop)
     (ae_of_all _ (fun x=> by rw [Real.norm_of_nonneg (show 0≤ f' x from pow_nonneg (zero_le_one.trans (expenses ..).1) _)]; exact hp x))
  refine ⟨hf, (integral_mono hf (hY.const_mul _) hp).trans ?_⟩
  rw [integral_const_mul]; apply mul_le_mul_of_nonneg_left _ (by unfold Y c; positivity)
  unfold b dice; rw [integral_add (integrable_const _) hr, integral_const]; rw [probReal_univ,one_smul]; exact add_le_add_right hQ _
end YM.ConnectedActivityE6.Blaze.Flux
