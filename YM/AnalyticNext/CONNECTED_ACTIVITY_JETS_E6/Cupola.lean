import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Intrados

/-!
# Stake flags/v bits and polynomial velocity crops

 Number of gates paid by D.Capture. Shrink χ inverse only against
 small Run. Permit post-Theta waits.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open Pulse Itinerary Scroll Vine Polar Frond Eider Corona
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a α β γ d η σ w s b : ℝ} {j : ℕ}
open Brush
attribute [local instance] Gauge.frobInner

private lemma chatter (G : Gauge) (χ : Chi) (v d : ℝ) {f : E→G.El} (h : Brush j (royalty G) d (fun y=> G.mat (f y)) x)
    (hv : 0<v) (hp : ∀ i∈ Set.Icc (0:ℝ) 4, Brush j w 1 χ.read i) (hw : 0≤w) (hq : d≤1) :
    let g:= G.colorScale; let Y:= (v*g)⁻¹*(2*(v*g)+(royalty G+royalty G)*d)
    Brush j 1 ((1+j.factorial*w)*((1+Y*Y)*(1+1))) (fun i=> χ.innerShare v (G.chord (f i))) x := by
  intro g Y; let f' (i:E):= G.mat (f i)-1
  have hg : 0<g := G.colorScale_pos; have ht: ContinuousAt (fun i=>G.chord (f i)) x := ((h.smooth.continuousAt.sub_const _).norm.div_const _)
  by_cases he : G.chord (f x) ≤ 2*v
  · have hh : ‖f' x‖≤2*(v*g) := ((div_le_iff₀ hg).mp he).trans_eq (by ring)
    have hx i: χ.innerShare v (G.chord (f i))= χ.innerShare (v*g) ‖f' i‖ := by
      apply congrArg χ.read; apply congrArg (fun x:ℝ=>x^2); change _/g/v=_; ring
    simp_rw [hx]; apply plateauChi χ (shrinker (h.separating (a_oneB G 1 h.pos)) hh hq) hp (mul_pos hv hg) hh
  refine Brush.zi ?_ zero_le_one (mul_nonneg (by positivity) (mul_nonneg (add_nonneg zero_le_one (mul_self_nonneg _)) (by norm_num)))
  filter_upwards [ht (lt_mem_nhds (lt_of_not_ge he))] with y hy
  by_contra hk; exact (χ.chosen_lt _ _ hv hk).not_ge (le_of_lt hy)

lemma notches (G : Gauge) (L : Side) (χ : Chi) (j : ℕ) {V : ℝ→ℝ} (h : Rate G L (-(1/2)) V) (b : ℝ) :
    ∃ v, Rate G L 0 v ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (X : Coat T F),
    X.x=x → X.χ=χ → S.patch.L=L → 0<b*X.t → ∀ (U: Config G f) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E→ Config G c) (y:E), Mode f y j (V x) → ∀ i A, Brush j 1 (|v x|) (fun y=> Mask.noise A χ i X.t b U X.k (f y)) y := by
  obtain ⟨w,hp,hX⟩:= Brush.compact (k:=j) (s:=Set.Icc (0:ℝ) 4) (f:=χ.read) isCompact_Icc
    (fun _ _=> χ.smooth.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  let g:= G.colorScale; let f x:=b*Pressure.fiery G x L * g; let Z x:= (f x)⁻¹*(2*f x+(royalty G+royalty G)*V x)
  have hg : 0<g := G.colorScale_pos
  let d x := ((1+(j.factorial:ℝ)*w)*((1+Z x*Z x)*(1+1)))
  have hv : Rate G L 0 d := by
    have h₁ := ((Rate.flame (G:=G) (L:=L)).mul_left b).mul_right g
    have hx : Rate G L (1/2) (fun x=> (f x)⁻¹) := by
      simpa only [f,_root_.mul_inv_rev] using! (((inverse_mist G L).mul_right b⁻¹).mul_left g⁻¹)
    have hX : Rate G L 0 Z := by convert hx.mul ((h₁.mul_left 2).add (h.mul_left (royalty G+royalty G))) using 1; norm_num
    exact ((((Rate.const 1).add ((hX.mul hX).weaken (by simp))).mul_right (1+1)).mul_left _)
  refine ⟨fun x=> (1+(1+1))*d x,hv.mul_left _,?_⟩
  filter_upwards [h.below (by norm_num) 1 zero_lt_one] with x hh c f S T F X hY hχ hL ht U E _ _ Y y hF i A
  have hk : Brush j 1 (d x) (fun z=> χ.innerShare (b*X.t) (wire (S.prediction U X.k) (Y z) i)) y := by
    have hp' : Brush j (royalty G) (V x) _ _ := offsetB (hF.atLink i) 1 (S.prediction U X.k i)⁻¹
    simp only [one_mul] at hp'
    have he:= chatter G χ (b*X.t) (V x) hp' ht hX hp.le ((le_abs_self _).trans hh)
    have hx : X.t=Pressure.fiery G x L := by unfold t; rw [hL,hY]
    exact he.climb le_rfl (by simp only [hx]; exact le_rfl)
  unfold Mask.noise; split_ifs with hi
  · apply (((Brush.certified hk.pos 1).climb (by exact (by norm_num : ‖(1:ℝ)‖≤1)) le_rfl).separating hk|>.exalt
      (?_ : ‖1-χ.innerShare (b*X.t) (wire (S.prediction U X.k) (Y y) i)‖≤1)).climb le_rfl (le_abs_self _)
    have hp: χ.innerShare (b*X.t) (wire (S.prediction U X.k) (Y y) i)∈ Set.Icc 0 1 := χ.range _
    exact abs_le.mpr ⟨by linarith only [hp.2],by linarith only [hp.1]⟩
  refine hk.climb le_rfl ((le_mul_of_one_le_left hk.pos (by norm_num : (1:ℝ)≤ 1+(1+1))).trans (le_abs_self _))

lemma brood (Y : Support c) (M : ℕ) : Y.card ≤ coverNumber M Y*Animals.ballCost M := by
  obtain ⟨D,h,hD⟩:= coverNumber_realized M Y; rw [← hD]; exact (card_le_card h.1).trans (Corona.halo_size D M)
lemma worn (X : Coat T F) {Y p : Support c} (he : Y⊆ p) : (X.plaza Y).card ≤ coverNumber X.B p*ballCost X.B*
    ballCost 1*Itinerary.density S.patch.L := by
  let Z:= halo 1 p
  have hp: (univ.filter fun i:Bond f=> atEdge S i∈ Z).card ≤ Z.card*Itinerary.density S.patch.L := perch S Z
  apply (card_le_card (show X.plaza Y ⊆ univ.filter _ from fun i hi=>?_)).trans (hp.trans ?_)
  swap
  · obtain ⟨x,hx,hv⟩:= Finset.not_disjoint_iff.mp (mem_filter.mp hi).2.2; exact mem_filter.mpr
      ⟨mem_univ _,halo_spec.mpr ⟨x,he hx,stride i hv⟩⟩
  exact Nat.mul_le_mul_right _ ((Corona.halo_size p 1).trans (Nat.mul_le_mul_right _ (brood p X.B)))
lemma canopy (u : E→ Directions G f) (A : Support c) (w : ℝ) {M : Finset (Bond f)} (p : ∀ i∈M, Brush j 1 w (fun y=>X.cone a (u y) i) x)
    (he : M.card≤ coverNumber X.B A*ballCost X.B*ballCost 1*Itinerary.density S.patch.L) (hw : 0 ≤ w) :
    Brush j 1 (coverNumber X.B A*ballCost X.B*ballCost 1*(Itinerary.density S.patch.L:ℝ)*w) (fun y=> X.enforce a (u y) M) x := by
  -- casts annotation
  have hg:= Brush.all_prod M (fun i y=> X.cone a (u y) i) (fun _=>1) (fun _=>w) p
  simp only [Finset.prod_const_one,Finset.sum_const,nsmul_eq_mul] at hg
  apply hg.climb le_rfl; exact mul_le_mul_of_nonneg_right (by exact_mod_cast he) hw
end YM.ConnectedActivityE6.Blaze
