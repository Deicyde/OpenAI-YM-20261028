import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Aria
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Periscope
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Serene

/-! # Full short price with same support and post-v phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica.Clutch
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a α β γ d η σ W s b μ : ℝ} {j : ℕ}
open Brush
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {V : E → Config G c} {y : E→ Directions G f} {w : E→ Air f G}

-- Keep selection intact when differentiating all costs.
private lemma certified_hat (i : Stream c f) (hA : 0≤a) (h : ∀ k∈parents i.2, Brush j a 1 (fun y=> message (vary X (V y)) (i.1,k)) x) :
    Brush j (2*((a*a)*(1+(1+1))^j)) 1 (fun y=> Vine.costs (vary X (V y)) (voltage (vary X (V y))) i.1 i.2) x := by
  have he : (parents i.2).card ≤ 2 := by rcases i with ⟨i,k|k|k⟩ <;> simp [parents]
  let C:= (a*a)*(1+(1+1))^j; have hc:0≤C := by unfold C; positivity
  have hp k (hk:k∈parents i.2) : Brush j C 1 (fun y=> pot (vary X (V y)) i.1 k (voltage (vary X (V y)))) x := by
    change Brush j C 1 (fun y=> if X.selected i.1 (spot S k) then _ else 0) x
    split_ifs
    · exact (semi (squared (h k hk))).trim
    exact Brush.zi EventuallyEq.rfl hc zero_le_one
  exact (Brush.spree _ _ (fun _=> C) zero_le_one hp).climb (by rw [sum_const,nsmul_eq_mul]; gcongr; exact_mod_cast he) le_rfl

lemma flyers (P : Teller G) (L : Side) (l j : ℕ) (hl : 1≤ l) (χ : Chi) {p q : ℝ→ℝ} (h : Rate G L (-(1/2)) p)
    (hp : Rate G L (-(1/2)) q) (hm : ∀ᶠ x in atTop,0≤p x) (a d γ W : ℝ) (D : Patch) (hd : D.Branches P.bind G)
    {η r Q : ℝ} (Y : ℝ) (ho : Torch η r Q) :
    ∃ C v, Rate G L (-(1/2)) C ∧ Rate G L 0 v ∧ (∀ x,0≤v x) ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S: StepData c f) (T: Tube G S), S.patch=D → Works P L x S T → Stamp T →
      Tent P L x d η r Q Y T → ShellAccess S G x W d γ → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (V:E→ Config G c) (y:E) (F:Forest S.ratio) (X: Coat T F) (z : Air f G)
      (R : Rep G f) (U : E→ Directions G f) (w:E→ Air f G), Intake P T x R → X.width=d → X.x=x → X.χ=χ → X.manifest →
      Mode V y j (p x) → Clutch X z a R.beta (q x) y j V U w → ∀ i : Stream c f, Brush j (|C x|)
        (v x*(1+coverNumber X.B (sleeve S X.B l (.inl i)))) (fun k=> Polar.hover (vary X (V k)) a R (U k) (X.input (worldZ X R.beta z)) i) y := by
  obtain ⟨C,hC,h₁⟩:= Vine.rain P L D hd j d γ W h hm Y ho
  obtain ⟨E,hE,h₂⟩:= star_earth P L D hd j a h hp hm
  obtain ⟨A,hA,hM,h⟩:= central G L χ j hp (2*a)
  let H x:= 2*((|C x| *|C x|)*(1+(1+1))^j); let K x:= 2*betaF G x L*(|E x|+H x); let v x:= 1+A x
  have ht:= hC.compare (v:=fun x=>|C x|) (Eventually.of_forall fun x=> (abs_abs _).le)
  have hh:= hE.compare (v:=fun x=> |E x|) (Eventually.of_forall fun x=> (abs_abs _).le)
  have hx x : 1≤ v x := le_add_of_nonneg_right (hM _)
  refine ⟨K,v,?_,(Rate.const _).add hA,fun x=> zero_le_one.trans (hx x),?_⟩
  · have hH : Rate G L (-(3/2)) H := (((ht.mul ht).mul_right _).mul_left 2).weaken (by norm_num)
    convert ((Rate.hat.mul_left 2).mul (hh.add hH)) using 1; norm_num
  filter_upwards [h,h₁,h₂] with x hp h₁ h₂ c f S T hS hP hT hZ hΞ E' _ _ V y F X z R U w hR hK hs hy hY hΥ H' i
  subst x; let o:=rowSite S i; let P':= X.booth o; let O:=sleeve S X.B l (.inl i)
  let D k:= vary X (V k); let p:= v X.x*(1+coverNumber X.B O); let ψ x:= X.enforce (2*a) (U x) P'
  let T':= X.input (worldZ X R.beta z)
  have hp':1≤p := (hx X.x).trans (le_mul_of_one_le_right (zero_le_one.trans (hx _)) (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  by_cases he : Inside o X.seeds (200*X.B)
  · exact Brush.zi (Eventually.of_forall fun x=> if_pos he) (abs_nonneg _) (zero_le_one.trans hp')
  have hη := h₁ c f S T hS hP hT hZ hΞ
  have hf : Brush j (H X.x) p (fun k=> Vine.costs (D k) (voltage (D k)) i.1 i.2) y := by
    apply (certified_hat i (abs_nonneg _) ?_).climb le_rfl hp'
    intro k hk; refine (hη F (i.1,k) X rfl hK E' V y hΥ (H'.tipped.symm ▸ hY) ?_).climb (le_abs_self _) le_rfl
    have ho : root S (i.1,k)=o := by unfold root; rw [cost_is_here, (parent_iff k _).mp hk]; rfl
    rw [ho]; apply Shell.clear he; rw [separation_self]; omega
  let f x:= ψ x* Polar.rootface (D x) (U x) T' true i.1 i.2
  have hs: Brush j (|E X.x|) p f y := by
    by_cases hh:ψ=ᶠ[𝓝 y] fun _=>0
    · exact Brush.zi (hh.mono fun y hy=> by change ψ y*_ = _; rw [hy,zero_mul]) (abs_nonneg _) (zero_le_one.trans hp')
    have hH:= h₂ _ _ S T hS hP _ V y F X z R.beta U w rfl hY hΥ H' i he hh
    have hθ : 0< 2*a*X.t := by rw [mul_assoc]; exact mul_pos (by norm_num) H'.pulse
    have hQ : Animals.neighbors X.B o ⊆ O := Corona.halo_mono (le_mul_of_one_le_left (Nat.zero_le _) hl) (Subset.refl _)
    have hv : Brush j 1 (A X.x*(coverNumber X.B O)) ψ y := hp _ _ S T F X rfl hy hP.length_eq hθ E' z a R.beta y V U w H' _ O hQ
    apply (hv.paints hH).climb (by rw [one_mul]; exact le_abs_self _) ?_
    unfold p v; nlinarith only [Nat.cast_nonneg (α:=ℝ) (coverNumber X.B O),hM X.x]
  have hD := (hs.gathering hf).smul (-R.beta*Raw.orientation)
  apply (hD.climb ?_ le_rfl).shimmy (Eventually.of_forall _)
  · rw [norm_mul,norm_neg, Real.norm_of_nonneg Raw.orientation_range.1.le,Real.norm_of_nonneg hR.positive.le]
    refine (mul_le_mul_of_nonneg_right ((mul_le_of_le_one_right hR.positive.le Raw.orientation_range.2).trans
      (show R.beta≤2*betaF G X.x L from hP.length_eq ▸ hR.window.2)) (add_nonneg hs.nonneg hf.nonneg)).trans (le_abs_self _)
  intro y; exact if_neg he

end YM.ConnectedActivityE6.Blaze.Silica.Clutch
