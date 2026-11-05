import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Spheres

/-!
# Point payment all scored post-Step.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} (I : Finset (Bond f)) {η r Q q Y A a β b p v d t σ : ℝ}

lemma tokens (G : Gauge) (L : Side) {f:ℝ→ℝ} (h : Rate G L 0 f) (j : ℕ) (g : ℝ) : Rate G L 0 (fun x=> Tablet.token j (f x) g) := by
  let d (S:Finset ℕ) x:= ∑ i ∈ S,(f x*g+1)^i*g
  suffices hv : ∀ S:Finset ℕ, Rate G L 0 (d S) from hv (Finset.range (j+1))
  intro S; induction S using Finset.induction_on with
  | empty => unfold d; simp only [sum_empty]; exact Rate.const _
  | insert i s hi hp =>
    unfold d; simp_rw [sum_insert hi]; apply Rate.add _ hp
    simpa only [zero_mul] using! ((((h.mul_right g).add (Rate.const 1)).pow i).mul_right g)

private lemma prices {W B C : ℝ→ℝ} {Z : ℝ→ℝ→ℝ} (j : ℕ) (h : Rate G L 0 W) (hp : Rate G L 0 B) (hv : Rate G L 0 C) (he : Polyprice G L Z)
    (u h' g : ℝ) : Polyprice G L (fun x y=> y* |B x| +seismic j u h' (W x) g (C x) (Z x y) y) := by
  have hh (x):= Polyprice.uniform G L x
  let p := Polyprice.variableP G L
  have hT : Polyprice G L (fun x y=> cenote j y g (W x) (C x)) := by
    apply (((hh (↑(j+1:ℕ))).together (((hh 1).combine p).powP j)).together ((hh j.factorial).together ?_))
    exact ((hh 1).combine ((((Polyprice.fixed h).together (hh g)).combine (hh 1)).together (((hh 1).combine (Polyprice.fixed hv)).powP j))).powP j
  have hF : Polyprice G L (fun x y=> (y*(Z x y*(token j (W x) g*Z x y)))*(1+(1+(driftP j (C x)+1)))^j) := by
    apply (p.together (he.together ((Polyprice.fixed (tokens G L h j g)).together he))).together
    exact ((hh 1).combine ((hh 1).combine ((Polyprice.fixed (hv.mul_left j)).combine (hh 1)))).powP j
  have he:= hp.compare (v:=fun x=> |B x|) (Eventually.of_forall fun x=> (abs_abs _).le)
  apply (p.together (Polyprice.fixed he)).combine
  apply (hh (1+j.factorial*h')).together ((hh 1).combine ?_); apply Polyprice.combine _ (hF.combine hF)
  exact (hh (j.factorial*u)).together (((hh 1).combine (((hh 1).combine hT).together (hh j))).powP j)

lemma rump (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W a : ℝ) (χ : Chi) (j : ℕ)
    {V u e : ℝ→ℝ} (h : Rate G L (-(1/2)) V) (hp : Rate G L (-(1/2)) u) (hv : ∀ᶠ x in atTop,0≤V x) (he : Rate G L 0 e)
    {η r S' : ℝ} (Y : ℝ) (p:Torch η r S') (d : ℝ) : ∃ (k:ℕ) (B:ℝ→ℝ), Rate G L 0 B ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T:Tube G S), Works P L x S T→ S.patch=D → ShellAccess S G x W K γ →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (y:E) (U:E→Config G c) (F:Forest S.ratio) (X:Coat T F) (z:Air f G)
      (R:Rep G f), X.x=x → X.width=K → X.χ=χ → Port P L η r S' Y X → Intake P T x R → Mode U y j (V x) →
        Clutch X z a R.beta (|u x|) y j U (fun i=> steer X d (worldZ X R.beta z) (U i)) (fun i=>course X d R.beta z (U i)) →
        (∀ i, Brush j 1 (e x) (fun v=> steerJ X d (worldZ X R.beta z) (U v) i) y) →
          ∀ I, Brush j 1 (|B x| * facescale I z^k) (fun y=> scalp I X (U y) R.beta d z) y := by
  obtain ⟨Q,hQ,hX⟩:= Brush.neighborhood (k:=j) 0 Real.contDiff_exp.contDiffAt
  obtain ⟨M,hM,hY⟩:= Brush.neighborhood (k:=j) 1 (Real.contDiffAt_log.mpr (by norm_num))
  obtain ⟨A,R,hA,hR,hT⟩:= Blaze.vines P L D hD K γ W χ j p h hv 1
  obtain ⟨H,hH,hP⟩:= bounded_stencils P D hD
  let m:= carat D P L 0 H; let f:= m*m+1; let t:= tubularPrice G L; let g:=payE η r S' t
  let v x:= kernelGrowth (radiusB x) G (V x); let W' x:=driftP j (v x+v x); let b x:=facePrice j (radiusB x) t f g
  let B:=payE (retain η r S') (S'⁻¹/2) (1+g) t; let C x:= burst G L x * (|u x| + (|A x| +|A x|)); let F x y:= C x+y
  have hg:= (jet_growth G L h).weaken (b:=0) (by norm_num)
  have hz {v : ℝ→ℝ} (h : Rate G L (-(1/2)) v):= h.compare (v:=fun x=>|v x|) (Eventually.of_forall fun i=> (abs_abs _).le)
  have hc : Rate G L 0 C := by convert (burst_rate G L).mul ((hz hp).add ((hz hA).add (hz hA))) using 1; ring
  obtain ⟨k,T,ht,hF⟩ := (prices j (polynomial G L j t f g) he (show Rate G L 0 W' from (hg.add hg).mul_left _)
    ((Polyprice.fixed hc).combine (Polyprice.variableP G L)) M Q B).fees
  refine ⟨k,T,ht,hT.mono ?_⟩
  intro x hx c f' S T hh hv hS E _ _ y U F X z A' he hK hχ h hv hM' hB' hK' I
  have hΓ:= h.sails; have hX': X.manifest:= h.placed
  have hL:(vary X (U y)).manifest := hB'.tipped.symm ▸ hX'
  subst x
  have hc:Rotator P L η r S' Y (vary X (U y)) := by rw [hB'.tipped]; exact hΓ
  have hp := Gate.plates X D (by assumption) hh.length_eq hΓ.room hM' H hH (hP _ _ S T (by assumption) hh.funds) (le_refl 0) P.top.width_pos
  have hx' := hx c _ S T (by assumption) hh hS F X E U y rfl hK hχ hM' hL hc.scale
  let w := facescale I z
  have he := (hK' (0,0)).pos; have hy:= hF X.x w (expenses I z).1; rw [abs_of_nonneg he] at hy
  refine (elevates I hY.self_of_nhds hX.self_of_nhds hc hp hx'.1 (abs_nonneg _) hB' hK' he (b:=C X.x+w) ?_).climb le_rfl ((le_abs_self _).trans hy)
  apply add_le_add_left
  unfold C
  exact mul_le_mul_of_nonneg_right (burst_h (L:=L) (hh.length_eq ▸ hv.window.2)) (add_nonneg (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _)))
end YM.ConnectedActivityE6.Blaze.Flux
