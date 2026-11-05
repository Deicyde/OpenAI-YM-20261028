import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inc

/-! # At a jointly tuned stamp, the reference value pays Help
 Masks themselves need not be nonzero at evaluation, so need extension
 to the closed hill; propagated by Armor. Off-tag U may be wild. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica.Clutch
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush   Tablet Strokes Quill Bid
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a A α β γ d η σ W s b μ r Q p q v : ℝ} {j n l : ℕ}
variable {V : E→ Config G c} {w : E → Directions G f} {u : E→ Air f G}

private lemma mistB (A : Stores S) (k:S.Choices) (x' W : ℝ) (d : ℕ) (hW:0<W) (ht : 0<Pressure.fiery G x' S.patch.L)
    (χ : Chi) {U : Config G f} (hp : Mask.tickets A d U k≠0) (hr : ∀ i∈A.dome d, i∈A.flags ↔ i∈ RG.flags (Pressure.temp x') (V x))
    (hV : Mode V x j p) (hx: ¬ (fun t=>Mask.profiles A χ d x' W U k (V t))=ᶠ[𝓝 x] fun _=>0) :
    Tags.Wide A d U k (V x) x' W := by
  let t:=Pressure.fiery G x' S.patch.L; let Z:=A.dome d
  have hs : (∏ i∈readFine Z S,fine A χ i t U)≠0 := fun h=> hx (Eventually.of_forall fun _ => by change (∏ i∈readFine Z S, fine A χ i t U)*_=0; rw [h, zero_mul])
  refine ⟨fun i hi => lt_of_le_of_ne (site_nn ..) fun h => left_ne_zero_of_mul hp (Finset.prod_eq_zero hi h.symm),fun i hi=> ?_,fun b hB=> ?_,hr⟩
  · have he : fine A χ i t U ≠0 := fun h=> hs (Finset.prod_eq_zero (mem_filter.mpr ⟨mem_univ _,hi⟩) h)
    unfold Mask.fine at he; dsimp only at he; constructor
    · intro h; rw [if_pos h] at he; exact (χ.exterior_gt _ _ (G.chord_nonneg _) (div_pos ht (by norm_num)) he).le
    intro h; rw [if_neg h] at he; change toll _ _ ≤ t/_; have hv:= χ.chosen_lt _ _ (by exact div_pos ht (by norm_num)) he; linarith
  let f(x:E) := wire (S.prediction U k) (V x) b
  have hh : ¬ (fun t' => noise A χ b t W U k (V t'))=ᶠ[𝓝 x] fun _=>0 := fun h => hx (h.mono fun x he=> mul_eq_zero_of_right _
    (Finset.prod_eq_zero (mem_filter.mpr ⟨mem_univ _,hB⟩) he))
  have he : Brush j (royalty G) p (fun i=> G.mat (V i b*(S.prediction U k b)⁻¹)) x := by
    simpa only [one_mul] using! offsetB (hV.atLink b) 1 (S.prediction U k b)⁻¹
  have hf: ContinuousAt f x := ((he.smooth.continuousAt.sub_const _).norm.div_const _)
  have hz:= mul_pos hW ht
  constructor
  · intro hi; by_contra! hv; apply hh; change f x<W*t at hv
    filter_upwards [hf.eventually (gt_mem_nhds hv)] with y hy; by_contra hp
    change noise A χ b t W U k (V y)≠ 0 at hp; unfold Mask.noise at hp; dsimp only at hp; rw [if_pos hi] at hp
    exact lt_asymm (χ.exterior_gt _ _ (G.chord_nonneg _) hz hp) hy
  intro hi; by_contra! hv; apply hh; change 2*W*t<f x at hv; rw [mul_assoc] at hv
  filter_upwards [hf.eventually (lt_mem_nhds hv)] with y hy; by_contra hp
  change noise A χ b t W U k (V y)≠ 0 at hp; unfold Mask.noise at hp; dsimp only at hp; rw [if_neg hi] at hp
  exact lt_asymm (χ.chosen_lt _ _ hz hp) hy

lemma dinner (P : Teller G) (D : Patch) (L : Side) (hd : D.Branches P.bind G) {Ñ : ChartRatio G} (h : LocalRatio Ñ)
    {a W : ℝ} (ha : 0<a) (hW : 0<W) (η r Q Y γ k μ : ℝ) (hm : γ*k≤ a) :
    ∃ C : ℝ, 0≤ C ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S: StepData c f) (T: Tube G S), Works P L x S T → S.patch=D → PointCharge T x W μ →
      ∀ (F : Forest S.ratio) (X: Coat T F), X.x=x → Port P L η r Q Y X → X.width=k → ShellAccess S G X.x W k γ →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (t:E) (V:E→ Config G c) (R : Rep G f), Intake P T X.x R →
      ∀ (u:E→ Directions G f) (z:E→ Air f G) (w:Air f G) (j : ℕ) (s v : ℝ), Mode V t j v → Clutch X w a R.beta s t j V u z →
      ∀ A : Stores S, A.place⊆ X.seeds.place → A.flags=∅ → ∀ (l : ℕ), 500≤l → Healthy (Pressure.temp X.x) (A.dome (l*X.B)) X.V →
      let U:= X.input (worldZ X R.beta w)
      (¬ (fun y=> X.enforce a (u y) (X.plaza (A.dome (304*X.B))))=ᶠ[𝓝 t] fun _=>0) → (Mask.tickets A (300*X.B) U X.k≠0) →
      (¬ (fun y=> Mask.profiles A X.χ (300*X.B) X.x W U X.k (V y))=ᶠ[𝓝 t] fun _=>0) →
        Real.exp (plumeLog (vary X (V t)) a R Ñ (u t) U A+tollFee S.patch (300*X.B)*A.shares) ≤
          Packets.income 1 (C*Delay.bill G L x^5) (R.beta*(μ*X.t^2)) A.shares := by
  let H x:=(2*a)*Pressure.fiery G x L
  obtain ⟨A,U,hA,hU,hV⟩:= max_prices P
  obtain ⟨Z,hZ,h₁⟩:= earns P L D hd A hA (w:=H) (Rate.flame.mul_left _) (Eventually.of_forall fun x=>
    mul_nonneg (by positivity) (by unfold Pressure.fiery temp; positivity))
  obtain ⟨K,hK,h₂⟩:= upkeep h P D L a η r Q Y ha
  have hx:= ((Rate.hat.mul_left 2).mul hZ).below (by norm_num) _ zero_lt_one
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [hx,h₁,h₂,hV L] with x hx he hh hV c f S T hp hD hG F X hX hZ hK' hA E _ _ t V R hr u z w j s v Θ hF Y hy hU l hl hB U hv hY hr'
  subst x
  let x:=X.x
  have h := hZ.sails.room
  rw [hF.tipped,show U=X.input (u t) from congr_arg X.input hF.unseat.symm, (sectorPass X (k:= (∅:Finset ℕ)) a R W Ñ (u t) h hZ.placed hl Y hB).2.1,
    Packets.income,one_mul]
  apply Real.exp_monotone
  have hk i (hi:i∈ Y.dome (300*X.B)) : i ∉ RG.flags (Pressure.temp X.x) (V t) := by
    rw [hF.atV]; exact Finset.disjoint_left.mp hB
        (Corona.halo_mono (le_trans (b:=500*X.B) (by omega) (Nat.mul_le_mul_right _ hl)) (Subset.refl _) hi)
  have hz := mistB Y X.k _ _ _ hW h.fiery X.χ hY (fun i hi=> iff_of_false (by simp [hU]) (hk i hi)) Θ hr'
  rw [hF.atV,show U=X.input (u t) from by rw [hF.unseat]] at hz
  rw [← hK'] at hA
  have hh' := hh c f S T F X rfl hD hp.length_eq hZ.sails hZ.empty R hr Y (u t); rw [← hD] at hh'
  have hΛ : γ*(2*(X.width*X.t)) ≤ H x := by
    rw [hK']; unfold H; rw [← hp.length_eq]; nlinarith only [mul_le_mul_of_nonneg_right hm (show 0 ≤ X.t from h.fiery.le)]
  have hc : Controlled X (304*X.B) Y (u t) (H X.x) := by
    intro i hi he; have hh : i∈ X.plaza (Y.dome (304*X.B)) := mem_filter.mpr ⟨mem_univ _,he,not_disjoint_iff.mpr ⟨atEdge S i,hi,center_end _⟩⟩
    unfold H; rw [← hp.length_eq]; exact (hF.fostered i (mul_pos ha h.fiery) (fun h=>hv (h.mono (fun t hi=> prod_eq_zero hh hi)))).1
  have hhV := he.2 c f S T F X rfl hD hp.length_eq h Y (u t) W γ μ hy (fun U=> ((hV _ _ S T hp).2 _).1) hG hA hΛ hc hz
  have hs : R.beta ≤ 2*betaF G X.x L := hp.length_eq ▸ hr.window.2
  have hP : R.beta*Z X.x ≤ Delay.bill G L X.x ^ 5 := (mul_le_mul_of_nonneg_right hs he.1).trans
    (((le_abs_self _).trans hx).trans (one_le_pow₀ (Delay.bill_ge ..)))
  apply hh'.trans
  nlinarith only [mul_le_mul_of_nonneg_left hhV hr.positive.le,mul_le_mul_of_nonneg_right hP (Nat.cast_nonneg (α:=ℝ) Y.shares)]
end YM.ConnectedActivityE6.Blaze.Silica.Clutch
