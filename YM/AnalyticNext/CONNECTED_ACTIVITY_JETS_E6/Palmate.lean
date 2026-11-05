import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Clods
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Plover

/-!
# All certified optional roles. Counting shape retains old κ footprint

 Extraction W Halo marks. Signs and mask controls through original departs.
 W.Seal prep chosen for everyone, not even using tickets in Atom.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
namespace Clutch

lemma flick (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W a : ℝ) (χ : Chi) (j : ℕ)
    {p q : ℝ→ℝ} (h : Rate G L (-(1/2)) p) (he : ∀ᶠ x in atTop, 0≤p x) (hp : Rate G L (-(1/2)) q) {η r S' : ℝ} (Y : ℝ)
    (ho : Torch η r S') (δ ε : ℝ) (hδ : 0 ≤ δ) (l:ℕ) (hl:1≤l) {Ñ : ChartRatio G} (hÑ : LocalRatio Ñ) :
    ∃ V v b : ℝ→ℝ, Rate G L (-(1/2)) V ∧ Rate G L 0 v ∧ (∀ x,0≤v x) ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S: StepData c f)
    (T : Tube G S), S.patch=D → Works P L x S T → Stamp T → Tent P L x K η r S' Y T → ShellAccess S G x W K γ →
      Sales (radiusB x) δ ε (sleeve S (radiusB x) l) (fun _=> b x) (fun _=>0) (V x) ∧
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F : Forest S.ratio) (X : Coat T F) (A : Rep G f)
      (Z : E→ Config G c) (u : E→ Directions G f) (z : E → Air f G) (y:E) (w : Air f G), X.x=x → X.χ=χ → X.width=K → X.manifest →
      Mode Z y j (p x) → Clutch X w a A.beta (q x) y j Z u z → Intake P T x A → ∀ i : Miniature c f, Brush j (b x)
        (v x*(1+coverNumber X.B (sleeve S X.B l i)))
        (fun k=> whelp (vary X (Z k)) a A Ñ (u k) (X.input (worldZ X A.beta w)) i) y := by
  obtain ⟨C,v,hC,hv,hV,hT⟩:= flyers P L l j hl χ h hp he a K γ W D hD Y ho
  obtain ⟨M,hM,h₁⟩:= puffs G L χ a hÑ hp j
  obtain ⟨A,F,hA,hF,h₂⟩:= mistropy P L D hD j Y ho h
  let b x:= |C x| + |M x| + |F x|
  have hh (A : ℝ→ℝ) (t : ℝ) (p : Rate G L t A) := p.compare (v:=fun x=>|A x|) (Eventually.of_forall fun x=> (abs_abs _).le)
  have hB:Rate G L (-(1/2)) b:= ((hh _ _ hC).add (hh _ _ hM)).add (hh _ _ hF)
  let n:= Fintype.card Signed*Census.spots L+(Itinerary.density L+Itinerary.density L)
  let E x:= ((Animals.ballCost ((l+1)*radiusB x):ℝ)*n)*(b x*Real.exp (δ*Animals.ballCost (l+1)))
  have hx:=width_rate G L (l+1) 0; simp only [add_zero] at hx
  refine ⟨E,fun x=>1+v x,b, (by simpa only [zero_add] using! (hx.mul_right n).mul (hB.mul_right _)), (Rate.const 1).add hv,
    fun x=> add_nonneg zero_le_one (hV x),?_⟩
  filter_upwards [hT,h₁,h₂,room G P L] with x hT hZ h hP c f S T hS hk hh hM hA
  have hz := hP c f S T hk
  have hy:0<radiusB x:= lt_of_lt_of_le (by norm_num) hz.sight.1
  have hb:0≤b x:= by unfold b; positivity
  refine ⟨YM.ConnectedActivityE6.fixed (smallCensus S L hk.length_eq) hy _ (packed S hy) hδ hb,?_⟩
  intro E _ _ _ F' X R Z u z y w hs hχ ho hX H hQ hI i
  let v' i:= (1+v x)*(1+(coverNumber X.B (sleeve S X.B l i):ℝ))
  have hL i : 1≤v' i := one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (hV _)) (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have ht := hM F' X hs ho hX
  have ht' : Port P L η r S' Y (vary X (Z y)) := by rw [hQ.tipped]; exact ht
  rcases i with i|i|i
  · refine (hT _ _ S T hS hk hh hM hA E Z y F' X w R u z hI ho hs hχ hX H hQ i).climb ((le_add_of_nonneg_right
      (abs_nonneg _)).trans (le_add_of_nonneg_right (abs_nonneg _))) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity))
  · change Brush j _ (v' (.inr (.inl i))) (fun k=> if voyage X.seeds (200*X.B) i then 0 else (vary X (Z k)).condensation i) _
    split_ifs with hu; exact Brush.zi EventuallyEq.rfl hb (zero_le_one.trans (hL _))
    have hF := (h c f S T F' X E Z y hS hk.length_eq hs ht' H i).2 (by
      refine Shell.clear (without i X.seeds hu) ?_; rw [separation_self]; omega)
    exact hF.climb ((le_abs_self _).trans (le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _)))) (hL _)
  change Brush j _ (v' (.inr (.inr i))) (fun k=> if _ ∧ X.Hot i then X.gentry Ñ a (u k) i else 0) _
  -- cluster dynamic must use constant plaza
  change Brush j _ (v' (.inr (.inr i))) (fun k=> X.solo (u k) Ñ a i) y; unfold solo; split_ifs
  next hx => apply (hZ _ _ S T F' X hs hk.length_eq hχ E w R.beta y Z u z hQ i).climb ((le_add_of_nonneg_left
    (abs_nonneg _)).trans (le_add_of_nonneg_right (abs_nonneg _))) (hL _)
  next h' => exact Brush.zi EventuallyEq.rfl hb (zero_le_one.trans (hL _))
end Clutch
end YM.ConnectedActivityE6.Blaze.Silica
