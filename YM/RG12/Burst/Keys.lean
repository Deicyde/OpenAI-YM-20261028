import YM.RG12.Burst.Age
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Vault
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Blush
open Function Filter Lattice RG Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ovens ConnectedActivityE6 Daisy Daisy.Charity Mallow Lotus
open PowerSeries Extra.Histories Progress.DirectedRecipe Next.Foundations Precision
open Blaze Blaze.March Poll Pond Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f n: Side}
variable {i j:ℕ} {o: Site n}{S:Support n}{B : BudgetPoint}
open Pressure Push.SectorMeasure Greenbelt Refrain
variable {S:StepData c f}{T: Tube G S}{L:Side}{P:Teller G} {Q: ConnectedActivityE6.Target G P}{W x μ C : ℝ}{o':Target.Order G W}{R:RG.Rep G f}
variable (H:Cash W x μ L Q o' C T R) (r : Cloud R) (o : Site c)
local notation "hd"=> r.live
local notation "hd'"=> r.pale
local notation "χ"=> Chi.canonical
variable (K R' : ℝ → Code G c)
variable (v: ℂ)
variable (F : YM.Labels.Frame G j)
section prices
local notation "M" => Blush.screen H r K R' v F
variable {R2 : Rep G c} (he:R2.p=B)
variable {A b q t d Y f₀ α k β e w t':ℝ}{n' ℓ:ℕ}(N: Captain H n' q t d Y A b t' f₀ k ℓ Chi.canonical)
namespace Burst10
open Daisy.Charity.RG12 Push.Local
variable {s:ℝ}(hs:1≤ s)(hz:Bikes Q L μ x α e f₀ n' ℓ) (hF:foam Q L)
  (h1:Trees.degreePrice (radiusB x) (s*(Q.costs L μ 1 x 0).rootHit) Q.δ ≤ 1/2)
  (h2:Trees.degreePrice (radiusB x) (s*(swing Q L μ 1 x 0).rootHit) Q.δ ≤1/2)
  (h3:Trees.degreePrice (radiusB x) (Q.goal L x+ value10 Q L μ x s f₀ n' ℓ) e≤1/2)
  (hR : Herd H N.conduit A f₀ ℓ)(hb:B.B=radiusB x)(hu:B.threshold=Pressure.temp x)(hk:B.order≤ n')(ha:B.supportExponent+2 ≤ α)(h:o∈ r.live.crest.image S.ratio.parent)
local notation "J!" i => brush10 r.live H N o B.power i
local notation "F!" i => brush10 r.pale H N o B.power i
local notation "w!" m => cash10 Q L μ x s f₀ n' ℓ e B.power m
local notation "u!" => R.p.mass r.live.crest r.live.weight * Real.exp (-Q.ε*coverNumber R.p.B r.live.crest)
local notation "q!" m => ‖v‖*(u! *(w! m) + u!*(w! m))
local notation "Z!" i => ‖v‖*((J! i) + F! i)
local notation "X!" => locus r.live H o
include hR h hu hk
lemma S' : ∀ i, B.Regular (locus r.live H o i) (pane H r v i) ∧ B.supBounds o (X! i) (pane H r v i) (Z! i):=by
  intro i; obtain ⟨hT,hQ⟩:= Daisy.Charity.RG12.supply r.live H N hR B h hu hk i
  obtain ⟨hp,hp'⟩:= Daisy.Charity.RG12.supply r.pale H N hR B (show o∈_ from r.turnout ▸ h) hu hk i; rw [← arches] at hp hp'
  have hh:= bound_smul Complex.I (pricingG hp hp'); rw [Complex.norm_I,one_mul] at hh
  exact ⟨regular_smul _ (regular_add (ornate hT) (regular_smul _ (ornate hp))), bound_smul v (bound_add (ornate hT) (regular_smul _ (ornate hp)) (pricingG hT hQ) hh)⟩
omit hR hu hk
include hs hz hF h1 h2 h3 hb ha
lemma sums (m:ℕ): SumBudget (fun i=>if m≤hue H i then Local.reservedMass B (X! i) (Z! i) else 0) (q! m):=by
   have hA:= skill (hd) H N (zero_lt_one.trans_le hs) h1 h2 hz hF h3
   have hA':= skill (hd') H N (zero_lt_one.trans_le hs) h1 h2 hz hF h3
   have hp:= bill10 r.live H N hs hz hA h B.power m; have hp':= bill10 r.pale H N hs hz hA' (show o∈_ from r.turnout ▸ h) B.power m
   simp_rw [← arches] at hp'
   have hP:= budget_scale (norm_nonneg v) (budget_plus hp hp')
   rw [← Blush.jewels r] at hP
   apply Eq.mp ?_ (budget_mono (g:=fun i=>if m≤ hue H i then Local.reservedMass B (X! i) (Z! i) else 0) hP ?_ ?_)
   · unfold cash10 jewelDebt; apply congr_arg; simp_rw [div_eq_mul_inv]; ring
   · intro i; split; next hh => exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (norm_nonneg _) (add_nonneg (brushN ..) (brushN ..)))
     exact le_rfl
   intro i; split
   next hh =>
     rw [Local.reservedMass,hb]; let t:=coverNumber (radiusB x) (locus r.live H o i); let k:=(J! i) + F! i
     apply (mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (show _≤α from ha) (show 0≤(t:ℝ) from Nat.cast_nonneg _))) (mul_nonneg (norm_nonneg v) (add_nonneg (brushN ..) (brushN ..)))).trans_eq
     ring -- exactly supp+2?
   next _=> simp
-- buy whole Local.weighted matrix loss (readPrice before L, no coupl factor). Not just d4 projection. TallyPivot possibly multiplies? post absorptions.
open Labels Source
variable {τ:ℝ}(g:Hol G) {S':SectionData F}(hΓ : Local.Readable g S' B c τ)
def rows10 (i:H.fragrances) := Local.weighted g F o (locus r.live H o i) B.threshold (pane H r v i)
include hΓ hR hu hk
lemma priced (m:ℕ): SumBudget (fun i=> F.coeffSize (if m≤hue H i then rows10 (B:=B) H r o v F g i else 0)) (Local.readPrice g F * (q! m)):=by
   have hx':1≤readPrice g F:=readPrice_pos ..
   have hx:= budget_scale (f:=_) (zero_le_one.trans hx') (sums (B:=B) H r o v N hs hz hF h1 h2 h3 hb ha h m)
   refine Push.AbsoluteSums.budget_mono hx (fun i=>Work.G08.size_nonneg ..) (fun i=> ?_)
   split
   next _=>
     obtain ⟨he,hV⟩:=Burst10.S' H r o v N hR hu hk h i
     exact (weighted_bound g F o he hΓ.order hΓ.power hV).trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hV.1 (Real.one_le_exp (mul_nonneg (by positivity [B.exponent_pos]) (Nat.cast_nonneg _)))) (zero_le_one.trans hx'))
   next _=>rw [mul_zero]; unfold Labels.Frame.coeffSize; simp only [Pi.zero_apply, norm_zero,Finset.sum_const_zero,le_refl]
lemma columns (m:ℕ) : Summable (fun i:H.fragrances=> if m≤ hue H i then rows10 (B:=B) H r o v F g i else 0) ∧ F.coeffSize (∑' i, if m≤ hue H i then rows10 (B:=B) H r o v F g i else 0) ≤ Local.readPrice g F*(q! m):=by
    have ht:= priced H r o v F N hs hz hF h1 h2 h3 hR hb hu hk ha h g hΓ m
    exact ⟨(Size.series F ht.2.1).of_norm,(Size.bound F ht.2.1).trans ht.2.2⟩
end Burst10
end prices
end YM.PhysicalNext.Repeat.Blush
