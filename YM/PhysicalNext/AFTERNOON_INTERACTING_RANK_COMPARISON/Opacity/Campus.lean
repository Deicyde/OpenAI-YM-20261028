import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Spokes
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tarps
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Legate
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Elliptic
/-!
# Per-sector accounting at x for E-path exponents

H.Tick coupling used in actual amount. CAB arithmetic band buys upper coupons
also for any positive β below its upper edge: prove this where needed. Inbound
budget entirely from previous stage. Post-publish logarithms in ℝ here and
assemble Epoch separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Ancestor
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums
    AnalyticNext.ConnectedActivity Aff Cab Coverage Calls Win Bid Push.AbsoluteSums
    Dictionary AnalyticBridge.Annulus.Map Dictionary.Geo Jewels Exterior
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {c f n : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x W d t a C Y θ Z : ℝ} {B : ℕ} {p q : Pilot G S x} {X : Support c} {v : Dyed G S} {Q : PathData G}

-- Atoms in all signed lanes, using same weights as apart

def attic (v : Dyed G S) {k : ℕ} (A : ℕ→ Atom G k) (p:Pilot G S x) := ∑ s:Signed,∑ i :Site f, PathData.atomSeries A v.source.p (pull s 0 (v.top p)) i

def leg1 (v : Dyed G S) (p:Pilot G S x):= -v.source.beta*Aff.weight * veil_cuff v.source.path v.source.clip v.source.p (till x) 1 (v.top p)
def leg2 (v : Dyed G S) (p:Pilot G S x):= v.source.beta * Aff.weight* veil_cuff v.things.down v.things.low v.bp (till x) S.patch.L.val p.view

def terra (v : Dyed G S) (p:Pilot G S x):= apart v.source (v.top p) x + coarseTail v.things x v.bp p.view v.source.beta
lemma patrons (v : Dyed G S) (p:Pilot G S x): let P:=v.source.path; let β:= v.source.beta; let w:=Aff.weight
    terra v p =gen v p+(leg1 v p+leg2 v p)+((-w*attic v P.loop p)+((-(β*w)*attic v P.cubic p)+(-(β*w)*attic v P.quartic p))) := by unfold terra gen leg1 leg2 attic coarseTail averaged apart reduced; dsimp only [averaged]; simp_rw [sum_add_distrib, ← mul_sum,sum_add_distrib]; unfold veil_cuff Aff.weight; ring

lemma universes (G : Gauge) (D : Patch) (u : ℕ) (e σ : ℝ) (he : 0≤e) (hσ : 0<σ): ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (v : Dyed G S) (W : ℝ) (P : Teller G), S.patch=D → Chips v P W x → ∀ (A : ℕ→Atom G u) (δ γ : ℝ), SumBudget (fun i=> (A i).budget σ) γ → |δ| *v.source.p.threshold^u*γ ≤ amend G D x (1/8) →
      Petty v W (radiusB x) e ((Fintype.card Signed:ℝ) * amend G D x (1/12)) (fun p:Pilot G S x=> -δ*attic v A p) := by
  filter_upwards [Calls.priced G D u e σ (1/8) (1/12) he hσ (by norm_num) (by norm_num)] with x hx c f S v W P hD hT A δ γ hL hδ
  let P₀:= v.source.p
  let H (i:Lamps f) (p:Pilot G S x):= -δ*(A i.2.2).placed P₀ (pull i.1 0 (v.top p)) i.2.1
  let t : Centered.Till:= ⟨1,0,zero_lt_one,le_rfl⟩; let k i:= t.sale (reserveLamp A P₀ δ S i)
  have hs i : k i=Real.exp 1*(|δ| *P₀.threshold^u*(A i.2.2).magnitude):= sway ..
  have ht :0<P₀.threshold:= P₀.threshold_pos
  have hn i:0≤ |δ| * P₀.threshold^u*(A i).magnitude:= mul_nonneg (by positivity) (by unfold Atom.magnitude; positivity)
  have hm i : 0≤k i:= (hs i).symm ▸ mul_nonneg (Real.exp_pos _).le (hn _)
  have hB i : (article A S x i).Nonempty:= by
    let T:=(A i.2.2); refine ⟨_,halo_subset _ _ (Finset.mem_image_of_mem i.1.act (mem_image_of_mem S.ratio.parent (mem_union_left _ (show i.2.1∈T.footprint i.2.1 from ?_))))⟩
    rw [Paths.atom_foot]; exact mem_insert_self ..
  refine (Petty.accepts (L:=H) (fun i=>Pulled.times (Pulled.fetch _) (chairmen hT A i)) hB hm (hx c f S P₀ v.things t A δ γ hD hL hδ|>.2) he ?_ (v:=v) (W:=W)).traded ?_
  · intro i p hp; unfold H; rw [hs,abs_mul,abs_neg]
    apply le_trans _ (le_mul_of_one_le_left (hn _) (Real.one_le_exp zero_le_one))
    exact (mul_le_mul_of_nonneg_left (healthy_atom (A i.2.2) P₀ (pull i.1 0 (v.top p)) i.2.1) (abs_nonneg _)).trans_eq (by ring)
  intro p
  let U s:= pull s 0 (v.top p)
  intro hp _
  unfold attic; rw [mul_sum]
  symm; apply HasSum.tsum_eq (Cab.favorite (α:=Signed) _ ?_); intro i; rw [mul_sum]
  exact Cab.favorite (α:=Site f) _ (fun j=> (((PathData.atom_dominated A P₀ j hσ hL).summable (U i)).hasSum.mul_left (-δ)))

private lemma rebateWave (G : Gauge) (D : Patch) (σ r C : ℝ) (d : ℕ) (hp : 0<d) (hσ : 0<σ) (hr : 0<r) : ∀ᶠ x in atTop,
    ∀ (β), 0 ≤ β → β ≤ 4*x → ∀ (n : Side) (R : PathData G) (φ : Clip) (Λ t : ℝ), R.Bounds φ σ C Λ →
       ∀ i : Buttons n,0 ≤ untaxed R i x D r σ ∧ ∀ p:Config G n, |β*Aff.weight * chiffon R φ i (till x) d t p| ≤ untaxed R i x D r σ := by
  filter_upwards [outerPay G D σ r C d hp hσ hr,eventually_gt_atTop (0:ℝ)] with x ht he β hb hβ n R φ Λ t hR i
  let z:=betaF G x D.L; have hu : x≤z:= le_add_of_nonneg_right (Work.E04.shift_nonneg ..); have hv:0<z:= lt_of_lt_of_le he hu
  let L:=Real.exp 1; let q:= untaxed R i x D r σ; have hp : q=L*(amend G D x r*laceFee R i σ) := mul_assoc ..
  have hNN:0≤ amend G D x r*laceFee R i σ:= mul_nonneg ((pos_ac _ _ _ r hv).le) (laceFee_nonneg ..)
  refine ⟨show 0≤ q from hp.symm ▸ mul_nonneg (Real.exp_pos _).le hNN, fun p=>?_⟩
  have hH:Wages.OnBand G D x (4*z):=⟨by linarith only [show 0<betaF G x D.L from hv],le_rfl⟩
  have he p:= (ht _ hH n R φ Λ t hR i p).1
  let f:= chiffon R φ i (till x) d t p; refine le_trans ?_ ((he p).trans ((le_mul_of_one_le_left hNN (Real.one_le_exp zero_le_one)).trans_eq hp.symm))
  change |β*Aff.weight*f|≤ |4*z*Aff.weight*f|; rw [mul_assoc β,mul_assoc (4*_ : ℝ),abs_mul,abs_mul (4*z) ,abs_of_nonneg hb,abs_of_nonneg (by positivity : 0 ≤ 4*z)]
  exact mul_le_mul_of_nonneg_right (by linarith only [hβ,hu]) (abs_nonneg _)

lemma credits (P : Teller G) (D : Patch) (e : ℝ) (he : 0 ≤ e): ∀ᶠ x in atTop,
    ∀ (c f : Side) (S : StepData c f) (v : Dyed G S) (W ω : ℝ), S.patch=D → Chips v P W x → v.source.beta ≤4*x →
      LaneCounts v.source.path x v.source.p.threshold v.source.clip ω 1 S.ratio.parent →
      let Q := Fintype.card Signed*((Fintype.card PlaqAxes:ℝ)*amend G D x 1)
      Petty v W (radiusB x) e Q (leg1 v (x:=x)) ∧ Petty v W (radiusB x) e Q (leg2 v (x:=x)):=by
  let w:=P.top.width; let u:=P.below.width; have hw:0<w:= P.top.width_pos; have hu:0<u:=P.below.width_pos
  filter_upwards [rebateWave G D w 2 P.top.paths 1 one_pos hw (by norm_num), rebateWave G D u 2 P.below.paths D.L.val (by positivity) hu (by norm_num),accent G D e P.top.paths w 2 1 D.L he (by norm_num) (by norm_num) hw,accent G D e P.below.paths u 2 1 1 he (by norm_num) (by norm_num) hu] with x he' hm hx hk' c f S v W ω hS h hβ hQ
  intro Q; subst D
  obtain ⟨f',f₀,h₁,h₂⟩:= h.boost.funded.feeds
  rw [← h.boost.funded.high,h.paths,h.clips] at h₁; rw [← h.boost.funded.low] at h₂
  let Z:=v.source; let F p:= v.top (x:=x) p; let g:=Z.beta*Aff.weight; let Y:=v.things
  have hE (i) := he' Z.beta h.beta.le hβ f _ _ _ v.source.p.threshold h₁ i
  have hH (i) := hm Z.beta h.beta.le hβ c _ _ _ (temp x) h₂ i
  have hv {G n} (L : PathData G) (q: Ratio c n) i:(rib L q x i).Nonempty:= ⟨_,halo_subset _ _ (Finset.mem_image_of_mem _ (mem_image_of_mem _ (mem_insert_self ..)))⟩
  constructor
  · refine (Petty.accepts (fun (i:Buttons f)=>Pulled.times (Pulled.fetch (-g)) (strand h hQ i)) (hv _ _) (fun i=>(hE i).1) (hx c f S.ratio _ rfl S.patch.odd_side _ _ h₁) he (fun i p hp=> ?_) (v:=v) (W:=W)).traded fun p hp he=>?_
    · rw [neg_mul,abs_neg]; exact (hE _).2 _
    unfold leg1; rw [neg_mul]; exact (((Cab.spool _ _ v.source.p (till x) 1 (v.top p) h₁).mul_left (-g)).tsum_eq).symm
  refine (Petty.accepts (fun (i:Buttons c)=>Pulled.times (Pulled.fetch g) (renew h i)) (hv _ _) (fun i=>(hH i).1) (hk' c c (plain c) _ rfl (by unfold plain; simp) _ _ h₂) he (fun i p hp=> (hH i).2 p.view) (v:=v) (W:=W)).traded fun p hp he=>?_
  unfold leg2; have hh := ((Cab.spool _ _ v.bp (till x) S.patch.L.val p.view h₂).mul_left g).tsum_eq; rw [h.tall] at hh; exact hh.symm
end YM.PhysicalNext.InteractingRank.Pump.Ancestor
