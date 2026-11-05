import YM.UVExtension.Wick.Wedge
import YM.UVExtension.Wick.Sherry

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
namespace Bower
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)

variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
variable {q : Q.rate≤γ} {hh: γ<0} {v₀ C₀ U q'' : ℝ}
local notation "Z₁"=> stalk Q q hh
-- independent of point, retires only within adopted ψ disk.
structure Outliner (N:Bower Q o L S.patch μ χ A b x j K u B C r d n) (hF:Festa Q L H V w g) (γ:ℝ) (q:Q.rate≤γ) (hh:γ<0) (U Z C v: ℝ) (k:ℕ) : Prop where
  margin : 0 ≤ Q.exp-v
  suits : Lush.Shirts o L (radiusB x) U (K*j*2) k
  good : 0≤Z
  size : 1≤U
  lush (z:Vines ι) (hp:z∈parade (betaF G x L) g) : Nonempty (Lush N hF z hp Z ((stalk Q q hh).costs L μ (z none).re x C))
  boxes t (ht:t∈parade (ι:=ι) (betaF G x L) g) (p:Molecule S) :
    permag (t none) (podium S G (H.unionP p) (radiusB x)).card ≤ Real.exp (v*coverNumber (radiusB x) (H.unionP p))
namespace Outliner
variable {k:ℕ} (p'M : Outliner N hF γ q hh U v₀ C₀ q'' k)
local notation "Σ" => parade (ι:=ι) (betaF G x L) g
local notation "B'"=> radiusB x
set_option quotPrecheck false
private abbrev shop (t: Vines ι) (ht:t∈parade (betaF G x L) g):= Classical.choice (p'M.lush t ht)

def badge (o : Molecule S) (v : ℝ) (f : Molecule S → ℝ):= Real.exp (v*coverNumber (radiusB x) (H.unionP o))*f o
abbrev dealP (t : Vines ι) (hx:t∈parade (betaF G x L) g):=shop N hF p'M t hx
private def pace (t : Vines ι) (hx:t∈parade (betaF G x L) g):= Mixed.selected S Q.halo (radiusB x) ((stalk Q q hh).costs L μ (t none).re x C₀) H.birth (dealP N hF p'M t hx).toll (lengths T R) (steamP S ((stalk Q q hh).costs L μ (t none).re x C₀)) 0 (k+j) 0 0

def paint (t: Vines ι) (hx:t∈parade (betaF G x L) g) (p:Molecule S) := U*(1+v₀+2*r)^j*badge (H:=H) p q'' (pace N hF p'M t hx)
abbrev award (G : Gauge) {P:Teller G} (Q : YM.ConnectedActivityE6.Target G P) (x U v r:ℝ) (L:Side) (μ:ℝ) (j k:ℕ):= U*(1+v+2*r)^j * Q.quantum L μ x 0 (k+j) 0 0
variable (t : Vines ι) (ht:t∈parade (betaF G x L) g)

lemma jetbook : (∀ p,0 ≤ paint N hF p'M t ht p) ∧ Ac.Hit H.unionP (radiusB x) (paint N hF p'M t ht) (Q.exp-q'') (award G Z₁ x U v₀ r L μ j k) := by
  let d:= dealP N hF p'M t ht; let p:= (stalk Q q hh).costs L μ (t none).re x C₀
  have he:p.Buy S.patch.L Q.halo (radiusB x):=by rw [H.laws.data.funds.length_eq]; exact d.pair
  let r' u:= badge (H:=H) u q'' (pace N hF p'M t ht); have hg:0≤ U*(1+v₀+2*r)^j:=by have h:=d.conduit.active; have hh:=p'M.good; have hx:=p'M.size; positivity
  have hR : Ac.Hit H.unionP (radiusB x) r' (Q.exp-q'') _:= sale_coast q''
    (show Ac.Hit H.unionP _ _ Q.exp (p.ceiling 0 (k+j) 0 0) from Mixed.mixed_hit S _ _ _ _ _ _ _ he d.acct 0 (k+j) 0 0)
  constructor
  · intro i; apply mul_nonneg hg (mul_nonneg (Real.exp_pos _).le _); unfold pace Mixed.selected; split; next h=> exact Mixed.zero_le_price S _ _ p _ _ _ _ he d.acct ..
    exact le_rfl
  intro i; convert budget_scale hg (hR i) using 1; ext x; simp only [paint]; split <;> first | rw [mul_zero] | apply mul_assoc
  rfl

section jets
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V': E → Config G c} {τ:E} {i:ℕ}
    (he:V' τ=X.V) (hV:Mode V' τ j u)
variable (p:Molecule S) (hv: Ac.Spark H.supportP p) (hp : Healthy (temp X.x) (H.unionP p) X.V) (hw : Matter.troupe T R Q.halo (radiusB x) p)
    (hP:(H.unionP p).Nonempty) (Z:Fin i→ E) (hi:i≤j)
local notation "X'"=> lensS (edgesM S (H.unionP p) (radiusB x)) G
local notation "Φ" => Lush.plated (τ:=τ) (X:=X) (H:=H) (A:=A) (V:=V) (V':=V') p Z

include he hm hr hc hX hF p'M hi hS hV hp hv hw
lemma cargo : let Y:=(F.order G).prod (volume : Measure (Body (↥ X'))); Integrable (Φ t) Y ∧ (∫ y, ‖Φ t y‖ ∂Y) ≤ paint N hF p'M t ht p*(∏ i, ‖Z i‖) := by
  intro Y; let k':=dealP N hF p'M t ht
  let b:= (stalk Q q hh).costs L μ (t none).re x C₀
  have ht': U≥1:=p'M.size
  obtain ⟨hA,h⟩:= Lush.plies N hS hF hX hm hc hr k' he hV p hi Z k U ht' p'M.suits p'M.good hp hw
  have hx:=p'M.boxes t ht p; rw [← chargedU (H.unionP p)] at hx
  have h' : Mixed.Allowed S Q.halo (radiusB x) _ H.birth _ 0 0 0 p:= ⟨hv,Nat.zero_le _,Nat.zero_le _, H.positive_volume _⟩
  unfold paint badge pace; refine ⟨hA,h.trans ?_⟩; rw [Mixed.selected, if_pos (show Mixed.Allowed S Q.halo (radiusB x) b H.birth (lengths T R) 0 0 0 p from h')]
  apply (mul_le_mul_of_nonneg_right hx _).trans_eq
  · unfold Mixed.Price; change _ * (_*_*_* (_:ℝ) * (_:ℝ)) =_ * (_ * (_ * (1+H.shapeW p)^_))*_; simp only [tabs]; unfold k'; ring
  have hh:0≤∏ i∈p,tabs S b (radiusB x) Q.halo k'.toll i:= by
    refine prod_nonneg fun i _=>?_ ; rcases i with i|i; unfold tabs Mixed.costs; dsimp only [Sum.elim]; split <;> first| exact mul_nonneg k'.pair.capture (Real.exp_pos _).le| exact le_rfl
    exact k'.acct.holds _
  have hu := k'.conduit.active; have hx:=H.positive_volume p; have hD:=p'M.good; exact mul_nonneg (mul_nonneg (by positivity) hh) (prod_nonneg fun i _=> norm_nonneg _)
include hP
lemma glaze : Bumps Σ (Lush.mercury (V:=V) (τ:=τ) (H:=H) (A:=A) (V':=V') (X:=X) p Z) := by
  let t:Vines ι:= fun i=> Option.elim' ((betaF G x L:ℝ):ℂ) (fun _=>0) i; have hz:t∈parade (betaF G x L) g:= marching _|>.2 ⟨seat_in (Festa.altitude (H:=H)),fun i=> by change ‖(0:ℂ)‖<g; rw [norm_zero]; exact hF.margin.trans_le hF.bound⟩
  let M:=(F.order G).prod (volume : Measure (Body (↥X')))
  intro Z' F' hg he' hh'
  have hm' z (hz:z∈Z') : Integrable (Φ (F' z)) M ∧ (∫ y, ‖Φ (F' z) y‖ ∂M)≤ (award G Z₁ x U v₀ r L μ j k)*(∏ i, ‖Z i‖):= by
    obtain ⟨hY,h⟩ := cargo N hS hF hX hm hc hr p'M (F' z) (he' hz) he hV p hv hp hw Z hi
    exact ⟨hY,h.trans (mul_le_mul_of_nonneg_right (own_price (jetbook N hF p'M _ (he' hz)|>.2) p'M.margin p hP) (prod_nonneg (fun _ _=> norm_nonneg _)))⟩
  refine Lamppost.tint (F:=fun z=>Φ (F' z)) (μ:=M) hg (fun i=> ?_) (fun i hi=> (hm' i hi).1) (fun i hi=>(hm' i hi).2)
  let R y:= F' y none; have he := ((Lush.blossom N hS hF hX hm hc hr (dealP N hF p'M t hz) he hV p hi Z hp (i.1,spill X' i.2)) Z' F' hg he' hh')
  apply DifferentiableOn.mul _ he; apply bulbs_hol _ _ (procDiff hh' _) (fun z hz=> breath (Festa.altitude (H:=H)) ((marching _|>.1 (he' hz)).1))
end jets
end Outliner
end Bower
end YM.UVExtension.Wick
