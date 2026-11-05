import YM.UVExtension.Linden.Day
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Linden
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} 
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
open PhysicalNext.Repeat Daisy Willow Wick Wick.Bower
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
variable {v₁ v₀ b₀ K' w g θ A r B' D d n' n : ℝ} {k j K : ℕ} {χ:Chi}
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)
    (M: PhysicalNext.Repeat.Lotus.Leaf R) (hl:Lines R V w (betaF G x L) M)
set_option quotPrecheck false
variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
local notation "bX"=> M.turn.badge S
local notation "Σ"=> parade (ι:=ι) (betaF G x L) g
variable (Y: Mojo Q o L μ A x d v₁ j χ)
variable {m:Molecule S}
variable {U:Mixed.Costs} {z : Vines ι} {hz:z∈parade (betaF G x L) g} (B₀:Lush N hF z hz v₀ U) (h₀:0≤v₀)
local notation "Θ"=> (z none).re
variable {q':Q.rate≤γ} {h':γ<0} {σ ω' C₀ U0:ℝ} (D': Outliner N hF γ q' h' U0 v₀ C₀ σ k)
local notation "ZV"=> Wick.stalk Q q' h'
local notation "b₁"=> Outliner.dealP N hF D'
open March Greenbelt Ursell Trees Concert Daisy.Charity
local notation "Tπ"=> Concert.aperture hF
local notation "Λ0"=> Canvas (betaF G x L) w ι
variable (J:(d:Canvas (betaF G x L) w ι)→ Cash W x μ L Q o a T (freshen d R V))
local notation "Fs"=> strop N hF M (v₁:=v₁) D'
local notation "Ψ"=> reasons (H:=H) M k j U0 v₀ v₁ r
local notation "f'"=> ivy N hF D'
local notation "qX"=> radiusB x
variable {ξ t ιt:ℝ} (hξ:0≤ξ)(ht:0<t)(he:0<ιt)(ha:ξ+t+ιt≤ Q.exp-σ)
    (hp: 0< Outliner.award G (stalk Q q' h') x U0 v₀ r L μ j k)
    (hT: degreePrice (radiusB x) (2^j*Outliner.award G (stalk Q q' h') x U0 v₀ r L μ j k) ιt≤1/2)
include Y D' hz hξ ht he ha hp hT
lemma grantW : SumBudget (fun i:H.fragrances=> Fs z i*Real.exp ((ξ+t)*coverNumber (radiusB x) (Song.perf H i))) ((2:ℝ)^j * Ψ * (1-1/2)⁻¹):=by
   let f i:= (2:ℝ)^j*f' z i; let b:= Outliner.award G (stalk Q q' h') x U0 v₀ r L μ j k
   have hx:0 ≤ ξ+t:=by linarith only [hξ,ht]
   have hy: Ready H.smallAt qX f (ξ+t) (2^j*b) ιt (1/2):=by
      refine ⟨mul_pos (by positivity) hp,he,hT,by norm_num,fun i=> mul_nonneg (by positivity) (ivy_nn N hF D' z _),fun w=> ?_⟩
      have he:= budget_pull (fun i:H.ThinP=>i.val) Subtype.val_injective ((Outliner.jetbook N hF D' z hz).2 w)
      refine budget_mono (budget_scale (show 0 ≤ (2:ℝ)^j by positivity) he) (fun i=>?_) fun i=>?_
      · split; next hx=> exact mul_nonneg (mul_nonneg (by positivity) (ivy_nn N hF D' z _)) (Real.exp_pos _).le
        exact le_rfl
      split; next h=>
        rw [if_pos (show w∈H.unionP i.val from h)]; unfold f Concert.ivy; rw [dif_pos hz,← mul_assoc]; try dsimp only
        exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (mul_nonneg (by positivity) (Outliner.jetbook N hF D' z hz|>.1 _))
      exact mul_nonneg (by positivity) (he.1 _)
   let u i:= (2:ℝ)^j*moss N hF M (v₁:=v₁) D' z i; have hu i:0≤ u i:=mul_nonneg (by positivity) (moss_nn N hF M Y D' _ _)
   have hp: SumBudget (Copse.priceV H.smallAt qX 0 u (ξ+t+ιt)) ((2:ℝ)^j*Ψ):=by
      refine budget_mono (budget_scale (show 0 ≤ (2:ℝ)^j by positivity) (budget_pull (fun i:H.ThinP=>i.val) Subtype.val_injective (styles N hF M Y (hz:=hz) D'))) (fun i=>mul_nonneg (hu _) (Real.exp_pos _).le) fun i=>?_
      unfold Copse.priceV u moss Copse.worth; rw [dif_pos hz,Copse.one,←mul_assoc ((2:ℝ)^j)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (show 0≤ _ from (by rw [show titleP ..= moss N hF M (v₁:=v₁) D' z i from ?_]; exact hu i; unfold moss; rw [dif_pos hz]))
   convert! Copse.tangled H.seam H.smallAt qX 0 H.testS hy hx hu hp using 1; ext1 i; unfold Copse.worth; rw [Copse.one]; rfl
variable (y:Site c)(m:H.fragrances)
local notation "V0"=> locus M H y
-- use collars.P(G,J), applies before assembly
include hT
noncomputable def fat (W:ℕ)(z:Vines ι) (i:H.fragrances) := if speaks M H i then 2*((grove H i)^(W*j))*(Fs z i) else 0
local notation "gM"=> fat N hF M (v₁:=v₁) D'
lemma paysV (W:ℕ): SumBudget (fun i=>gM W z i * Real.exp (ξ*coverNumber (radiusB x) (V0 i))) ((2*collars G t x j W)*(2^j*Ψ*(1-1/2)⁻¹)):=by
   have hs:=grantW N hF M Y (hz:=hz) D' hξ ht he ha hp hT; have hu:0≤ 2*collars G t x j W:= by unfold collars Reserves.polyPrice shiftG; positivity
   refine budget_mono (budget_scale hu hs) (fun i=>?_) (fun i=>?_); rotate_left
   · unfold fat; split; next h=>
      unfold locus; rw [if_pos h]; let b:ℝ:= coverNumber (radiusB x) (Song.perf H i); have hh:0 ≤ b:= Nat.cast_nonneg _
      have hf:0≤ Fs z i:= nonneg_of_mul_nonneg_left (hs.1 i) (Real.exp_pos _)
      unfold Concert.grove; rw [mul_pow,← mul_assoc]; refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show (1+b)^_≤ polyPrice t _ *Real.exp (t*b) from polynomial_cost ht hh _) (show 0≤ 2* shiftG x ^ (W*j) from mul_nonneg (by norm_num) (pow_nonneg (by unfold shiftG; positivity) _))) hf) (Real.exp_pos _).le).trans_eq ?_; unfold collars b; rw [add_mul ξ,Real.exp_add,show H.bookFoot (.inr i)=Song.perf H i from rfl]; ring
     rw [zero_mul]; exact (budget_scale hu hs).1 _
   unfold fat; apply mul_nonneg _ (Real.exp_pos _).le; split; next he=> exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans (grove_ge _)) _)) (nonneg_of_mul_nonneg_left (hs.1 i) (Real.exp_pos _))
   exact le_rfl
omit hT hp ha he hξ ht hz Y D'
lemma speakers (d:Λ0) : speaks (mantle M hl d) (J d) ((fleet d J H).furrow m) ↔ speaks M H m:=by
    unfold speaks mantle; rw [hl.turn]; rfl
lemma retina (d:Λ0): locus (mantle M hl d) (J d) y ((fleet d J H).furrow m)= locus M H y m:=by
    unfold locus; simp only [speakers M hl J m d]; split; swap; · rfl
    rfl
abbrev rivets (d:Λ0) := matin (mantle M hl d) (J d) ((fleet d J H).furrow m) χ
variable (P0:BudgetPoint)(hP:P0.threshold=temp x)(hh:P0.order ≤ j)(hJ:Sailor G P0.threshold v j)(hY:0 ≤ v) (hf:j*v ≤ u)(hReg:∀ i:H.fragrances,∀ d:Canvas (betaF G x L) w ι,P0.Regular (locus M H y i) (matin (mantle M hl d) (J d) ((fleet d J H).furrow i) χ))
-- handle.Concert.b.Trans
include Y D' hT hP hh hJ hY hξ ht he ha hp hS hF hl hf hReg
variable (hO:y∈ M.crest.image S.ratio.parent)
include hO
lemma aloft (z:Concert.Tap P0 G y (locus M H y m))(W:ℕ)(hw:P0.power≤W) :∃ f:Vines ι→ℂ, Bumps (Concert.aperture hF).span f ∧ (∀ d,f ((Concert.aperture hF).call d)=↑(z.read (matin (mantle M hl d) (J d) ((fleet d J H).furrow m) χ)))∧∀ z∈(Concert.aperture hF).span, ‖f z‖≤ gM W z m:=by
   by_cases hk : speaks M H m; swap
   · refine ⟨0, Lamppost.bumps _ _ (differentiableOn_const _),fun d=>?_,fun z _=> ?_⟩; swap; · unfold fat; rw [if_neg hk]; exact norm_zero.le
     have h:= quiet (mantle M hl d) (J d) χ ((fleet d J H).furrow m) (fun h=>hk ((speakers M hl J m d).1 h)); rw [h]; unfold Concert.Tap.read; rw [show (0: Config G c → ℝ)=(fun _=>0) from rfl,show leftDerivs ..= _ from Work.G07.left_const (G:=G) (0:ℝ) z.poll z.view]; split<;>rfl
   simp_rw [fat,if_pos hk]; let b:=2^j*Ψ*(1-1/2)⁻¹; have ht':∀ i∈(Concert.aperture hF).span,0 ≤ Fs i m∧Fs i m ≤ b:=by
      intro i hi; change i∈parade (ι:=ι) _ _ at hi; have he:= grantW N hF M Y (hz:=hi) D' hξ ht he ha hp hT; have hh:0 ≤ Fs i m:=nonneg_of_mul_nonneg_left (he.1 m) (Real.exp_pos _); have hB:0≤ ξ+t:=by linarith
      exact ⟨hh,(le_mul_of_one_le_right hh (Real.one_le_exp (mul_nonneg hB (Nat.cast_nonneg _)))).trans (budget_single he m)⟩
   have hx: locus M H y m= Song.perf H m:= if_pos hk
   have he': y∈ Song.perf H m:= hx ▸ seatY M H y hO m
   have hg:0 ≤ b:= by
      obtain ⟨z⟩:=canvas_nonempty (ι:=ι) (altitude (H:=H)) hF.margin; have h:= ht' _ ((Concert.aperture hF).within z); exact h.1.trans h.2
   obtain ⟨f,h,hF',hQ⟩:= conduct (g:=fun d=>matin (mantle M hl d) (J d) ((fleet d J H).furrow m) χ) hJ hY hf hh (hReg m) z (fun i=> Fs i m) (by
     intro E i A t P τ hv he; exact braids N hS hF M hl he Y D' m (hx ▸ hP ▸ hv.symm ▸ z.live) J) (by
      rw [hx]; intro x' hx'; let S0:= Song.perf H m; have hs:(separation x' y:ℝ)≤ (coverNumber (radiusB x) S0:ℝ)*(4*(radiusB x:ℝ)+2)+2* (radiusB x:ℝ):=by exact_mod_cast Lattice.Corona.extent S0 (radiusB x) hx' he'
      unfold Concert.grove shiftG; unfold S0 at hs; nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]) (grove_ge m (H:=H)) ht' hg
   exact ⟨f,h,hF',fun i hi=> (hQ i hi).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (grove_ge _) (Nat.mul_le_mul_right _ hw)) (by norm_num)) ((ht' i hi).1))⟩
end YM.UVExtension.Linden
