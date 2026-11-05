import YM.UVExtension.Linden.Shine
import YM.UVExtension.Linden.Timber
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
variable (p:Molecule S) (hp: Healthy (temp X.x) (H.unionP p) X.V)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V':E → Config G c} {τ:E}
    (ht: V' τ=X.V)(hV:Mode V' τ j u) (t:F.Slice G × Air f G) (q:Vines ι) -- S α
local notation "cA"=> (pilot M p X A Q.table (W:=W) o.a Q.halo V)
local notation "bA"=> (buffer M p X A Q.table (W:=W) o.a Q.halo V)
local notation "Λ"=> grown (ι:=ι) (betaF G x L) w
local notation "Z'"=> edgesM S (H.unionP p) (radiusB x)
local notation "X'"=> lensS Z' G
variable (Y: Mojo Q o L μ A x d v₁ j χ)
variable {m:Molecule S}
variable {U:Mixed.Costs} {z : Vines ι} {hz:z∈parade (betaF G x L) g} (B₀:Lush N hF z hz v₀ U) (h₀:0≤v₀)
local notation "Θ"=> (z none).re
variable {i:ℕ} (hi:i≤j) (Z:Fin i→ E)
local notation "Γ'"=> (F.order G).prod X.dice
local notation "Λx"=> flax (V:=V) (M:=M) (A:=A) (H:=H) (X:=X) (V':=V') (τ:=τ) p Z
local notation "P'"=> (F.order G).prod (volume : Measure (Body (↥ X')))
variable {q':Q.rate≤γ} {h':γ<0} {σ ω' C₀ U0:ℝ} (D': Outliner N hF γ q' h' U0 v₀ C₀ σ k)
local notation "ZV"=> Wick.stalk Q q' h'
local notation "b₁"=> Outliner.dealP N hF D'
def post (X:Coat T F) (_Z0:A=A) (q:Vines ι) := if M.turn.badge S∈p ∧ Ac.Spark H.supportP p∧ troupe T R Q.halo (radiusB x) p then (Fintype.card S.Choices:ℂ)⁻¹*∑ t,
    marsh (V:=V) (A:=A) (V':=V') (τ:=τ) (X:=(planted X p).taggedL t) (H:=H) M p Z q else 0
local notation "Δ"=> post (A:=A) (V:=V) (V':=V') (H:=H) (τ:=τ) M p Z X rfl
local notation "Ψ"=> titleP N hF M (v₁:=v₁) (hz:=hz) D'
include Y hS ht hV hX hp hc hr hi hl D'
lemma bright: Bumps Σ Δ:=by
   unfold post; split; next h=>
    intro U f hx ht' hv; exact (DifferentiableOn.fun_sum (fun i (_:i∈Finset.univ)=> flowers (X:=((planted X p).taggedL i)) N hS hF M hl hX (planted_valid ..) hc hr p hp ht hV Y hi Z D' h.2.1 h.1 h.2.2 U f hx ht' hv)).const_mul _
   exact Lamppost.bumps _ _ (differentiableOn_const _)
include hz
lemma play : ‖Δ z‖ ≤ Ψ p * (∏ i, ‖Z i‖):=by
   unfold post; split; swap; · exact norm_zero.trans_le (mul_nonneg (affluent N hF M Y D' p) (Finset.prod_nonneg fun _ _=> norm_nonneg _)) -- hz explicit inference
   next Hh =>
    let K:ℝ:=Fintype.card S.Choices; have ht' : 0<K:= by unfold K; positivity
    rw [norm_mul,norm_inv, Complex.norm_natCast]
    have hpc i: ‖marsh (V:=V) (V':=V') (X:=((planted X p).taggedL i)) (A:=A) (τ:=τ) (H:=H) M p Z z‖ ≤ Ψ p * (∏ i, ‖Z i‖):= by
       apply le_trans (norm_integral_le_integral_norm _) (targetW N hS hF M hl hX (X:=((planted X p).taggedL i)) (planted_valid ..) hc hr p hp ht hV Y hi Z D' Hh.2.1 Hh.1 Hh.2.2).2
    exact (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun i _=> hpc i)) (inv_nonneg.mpr ht'.le)).trans_eq (by rw [Finset.sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ ht'.ne'])

omit hz Y D'
include N hF
lemma vernal (r:Drums ι)(hv:Λ r)(hΩ:(roster p).flags=∅): let Y:= hl.leaf r hv; let f' t:=Y.picture (vary X (V' t)) p W o.a Q.table Q.halo
    ContDiffAt ℝ (↑j) f' τ ∧ Δ (hoist r)=Complex.ofReal (iteratedFDeriv ℝ i f' τ Z):=by
  intro Y f; let I':= (planted X p); let J t:= I'.taggedL t; let A':= chunk R (blend V (r∘some)) (r none); let H':=(hF.mixture r hv).some; let r' i:=Y.grove (vary X (V' i)) p W o.a Q.table Q.halo
  let I:= podium S G (H.unionP p) (radiusB x); have hB: X.B=radiusB x:=congr_arg _ hX; have heq t := (((N.granted _ _ S T _ _ H' hS rfl).2 E V' F (J t) τ hX hc hr (planted_valid ..) ht hV).1)
  have hs: Healthy (temp x) (H.unionP p) X.V:= by rw [hX] at hp; exact hp
  have hx:f=ᶠ[𝓝 τ] r':= ash (H:=H') (X:=X) Y p hX hr hs hΩ heq
  unfold post; by_cases hh:M.turn.badge S∈p
  swap
  · have hp:f=ᶠ[𝓝 τ] fun _=>0:= Eventually.of_forall fun i=> Daisy.stalk Y _ (show Y.turn.badge S∉ p from (by unfold Y; rw [hl.turn]; exact hh)); refine ⟨contDiffAt_const.congr_of_eventuallyEq hp,?_⟩; rw [if_neg (fun h=>hh h.1), (hp.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]; cases i; simp; rw [iteratedFDeriv_succ_const]; exact Complex.ofReal_zero.symm
  split
  next hy=>
    let m j t:=Y.cinema (vary (J j) (V' t)) p W o.a Q.table Q.halo I
    have hh t: r' t=likely (fun i=>m i t):= by
      unfold r' Leaf.grove; rw [show (vary X (V' t)).B=radiusB x from congr_arg _ hX]; rw [if_pos (show Ac.Spark (areas A' T Q.halo (radiusB x)) p ∧ troupe T A' Q.halo (radiusB x) p from hy.2)]; apply congr_arg likely; funext i; exact (Y.casin X p H' hX hΩ hs i (V' t) (V' t) (fun _ _ _=>rfl)).symm
    let θ:ℝ:= (Fintype.card S.Choices:ℝ)⁻¹; let D':Cash W X.x μ L Q o a T A':=hX.symm ▸ H'; have ha:8*o.a*Pressure.fiery G X.x S.patch.L≤ A/2:=by rw [hX,H.laws.data.funds.length_eq]; exact N.foot
    have hQ j:m j =ᶠ[𝓝 τ] fun t=>∫ t',Y.carat Z' (J j) (V' t) A Q.table p W o.a Q.halo t' ∂((F.order G).prod (J j).dice):=by
       have hC:H.unionP p=D'.unionP p:=by change _= ground R T Q.halo (radiusB X.x) p; rw [hX]; rfl
       unfold m I; rw [hC,← hB]; exact Y.chutes (J j) p D' hr (planted_valid X p) (heq j) N.bay (show 8*o.a*Pressure.fiery G X.x _≤ _ from ha)
    have hA j': ContDiffAt ℝ (↑j) (m j') τ:= ((Y.boosts (X:=J j') p D' hr (planted_valid X p) Z' (heq j') N.bay ha).1.calls.1).congr_of_eventuallyEq (hQ j')
    let y' i:= θ • ∑ v,m v i; have hb':f=ᶠ[𝓝 τ] y':= hx.trans (Eventually.of_forall hh)
    have hL:= ContDiffAt.sum (s:=Finset.univ) (fun i _=> hA i); refine ⟨(show ContDiffAt ℝ (↑j) y' τ from hL.const_smul _).congr_of_eventuallyEq hb',?_⟩
    have hQ' (t): marsh (V:=V) (A:=A) (V':=V') (τ:=τ) (X:=(planted X p).taggedL t) (H:=H) M p Z (hoist r)= ((iteratedFDeriv ℝ i (m t) τ Z:ℝ):ℂ) := pine (X:=(planted X p).taggedL t) N hS hF M hl hX (planted_valid ..) hc hr p ht hV hi Z r hv -- X explicit
    simp_rw [hQ']; rw [(hb'.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]; unfold y'; rw [iteratedFDeriv_const_smul_apply' (hL.of_le (by exact_mod_cast hi)), iteratedFDeriv_fun_sum_apply (n:=i)]; swap; · exact fun i _=> (hA i).of_le (by exact_mod_cast hi)
    unfold θ; simp; exact Or.inl rfl
  next h=>
    have hs:f=ᶠ[𝓝 τ] (fun _=> (0:ℝ)):= hx.trans (Eventually.of_forall (fun i=> by unfold r' Leaf.grove; rw [show (vary X (V' i)).B=radiusB x from congr_arg _ hX]; exact if_neg (fun h'=> h ⟨hh,h'⟩)))
    refine ⟨contDiffAt_const.congr_of_eventuallyEq hs,?_⟩; rw [(hs.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]; cases i; simp; rw [iteratedFDeriv_succ_const]; exact Complex.ofReal_zero.symm
end YM.UVExtension.Linden
