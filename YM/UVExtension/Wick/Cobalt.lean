import YM.UVExtension.Wick.Plaid

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
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' t n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
namespace Bower
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)

variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
variable (z : Vines ι) (hv:z∈parade (ι:=ι) (betaF G x L) g)
set_option quotPrecheck false
local notation "β" => z none
local notation "θ" => (z none).re
local notation "Ψ" => z ∘ some
variable (hq : ‖z none‖/ (z none).re≤2)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V': E → Config G c} {τ:E}
    (ht:V' τ=X.V) (hM:Mode V' τ j u)
local notation "S₁"=> steer X A
local notation "P₁"=> warmth X
variable {J:Cash W x μ L Q o a T (flight R (z none).re)}
-- Size inflation due to Log SHIFT and scaled probes plus measured old y. Currency v≥1.
section factors
variable (Ξ:Utopia J j u d r C χ)
    {fa:∀ i:ι,Cash W x μ L Q o a T (chunk R (V i) (z none).re)} (Φ : ∀ i,Utopia (fa i) j u d r C χ)
    (L' M' t:ℝ)
local notation "ΦK"=>fun i=>(Φ i).goalsK
local notation "ΦL"=>fun i=>(Φ i).goalsL
-- sale cap test includes tags BEFORE art
abbrev tallyK (G : ℝ):=fun i=>t*platK Ξ.goalsK (ΦK) G i
abbrev tallyL (G : ℝ):=fun i=>t*platK Ξ.goalsL (ΦL) G i
abbrev tallyP (t g : ℝ) := rates (tallyK z Ξ Φ t g) (tallyL z Ξ Φ t g) Ξ.M
abbrev tallyQ (t g : ℝ) := rates (tallyK z Ξ Φ t g) (tallyL z Ξ Φ t g) (Ξ.M*Ξ.rad)
-- phases statements; gamma from stalk.
variable (hp : Q.rate ≤ γ) (hg: γ<0) (hT:0≤t) (ht': L'*M' ≤t) (hL':0≤L') (hr':0≤M') (hl': L' ≤t) (htB : 1≤t)
    (C₀ : ℝ)
local notation "Z₀"=> stalk Q hp hg
local notation "θ₁"=> ((stalk Q hp hg).costs L μ ((z none).re) x C₀)
local notation "Γ"=> tallyQ z Ξ Φ t g
local notation "C*"=> tallyP z Ξ Φ t g
-- comparator independent of Healthy, across x masks. 
include hT htB
lemma funnelZ (h:0≤g) (i:Alphabet c f):
    let f x:= (Φ x).flair
    0 ≤ tallyP z Ξ Φ t g i ∧ 0≤ tallyQ z Ξ Φ t g i ∧ tallyQ z Ξ Φ t g i ≤ t*platK Ξ.flair f g i := by
  intro f; have hv x: 0 ≤ platK Ξ.flair f g x:= add_nonneg (mul_nonneg (by norm_num) (Ξ.uses.nonneg x)) (mul_nonneg h (sum_nonneg fun i _=> (Φ i).uses.nonneg x))
  rcases i with i|i|i
  · exact ⟨mul_nonneg hT (hv (.inl i)),mul_nonneg hT (hv (.inl i)),le_rfl⟩
  · exact ⟨mul_nonneg hT (hv (.inr (.inl i))),mul_nonneg hT (hv (.inr (.inl i))),le_rfl⟩
  refine ⟨Ξ.positive,mul_nonneg Ξ.positive Ξ.awake,?_⟩ -- t≥1 include
  have hh:= sum_nonneg (f:=fun j=>f j (.inr (.inr i))) (fun j (_:j∈(Finset.univ:Finset ι))=> (Φ j).uses.nonneg (.inr (.inr i)))
  change Ξ.M*Ξ.rad ≤ t*(2*(Ξ.M*Ξ.rad)+g*∑ j,f j _); nlinarith [htB,mul_nonneg Ξ.positive Ξ.awake,mul_nonneg h hh]

variable (hP : (θ₁).Buy L Q.halo (radiusB x))
    (hv': Sales (radiusB x) Q.relative Q.ε (footprints T R Q.halo (radiusB x)) (tallyQ z Ξ Φ t g)
      (Sum.elim (forcedExtra R) (Sum.elim (exCharge T R) (fun _=>0))) (betaF G x L^γ))
    (h₁ : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (w d:ℝ) (f:E→ℝ),
      w≤1/2 → Brush j w d (fun i=>Real.exp (f i)-1) x → Brush j (L'*w) d f x)
    (h₂ : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (w d:ℝ) (f:E→ℂ),
      Brush j w d f x→ w≤1 → Brush j (M'*w) d (fun i=> Complex.exp (f i)-1) x)
    (h₃ : ((betaF G x L)^ Q.rate:ℝ) ≤ 1/2) (h₄ : (betaF G x L)^γ≤1)
variable (y':Air f G) (k:Finset ℕ)
local notation "S'"=> fun i:E=> steer X A (loom X y') (V' i)
local notation "F'"=> fun i:E=> sailplane X A y' (V' i)
local notation "X'"=>fun i:E=> vary X (V' i)
local notation "U"=>X.input (loom X y')
local notation "ψ"=> fun i (t:E)=> amberP (vary X (V' t)) R Q.table W o.a k Q.halo V (z none) (z ∘ some) (F' t) (S' t) U i
include hS N hF hv hX hm hc hr ht hM hp hq ht' hL' hl' hg htB hv' h₁ h₂ h₃ h₄
lemma easel (i:Alphabet c f) (he:Healthy (temp X.x) (J.supportP (.inr i)) X.V) : Brush j (tallyP z Ξ Φ t g i)
    (r*spanW T R (radiusB x) Q.halo (.inr i)) (ψ (.inr i)) τ := by
  have h:= marching z|>.1 hv; have hh:0 ≤ g:= le_trans hF.margin.le hF.bound
  have hi i: ‖z (some i)‖ ≤ g:= (h.2 i).le
  rcases i with i|i|i
  · have hK v: Brush j ((Φ v).goalsK i) (r*spanW T R (radiusB x) Q.halo (.inr (.inl i)))
      (fun t=> sheath (X' t) o.a (chunk R (V v) 1) (S' t) U i) τ:= ornate N hS hX hm hc hr ht hM y' k rfl (fa v) (Φ v) _ he
    have hp v:= scales (rises (hK v)) (z (some v))
    have hd:= (ornate N hS hX hm hc hr ht hM y' k rfl J Ξ (.inl i) he).pos
    apply (Brush.spree univ _ _ hd (fun i _=> hp i)).climb _ le_rfl
    have hz:0≤Ξ.goalsK i:= Ξ.tagged (.inr (.inl i)); have he : 0 ≤ ∑ j,(Φ j).goalsK i:= sum_nonneg fun j _=> (hK j).nonneg
    apply le_trans (Finset.sum_le_sum (s:=Finset.univ) (f:=fun v=>‖z (some v)‖*((Φ v).goalsK i)) (fun v _=> mul_le_mul_of_nonneg_right (hi v) (hK v).nonneg)); rw [← mul_sum]; change g*_ ≤ t*(2*Ξ.goalsK i+g*_); apply le_trans (le_add_of_nonneg_left (mul_nonneg (show 0≤(2:ℝ) from by norm_num) hz)); exact le_mul_of_one_le_left (add_nonneg (mul_nonneg (by norm_num) hz) (mul_nonneg hh he)) htB
  · have hz : 0≤Q.relative:= by unfold Target.relative; linarith [Q.bound,Q.usable,Q.pos]
    have hk := raybrush N hS hX hm hc hr ht hM y' hv hq Ξ Φ i L' hL' h₁ he ((Ξ.uses.atom hz Q.usable.le (.inr (.inl i)) (exChart ..)).trans h₃) (fun j=> ((Φ j).uses.atom hz Q.usable.le (.inr (.inl i)) (exChart ..)).trans h₃) hh
    let T':= platK Ξ.goalsL (ΦL) g i; have hθ : t*T'≤1:= (hv'.atom hz Q.usable.le (.inr (.inl i)) (exChart ..)).trans h₄
    have h' : 0 ≤ T':= add_nonneg (mul_nonneg (by norm_num) (Ξ.uses.nonneg (.inr (.inl i)))) (mul_nonneg hh (sum_nonneg (fun j _=> (Φ j).uses.nonneg (.inr (.inl i)))))
    apply ((h₂ E τ _ _ _ hk ((mul_le_mul_of_nonneg_right hl' h').trans hθ))).climb _ le_rfl; change _ ≤ t*T'; have hp : M'*L' ≤ t:=mul_comm ..|>.trans_le ht'; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hp h'
  exact rises (ornate N hS hX hm hc hr ht hM y' k rfl J Ξ (.inr (.inr i)) he)
end factors
end Bower
end YM.UVExtension.Wick
