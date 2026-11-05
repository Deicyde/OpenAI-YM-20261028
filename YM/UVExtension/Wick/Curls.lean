import YM.UVExtension.Wick.Cradle

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

lemma overlog {y v:ℝ} (hk : v≤1/2) (hv : |Real.exp y-1|≤ v) : ‖y‖ ≤2*v:= by
  obtain ⟨he,hp⟩:= abs_le.mp hv; rw [Real.norm_eq_abs]; apply abs_le.mpr
  have hp':0 ≤ v:= le_trans (abs_nonneg (Real.exp y-1)) hv
  constructor
  · have ht : (-y+1)*Real.exp y≤1:= by
      exact ((mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-y)) (Real.exp_pos y).le)).trans_eq (by rw [← Real.exp_add]; simp)
    by_cases hh : 0 ≤ y; linarith
    nlinarith [Real.exp_pos y]
  linarith [Real.add_one_le_exp y]
lemma fugue (j : ℕ):∃ T:ℝ,1≤T ∧ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (w d:ℝ) (f:E→ℝ),
    w≤1/2 → Brush j w d (fun i=>Real.exp (f i)-1) x → Brush j (T*w) d f x:= by
  let g(y:ℝ):=Real.log (1+y)
  obtain ⟨v,hv,h⟩:= Brush.compact (s:=Set.Icc (-1/2) (1/2)) (f:=g) (k:=j) isCompact_Icc
    (fun i hi=> (by obtain ⟨ht,hq⟩:=hi; exact (contDiffAt_const.add contDiffAt_id).log (by change 1+i ≠0; linarith)))
  refine ⟨2+j.factorial*v,by have h':0 ≤ (j.factorial:ℝ)*v:=mul_nonneg (Nat.cast_nonneg _) hv.le; linarith,fun E _ _ x w d f hw hp=>?_⟩
  have hh : |Real.exp (f x)-1|≤ w:= hp.bound
  have hk i:g (Real.exp (f i)-1)=f i := by unfold g; rw [add_sub_cancel,Real.log_exp]
  have hI : Real.exp (f x)-1∈ Set.Icc (-1/2) (1/2):= by have h:=abs_le.mp hh; constructor <;> linarith [h.2,h.1]
  apply (hp.even (h _ hI) (by linarith) (by norm_num) ?_).shimmy (Eventually.of_forall fun i=>(hk _).symm)
  rw [hk]; exact overlog hw hh

local notation "T'"=> vary X
variable (Y : Air f G) (k: Finset ℕ)
local notation "u'"=> fun i:E=> steer X A (loom X Y) (V' i)
local notation "X'"=> fun i:E=> vary X (V' i)
local notation "W'"=> sailplane X A Y
local notation "U"=> X.input (loom X Y)
local notation "ℓ" => r
include N hS hX hm hc hr ht hM
lemma ornate {u₀:ℝ} {R':Rep G f} (h : R'.beta=u₀) (H':Cash W x μ L Q o a T R') (Ξ:Utopia H' j u d r C χ)
    (p:Alphabet c f) (ht':Healthy (temp X.x) (H'.supportP (.inr p)) X.V) :
    Brush j (Ξ.tag (.inr p)) (ℓ*spanW T R' (radiusB x) Q.halo (.inr p)) (fun i=> Polar.ember (X' i) o.a R' W Q.table (u' i) U
      (scaled u₀ (W' (V' i))) k Q.halo (.inr p)) τ:= by
  subst u₀; have hp:=H'.laws.intake.positive
  obtain ⟨hU,hY⟩:= ((N.granted _ _ _ _ _ _ H' hS rfl).2 E V' F X τ hX hc hr hm ht hM).2 (scaled R'.beta Y)
  have h := Ξ.stream E F X V' _ _ _ _ hX hr hc hm hM hU k (.inr p) ht'
  unfold Utopia.tag; rw [← show X.B=_ from congr_arg radiusB hX]
  apply h.shimmy; filter_upwards with i; rw [flown _ _ hp, fanned X _ hp]; rfl

lemma raybrush {z:Vines ι} (hv:z∈parade (betaF G x L) g) (hp: ‖z none‖/ (z none).re≤2) {H' : Cash W x μ L Q o a T (flight R (z none).re)} (Ξ:Utopia H' j u d r C χ)
    {fa:∀ i:ι,Cash W x μ L Q o a T (chunk R (V i) (z none).re)} (Φ : ∀ i,Utopia (fa i) j u d r C χ)
    (p : LogIndex c f)
    (L' : ℝ) (hr':0≤L') (hT : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (w d:ℝ) (f:E→ℝ),
      w≤1/2 → Brush j w d (fun i=>Real.exp (f i)-1) x → Brush j (L'*w) d f x)
    (hh:Healthy (temp X.x) (H'.supportP (.inr (.inr (.inl p)))) X.V) (hhK: Ξ.goalsL p ≤1/2) (hg':∀ i,(Φ i).goalsL p≤1/2) (hB:0≤g):
    Brush j (L'*platK Ξ.goalsL (fun i=>(Φ i).goalsL) g p) (r*spanW T R (radiusB x) Q.halo (.inr (.inr (.inl p))))
      (fun i=> valRay (X' i) R V o.a Q.table (u' i) U (W' (V' i)) (z none) (z ∘ some) p) τ := by
  let y:=(z none).re; have hy :0 < y:= H'.laws.intake.positive
  have heR i : valRay (X' i) R V o.a Q.table (u' i) U (W' (V' i)) (z none) (z ∘ some) p=_:=  (loftR (X' i) V R (Z:=Q.table) (a:=o.a) (z:=W' (V' i)) (u' i) U (z none) hy (z ∘ some) p).2 -- specialize
  let g₀ C i:= logMoment (X' i) o.a C Q.table (u' i) U (scaled y (W' (V' i))) p
  have h'w : Brush j (Ξ.goalsL p) (r*spanW T R (radiusB x) Q.halo (.inr (.inr (.inl p)))) (fun i=>Real.exp (g₀ (flight R y) i)-1) τ:= ornate N hS hX hm hc hr ht hM Y ∅ rfl H' Ξ _ hh
  let d':= r* spanW T R (radiusB x) Q.halo (.inr (.inr (.inl p)))
  have ht i: Brush j ((Φ i).goalsL p) d' (fun x=> Real.exp (g₀ (chunk R (V i) y) x)-1) τ:= ornate N hS hX hm hc hr ht hM Y ∅ rfl (fa i) (Φ i) _ hh
  have hS i:0≤(Φ i).goalsL p:= (ht i).nonneg; have hhD : 0 ≤ ∑ j, (Φ j).goalsL p:= sum_nonneg fun j _=> hS j
  have heV (i:ι): ‖z (some i)‖≤g:= ((marching _|>.1 hv).2 i).le
  simp_rw [heR]; split
  next hh =>
    have hp i:= scales (rises (hT E _ _ _ (g₀ (chunk R (V i) y)) (hg' i) (ht i))) (z (some i))
    apply (Brush.spree (ι:=ι) univ _ _ h'w.pos (fun i _=> hp i)).climb _ le_rfl
    apply le_trans (Finset.sum_le_sum (s:=Finset.univ) (g:=fun i=> g*(L'*(Φ i).goalsL p)) (fun i _=> mul_le_mul_of_nonneg_right (heV i) (mul_nonneg hr' (hS i))))
    unfold platK; rw [← mul_sum,← Finset.mul_sum]; nlinarith [h'w.nonneg]
  next hh=>
    have ht:(‖(if betaBit p then z none/((z none).re:ℂ) else 1)‖) ≤2:= by
      split; next ht=> rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hy.le]; exact hp
      rw [norm_one]; norm_num
    apply (scales (rises (hT E τ _ _ (g₀ (flight R y)) hhK h'w)) (if betaBit p then z none/((z none).re:ℂ) else 1)).climb _ le_rfl
    refine (mul_le_mul_of_nonneg_right ht (mul_nonneg hr' h'w.nonneg)).trans ?_
    unfold platK; nlinarith [mul_nonneg hB hhD]
end Bower
end YM.UVExtension.Wick
