import YM.UVExtension.Wick.Ever

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
variable {x y γ W μ δ e b B C u : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}

namespace Festa
variable {X} (K : Festa Q L H V b B) (hx:X.x=x) (hX:X.width=o.K) (hm:X.manifest)
    {q : Q.rate≤γ} {hh' : γ<0} {v l:ℝ}
local notation "σ" => parade (ι:=ι) (betaF G x L) B

structure Pavilion (H:Cash W x μ L Q o a T R) (V:ι→ Juice G f) (B γ v l:ℝ) (q:Q.rate≤γ) (hh':γ<0) : Prop where
  build x' (hx:x'∈parade (ι:=ι) (betaF G x L) B) : ∃ J:Cash W x μ L Q o a T (flight R (x' none).re), Nonempty (Copal J ((stalk Q q hh').costs L μ (x' none).re x v) V B (x' none))
  cover t (ht:t∈parade (ι:=ι) (betaF G x L) B) (p:Molecule S) : permag (t none) (podium S G (H.unionP p) (radiusB x)).card ≤ Real.exp (l*coverNumber (radiusB x) (H.unionP p))

lemma lodges {l:ℝ} (hz: 0<δ) (hp: Q.rate+δ<γ) (p:γ<0) (v:ℝ) (hv: 0≤v) (N: ℕ) (hm:0<l) (W:ℝ) (h:0<μ) : ∃ A, 0≤ A ∧∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T:Tube G S) (o:Target.Order G W) (R:Rep G f) (H:Cash W x μ L Q o v T R)
      (K:Type) [Fintype K] (Y:K→ Juice G f), Fintype.card K=N→ ∀ b, Festa Q L H Y b (betaF G x L^δ)→ Pavilion H Y (betaF G x L^δ) γ A l (by linarith) p := by
  obtain ⟨A,hA,hK⟩ := Copal.cost (L:=L) hp p hz hv N W h
  refine ⟨A,hA,?_⟩
  filter_upwards [hK,aisles G L l hm] with x hx hl c f S T o R H K _ Y he b hY
  constructor
  · intro t ht; obtain ⟨hv,hk⟩:= marching t|>.1 ht; obtain ⟨J⟩:= hY.known _ hv
    exact ⟨J,hx _ _ S T _ _ J _ K Y he hv rfl (fun i=>hY.kin i _ hv)⟩
  intro t ht p'; have hv:= (hl _ _ S (H.unionP p') _ H.laws.data.funds.length_eq ((marching t).1 ht|>.1)).2.2.2; rwa [Fintype.card_coe] at hv

variable (h : Pavilion H V B γ v l q hh') {t : Vines ι} {c':Molecule S} (hv : (H.unionP c').Nonempty)
    (hl : 0 ≤ Q.exp-l)
include hv hm hx h K hX hl
lemma caja (hh : Ac.Spark H.supportP c') : Bumps σ (cashBox H X V c') := by
  let D:=podium S G (H.unionP c') X.B; let E:=(F.order G).prod (volume : Measure (Body (↥ D)))
  intro S' g hg hD hf
  let p z:=subtend X R W o.a Q.table Q.halo (H.unionP c') V c' (g z) -- supply
  have hK i:Bumps σ (fun t=>subtend X R W o.a Q.table Q.halo (H.unionP c') V c' t i):= by
    intro t c ht hm hh
    exact ((bulbs_hol (r:=fun w=> c w none) _ _ ((ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _:Option ι=>ℂ) none).differentiable.comp_differentiableOn hh) (fun z hz=> breath (altitude (H:=H)) (marching (c z)|>.1 (hm hz)).1)).mul (gush_hol X (H:=H) (V:=V) c' _ t c ht hm hh))
  have hR x0 (hx':x0∈S') : Integrable (p x0) E ∧ (∫ a, ‖p x0 a‖ ∂E)≤ (stalk Q q hh').quantum L μ x 0 0 0 0 := by
    obtain ⟨U,⟨N⟩⟩ := h.build _ (hD hx'); obtain ⟨he,hM⟩ := K.reward hx hX hm c' N l (h.cover _ (hD hx')) (hD hx') hh 0 (Nat.zero_le _)
    exact ⟨he,hM.trans (own_price (Festa.profit (H:=H) N l 0) hl c' hv)⟩
  exact Lamppost.tint (F:=p) (μ:=E) hg (fun i=> hK _ _ g hg hD hf) (fun i hi=> (hR i hi).1) (fun i hi=> (hR i hi).2)
omit hm in lemma stems : Bumps σ (bubble H V X c') := by
  unfold bubble; split
  next he=>
    have hp : Ac.Spark H.supportP c':= by
      have hh:= he.1; unfold Coat.B at hh; rw [hx] at hh; exact hh
    intro Z f hZ hE hf; exact (DifferentiableOn.fun_sum fun i _ => K.caja (X:=((planted X c').taggedL i)) hx hX (planted_valid ..) h hv hl hp Z f hZ hE hf).const_mul _
  exact Lamppost.bumps _ _ (differentiableOn_const _)

-- uniform forests, all p with #flag stamps≥i. keep EXP
omit hm hx hv hX hl
variable {z:Vines ι}
include K h
lemma canthus (ht:z∈σ) (i:ℕ) :
    ∃ f:Molecule S→ℝ, (∀ i,0≤ f i) ∧ Ac.Hit H.unionP (radiusB x) f (Q.exp-l) ((stalk Q q hh').quantum L μ x 0 0 i 0) ∧
    ∀ (F:Forest S.ratio) (X:Coat T F), X.x=x → X.width=o.K→ ∀ p:Molecule S,i≤Cash.numP p→ ‖bubble H V X p z‖≤ f p := by
  obtain ⟨J,⟨N⟩⟩:= h.build z ht; refine ⟨fawn N l i,fawn_nn N l i,Festa.profit N l i,?_⟩
  intro F X hx hp p hi; unfold bubble; split; swap; · exact (norm_zero).trans_le (fawn_nn N l ..)
  next he =>
    have hh : Ac.Spark H.supportP p:= by have hp:= he.1; unfold Coat.B at hp; rw [hx] at hp; exact hp
    let C:ℝ:=Fintype.card S.Choices; have hC:0<C:=by unfold C; positivity
    let f(x):= cashBox H ((planted X p).taggedL x) V p z; have hv t : ‖f t‖≤ fawn N l i p:= (norm_integral_le_integral_norm _).trans
      ((K.reward (X:=((planted X p).taggedL t)) hx hp (planted_valid ..) p N l (h.cover z ht) ht hh i hi).2)
    rw [norm_mul,norm_inv, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (s:=Finset.univ) (fun i _=> hv i))) (inv_nonneg.mpr hC.le)).trans_eq (by rw [Finset.sum_const, card_univ, nsmul_eq_mul,inv_mul_cancel_left₀ hC.ne'])
end Festa
end YM.UVExtension.Wick
