import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Corbel
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Palmate
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sleet

/-!
# Purchases for approximate θ & fields on every Word certificate

 Sales across all optional choices after joint warning profitability. Use
 irrespective of fields off this evaluation, lifetime near P.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a A α β γ d η σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q : YM.ConnectedActivityE6.Target G P}
variable {V : E→ Config G c} {w : E → Directions G f} {u : E→ Air f G}
namespace Clutch

/-- local speed for one label. -/
def twigs (R : Rep G f) (T : Tube G S) (b l : ℕ) (i : Alphabet c f) : ℝ :=
    1+(coverNumber b (footprints T R l b i)+ lengths T R i)

structure Eager (Q : YM.ConnectedActivityE6.Target G P) (o : Target.Order G W) (X A : ℝ) (i : ℕ) (v w : ℝ) (C : ℝ)
    (χ : Chi) (T : Tube G S) (R : Rep G f) (V : ℕ→ℝ) (y : LogIndex c f → ℝ) : Prop where
  first : Sales (radiusB X) Q.relative Q.ε (Raw.forcedFoot S.ratio Q.halo (radiusB X) R) V (Raw.forcedExtra R) C
  hair : Sales (radiusB X) Q.relative Q.ε (roadway T R (radiusB X) Q.halo) y (exCharge T R) C
  stamina : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F : Forest S.ratio) (Z : Coat T F)
      (U:E→Config G c) (u:E→ Directions G f) (z : E→ Air f G) (x:E) (t:Air f G), Z.x=X → Z.width=o.K → Z.χ=χ → Z.manifest →
      Mode U x i v → Clutch Z t o.a R.beta w x i U u z →
        ∀ k : Finset ℕ,
        (∀ p, Brush i (y p) (A*twigs R T Z.B Q.halo (.inr (.inl p)))
          (fun v=> Polar.ember (vary Z (U v)) o.a R W Q.table (u v) (Z.input (worldZ Z R.beta t)) (z v) k Q.halo (.inr (.inr (.inl p)))) x) ∧
        (∀ p, Brush i (V p) (A*twigs R T Z.B Q.halo (.inl p))
          (fun v=>Polar.ember (vary Z (U v)) o.a R W Q.table (u v) (Z.input (worldZ Z R.beta t)) (z v) k Q.halo (.inr (.inl p))) x)

lemma pay_busy (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) {t : ℝ} (h : -(1/2:ℝ)<t) (ht : t<0) :
    ∃ n : ℕ, ∀ (L:Side), n≤L.val → ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ) (o:Target.Order G W) (v w : ℝ→ℝ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop,0≤ v x) → Rate G L (-(1/2)) w → ∃ A C, Rate G L 0 A ∧ Rate G L t C ∧ (∀ x,1≤A x) ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), Works P L x S T → S.patch=D → Stamp T →
      Tent P L x o.K o.eta o.gap o.ample o.indexPay T → ShellAccess S G x W o.K o.γ → ∀ (R:Rep G f), Intake P T x R →
      ∃ V y, Eager Q o x (A x) i (v x) (w x) (C x) χ T R V y := by
  let a:= Q.relative; have hv : 0≤a := by unfold a Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  obtain ⟨N,hN⟩:= hearth P Q.halo Q.usable Q.grants.1 Q.grants.2.1 Q.grants.2.2 hv
  refine ⟨N,fun L hL D hd i χ W o v w hx H hV=>?_⟩
  obtain ⟨B,hB,hFb,hP⟩:= hN L hL i χ o.a t h v w hx hV
  obtain ⟨A,hA,hG⟩:= Clutch.waits P L D hd o.K o.γ W o.a χ i hx H hV o.indexPay o.f t Q.relative Q.ε ht hv Q.halo
    ((by have h:=Q.buys; omega))
  obtain ⟨C,U,b,hC,hU,hY,hQ⟩:= Clutch.flick P L D hd o.K o.γ W o.a χ i hx H hV o.indexPay o.f Q.relative Q.ε hv Q.halo
    (by have h:=Q.buys; omega) Q.table_exists
  let V x := B x+(1+U x); have h' x:1≤V x := by unfold V; linarith [hFb x,hY x]
  obtain ⟨R,hR,H'⟩:= Brush.expands i
  have hs:= (hC.weaken h.le).add hA; have hT:= (Rate.power (G:=G) (a:=t)).add hs
  refine ⟨V,_,hB.add ((Rate.const 1).add hU),(Rate.power (a:=t)).add (hT.mul_left R),h',?_⟩
  filter_upwards [hP,hG,hQ,hT.below ht 1 zero_lt_one] with x hp hZ hA h c f S T H hS hF' hv' hm R' hRZ
  obtain ⟨u,k,hu,hk,hW⟩ := hp _ _ S T R' H.length_eq hRZ
  obtain ⟨y,he,hQ⟩:=hZ _ _ S T hS H hm hv'
  obtain ⟨hX,hY'⟩:= hA _ _ S T hS H hF' hv' hm
  let Y := Sum.elim u (Sum.elim (fun (_:Miniature c f)=>b x) y)
  let s:= betaF G x L ^ t
  have hh : Sales (radiusB x) Q.relative Q.ε (roadway T R' (radiusB x) Q.halo) Y (exCharge T R') (s+(C x+A x)) := hu.together (hX.together he)
  have hz := mul_nonneg hR (budget_nonneg (hh.hit 0))
  refine ⟨k,fun p=> R*Y p, hk.raise (le_add_of_nonneg_right hz), ((hh.shift hR (fun i => mul_nonneg hR (hh.nonneg i)) (fun i=> le_rfl)).raise (le_add_of_nonneg_left (budget_nonneg (hk.hit 0)))),?_⟩
  intro E _ _ _ F Z v u z x' V' hΖ hK hχ hM H'V ht k
  let I:=Z.input (worldZ Z R'.beta V'); let f j:=twigs R' T Z.B Q.halo j
  have hBF:= hW F Z E I v u x' z V' hΖ hχ H'V ht
  have hF i:1≤f i := le_add_of_nonneg_right (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hj k (p q : ℕ) (h : F = F) (he : f k=1+(p+(q:ℝ))) : B x*(p+(q:ℝ)) ≤ V x*f k := by
    rw [he]; refine mul_le_mul (le_add_of_nonneg_right (add_nonneg zero_le_one (hY x))) (le_add_of_nonneg_left zero_le_one)
      (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (zero_le_one.trans (h' _))
  let Δ p:= V x*f p
  have hz : radiusB x=Z.B := congr_arg _ hΖ.symm
  constructor
  · intro j; apply H' E _ (Y j) (Δ _) (fun h=> logMoment (vary Z (v h)) o.a R' Q.table (u h) I (z h) j) _
      ((hh.atom hv Q.usable.le j (exChart ..)).trans ((le_abs_self _).trans h))
    rcases j with j|j|j
    · have hf:=hBF.1 j
      rw [hz] at hf; exact hf.climb le_rfl (hj _ _ _ rfl rfl)
    · have hp:= hY' E F Z R' v u z x' V' hΖ hχ hK hM H'V ht hRZ j
      apply hp.climb le_rfl
      unfold Δ; unfold f twigs lengths; simp only [Sum.elim,exCharge,Nat.cast_zero,add_zero]
      refine mul_le_mul_of_nonneg_right (le_trans (b:=1+U x) (le_add_of_nonneg_left zero_le_one) (le_add_of_nonneg_left (hFb x))) (by positivity)
    exact (hQ E F Z R' v u z x' V' hΖ hχ hK hM H'V ht hRZ j).climb le_rfl (one_le_mul_of_one_le_of_one_le (h' _) (hF _))
  intro j; have hs:= hBF.2 j; rw [hz] at hs; exact hs.climb le_rfl (hj _ _ _ rfl rfl)
end Clutch
end YM.ConnectedActivityE6.Blaze.Silica
