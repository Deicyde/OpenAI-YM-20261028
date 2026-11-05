import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Grades
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

open PhysicalNext.Repeat.Height
def teeth (c f : Side) : LogIndex c f → ℕ:= Sum.elim (Raw.extraA c f) (Sum.elim (fun _=>0) (fun _=>2))
-- Port of stamina on concrete weights with price of all optional leg extras.
lemma rushPrices (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) {t : ℝ} (h : -(1/2:ℝ)<t) (ht : t<0) :
    ∃ n : ℕ, ∀ (L:Side), n≤L.val → ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ) (o:Target.Order G W) (v w : ℝ→ℝ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop,0≤ v x) → Rate G L (-(1/2)) w → ∃ A C, Rate G L 0 A ∧ Rate G L t C ∧ (∀ x,1≤A x) ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), Works P L x S T → S.patch=D → Stamp T →
      Tent P L x o.K o.eta o.gap o.ample o.indexPay T → ShellAccess S G x W o.K o.γ → ∀ (R:Rep G f), Intake P T x R →
      ∃ V y, Sales (radiusB x) Q.relative Q.ε (roadway T R (radiusB x) Q.halo) (fun i=> grow G L x^ teeth c f i * y i) (exCharge T R) (C x) ∧ Eager Q o x (A x) i (v x) (w x) (C x) χ T R V y := by
  let a:= Q.relative; have hv : 0≤a := by unfold a Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  obtain ⟨N,hN⟩:= hearthGrades P Q.halo Q.usable Q.grants.1 Q.grants.2.1 Q.grants.2.2 hv
  refine ⟨N,fun L hL D hd i χ W o v w hx H hV=>?_⟩
  obtain ⟨B,hB,hFb,hP⟩:= hN L hL i χ o.a t h v w hx hV
  obtain ⟨A,hA,hG⟩:= Clutch.waits P L D hd o.K o.γ W o.a χ i hx H hV o.indexPay o.f (-2) Q.relative Q.ε (by norm_num) hv Q.halo
    ((by have h:=Q.buys; omega))
  obtain ⟨C,U,b,hC,hU,hY,hQ⟩:= Clutch.flick P L D hd o.K o.γ W o.a χ i hx H hV o.indexPay o.f Q.relative Q.ε hv Q.halo
    (by have h:=Q.buys; omega) Q.table_exists
  let V x := B x+(1+U x); have h' x:1≤V x := by unfold V; linarith [hFb x,hY x]
  obtain ⟨R,hR,H'⟩:= Brush.expands i
  have hs:= (hC.weaken h.le).add (show Rate G L t (fun x=>grow G L x^2*A x) from (((Rate.power (G:=G) (L:=L) (a:=3/8)).pow 2).mul hA).weaken (by push_cast; linarith only [h])); have hT:= (Rate.power (G:=G) (a:=t)).add hs
  refine ⟨V,_,hB.add ((Rate.const 1).add hU),(Rate.power (a:=t)).add (hT.mul_left R),h',?_⟩
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hP,hG,hQ,hT.below ht 1 zero_lt_one] with x hg hp hZ hA h c f S T H hS hF' hv' hm R' hRZ
  obtain ⟨u,k,hu,hk,hW⟩ := hp _ _ S T R' H.length_eq hRZ
  obtain ⟨y,he,hQ⟩:=hZ _ _ S T hS H hm hv'
  obtain ⟨hX,hY'⟩:= hA _ _ S T hS H hF' hv' hm
  let Y := Sum.elim u (Sum.elim (fun (_:Miniature c f)=>b x) y)
  let s:= betaF G x L ^ t
  have hh : Sales (radiusB x) Q.relative Q.ε (roadway T R' (radiusB x) Q.halo) (fun i=>grow G L x^teeth c f i* Y i) (exCharge T R') (s+(C x+grow G L x^2*A x)) := by
    have ht_or:1≤ grow G L x:= Real.one_le_rpow hg (by norm_num)
    have hl := hu.together (hX.together (boost_price he (pow_nonneg (zero_le_one.trans ht_or) 2)))
    convert hl using 1
    · rfl
    · funext i; rcases i with i|i|i <;> simp only [Y, Sum.elim,teeth,pow_zero,one_mul]
    · rfl
  have hz := mul_nonneg hR (budget_nonneg (hh.hit 0))
  let g (i:LogIndex c f):= R*Y i
  have hX' := hh.shift hR (z:=fun i=>grow G L x^teeth c f i*g i) (fun i=> by unfold g; rw [mul_left_comm]; exact mul_nonneg hR (hh.nonneg _)) (fun i=> by unfold g; rw [mul_left_comm])
  have ht_or:1≤ grow G L x:= Real.one_le_rpow hg (by norm_num)
  have hS' := hX'.raise (le_add_of_nonneg_left (budget_nonneg (hk.hit 0)))
  refine ⟨k,g,hS',hk.raise (le_add_of_nonneg_right hz),store_price (teeth c f) hS' ht_or,?_⟩
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
      (((store_price (teeth c _) hh ht_or).atom hv Q.usable.le j (exChart ..)).trans ((le_abs_self _).trans h))
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
