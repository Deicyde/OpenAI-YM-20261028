import YM.PhysicalNext.FLAT_PUSH_RESPONSE.OnTrack
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Rush
import YM.Primitives.SMALL_FIELD_EXTERIOR.Identity
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
variable {a A α β γ d η σ W s b μ r p q C C' v : ℝ} {j n l : ℕ} {Q : YM.ConnectedActivityE6.Target G P}
variable {V : E→ Config G c} {w : E → Directions G f} {u : E→ Air f G} {o : Target.Order G W} {χ : Chi}

open PhysicalNext.Repeat.Height
def horn : Alphabet c f → ℕ := Sum.elim (fun _=>0) (Sum.elim (teeth c f) (fun _=>2))

def Heavy {C : ℝ} {H : Cash W s μ L Q o C T R} {χ : Chi} (I : Utopia H j v d r C' χ) :=
    Sales (radiusB s) Q.relative Q.ε (footprints T R Q.halo (radiusB s))
      (fun i=> grow G L s ^ horn i * I.flair i) (Sum.elim (Raw.forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (Q.goal L s)
namespace Utopia
lemma twinkles (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0 < W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W) (v w : ℝ→ℝ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop,0≤v x) → Rate G L (-(1/2)) w → ∃ (C':ℝ) (r:ℝ→ℝ), 0≤C' ∧ Rate G L 0 r ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T → ∀ (R:Rep G f) (C:ℝ) (H:Cash W x μ L Q o C T R),
      ∃ Ξ : Utopia H i (v x) (w x) (r x) C' χ, Heavy Ξ := by
  obtain ⟨t,hT,ht⟩:= exists_between Q.start
  obtain ⟨n,hn⟩:= Clutch.rushPrices P Q hT (ht.trans Q.stop)
  refine ⟨n,fun L hL D hd i χ W hw μ hm o v w hv hwV hW=>?_⟩
  obtain ⟨C,hC,hΨ⟩:= Clutch.chimney P D L hd o.K o.γ W o.a χ i Q.table_exists hv hwV hW μ o.indexPay o.f o.large hw o.gamma
  obtain ⟨B,J,hB,hJ,hv',h⟩:= hn L hL D hd i χ W o v w hv hwV hW
  obtain ⟨A,hA,hy,hQ⟩:=Clutch.ash G L χ i hW hv W o.a Q.halo (by have h:=Q.buys; omega)
  obtain ⟨Y,hY,hF⟩:= Coat.alarm_bills (η:=o.eta) (r:=o.gap) (Q:=o.ample) (Y:=o.indexPay) P L (-5) (half_pos o.rare)
  let g x:= betaF G x L ^(-(2:ℝ)); let Z x:= B x+A x; have hZ x:1≤Z x:= (hv' x).trans (le_add_of_nonneg_right (hy x))
  have hp:0≤ Q.relative := by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  let u := Coat.topStorm D+1; have hu : 0 ≤ u := by unfold u; linarith [topStorm_one D]
  obtain ⟨b,hb,hH⟩:= exponent_fee G L Q.halo Q.relative Q.ε t u hp (fun x=> grow G L x^2*g x) (show Rate G L t _ from
    (((Rate.power (G:=G) (L:=L) (a:=3/8)).pow 2).mul (Rate.power (G:=G) (L:=L) (a:= -2))).weaken (by push_cast; linarith))
  refine ⟨C,Z,hC,hB.add hA,?_⟩
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hΨ,h,hQ,hF,hY (-4) (by linarith),Q.pay_for L hm hC,(hJ.add (hJ.add hb)) Q.rate ht]
    with x hgθ hΨ h hQ he hV hA hv c f S T hS hF R C' H
  have hΓ:= H.laws.data; have hh:= H.laws.intake
  have hΘ: 0<betaF G x L:=by have he:=hh.height; rw [hΓ.funds.length_eq] at he; linarith
  have hg:0≤g x:= by unfold g; positivity
  have h' := (hΓ.localP)
  obtain ⟨V,y,hG,H'⟩:= h _ _ S T hΓ.funds hS hF h' hΓ.access R hh
  have hΞ:=hH x c f S hΓ.funds.length_eq (by have h:= hΓ.room.sight; omega) (mul_nonneg hu (mul_nonneg (pow_nonneg (show 0≤grow G L x from Real.rpow_nonneg (zero_le_one.trans hgθ) _) _) hg))
  have hl : Sales (radiusB x) Q.relative Q.ε (footprints T R Q.halo (radiusB x)) (fun i=> grow G L x^horn i*rates V y (u*g x) i) (Sum.elim
    (Raw.forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (Q.goal L x) := by
    have ht:= (H'.first.together (hG.together hΞ)).raise ((le_abs_self _).trans hv)
    convert ht using 1
    · rfl
    · funext i; rcases i with i|i|i <;> simp only [Sum.elim, rates,horn]; simp
      ring
    · rfl
  refine ⟨⟨V,y,u,hu,g x,hg,hF,hZ x,(by rw [hΓ.funds.length_eq]; exact hA R.beta (hΓ.funds.length_eq ▸ hh.window.1)),
      store_price _ hl (Real.one_le_rpow hgθ (by norm_num)),?_,?_⟩,hl⟩
  · intro E _ _ _ F X A' v' w' z q ht hX hχ hZ' hM hp F' k p hv
    have ht' := h' F X ht hX hZ'

    obtain ⟨hL,hK⟩:=H'.stamina E F X A' v' w' z q ht hX hχ hZ' hM hp k
    rcases p with p|p
    · by_cases he: Packets.connected S Q.halo X.B p
      swap; · apply Brush.zi (Eventually.of_forall (fun y:E=> if_neg he)) (by unfold stout Mixed.costs; simp only [Sum.elim,if_neg he]; exact le_rfl)
                (show 0≤Z x*1 from mul_nonneg (zero_le_one.trans (hZ x)) zero_le_one)
      have hh' : Healthy (Pressure.temp X.x) (p.dome (Q.halo*X.B)) X.V := by unfold Coat.B; rw [ht] at *; exact hv
      have hX:= hΨ c f S T hS hΓ.funds hΓ.access hΓ.grant E z A' F X R v' q w' ht hχ hX ht' hM hh hp p Q.halo k Q.buys
        (Packets.shares_nonzero S _ _ he) hh'
      apply hX.shimmy (Eventually.of_forall (fun y=> if_pos he))|>.climb _ (show 1≤Z x*1 by rw [mul_one]; exact hZ _)
      unfold stout; simp only [Mixed.costs,Sum.elim,if_pos he,steamP,Target.costs,Buy.quote]; unfold Grant.credit Coat.t; rw [ht,hΓ.funds.length_eq]
    have ha : 0 ≤ twigs R T X.B Q.halo p := add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hv : B x*twigs R T X.B Q.halo p≤Z x*twigs R T X.B Q.halo p := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hy x)) ha
    rcases p with p|p|p
    · exact (hK p).climb le_rfl hv
    · exact (hL p).climb le_rfl hv
    unfold u; rw [← hS]; refine (hQ c f S T F X R ht hχ hΓ.funds.length_eq
      (show 0<W*X.t from mul_pos hw ht'.sails.room.fiery) _ q z A' v' w' hp hM p k _).climb le_rfl ?_
    apply le_trans _ (mul_le_mul_of_nonneg_right (show A x ≤ Z x from le_add_of_nonneg_left (zero_le_one.trans (hv' _))) ha)
    apply le_of_eq; unfold twigs lengths; simp
    exact Or.inl rfl
  intro F X ht hK _ hp K
  have hV' : betaF G x L^(2*(-(2:ℝ)))=g x^2 := by unfold g; rw [mul_comm, Real.rpow_mul hΘ.le, Real.rpow_two]
  exact (he.2 c f S T F X ht hΓ.funds.length_eq (h' F X ht hK hp).sails R (ht.symm ▸ hh) K).trans
    (pow_le_pow_left₀ he.1 (((le_abs_self _).trans hV).trans_eq (by rw [← hV',show 2*(-2:ℝ)=-4 by norm_num])) _)
end Utopia
end YM.ConnectedActivityE6.Blaze.Silica
