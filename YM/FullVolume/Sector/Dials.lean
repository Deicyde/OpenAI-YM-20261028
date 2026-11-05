import YM.FullVolume.Sector.Grant
/-! Revenue: same geometry and shots even when λ prices now in all coefficient directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
section equality
variable {H':Rep G f}
def units (T : Tube G S) (R:Rep G f) := Sum.elim (Raw.forcedExtra R) (Sum.elim (exCharge T R) (fun _ : WarningAt c f=> (0:ℕ)))
-- for Sales tribe tally. Commit all occupancy
lemma surveyed (h: Facing R H') (m B : ℕ): footprints T H' m B= footprints T R m B ∧ units T H'=units T R:=by
  obtain ⟨u,c,⟨v,d,e₁,e₂⟩,v',p,t⟩:= R; obtain ⟨u',c',⟨w,f',d₁,d₂⟩,w',p',t'⟩:= H'; obtain ⟨ht,hh,h',hb,he,-,-⟩:= h; cases hh; cases ht; cases h'; cases hb; cases he; exact ⟨rfl,rfl⟩
end equality
section commerce
lemma tribute {a ε : ℝ} {ι : Type*} {f g:ι→ℝ} {X:ι→ Support c} {b : ι → ℕ} {B:ℕ} (h:Sales B a ε X f b d) (hr:Sales B a ε X g b n): Sales B a ε X (f+g) b (d+n):=by
  refine ⟨fun i=>add_nonneg (h.nonneg i) (hr.nonneg i),fun i=> ?_⟩
  convert budget_plus (h.hit i) (hr.hit i) using 2 with z; split; next ht=> unfold tariff; dsimp only [Pi.add_apply]; ring
  simp
lemma suite_sum {ι q:Type*}{a ε:ℝ} {v:q→ℝ}{B:ℕ} {Z:ι→ Support c} [Fintype q] (X:q→ι→ℝ) (b:ι→ℕ) (h:∀ i,Sales B a ε Z (X i) b (v i)): Sales B a ε Z (∑ i,X i) b (∑ i,v i):=by
  classical
  suffices h':∀ J:Finset q,Sales B a ε Z (∑ i∈J,X i) b (∑ i∈J,v i) from h' _
  intro J; induction J using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact ⟨fun _=>le_rfl,fun _=>by simp [tariff,SumBudget]⟩
  | insert i J hi hj=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact tribute (h i) hj
end commerce
namespace Lyre
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K) (q:Signal j)
local notation "W₀"=> radiusB x₀
local notation "C₀"=> Q.goal L x₀
-- Canon. v price function
abbrev billK i:=(FullVolume.Ray.bounty (k:=2) trio*v^2)*M.countsK i
abbrev billE i:=(q.A*v^2)*M.countsE i
abbrev ledger (a:ℝ):= rates (M.billK) (M.billE q) a
abbrev salary (q:Signal j) (v:ℝ):=( (FullVolume.Ray.bounty (k:=2) trio+q.A)*v^2+1)
abbrev weft := M.pole.stencil.M*M.pole.stencil.rad
lemma fortify : Sales (W₀) Q.relative Q.ε (footprints T R Q.halo W₀) (M.ledger q M.weft) (units T R) (salary q v * (3*C₀+C₀)):=by
  let V i:= M.bline i |>.stencil; let k i:= (V i).flair; let H:=M.pole.stencil; let f:Alphabet c f→ℝ:=(∑ i,k i)+H.flair
  have hp (i): Sales W₀ Q.relative Q.ε (footprints T R Q.halo W₀) (k i) (units T R) C₀:= by
    have he := (surveyed (T:=T) (U.seats _ (U.lay (trio i).2)) Q.halo W₀)
    rw [← he.1,← he.2]; exact (V i).uses
  have he := suite_sum (v:=fun _=> C₀) k (units T R) hp
  rw [Finset.sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin] at he; norm_cast at he
  have hf : Sales W₀ Q.relative Q.ε _ f (units T R) _:= tribute he (show Sales W₀ Q.relative Q.ε (footprints T R Q.halo W₀) H.flair (units T R) C₀ from H.uses)
  have hS : FullVolume.Ray.bounty (k:=2) trio*v^2 ≤ salary q v:=by unfold salary; rw [add_mul]; linarith only [mul_nonneg q.pos (sq_nonneg v)]
  have hT:q.A*v^2≤ salary q v:=by unfold salary; rw [add_mul]; linarith only [mul_nonneg (FullVolume.Ray.bounty_nn (k:=2) trio) (sq_nonneg v)]
  have hv : 1≤ salary q v:=by unfold salary; exact le_add_of_nonneg_left (mul_nonneg (add_nonneg (FullVolume.Ray.bounty_nn (k:=2) trio) q.pos) (sq_nonneg _))
  refine hf.shift (zero_le_one.trans hv) ?_ ?_
  · rintro (i|i|i)
    · exact mul_nonneg (mul_nonneg (FullVolume.Ray.bounty_nn (k:=2) trio) (sq_nonneg _)) ((M.k_pos 0 i).trans (M.k_rise 0 i))
    · exact mul_nonneg (mul_nonneg q.pos (sq_nonneg _)) ((M.l_pos 0 i).trans (M.l_rise 0 i))
    exact mul_nonneg H.positive H.awake
  rintro (i|i|i)
  · unfold f; simp_rw [Pi.add_apply,Finset.sum_apply]; exact mul_le_mul hS (le_add_of_nonneg_right (H.uses.nonneg (.inl i))) (sum_nonneg fun j _=> M.k_pos j i) (zero_le_one.trans hv)
  · unfold f; simp_rw [Pi.add_apply,Finset.sum_apply]; exact mul_le_mul hT (le_add_of_nonneg_right (H.uses.nonneg (.inr (.inl i)))) (sum_nonneg fun j _=> M.l_pos j i) (zero_le_one.trans hv)
  let x:ConnectedActivityE6.Alphabet c _:=.inr (.inr i); apply le_trans _ (le_mul_of_one_le_left (hf.nonneg x) hv)
  unfold f; simp_rw [Pi.add_apply,Finset.sum_apply]
  exact le_add_of_nonneg_left (sum_nonneg fun j _=> (V j).uses.nonneg x)
end Lyre
end YM.ConnectedActivityE6.Empire
