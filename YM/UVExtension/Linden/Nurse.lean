import YM.UVExtension.Linden.Hazel
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
open March Greenbelt Ursell Trees Concert Daisy.Charity
noncomputable def coined (Q: Target G P)(k:ℕ) := Real.exp (Q.relative*(k+1)*Footprint.preCost (Q.halo+5))
noncomputable def prices (M:Leaf R)(k:ℕ) := M.weight* Copse.worth k R.p.B R.p.supportExponent M.crest
private lemma toes (d:ℕ)(hf: Daisy.foam Q L)( _H0:H=H)(hp: R.p.B ≤2*radiusB x)(Y:Leaf R) : Q.relative * Copse.cover d (radiusB x) (H.supportP (Y.turn.badge S)) ≤ Q.relative * (d+1)*Footprint.preCost (Q.halo+5)+ Q.ε * Copse.cover d R.p.B Y.crest:= by
   let b:=radiusB x; have hb:0<b:= lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1; let h:= Copse.mutate d b S.ratio R.p.B Q.halo Y.crest hb hp
   rw [show H.supportP (Y.turn.badge S)= Footprint.enlargement S.ratio Q.halo b (RG.inspected Y.crest) from Y.turn.badge_area R T Q.halo _]
   let u:= Q.relative; have hh : 0 ≤ u:=by unfold u Target.relative; linarith [Q.bound,Q.pos,Q.usable]
   have hl:u*Footprint.conversion S.ratio (Q.halo+5) ≤ Q.ε:= by unfold Footprint.conversion; rw [show S.ratio.count=L from H.laws.data.funds.length_eq]; exact hf
   refine (mul_le_mul_of_nonneg_left h hh).trans ?_; change u*(_*_+_*_) ≤ _; rw [mul_add,←mul_assoc,←mul_assoc]; gcongr

lemma capitalSup (d:ℕ)(hf: Daisy.foam Q L)(hp: R.p.B ≤2*radiusB x)(Y:Leaf R): ceiling (H:=H) d Y ≤ coined Q d * prices Y d:=by
    have he:= toes d hf (show H=H from rfl) hp Y; let i:= Copse.cover d R.p.B Y.crest
    have ht: Y.weight ≥0:=Y.profit; unfold ceiling coined prices Copse.worth; rw [mul_left_comm _ Y.weight,←Real.exp_add]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) ht
    have hC:= H.laws.intake.exponent; have hk:= Q.grants.1; have hh: Q.exp+Q.δ ≤ Q.relative:=by unfold Target.relative; linarith [Q.usable]
    refine ((mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) _)).trans he).trans (add_le_add_right (mul_le_mul_of_nonneg_right (show Q.ε≤R.p.supportExponent by linarith only [hC,hk,Q.usable]) (Nat.cast_nonneg (α:=ℝ) _)) _)
noncomputable def scalarM (Q: Target G P)(_x U v₀ v₁ r:ℝ)(k j:ℕ):= U*(1+v₀+2*(v₁+r))^j * polyPrice Q.ε (k+j) *coined Q 0
lemma capitalsE  {C₀:ℝ}(M:Leaf R)(Y: Mojo Q o L μ A x d v₁ j χ) (hF:Festa Q L H V w g) (N: Bower Q o L S.patch μ χ A b x j K u B C r d n) {h : Q.rate ≤ γ}{h' : γ<0} (X': Outliner N hF γ h h' K' v₀ C₀ n' k) (hf: Daisy.foam Q L) (hp:R.p.B ≤ 2*radiusB x) : reasons (H:=H) M k j K' v₀ v₁ r ≤ scalarM Q x K' v₀ v₁ r k j*prices M 0:=by
   have he:= toes 0 hf (show H=H from rfl) hp M; simp_rw [Copse.one] at he; have hC:= H.laws.intake.exponent; have hc:= Q.grants.1; let u:= coverNumber R.p.B M.crest
   have hk : 0 ≤ K'*(1+v₀+2*(v₁+r))^j:=by
      let t:_:= (Concert.aperture hF).call (Classical.choice (canvas_nonempty (ι:=ι) (altitude (H:=H)) hF.margin)); let hv:= (Concert.aperture hF).within (Classical.choice (canvas_nonempty (ι:=ι) (altitude (H:=H)) hF.margin)); let H:= Outliner.dealP N hF X' t hv; have h:= Y.funded; have hh:= H.conduit.active; have hp:= X'.size; have ht:= X'.good; positivity
   let v:= K'*(1+v₀+2*(v₁+r))^j *polyPrice Q.ε (k+j)*M.weight; have hv:0≤v:=mul_nonneg (mul_nonneg hk (by unfold polyPrice; have h:=Q.usable; positivity)) M.profit; let i:= coverNumber (radiusB x) (H.supportP (M.turn.badge S))
   unfold reasons currency prices Copse.worth scalarM coined
   rw [Copse.one]; calc
      _ = v* Real.exp (Q.relative*i +2*Q.ε*(u:ℝ)):=by unfold v u i; rw [Real.exp_add]; ring
      _ ≤ v*Real.exp ((Q.relative*((0:ℕ)+1)*Footprint.preCost (Q.halo+5)) + R.p.supportExponent*(u:ℝ)):= by
        apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) hv; have hv:3*Q.ε≤R.p.supportExponent:=by linarith only [Q.usable,hC,hc]
        unfold i u; push_cast at *; nlinarith only [he,mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg (α:=ℝ) u)]
      _ = _:=by unfold v u; rw [Real.exp_add]; push_cast; ring
end YM.UVExtension.Linden
