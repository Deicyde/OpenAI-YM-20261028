import YM.FullVolume.Sector.Hinge
/-! Real vertex formula on extended parameter windows. Includes exact Jacobian exponent scaling. No comparing unrelated Haar kernels. -/
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
variable {F : Tree.Forest S.ratio}
namespace Tune
variable (U : Tune H v δ) (X : Coat T F)
local notation "Λ"=> U.pole
local notation "β"=> R.beta
local notation "w₀"=> radiusB x₀
local notation "B₀"=> U.notes
include U
lemma normed : 1≤ v := U.pole.price
lemma lay {t:ℝ} (h:t∈sun): |t| ≤6*v:= (abs_le.mpr h).trans (by linarith [U.normed])
lemma away (i:ℝ) (j:Fin (2*k+1)): |v*(Λ).seat i j| ≤6*v:=by rw [abs_mul,abs_of_pos (Λ).full.1,mul_comm v]; exact mul_le_mul_of_nonneg_right ((Λ).realms ..) (Λ).full.1.le
lemma plot_rel (t:ℝ) (ht : |t|≤6*v) : (U.notes t).beta=β*(Λ).flow t^2:=by rw [← U.pitch _ ht]; exact (pledge (U.seats t ht)).symm
lemma arena (t:ℝ)(ht:|t|≤6*v) : H.supportP = (U.beams t ht).supportP:= Match.same_area (U.seats t ht).3 (U.seats t ht).reg (U.seats t ht).forced
lemma stage (t:ℝ)(ht:|t|≤6*v) : H.unionP = (U.beams t ht).unionP:=by unfold Cash.unionP; rw [U.arena t ht]
lemma length (t:ℝ)(ht:|t|≤6*v) : ConnectedActivityE6.lengths T R=ConnectedActivityE6.lengths T (U.notes t):=by
  have he:= U.seats t ht
  rcases R with ⟨x,y,⟨b,c,e,f⟩,r,u,v₀⟩
  generalize hF: U.notes t=Y at *; obtain ⟨x',y',⟨b',c',e',f'⟩,r',u',v₁⟩:=Y
  obtain ⟨hr,hc,hp,hX,hE,ha,hb⟩:=he; cases hr; cases hp; cases hc; cases hE; cases hX; rfl
lemma troupe_hold (t:ℝ)(ht:|t|≤6*v) (p:Molecule S): Matter.troupe T R Q.halo w₀ p ↔ Matter.troupe T (U.notes t) Q.halo w₀ p:=by
  unfold Matter.troupe Contract.sealed Contract.incidence; rw [(U.seats t ht).forced]
lemma tune_span (t:ℝ)(ht:|t|≤6*v) : spanW T R (radiusB x₀) Q.halo=spanW T (U.notes t) (radiusB x₀) Q.halo:=by
  have he:=U.seats t ht
  -- via proof irrelevance. keep
  rcases R with ⟨x,y,⟨b,c,e,f⟩,r,u,v₀⟩
  generalize hF: U.notes t=Y at *; obtain ⟨x',y',⟨b',c',e',f'⟩,r',u',v₁⟩:=Y
  obtain ⟨hr,hc,hp,hX,hE,ha,hb⟩:=he; cases hr; cases hp; cases hc; cases hE; cases hX; rfl
lemma melody (i:ℝ) (hi:|i|≤6*v) :
    Real.log (measure_g Q.table (B₀ i).beta)-Real.log (measure_g Q.table β)= -(Fintype.card G.ColorIndex:ℝ)* Real.log ((Λ).flow i):=by
  have ht:= U.seats i hi
  let w:ℝ:= Real.sqrt (2*Real.pi); have hw:0<w:=by unfold w; positivity
  have h0:= Q.table_exists.scale
  obtain ⟨ha,hb,hc,hK,hZ⟩:= uplift ht
  let v:= Fintype.card G.ColorIndex
  let V:= measure_g Q.table (B₀ i).beta
  rw [← pitch U i hi]; apply sub_eq_iff_eq_add.mpr
  have hh : measure_g Q.table R.beta= V*((low R (B₀ i))^v) :=by
    unfold V measure_g; rw [mul_assoc, ← mul_pow, mul_assoc, hK]
  have hV:0<V:= by change 0< Q.table.scale * (w*Coat.gStep _)^v; positivity
  rw [hh,Real.log_mul hV.ne' (pow_pos hc _).ne',Real.log_pow]; unfold v V; ring

def count (p : Stores S) := (X.pens p).card*Fintype.card G.ColorIndex
lemma lit (i:ℝ) (hi:|i|≤ 6*v) (u:Directions G f) (V:Config G f) (M:Finset ℕ) (p : Stores S) :
    Polar.stock X o.a (U.notes i) W Q.table u V M p= Polar.stock X o.a R W Q.table u V M p * (Λ).flow i^(count X p)*Real.exp ((Λ).sqcost i*(β*(chalky X u V p+crispy X p))):=by
  rw [stockMoon o.a W (U.seats i hi),melody U i hi, plot_rel U i hi]
  simp_rw [mul_assoc]; apply congr_arg
  let g:= (Λ).flow i; have hu : 0<g:= zero_lt_one.trans_le ((Λ).moves i hi).1
  rw [← Real.exp_log (pow_pos hu (count X p)), Real.log_pow, ← Real.exp_add]; apply congr_arg; unfold Fold.sqcost count; push_cast; unfold g; ring
end Tune
end YM.ConnectedActivityE6.Empire
