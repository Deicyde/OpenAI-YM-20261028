import YM.FullVolume.Sector.Post
/-! Optional alphabet repricing without losing aperture on each shape. -/
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
namespace Lyre
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
local notation "ψ" => U.pole
variable (X : Coat T F)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U₀:E→ Config G c} {s:E} (hx:X.x=x₀)(he:X.width=o.K)(hv:X.χ=χ)(hm:X.manifest)(hy:U₀ s=X.V)(hU:Mode U₀ s j u)
variable (z:Air f G)
local notation "Λ" => U.pole
local notation "β"=> R.beta
local notation "w₀"=> radiusB x₀
local notation "I₀" => X.input (worldZ X β z)
local notation "f₀" => fun i=> steer X A (worldZ X β z) (U₀ i)
local notation "z₀" => fun i=> course X A β z (U₀ i)
local notation "Yd"=> fun i=> vary X (U₀ i)
section amounts
-- Ruler input.
def trio (j:Fin 3): ↑sun := ⟨(j.val:ℝ)-1,by have hp : (j.val:ℝ) ≤ (2:ℕ):= Nat.cast_le.mpr (Nat.le_of_lt_succ j.isLt); change _ ≤ _ ∧ _ ≤_; push_cast at hp; constructor<;>linarith [Nat.cast_nonneg (α:=ℝ) j.val]⟩
lemma in_trio: Injective (fun i=> (trio i).val):= fun i j h=> Fin.ext (Nat.cast_injective (R:=ℝ) (sub_left_inj.mp h))
-- posterior pilot at all triples
abbrev bline (i:Fin 3):= M.plot (trio i).val (U.lay (trio i).property)
abbrev shape (p:Head S):= r*spanW T R w₀ Q.halo p
abbrev countsE (i:LogIndex c f) := ∑ j:Fin 3,(M.bline j).stencil.goalsL i
abbrev countsK i := ∑ j:Fin 3,(M.bline j).stencil.goalsK i
lemma k_pos i l: 0≤ (M.bline i).stencil.goalsK l:=(M.bline i).stencil.uses.nonneg (Sum.inl l)
lemma l_pos i l: 0≤ (M.bline i).stencil.goalsL l:=(M.bline i).stencil.uses.nonneg (.inr (.inl l))
lemma upbeat i l: (M.bline i).stencil.goalsL l ≤ Q.goal L x₀:= by
  apply ((M.bline i).stencil.uses).atom (by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]) Q.usable.le (Sum.inr (Sum.inl l)); exact exChart ..
lemma k_rise i l: (M.bline i).stencil.goalsK l ≤ countsK M l:= Finset.single_le_sum (fun i _=> k_pos M i l) (mem_univ i)
lemma l_rise i l: (M.bline i).stencil.goalsL l ≤ countsE M l:= Finset.single_le_sum (fun i _=> l_pos M i l) (mem_univ i)
lemma total_l i: countsE M i ≤ 3*(Q.goal L x₀):= (sum_le_sum (fun j (_:j∈univ)=>upbeat M j i)).trans_eq (by simp)
end amounts
section logs
variable (f₁:Finset ℕ)
omit [FiniteDimensional ℝ E]
-- use V held; ink extends scalar
lemma mural (g:ℝ→ℝ)(Y:Coat T F) (z:Air f G)(u:Directions G f) (V:Config G f) (i:LogIndex c f)
    (h: Set.EqOn g (fun t=> logMoment Y o.a (U.notes t) Q.table u V (U.pole.flow t • z) i) sun) : ∃ f, Set.EqOn f g sun ∧ FullVolume.Ray.ink 2 f := by
  by_cases he: oldVac c f i
  · let n:= logMoment Y o.a R Q.table u V z i
    let t(a:ℝ):= if flips c f i then n*(U.pole.flow a*U.pole.flow a) else n
    refine ⟨t,fun x hx=>?_ ,?_⟩
    · have hf:= U.seats _ (U.lay hx); unfold t n; rw [h hx]; dsimp only; rw [← U.pitch x (U.lay hx), flicker o.a hf _ _ _ _ _ _ he]; split_ifs<;> ring
    unfold t; split
    next hz =>exact FullVolume.Ray.ink.scale _ ((FullVolume.Ray.ink.straight (U.pole.peak) (U.pole.slope)).docket (FullVolume.Ray.ink.straight (U.pole.peak) (U.pole.slope)))
    exact FullVolume.Ray.ink.termC _
  unfold oldVac at he; push Not at he; obtain ⟨i,rfl⟩:=he
  obtain ⟨f,hf,hK⟩:=U.onto V i; let a:= Y.enforce (2*o.a) u (Y.plaza (Raw.space T 0 Y.B R (.inl i)))
  refine ⟨_,fun x hx=>?_, FullVolume.Ray.ink.scale (-a) hK⟩
  rw [h hx]; change -a * _= -(U.notes x).activities.regularOccurrence _ _ V * Y.enforce _ _ (Y.plaza _)
  rw [hf hx, ← location (T:=T) (U.seats x (U.lay hx))]; unfold a; ring
include M
lemma lured (Y:Coat T F) (u:Directions G f) (V:Config G f)(i:ℕ): ∃ f, Set.EqOn f (fun t=>Polar.sheath Y o.a (U.notes t) u V i) sun ∧ FullVolume.Ray.ink 2 f := by
  obtain ⟨f,h,hK⟩:= U.quote V i; let s:= Y.enforce (2*o.a) u (Y.plaza (forcedFoot S.ratio 0 Y.B R i)); refine ⟨_,fun i hi=>?_,FullVolume.Ray.ink.scale s hK⟩
  dsimp only; rw [h hi]; unfold sheath s; rw [← pointed (S:=S) (U.seats i (U.lay hi)),mul_comm]
omit M
end logs
section
-- specialize with common A prices from White (only Log, pass tuple)
structure Signal (j:ℕ) where
  A : ℝ
  B : ℝ
  pos : 0≤A
  plus : 1≤B
  emits : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (p v d:ℝ) (f:ℝ→E→ℝ), 1≤p→v≤1/2 → B*p^2*v≤1 → (∀ i, Brush j v d (fun x=>Real.exp (f (trio i).val x)-1) x) → (∀ y:E,∃ g:ℝ→ℝ,Set.EqOn g (fun t=>f t y) sun∧ FullVolume.Ray.ink 2 g) → Weigh j x p (A*p^2*v) d (fun t x=> Real.exp (f t x)-1)
lemma signed_signal (j:ℕ): Nonempty (Signal j):= by obtain ⟨A,B,hb,ht,h⟩:= FullVolume.Ray.faded j (k:=2) trio in_trio; exact ⟨⟨A,B,hb,ht,h⟩⟩
include M hx he hv hm hy hU
variable (q:Signal j) (hk : 3*Q.goal L x₀ ≤ 1/2) (hT: q.B*v^2*(3*Q.goal L x₀) ≤1)
lemma hatched (k:Finset ℕ) (i:ℕ) (hZ:Healthy (Pressure.temp X.x) (H.supportP (.inr (.inl i))) X.V) :
    Weigh j s v ((FullVolume.Ray.bounty (k:=2) trio*v^2)*M.countsK i) (shape (R:=R) (Q:=Q) (T:=T) (x₀:=x₀) (r:=r) (.inr (.inl i))) (fun t x=> vertex M X U₀ z k (Sum.inr (Sum.inl i)) t x):=by
  apply starpath (k:=2) trio in_trio U.normed (Finset.sum_nonneg fun j _=>M.k_pos j i)
  · intro j; exact (emitted M X hx he hv hm hy hU z (U.lay (trio j).property) _ k hZ).climb (M.k_rise j i) le_rfl
  intro y; exact lured M (Yd y) (f₀ y) I₀ i
include hk hT
lemma loglift (k:Finset ℕ)(i:LogIndex c f) (hZ:Healthy (Pressure.temp X.x) (H.supportP (.inr (.inr (.inl i)))) X.V) : Weigh j s v (q.A*v^2*M.countsE i) (shape (R:=R) (Q:=Q) (T:=T) (x₀:=x₀) (r:=r) (Alabaster.logKey S i)) (fun t x=> vertex M X U₀ z k (Alabaster.logKey S i) t x):=by
  let F t (x:E):= logMoment (Yd x) o.a (U.notes t) Q.table (f₀ x) (I₀) (U.pole.flow t • (z₀ x)) i
  apply q.emits E s _ _ _ F U.normed ((M.total_l i).trans hk) ?_ ?_ ?_
  · exact (mul_le_mul_of_nonneg_left (M.total_l _) (mul_nonneg (zero_le_one.trans q.plus) (sq_nonneg _))).trans hT
  · intro j; exact (emitted M X hx he hv hm hy hU z (U.lay (trio j).property) _ k hZ).climb (M.l_rise j i) le_rfl
  intro y; exact mural (U:=U) (fun t=> F t y) (Yd y) (z₀ y) (f₀ y) I₀ i (fun _ _=>rfl)
omit hk hT
lemma alerts (k:Finset ℕ)(i: WarningAt c f) (hZ:Healthy (Pressure.temp X.x) (H.supportP (.inr (.inr (.inr i)))) X.V) : Weigh j s v M.pole.stencil.M (shape (R:=R) (Q:=Q) (T:=T) (x₀:=x₀) (r:=r) (.inr (.inr (.inr i)))) (fun t x=> vertex M X U₀ z k (.inr (.inr (.inr i))) t x):=by
  let V(y:E) := Polar.sprinkle (Yd y) o.a R W (f₀ y) (I₀) k i
  have hz := M.pole.stencil.stream E F X U₀ (f₀) (z₀) s z hx he hv hm hU ((M.pole.rays F X hx he hv hm E U₀ s hy hU).2 z|>.1) k _ hZ
  rw [show X.B=w₀ from congr_arg _ hx] at hz
  exact (FullVolume.Ray.Weigh.still (f:=V) hz U.normed).cong (fun t ht=> Eventually.of_forall fun y=> (alarmWhistle o.a _ (U.seats t (U.lay ht)) _ k _ _ i).symm)
end
end Lyre
end YM.ConnectedActivityE6.Empire
