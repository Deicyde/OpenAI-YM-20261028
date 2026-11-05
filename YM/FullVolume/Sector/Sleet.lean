import YM.FullVolume.Sector.Fruit
/-! Unforced label arcs: same literal shape pays ANY moment Rookie. All `V` traces over actual group. -/
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
variable {V:ℝ→ℝ} (W':Lake G L (payE o.eta o.gap o.ample (Census.tubularPrice G L)) (K*j*2) V k)
variable {p:Signal j} {ν α:ℝ} (hc:Clear Q L μ ν x₀ v p) (hr:Clarity H j A' δ ν)
local notation "τ"=> spicesF G r L' (V x₀) K j
-- Geometry fixed through every requested test.Set weights from mixed tree.
def payment (k:ℕ)(t ν α:ℝ)(p:Signal j)(i:Molecule S) := if H.ticketsP 0 0 0 i then t*M.valued ν α p k i else 0
def sky (i:Molecule S):= M.payment (k+j) (τ) ν α p i
lemma pay_valid (t) (hf:0≤t)(i:Molecule S):0≤ M.payment k t ν α p i:=by unfold payment; split; exact mul_nonneg hf (M.valued_pos ..); exact le_rfl
lemma paid_sky (i:Molecule S):0≤ sky (V:=V) (p:=p) (k:=k) (ν:=ν) (α:=α) M i:=pay_valid M _ (M.spicesF_sound _) _
-- same primitive U, not necessarily fare.Ref
local notation "m"=> M.payment (k+j) (τ) ν α p
variable (Y':Margin G L x₀ α δ) (w:Rung) (η:ℝ) (hh : ∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/v)^i)‖ ≤ η)
include M hx he hv hy hU
-- hue variation, from Pattern.Rainbow using Plot.flow.
lemma raining (i:ℝ) (ht':i∈sun)(p:Molecule S) (hE:(roster p).flags=∅) (hH:Healthy (Pressure.temp x₀) (H.unionP p) X.V):
      ∀ᶠ y in 𝓝 s, fringe (vary X (U₀ y)) W o.a p (U.notes i) Q.table Q.halo = shelter (vary X (U₀ y)) W o.a p (U.notes i) Q.table Q.halo:= by
  let V:= U₀; have h0:=U.lay ht'; let R:=U.notes i; let H' := U.beams i h0
  let K:= (planted X p); let Y t y:= vary (K.taggedL t) (V y); have ht:= H'.laws.data
  have hy' : Healthy (Pressure.temp x₀) (H'.unionP p) X.V:= (congr_fun (U.stage i h0) p) ▸ hH
  have hf t: ∀ᶠ y in 𝓝 s,Hue (Y t y):= eventual_hue (((M.plot i h0).rays F (K.taggedL t) hx he hv (planted_valid X p) E V s hy hU).1)
    (ht.localP F (K.taggedL t) hx he (planted_valid X p)).sails
  filter_upwards [eventually_all.mpr hf] with y hh
  let Z:= vary X (V y)
  let a (z:Coat T F):= shelter z W o.a p R Q.table Q.halo
  have hF z : a (Z.rinse z)=a Z := by
    unfold a shelter; rw [show (Z.rinse z).B=Z.B from rfl, show Z.B=radiusB x₀ from congr_arg _ hx]; split
    next h =>
      apply congr_arg likely; funext q
      let I:=podium S G (H'.unionP p) (radiusB x₀); let b X:= bars I (F:=F) (T:=T) X p R Q.table W o.a Q.halo
      change b ((preps (vary X (gauge z (V y))) (roster p)).taggedL q)=b ((preps Z (roster p)).taggedL q)
      have ht k : b (vary (K.taggedL q) k)=b ((preps (vary X k) (roster p)).taggedL q) := Blaze.spices p H' X hx k k (fun _ _ _=>rfl) hy' hE q
      unfold Z; rw [← ht, ← ht]
      change b ((Y q y).rinse z)=b (Y q y)
      unfold b I; rw [← chargedU];
      apply Stained.coastal (show Intake P T (Y q y).x R from hx.symm ▸ H'.laws.intake)
        (show ShellAccess S G (Y q y).x W (Y q y).width o.γ from (by change ShellAccess S G X.x W X.width o.γ; rw [hx,he]; exact H'.laws.data.access))
        _ _ _ z Q.table_exists _ _ (hh q)
      · apply mul_pos o.large; unfold Coat.t; change 0<Pressure.fiery G X.x _; rw [hx]; exact H'.laws.data.room.fiery
      unfold Coat.t; change 4*_ * Pressure.fiery G X.x _ < _; rw [hx,H'.laws.data.funds.length_eq]; exact H'.laws.data.covers
    next => rfl
  change (∫ z, a (Z.rinse z) ∂ _) = a Z; simp_rw [hF]; simp
include hc hr W' hh Y'
lemma promotes (i:H.ThinP) (hJ:Healthy (Pressure.temp x₀) (H.unionP i.val) X.V) :
    let f t x:= fringe (vary X (U₀ x)) W o.a i.val (U.notes t) Q.table Q.halo
    Brush j (η*(m i.val)) 1 (fun x=> FullVolume.Ray.trace w (fun t=>f t x)) s:=by
  intro f
  let V₀:= fun t x=> shelter (vary X (U₀ x)) W o.a i.val (U.notes t) Q.table Q.halo
  have hA :0≤η:= (norm_nonneg _).trans (hh 0)
  suffices ht:Brush j (η*(m i.val)) 1 (fun x=> FullVolume.Ray.trace w (fun t=> V₀ t x)) s from ht.shimmy (by
    have hf (t:↑FullVolume.Ray.sun): f t=ᶠ[𝓝 s] V₀ t:= raining M X hx he hv hy hU t t.2 i.val i.2.2 hJ
    filter_upwards [(Finset.eventually_all _).mpr (fun i (_:i∈w.support)=> hf i)] with x ht; exact Finset.sum_congr rfl (fun i hi=> congr_arg _ (ht i hi)))
  let D t:= shieldS (U:=U) (X.taggedL t) U₀ -- fixed on plant
  let Y:= planted X i.val
  let v(t:S.Choices) (x:ℝ):= shieldS (U:=U) (Y.taggedL t) U₀ i.val x
  by_cases h: Ac.Spark H.supportP i.val ∧ Matter.troupe T R Q.halo w₀ i.val
  · rw [payment,if_pos ((H.attends ..).2 h.1)]; let d':=(Fintype.card S.Choices:ℝ)⁻¹; let a:=η*((τ)*M.valued ν α p (k+j) i.val)
    have he' (t:S.Choices): Brush j a 1 (fun x=> FullVolume.Ray.trace w (fun i=>v t i x)) s:= sworn M (Y.taggedL t) hx he hv (planted_valid X i.val) hy hU W' hc hr Y' w η hh i.val h.2 hJ -- order
    refine (((Brush.spree Finset.univ _ (fun _=> a) zero_le_one (fun t _=> he' t)).smul d').climb ?_ le_rfl).shimmy (Eventually.of_forall fun y=>?_)
    · have hh : (Fintype.card S.Choices:ℝ)≠0:= by exact_mod_cast (Fintype.card_ne_zero (α:=S.Choices))
      unfold d'; rw [norm_inv,Real.norm_natCast,sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ hh a]
    change ∑ z∈w.support,w z*V₀ z.val y = _
    have hg (z: sun): V₀ z y= d' * ∑ t,v t z y:=by
      have hp:=U.lay z.2; let P:= U.beams _ hp
      change (if Ac.Spark _ i.val ∧ _ then _ else _)= _
      have ha : P.supportP=H.supportP:=(U.arena z.val hp).symm
      have hF : P.unionP i.val=H.unionP i.val:= (congr_fun (U.stage z.val hp) _).symm
      have ht : (vary X (U₀ y)).B=radiusB x₀:= congr_arg _ hx
      rw [ht,if_pos (show Ac.Spark (areas (U.notes z) T Q.halo w₀) i.val ∧ Matter.troupe T (U.notes z) Q.halo w₀ i.val from ⟨(show Ac.Spark P.supportP i.val from ha.symm ▸ h.1),(U.troupe_hold z.val hp i.val).1 h.2⟩)]
      refine congr_arg (d' * ·) (Finset.sum_congr rfl fun t he₁=>?_)
      have hh:Healthy (Pressure.temp x₀) (P.unionP i.val) X.V:= hF.symm ▸ hJ
      unfold v shieldS; rw [← hF]; exact (spices i.val P X hx (U₀ y) (U₀ y) (fun _ _ _=>rfl) hh i.2.2 t).symm
    change ∑ z∈w.support,w z*V₀ z.val y = d' * ∑ t,∑ z∈w.support,w z*v t z.val y; rw [Finset.sum_comm ,mul_sum]; apply sum_congr rfl; intro z hz; rw [hg z,mul_left_comm,Finset.mul_sum (a:=w z)] -- syntax
  have hs x t (ht:t∈FullVolume.Ray.sun): V₀ t x=0 := by
    unfold V₀ shelter; split
    next h1=> have he:= h1; rw [show (vary X (U₀ x)).B=w₀ from congr_arg _ hx] at he; exact False.elim (h ⟨(U.arena t (U.lay ht)).symm ▸ he.1,(U.troupe_hold t (U.lay ht) i.val).2 he.2⟩)
    rfl
  apply Brush.zi _ (mul_nonneg hA (M.paid_sky ..)) zero_le_one; filter_upwards with y; unfold FullVolume.Ray.trace; exact Finset.sum_eq_zero fun i _=> smul_eq_zero.mpr (Or.inr (hs _ _ i.property))
end Lyre
end YM.ConnectedActivityE6.Empire
