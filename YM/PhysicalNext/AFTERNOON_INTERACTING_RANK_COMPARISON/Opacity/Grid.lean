import YM.Extra.MULTISOURCE_BOUNDS.Merger
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Crust
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.TableCosts

/-!
# Uniform θ-tariff grid for exterior sensors with optional BG boosters
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Grid
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display Display.Sew  Marker Milk
    Next.SectorChange.Gaussian Schur Wisps AnalyticNext.ConnectedActivity.Win Local Next.SectorChange.Rows
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ENNReal
variable {c f : Side} {G : Gauge} {S : StepData c f} {x W t q K : ℝ} {A : Stores S} {v : Dyed G S} {P : Teller G} {F : Forest S.ratio}

def marks (G : Gauge) (D : Patch) := Aff.density_variables G D.L + Jewels.gSeat D + 1
lemma fleck_notice (S : StepData c f) (G : Gauge): governs (toes S) (marks G S.patch) := by
  apply Aff.governs_closer _ (Aff.population_add _ _ (show governs (fun i : Cell f=> S.ratio.parent i.1) (Aff.densityF S.patch.L) from Aff.population_copy S.ratio.parent (Aff.population_parent _))
    (Aff.population_add _ _ (Aff.governs_fst c Axis) (Aff.population_add _ _ (Aff.population_physical c)
      (Aff.population_add _ _ (Aff.governs_fst c Axis) (Aff.governs_home S)))))
  have hh:0≤Aff.density_variables G S.patch.L:=by unfold Aff.density_variables Aff.density_home; positivity
  unfold marks Jewels.gSeat; linarith [show 0≤ (S.patch.L.val:ℝ)^4 by positivity]
lemma gauges (D:Patch) : 0< marks G D:= by unfold marks Jewels.gSeat Aff.density_variables Aff.density_home Aff.densityC Aff.densityF; positivity
lemma debt_degree (A : Stores S) (G : Gauge) (F : Forest S.ratio) : governs (m:=In x A F (G:=G)) (Wisps.front A F) (marks G S.patch):= by
  intro Y r
  let H:=univ.filter fun j: Aff.Vars G f=> separation Y (Aff.dcol S j) ≤ r
  let D' := univ.filter fun i:In x A F (G:=G) => separation Y (Wisps.front A F i)≤r
  let j : In x A F (G:=G) ↪ Aff.Vars G f := ⟨fun i=>(i.1.val.val,i.2), fun i k h=>Prod.ext (Subtype.ext (Subtype.ext (congr_arg Prod.fst h))) (congr_arg (Prod.snd (α:=Bond f)) h)⟩
  have hs : D'.map j ⊆ H := by
    intro i hi; obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hk).2⟩
  have ht: Aff.density_variables G S.patch.L ≤ marks G S.patch:= by unfold marks Jewels.gSeat Aff.densityC Aff.density_home Aff.densityF; exact le_trans (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_right zero_le_one)
  apply le_trans (b:= (H.card:ℝ)) _ (Aff.governs_closer _ (Aff.governs_vars (G:=G) S) ht Y r)
  exact Nat.cast_le.mpr ((card_map j ..|>.symm).trans_le (card_le_card hs))

def density (G : Gauge) (D : Patch) (B : ℕ) := marks G D * (1+(2*B:ℕ))^4
lemma den_pos :0 < density G S.patch (radiusB x):= by unfold density; have hm:=gauges (G:=G) S.patch; positivity

def damp (G : Gauge) (K : ℝ) (D : Patch) (B : ℕ) := (8*K*density G D B)⁻¹

-- Does NOT assert T's forecast; every k,A given. One tilt suffices.
local notation "I"=>In x A F (G:=G)
local notation "U"=>damp G K S.patch (radiusB x)
private def heft (L : ℝ) (p : Finset (Fleck S)) (i:I):=
    ∑ j∈p, if separation (toes S j) (front A F i)≤2*radiusB x then damp G L S.patch (radiusB x) else 0
lemma fill_room (C : Gaussian.Table I) (hp : C.PosDef) (hC : Pours C (front A F) (front A F) 0 K) (hk : 0<K) (hq : 0≤q) (a : ℝ) (ht : 0≤a) (p : Finset (Fleck S)):∃ D : Tilt.Plan C, Tilt.total D≤a*Real.exp (1/4-U*q^2)^p.card ∧
    ∀ z, (∀ j∈p, ¬ Toned (A:=A) (F:=F) (G:=G) (2*radiusB x) (toes S j) z q) → a ≤ Tilt.banner D z:= by
  let d:=2*radiusB x
  let u:=U; let H:= density G S.patch (radiusB x); let w:= heft (F:=F) (G:=G) (A:=A) (x:=x) K p
  let F' (j : Fleck S) (i : I):= if separation (toes S j) (front A F i)≤d then u else 0
  have hm:0<H:= den_pos; have hu:0≤u:=by change 0 ≤ (8*K*H)⁻¹; positivity
  have hg : H*u*K = 1/8:= by change H * (8*K*H)⁻¹ * _ = _; field_simp
  have hx (i:I): w i ≤ H*u:= by
    unfold w heft; rw [← sum_filter,sum_const,nsmul_eq_mul]
    let y:= front A F i
    refine mul_le_mul_of_nonneg_right ?_ hu
    let D:= p.filter fun j=> separation (toes S j) y≤d
    change (D.card:ℝ) ≤ H
    refine (Nat.cast_le.mpr (Finset.card_le_card (show D ⊆ _ from ?_))).trans (fleck_notice S G y d)
    exact fun j hj=> mem_filter.mpr ⟨mem_univ _,(separation_comm ..).trans_le (mem_filter.mp hj).2⟩
  let v':= (p.card:ℝ)*u*q^2
  have hw' (j) (i : I): 0≤ F' j i:= by unfold F'; split; exact hu;exact le_rfl
  have hb (i) : ∑ j,w j*|C i j|≤1/8:= by
    apply (Finset.sum_le_sum (g:=fun j=> H*u*|C i j|) (fun j _=> mul_le_mul_of_nonneg_right (hx j) (abs_nonneg _))).trans; rw [← mul_sum,← hg]; exact mul_le_mul_of_nonneg_left (TableCosts.row_budget hC le_rfl i) (mul_nonneg hm.le hu)
  obtain ⟨P,hP,hp⟩:= Tilt.crop_pays hp w (fun _=> sum_nonneg (fun i _=> hw' i _)) v' a ht hb
  refine ⟨P,?_,fun z hz=> hp z ?_⟩
  · have hh (j : Fleck S): ∑ i : I,F' j i * C i i ≤ 1/8 := by
      apply (Finset.sum_le_sum (g:=fun i=> F' j i*K) (fun i _=> ?_)).trans
      · rw [← sum_mul]; unfold F'; rw [← sum_filter,sum_const,nsmul_eq_mul,← hg]; gcongr
        exact debt_degree A G F (toes S j) d
      apply mul_le_mul_of_nonneg_left _ (hw' j i)
      exact (le_abs_self _).trans ((Finset.single_le_sum (f:=fun j=>|C i j|) (fun _ _=>abs_nonneg _) (mem_univ i)).trans (TableCosts.row_budget hC le_rfl i))
    rw [hP,← Real.exp_nat_mul]; apply mul_le_mul_of_nonneg_left _ ht; apply Real.exp_monotone
    have ht' : ∑ i,w i*C i i ≤ (p.card:ℝ)/8:= by
      unfold w heft; simp_rw [sum_mul]; rw [sum_comm]; refine (Finset.sum_le_sum (g:=fun _=> (1:ℝ)/8) (fun i _=> hh i)).trans_eq (by simp; ring)
    unfold v' u; linarith only [ht']
  unfold Tilt.powerAt w heft; simp_rw [sum_mul]; rw [sum_comm]
  refine le_trans ?_ (Finset.sum_le_sum (f:=fun _=>u*q^2) (fun j hj=>?_))
  · simp only [sum_const,nsmul_eq_mul,mul_assoc,v', le_refl]
  have h:=hz j hj; unfold Toned at h; push Not at h; obtain ⟨v,hv,hq'⟩:=h
  apply le_trans _ (Finset.single_le_sum (f:=fun i=>F' j i*z i^2) (fun i _=>mul_nonneg (hw' j i) (sq_nonneg _)) (mem_univ v)); unfold F'; rw [if_pos hv, ← sq_abs (z v)]
  gcongr
end YM.PhysicalNext.InteractingRank.Pump.Grid
