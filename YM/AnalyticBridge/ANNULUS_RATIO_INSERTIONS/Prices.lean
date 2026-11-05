import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Guard
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ledger


/-!
# Ancillary overhead paid in this interface

Haar Jacobians relative to scale, active broad cuts, and **missing**
frozen-link scalars from Fsct. Do *not* bound the whole product cost by
a single-link cost . Explicit local conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix Bloch
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented
open SectorNext.Remainder.Affine Harvest
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Coarse volume for local prices. Need not be connected. -/
def elbow (l : ℕ) := 4*(l+l+1)^4
lemma elbow_room (O : Stores S) (R l B : ℕ) (hl : R≤l*B) :
    (O.dome R).card ≤ elbow l * (B+1)^4 * O.shares := by
  have hi := Corona.halo_size O.place R
  apply hi.trans
  have hh : R+R+1 ≤ (l+l+1)*(B+1) := by rw [Nat.mul_add,Nat.add_mul,Nat.add_mul]; omega
  calc
    _ ≤ 4*O.shares*((l+l+1)*(B+1))^4 := Nat.mul_le_mul (Work.E01.place_card _) (Nat.pow_le_pow_left hh 4)
    _ = _ := by unfold elbow; ring

def vans (L : Side) (l : ℕ) := L.val^4*(Fintype.card Axis)*elbow l

/-- Count fine positions (no injectivity of covers into torus needed). -/
lemma berth (O : Stores S) (R l B : ℕ) (hl : R≤l*B) (s : Finset (Bond f))
    (h : ∀ i∈s,S.ratio.parent i.1∈O.dome R) :
    s.card ≤ vans S.patch.L l * (B+1)^4 * O.shares := by
  let g := S.ratio
  let home : Bond f ≃ ((Site c × Site g.count) × Axis) := Equiv.prodCongr g.splitSites (Equiv.refl _)
  let t := s.map home.toEmbedding
  let H := O.dome R
  have hs : t ⊆ (H ×ˢ (Finset.univ : Support g.count)) ×ˢ (Finset.univ : Finset Axis) := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h j hj, Finset.mem_univ _⟩,Finset.mem_univ _⟩
  have hi := Finset.card_le_card hs
  simp only [t,Finset.card_map,Finset.card_product,Finset.card_univ,site_card] at hi
  have hH := elbow_room O _ _ _ hl
  calc
    _ ≤ (elbow l * (B+1)^4 * O.shares)*S.patch.L.val^4*Fintype.card Axis := hi.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hH))
    _ = _ := by unfold vans; ring

lemma requests (O A : Stores S) (F : Forest S.ratio) (x : ℝ) (R l : ℕ) (h : R≤l*radiusB x) :
    (localDoors O A F x R).card ≤ vans S.patch.L l * (radiusB x+1)^4 * O.shares := by
  let e : Active A x F ↪ Bond f :=
    ⟨fun i => i.val.val, fun _ _ h => Subtype.ext (Subtype.ext h)⟩
  rw [← Finset.card_map (s:=localDoors O A F x R) e]
  apply berth O _ _ _ h
  intro i hi; obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
  exact (Finset.mem_filter.mp hj).2

/-- Held links attributed to this owner (and no others for disjoint
owners at these radii; see consumer). Includes the phase-space scalar
for every such link, even if autoShell is zero. -/
def missing (O A : Stores S) (F : Forest S.ratio) (x : ℝ) := (Finset.univ : Finset (Frozen A x F)).filter
    fun i => S.ratio.parent i.val.val.1∈O.dome (10*radiusB x) ∨
      S.ratio.parent (i.val.val.1+Lattice.step i.val.val.2)∈O.dome (10*radiusB x)



lemma missing_berth (O A : Stores S) (F : Forest S.ratio) (x : ℝ) (hx : 1≤radiusB x) :
    (missing O A F x).card ≤ vans S.patch.L 11 * (radiusB x+1)^4 * O.shares := by
  let e : Frozen A x F ↪ Bond f :=
    ⟨fun i => i.val.val,fun i j h => Subtype.ext (Subtype.ext h)⟩
  rw [← Finset.card_map (s:=missing O A F x) e]
  apply berth O (11*radiusB x) _ _ (le_refl _)
  intro i hi
  obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
  rcases (Finset.mem_filter.mp hj).2 with h|h
  · exact Corona.halo_mono (by omega) (fun _ hi => hi) h
  obtain ⟨k,hk,hl⟩ := halo_spec.mp h
  rw [Stores.dome,halo_spec]
  refine ⟨k,hk,?_⟩
  have hh := separation_triangle k (S.ratio.parent (j.val.val.1+Lattice.step j.val.val.2)) (S.ratio.parent j.val.val.1)
  have ht := Work.E03.parent_step S j.val.val.1 j.val.val.2
  rw [separation_comm] at ht
  change separation k (S.ratio.parent j.val.val.1) ≤ _
  omega

variable (O A : Stores S) (F : Forest S.ratio) (x : ℝ) (V : Config G c)
variable (Y : LinkArray G (Frozen A x F)) (q : Chi) (d : ℝ) (J : ChartRatio G) (a : Prices G (Active A x F))

def patchBudget (R : ℕ) := ∏ i ∈ localDoors O A F x R, extended q J d (tape a i)

def rentals (R : ℕ) := border O A F x R q d a * patchBudget O A F x q d J a R

lemma border_range (R : ℕ) : border O A F x R q d a ∈ Set.Icc (0:ℝ) 1 := by
  let H := localDoors O A F x R
  let f := fun i : Active A x F => broad q d (tape a i)
  have he i : f i ∈ Set.Icc (0:ℝ) 1 := broad_range ..
  change (∏ i∈H, f i) ∈ _
  exact ⟨Finset.prod_nonneg fun i _ => (he i).1,(Finset.prod_le_prod (fun i (_:i∈H) => (he i).1) (fun i _ => (he i).2)).trans (by simp)⟩

lemma rental_border (R : ℕ) (h : rentals O A F x q d J a R ≠ 0) : border O A F x R q d a ≠0 := left_ne_zero_of_mul h

lemma rental_nn (R : ℕ) : 0 ≤ rentals O A F x q d J a R :=
  mul_nonneg (border_range ..).1 (Finset.prod_nonneg fun _ _ => (extended_pos ..).le)

lemma rental_price (R l : ℕ) (h : R≤l*radiusB x) {E : ℝ} (hd : 0<d)
    (hp : ∀ u : G.Color, ‖u‖ ≤ 4*d → |Real.log (J.J u)| ≤ E*‖u‖^2) (he : 0 ≤ E) :
    ‖rentals O A F x q d J a R‖ ≤ Real.exp (((vans S.patch.L l : ℕ):ℝ) *
      ((radiusB x:ℝ)+1)^4 * O.shares * (E*(4*d)^2)) := by
  let B i := extended q J d (tape a i)
  let P := E*(4*d)^2
  have hP : 0≤P := mul_nonneg he (sq_nonneg _)
  have hb (i : Active A x F) : Real.log (B i) ≤ P := (le_abs_self _).trans ((price_extended q hd hp he (tape a i)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min (norm_nonneg _) (by positivity)) (min_le_right ..) 2) he))
  have hc := Nat.cast_le (α:=ℝ).mpr (requests O A F x R l h)
  push_cast at hc
  rw [Real.norm_of_nonneg (rental_nn ..)]; unfold rentals
  apply (mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => (extended_pos ..).le) ((border_range ..).2)).trans
  calc
    _ ≤ ∏ _i∈localDoors O A F x R, Real.exp P := by
      refine Finset.prod_le_prod (fun _ _ => (extended_pos ..).le) (fun i _ => ?_)
      exact (Real.exp_log (extended_pos q J d _)).symm.trans_le (Real.exp_monotone (hb i))
    _ ≤ _ := by rw [← Real.exp_sum]; apply Real.exp_monotone; rw [Finset.sum_const,nsmul_eq_mul]; gcongr

lemma rental_meas (R : ℕ) : Measurable (fun a' : Prices G (Active A x F) => border O A F x R q d a') ∧
    (LocalRatio J → 0<d → 4*d < J.radius → Measurable (fun a' : Prices G (Active A x F) => rentals O A F x q d J a' R)) := by
  have hm (i : Active A x F) : Measurable (fun a' : Prices G (Active A x F) => tape a' i) := (measurable_pi_apply _).comp tape.measurable
  have h : Measurable (fun a' : Prices G (Active A x F) => border O A F x R q d a') :=
    Finset.measurable_fun_prod _ fun i _ => (broad_smooth q d).continuous.measurable.comp (hm i)
  refine ⟨h,fun hi hd he => h.mul (Finset.measurable_fun_prod _ fun i _ =>
    (extended_smooth q hi hd he).continuous.measurable.comp (hm i))⟩

def shortfall (β : ℝ) := Real.exp (-((missing O A F x).card:ℝ)*Real.log (spare J β))

lemma missing_price (hx : 1≤radiusB x) {β : ℝ} {C : ℝ} (hc : - Real.log (spare J β) ≤ C) (hh : 0≤C) :
    shortfall O A F x J β ≤ Real.exp (((vans S.patch.L 11 : ℕ):ℝ) *
      ((radiusB x:ℝ)+1)^4 * O.shares*C) := by
  have hi := Nat.cast_le (α:=ℝ).mpr (missing_berth O A F x hx)
  push_cast at hi
  apply Real.exp_monotone; rw [neg_mul,← mul_neg]; exact le_trans (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)) (mul_le_mul_of_nonneg_right hi hh)

variable {β : ℝ}
/-- Fixed hardware loss for the missing $s_g$, retaining all color
components and the ChartRatio scale. Log of β_hat_f = y here.
No O(#all links) put on the packet.
-/
lemma slots {L : Side} (hJ : LocalRatio J) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x β : ℝ), 1≤SectorNext.Remainder.Scales.y G L x → 0<β → β ≤ 2*SectorNext.Remainder.Scales.y G L x →
    -Real.log (spare J β) ≤ C*(1+Real.log (SectorNext.Remainder.Scales.y G L x)) := by
  let N := (Fintype.card G.ColorIndex:ℝ)
  let a := Real.log (Real.sqrt (2*Real.pi))
  let M := |Real.log J.scale|
  let C := 1 + N*(|a|+Real.log 2+1) + M
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hs := Real.log_nonneg (show (1:ℝ)≤2 by norm_num)
  have hM : 0≤M := abs_nonneg _
  have ha : 0≤|a| := abs_nonneg _
  refine ⟨C,?_,?_⟩
  · unfold C; positivity
  intro x β hy hβ he
  let Y := SectorNext.Remainder.Scales.y G L x
  have hv : 0 ≤ Real.log Y := Real.log_nonneg hy
  have hc := Real.log_le_log hβ he
  change _ ≤ Real.log (2*Y) at hc
  rw [Real.log_mul two_ne_zero ((by change 0<SectorNext.Remainder.Scales.y G L x; linarith):0<Y).ne'] at hc
  let g := coupling β
  have hg : 0<g := coupling_pos hβ
  have hP : 0<(2*Real.pi) := mul_pos (by norm_num) Real.pi_pos
  have hP' := Real.sqrt_pos.mpr hP
  unfold spare
  rw [Real.sqrt_mul hP.le, Real.sqrt_sq hg.le, Real.log_mul (pow_pos (mul_pos hP' hg) _).ne' hJ.scale.ne',Real.log_pow,
    Real.log_mul hP'.ne' hg.ne']; unfold g coupling; rw [Real.log_inv,Real.log_sqrt hβ.le]
  change -(N*(a+- (Real.log β / 2)) + _) ≤ C*(1+Real.log Y)
  have h1 : -a ≤ |a| := neg_le_abs _
  have h2 : -(N*(a+- (Real.log β / 2))) ≤ N*(|a|+Real.log 2+Real.log Y) := by nlinarith only [mul_le_mul_of_nonneg_left (show -(a+- (Real.log β / 2)) ≤ |a|+Real.log 2+Real.log Y by linarith) hN]
  have h3 : -Real.log J.scale ≤ M := neg_le_abs _
  unfold C; nlinarith only [h2,h3,hN,hM,mul_nonneg
    (mul_nonneg hN (add_nonneg ha hs)) hv,mul_nonneg (add_nonneg zero_le_one hM) hv]

/-- Bound local broad, actual Haar ratio, and frozen $s_g$ deficit
by one incidence-priced expenditure from Ledger. Can buy extra `e'`
for caller's other factors (NOT claiming all fit!). -/
def tally (C E : ℝ) (L : Side) (l : ℕ) := 16*E*(vans L l:ℝ)+C*(vans L 11:ℝ)
lemma local_salary {β C E : ℝ} (R l : ℕ) (h : R ≤ l*radiusB x) (n : ℕ) (hnt : 4≤n) (hx : 1≤radiusB x)
    (hd : 0<d) (hd' : d≤1) (hP : ∀ u : G.Color, ‖u‖ ≤ 4*d → |Real.log (J.J u)| ≤ E*‖u‖^2) (hE : 0 ≤ E) (hC : 0≤C)
    (hy : 1 ≤ SectorNext.Remainder.Scales.y G S.patch.L x)
    (he : -Real.log (spare J β) ≤ C*(1+Real.log (SectorNext.Remainder.Scales.y G S.patch.L x))) {H e' : ℝ}
    (hK : AnnulusRatioInsertions.tally C E S.patch.L l + e' ≤ H) :
    let Z c := SectorNext.Remainder.coin G S.patch.L c n x * O.shares
    Real.exp (Z e') * (shortfall O A F x J β * ‖rentals O A F x q d J a R‖) ≤ Real.exp (Z H) := by
  intro Z
  let B := SectorNext.Remainder.Scales.b x
  have hB : (radiusB x:ℝ) + 1=B := add_comm ..
  let L := 1+Real.log (SectorNext.Remainder.Scales.y G S.patch.L x)
  have hL : 1≤L := by have := Real.log_nonneg hy; unfold L; linarith
  have hb : 1≤B := SectorNext.Remainder.Scales.size x
  have hm' : 0≤(O.shares:ℝ) := Nat.cast_nonneg _
  apply (mul_le_mul_of_nonneg_left (mul_le_mul (missing_price O A F x J hx he (mul_nonneg hC (zero_le_one.trans hL)))
    (rental_price O A F x q d J a R l h hd hP hE) (norm_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le).trans
  rw [← Real.exp_add,← Real.exp_add,hB]; apply Real.exp_monotone
  let u := (vans S.patch.L l:ℝ); let v := (vans S.patch.L 11:ℝ)
  have hu : 0 ≤ u := Nat.cast_nonneg _; have hv : 0 ≤ v := Nat.cast_nonneg _
  have hh : B^4 ≤ B^n := pow_le_pow_right₀ hb hnt
  have ht : E*(4*d)^2 ≤ 16*E*L := by apply (mul_le_mul_of_nonneg_left (show (4*d)^2 ≤ 16 by nlinarith) hE).trans; nlinarith
  change Z e'+(v*B^4*_* (C * L) + u*B^4*(O.shares:ℝ)*(E*(4*d)^2)) ≤ _
  have h1 : v*B^4*(O.shares:ℝ)*(C*L) ≤ C*v*B^n*L*(O.shares:ℝ) := by calc
    _ ≤ v*B^n*(O.shares:ℝ)*(C*L) := by gcongr
    _ = _ := by ring
  have h2 : u*B^4*(O.shares:ℝ)*(E*(4*d)^2) ≤ 16*E*u*B^n*L*(O.shares:ℝ) := by calc
    _ ≤ u*B^n*(O.shares:ℝ)*(16*E*L) := by gcongr
    _ = _ := by ring
  have hK' := mul_le_mul_of_nonneg_right hK (show 0≤B^n*L*(O.shares:ℝ) by positivity)
  change e'*B^n*L*↑O.shares+_ ≤ H*B^n*L*↑O.shares
  change (16*E*u+C*v+e')*_ ≤ _ at hK'
  nlinarith only [h1,h2,hK']

end YM.AnalyticBridge.AnnulusRatioInsertions
