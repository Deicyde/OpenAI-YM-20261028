import YM.WilsonBulk.Staves.Flow

/-!
# Paying shift-and-noise for Ward identity all ranks (no scalar limits).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Lattice Laurent Function Filter Bloch Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset Equiv
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {α : Type} {G : Gauge} {u e q j n : ℕ} {c : Side}
open PowerSeries (coeff constantCoeff)
open MvPolynomial (X C homogeneousComponent)
lemma passesW [Fintype α] {W : Formula α} (he : W.IsHomogeneous q) (A : Record α) (ha : Document A) (i : α) (u n : ℕ) :
    homogeneousComponent (σ:=α) n (coeff u (player i (volumeTape A))*W) = if q≤n then ((n-q+1:ℕ):ℝ) • (script (margin (A u (n-q+1)) i)*W) else 0 := by
  rw [reports_with ha]; simp only [sum_mul,map_sum, pure_read _ _ W he]; by_cases h : q≤n
  · rw [sum_eq_single (n-q), if_pos h, if_pos (by omega)]
    · intro a _ ha; exact if_neg (by omega)
    intro h'; rw [ha.cap u _ (by simp only [allowed,mem_range] at h'; omega)]; simp
  rw [if_neg h]; exact sum_eq_zero fun b _=> if_neg (by omega)
lemma proceeding_script (x : Pennant G c) (V : Record (Pennant G c)) (h : Document V) (n : ℕ) (hh : q≤ e) :
    script (margin (proceeding backed V e n q) x)= if x.2.1=coord 0 then ∑ y : Pennant G c,∑ t:Bool, if x.1=lastAt (fret y) t then
      homogeneousComponent (σ:=Pennant G c) n (coeff (e-q) (player y (volumeTape V)) * coeff q (submit (named∘selvedge (fret y)) (motive t y.2.2 x.2.2))) else 0 else 0 := by
  simp_rw [passesW (sock_pure ..) V h]
  rw [proceeding]; split
  next he=>
    rw [margin_scale,postage,post_mark,script_scale,script_escort,pillar,smul_ite,smul_zero]
    simp_rw [if_pos he.2, smul_sum, smul_ite, smul_zero]
  next hz=> simp only [if_neg (c:= q≤n) (fun h=>hz ⟨hh,h⟩),margin_zero,script_zero,ite_self,sum_const_zero]

-- changes-aware extraction. rank n OTHERS. through all periods but branch independent.
lemma farthing (V : Record (Pennant G c)) (h : Regime (volumeTape V)) (hp : Document V) (e n) (x : Pennant G c) :
    script (margin (∑ q∈range (e+1),proceeding backed V e n q) x)=0 := by
  let p := volumeTape V; let P:=Pennant G c
  rw [margin_grabs,script_sum]; by_cases hu:x.2.1=coord 0; swap
  · exact sum_eq_zero fun a ha=> by rw [proceeding_script x V hp n (by rw [mem_range] at ha; omega), if_neg hu]
  have hv := declaration p x.1 x.2.2 h.dance
  let w:= homogeneousComponent (σ:=P) (R:=ℝ) n
  have he (u v : Tape P) : w (coeff e (u*v))= ∑ q∈range (e+1),w (coeff (e-q) u * coeff q v) := by
    rw [mul_comm,PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=> coeff i v*coeff j u),map_sum]; refine sum_congr rfl fun i _=>?_; rw [mul_comm]
  have hx (p : Prop) [Decidable p] (f:ℕ→ Formula P): (if p then ∑ q∈range (e+1),f q else 0)=∑ q∈range (e+1),if p then f q else 0:= by by_cases he:p <;> simp_all
  have hh := congr_arg (fun v:Tape P=> w (coeff e v)) hv; simp_rw [map_zero,map_sum,apply_ite (coeff _),map_zero,apply_ite w,he,map_zero,hx] at hh -- lemma name?
  rw [← permute_three] at hh
  refine Eq.trans (sum_congr rfl fun i hi=> ?_) hh; rw [proceeding_script x V hp n (by rw [mem_range] at hi; omega), if_pos hu]

lemma sentry (V : Record (Pennant G c)) (h : Regime (volumeTape V)) (hp : Document V) (e n : ℕ) :
    (∑ q∈range (e+1),proceeding backed V e n q)=0 := by
  refine margin_force fun x=> ?_; rw [margin_grabs, margin_zero]; refine script_trust (Regular.summed fun i _=> ?_) Regular.zero ?_
  · rw [proceeding]; split; next he=>
      rw [margin_scale,postage,post_mark,spiro,tailBuff,post_mark]; exact (Regular.rank_cast _ _ (polish_ready _)).scaled _
    rw [margin_zero]; exact Regular.zero
  rw [← margin_grabs, script_zero, farthing _ h hp]
end Parapet
end YM.WilsonBulk
