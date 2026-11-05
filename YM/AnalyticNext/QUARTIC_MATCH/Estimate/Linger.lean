import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Collective


/-!
# Patch supports; lift prices stay pre-L even with contacts
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

namespace Yard
variable {c f : Side} (S : StepData c f)
local notation "L" => S.patch.L
local notation "r" => S.patch.radius
local notation "l" => S.patch.L.val
local notation "V" => S.patch.Points
local notation "k" => S.patch.J

def pScale (i : ℕ) := (2*(i+3:ℝ)+1)^4
lemma pScale_ge (i : ℕ) : 1 ≤ pScale i := by
  unfold pScale; exact one_le_pow₀ (le_add_of_nonneg_left (by positivity))
lemma cites : (Fintype.card V:ℝ)=(2 * (r:ℝ)+1)^4 := by rw [Fintype.card_coe,Patch.sites, Pressure.box_length,card_layers]; push_cast; rfl
lemma recruits : (l:ℝ)^4 ≤ (Fintype.card V:ℝ) := by
  rw [cites, Patch.radius]; push_cast; apply pow_le_pow_left₀ (by positivity); nlinarith only
      [show 0<(l:ℝ) from side_pos S.patch.L,show (0:ℝ) ≤ S.patch.J by positivity]
lemma troupe : (Fintype.card V:ℝ) ≤ pScale k * (l:ℝ)^4 := by
  rw [cites,pScale,← mul_pow]; apply pow_le_pow_left₀ (by positivity); unfold RG.Patch.radius; push_cast
  linarith [show (1:ℝ) ≤ l by exact_mod_cast S.patch.L.property]
lemma earn (u : V) : S.patch.weight u ≤ pScale k/(Fintype.card V:ℝ) := by
  have h : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ h).mpr; apply (mul_le_mul_of_nonneg_left (troupe S) (S.patch.weight_nonneg u)).trans
  have ht := mul_le_mul_of_nonneg_right (Pressure.light S.patch u) (show 0 ≤ pScale k from zero_le_one.trans (pScale_ge ..))
  rwa [mul_assoc, mul_comm ((l:ℝ)^4),one_mul] at ht

def shade (i : ℕ) : ℕ := i+4
def give (i : ℕ) : ℝ := ((box (shade i)).card:ℝ)
lemma give_ge (i : ℕ) : 1 ≤ give i := by unfold give; exact_mod_cast (show 1 ≤ (box (shade i)).card from Finset.card_pos.mpr ⟨0,center_box _⟩)
lemma residue_pay (u : V) : carry (0:Site L) u.val∈box (shade S.patch.J) := by
  let C := carry (0:Site L) u.val
  have h := carry_spec (0:Site L) u.val
  let y := lift (arrives (0:Site L) u.val)
  rw [lift_origin,zero_add] at h
  have he : u.val = y+l • C := h
  have ht := (box_iff_layers ..).mp u.property
  have hx : y ∈ box (S.patch.L.val/2) := S.ratio.half_box S.patch.odd_side _
  rw [box_iff_layers]; intro i
  have h := ht i; have hu := (box_iff_layers ..).mp hx i
  unfold layers at *; rw [Finset.mem_Icc] at h hu ⊢
  have hv : u.val i=y i+(l:ℤ)*C i := by
    calc
      _ = (y+l • C) i := congr_fun he i
      _ = _ := by rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]
  have hL : 0 < (l:ℤ) := by positivity
  have hb' : ((l/2:ℕ):ℤ) ≤ (l:ℤ) := by exact_mod_cast Nat.div_le_self l 2
  unfold RG.Patch.radius at h
  push_cast at h
  unfold shade; change -((↑(S.patch.J+4):ℤ)) ≤ C i ∧ C i ≤ _; push_cast
  constructor
  · apply le_of_mul_le_mul_left _ hL; linarith only [hv,h.1,hu.2,hb']
  apply le_of_mul_le_mul_left _ hL; linarith only [hv,h.2,hu.1,hb']

lemma tribute (t : Site f) :
    (((Finset.univ : Finset (Site c × V)).filter (fun i => atPoint S i.1 i.2=t)).card:ℝ) ≤ give k := by
  let w i := carry (0:Site L) i
  let p := ((Finset.univ : Finset (Site c × V)).filter (fun i => atPoint S i.1 i.2=t))
  let g (q : p) : ↥(box (shade k)) := ⟨w q.val.2.val,residue_pay S q.val.2⟩
  have hm (q : p) : arrives (0:Site L) q.val.2.val=S.ratio.residue t := by
    have he : atPoint S q.val.1 q.val.2=t := (Finset.mem_filter.mp q.property).2
    unfold arrives; rw [← he,lift_origin,zero_add,atPoint, map_add,S.ratio.residue_embed,S.ratio.residue_wrap,add_zero]; rfl
  have hh : Injective g := by
    intro a b h
    have hv : a.val.2=b.val.2 := by
      apply Subtype.ext
      have hb := carry_spec (0:Site L) a.val.2.val; have hc := carry_spec (0:Site L) b.val.2.val
      rw [hm,lift_origin,zero_add,show carry (0:Site L) _=_ from (show w a.val.2.val=w b.val.2.val from congr_arg Subtype.val h)] at hb
      rw [hm,lift_origin,zero_add] at hc; exact hb.trans hc.symm
    refine Subtype.ext (Prod.ext ?_ hv)
    have hp : atPoint S a.val.1 a.val.2 = t := (Finset.mem_filter.mp a.property).2
    have he : atPoint S b.val.1 b.val.2 = t := (Finset.mem_filter.mp b.property).2
    rw [hv] at hp
    exact S.ratio.embed_injective (add_left_cancel (show wrap f b.val.2.val+ _ = wrap f b.val.2.val + _ from hp.trans he.symm))
  unfold give; apply Nat.cast_le.mpr
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hh

def pro (g : Site f→ℝ) (x : Site c) := avg fun i => g (atPoint S x i)

def disk : Matrix (Site c) (Site f) ℝ := fun x y => pro S (Pi.single y 1) x
lemma disk_rate (g : Site f→ℝ) : pro S g=disk S*ᵥ g := by
  funext i
  unfold pro disk pro mulVec dotProduct avg;simp only [smul_eq_mul,mul_assoc,Finset.sum_mul]
  rw [← Finset.mul_sum,Finset.sum_comm];
  apply congr_arg; refine Finset.sum_congr rfl fun y _ => ?_; rw [Finset.sum_eq_single (atPoint S i y)]; simp
  · intro j _ hj; rw [Pi.single_eq_of_ne hj.symm,zero_mul]
  simp
lemma disk_nonneg (x t) : 0 ≤ disk S x t := Purse.avg_pos _ fun i => by
  by_cases hh : atPoint S x i=t <;> simp [hh]
lemma disk_rows (x) : ∑ t, disk S x t=1 := by
  have he := congr_fun (disk_rate S (fun _ => 1)) x
  simpa only [pro, avg_const,mulVec,dotProduct,mul_one] using he.symm
lemma disk_columns (t) : ∑ i, disk S i t ≤ give k*((l:ℝ)^4)⁻¹ := by
  have ht := recruits S; let H : ℝ := Fintype.card V
  have hx : 0 < H := by unfold H; exact_mod_cast Fintype.card_pos
  have he : (∑ i, disk S i t)=H⁻¹ * (((Finset.univ : Finset (Site c × V)).filter (fun i => atPoint S i.1 i.2=t)).card:ℝ) := by
    unfold disk pro avg
    simp only [smul_eq_mul]; rw [← Finset.mul_sum]
    have hh (i) (j : V) : (Pi.single t 1:Site f→ℝ) (atPoint S i j)=if atPoint S i j=t then 1 else 0 := by split_ifs with h <;> simp [h]
    simp_rw [hh]; rw [← Fintype.sum_prod_type (fun i => if atPoint S i.1 i.2=t then (1:ℝ) else 0)]
    rw [← Finset.sum_filter]; simp [H]
  rw [he,mul_comm]; exact mul_le_mul (tribute ..) ((inv_le_inv₀ hx (pow_pos (side_pos S.patch.L) 4)).mpr ht) (by positivity) (zero_le_one.trans (give_ge _))
lemma pro_ell (g : Site f→ℝ) : rlen (pro S g) ≤ (give k/(l:ℝ)^2)*rlen g := by
  rw [disk_rate]; have hL := side_pos S.patch.L; have hg := give_ge S.patch.J; let h := give k
  apply smear (a:=1) (b:=h*((l:ℝ)^4)⁻¹) (fun i => by simp only [Real.norm_of_nonneg (disk_nonneg ..),disk_rows]; exact le_rfl) zero_le_one (fun j => by
    simp only [Real.norm_of_nonneg (disk_nonneg ..)]; exact disk_columns ..) ?_ (div_nonneg (zero_le_one.trans hg) (by positivity))
  rw [one_mul,div_pow,div_eq_mul_inv]
  apply mul_le_mul ?_ (le_of_eq ?_) (by positivity) (sq_nonneg _)
  · unfold h; nlinarith only [hg]
  · congr 1; ring
end Yard
end YM.AnalyticNext.QuarticMatch.Estimate
