import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import YM.Further.FREE_COVARIANCE_KP.KP.House

/-! # Telescoping on the mesh and exact integration by clips -/

set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Lattice Bloch Laurent
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {n : Side}









abbrev St := Axis→Fin 3
def posi (v : St) : Cover := fun i => (v i).val-1
def pav (n : Side) (a : Site n×St) := lift a.1 + n.val • posi a.2
lemma pav_wrap (a : Site n × St) : wrap n (pav n a)=a.1 := by
  unfold pav; rw [map_add,wrap_lift,map_nsmul]; suffices n.val • wrap n (posi a.2)=0 by rw [this, add_zero]
  funext i; simp [nsmul_eq_mul]
lemma pav_sep (n : Side) : Injective (pav n) := by
  intro ⟨x,i⟩ ⟨y,j⟩ h
  have he := congr_arg (wrap n) h
  rw [pav_wrap,pav_wrap] at he
  dsimp only at he
  subst y
  congr 1
  unfold pav at h
  have he := add_left_cancel h
  funext d
  apply Fin.ext
  have h := congr_fun he d
  change n.val • ((i d).val-1 : ℤ)= n.val • ((j d).val-1 : ℤ) at h
  have hv := mul_left_cancel₀ (Int.natCast_pos.mpr n.property).ne' (show (n.val:ℤ)*_= (n.val:ℤ)*_ from by simp only [nsmul_eq_mul] at h; exact h)
  omega
lemma local_price (x : Site n) (i:Axis) : |lit n (lift x) i| ≤ Real.pi := by
  change |(2 * Real.pi/n.val * ↑(lift x i):ℝ)| ≤ _
  obtain ⟨h₁,h₂⟩ := lift_centers x i; have he := side_pos n; have hπ := Real.pi_pos
  have hu : -(n.val:ℝ)<2 * (↑(lift x i):ℝ) := by exact_mod_cast h₁
  have hv : 2 * (↑(lift x i):ℝ) ≤ n.val := by exact_mod_cast h₂
  rw [abs_le]; constructor <;> (field_simp; nlinarith)
lemma cor_axis (x : Cover) (v : Cover) (i : Axis) : lit n (x + n.val • v) i=lit n x i+2*Real.pi * v i := by
  have h:=side_pos n; simp [lit,leap,rcast,nsmul_eq_mul]; field_simp
lemma roof_hit (x:Cover) (h : house (lit n x)≠0) : ∃ a, pav n a=x := by
  let a := wrap n x; obtain ⟨v,hv⟩ := cover_of_eq (lift a) x (wrap_lift _)
  have hu i : -1≤v i ∧ v i≤1 := by
    have he := local_price a i
    have ht : lit n x∈facade := by_contra fun hh => h (house_off _ hh)
    have hh : |lit n x i|≤5*Real.pi/4 := ht i; rw [hv,cor_axis] at hh
    have hz := Real.pi_pos; obtain ⟨hu,hv⟩ := abs_le.mp he; obtain ⟨hb,hs⟩ := abs_le.mp hh; constructor
    · by_contra! h; have ht' : (↑(v i):ℝ) ≤ -2 := by exact_mod_cast (show v i≤ -2 by omega)
      nlinarith
    by_contra! h; have ht' : 2 ≤ (↑(v i):ℝ) := by exact_mod_cast (show 2 ≤ v i by omega)
    nlinarith
  let s : St := fun i => ⟨(v i+1).toNat,by have hh:=hu i; omega⟩
  refine ⟨(a,s),?_⟩
  unfold pav
  change _ + n.val • posi s = _
  rw [hv,show posi s=v from funext fun i=> by unfold posi s; have hh:=hu i; dsimp only; omega]
lemma fold_door (a:Site n) : ∑ i:St, house (lit n (pav n (a,i)))=1 := by
  have hh (x:ℝ) (h : |x|≤Real.pi) : ∑ k:Fin 3, beam (x+2*Real.pi*((↑((k.val:ℤ)-1)):ℤ))=1 := by
    rw [Fin.sum_univ_three]; unfold beam; have hπ := Real.pi_pos; obtain ⟨hb,hc⟩ := abs_le.mp h
    have hg := at_corner (x+2*Real.pi) (by linarith)
    have hd := at_line (x-2*Real.pi-2*Real.pi) (by unfold mural; linarith)
    norm_num [← sub_eq_add_neg]; linarith
  unfold pav house; rw [← Complex.ofReal_sum]
  let f (i:Axis) (k : Fin 3) := beam (lit n (lift a) i+ 2*Real.pi*((k.val:ℤ)-1 :ℤ))
  simp_rw [cor_axis]
  change ↑(∑ k:St, ∏ i:Axis, f i (k i))=(1:ℂ)
  rw [← Fintype.prod_sum]
  simp_rw [show ∀ i:Axis, ∑ j:Fin 3, f i j=1 from fun i=> hh _ (local_price a i)]
  simp


end YM.Further.FreeCovariance.KP
