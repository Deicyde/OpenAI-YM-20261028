import YM.Further.FREE_COVARIANCE_KP.KP.Plain
import YM.PREC.Stacks
import YM.Work.F06.Energy



/-! # Recover real-frequency ellipticity from every true period -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex Lattice Bloch Laurent Matrix Exterior Precision Work.F06
open scoped Topology BigOperators InnerProductSpace

variable {α Ω η : ℝ}

/-- common pre-L prices only. -/
structure Firm (α Ω η : ℝ) where
  row : Row (TypeFace 2) (TypeFace 2)
  basic : row.strip α Ω
  heats (n : Side) : Numeric (row.acts n) η Ω
  initial : row.read 0=1

namespace Firm
variable (f : Firm α Ω η) (ha : 0<α)

include ha
lemma safety : f.row.safe := Row.rights _ _ f.basic ha.le
lemma real_lower {n : Side} (p : Site n) (x : TypeFace 2 → ℂ) : η*sqLength x ≤ pairingRe (f.row.read (mon p)) x x := by
  let M := TypeFace 2
  let N := Body 2 n
  let B := f.row.acts n; let L := f.row.read (mon p)
  let y (r : N) := cell p r.1 * x r.2
  let A := approached B
  have he : η*sqLength y ≤ pairingRe A y y := by
    let u (r) := (y r).re; let v (r) := (y r).im
    have hh : sqLength y = dotProduct u u + dotProduct v v := by
      simp only [sqLength,dotProduct,re_sum,← Finset.sum_add_distrib,Pi.star_apply,Complex.star_def,Complex.mul_re,Complex.conj_re, Complex.conj_im]
      simp [u,v]
    have hz : pairingRe A y y = dotProduct u (B *ᵥ u) + dotProduct v (B *ᵥ v) := by
      simp only [pairingRe, Matrix.mulVec,dotProduct,re_sum,← Finset.sum_add_distrib,A,approached,Matrix.map_apply,
        Pi.star_apply,Complex.star_def,Complex.mul_re,Complex.conj_re, Complex.conj_im, im_sum,Complex.ofReal_im, Complex.ofReal_re,mul_im,zero_mul]
      simp [u,v]
      rfl
    rw [hh,hz,mul_add]; exact add_le_add (f.heats n u).1 (f.heats n v).1
  have hu (X : TypeFace 2 → ℂ) (r : N) : (rotations n M *ᵥ (fun k : N => if k.1=p then X k.2 else 0)) r = cell p r.1 * X r.2 := by simp [rotations,Matrix.mulVec,dotProduct,Fintype.sum_prod_type, mul_ite,ite_mul]
  have hz (t : N) : (A*ᵥy) t=cell p t.1 * (L*ᵥx) t.2 := by
    let v (i : N) := if i.1=p then x i.2 else 0
    rw [show y=rotations n M *ᵥ v from (funext (hu x)).symm,mulVec_mulVec,show A*rotations n M = _ from circulant n f.row (f.safety ha),← Matrix.mulVec_mulVec]
    apply Eq.trans ?_ (hu _ t)
    congr 1
    funext i; by_cases h : i.1=p <;> simp [v,fiber,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,L, ite_mul,mul_ite,h]
    rfl
  let c := (n.val:ℝ)^4
  have hh (v : M → ℂ) : (dotProduct (star y) (fun r : N => cell p r.1 * v r.2)).re = c * (dotProduct (star x) v).re := by
    have ht (i : Site n) (j : TypeFace 2) : star (cell p i*x j) * (cell p i * v j)=star (x j)*v j := by rw [star_mul, mul_assoc _ (star _),← mul_assoc (star (cell _ _)), Complex.star_def,cell_bar,inv_mul_cancel₀ (cell_ne _ _),one_mul]
    simp only [dotProduct,Fintype.sum_prod_type, Pi.star_apply,y,N,Body,Co,ht,c,re_sum,M]; simp
  rw [pairingRe,sqLength,show A*ᵥy=_ from funext hz,hh,show y=(fun r => cell p r.1*x r.2) from rfl,hh] at he
  change η*(c*sqLength x) ≤ c * pairingRe L x x at he; rw [mul_left_comm] at he; exact (mul_le_mul_iff_right₀ (pow_pos (side_pos n) _)).mp he
end Firm

/-- Real frequency step (radians), not physical pitch. -/
def leap (n : Side) : ℝ := 2*Real.pi / n.val
def lit (n : Side) (x : Cover) := leap n • rcast x
lemma leap_pos (n) : 0<leap n := div_pos (by positivity) (side_pos n)
lemma lit_mon {n : Side} (p : Site n) : mcast (lit n (lift p))=mon p := by
  ext1 i; simp [lit,leap,mcast,rcast,mon,reciprocal]; ring
lemma lit_alias {n : Side} (x : Cover) : ∃ v : Cover, mcast (lit n x)=mon (wrap n x)+reciprocal v := by
  obtain ⟨v,hv⟩ := cover_of_eq (lift (wrap n x)) _ (wrap_lift _); refine ⟨v,?_⟩
  rw [← lit_mon]
  have hn := side_ne n
  ext1 i; change ((↑(leap n * (x i:ℝ))) :ℂ) = _
  conv_lhs => rw [hv]
  simp [lit,leap,mcast,rcast,reciprocal,nsmul_eq_mul]; field_simp

def mark (r : ℝ) (p : E4) : Cover := fun i => ⌊p i / r⌋
lemma marked_bound {r : ℝ} (h : 0<r) (p : E4) (i) : |(r • rcast (mark r p)) i - p i| ≤ r := by
  change |r*((↑⌊p i/r⌋):ℝ)-_|≤_
  have ht := (le_div_iff₀ h).mp (Int.floor_le (p i/r))
  have he := (div_lt_iff₀ h).mp (Int.lt_floor_add_one (p i/r)); rw [abs_le]; constructor <;> linarith
lemma refining (p : E4) : Tendsto (fun k : ℕ => let n : Side := ⟨k+1,Nat.succ_pos _⟩; lit n (mark (leap n) p)) atTop (𝓝 p) := by
  let N (k : ℕ) : Side := ⟨k+1,Nat.succ_pos _⟩
  let v (k) := lit (N k) (mark (leap (N k)) p)
  have ht (i) : Tendsto (fun k => v k i) atTop (𝓝 (p i)) := by
    have hm : Tendsto (fun k => leap (N k)) atTop (𝓝 0) := by
      have hm : Tendsto (fun k : ℕ => (↑k:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      change Tendsto (fun k : ℕ => (2*Real.pi)/((k+1:ℕ):ℝ)) _ (𝓝 0)
      simpa only [ Nat.cast_add,Nat.cast_one,mul_zero, Function.comp_def,div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hm).const_mul (2*Real.pi)
    rw [tendsto_iff_dist_tendsto_zero]; exact squeeze_zero (fun _ => dist_nonneg) (fun k=> marked_bound (leap_pos (N k)) p i) hm
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Axis=>ℝ)).symm
  exact L.continuous.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr ht)

lemma plan_prices (b c) (ha : 0<α) (R : ℝ) : Plain R (fun (f : Firm α Ω η) (p : E4) => f.row.read (mcast p) b c) :=
  radial_prices ha R _ (fun f => Row.constant_strip f.row f.basic b c)
lemma real_price {f : Firm α Ω η} (ha : 0<α) (p : E4) (x : TypeFace 2 → ℂ) : η*sqLength x ≤ pairingRe (f.row.read (mcast p)) x x := by
  have he (b c : TypeFace 2) : Continuous (fun p:E4 => f.row.read (mcast p) b c) := ((plan_prices b c ha 0).smooth f).continuous
  have hu : Continuous (fun p:E4 => pairingRe (f.row.read (mcast p)) x x) := by unfold pairingRe dotProduct Matrix.mulVec; fun_prop
  apply ge_of_tendsto' (hu.continuousAt.tendsto.comp (refining p)); intro k
  let n : Side := ⟨k+1,Nat.succ_pos _⟩; let v := mark (leap n) p
  change η*sqLength _ ≤ pairingRe (f.row.read (mcast (lit n v))) _ _; obtain ⟨r,hr⟩ := lit_alias v
  rw [hr,Row.periods]; exact f.real_lower ha _ x
end YM.Further.FreeCovariance.KP
