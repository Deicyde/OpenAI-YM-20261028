import YM.Pert.Fourier.Uniform
import YM.Pert.Fourier.Inversion
import Mathlib.Analysis.Real.Pi.Bounds
/-! Periodic versions of annular cutoffs and symbols. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Lattice Full Function Complex Set Filter Topology
open scoped ContDiff
variable {n : Side}
def stretch (t : ℝ) (p : Site n) : E4 := t⁻¹ • moment p
def crop (t : ℝ) (p : Site n) : ℝ := disk (stretch t p)
def ringM (D : List Axis) (t : ℝ) (p : Site n) : ℂ := middle D t (stretch t p)
def roof (D : List Axis) (t : ℝ) (p : Site n) : ℂ := last D t (stretch t p)
lemma stretch_norm {t : ℝ} (ht : 0<t) (p : Site n) : ‖stretch t p‖ = ‖moment p‖/t := by rw [div_eq_inv_mul]; simp [stretch,norm_smul,Real.norm_of_nonneg ht.le]
lemma stretch_double {t : ℝ} (ht : 0<t) (p : Site n) : stretch (2*t) p=(1/2:ℝ) • stretch t p := by
  unfold stretch; rw [smul_smul]; congr 1; field_simp
lemma stretch_fwd (t : ℝ) (ht : t≠0) (q : E4) : t • (t⁻¹ • q) = q := by rw [smul_smul,mul_inv_cancel₀ ht,one_smul]
lemma incVec_twist (r : ℝ) (x y : Cover) : incVec r (x+y)=incVec r x+incVec r y := by ext i; simp [Full.incVec,add_mul,mul_add]
lemma incVec_nscale (r : ℝ) (x : Cover) (j : ℕ) : incVec r (j • x) = j • incVec r x := by ext i; simp [Full.incVec,nsmul_eq_mul]; ring
lemma incVec_neg (r : ℝ) (x : Cover) : incVec r (-x) = -incVec r x := by ext i; simp [Full.incVec,neg_mul]
lemma incVec_step (r : ℝ) (i : Axis) : incVec r (step i)=r • basis i := by ext j; simp [Full.incVec]; try {split <;> simp}
lemma scal_step (r : ℝ) (z : Cover) (i : Axis) (j : ℕ) : incVec r (z-j • step i)=incVec r z+j • (-(r • basis i)) := by rw [sub_eq_add_neg,incVec_twist,incVec_neg,incVec_nscale,incVec_step,smul_neg]
lemma to_grid (x : Cover) (r s : ℝ) : r • incVec s x=incVec (r*s) x := by ext i; simp [incVec,mul_assoc]
lemma numerator_redef (x : Cover) (i : Axis) (t : ℝ) (ht : 0 < t) : ((t:ℂ)*numerator t (t⁻¹ • incVec (mesh n) x) i = char (wrap n x) (step i) - 1) := by
  let q := t⁻¹ • incVec (mesh n) x
  have he : t * q i = incVec (mesh n) x i := congrArg (fun z:E4 =>z i) (stretch_fwd t ht.ne' (incVec _ x))
  unfold numerator
  have hz := phaseQ_mul (t*q i)
  rw [real_smul] at hz; push_cast at hz
  calc _ = phase (incVec (mesh n) x i) - 1 := by rw [← he,← hz,mul_assoc]
    _ = _ := by rw [swap (wrap n x), char,show dot (step i) (wrap n x) = ((x i:ℤ):ZMod n.val) by simp [dot,wrap,step_apply,mul_comm],ZMod.stdAddChar_coe]; simp only [phase,incVec_apply,mesh]; push_cast; ring_nf
lemma denominator_eq (x : Cover) (t : ℝ) (ht : 0 < t) : (t^2:ℂ)*latticeD t (t⁻¹ • incVec (mesh n) x) = ↑(delta (moment (wrap n x))) := by
  let q:= t⁻¹ • incVec (mesh n) x
  have hx (i : Axis) (t : ℝ) (ht : 0<t) : phase (t*(t⁻¹ • incVec (mesh n) x) i) = char (wrap n x) (step i) := by
    have he := numerator_redef (n:=n) x i t ht
    have hz := phaseQ_mul (t*(t⁻¹ • incVec (mesh n) x) i)
    rw [real_smul] at hz; push_cast at hz
    unfold numerator at he; rw [←mul_assoc,hz,sub_left_inj] at he; exact he
  have he (i : Axis) : (-4 *(Real.sin (t*(q i)/2))^2 : ℝ) = -4 * (Real.sin ((moment (wrap n x) i)/2))^2 := by
    apply Complex.ofReal_injective
    exact (show (((-4 *(Real.sin (t*(q i)/2))^2 : ℝ):ℂ) = (-4 * (Real.sin ((moment (wrap n x) i)/2))^2:ℝ)) by
      rw [← exp_pair, ← second_char,← neg_mul,← ofReal_neg]; change phase _ + phase (- (t * q i)) - _ = _; rw [hx i t ht]; congr 2
      rw [← mul_left_inj' (Complex.exp_ne_zero ((t*q i:ℝ)*I))]; unfold phase; simp only [ofReal_neg,neg_mul]; rw [Complex.exp_neg, inv_mul_cancel₀ (Complex.exp_ne_zero _)]
      rw [show Complex.exp _ = char (wrap n x) (step i) by exact hx i t ht]; simp [← char_add,char_zero])
  unfold latticeD delta; push_cast only [Complex.ofReal_sum]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
  have H := sinQ_mul (t*q i/2); have e : (t^2:ℝ)*(q i*sinQ (t*q i/2))^2=4*Real.sin (t*q i/2)^2 := by rw [← H]; ring
  have hy : (4:ℝ)*Real.sin (t*q i/2)^2 = 4*Real.sin ((moment (wrap n x) i)/2)^2 := by linarith only [he i];
  rw [← hy, ← ofReal_pow, ← ofReal_mul]; exact congrArg ofReal (e)
set_option maxHeartbeats 500000 in
lemma periodic_symbol (D : List Axis) (x : Cover) (t : ℝ) (ht : 0<t) : symbol D t (t⁻¹ • incVec (mesh n) x) = symbol D t (stretch t (wrap n x)) := by
  unfold symbol
  have e : latticeD t (t⁻¹ • incVec (mesh n) x) = latticeD t (stretch t (wrap n x)) := by
    let a := Lattice.lift (wrap n x)
    have h12 : wrap n a = wrap n x := Lattice.wrap_lift _
    have e1 := denominator_eq (n:=n) x t ht
    have e2 := denominator_eq (n:=n) a t ht
    rw [h12] at e2
    have e3 := ne_of_gt (pow_pos ht 2)
    exact Complex.ofReal_injective (mul_left_cancel₀ (by exact_mod_cast e3 : ((t:ℂ)^2:ℂ)≠0) (e1.trans e2.symm))
  have h : numerator t (t⁻¹ • incVec (mesh n) x) = numerator t (stretch t (wrap n x)) := by
    funext k
    let a := Lattice.lift (wrap n x)
    have h12 : wrap n a = wrap n x := Lattice.wrap_lift _
    have e1 := numerator_redef (n:=n) x k t ht
    have e2 := numerator_redef (n:=n) a k t ht
    rw [h12] at e2
    exact mul_left_cancel₀ (by exact_mod_cast ht.ne' : (t:ℂ)≠0) (e1.trans e2.symm)
  rw [e,h]
lemma left_cell (x : Cover) (h : x ≠ Lattice.lift (wrap n x)) : ∃ i : Axis, Real.pi ≤ mesh n * |(x i:ℤ)| := by
  by_contra! hf
  apply h; symm; rw [lift_eq_iff]; refine ⟨rfl,fun i=>?_⟩
  have h0 := hf i; norm_cast at h0
  have h1 : 2 * |(x i:ℝ)| < n.val := by
    have hv : mesh n * |(x i:ℝ)| < Real.pi := by simpa using hf i
    apply lt_of_mul_lt_mul_left (a:=mesh n) _ mesh_pos.le; rw [show mesh n * (2*_) = 2*(mesh n * |(x i:ℝ)|) from by ring,mesh_val]; linarith
  have h2 : ((2:ℤ)*|x i| : ℤ) < ↑n.val := by exact_mod_cast h1
  have := le_abs_self (x i); have := neg_le_abs (x i); omega
lemma spill (x : Cover) (h : x ≠ Lattice.lift (wrap n x)) {v : E4} {j : ℕ} {f : Axis} : Real.pi ≤ ‖incVec (mesh n) x‖ := by
  obtain ⟨k,hk⟩ := left_cell (n:=n) x h
  have he := coordinate_le (incVec (mesh n) x) k
  simp_rw [incVec_apply,abs_mul,abs_of_pos mesh_pos] at he
  exact (le_trans (b:=mesh n * ↑|x k|) hk (by simpa using he))
lemma spill_near {m j : ℕ} (hm : mesh n * m ≤ Real.pi-2) (hj : j ≤ m) (v : Site n) (f : Axis) (h : Lattice.lift v - j • step f ≠ Lattice.lift (v-j • step f)) :
    2 ≤ ‖moment (v-j • step f)‖ := by
  by_cases hb : ∀ i, |(Lattice.lift (v-j • step f) i : ℝ)| ≤ (n.val:ℝ)/2 - (j:ℕ)
  · have e (i : Axis) : Lattice.lift ((v-j • step f)+j • step f) i = Lattice.lift (v-j • step f) i + j • (step f : Cover) i := by
      suffices hv : Lattice.lift (v-j • step f+j • step f)=Lattice.lift (v-j • step f)+ j • step f by exact congrFun hv i
      rw [lift_eq_iff]; refine ⟨by simp only [map_add,map_nsmul,wrap_step,wrap_lift], fun s=>?_⟩
      have hm1 : -(n.val:ℝ)/2 < ((Lattice.lift (v-j • step f) s + ↑j • (step f : Cover) s:ℤ):ℝ) := by
        have hv := abs_le.mp (hb s); have : (j:ℝ)>0 ∨ j=0 := by
          have hx := Nat.cast_nonneg (α:=ℝ) j
          rcases eq_or_lt_of_le hx with he|he
          · right; exact_mod_cast he.symm
          exact Or.inl he
        rcases this with ht|ht
        · push_cast; have : 0 ≤ (↑((step f : Cover) s) : ℝ) := by simp only [step_apply]; split <;> norm_num
          simpa only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast] using! (show _ by nlinarith [hv.1,hv.2] : -(n.val:ℝ) / 2 < (Lattice.lift (v - j • step f) s:ℤ) + (j:ℝ) * ↑((step f:Cover) s))
        rw [ht]; have hu : -(n.val:ℝ)/2 < (Lattice.lift v s:ℝ) := by
          have h0 := (lift_centers v s).1
          have h' : -(n.val:ℝ) < 2*(Lattice.lift v s:ℝ) := by exact_mod_cast h0
          linarith
        simpa only [Nat.cast_ofNat,zero_smul,add_zero,sub_zero] using hu
      have hm2 : ((Lattice.lift (v-j • step f) s + ↑j • (step f : Cover) s:ℤ):ℝ) ≤ (n.val:ℝ)/2 := by
        have H : (↑((step f : Cover) s):ℝ) ≤ 1 := by simp only [step_apply]; split <;> norm_num
        have he := (abs_le.mp (hb s)).2; set A : ℤ := Lattice.lift (v-j • step f) s with eqA; norm_cast; push_cast [nsmul_eq_mul]; nlinarith only [H,he, Nat.cast_nonneg (α:=ℝ) j]
      rw [Pi.add_apply,Pi.smul_apply]
      exact_mod_cast (show -(n.val:ℝ) < 2 * ((Lattice.lift (v - j • step f) s+j • (step f:Cover) s : ℤ):ℝ) ∧ 2*((Lattice.lift (v - j • step f) s+j • (step f:Cover) s : ℤ):ℝ) ≤ n.val from ⟨by linarith only [hm1],by linarith only [hm2]⟩)
    have eh : v - j • step f + j • step f = v := sub_add_cancel ..
    have : Lattice.lift v = Lattice.lift (v-j • step f) + j • (step f : Cover) := by
      rw [sub_add_cancel v _] at e
      exact funext e
    exact (h (sub_eq_iff_eq_add.mpr this)).elim
  push Not at hb
  obtain ⟨k,hk⟩ := hb
  have he := coordinate_le (moment (v-j • step f)) k
  rw [moment_apply,abs_mul,abs_of_pos mesh_pos] at he
  have h2 := mesh_val (n:=n)
  have hv := mul_lt_mul_of_pos_left hk (mesh_pos (n:=n))
  have hj : (j:ℝ)≤m := by exact_mod_cast hj
  have hh := mul_le_mul_of_nonneg_left hj (mesh_pos (n:=n)).le
  linarith
end YM.Pert.Band
