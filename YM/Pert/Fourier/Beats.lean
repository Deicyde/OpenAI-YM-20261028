import YM.Pert.Fourier.Periodic
/-! Centered window lifts of iterated momentum differences. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Lattice Full Function Filter Set Topology Metric
open scoped ContDiff BigOperators
variable {Y : Type*} [NormedAddCommGroup Y] {n : Side}

def gridDiff (f : Site n) : ℕ → (Site n → Y) → Site n → Y | 0,g,x => g x | (i+1),g,x => gridDiff f i g (x+f)-gridDiff f i g x
lemma gridDiff_zero (i : ℕ) (f x : Site n) : gridDiff f i (0:Site n→Y) x = 0 := by induction i generalizing x with | zero => rfl | succ i h => rw [gridDiff,h,h,sub_self]
lemma translated (i : ℕ) {f p : Site n} {e q : E4} {g : Site n→ Y} {H : E4 → Y} (he : ∀ j ≤ i, g (p + j • f) = H (q + j • e)) :
  gridDiff f i g p = punch e i H q := by
  induction i generalizing p q with
  | zero => simpa using! he 0 le_rfl
  | succ i ih => rw [gridDiff,show punch e (i+1) H q = punch e i H (q+e)-punch e i H q from rfl, ih (p:=p) (q:=q) (fun j hj=> he _ (by omega)), ih (q:=q+e) _]; intro j hj; simpa only [add_comm j 1,add_nsmul,one_nsmul, add_assoc] using! he (j+1) (by omega)
lemma local_eq {t : ℝ} (ht : 0<t) (h1 : t ≤ 1) {v : ℕ} (hm : mesh n * v ≤ 1/2)
    (j : ℕ) (hv : j ≤ v) (g : Axis) (p : Site n) (D : List Axis) :
  let x := Lattice.lift p - j • (step g : Cover)
  let q := t⁻¹ • incVec (mesh n) x
  ringM D t (p-j • step g) = middle D t q ∧ roof D t (p-j • step g) = last D t q := by
  intro x q
  have he : wrap n x = p-j • step g := by simp only [x,map_nsmul,map_sub,wrap_step,wrap_lift]
  have hp := periodic_symbol (n:=n) D x t ht
  by_cases hx : x = Lattice.lift (p-j • step g)
  · constructor <;> dsimp only [q] <;> rw [hx] <;> rfl
  have hb := spill_near (le_trans hm (show (1:ℝ)/2≤Real.pi-2 from by linarith [Real.pi_gt_three])) hv p g hx
  have ha := spill (j:=0) (v:=q) (f:=g) x (show _ by rwa [he])
  have h0 : 2 ≤ ‖stretch t (p-j • step g)‖ := by rw [stretch_norm ht]; rw [le_div_iff₀ ht]; linarith
  have h0' : 2 ≤ ‖q‖ := by change 2 ≤ ‖t⁻¹•_‖; rw [norm_smul,norm_inv,Real.norm_of_nonneg ht.le, inv_mul_eq_div,le_div_iff₀ ht]; linarith [Real.pi_gt_three]
  constructor
  · unfold ringM middle; simp only [outermost h0, disk_out (le_trans one_le_two h0), outermost h0',disk_out (le_trans one_le_two h0'),sub_self,Complex.ofReal_zero,zero_mul]
  · unfold roof last; simp only [disk_out (le_trans one_le_two h0), disk_out (le_trans one_le_two h0')]; simp only [sub_zero, Complex.ofReal_one,one_mul]; exact ((periodic_symbol D x t ht).trans (by rw [he])).symm
lemma path_ordinal (t : ℝ) (g : Axis) (p : Site n) (j : ℕ) : stretch t p + j • (((-t⁻¹)*(mesh n)) • basis g) = t⁻¹ • incVec (mesh n) (Lattice.lift p - j • step g) := by
  rw [scal_step, stretch,moment,smul_add,← smul_smul,neg_smul]; congr 1; rw [smul_neg,smul_neg,smul_comm j (t⁻¹:ℝ),smul_neg]
lemma path_eq {t : ℝ} (ht : 0<t) (h1 : t ≤ 1) {v : ℕ} (hm : mesh n * v ≤ 1/2)
    (g : Axis) (p : Site n) (D : List Axis) :
   let q := stretch t p
   let e := ((-t⁻¹)*(mesh n)) • basis g
   gridDiff (-step g) v (ringM D t) p = punch e v (middle D t) q ∧ gridDiff (-step g) v (roof D t) p = punch e v (last D t) q := by
  intro q e
  have hx : ∀ j : ℕ, p + j • (-step g) = p - j • step g := fun j => by rw [smul_neg,sub_eq_add_neg]
  have hq := fun j hj => local_eq ht h1 hm j hj g p D
  constructor
  · apply translated; intro j h; change _=(middle D t) ((stretch t p)+j • (((-t⁻¹)*(mesh n)) • basis g)); rw [path_ordinal,hx]; exact (hq _ h).1
  · apply translated; intro j h; change _=(last D t) ((stretch t p)+j • (((-t⁻¹)*(mesh n)) • basis g)); rw [path_ordinal,hx]; exact (hq _ h).2

lemma punch_far {q : E4} (h : 3 < ‖q‖) {e : E4} (j : ℕ) (he : (j:ℝ)*‖e‖ ≤ 1) (f : E4 → ℂ) (hf : ∀ x, 2 ≤ ‖x‖ → f x=0) : punch e j f q=0 := by
  have eq := translated (n:=1) (p:=0) (f:=0) (g:=(0:Site 1 → ℂ)) (q:=q) (e:=e) (H:=f) j (fun i hi => ?_)
  · symm; rw [← eq,gridDiff_zero]
  dsimp; symm; apply hf
  have hx := norm_sub_le (q+i • e) (i • e)
  rw [add_sub_cancel_right, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast] at hx; -- wrong lemma
  rw [← Nat.cast_smul_eq_nsmul ℝ]; linarith [mul_le_mul_of_nonneg_right (by exact_mod_cast hi : (i:ℝ)≤j) (norm_nonneg e)]

set_option maxHeartbeats 350000 in
lemma punches (D : List Axis) (v : ℕ) : ∃ C > 0, ∀ {n : Side} {t : ℝ}, 0<t → t ≤ 1 → mesh n * v ≤ 1/2 → mesh n * v ≤ t → ∀ (f : Axis) (p : Site n), let T : ℝ := (mesh n)/t;
   ‖gridDiff (-step f) v (ringM D t) p‖ ≤ (if ‖stretch t p‖ ≤ 3 then T^v*C else 0) ∧ (1/2 ≤ t → ‖gridDiff (-step f) v (roof D t) p‖ ≤ T^v*C) := by
  obtain ⟨a,hap,ha⟩ := middle_bound v D; obtain ⟨b,hbp,hb⟩ := last_bound v D
  refine ⟨max a b,lt_of_lt_of_le hap (le_max_left ..),?_⟩; intro n t ht h1 hv0 hv f p T
  have he := path_eq ht h1 hv0 f p D
  rw [he.1,he.2]
  let e := (-t⁻¹*mesh n) • basis f
  have eh : ‖e‖ = T := by unfold e T; rw [norm_smul, neg_mul,Real.norm_eq_abs,abs_neg,abs_of_pos (mul_pos (inv_pos.mpr ht) mesh_pos),basis_norm,mul_one,inv_mul_eq_div]
  have hn (j : ℕ) : ‖j • e‖ = (j:ℝ) * T := by rw [← Nat.cast_smul_eq_nsmul ℝ,norm_smul,Real.norm_natCast,eh]
  have hT (h : (mesh n) * (v:ℝ) ≤ t) : (v:ℝ)*T ≤ 1 := by dsimp only [T]; have e : mesh n * (v:ℝ)/t≤1 := (div_le_one ht).mpr h; convert! e using 1; ring
  have ht0 : 0 ≤ T := by unfold T; exact (div_pos mesh_pos ht).le
  have hmax (j : ℕ) (hj : j<v) : ((j+1:ℕ):ℝ)*T ≤ 1 := (mul_le_mul_of_nonneg_right (by exact_mod_cast (hj : j+1≤v)) ht0).trans (hT hv)
  have reach (j : ℕ) (h : ‖stretch t p‖ ≤ 3) (hj : j<v) : stretch t p + j • e + e∈ closedBall (0:E4) 6 := by
    have hs := hmax j hj
    rw [mem_closedBall,dist_zero_right, add_assoc,← succ_nsmul]; grw [norm_add_le]; simp only [hn]; linarith only [hs,h]
  have cost (i : Axis) (j : ℕ) (hj : j ≤ v) : |t * ((j • e) i)| ≤ 1/2 := by
    rw [abs_mul,abs_of_pos ht]; grw [coordinate_le, hn]; rify at hj; unfold T; have hh := mul_le_mul_of_nonneg_left hj (mesh_pos (n:=n)).le; convert! hh.trans hv0 using 1; field_simp
  constructor
  · split
    next h =>
      have hs := middle_diff D t (abs_le.mpr ⟨by linarith,h1⟩)
      have hh : Smooth v (closedBall (0:E4) 6) (middle D t) := fun x _ => ((hs x).comp (g:=uncurry (middle D)) (f:=fun b : E4 => (t,b)) x (contDiffAt_const.prodMk (contDiffAt_id (𝕜:=ℝ)))).of_le (by norm_cast; simp)
      have kn := Band.puncture v (closedBall 0 6) (convex_closedBall (0:E4) 6) (stretch t p) e a (middle D t) ⟨by rw [mem_closedBall,dist_zero_right]; exact h.trans (by norm_num),fun j hj => reach j h hj⟩ hh (fun x hx => ha (t,x) ⟨ht.le,h1⟩ hx)
      rw [←eh]; exact kn.trans (mul_le_mul_of_nonneg_left (le_max_left ..) (by positivity))
    next h =>
      have hh (x : E4) (hx : 2 ≤ ‖x‖) : middle D t x=0 := by simp only [middle,disk_out (le_trans one_le_two hx),outermost hx,sub_zero]; simp
      rw [punch_far (not_le.mp h) (e:=e) v (by rw [eh]; exact hT hv) _ hh]; simp
  intro h
  have box_pi (i : Axis) : |t*(stretch t p i)| ≤ Real.pi := by
    rw [show t*(stretch t p i)=(moment p) i from congrArg (fun q : E4 => q i) (stretch_fwd t ht.ne' (moment p))]
    exact moment_cube p i
  have kn0 : nob (box t) (stretch t p) e v := ⟨fun i => (box_pi i).trans (by unfold cap; linarith only [Real.pi_pos]), fun j hj i => by
    calc |t*((stretch t p + j • e + e) i)| = |t*(stretch t p i)+ t* (((j+1) • e) i)| := by rw [← mul_add,add_nsmul,one_smul, add_assoc,PiLp.add_apply]
         _ ≤ |t*(stretch t p i)| + |t*(((j+1) • e) i)| := abs_add_le ..
         _ ≤ Real.pi + 1/2 := add_le_add (box_pi i) (cost i _ hj)
         _ ≤ _ := by unfold cap; linarith [Real.two_le_pi]⟩
  have hh : Smooth v (box t) (last D t) := fun x hx => ((last_diff D t x (fun i => (hx i).trans_lt (by unfold cap; linarith [Real.pi_pos]))).comp (g:=uncurry (last D)) (f:=fun b : E4 => (t,b)) x (contDiffAt_const.prodMk (contDiffAt_id (𝕜:=ℝ)))).of_le (by norm_cast; simp)
  have kn := Band.puncture v (box t) (convex_box t) (stretch t p) e b (last D t) kn0 hh (fun x hx => hb (t,x) ⟨⟨⟨h,h1⟩,trivial⟩,hx⟩)
  rw [←eh]; exact kn.trans (mul_le_mul_of_nonneg_left (le_max_right ..) (by positivity))
end YM.Pert.Band
