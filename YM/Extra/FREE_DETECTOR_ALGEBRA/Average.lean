import YM.Extra.FREE_DETECTOR_ALGEBRA.RanksTwo

set_option warningAsError false

/-! Four-dimensional mean probes on angular polynomials.
No measures needed here: normalize by advancing to a common homogeneous
degree then take powers of the Laplacian. `Average` compatible across
representatives of possibly different *even* degrees on the unit sphere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.OPE
open Function Filter Set Tensor Analysis Maxwell Wick Residue SphereTest Pair
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : E4 → F} {j k : ℕ}

def ends (j : ℕ) (f : E4 → F) : F := ((lap (F:=F))^[j]) f 0

lemma ends_lap (i : ℕ) : ends i (lap f)=ends (i+1) f := by rw [ends,ends, iterate_succ_apply]
lemma lap_diff (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (lap f) := ContDiff.sum (fun i _ => grad_diff_all (grad_diff_all hf i) i)

lemma ends_add (i : ℕ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : ends i (f+g)=ends i f + ends i g := by
  induction i generalizing f g with
  | zero => rfl
  | succ i ih => rw [← ends_lap,lap_add' hf hg,ih (lap_diff hf) (lap_diff hg),ends_lap,ends_lap]
lemma ends_scale (i : ℕ) (hf : ContDiff ℝ ∞ f) (c : ℝ) : ends i (c • f)=c • ends i f := by
  induction i generalizing f with
  | zero => rfl
  | succ i ih => rw [← ends_lap,lap_scale' hf,ih (lap_diff hf),ends_lap]
lemma ends_linear (i : ℕ) (hf : ContDiff ℝ ∞ f) (L : F →L[ℝ] E) : ends i (fun x => L (f x))=L (ends i f) := by
  induction i generalizing f with
  | zero => rfl
  | succ i ih => rw [← ends_lap,lap_linear hf,ih (lap_diff hf),ends_lap]
lemma ends_sum {ι : Type*} (s : Finset ι) (i : ℕ) (f : ι → E4 → F) (hf : ∀ a ∈ s,ContDiff ℝ ∞ (f a)) : ends i (∑ a ∈ s, f a) = ∑ a ∈ s, ends i (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty,Finset.sum_empty]
    induction i with
    | zero => rfl
    | succ i ih => rw [← ends_lap,show lap (0:E4→F)=0 from lap_zero _]; exact ih
  | insert a s ha ih =>
    have ht := hf a (Finset.mem_insert_self ..); have hh := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ends_add _ ht (show ContDiff ℝ ∞ (∑ i ∈ s,f i) by rw [funext fun x => Finset.sum_apply x s f]; exact ContDiff.sum hh), ih hh]

lemma lap_value (i) (f : E4 → F) (hf : Pure (2*i) f) : ends (i+1) (qRad • f)= (4*((i:ℝ)+1)*((i:ℝ)+2)) • ends i f := by
  induction i generalizing f with
  | zero =>
    rw [← ends_lap, lap_raise hf]; change ((4*(2+(↑(2*0:ℕ):ℝ)) : ℝ) • f 0 + qRad 0 • lap f 0)=_ • f 0
    simp [qRad]
  | succ i ih =>
    have hh : Pure (2*i) (lap f) := Pure.laplace ((show 2*i+2=2*(i+1) by omega) ▸ hf)
    rw [← ends_lap (i+1),lap_raise hf, ends_add _ (show ContDiff ℝ ∞ ((4 * (2 + (↑(2 * (i + 1):ℕ):ℝ))) • f) from contDiff_const.smul hf.smooth) (pure_square.smooth.smul hh.smooth),
      ends_scale _ hf.smooth _, ih _ hh, ends_lap]
    push_cast; module

def brim (i : ℕ) : ℝ := 4^i * i.factorial * (i+1).factorial

lemma brim_next (i) : brim (i+1)=(4*((i:ℝ)+1)*((i:ℝ)+2))*brim i := by
  unfold brim; rw [Nat.factorial_succ (i+1),Nat.factorial_succ,pow_succ]; push_cast; ring

def Above (i : ℕ) (f : E4 → F) (c : F) := ∃ g,Pure (2*i) g ∧ EqOn g f unitSet ∧ ends i g=brim i • c
def Average (f : E4 → F) (c : F) := ∃ i : ℕ, Above i f c

variable {i : ℕ} {c b : F}

lemma Above.advances (h : Above i f c) (he : i ≤ k) : Above k f c := by
  induction k,he using Nat.le_induction with
  | base => exact h
  | succ k he ih =>
    obtain ⟨Y,hF,hh,hc⟩ := ih
    let L := ContinuousLinearMap.lsmul ℝ (E:=F) ℝ
    refine ⟨qRad • Y,(show 2+2*k=2*(k+1) by omega) ▸ pure_square.bilinear hF L,fun x hx => ?_,?_⟩
    · have ht : ‖x‖=1 := by simpa using hx
      simp [ht,qRad,hh hx]
    rw [lap_value k _ hF,hc,brim_next]; module






lemma Above.plus (h : Above i f c) (he : Above i g b) : Above i (f+g) (c+b) := by
  obtain ⟨F,H1,H2,H3⟩ := h; obtain ⟨G,J1,J2,J3⟩ := he
  refine ⟨F+G,H1.plus J1,fun x hx => congr_arg₂ (·+·) (H2 hx) (J2 hx),?_⟩; rw [ends_add _ H1.smooth J1.smooth,H3,J3,smul_add]
lemma Average.plus (h : Average f c) (he : Average g b) : Average (f+g) (c+b) := by
  obtain ⟨i,h⟩ := h; obtain ⟨j,he⟩ := he; exact ⟨max i j,(h.advances (le_max_left i j)).plus (he.advances (le_max_right i j))⟩
lemma Average.test (h : Average f c) (he : EqOn f g unitSet) : Average g c := by
  obtain ⟨i,F,hF,h,ht⟩ := h; exact ⟨i,F,hF,h.trans he,ht⟩
lemma Average.linear (h : Average f c) (L : F →L[ℝ] E) : Average (fun x => L (f x)) (L c) := by
  obtain ⟨i,F,hF,h,ht⟩ := h; refine ⟨i,fun x => L (F x),hF.linear L,fun x hx => congr_arg L (h hx),?_⟩
  rw [ends_linear _ hF.smooth L,ht,map_smul]
lemma avg_const (c : F) : Average (fun _ => c) c := by
  refine ⟨0,fun _ => c,⟨contDiff_const,fun _ _ => by simp⟩,fun _ _ => rfl,?_⟩; simp [ends,brim]
lemma Average.vScale (h : Average f c) (t : ℝ) : Average (t • f) (t • c) := Average.linear h (t • ContinuousLinearMap.id ℝ _)
lemma Average.sum {ι : Type*} (s : Finset ι) (f : ι → E4 → F) (c : ι → F) (h : ∀ i∈s,Average (f i) (c i)) : Average (fun x => ∑ i∈s,f i x) (∑ i∈s,c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact avg_const _
  | insert a s ha ih => simp_rw [Finset.sum_insert ha]; exact (h _ (Finset.mem_insert_self ..)).plus (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

section harmonic
variable {G : Gauge}

def paths (S T : Sol G.Color j) (i b : Axis) (x : E4) : ℝ := ⟪S.field i b x,T.field i b x⟫
lemma pure_paths (S T : Sol G.Color j) (i b : Axis) : Pure (2*j) (paths S T i b) := by
  rw [two_mul]; exact (pure_diag (S.val i b)).bilinear (pure_diag (T.val i b)) (innerSL ℝ)
lemma lap_paths (S T : Sol G.Color (j+1)) (i b : Axis) : lap (paths S T i b) = (2*((j+1:ℕ):ℝ)^2) • (∑ a : Axis, paths (S.freeze a) (T.freeze a) i b) := by
  funext x; change lap (fun x => innerSL ℝ (diagonal (S.val i b) x) (diagonal (T.val i b) x)) x = _
  rw [lap_pair (diag_smooth (S.val i b) ∞) (diag_smooth (T.val i b) ∞) (innerSL ℝ) x]
  change ⟪lap (S.field i b) x,T.field i b x⟫ + ⟪S.field i b x,lap (T.field i b) x⟫ + _ = _
  rw [S.harmonic, T.harmonic]; simp_rw [show ∀ a : Axis, grad a (diagonal (S.val i b)) = _ from fun a => S.grad_field a i b,
    show ∀ a : Axis,grad a (diagonal (T.val i b)) = _ from fun a => T.grad_field a i b, Pi.smul_apply]
  simp only [inner_zero_left,inner_zero_right,zero_add,mul_assoc,smul_eq_mul,Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  change 2*⟪((j+1:ℕ):ℝ) • (S.freeze a).field i b x, ((j+1:ℕ):ℝ) • (T.freeze a).field i b x⟫ = _
  rw [real_inner_smul_left,real_inner_smul_right]; unfold paths; ring
lemma ends_paths (S T : Sol G.Color j) (i b : Axis) : ends j (paths S T i b)=(2^j * (j.factorial:ℝ)^2)* dotDir (S.val i b) (T.val i b) := by
  induction j with
  | zero =>
    simp only [ends,Function.iterate_zero_apply,pow_zero,Nat.factorial_zero,Nat.cast_one,one_pow,mul_one,one_mul,dotDir_eval]
    simp_rw [show ∀ v : Dirs 0, dir v = fun _ => (0:E4) from fun v => Subsingleton.elim _ _]; simp; rfl
  | succ j ih =>
    let f (a : Axis) := paths (S.freeze a) (T.freeze a) i b
    have hh a : ContDiff ℝ ∞ (f a) := (pure_paths ..).smooth
    rw [← ends_lap, lap_paths]
    rw [ends_scale _ (show ContDiff ℝ ∞ (∑ a : Axis, f a) from (by rw [show (∑ a : Axis,f a)=(fun x => ∑ a : Axis,f a x) from funext fun x => Finset.sum_apply x Finset.univ f]; exact ContDiff.sum fun _ _ => hh _)) _, ends_sum _ _ _ (fun a _ => hh a)]
    unfold f
    simp_rw [fun a => ih (S.freeze a) (T.freeze a),dotDir_eval]
    conv_rhs => rw [sum_dirs]
    simp_rw [dir_cons]
    simp_rw [Nat.factorial_succ,pow_succ (2:ℝ),smul_eq_mul,Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun w _ => ?_
    push_cast; unfold Sol.freeze; simp; ring
lemma avg_paths (S T : Sol G.Color j) (i b : Axis) : Average (paths S T i b) ((2^j *((j:ℝ)+1))⁻¹ * dotDir (S.val i b) (T.val i b)) := by
  refine ⟨j,_,pure_paths S T i b,fun x hx => rfl,?_⟩
  rw [ends_paths,brim,Nat.factorial_succ]
  rw [show (4:ℝ)^j = (2:ℝ)^j * 2^j by rw [← mul_pow]; norm_num]
  simp only [smul_eq_mul]; push_cast; field_simp
end harmonic
end YM.Extra.FD.OPE
