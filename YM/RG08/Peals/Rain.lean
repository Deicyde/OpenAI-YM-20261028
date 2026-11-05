import YM.RG08.Peals.Song

/-! # Spatial rank summations of finite batch -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff
variable {α X ι : Type}

abbrev wheel (n : ℕ) := Finset.antidiagonal n

lemma triangle_sum {R : Type*} [AddCommMonoid R] (f : ℕ → ℕ → R) (L M : ℕ)
    (h : ∀ x y,f x y≠0 → x < L+1 ∧ y < M+1) : (∑ x∈range (L+1), ∑ y∈range (M+1), f x y) =
    (∑ z∈range (L+M+1), ∑ p∈ wheel z,f p.1 p.2) := by
  classical
  let T := (range (L+M+1)).sigma wheel
  let S : Finset (ℕ×ℕ) := (range (L+1)) ×ˢ range (M+1)
  let g (x : Sigma (fun _ : ℕ=> ℕ×ℕ)) := f x.2.1 x.2.2
  rw [← Finset.sum_sigma (t:=wheel) (f:=fun i=>f i.2.1 i.2.2), ← Finset.sum_product' _ _ f]
  let V (i : ℕ×ℕ) : Sigma (fun _ : ℕ=> ℕ ×ℕ) := ⟨i.1+i.2,i⟩
  have hx : Injective V := by intro i j hj; exact congr_arg (fun q : Sigma (fun _ : ℕ=> ℕ×ℕ) => q.2) hj
  have hp (i) (hi : i∈ S) : V i∈T := by
    have he := mem_product.mp hi; simp only [mem_range] at he; refine mem_sigma.mpr ⟨mem_range.mpr ?_,mem_antidiagonal.mpr rfl⟩; unfold V; simp; omega
  change ∑ i∈S, f i.1 i.2=∑ j∈T,g j
  rw [← show (∑ j∈S.image V,g j)=∑ i∈S,f i.1 i.2 from sum_image (g:=V) (f:=g) hx.injOn]
  apply sum_subset (by intro i hi; obtain ⟨p,h,rfl⟩ := mem_image.mp hi; exact hp p h)
  intro i hi hy; contrapose! hy; obtain ⟨x,i,j⟩ := i
  have hh := h i j hy; have he := mem_antidiagonal.mp (mem_sigma.mp hi).2
  refine mem_image.mpr ⟨(i,j),mem_product.mpr ⟨mem_range.mpr hh.1,mem_range.mpr hh.2⟩,?_⟩; change Sigma.mk (i+j) _=Sigma.mk _ _; rw [show i+j=x from he]

section calculus
variable [Fintype X] [DecidableEq X]
lemma arch_total_l (K : Matrix X X ℝ) {F H : Psalm X} (h : ContDiff ℝ ω F) (g : ContDiff ℝ ω H) (P : Psalm X) : arch K (F+H) P=arch K F P+arch K H P := by
  ext1 x; simp only [arch,Daddition _ h g,Pi.add_apply,mul_add,add_mul,sum_add_distrib]
lemma arch_total_r (K : Matrix X X ℝ) {F H : Psalm X} (h : ContDiff ℝ ω F) (g : ContDiff ℝ ω H) (P : Psalm X) : arch K P (F+H)=arch K P F+arch K P H := by
  ext1 x; simp only [arch,Daddition _ h g,Pi.add_apply,mul_add,sum_add_distrib]
@[simp] lemma arch_stop (K : Matrix X X ℝ) (F : Psalm X) : arch K 0 F=0 := by ext1 x; change arch K (fun _=>0) F x= (0:ℝ); simp [arch,D]
@[simp] lemma arch_wait (K : Matrix X X ℝ) (F : Psalm X) : arch K F 0=0 := by ext1 x; change arch K F (fun _=>0) x= (0:ℝ); simp [arch,D]
lemma arch_first (K : Matrix X X ℝ) (s : Finset ι) {f : ι→Psalm X} (h : ∀ i∈s,ContDiff ℝ ω (f i)) (g : Psalm X) :
    arch K (∑ i∈s,f i) g=∑ i∈s,arch K (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hv (j) (hj : j∈s) := h j (mem_insert_of_mem hj)
    rw [sum_insert hi,sum_insert hi,arch_total_l _ (h _ (mem_insert_self ..)),ih hv]; rw [show (∑ i∈s,f i)=(fun x => ∑ i∈s,f i x) from funext fun x=> Finset.sum_apply x ..]; exact ContDiff.sum hv
lemma arch_second (K : Matrix X X ℝ) (s : Finset ι) {f : ι→Psalm X} (h : ∀ i∈s,ContDiff ℝ ω (f i)) (g : Psalm X) :
    arch K g (∑ i∈s,f i)=∑ i∈s, arch K g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hv (j) (hj : j∈s) := h j (mem_insert_of_mem hj)
    rw [sum_insert hi,sum_insert hi,arch_total_r _ (h _ (mem_insert_self ..)),ih hv]; rw [show (∑ i∈s,f i)=(fun x => ∑ i∈s,f i x) from funext fun x=> Finset.sum_apply x ..]; exact ContDiff.sum hv
lemma lap_sum (K : Matrix X X ℝ) (s : Finset ι) {f : ι→Psalm X} (h : ∀ i∈s,ContDiff ℝ ω (f i)) :
    lap K (∑ i∈s,f i)=∑ i∈s, lap K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact lap_const _ _
  | insert i s hi ih =>
    have hv j (hj:j∈s):= h j (mem_insert_of_mem hj)
    rw [sum_insert hi,sum_insert hi,lap_total _ (h _ (mem_insert_self ..)),ih hv]; rw [show (∑ i∈s,f i)=(fun x => ∑ i∈s,f i x) from funext fun x=> Finset.sum_apply x ..]; exact ContDiff.sum hv
end calculus

variable [Fintype α] [DecidableEq α] {V W : Verse α} {n L p : ℕ} {m : Side} {M : Row α α}
private lemma arch_zero_left (A : Shale α 0) (f : Psalm (Co m α)) : arch (M.acts m) (stanza A m) f=0 := by
  funext x; unfold stanza arch; simp_rw [Dhush]; simp
private lemma arch_zero_right (A : Shale α 0) (f : Psalm (Co m α)) : arch (M.acts m) f (stanza A m)=0 := by
  funext x; unfold stanza arch; simp_rw [Dhush]; simp
private lemma lap0 (A : Shale α 0) : lap (M.acts m) (stanza A m)=0 := by
  funext x; unfold stanza lap; simp_rw [Dhush]; simp [D]
private lemma lap1 (A : Shale α 1) : lap (M.acts m) (stanza A m)=0 := by
  have h : Tensor.Sym (recital A m) := fun v s=> by rw [show v ∘ s=v from funext fun _=>congr_arg v (Subsingleton.elim ..)]
  funext x; unfold stanza lap; simp_rw [Dfade _ (recital A m) (n:=0) h]; norm_num [Dhush]

def grand (M : ℕ) (V : Verse α) (m : Side) := ∑ r∈range (M+1), stanza (V r) m
lemma gran_lap (h : Whole M) (hp : ∀ r,Tunable (V r)) : lap (M.acts m) (grand (n+2) V m)=grand n (fun r=> chirp M (some m) (V (r+2))) m := by
  unfold grand; rw [lap_sum (h:=fun i _=> stanza_smooth (V i) m),sum_range_succ',sum_range_succ',lap0,lap1,add_zero,add_zero]; apply sum_congr rfl; intro i _; exact (tiring h (hp _) m).symm
lemma repeat_gran_arch (h : Whole M) (hv : ∀ r, Tunable (V r)) (hw : ∀ r, Tunable (W r)) (he : ∀ i,L+1 < i → V i=0) (hW : ∀ i,n+1 < i → W i=0) :
    arch (M.acts m) (grand (L+1) V m) (grand (n+1) W m)=grand (L+n) (symphony M V W) m := by
  unfold grand; rw [arch_first (h:=fun i _=> stanza_smooth (V i) m)]; simp_rw [arch_second (s:=range (n+1+1)) _ (fun i _=> stanza_smooth (W i) m)] -- syntax
  rw [sum_range_succ']; simp only [arch_zero_left,sum_const_zero,add_zero];
  simp_rw [sum_range_succ' (n:=n+1),arch_zero_right,add_zero]
  let F i j := arch (M.acts m) (stanza (V (i+1)) m) (stanza (W (j+1)) m)
  rw [triangle_sum F L n]; refine sum_congr rfl (fun i _=> ?_)
  · rw [symphony,stanza_sum _ _ (fun j _=> (prolong_tunable _ (medley_tunable h (hv _|>.1) (hw _|>.1))).1)]
    apply sum_congr rfl; intro v hh
    have hu := mem_antidiagonal.mp hh;
    rw [← hu,prolong_self]; exact (duets_play (hv _) (hw _) h m).symm
  intro i j hf
  constructor
  · by_contra hv; rw [show F i j=0 by unfold F; rw [he _ (by omega),stanza_zero,arch_stop]] at hf; contradiction
  by_contra hy; rw [show F i j=0 by unfold F; rw [hW _ (by omega),stanza_zero,arch_wait]] at hf; contradiction
end YM.RG08
