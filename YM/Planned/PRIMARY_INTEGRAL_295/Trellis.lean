import YM.Next.FREE_KERNELS.Signal
import YM.Planned.PRIMARY_INTEGRAL_295.Route
import YM.Work.A12

/-!
# Newton parts for stamped windows

All forward difference comparisons on the cover, also for negative
integer offsets. `piece` here *calls* the recursive Newton pieces for
the forward differences; avoids the inverse estimates/determinant of
reflection samples of other labels. Later use these only on stationary
rows whose pre-L constants pay for the outcomes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Trellis
open Filter Function Set Lattice RG Precision Laurent Next.Free Place 
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def offset (f : Cover→E) (i : Axis) (x : Cover) := f (x+step i)-f x

def delta (f : Cover→E) : List Axis → Cover→E
  | [] => f
  | i::l => offset (delta f l) i

omit [NormedSpace ℝ E] in
lemma delta_plus (f : Cover→E) (l q : List Axis) : delta f (l++q)=delta (delta f q) l := by
  induction l with
  | nil=>rfl
  | cons i l ih=>rw [List.cons_append,delta,delta,ih]
omit [NormedSpace ℝ E] in
lemma offset_exchange (f : Cover→E) (i j : Axis) : offset (offset f i) j = offset (offset f j) i := by
  ext1 x; unfold offset; rw [add_right_comm x]; abel

def sector : ℕ → (Cover→E) → (E4→E)
  | 0 => fun f _ => f 0
  | n+1 => fun f z => (((n+1 : ℕ) : ℝ)⁻¹) • ∑ i : Axis, z i • sector n (offset f i) (z-basis i)

section polynomial
private lemma slot_band (f : E4→E) (i : Axis) (k : ℕ) (h : f∈rangeLt E k) :
    (fun x : E4=> x i • f x)∈rangeLt E (k+1) := by
  let V := EuclideanSpace.proj (𝕜:=ℝ) i
  obtain ⟨p,hp,rfl⟩ := range_decompose h
  rw [show (fun x : E4=> x i • (∑ i,p i) x)=(∑ a, fun x:E4=> x i • p a x) from
    funext fun x => by rw [Finset.sum_apply, Finset.sum_apply, Finset.smul_sum]]
  apply Submodule.sum_mem; intro j _
  obtain ⟨T,hT⟩ := can_write.1 (hp j)
  rw [hT, show (fun x : E4=>x i • Tensor.diagonal T x)=Tensor.diagonal (Tensor.added T V) from
    funext fun x=>(Tensor.added_diag T V x).symm]
  exact exact_le_band (Nat.add_lt_add_right j.isLt _) (simple _)

lemma sector_band (f : Cover→E) (n : ℕ) : sector n f∈ rangeLt E (n+1) := by
  induction n generalizing f with
  | zero => exact exact_le_band (Nat.zero_lt_succ 0) (exact_constant _)
  | succ n ih =>
    have he i : (fun x : E4=> sector n (offset f i) (x-basis i))∈ rangeLt E (n+1) := by
      simp_rw [sub_eq_add_neg]; exact band_shift (ih _) _
    rw [show sector (n+1) f=(((n+1:ℕ):ℝ)⁻¹) • (∑ i:Axis,fun x:E4=> x i • sector n (offset f i) (x-basis i)) from
      funext fun x=>by rw [Pi.smul_apply,Finset.sum_apply]; rfl]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun i _=> slot_band _ i _ (he i)))

/-- Discrete directional derivative of the Newton part. -/
lemma sector_step (f : Cover→E) (j : Axis) (x : E4) (n : ℕ) :
    sector (n+1) f (x+basis j)-sector (n+1) f x=sector n (offset f j) x := by
  classical
  -- pull out the linear coefficient x and group whole residuals
  have he (f : Axis→E4→E) (x : E4) : (∑ i:Axis,(x+basis j) i • f i (x+basis j-basis i)) - (∑ i:Axis,x i • f i (x-basis i)) =
      f j x+∑ i:Axis,x i • (f i (x-basis i+basis j)-f i (x-basis i)) := by
    have hz i : x+basis j-basis i = x-basis i+basis j := by abel
    have hu : ∑ i:Axis,basis j i • f i (x+basis j-basis i)=f j x := by simp
    simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib,hu,smul_sub,Finset.sum_sub_distrib]; simp_rw [hz]; abel
  induction n generalizing f x with
  | zero =>
    rw [sector,sector,← smul_sub,he (fun i => sector 0 (offset f i))]
    simp [sector]
  | succ n ih =>
    let m := n+1
    rw [sector,← smul_sub,he (fun i => sector (n+1) (offset f i))]
    have hv (i : Axis) := ih (offset f i) (x-basis i)
    simp_rw [hv,fun i=> offset_exchange f i j]
    let v := sector (n+1) (offset f j) x
    have hw : ∑ i:Axis,x i • sector n (offset (offset f j) i) (x-basis i)= (m :ℝ) • v := by
      unfold v; rw [sector]; symm
      change (m:ℝ) • (((m:ℝ)⁻¹) • _)=_; rw [smul_smul,mul_inv_cancel₀ (by unfold m; positivity),one_smul]
    rw [hw, show sector (n+1) (offset f j) x+ (m:ℝ) • v = (↑(m+1):ℝ) • v by
      change v + (m:ℝ) • v=_; push_cast; rw [add_smul,one_smul]; abel]
    rw [show (↑(n+1+1):ℝ)=(↑(m+1):ℝ) from rfl, smul_smul,inv_mul_cancel₀ (by positivity),one_smul]

lemma price_point (n : ℕ) : ∃ C : ℝ,1≤C ∧ ∀ (f : Cover→E) (B : ℝ),0≤B →
    (∀ l:List Axis,l.length=n→‖delta f l 0‖ ≤ B) → ∀ x:E4, ‖sector n f x‖ ≤ C*B*(1+‖x‖)^n := by
  induction n with
  | zero =>
    refine ⟨1,le_refl _,fun f B he h x => ?_⟩
    simpa [sector,delta] using h [] rfl
  | succ n ih =>
    obtain ⟨C,hC,H⟩ := ih
    refine ⟨4*C*(2^n:ℝ),one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) hC) (one_le_pow₀ (by norm_num)),fun f B hb hf x=> ?_⟩
    have he (i : Axis) {l : List Axis} (hl : l.length=n) : ‖delta (offset f i) l 0‖ ≤ B := by
      convert hf (l++[i]) (by simp [hl]) using 2; rw [delta_plus]; rfl
    rw [sector,norm_smul]; let p := ((n+1:ℕ):ℝ); have hp : 1≤p := by unfold p; simp
    refine ((mul_le_of_le_one_left (norm_nonneg _) (show ‖p⁻¹‖≤1 by rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hp)).trans (norm_sum_le ..)).trans ?_
    let v := 1+‖x‖; have hv : 1≤v := by simp [v]
    have hh i : ‖x i‖≤ v := (PiLp.norm_apply_le x i).trans (le_add_of_nonneg_left zero_le_one) -- name
    have hk i : 1+‖x-basis i‖≤2*v := by have h := norm_sub_le x (basis i); rw [show ‖basis i‖=1 from by simp] at h; unfold v; linarith [norm_nonneg x]
    refine (Finset.sum_le_sum (g:=fun (_:Axis) => v*(C*B*(2*v)^n)) (fun i _=> ?_)).trans_eq ?_
    · rw [norm_smul]; exact mul_le_mul (hh i) ((H _ B hb (fun l => he i (l:=l)) _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hk i) n) (by positivity))) (norm_nonneg _) (by positivity)
    unfold v; simp [Axis,mul_pow]; ring
end polynomial

def fitting (f : Cover→E) (n : ℕ) (x : Cover) : E := ∑ i∈ Finset.range n, sector i f (seat x)

def surplus (f : Cover→E) (n : ℕ) := f-fitting f n

@[simp] lemma atBase (f : Cover→E) (n : ℕ) : surplus f (n+1) 0=0 := by
  unfold surplus; simp only [Pi.sub_apply, fitting,seat_zero]; rw [Finset.sum_range_succ']; simp [sector]
lemma baked (f : Cover→E) (n : ℕ) (i : Axis) : offset (surplus f (n+1)) i=surplus (offset f i) n := by
  ext x; unfold surplus offset fitting
  simp only [Pi.sub_apply,seat_add,seat_step]
  apply Eq.trans (show _ = (f (x+step i)-f x) - ((∑ j∈Finset.range (n+1), sector j f (seat x+basis i))-(∑ j∈Finset.range (n+1),sector j f (seat x))) by abel)
  congr 1; rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']; simp only [sector_step]
  rw [sector,sub_self,add_zero]; rfl

-- length exactly size x, initial vertex conventions
lemma shortens (x : Cover) (h : x ≠ 0) : ∃ (y : Cover) (i : Axis), size x=size y+1 ∧ (y=x+step i ∨ x=y+step i) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp h
  change x i ≠ 0 at hi
  have hh y (he : ∀ j : Axis,j≠i→x j=y j) (ht : (x i).natAbs=(y i).natAbs+1) : size x=size y+1 := by
    unfold size; rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),← Finset.sum_erase_add _ (fun j=> (y j).natAbs) (Finset.mem_univ i), ht,← add_assoc]; congr 2
    apply Finset.sum_congr rfl; intro j hj; rw [he _ (Finset.ne_of_mem_erase hj)]
  rcases lt_or_gt_of_ne hi with h|h
  · exact ⟨x+step i,i,hh (x+step i) (fun j hj=> by simp [hj]) (by simp; omega),Or.inl rfl⟩
  exact ⟨x-step i,i,hh (x-step i) (fun j hj=>by simp [hj]) (by simp;omega),Or.inr (sub_add_cancel ..).symm⟩

omit [NormedSpace ℝ E] in
lemma telescoped (f : Cover→E) (L : ℕ) (C : ℝ) (hC : 0 ≤ C) (h : ∀ (x : Cover) (i : Axis), size x ≤ L → ‖offset f i x‖≤C)
    (x : Cover) (hx : size x ≤ L) : ‖f x - f 0‖ ≤ C * size x := by
  induction hm : size x using Nat.strong_induction_on generalizing x with
  | h m ih =>
    by_cases he : x = 0
    · rw [he, sub_self,norm_zero]; positivity
    obtain ⟨y,i,he,ht⟩ := shortens x he
    have hl : size y≤L := by omega
    have hy := ih (size y) (by omega) y hl rfl
    have he' : ‖f x-f y‖≤C := by
      rcases ht with h'|h'
      · rw [norm_sub_rev,h']; exact h x i hx
      rw [h']; exact h y i hl
    refine (le_trans (le_of_eq (congr_arg norm (show f x-f 0=(f x-f y)+(f y-f 0) by abel)))
      ((norm_add_le ..).trans (add_le_add he' hy))).trans_eq ?_
    rw [← hm,he,Nat.cast_add]; ring

/-- Signed offsets including negative via actual telescope on the cover.
The coefficient constant need not be resampled for this stencil. -/
lemma accrue (n : ℕ) (f : Cover→E) (M : ℕ) (C : ℝ) (hC : 0≤C) (h : ∀ l : List Axis, l.length=n →
    ∀ y : Cover, size y≤M → ‖delta f l y‖ ≤ C) (x : Cover) (hx : size x ≤ M) : ‖surplus f n x‖ ≤ C * (size x:ℝ)^n := by
  classical
  induction n generalizing f x with
  | zero => simpa [surplus,fitting,delta] using h [] rfl x hx
  | succ n ih =>
    have he (i : Axis) (l : List Axis) (hl:l.length=n) (y : Cover) (hy : size y≤M) : ‖delta (offset f i) l y‖≤ C := by
      have h := h (l++[i]) (by simp [hl]) y hy; rw [delta_plus] at h; exact h
    have H (y : Cover) (i : Axis) (h : size y ≤ size x) : ‖offset (surplus f (n+1)) i y‖ ≤ C*(size x:ℝ)^n := by
      rw [baked]
      apply (ih (offset f i) (he i) y (h.trans hx)).trans
      gcongr
    have hg := telescoped (surplus f (n+1)) (size x) _ (show 0≤C*(size x:ℝ)^n by positivity) H x le_rfl
    rw [atBase,sub_zero] at hg; exact hg.trans_eq (by ring)
end YM.Planned.PrimaryIntegral295.Trellis
