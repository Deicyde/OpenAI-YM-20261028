import YM.Next.FREE_KERNELS.Gear

/-!
# On the actual patch

Verify `mean` starting with the patch's fixed positive line reads, J-fold
roll (including multiplicity), with its weights / counts. Any period; paths
that repeat sites still count each edge read. Tensorless coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Finset
open scoped Topology BigOperators ComplexConjugate

lemma midpoint_given (P : Patch) (x : Axis → Fin P.L.val) :
    (fun i => ((x i).val:ℤ) - mid P.L) ∈ box (P.L.val/2) := by
  have he := mid_double P.L P.odd_side
  rw [box_test]; constructor <;> intro i <;> have hi := (x i).isLt <;> unfold mid at * <;> omega

def aim (P : Patch) (x : Axis → Fin P.L.val) : P.Small := ⟨_,midpoint_given P x⟩
lemma aim_bijective (P : Patch) : Function.Bijective (aim P) := by
  constructor
  · intro a b h; have he := congr_arg Subtype.val h
    apply funext; intro i; apply Fin.ext; have hh := congr_fun he i; change (↑(a i).val:ℤ)-_=(↑(b i).val:ℤ)-_ at hh; omega
  intro x
  have he i : ∃ a : Fin P.L.val, (↑a.val:ℤ)-mid P.L=x.val i := by
    let y := x.val i
    have ht : -mid P.L≤y ∧ y≤mid P.L := ⟨(box_test.mp x.property).1 i,(box_test.mp x.property).2 i⟩
    have hc := mid_double P.L P.odd_side
    refine ⟨⟨(y+mid P.L).toNat,?_⟩,?_⟩ 
    · omega
    change ((y + mid P.L).toNat:ℤ)-_=_; omega
  choose a ha using he; exact ⟨a,Subtype.ext (funext ha)⟩

lemma pays_area (P : Patch) (p : Momentum) :
    (Fintype.card P.Small:ℂ)⁻¹ * ∑ b : P.Small, mode p b.val=area P.L p := by
  let L := P.L
  let e := Equiv.ofBijective (aim P) (aim_bijective P)
  let f (i : Axis) (n : Fin L.val) := twirl (p i) ((n.val:ℤ)-mid L)
  have he (a : Axis → Fin P.L.val) : mode p (e a).val=∏ i, f i (a i) := by
    unfold mode; rw [Finset.mul_sum,Complex.exp_sum]; refine Finset.prod_congr rfl fun i _ => ?_
    unfold f twirl; change Complex.exp (Complex.I*(p i*(((a i).val:ℤ)-mid P.L:ℤ)))=_; congr 1; ring
  have hp : Fintype.card P.Small=L.val^4 := by rw [← Fintype.card_congr e]; simp [Axis,L]
  rw [hp,← e.sum_comp, Nat.cast_pow]; simp_rw [he]; rw [← Fintype.prod_sum f]
  have hh (i : Axis) : plank P.L (p i)=(L.val:ℂ)⁻¹ * ∑ n : Fin L.val, f i n := by rw [plank_centers]; exact congr_arg ((L.val:ℂ)⁻¹*·) (Fin.sum_univ_eq_sum_range (fun n => twirl (p i) ((n:ℤ)-mid L)) L.val).symm
  unfold area; simp_rw [hh]; simp [Finset.prod_mul_distrib, Axis]

lemma pays_roll (P : Patch) (p : Momentum) :
    ∑ a : P.Points, (P.weight a:ℂ)*mode p a.val=massFilter P p := by
  have hm (s : Finset (Fin P.J)) (t : P.Rolls) : mode p (∑ i∈s,(t i).val)=∏ i∈s, mode p (t i).val := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s h ih => rw [Finset.sum_insert h,Finset.prod_insert h,mode_shift,ih]
  let f (i : Fin P.J) (x : P.Small) := mode p x.val
  have hc := calc
    (∑ a : P.Points, (P.weight a:ℂ)*mode p a.val) = ∑ b : P.Rolls, ((Fintype.card P.Rolls:ℂ)⁻¹) * mode p (P.addRoll b).val := by
      unfold Patch.weight; simp_rw [Complex.ofReal_sum,Finset.sum_mul]
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _ => ?_
      simp_rw [apply_ite ((↑) : ℝ → ℂ), Complex.ofReal_zero, Complex.ofReal_inv,Complex.ofReal_natCast, ite_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ,if_true]
    _ = (Fintype.card P.Rolls:ℂ)⁻¹*∑ t : P.Rolls, ∏ i, f i (t i) := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by unfold f Patch.addRoll; rw [hm]
    _ = ((Fintype.card P.Small:ℂ)⁻¹ *∑ a : P.Small, mode p a.val)^P.J := by rw [← Fintype.prod_sum f]; simp [f,Patch.Rolls,mul_pow]
    _ = _ := by rw [pays_area]
  exact hc

variable {c f : Side} (S : StepData c f)

lemma line_walk (x : Site f) (i : Axis) (n : ℕ) (a : form 1 f) :
    integralLink x (List.replicate n (posDir i)) a = ∑ l∈Finset.range n, a (x+l • step i,coord i) := by
  change linkSum _ _ _ = _
  induction n generalizing x with
  | zero => simp [linkSum]
  | succ n ih =>
    rw [List.replicate_succ,linkSum, ih, Finset.sum_range_succ']
    simp only [posDir, Bool.false_eq_true,↓reduceIte, Step.used,Step.vec,zero_smul,add_zero,succ_nsmul]
    rw [add_comm]; congr! 2 with a b; abel_nf

lemma mean_run_real (a : form 1 f) (x : Body 1 c) :
    (mean S *ᵥ a) x = ∑ y : S.patch.Points, S.patch.weight y *
      ∑ l∈Finset.range S.patch.L.val, a (atPoint S x.1 y+l • step (axisEquiv.symm x.2),x.2) := by
  simp only [mean,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    StepData.repath,line_walk,smul_eq_mul,show coord (axisEquiv.symm x.2)=x.2 from axisEquiv.apply_symm_apply _]

lemma mean_run (a : Body 1 f → ℂ) (x : Body 1 c) :
    (approached (mean S) *ᵥ a) x = ∑ y : S.patch.Points, (S.patch.weight y:ℂ)*
      ∑ l∈Finset.range S.patch.L.val, a (atPoint S x.1 y+l • step (axisEquiv.symm x.2),x.2) := by
  apply Complex.ext
  · have hm := mean_run_real S (fun i => (a i).re) x
    simpa [approached, Matrix.mulVec,dotProduct,Complex.mul_re,Complex.re_sum] using hm
  have hm := mean_run_real S (fun i => (a i).im) x; simpa [approached, Matrix.mulVec,dotProduct,Complex.mul_im,Complex.im_sum] using hm

lemma pays_route (p : Site c) (l : Site S.patch.L) (x : Body 1 c) :
    let q := aliasAt (mon p) l; let i := axisEquiv.symm x.2
    ∑ y : S.patch.Points, (S.patch.weight y:ℂ) * ∑ k∈Finset.range S.patch.L.val, mode q (lift (atPoint S x.1 y+k • step i)) =
      cell p x.1 * (S.patch.L.val:ℂ)*pullLine S.patch i q := by
  intro q i
  let L := S.patch.L
  have he (y : S.patch.Points) (k : ℕ) :
      mode q (lift (atPoint S x.1 y+k • step i))=mode q y.val*cell p x.1*twirl (q i) k := by
    have ht : mode q (lift (atPoint S x.1 y + k • step i))=mode q (y.val+L.val • lift x.1+k • step i) := by
      apply mesh_alias S.ratio
      rw [wrap_lift,map_add,map_nsmul, wrap_step, map_add]; rfl
    have hh : mode q (k • (step i:Cover))=twirl (q i) k := by rw [← mode_scale,Exterior.factor,Pi.smul_apply,nsmul_eq_mul]; unfold twirl; push_cast; congr 1; ring
    rw [ht,mode_shift,mode_shift,← mode_scale,hh,show L.val • q=_ from alias_scale (mon p) l,mode_phase,mode_periodic,mul_one]; rfl
  simp_rw [he,← Finset.mul_sum]; unfold pullLine rail
  rw [← pays_roll S.patch]
  have h0 := side_ne L; unfold L at *; simp_rw [Finset.sum_mul, Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_; field_simp
lemma patch_service : Runs (rotations c (TypeFace 1)) (readings S.ratio (TypeFace 1)) (mean S)
    (fiber fun p : Site c => upAlias fun l : Site S.patch.L =>
      (S.patch.L.val:ℂ) • mask 1 (fun i => pullLine S.patch i (aliasAt (mon p) l))) := by
  unfold Runs; ext ⟨x,b⟩ ⟨p,l,i⟩
  let L := S.patch.L
  let a := axisEquiv.symm b
  let q := aliasAt (mon p) l
  rw [rot_fiber]
  change (approached (mean S) *ᵥ fun v => (readings S.ratio (TypeFace 1)) v (p,l,i)) (x,b) = cell p x*((L.val:ℂ) • mask 1 _) b i
  rw [mean_run]; simp_rw [sample]; rw [Matrix.smul_apply, mask_value]; by_cases h : b=i
  · simp only [h,if_true];
    have he := pays_route S p l (x,b); dsimp only at he; subst i; exact he.trans (mul_assoc ..)
  simp [h]
end YM.Next.Free
