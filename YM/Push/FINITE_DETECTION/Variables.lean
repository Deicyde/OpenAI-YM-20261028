import YM.Push.FINITE_DETECTION.Centered
import YM.Work.G07.Stencil

/-! Linear probe variables diagonalizing the actual reflected one-leg kernel,
and their relation to the radial-jet substitutions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Free
open Function Set Filter Maxwell Kelvin
open scoped Topology BigOperators ContDiff ComplexConjugate
variable {G : Gauge} {j l : ℕ}

lemma frob_symm (Y Z : Shell G j) : asProbe Y Z = asProbe Z Y := by
  change frob Y.val Z.val = frob Z.val Y.val
  rw [frob_apply, frob_apply]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => mul_comm ..

lemma frob_pos (Y : Shell G j) (h : Y ≠ 0) : 0 < asProbe Y Y := by
  by_contra! hv
  change frob Y.val Y.val ≤ 0 at hv
  rw [frob_apply] at hv; simp_rw [← sq] at hv
  have he := le_antisymm hv (by positivity)
  rw [Finset.sum_eq_zero_iff_of_nonneg (by intros; positivity)] at he
  apply h; apply Subtype.ext
  funext i k; ext1 u; ext1 c
  have he := he c (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (by intros; positivity)] at he; specialize he i (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (by intros; positivity)] at he; specialize he k (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (by intros; positivity)] at he
  change (Y.val i k u) c = 0
  rw [show u = fun a : Fin j => ∑ q : Axis, u a q • basis q from funext fun a => (space_expand _).symm,
    ContinuousMultilinearMap.map_sum]
  change EuclideanSpace.proj (𝕜 := ℝ) c _ = 0
  rw [map_sum]
  apply Finset.sum_eq_zero; intro r _
  have hv : (Y.val i k (basis ∘ r)) c = 0 := sq_eq_zero_iff.mp (he r (Finset.mem_univ _))
  change (Y.val i k (fun a => _ • (basis ∘ r) a)) c = _
  rw [(Y.val i k).map_smul_univ]; simp [hv]

def pairingShell : LinearMap.BilinForm ℝ (Shell G j) where
  toFun := asProbe
  map_add' Y Z := by ext1 X; change frob _ _ = frob _ _ + frob _ _; simp [frob_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c Y := by ext1 X; change frob _ _ = c * frob _ _; simp [frob_apply, mul_assoc, Finset.mul_sum]

lemma fullPair : Bijective (pairingShell (G := G) (j := j)) := by
  let L := pairingShell (G := G) (j := j)
  change Bijective L
  have hi : Injective L := fun x y h => by
    by_contra hxy
    have he : L (x-y) = 0 := by rw [map_sub,h,sub_self]
    exact (frob_pos _ (sub_ne_zero.mpr hxy)).ne' (LinearMap.congr_fun he (x-y))
  refine ⟨hi,LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq ?_)⟩
  exact (LinearMap.finrank_range_of_inj hi).trans (Subspace.dual_finrank_eq ..).symm

lemma orthShell (G : Gauge) (j : ℕ) : ∃ Y : Module.Basis (Fin (legDim G j)) ℝ (Shell G j),
    LinearMap.IsOrthoᵢ pairingShell Y := LinearMap.BilinForm.exists_orthogonal_basis ⟨frob_symm⟩

def picked (t : Slot G) := (orthShell G t.1).choose t.2
def lengthSq (t : Slot G) := gain t.1 * asProbe (picked t) (picked t)
lemma lengthSq_pos (t : Slot G) : 0 < lengthSq t :=
  mul_pos gain_pos (frob_pos _ ((orthShell G t.1).choose.ne_zero t.2))

lemma picked_matrix (a b : Slot G) : pairCol (picked a) (picked b) = if a=b then lengthSq a else 0 := by
  rcases a with ⟨i,a⟩; rcases b with ⟨j,b⟩
  rcases eq_or_ne i j with he|he
  · subst j
    rw [pairCol_diag]
    split_ifs with hab
    · have h : a=b := Sigma.mk.inj_iff.mp hab |>.2 |> eq_of_heq; subst a; rfl
    have h : b ≠ a := fun e => hab (by subst a; rfl)
    rw [show frob (picked (G := G) ⟨i,b⟩).val (picked ⟨i,a⟩).val = 0 from (orthShell G i).choose_spec h, mul_zero]
  rw [if_neg (by simp [he]), pairCol_distinct (j := i) (l := j) _ _ he]

/-! Formal linear combinations of order-1 (in field degree, not Taylor degree)
variables. `ordinary` goes into the actual `WickPol`. -/
abbrev Vars (G : Gauge) := Slot G →₀ ℂ

def e (a : Slot G) : Vars G := Finsupp.single a 1

def ordinary (G : Gauge) : Vars G →ₗ[ℂ] WickPol G := Finsupp.linearCombination ℂ MvPolynomial.X
@[simp] lemma ordinary_e (a : Slot G) : ordinary G (e a) = MvPolynomial.X a := by simp [ordinary,e]

def encode (p : Probe G j) : Vars G := ∑ i : Fin (legDim G j), ((p (frame G j i) : ℂ)) • e ⟨j,i⟩
lemma ordinary_encode (p : Probe G j) : ordinary G (encode p) = symbol j p := by
  simp only [encode,map_sum,map_smul,ordinary_e, MvPolynomial.smul_eq_C_mul, symbol]
lemma at_encode (p : Probe G j) (A : TaylorTower G) : probe A (ordinary G (encode p)) = (p (A j) : ℂ) :=
  congr_arg (probe A) (ordinary_encode _ ) |>.trans (symbol_test ..)

def tensorMatrix (B : Slot G → Slot G → ℂ) : Vars G →ₗ[ℂ] Vars G →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ fun i => Finsupp.linearCombination ℂ (B i)
@[simp] lemma tensorMatrix_e (B : Slot G → Slot G → ℂ) (a b) : tensorMatrix B (e a) (e b) = B a b := by
  simp [tensorMatrix,e]

def Q (G : Gauge) := tensorMatrix (G := G) fun a b => (legKernel (coordinateLeg a) (coordinateLeg b) pole : ℂ)

lemma pairing_encode_at (p : Probe G j) (q : Probe G l) {x : E4} (hx : x ∈ away) :
    tensorMatrix (fun a b => (legKernel (coordinateLeg a) (coordinateLeg b) x : ℂ)) (encode p) (encode q) = (pairing hx p q : ℝ) := by
  have he {j} (p : Probe G j) : p = ∑ i : Fin (legDim G j), p (frame G j i) • coordinateLeg ⟨j,i⟩ := by
    ext1 Y; conv_lhs => arg 2; rw [← (frame G j).sum_repr Y]
    let B (i : Fin (legDim G j)) : Probe G j := coordinateLeg ⟨j,i⟩
    change p _ = (∑ i, p (frame G j i) • B i) Y
    simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  conv_rhs => rw [he p, he q]
  simp only [encode,map_sum,map_smul, LinearMap.sum_apply,LinearMap.smul_apply,Complex.ofReal_sum,Complex.ofReal_mul, smul_eq_mul]
  simp only [Finset.mul_sum,tensorMatrix_e]
  rfl

lemma pairing_encode (p : Probe G j) (q : Probe G l) : Q G (encode p) (encode q) = (pairing pole_in p q : ℝ) := pairing_encode_at p q pole_in

def eigenVar (a : Slot G) := ∑ i ∈ Finset.range (a.1+1), encode (column (picked a) i)
def reflectedVar (a : Slot G) := ∑ i ∈ Finset.range (a.1+1), encode ((column (picked a) i).comp mirrorJet)

lemma pairing_var (a b : Slot G) : Q G (eigenVar a) (reflectedVar b) = if a=b then (lengthSq a : ℂ) else 0 := by
  simp only [eigenVar,reflectedVar,map_sum,LinearMap.sum_apply,pairing_encode]
  rw [Finset.sum_comm]
  simpa only [pairCol,form,Complex.ofReal_sum,apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero]
    using congr_arg (fun x : ℝ => (↑x : ℂ)) (picked_matrix a b)

def forward (G : Gauge) : WickPol G →ₐ[ℂ] WickPol G := MvPolynomial.aeval (fun i => ordinary G (eigenVar i))
def reversed (G : Gauge) : WickPol G →ₐ[ℂ] WickPol G := MvPolynomial.aeval (fun i => ordinary G (reflectedVar i))

lemma coversVars (p : Probe G j) : symbol j p ∈ (forward G).range := by
  induction j using Nat.strong_induction_on with | h j ih => ?_
  let b := (orthShell G j).choose.map (LinearEquiv.ofBijective (pairingShell (G := G) (j := j)) fullPair)
  rw [← b.sum_repr p]
  have ht : symbol j (∑ i, b.repr p i • b i) = ∑ i, (b.repr p i : ℂ) • symbol j (b i) :=
    equalPol _ _ (fun A => by simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply, smul_eq_mul,symbol_test, Complex.ofReal_sum,Complex.ofReal_mul])
  rw [ht]
  apply Subalgebra.sum_mem; intro i _
  have he : b i = asProbe (picked ⟨j,i⟩) := rfl
  apply Subalgebra.smul_mem
  have hw : forward G (MvPolynomial.X ⟨j,i⟩) = symbol j (b i) + ∑ k ∈ Finset.range j, symbol k (column (picked ⟨j,i⟩) k) := by
    simp only [forward,MvPolynomial.aeval_X,eigenVar,map_add,map_sum,ordinary_encode, he,Finset.sum_range_succ,column_self,add_comm]
  rw [eq_sub_of_add_eq hw.symm]; exact Subalgebra.sub_mem _ ⟨_,rfl⟩ (Subalgebra.sum_mem _ fun k hk => ih k (Finset.mem_range.mp hk) _)

lemma forward_full (G : Gauge) : Surjective (forward G) := fun q => by
  change q ∈ (forward G).range
  induction q using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a,MvPolynomial.aeval_C ..⟩
  | add _ _ hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X _ i hp => exact Subalgebra.mul_mem _ hp (symbol_coordinate i ▸ coversVars (coordinateLeg i))

def reflectedTower (A : TaylorTower G) : TaylorTower G := fun j => mirrorJet (A j)
lemma reflects_at (A : TaylorTower G) (p : WickPol G) : probe A (reversed G p) = probe (reflectedTower A) (forward G p) := by
  suffices (probe A).comp (reversed G) = (probe (reflectedTower A)).comp (forward G) from DFunLike.congr_fun this p
  ext a
  simp [reversed,forward,reflectedVar,eigenVar,at_encode,reflectedTower]

def barred (p : WickPol G) := MvPolynomial.map (starRingEnd ℂ) p
@[simp] lemma eval_bar (A : TaylorTower G) (p : WickPol G) : probe A (barred p) = star (probe A p) := by
  unfold barred
  induction p using MvPolynomial.induction_on with
  | C a => simp [probe]
  | add _ _ hp hq => rw [map_add,map_add,map_add,hp,hq,star_add]
  | mul_X _ i hp => rw [map_mul,map_mul,map_mul,hp,MvPolynomial.map_X]; simp [probe]
lemma forward_bar_at (A : TaylorTower G) (p : WickPol G) : probe A (forward G (barred p)) = star (probe A (forward G p)) := by
  unfold barred
  induction p using MvPolynomial.induction_on with
  | C a => simp [forward,probe]
  | add _ _ hp hq => rw [map_add,map_add,map_add,map_add,map_add,hp,hq,star_add]
  | mul_X _ i hp => rw [map_mul,map_mul,map_mul,map_mul,map_mul,hp,MvPolynomial.map_X]
                    simp [forward, eigenVar,at_encode]

lemma reversed_observable {v : Labels.Label G j} {p : WickPol G} (h : observable G j v = forward G p) :
    observable G j (Labels.tensor σ (Labels.realBar v)) = reversed G (barred p) := by
  apply equalPol; intro A
  change probe A (reduceEq (Labels.rotated σ (Labels.realBar v).val)) = _
  rw [jet_value,Labels.rotated,σ_inv,Labels.eval_changed]
  rw [reflects_at,forward_bar_at,← h]
  change Labels.read (Labels.changedJet _ _) (Labels.conjPol _) = star (probe _ (reduceEq v.val))
  rw [jet_value, Labels.conj_value]
  congr 3; exact funext fun i => (gaugeMirror (A i)).symm
end YM.Push.FiniteDetection.Free
