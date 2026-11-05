import YM.Push.LOOP_COEFFICIENT.PlaneRules

/-!
# Ward, rotation and conjugation through the same cofinal periods
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent Precision RG Exterior
open scoped Topology BigOperators ContDiff ComplexConjugate
variable {n : Side} {E F H a b c : Type}
variable [Fintype E] [Fintype F] [Fintype H] [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c]
  {A : Grid n E a} {B : Grid n F b} {C : Grid n H c}

omit [Fintype a] [Fintype c] in
lemma sample_mul (i q j : Site n) (X : Matrix E F ℂ) {Y : Matrix F H ℂ} {W : Matrix b c ℂ} (h : Routed B C q j Y W) :
    sample A C (X*Y) i j = sample A B X i q * W := by
  simp only [sample,Matrix.smul_mul,Matrix.mul_assoc,show Y * plane C j = _ from h]
omit [Fintype a] [Fintype b] in
lemma sample_transpose (i j : Site n) (X : Matrix E F ℂ) : (sample A B X i j).transpose = sample B A X.transpose j i := by
  simp only [sample,transpose_smul,transpose_mul, Matrix.mul_assoc,transpose_transpose]
omit [Fintype E] [Fintype a] [Fintype b] in
lemma plane_star (i : Site n) : (plane A i).conjTranspose = (plane A (-i)).transpose := by
  ext j k
  simp only [conjTranspose_apply,transpose_apply,plane, Matrix.of_apply]
  split
  next h => rw [Complex.star_def,cell_bar,cell_duality (-i),cell_inverse,cell_duality i]
  simp
omit [Fintype a] [Fintype b] in
lemma sample_adj (i j : Site n) (X : Matrix E F ℂ) : (sample A B X i j).conjTranspose = sample B A X.conjTranspose (-j) (-i) := by
  rw [sample,conjTranspose_smul, conjTranspose_mul,conjTranspose_mul,plane_star, show (plane A i).transpose.conjTranspose = (plane A i).conjTranspose.transpose from rfl,plane_star]
  simp only [sample, transpose_transpose,Matrix.mul_assoc]
  congr 1
  simp

omit [Fintype a] [Fintype c] in
lemma sample_sandwich {G : Matrix F E ℂ} {p p' r r' : Site n} {V W : Matrix b a ℂ} (X : Matrix F F ℂ)
    (hG : Routed B A r p G V) (hG' : Routed B A r' p' G W) :
    sample A A (G.transpose * X * G) p p' = V.transpose * sample B B X r r' * W := by
  rw [sample_mul (B:=B) p r' p' _ hG',← transpose_transpose (sample A B (G.transpose * X) p r'), sample_transpose,transpose_mul,
    transpose_transpose,sample_mul r' r p _ hG, transpose_mul,sample_transpose,transpose_transpose]

lemma of_bend_symm [DecidableEq E] {f : (E → ℝ) → ℝ} (hf : ContDiffAt ℝ ω f 0) : (bilinearAt f 0).IsSymm := by
  ext i j; change Work.F05.bend _ _ _ _ = Work.F05.bend _ _ _ _
  exact hf.isSymmSndFDerivAt_of_omega _ _
lemma of_bend_null [DecidableEq E] [DecidableEq F] (f : (E → ℝ) → ℝ) (R : Matrix E F ℝ) (h : ∀ v x,Work.F05.bend f 0 x (R *ᵥ v)=0) : bilinearAt f 0 * R = 0 := by
  apply pairing_ext (Y:=0); intro x v; rw [← Matrix.mulVec_mulVec, bilinearAt_dotProduct, ← Work.F05.bend_apply,h,Matrix.zero_mulVec,dotProduct_zero]
lemma of_bend_congruence [DecidableEq E] {f g : (E → ℝ) → ℝ} (R : Matrix E E ℝ)
    (h : ∀ x y, Work.F05.bend g 0 (R *ᵥ x) (R *ᵥ y) = Work.F05.bend f 0 x y) : R.transpose * bilinearAt g 0 * R = bilinearAt f 0 := by
  apply pairing_ext (Y:=bilinearAt f 0)
  intro x y; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,
    bilinearAt_dotProduct,bilinearAt_dotProduct,← Work.F05.bend_apply, ← Work.F05.bend_apply]; exact h x y

variable {s : ℕ → Side} {G : Gauge} {V W : Momentum → Matrix (Axes G) (Axes G) ℂ}
    {X Y : ∀ i, Matrix (BondKey G (s i)) (BondKey G (s i)) ℝ}

lemma orbit_cont (a : Signed) : Continuous (orbitSymbol G a) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j; unfold orbitSymbol; dsimp only [of_apply]; split
  · unfold corner; split
    · simp_rw [← Complex.exp_neg]; fun_prop
    exact continuous_const
  exact continuous_const
lemma longitudinal_cont : Continuous (longitudinal G) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j; unfold longitudinal; dsimp only [of_apply]; split
  · unfold Exterior.q; fun_prop
  exact continuous_const
lemma signed_cont (s : Signed) : Continuous (s.act (R:=ℂ)) := by
  apply continuous_pi; intro i; unfold Signed.act; split <;> fun_prop
lemma star_signed (s : Signed) (p : Momentum) : star (s.act p) = s.act (star p) := by ext1 i; simp [Signed.act]; split <;> simp

abbrev LinkMirror (X : ∀ i, Matrix (BondKey G (s i)) (BondKey G (s i)) ℝ) (V : Momentum → Matrix (Axes G) (Axes G) ℂ) :=
    Mirrors (fun i => linksGrid G (s i)) (fun i => linksGrid G (s i)) (fun i => cmat (X i)) V

namespace LinkMirror
variable (h : LinkMirror X V) (hs : Expands s) {p : Momentum} (hp : star p = p)
include h hs hp
lemma samples : Tendsto (fun i => sample (linksGrid G (s i)) (linksGrid G (s i)) (cmat (X i)) (-freqSite p (s i)) (freqSite p (s i))) atTop (𝓝 (V p)) := h _ _ _ hp (freq_limit hs hp) fun _ => freq_match ..

lemma symmetric (hX : ∀ i, (X i).IsSymm) : (V p).transpose = V (-p) := by
  refine tendsto_nhds_unique ((continuous_id.matrix_transpose.continuousAt.tendsto.comp (h.samples hs hp)).congr (fun i => ?_))
    (h _ _ _ (by rw [star_neg,hp]) (freq_limit hs hp).neg fun i => (freq_match ..).neg)
  change (sample _ _ _ _ _).transpose = sample _ _ _ (-(-_)) _
  rw [sample_transpose,neg_neg,show (cmat (X i)).transpose=cmat ((X i).transpose) from rfl,hX i]

lemma hermitian (hX : ∀ i, (X i).IsSymm) : (V p).IsHermitian := by
  refine tendsto_nhds_unique ((continuous_id.matrix_conjTranspose.continuousAt.tendsto.comp (h.samples hs hp)).congr (fun i => ?_)) (h.samples hs hp)
  change (sample _ _ _ _ _).conjTranspose = _
  rw [sample_adj,neg_neg, show (cmat (X i)).conjTranspose = cmat ((X i).transpose) from (prom_adj _).symm,hX i]

lemma ward (hX : ∀ i, X i * R_g (1:Wilson.Config G (s i)) = 0) : V p * longitudinal G p = 0 := by
  refine tendsto_nhds_unique (tends_mul (h.samples hs hp) (longitudinal_cont.continuousAt.tendsto.comp (freq_limit hs hp)))
    ((tendsto_const_nhds (x:= (0:Matrix _ _ ℂ))).congr fun i => ?_)
  rw [Function.comp_apply, ← show sample (linksGrid G (s i)) (nodesGrid G (s i)) _ (-freqSite p (s i)) (freqSite p (s i)) = _ from sample_mul _ _ _
    (cmat (X i)) (R_zero_routed (freq_match ..)), ← cmat_mul, hX i, map_zero,sample,Matrix.mul_zero,Matrix.zero_mul,smul_zero]

lemma spin (a : Signed) (hY : LinkMirror Y W) (he : ∀ i, let L := linkSpin a 1; L.transpose * X i * L = Y i) :
    (orbitSymbol G a (-p)).transpose * V (a⁻¹.act p) * orbitSymbol G a p = W p := by
  let M i := cmat (linkSpin a (1:Wilson.Config G (s i)))
  have hm i : (M i).transpose * cmat (X i) * M i = cmat (Y i) := by rw [← he i]; simp only [cmat_mul]; rfl
  have ht := (orbit_cont (G:=G) a)
  let f i := freq p (s i); let k i := freqSite p (s i)
  have hf i : Matches (f i) (k i) := freq_match ..
  have hk : Tendsto f atTop (𝓝 p) := freq_limit hs hp
  have hv i := sample_sandwich (cmat (X i)) (orbit_routed (G:=G) (hf i).neg a) (orbit_routed (G:=G) (hf i) a)
  refine tendsto_nhds_unique ((tends_mul (tends_mul (ht.matrix_transpose.continuousAt.tendsto.comp hk.neg)
    (h _ _ (fun i => a⁻¹.act (k i)) (by rw [star_signed,hp]) ((signed_cont _).continuousAt.tendsto.comp hk) (fun i => (hf i).signed _))) (ht.continuousAt.tendsto.comp hk)).congr
    (fun i => Eq.symm ?_)) (hY _ _ _ hp hk hf)
  simpa only [Signed.act_neg, show ∀ i, (cmat (linkSpin a (1:Wilson.Config G (s i))))= M i from fun _ => rfl, hm] using! hv i

lemma color (he : ∀ i u, let L := linkAdj (constantGauge u); L.transpose * X i * L = X i) (u : G.El) :
    (fiberColor G u).transpose * V p * fiberColor G u = V p := by
  refine tendsto_nhds_unique ((tends_mul (tends_mul tendsto_const_nhds (h.samples hs hp)) tendsto_const_nhds).congr (fun i => Eq.symm ?_)) (h.samples hs hp)
  have hv := sample_sandwich (cmat (X i)) (fiberColor_routed u (-freqSite p (s i))) (fiberColor_routed u (freqSite p (s i)))
  rw [show (cmat (linkAdj (constantGauge u)))ᵀ * cmat (X i) * cmat (linkAdj (constantGauge u)) = cmat (X i) by
        conv_rhs => rw [← he i u]; simp only [cmat_mul]
        rfl] at hv
  exact hv
end LinkMirror
end YM.Push.Loops
