import YM.Next.FREE_KERNELS.Signed
import YM.Work.F07


/-!
# Bed preparation per smoothing index (before L)

`Quote` includes both projections of trace budget and the books with roots.
Pay a uniform family of sufficiently small direct prices. Kernel k, the
prescribed positive penalty coefficient, stays fixed. No free β or fit of
the continuum budgets implied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid
open Work.F06 (sqLength pairingRe countCeil)
open Work.F07 (Band)
open scoped Topology BigOperators ComplexConjugate
variable {j : ℕ}

lemma full_cover (M : Bed) (p : Clip) (n : Side) : (M.full p n).transpose*M.full p n=p.direct • 1+(M.roots.acts n).transpose*M.roots.acts n := by
  let H := (1:Matrix (Body 2 n) (Body 2 n) ℝ); let D := M.roots.acts n
  have he (a b : Body 2 n) : ∑ i, Real.sqrt p.direct * H i a * (Real.sqrt p.direct*H i b)=p.direct * H a b := by
    have ht := Real.sq_sqrt p.quadratic_pos.le
    calc
      _ = p.direct*(H.transpose*H) a b := by rw [mul_apply,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Matrix.transpose_apply,show Real.sqrt p.direct*H i a*(Real.sqrt p.direct*H i b)=Real.sqrt p.direct ^ 2*(H i a*H i b) by ring,ht]
      _ = _ := by unfold H; simp
  ext a b; rw [Matrix.mul_apply,Fintype.sum_prod_type]; simp only [Bed.full,of_apply, Matrix.transpose_apply,Fintype.sum_sum_type]
  change ∑ x : Site n, ((∑ i, _) + (∑ j,_)) = _
  rw [Finset.sum_add_distrib]; rw [Matrix.add_apply,Matrix.smul_apply,Matrix.mul_apply,Fintype.sum_prod_type]
  specialize he a b
  rw [Fintype.sum_prod_type] at he
  change (∑ x : Site n, ∑ i, Real.sqrt p.direct * H (x,i) a * (Real.sqrt p.direct * H (x,i) b)) + _ = _
  rw [he]; rfl

lemma low_ceiling {m : Type} [Fintype m] {X : Row m m} {v A : ℝ} (hf : Funds X v A) (hc : RG.Clip)
    [DecidableEq m] (hq : hc.direct≤v/2) (U : ℝ) (hu : A≤U) (hh : Whole X) : Funds (minusRows X (scaleRows hc.direct (unitRow m))) (v/2) U := by
  intro p hp; have h := hf p hp
  rw [read_less hh.safe ((Whole.coin m).weight _).safe hp,read_weight,read_unit]
  constructor
  · unfold IsHermitian; rw [Matrix.conjTranspose_sub,h.1]; simp
  intro x
  change v/2*sqLength x ≤ pairingRe _ x x ∧ pairingRe _ x x ≤ U*sqLength x
  rw [Work.F06.pairingRe_sub,Work.F06.pairingRe_scale,price_unit]
  have he : v*sqLength x ≤ pairingRe _ x x ∧ pairingRe _ x x ≤ A*sqLength x := h.2 x
  have hx := Work.F06.sqLength_nonneg x
  have h1 := mul_nonneg hc.quadratic_pos.le hx
  have h2 := mul_le_mul_of_nonneg_right hq hx
  have h3 := mul_le_mul_of_nonneg_right hu hx
  constructor <;> linarith

/-- Exact fixed rows of a Bed; independent of choice of path lengths. -/
structure Defined (k l : ℝ) (v : Train j) (M : Bed) : Prop where
  diag : M.diagonal=pink k v
  dual : M.dual_diag=blue k v
  metric : M.metric=amend k l v
  inverse : M.inverse=pledge k l v

lemma floor_revise {M : Bed} {a : Clip} {n : Side} {v w V W : ℝ} (h : Floor M a n v w) (ht : V≤v) (hu : w≤W) : Floor M a n V W := by
  have hm (A : Matrix (Body 2 n) (Body 2 n) ℝ) (ha : Numeric A v w) : Numeric A V W := by
    intro i; constructor
    · exact (mul_le_mul_of_nonneg_right ht (by unfold dotProduct; apply Finset.sum_nonneg; intro k _; rw [← sq]; positivity)).trans (ha _).1
    exact (ha i).2.trans (mul_le_mul_of_nonneg_right hu (by unfold dotProduct; apply Finset.sum_nonneg; intro k _; rw [← sq]; positivity))
  exact {h with uniform:=⟨hm _ h.uniform.1,hm _ h.uniform.2⟩}

lemma cover_revise {M : Bed} {v w V W : ℝ} (h : M.covered v w) (ht : V≤v) (hu : w≤W) : M.covered V W := by obtain ⟨a,b,c,d,e⟩ := h; exact ⟨strip_mono a ht hu,strip_mono b ht hu,strip_mono c ht hu, strip_mono d ht hu,strip_mono e ht hu⟩

lemma bid_bed (k l : ℝ) (hk : 0<k) (hl : 0≤l) (hj : 4≤j) :
    ∃ γ σ v C : ℝ, 0<γ ∧ 0<σ ∧ 0<v ∧ 0<C ∧
      ∀ (A : RG.Clip), A.direct ≤ γ → ∀ R : Train j, ∃ M : Bed, Defined k l R M ∧
        M.covered σ C ∧ (∀ n, Floor M A n v C) ∧ (∀ n G, Bid.Sworn M n G) ∧
        (R=Train.top j → ∀ n,M.diagonal.acts n=1) := by
  let w (i : Train j) := i
  obtain ⟨η,G,hη,hG,h⟩ := heart_banked k hk hj w
  have hh := (heart_heats k hk hj w).1
  have hg := (insurance k l hk hl hj w).1
  obtain ⟨a,X,ha,hX,hf⟩ := hh.funds
  obtain ⟨b,Y,hb,hY,hJ⟩ := hg.funds
  obtain ⟨ρ,U,hρ,hU,hb'⟩ := hg.stock.uniform
  have hR := pledge_warm k l hk hl hj w
  obtain ⟨μ,V,hμ,hV,hV'⟩ := hR.stock.uniform
  let γ := b/2; have hγ : 0<γ := by unfold γ; linarith
  let C := U+γ+Y
  let paid (c : Clip) (R : Train j) := minusRows (amend k l R) (scaleRows c.direct (unitRow (TypeFace 2)))
  obtain ⟨s,Q,ν,hs,hν,h'⟩ := Work.F07.answer (TypeFace 2) C γ ρ hγ hρ
  have he : 0 ≤ max Q 0 := le_max_right ..
  let σ := min η (min ρ (min μ ν))
  let B := X+Y+V+U+G+max Q 0
  have hB : 0<B := by unfold B; linarith
  refine ⟨γ,σ,min a b,B,hγ,lt_min hη (lt_min hρ (lt_min hμ hν)),lt_min ha hb,hB,fun p hp R => ?_⟩
  have hr : (amend k l R).strip ρ U := by simpa only [w,mul_one] using hb' R
  have ht : (paid p R).strip ρ C := by
    unfold paid
    apply strip_mono (strip_minus hr (strip_scale strip_unit _)) le_rfl
    rw [Real.norm_eq_abs,abs_of_pos p.quadratic_pos,mul_one]; unfold C; linarith
  obtain ⟨F,_,hF,hA⟩ := h' (paid p R) ht
    (low_ceiling (hJ R) p hp _ (by unfold C; linarith) ⟨ρ,U,hρ,hr⟩)
  let M : Bed := ⟨pink k R,blue k R,amend k l R,pledge k l R,F⟩
  refine ⟨M,⟨rfl,rfl,rfl,rfl⟩,?_,?_,?_,?_⟩
  · have hQ : Q≤max Q 0 := le_max_left ..
    refine ⟨strip_mono (h R).1 (min_le_left ..) ?_, strip_mono hr ((min_le_right ..).trans (min_le_left ..)) ?_, strip_mono (hV' R) ((min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..))) ?_, strip_mono hF ((min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..))) ?_,strip_mono (h R).2 (min_le_left ..) ?_⟩ <;> unfold B <;> linarith
  · intro n
    obtain ⟨_,h₁,h₂,h₃,h₄,h₅⟩ := obligations k l hk hl hj R n
    obtain ⟨he,hq⟩ := heart_inverse k hk hj R n
    obtain ⟨hs,hm⟩ := obey_band _ (hg.stock.whole R) (hJ R) n
    obtain ⟨hv,hy⟩ := obey_band _ (hh.stock.whole R) (hf R) n
    have hbZ (T : Row (TypeFace 2) (TypeFace 2)) (K V) (hN : Numeric (T.acts n) K V) (hA : min a b≤K) (hB : V≤B) : Numeric (T.acts n) (min a b) B := by
      intro v
      have hv : 0≤ dotProduct v v := by unfold dotProduct; apply Finset.sum_nonneg; intro k _; rw [← sq]; positivity
      exact ⟨(mul_le_mul_of_nonneg_right hA hv).trans (hN v).1,(hN v).2.trans (mul_le_mul_of_nonneg_right hB hv)⟩
    refine ⟨he,h₁.1,?_,forced_amend k l hk hl hj R,h₂,⟨h₄,hq.1⟩,hbZ _ b Y hm (min_le_right ..) (by unfold B; linarith), hbZ _ a X hy (min_le_left ..) (by unfold B; linarith)⟩
    rw [full_cover,show M.roots=F from rfl,← (hA n).1];
    unfold paid; rw [Whole.less (hg.stock.whole R) ((Whole.coin _).weight _) _,acts_scale,acts_unit]; simp; rfl
  · intro n G; exact sworn_metric k l hk hl hj R n M rfl G
  intro hT n
  change (record (pulse k R)).acts n=1
  subst R
  have he := Whole.eq_on (hh.stock.whole (Train.top j)) (Whole.coin (TypeFace 2)) (fun p hp => Eq.trans ((heart_true k hk hj (Train.top j)).1.echo _ hp) ((top_metric k hk j (base_subset_realCube zone_pos hp)).2.trans (read_unit _ p).symm)) n
  exact he.trans (acts_unit n)
end YM.Next.Free
