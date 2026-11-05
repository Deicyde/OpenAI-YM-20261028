import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Clover
import YM.Next.SCHEDULE.Circuit
import YM.Next.WARD_BIN.Wheels
import YM.Push.PRICE_COMPILER.Post
import YM.UVNext.PRICED_KERNELS.Echo




/-!
# Per-path pair prescriptions for the shape estimate

Use `Around` also for higher atoms. Index by final anchor, so `pull`
includes the value of o (actual source of the action is 0). All slots
with full paths and both end orientations. Row answers go on a Y
chosen here, including **all** sites queried to compute the kept test for this contribution to the clipping discrepancy. The extra window gate is essential;
for `Selector` this follows from a sufficiently long actual delay, not
taken automatically in a bare Template. Producer of the previous ledger
must really buy paths on these supports.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice RG Wilson Precision Push Next.Scheduling.Wages Work
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace Classical

variable {G : Gauge} {n : Side} (P : PathData G) (c : Clip) (b : BudgetPoint)

/-- Around chooses site and the channel. Last sort arbitrary payload. -/
abbrev Around (n : Side) (ι : Type) := Site n × Signed × ι
namespace Around
variable {ι : Type} (w : Around n ι)
abbrev atPin := w.1
abbrev turns := w.2.1
abbrev token := w.2.2

def region (X : Support n) := X.image (affine w.turns w.atPin)
def read {Z : Type*} (f : Config G n→Z) (U : Config G n) := f (pull w.turns w.atPin U)
def move (ι : Type) (s : Signed) (x : Site n) : Equiv.Perm (Around n ι) :=
  (WardBin.Wheels.aerial s x).prodCongr ((Equiv.mulLeft s).prodCongr (Equiv.refl _))



lemma carries (s : Signed) (x : Site n) (X : Support n) :
    (move ι s x w).region X = (w.region X).image (affine s x) := by
  rw [region,region,Finset.image_image]; change Finset.image (affine (s*w.turns) (affine s x w.atPin)) _=_; congr 1
  ext1; simp [affine,Function.comp_apply,Signed.act_mul,Signed.act_add,add_assoc]
lemma read_move {Z : Type*} (s : Signed) (x : Site n) (f : Config G n→Z) (U : Config G n) :
    (move ι s x w).read f U=w.read f (pull s x U) := by rw [read,read,pull_pull]; rfl
lemma pull_home : affine w.turns w.atPin 0=w.atPin := by simp [affine]
end Around

lemma mask_cov {X : Support n} {f g : Config G n → ℝ} (t : ℝ)
    (s : Signed) (o : Site n) (U : Config G n) (h : f (pull s o U)=g U) :
    masked t (Finset.image (affine s o) X) g U=masked t X f (pull s o U) := by
  have he := WardBin.Wheels.safe s o U (t:=t) (S:=X)
  by_cases hy : Healthy t (Finset.image (affine s o) X) U
  · rw [masked_eq _ _ _ _ hy,masked_eq _ _ _ _ (he.mp hy),h]
  rw [masked_ne _ _ _ _ hy, masked_ne _ _ _ _ (mt he.mpr hy)]

/-- Each path pair counts even if has common data or zero coefficient. -/
abbrev Sequence := PlaqAxes × (Unit ⊕ (ℕ × ℕ))

abbrev Card (n : Side) := Around n Sequence

def weight : ℝ := (Fintype.card Signed : ℝ)⁻¹
lemma weight_pos : 0 < weight := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
lemma weight_count : (Fintype.card Signed : ℝ)*weight=1 := mul_inv_cancel₀ (Nat.cast_pos.mpr Fintype.card_pos).ne'


abbrev first (x : PlaqAxes) (i : ℕ) := (P.row x i).2
abbrev earnCoeff (x : PlaqAxes) (i : ℕ) := (P.row x i).1

def copper (x : PlaqAxes) (d : ℕ × ℕ) : ℝ := weight/2*earnCoeff P x d.1*earnCoeff P x d.2

/-- Y in the orientation where its actual kept-row selector is used. -/
def imageOf (j : Sequence) : Support n := match j.2 with
  | .inl _ => ringlet 0
  | .inr (i,k) => halo b.B {0} ∪ walkCuts (first P j.1 i) 0 ∪ walkCuts (first P j.1 k) 0

lemma ringlet_sub (j : Sequence) : ringlet 0 ⊆ imageOf (n:=n) P b j := by
  unfold imageOf; split
  · exact Finset.Subset.refl _
  apply (Corona.halo_mono b.B_pos (Finset.Subset.refl _)).trans
  apply Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left

def cardSite (i : Card n) : RegularAddress n :=
  { site := i.1
    support := i.region (imageOf P b i.token)
    anchor := Finset.mem_image.mpr ⟨0,ringlet_sub P b _ (central _),i.pull_home⟩ }

lemma petal (i : Card n) : ringlet i.1 ⊆ (cardSite P b i).support := by
  change ringlet i.atPin ⊆ _
  rw [← i.pull_home,ringlet_turn]; exact Finset.image_subset_image (ringlet_sub ..)

def directWord (i : PlaqAxes) : Face (Per n) := (0,i)

def raw (j : Sequence) (U : Config G n) : ℝ := j.2.elim
  (fun _ => weight * c.direct * G.price (faceValue U (directWord j.1)))
  (fun d => copper P j.1 d * ⟪(first P j.1 d.1).atSite U 0,(first P j.1 d.2).atSite U 0⟫_ℝ)

def response (j : Sequence) (U : Config G n) : ℝ := j.2.elim
  (fun _ => weight*c.direct/2*⟪needles 0 U j.1,needles 0 U j.1⟫_ℝ)
  (fun d => copper P j.1 d * ⟪needles 0 U (first P j.1 d.1).plaq,needles 0 U (first P j.1 d.2).plaq⟫_ℝ)

/-- Partner for mask/path move in the exponent; keep clipping. -/
def literal (j : Sequence) (U : Config G n) : ℝ := j.2.elim
  (fun _ => weight * PathData.clipped c b.threshold (G.chord (faceValue U (directWord j.1))))
  (fun _ => if PathData.kept c b.threshold 0 U then raw P c j U else 0)

/-- Extra after threshold paid. Uses output stage radius. -/
def Selector := 2 ≤ b.threshold * Real.exp (b.B / c.relaxation)
lemma outside_kept (h : Selector c b) (F : Face (Per n)) (U : Config G n) (hh : b.B ≤ separation 0 F.1) :
    G.chord (faceValue U F) ≤ b.threshold*Real.exp (separation 0 F.1 / c.relaxation) := by
  apply (G.chord_le_two _).trans (h.trans _); refine mul_le_mul_of_nonneg_left ?_ b.threshold_pos.le
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by exact_mod_cast hh) c.radius_pos.le)
private lemma row_healthy (h : Selector c b) (U : Config G n) (ht : Healthy b.threshold (halo b.B {0}) U) : PathData.kept c b.threshold 0 U := by
  intro F
  by_cases hx : b.B ≤ separation 0 F.1
  · exact outside_kept _ _ h F U hx
  apply (local_chord ht F (by simp only [halo_spec,Finset.mem_singleton,exists_eq_left]
                              exact le_of_lt (lt_of_not_ge hx))).trans
  apply le_mul_of_one_le_right b.threshold_pos.le
  exact Real.one_le_exp (div_nonneg (by positivity) c.radius_pos.le)

lemma literal_here (h : Selector c b) (U : Config G n) (j : Sequence) (ht : Healthy b.threshold (imageOf P b j) U) :
    literal P c b j U=raw P c j U := by
  rcases j with ⟨x,(_|⟨i,k⟩)⟩
  · have he := local_chord ht (directWord x) (central (0:Site n))
    simp only [literal,raw,Sum.elim_inl,PathData.clipped,if_pos he,G.chord_price]; ring
  have hz := row_healthy c b h U (Disjoint.mono_left (by
    change halo _ _ ⊆ _ ∪ _ ∪ _; apply Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left) ht)
  exact if_pos hz


end YM.AnalyticBridge.CouplingShape
