import YM.Further.CURVED_GAUSSIAN_JETS.Algebra
import YM.SectorNext.VACUUM_NORMALIZATION.Factors

/-!
# Regular/frozen coordinates on the actual Tree.Forest

Complete on frozen **non-tree** links by identity, not by a zero row
and not by attaching regular-coordinate costs to them. Tree edges weren't
integrated in additive coordinates in the first place.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets
open MeasureTheory Filter Matrix Function Lattice Tree RG Precision SectorNext.Vacuum
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

set_option linter.unusedSectionVars false
namespace Joint
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K]

def join (A : Table I) (B : Table J) : Table (I⊕J) := fromBlocks A 0 0 B

def place (e : I ≃ K) (A : Table I) := A.submatrix e.symm e.symm
lemma join_form (A : Table I) (B : Table J) (x : Vec (I⊕J)) :
    quad (join A B) x = quad A (x ∘ Sum.inl) + quad B (x ∘ Sum.inr) := by
  rw [quad, join, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]; simp [quad,dotProduct,comp_def]
lemma dot_nonneg (x : Vec I) : 0 ≤ dotProduct x x := Finset.sum_nonneg fun _ _=>mul_self_nonneg _
lemma dot_pos {x : Vec I} (h : x ≠ 0) : 0 < dotProduct x x := by
  obtain ⟨i,hi⟩ := (Function.ne_iff.mp h)
  exact (mul_self_pos.mpr hi).trans_le (Finset.single_le_sum (f:=fun i => x i*x i) (fun i _ => mul_self_nonneg _) (Finset.mem_univ i))
lemma place_form (e : I ≃ K) (A : Table I) (x : Vec K) :
    quad (place e A) x = quad A (x ∘ e) := by
  unfold quad dotProduct mulVec; rw [← e.sum_comp]; unfold place dotProduct
  simp [←e.sum_comp]

lemma join_herm {A : Table I} {B : Table J} (ha : A.IsHermitian) (hb : B.IsHermitian) :
    (join A B).IsHermitian := ha.fromBlocks (by simp) hb
lemma join_pos {A : Table I} {B : Table J} (ha : A.PosDef) (hb : B.PosDef) :
    (join A B).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (join_herm ha.1 hb.1) fun x hx => ?_
  rw [star_trivial]; change 0<quad (join A B) x; rw [join_form]
  have hh : ∀ y, 0 ≤ quad A y := fun y => by simpa only [star_trivial] using ha.posSemidef.dotProduct_mulVec_nonneg y
  have ht : ∀ y, 0 ≤ quad B y := fun y => by simpa only [star_trivial] using hb.posSemidef.dotProduct_mulVec_nonneg y
  by_cases h : x ∘ Sum.inl=0
  · have h' : x ∘ Sum.inr ≠ 0 := fun he => hx (funext fun i => by cases i with
          | inl i => exact congr_fun h i
          | inr j => exact congr_fun he j)
    exact add_pos_of_nonneg_of_pos (hh _) (by simpa only [star_trivial] using hb.dotProduct_mulVec_pos h')
  exact add_pos_of_pos_of_nonneg (by simpa only [star_trivial] using ha.dotProduct_mulVec_pos h) (ht _)
lemma join_one : join (1:Table I) (1:Table J)=1 := Matrix.fromBlocks_one
lemma place_one (e : I ≃ K) : place e (1:Table I)=1 := Matrix.submatrix_one_equiv e.symm
lemma join_numeric {A : Table I} {B : Table J} {η L : ℝ} (ha : Numeric A η L) (hb : Numeric B η L) :
    Numeric (join A B) η L := by
  intro v; change _ ≤ quad (join A B) _ ∧ _ ; rw [show dotProduct v v = quad (join 1 1) v by rw [quad,join_one, Matrix.one_mulVec]]
  change _ ≤ quad (join A B) _ ∧ quad (join A B) _ ≤ _
  simp only [join_form,quad, Matrix.one_mulVec,mul_add]
  exact ⟨add_le_add (ha _).1 (hb _).1,add_le_add (ha _).2 (hb _).2⟩
lemma place_numeric {A : Table I} {η L : ℝ} (e : I ≃ K) (ha : Numeric A η L) : Numeric (place e A) η L := by
  intro v; change _ ≤ quad (place e A) v ∧ quad (place e A) v ≤ _
  rw [show dotProduct v v=quad (place e 1) v by rw [quad, place_one, Matrix.one_mulVec], place_form,place_form]
  unfold quad; rw [one_mulVec]; exact ha _
lemma one_numeric {η L : ℝ} (h : η≤1) (hl : 1≤L) : Numeric (1 : Table I) η L := fun v=> by
  rw [one_mulVec]; exact ⟨mul_le_of_le_one_left (dot_nonneg _) h, le_mul_of_one_le_left (dot_nonneg _) hl⟩
lemma place_mul (e : I ≃ K) (A B : Table I) : place e (A*B) = place e A * place e B := by unfold place; rw [submatrix_mul_equiv _ _ _ e.symm]
lemma join_mul (A B : Table I) (C D : Table J) : join (A*B) (C*D)=join A C * join B D := by simp [join,fromBlocks_multiply]
lemma place_sub (e : I ≃ K) (A B : Table I) : place e (A-B)=place e A-place e B := rfl
lemma join_sub (A B : Table I) (C D : Table J) : join (A-B) (C-D)=join A C-join B D := by ext (i|j) (k|l) <;> simp [join]
lemma extend_correct (e : I⊕J ≃ K) (A B : Table I) : place e (join A 1)*place e (join B 1)-1 = place e (join (A*B-1) 0) := by
  rw [← place_mul, ← join_mul, mul_one,← place_one e,← join_one, ← place_sub, ← join_sub, sub_self]
lemma join_rate {q : ℝ} {A : Table I} (h : Round.rowRate q A) {B : Table J} (hb : Round.rowRate q B) : Round.rowRate q (join A B) := by
  rintro (i|j) <;> rw [Fintype.sum_sum_type] <;> simp [join,h _, hb _]
lemma place_rate {q : ℝ} {A : Table I} (e : I ≃ K) (h : Round.rowRate q A) : Round.rowRate q (place e A) := by
  intro i; rw [← e.sum_comp]; simpa [place] using h (e.symm i)
lemma place_det (e : I⊕J ≃ K) (A : Table I) (B : Table J) : (place e (join A B)).det=A.det*B.det := by
  rw [place,det_submatrix_equiv_self, join,det_fromBlocks_zero₂₁]
end Joint
variable {G : Gauge} {c f : Side} {r : Ratio c f} {F : Forest r}
  (H : Finset F.Free)
abbrev Soft := {i // i∉H}
abbrev Bits (G : Gauge) := Soft H × G.ColorIndex

def tape (G : Gauge) : Bits H G ⊕ (H × G.ColorIndex) ≃ Key F G :=
  ((Equiv.sumProdDistrib _ _ _).symm.trans ((Equiv.sumComm _ _).prodCongr (Equiv.refl _))).trans
    ((Equiv.sumCompl (· ∈ H)).prodCongr (Equiv.refl _))
open Joint

def mount (A : Table (Bits H G)) : Table (Key F G) := place (tape H G) (join A 1)
lemma mount_pos {A : Table (Bits H G)} (ha : A.PosDef) : (mount H A).PosDef :=
    (join_pos ha Matrix.PosDef.one).submatrix (tape H G).symm.injective

lemma mount_rate {A C : Table (Bits H G)} {q : ℝ} (h : Round.rowRate q (A*C-1)) (hq : 0≤q) : Round.rowRate q (mount H A*mount H C-1) := by
  unfold mount; rw [extend_correct]; exact place_rate _ (join_rate h (fun j => by simpa using hq))
lemma mount_det (A : Table (Bits H G)) : (mount H A).det=A.det := by
  rw [mount, Joint.place_det, Matrix.det_one, mul_one]

lemma soft_card : Fintype.card (Soft H)=nt F-H.card := by convert Fintype.card_subtype_compl (·∈H) using 1; simp [nt]
lemma bits_card : Fintype.card (Bits H G)=(nt F-H.card)*Module.finrank ℝ G.Color := by rw [Fintype.card_prod,soft_card]; simp [Gauge.Color]
lemma regular_surface (A : ChartRatio G) {g β : ℝ} (_hg : 0<g) (hh : β*g^2=1) (C : Table (Bits H G)) :
    ((2*Real.pi*g^2)^((Fintype.card (Bits H G):ℝ)/2)) * A.scale^Fintype.card (Soft H) * Real.sqrt C.det =
      surface F A β H (mount H C) := by
  have he : β≠0 := by intro h; rw [h,zero_mul] at hh; exact zero_ne_one hh
  rw [surface, mount_det, soft_card,bits_card,show 2*Real.pi*g^2=2*Real.pi/β by field_simp; linarith only [hh]]

/-- Forms to callers with both the actual chart/measure factors and the
external full-key Factors conventions. -/
theorem regular_pays (A : ChartRatio G) (hA : LocalRatio A) {g β : ℝ} (he : 0<β) (hg : 0<g) (hh : β*g^2=1)
    (B : Table (Key F G)) (hb : 0<B.det) {K C : Table (Bits H G)} (hk : K.PosDef) (hs : C.IsHermitian)
    {q : ℝ} (h : Round.rowRate q (K*C-1)) (hz : 0≤q) (hq : q<1) :
    flatLine F A β B * Real.exp (residualLog F A β H B (mount H K) (mount H C)) =
      ((2*Real.pi*g^2)^((Fintype.card (Bits H G):ℝ)/2))*A.scale^Fintype.card (Soft H)*Real.sqrt C.det ∧ C.PosDef := by
  rw [regular_surface H A hg hh]
  have hC := corrected_pos hk hs h hq
  exact ⟨(unloads F A hA β he H B _ _ hb (mount_pos H hk) (mount_pos H hC).1 hz hq (mount_rate H h hz)).2,hC⟩

end YM.Further.CurvedGaussianJets
