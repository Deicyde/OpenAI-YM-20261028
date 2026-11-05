import YM.Next.RANK.Combing

/-! Pay from ALL tags before log. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Set MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {V Ω : Type*}
variable {C : Family G} {i k l j m p q d D a n N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points n} {hk : i<k} {h : middle C.path.levels b k ≤ i}
variable {c : Course C N p k} {τ ε : ℝ}
variable {U T} (E : StageX (d:=d) c R x b hk h q T τ U ε)

lemma extras [MeasurableSpace Ω] (g : Ω→ ℂ) (μ : Measure Ω) (q : Prop) : (∫ u,dot q (g u)∂μ)= dot q (∫ u,g u ∂μ):= by unfold dot; split; exact integral_conj; rfl
lemma extra_int [MeasurableSpace Ω] (g : Ω→ℂ) (μ : Measure Ω) (q : Prop) (h : Integrable g μ): Integrable (dot q ∘ g) μ:= by unfold dot; split; exact RCLike.conjCLE.toContinuousLinearMap.integrable_comp h; exact h
lemma circle_diff (X : Prop) (a b c d) : dot X (a+b-c*d)=dot X a+dot X b-dot X c*dot X d:= by unfold dot;split;simp; rfl
lemma dot_times (X : Prop) (u v : ℂ) : dot X u*dot X v=dot X (u*v):=by unfold dot;split; simp; rfl
lemma dot_equal (X : Prop) (p q : ℂ) : ‖dot X p-dot X q‖=‖p-q‖:= by unfold dot; split; rw [← star_sub,norm_star];rfl

lemma reparations (X : (j:Fin E.count) → (E.tag j).Θ → ℂ) (z : Prop) (a : ℂ) (p : ℝ)
    (h : ∀ j, letI:=(E.tag j).M; ‖(∫ u,X j u ∂(E.tag j).μ) - a‖ ≤ p) : ‖plaids E (fun j u=>dot z (X j u))-dot z a‖ ≤ p:= by
  let R (j:Fin E.count) :=
    letI := (E.tag j).M
    ∫ u,X j u ∂(E.tag j).μ
  have he : plaids E (fun j u=>dot z (X j u))-dot z a= ∑ j : Fin E.count,(E.weight j:ℂ)*(dot z (R j)-dot z a):= by
    unfold plaids mixedEval; simp only [mul_sub,Finset.sum_sub_distrib,extras]
    rw [← Finset.sum_mul,← Complex.ofReal_sum,E.total,Complex.ofReal_one,one_mul]
  rw [he]; apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ j : Fin E.count, E.weight j*p:= sum_le_sum fun j _=> by rw [norm_mul, dot_equal, Complex.norm_real,Real.norm_of_nonneg (E.pos j)]; exact mul_le_mul_of_nonneg_left (h j) (E.pos j)
    _ = _ := by rw [← sum_mul,E.total,one_mul]

section
variable (P : pennant n → poly (Chamber G C.S (i+1) p))

def invitation (T : Lane C k b p d x (show i≤k from hk.le)) (c : Course C N p k) (h : middle C.path.levels b k ≤ i) (j : Index x b C.path.levels p d (show i+1≤k from hk)) :=
    glory x b p c.allow hk (h.trans (Nat.le_succ _)) T.1 j.val (anneals C c (i+1)) (P j.val)




lemma engages i' (u : Index x b C.path.levels p d (show i+1≤k from hk)) (z) :
    planted E (invitation (hk:=hk) P T c h) i' u z= dot ((Ship.yard C b c.allow p).hand T.1) ((↑((E.tag i').Γ u z):ℂ)*traceU (E.tag i') u (P u.val) z):= by rw [dot_move]; rfl

variable {B Y L w θ} (X : roomTest C.path.levels b k p d q)
variable (H : Healthy θ (dolmens x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U)
variable (hr : Metal b c R hk ε τ θ B Y L) (Hε : 0 < ε) (he : ε ≤ 1)
variable (Vh : ∀ u, Poetic (P u)) (Vm : ∀ u, coin (P u) ≤ w) (VD : ∀ u,totalDegree (P u) ≤ D)
variable (Vs : ∀ u,∀ i'∈ (P u).vars, spotP b (i+1) d (show i+1≤k from hk) (C:=C) x u i')
include X H hr Hε he Vh Vm VD Vs
lemma dominant (u : Index x b C.path.levels p d (show i+1≤k from hk)) (hp : tests x b hk (C:=C) T.2.val u) :
    let v:= fun (j:Fin E.count) => planted E (invitation (hk:=hk) P T c h) j u
    (∀ j, letI:=(E.tag j).M; Integrable (v j) (E.tag j).μ) ∧
    ‖plaids E v-dot ((Ship.yard C b c.allow p).hand T.1) (elegance b c x hk h T U ((R i).read (P u.val)))‖ ≤ grant₁ B ε w D:= by
  intro v
  have ht j:= worn_single (E.tag j) u X hr H Hε he hp (VD _) (Vh _) (Vm _) (Vs _)
  rw [show v=(fun j z=> _) from funext fun j=> funext fun z=> engages E P j u z]
  refine ⟨fun j=>?_,reparations _ _ _ _ _ (fun i=> (ht i).2)⟩
  letI:=(E.tag j).M; exact extra_int _ _ _ (ht j|>.1)

lemma entangles (u v : Index x b C.path.levels p d (show i+1≤k from hk)) (hu : tests x b hk (C:=C) T.2.val u) (hv : tests x b hk (C:=C) T.2.val v) :
    let f:= fun (j:Fin E.count) z => planted E (invitation (hk:=hk) P T c h) j u z * planted E (invitation (hk:=hk) P T c h) j v z
    (∀ j,letI:=(E.tag j).M; Integrable (f j) (E.tag j).μ) ∧
    ‖plaids E f-dot ((Ship.yard C b c.allow p).hand T.1) (elegance b c x hk h T U ((R i).read ((P u.val)*(P v.val))))‖ ≤ grant₂ B ε w D:= by
  intro f
  have ht j:= worn_pair (E.tag j) u X hr H Hε he hu (VD _) (Vh _) (Vm _) (Vs _) v hv (P v.val) (VD _) (Vh _) (Vm _) (Vs _)
  simp_rw [f,engages,dot_times]
  refine ⟨fun j=>?_,reparations _ _ _ _ _ (fun i=> (ht i).2)⟩
  letI:=(E.tag j).M; exact extra_int _ _ _ (ht j|>.1)
end

lemma plaids_add (s t : (j:Fin E.count) → (E.tag j).Θ →ℂ) (h : ∀ j,letI:=(E.tag j).M; Integrable (s j) (E.tag j).μ) (H : ∀ j,letI:=(E.tag j).M; Integrable (t j) (E.tag j).μ) :
    plaids E (fun j z=> s j z+t j z)=plaids E s+plaids E t:= by
  unfold plaids mixedEval; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _=> ?_; letI:=(E.tag j).M; dsimp only; rw [integral_add (h j) (H j)]; exact mul_add ..
end YM.Next.Rank.Tapes
