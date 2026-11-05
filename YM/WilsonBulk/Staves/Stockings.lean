import YM.WilsonBulk.Staves.Loom

/-!
# One/two point color invariance and shape, exact on cover. Keep formal compatibility; Stacks
  uses nonabelian simple no forced color. For every part of the full action AFTER coupling read.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Lattice Laurent Function Filter Bloch Matrix LinearMap RG Precision Stationary Exterior Wilson Pert.Bulk Sheet Atelier Finset
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {α β : Type} {p q σ : ℝ} {c d : Side} {u r n e : ℕ} {I : Library G}

abbrev Mant (A : Type) := A × PotentialForm
def scans (x : Mant α) (U : Page (α × Cloth G) 1) (i : G.ColorIndex) : ℝ:= U (fun _=>selvedge x i)
def juror (U : Text (Cloth G) 1) (x : Mant Cover) : G.Color →ₗ[ℝ] ℝ := {
    toFun i:= ∑ j,scans x U j*i j
    map_add' i j:= by simp [mul_add,sum_add_distrib]
    map_smul' r i:= by unfold scans; simp [smul_eq_mul,mul_left_comm,mul_sum] }
def card (i : G.ColorIndex) : G.Color := WithLp.toLp 2 (spike i)
lemma juror_card (U : Text (Cloth G) 1) (x : Mant Cover) (i) : juror U x (card i)=scans x U i:= by simp [juror,card,mul_ite]
lemma jets (u : G.El) {b : G.Color} (i : G.ColorIndex) : G.adjoint u b i= ∑ j, glass u i j * b j := congr_fun (matrices_real u b) i
lemma scans_rotate (B : Mant Cover) (h : Whisper I) (u : G.El) (i : G.ColorIndex) : ∑ j, scans B (I e 1) j*glass u j i = scans B (I e 1) i := by
  let x := selvedge B i; have hh:= h.multirank u (fun _ : Fin 1=> x) e; simp only [ravel] at hh
  rw [typeset_fin_hitch] at hh; simp only [Fintype.sum_unique, Fintype.prod_unique] at hh
  refine Eq.trans (sum_congr rfl fun a _=>?_) hh; rw [mul_comm]; unfold x selvedge scans; congr! with k; fin_cases k; rfl
lemma color_null (h : Whisper I) (hs : G.Simple) (e : ℕ) : I e 1=0 := by
  ext1 v; let i := v 0; have he:= fun a y => scans_rotate (fret i) h a y (e:=e) -- syntax
  have hh (a : G.El) (y : G.Color) : juror (I e 1) (fret i) (G.adjoint a y) = juror (I e 1) (fret i) y := by
    simp only [juror,LinearMap.coe_mk,AddHom.coe_mk,jets,mul_sum,← mul_assoc]; rw [sum_comm]; simp_rw [← sum_mul,he a]
  rw [show v=(fun _:Fin 1=>selvedge (fret i) i.2.2) from funext fun j=> Fin.fin_one_eq_zero j ▸ rfl]; change scans _ _ _=_
  rw [← juror_card,Push.Loops.invariant_null hs _ hh]; simp
lemma low_null (n : Side) (h : Whisper I) (hs : G.Simple) (e : ℕ) : Sheet.issue n I e 1=0 := by rw [Sheet.issue,color_null h hs, coupon_zero]

-- strip link row colors
abbrev glimpseK (x y : Mant α) (F : Page (α × Cloth G) 2) := fun i j=> F (two (selvedge x i) (selvedge y j))
def notice (f : G.ColorIndex →ℝ) : G.Color →ₗ[ℝ] ℝ := {
  toFun x:=∑ i, x i*f i
  map_add' x y:= by simp [add_mul,sum_add_distrib]
  map_smul' r x:= by simp [mul_assoc,mul_sum] }
def pigmentary (x y : Mant α) (P : Page (α × Cloth G) 2) : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ := {
  toFun i:= ∑ k:G.ColorIndex, i k • notice (glimpseK x y P k)
  map_add' i j:= by simp [add_smul,sum_add_distrib]
  map_smul' r i:= by simp [mul_smul,smul_sum] }
lemma pigmentary_at (x y : Mant α) (P : Page (α × Cloth G) 2) (i j : G.Color) : pigmentary x y P i j =∑ k:G.ColorIndex, ∑ l:G.ColorIndex, i k * j l*glimpseK x y P k l := by simp [pigmentary, notice, LinearMap.sum_apply,mul_sum, mul_assoc]
lemma pigmentary_card (x y : Mant α) (P : Page (α × Cloth G) 2) (i j : G.ColorIndex) : pigmentary x y P (card i) (card j)= glimpseK x y P i j := by rw [pigmentary_at]; simp [card, ite_mul,mul_ite]
lemma cards (i j : G.ColorIndex) : inner ℝ (card i) (card j)= if i=j then 1 else 0:= by simp only [Work.F03.inner_color]; simp [card,eq_comm]
lemma spate (B C : Mant Cover) (h : Whisper I) (u : G.El) (i j : G.ColorIndex) : ∑ a,∑ b, glass u a i*glass u b j *glimpseK B C (I e 2) a b = glimpseK B C (I e 2) i j := by
  let T:= I e 2; let f (a b : G.ColorIndex):=two (selvedge B a) (selvedge C b)
  have hh:= h.multirank u (f i j) e; unfold ravel at hh; rw [typeset_fin_hitch] at hh; simp_rw [typeset_fin_hitch (f:=fun v:Legs G.ColorIndex 1=>_)] at hh -- likely
  simp only [Fintype.sum_unique, Fin.prod_univ_two] at hh
  refine Eq.trans (sum_congr rfl fun a _=> sum_congr rfl fun b _=> ?_) hh; change _ * T _= (glass u a i*glass u b j)* T _; congr 2; ext1 z; fin_cases z <;> rfl
lemma Whisper.pair_plate (h : Whisper I) (hs : G.Simple) (e : ℕ) (x y : Mant Cover) (i j k : G.ColorIndex) : glimpseK x y (I e 2) i j = if i=j then glimpseK x y (I e 2) k k else 0 := by
  let T := I e 2; let P:= pigmentary x y T; let w:= glimpseK x y T
  have hP (u : G.El) (a b : G.Color) : P (G.adjoint u a) (G.adjoint u b)= P a b := by
    unfold P; simp_rw [pigmentary_at, jets,sum_mul,mul_sum,sum_mul]; rw [around_rect]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_
    conv_rhs => rw [← spate x y h u i j]
    simp_rw [mul_sum]; refine sum_congr rfl fun k _=>sum_congr rfl fun l _=>?_; ring
  obtain ⟨c,hc⟩:= Push.Loops.scalar_form hs P hP; change w i j = if i=j then w k k else 0
  have hv (i j : G.ColorIndex) : w i j = c * inner ℝ (card i) (card j) := by unfold w; rw [← pigmentary_card]; exact hc _ _
  simp_rw [hv,cards]; simp [mul_ite]
end YM.WilsonBulk.Parapet
