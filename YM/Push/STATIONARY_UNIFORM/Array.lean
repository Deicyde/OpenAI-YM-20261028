import YM.Push.STATIONARY_UNIFORM.Beacons
import YM.Push.STATIONARY_UNIFORM.Count
import YM.Push.STATIONARY_UNIFORM.FrameBall


/-!
# Physical coordinates of the real tree score

A literal copy of the normalized spaces using **individual real orthonormal color
indices** and positioned at *fine sites*. In particular the sum of squares on
vertical inputs gives exactly the norm in PriceGap; for implicit estimates in
volume-independent sup balls also expose both directions' sup comparisons,
with gauge costs only. All orientations ultimately read these very same stored
variables. No independence required.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior
open Next.Fluctuations Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {p : Ratio c f} (B : Forest p)

abbrev Primary (c : Side) (G : Gauge) := Body 1 c × G.ColorIndex
abbrev Joint (G : Gauge) := Primary c G ⊕ Key B G

def partSpace (ι κ : Type) [Fintype ι] [Fintype κ] :
    Positions (ι ⊕ κ) ≃L[ℝ] Positions ι × Positions κ := by
  let L : Positions (ι ⊕ κ) ≃ₗ[ℝ] Positions ι × Positions κ :=
    { Equiv.sumArrowEquivProdArrow ι κ ℝ with
      map_add' := fun v w => rfl
      map_smul' := fun s v => rfl }
  exact L.toContinuousLinearEquiv

lemma part_norm {ι κ : Type} [Fintype ι] [Fintype κ] (v : Positions (ι ⊕ κ)) (y : ℝ) :
    ‖partSpace ι κ v‖ ≤ y ↔ ‖v‖ ≤ y := by
  rcases lt_or_ge y 0 with hy|hy
  · simp only [not_le.mpr (hy.trans_le (norm_nonneg _))]
  rw [Prod.norm_def,max_le_iff]
  simp_rw [pi_norm_le_iff_of_nonneg hy]
  refine ⟨fun h i => ?_, fun h => ⟨fun i => h (Sum.inl i),fun i => h (Sum.inr i)⟩⟩
  cases i with
  | inl i => exact h.1 i
  | inr i => exact h.2 i

lemma parts_isometry {ι κ : Type} [Fintype ι] [Fintype κ] (v : Positions (ι ⊕ κ)) : ‖partSpace ι κ v‖=‖v‖ :=
  le_antisymm ((part_norm v _).mpr le_rfl) ((part_norm v _).mp le_rfl)

def tint (G : Gauge) (ι : Type) [Fintype ι] : Positions (ι × G.ColorIndex) ≃L[ℝ] (ι → G.Color) := by
  let L : Positions (ι × G.ColorIndex) ≃ₗ[ℝ] (ι → G.Color) := {
    toFun v i := WithLp.toLp 2 (fun j => v (i,j))
    invFun v i := v i.1 i.2
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' := fun v w => rfl
    map_smul' := fun s v => rfl }
  exact L.toContinuousLinearEquiv

def paint (G : Gauge) : Positions (Joint B G) ≃L[ℝ] In G c × AxisChart G B :=
  (partSpace _ _).trans ((tint G _).prodCongr (tint G _))

lemma vertical_count (v : Positions (Key B G)) :
    (∑ i, ‖(tint G _ v) i‖^2) = ∑ i, (v i)^2 := by
  rw [Fintype.sum_prod_type]; simp_rw [EuclideanSpace.real_norm_sq_eq]; rfl

-- a sup norm on color reals not confused with Mahler or lattice norms

def shade (G : Gauge) : ℝ := 1+G.lieDim
lemma shade_one (G : Gauge) : 1 ≤ shade G := by unfold shade; simp
lemma shade_pos (G : Gauge) : 0 < shade G := lt_of_lt_of_le zero_lt_one (shade_one G)

lemma tint_le {ι : Type} [Fintype ι] (x : Positions (ι×G.ColorIndex)) : ‖tint G ι x‖ ≤ shade G*‖x‖ := by
  have h := shade_pos G
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg h.le (norm_nonneg _))).mpr; intro i
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg h.le (norm_nonneg _))).mp
  have he (j) : ((tint G ι x) i j)^2 ≤ ‖x‖^2 := by
    change (x (i,j))^2 ≤ _
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm x _) _
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow]
  refine (Finset.sum_le_sum (fun j _ => he j)).trans ?_
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fin]
  refine mul_le_mul_of_nonneg_right (le_trans (by unfold shade; linarith) (le_self_pow₀ (shade_one G) (by decide))) (sq_nonneg _)

lemma tint_inv_le {ι : Type} [Fintype ι] (x : ι → G.Color) : ‖(tint G ι).symm x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i
  change ‖x i.1 i.2‖ ≤ _
  apply le_trans _ (norm_le_pi_norm x i.1)
  simp only [Real.norm_eq_abs]
  have h := abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i.2) (x i.1)
  simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_mul] using h

/-- Located at fine speed. -/
def address (G : Gauge) : Joint B G → Site f
  | Sum.inl i => p.embed i.1.1
  | Sum.inr i => i.1.val.1

def townCost (G : Gauge) := Fintype.card (TypeFace 1 × G.ColorIndex) + Fintype.card (Axis × G.ColorIndex)

lemma town : Multiplicity (address (G:=G) B) (townCost G) := by
  let F := TypeFace 1 × G.ColorIndex
  let T := Axis × G.ColorIndex
  let t : Joint B G → F ⊕ T := Sum.elim (fun i => Sum.inl (i.1.2,i.2)) (fun j => Sum.inr (j.1.val.2,j.2))
  intro x
  have ht : Set.InjOn t ↑(Finset.univ.filter (fun i => address B G i=x)) := by
    rintro (i|i) hi (j|j) hj H
    all_goals
      have he := (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
      simp only [t,Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,Sum.inr.injEq, Sum.inr_ne_inl,
        Sum.inl_ne_inr] at H
    · have h := Prod.mk.inj H
      exact congr_arg Sum.inl (Prod.ext (Prod.ext (p.embed_injective he) h.1) h.2)
    have h := Prod.mk.inj H
    exact congr_arg Sum.inr (Prod.ext (Subtype.ext (Prod.ext he h.1)) h.2)
  have h := Finset.card_le_card_of_injOn t (t:=Finset.univ) (fun i _ => Finset.mem_univ _) ht
  simpa only [townCost, F, T, Finset.card_univ,Fintype.card_sum] using h

variable (G)

def outer (v : Positions (Joint B G)) := represent (paint B G v).1

def fine (v : Positions (Joint B G)) := lifting B (outer G B v) (paint B G v).2

variable {G}

lemma pinA (x : Body 1 c) (p : Positions (Joint B G)) (j : G.ColorIndex) :
    (paint B G p).1 x j=p (Sum.inl (x,j)) := rfl
lemma pinB (x : B.Free) (p : Positions (Joint B G)) (j : G.ColorIndex) :
    (paint B G p).2 x j=p (Sum.inr (x,j)) := rfl

lemma paint_le (v : Positions (Joint B G)) : ‖paint B G v‖ ≤ shade G*‖v‖ := by
  rw [← parts_isometry v,Prod.norm_def (paint B G v),max_le_iff]
  let p := partSpace _ _ v
  constructor
  · change ‖tint _ _ p.1‖ ≤ _
    exact (tint_le _).trans (mul_le_mul_of_nonneg_left (norm_fst_le _) (shade_pos _).le)
  change ‖tint _ _ p.2‖ ≤ _
  exact (tint_le _).trans (mul_le_mul_of_nonneg_left (norm_snd_le _) (shade_pos _).le)

def PaintSupply (G : Gauge) (n : ℕ) (Z : ℝ) : Prop := 0 < Z ∧
  ∀ x : G.Color, ‖x‖ ≤ shade G → Allows n (fun z => G.mat (G.lieExp z)) x Z

lemma paint_supply (G : Gauge) (n : ℕ) : ∃ Z : ℝ, PaintSupply G n Z := by
  obtain ⟨K,hK,H⟩ := exists_allows (isCompact_closedBall 0 (shade G)) (fun x _ => G.exp_jet.contDiffAt (x:=x)) n
  refine ⟨1+K,by positivity,fun x hx => (H x (by simpa using hx)).mono (by linarith)⟩

def outerCost (G : Gauge) (n : ℕ) (Z : ℝ) := composeCost n Z (shade G)
lemma outer_pos (G : Gauge) (n : ℕ) {Z : ℝ} (hp : 0<Z) : 0 < outerCost G n Z := by unfold outerCost composeCost; have := shade_pos G; positivity
lemma outer_supply {n Z} (hp : PaintSupply G n Z) : Inputs (outer G B) n (outerCost G n Z) := by
  refine ⟨by simp [outer], (outer_pos G n hp.1).le, ?_⟩
  intro e v hv
  let L := ContinuousLinearMap.proj (φ:=fun _ : Body 1 c => G.Color) (R:=ℝ) (e.1,coord e.2) ∘L (ContinuousLinearMap.fst ℝ (In G c) (AxisChart G B) ∘L (paint B G).toContinuousLinearMap)
  have hh : ‖L‖ ≤ shade G := L.opNorm_le_bound (shade_pos G).le fun w =>
    le_trans (norm_le_pi_norm (paint B G w).1 (e.1,coord e.2)) ((norm_fst_le _).trans (paint_le B w))
  have h : ‖L v‖ ≤ shade G := (L.le_opNorm _).trans <| le_trans (mul_le_mul hh hv (norm_nonneg _) (shade_pos _).le) (by rw [mul_one])
  simp_rw [outer, Work.F03.represent_link]
  exact (hp.2 (L v) h).comp (f:=L) (allows_linear hh h)

def fineCost (G : Gauge) (n : ℕ) (Z : ℝ) :=
  let o := outerCost G n Z
  let H := o+‖(1:G.Mat)‖
  H+2^n*H*H

lemma fine_supply {n Z} (hp : PaintSupply G n Z) : Inputs (fine G B) n (fineCost G n Z) := by
  let o := outerCost G n Z; let H := o+‖(1:G.Mat)‖
  have ho : 0 ≤ o := (outer_pos G n hp.1).le
  have h1 : ‖(1:G.Mat)‖ ≤ H := le_add_of_nonneg_left ho
  have hh := (show 0 ≤ ‖(1:G.Mat)‖ from norm_nonneg _).trans h1
  have he : o ≤ H := le_add_of_nonneg_right (norm_nonneg _)
  refine ⟨by simp only [fine,outer,map_zero,Prod.fst_zero, Prod.snd_zero,link_one,lifted,replica_one], by change 0≤H+2^n*H*H; positivity,fun e v hv => ?_⟩
  have h (j : B.Free) : Allows n (fun z : Positions (Joint B G) => G.mat (G.lieExp ((paint B G z).2 j))) v o := by
    let L := ContinuousLinearMap.proj (φ:=fun _ : B.Free => G.Color) (R:=ℝ) j ∘L (ContinuousLinearMap.snd ℝ (In G c) (AxisChart G B) ∘L (paint B G).toContinuousLinearMap)
    have hh : ‖L‖ ≤ shade G := L.opNorm_le_bound (shade_pos G).le fun w =>
      le_trans (norm_le_pi_norm (paint B G w).2 j) ((norm_snd_le _).trans (paint_le B w))
    have h : ‖L v‖ ≤ shade G := (L.le_opNorm _).trans <| le_trans (mul_le_mul hh hv (norm_nonneg _) (shade_pos _).le) (by rw [mul_one])
    exact (hp.2 _ h).comp (f:=L) (allows_linear hh h)
  have ha : Allows n (fun z => G.mat (replica p (outer G B z) e)) v H := by
    unfold replica; split
    · rw [G.mat_one]; exact allows_const v h1
    exact ((outer_supply B hp).2.2 _ v hv).mono he
  by_cases hw : e∈B.trunks
  · have he (z : Positions (Joint B G)) : G.mat (fine G B z e)=1 := by rw [show fine G B z e=1 from B.on_tree _ ⟨e,hw⟩]; rfl
    simp_rw [he]; exact (allows_const (n:=n) v h1).mono (le_add_of_nonneg_right (by change 0 ≤ 2^n*H*H; positivity))
  have ht (z : Positions (Joint B G)) : fine G B z e = G.lieExp ((paint B G z).2 ⟨e,hw⟩) * replica p (outer G B z) e := B.off_tree _ ⟨e,hw⟩
  simp_rw [ht]; exact (((h ⟨e,hw⟩).mono he).times ha).mono (le_add_of_nonneg_left hh)
end YM.Push.Uniform
