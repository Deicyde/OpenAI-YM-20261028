import YM.Push.RELAY_DIFFERENCE.Finite

/-!
# The top price of the actual Wdff and visits 

Use only literals with the common terminal and threshold. This file estimates
the payload cost BEFORE absorbing masks. Both the group supremum and full
top budget-point's left derivatives under the indicators. The one-step
shift of the entire stencil matters; carry its translated support and its
cost of changing metric origin explicitly. Even with `a_N^-1` the price is
subpower (with a particular additional price floor `shiftCosts` needed
for the orders; not assumed automatically by Makes). This is a substantial
input to, but NOT by itself, preparing the representations Encoded or Joint.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Labels Lattice Cells Marker Overlay Stock Bid Source
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
open Next.Foundations
variable {G : Gauge} {C : Family G} {n : Side} {d e N p : ℕ} {F : Trial C} {f : Extraction.Order}

abbrev regional (X : Finset Cover) (o : Site n) := X.image fun x => wrap n x + o

def unpriced (C : Family G) (F : Trial C) (e N p : ℕ) (o : Site (C.side N p)) :=
    weight C e N • F N p o

def clothed (B : BudgetPoint) (X : Support n) (o : Site n) (u : Config G n → ℂ) (c b : ℝ) : Prop :=
    B.Regular X u ∧ B.supBounds o X u c ∧ 0 ≤ b ∧ ∀ U,‖u U‖ ≤ b

/-- Raw protection of origin and same literally translated entries on
ordered tails (`Stencilled.literal` etc separate). Deliver simultaneous
support and prices. Costs uniform in all sites and no calibration at them. -/
def RawProtected (C : Family G) (f : Extraction.Order) (F : Trial C) (e : ℕ) :=
    ∃ X : Finset Cover, 0∈X ∧ ∃ c b : Cutoffs → ℝ, Slow C f c ∧ Slow C f b ∧
    f.late fun N p => ∀ o, clothed (C.path.levels.budget N) (regional X o) o (unpriced C F e N p o) (c (N,p)) (b (N,p))

section Directions
/-- Scale all direction costs together. No derivative wasting at flags.
Works for the defined leftDerivs (in their order). -/
lemma left_dilate (u : Config G n → ℂ) (v : List (Directions G n)) (a : ℝ) (U : Config G n) :
    leftDerivs u (v.map fun A => a • A) U = a^v.length • leftDerivs u v U := by
  induction v generalizing U with
  | nil => simp [leftDerivs]
  | cons x v ih =>
    simp only [List.map_cons,leftDerivs,ih, deriv_fun_const_smul_field]
    have hi (t : ℝ) : t • a • x = (a*t) • x := by rw [smul_smul, mul_comm]
    simp_rw [hi]
    let G (t : ℝ) := leftDerivs u v (increment U (t • x))
    change a^v.length • deriv (fun t => G (a*t)) 0 = _
    rw [deriv_comp_mul_left, mul_zero, smul_smul,List.length_cons,pow_succ]

def jump (P : BudgetPoint) : ℝ := ((2:ℝ)^P.power)^P.order

lemma dir_shift (P : BudgetPoint) (X : Support n) (u : Config G n → ℂ) {c : ℝ}
    (o r : Site n) (he : separation r o ≤ 1) (h : P.supBounds r X u c) : P.supBounds o X u (jump P * c) := by
  let b := (2:ℝ)^P.power
  have hb : 1 ≤ b := one_le_pow₀ (by norm_num)
  have hp : 0 < b := zero_lt_one.trans_le hb
  have hh (A : Directions G n) (ht : P.dirBound o A) : P.dirBound r (b⁻¹ • A) := by
    intro i
    have he : 1+(separation i.1 o:ℝ) ≤ 2*(1+(separation i.1 r:ℝ)) := by
      have hu := (separation_triangle i.1 r o).trans (Nat.add_le_add_left he _)
      have hv : (separation i.1 o:ℝ) ≤ ↑(separation i.1 r) + (1:ℝ) := by exact_mod_cast hu
      linarith only [hv,Nat.cast_nonneg (α:=ℝ) (separation i.1 r)]
    change ‖b⁻¹ • A i‖ ≤ _
    rw [norm_smul_of_nonneg (inv_pos.mpr hp).le]
    calc
      _ ≤ b⁻¹*(P.threshold * (1+(separation i.1 o:ℝ))^P.power) :=
        mul_le_mul_of_nonneg_left (ht i) (inv_pos.mpr hp).le
      _ ≤ b⁻¹*(P.threshold * (2*(1+(separation i.1 r:ℝ)))^P.power) := by
        have hx := P.threshold_pos; gcongr
      _ = _ := by rw [mul_pow]; change b⁻¹*(P.threshold*(b*_))=_; field_simp
  refine ⟨mul_nonneg (show 0 ≤ b^P.order by positivity) h.1,fun U hu l hl hx => ?_⟩
  let q := l.map fun A => b⁻¹ • A
  have he : q.length=l.length := List.length_map ..
  have ht := left_dilate u q b U
  have hg : q.map (fun A => b • A) = l := by simp [q, Function.comp_def, hp.ne']
  rw [← hg, left_dilate,norm_smul_of_nonneg (pow_nonneg hp.le _)]
  exact mul_le_mul (pow_le_pow_right₀ hb (he.trans_le hl))
    (h.2 U hu q (he.trans_le hl) (fun i hi => by obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact hh _ (hx _ hj)))
    (norm_nonneg _) (pow_nonneg hp.le _)
end Directions

section Size
variable (C) (d N p)

/-- Form a proof for any combination at the price paid in C alone.
No need all-B credit. Supports at actual position. -/
lemma section_bounds (h : C.Makes) (he : C.ref d ≤ N) (o : Site (C.side N p)) (x : C.label d) :
    let B := C.path.levels.budget N
    let F := C.labels.level d
    let T := C.localSection d
    let f := T.places (F.scaled B.threshold⁻¹ x) o
    B.Regular (T.footprint o) f ∧ B.supBounds o (T.footprint o) f ((C.path.levels.params N).columns * F.coeffSize x) := by
  intro B F T f
  let L : C.label d →ₗ[ℂ] Config G (C.side N p) → ℂ := {
    toFun v := T.places v o
    map_add' a b := funext fun U => congr_fun (T.eval_linear.map_add a b) (expandAt o U)
    map_smul' a b := funext fun U => congr_fun (T.eval_linear.map_smul a b) (expandAt o U) }
  let v := F.scaled B.threshold⁻¹ x
  have hv : f = ∑ i : Fields C d, v i • L (needle C d i) := by
    simp_rw [←map_smul, ←map_sum, recompose]; rfl
  let a := (C.path.levels.params N).columns
  let s (i : Fields C d) : ℝ := a*B.threshold^(F.grades i).2
  have he i : B.Regular (T.footprint o) (L (needle C d i)) ∧ B.supBounds o (T.footprint o) (L (needle C d i)) (s i) := h.priced d N p he o i
  have hk i : ‖v i‖*s i = a*‖x i‖ := by
    unfold v
    have hh : F.scaled B.threshold (F.scaled B.threshold⁻¹ x) = x := F.scaled_inv B.threshold_pos.ne' x
    unfold s
    have hx := B.threshold_pos
    rw [F.scaled_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr hx).le _)]
    rw [inv_pow]
    field_simp
  obtain ⟨hg,hq⟩ := regular_bound_sum (Finset.univ (α:=Fields C d)) (fun i => v i • L (needle C d i))
    (fun i => ‖v i‖*s i) (fun i _ => ⟨regular_smul _ (he i).1,bound_smul _ (he i).2⟩)
  rw [hv]
  simp_rw [hk,←Finset.mul_sum] at hq; exact ⟨hg,hq⟩

/-- Normalize before any mask/projection. -/
lemma charged (x : C.label d) (o : Site (C.side N p)) :
    weight C d N • C.O N p x o = (C.localSection d).places ((C.labels.level d).scaled
      (C.path.levels.budget N).threshold⁻¹ ((C.factory d N p).terminal.symm x)) o := by
  have he : weight C d N ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.path.S.a_pos N).ne')
  change (weight C d N) • ((weight C d N)⁻¹ • _) = _
  rw [smul_smul, mul_inv_cancel₀ he, one_smul]; rfl

/-- Full group cost of the sections before any scaling, from the actual
cover cylinder, all placements. -/
def away_cost (C : Family G) (d : ℕ) := ∃ b : ℝ,1 ≤ b ∧
    ∀ (v : C.label d) (p : Side) (o : Site p) (U), ‖(C.localSection d).places v o U‖ ≤ b*(C.labels.level d).coeffSize v

theorem offmask : away_cost C d := by
  classical
  let T := C.localSection d
  have he (i : Fields C d) : ∃ b : ℝ, ∀ U, ‖T.evaluate (needle C d i) U‖ ≤ b :=
    (T.continuous_evaluate (needle C d i)).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  choose A hA using he
  obtain ⟨b,hb,ht⟩ := ((eventually_ge_atTop (1:ℝ)).and (eventually_all.mpr fun i : Fields C d => eventually_ge_atTop (A i))).exists
  refine ⟨b,hb,fun v p o U => ?_⟩
  let L : C.label d →ₗ[ℂ] _ := T.eval_linear.mk' _
  change ‖L v _‖ ≤ _
  let x := expandAt o U
  have hu : (∑ i : Fields C d, v i • (L (needle C d i) x)) = L v x := by
    conv_rhs => rw [← recompose v, map_sum]
    simp only [Finset.sum_apply,Pi.smul_apply,map_smul]
  rw [← hu]
  apply (norm_sum_le ..).trans
  unfold Frame.coeffSize; rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [norm_smul,mul_comm]; exact mul_le_mul_of_nonneg_right ((hA i x).trans (ht i)) (norm_nonneg _)
end Size

lemma coords_slow (v : Rowe C d) (h : Slow C f v) : Slow C f fun j => (C.labels.level d).coeffSize (v j) := by
  let K (i : Fields C d) (j) := v j i
  have he (i : Fields C d) : Slow C f (K i) := h.reduce (Eventually.of_forall fun j => norm_le_pi_norm (v j) i)
  exact Slow.sum _ _ fun i _ => (he i).norm
lemma scaled_slow (v : Rowe C d) (h : Slow C f v) (K : G.Simple) :
    Slow C f fun j => (C.labels.level d).coeffSize
      ((C.labels.level d).scaled (C.path.levels.budget j.1).threshold⁻¹ (v j)) := by
  let B (i : Fields C d) (j) := v j i
  have he (i : Fields C d) : Slow C f (B i) := h.reduce (Eventually.of_forall fun j => norm_le_pi_norm (v j) i)
  let t (j : Cutoffs) := (C.path.levels.budget j.1).threshold⁻¹
  let F := C.labels.level d
  have hf (i : Fields C d) : Slow C f (fun j => F.scaled (t j) (v j) i) := by
    have ht : Slow C f fun j => ((t j)^((F.grades i).2):ℝ) := (threshold_price K).pow _
    exact (ht.reduce (Eventually.of_forall fun j => (Complex.norm_real ((t j)^((F.grades i).2))).le)).mul (he i)
  exact Slow.sum _ _ fun i _ => (hf i).norm

theorem RawProtected.upper (h : C.Makes) (K : G.Simple) (v : Rowe C d) (hw : dollar C f v) :
    RawProtected C f (Bid.upper C v) d := by
  let T := C.localSection d
  let F := C.labels.level d
  let B (i : Cutoffs) := C.path.levels.budget i.1
  let x (i : Cutoffs) : C.label d := (C.factory d i.1 i.2).terminal.symm (v i)
  obtain ⟨b,hb,hB⟩ := offmask C d
  have hv : Slow C f x := (dollar_slow v).1 hw
  let c i := (C.path.levels.params (Prod.fst i)).columns * F.coeffSize (x i)
  let u i := b * F.coeffSize (F.scaled ((B i).threshold⁻¹) (x i))
  refine ⟨T.stencil,(h.sections d).anchored,c,u,
    (columns_slow (C:=C)).mul (coords_slow x hv), (Slow.const (C:=C) b).mul (scaled_slow x hv K),?_⟩
  unfold Order.late
  refine Eventually.of_forall fun a => ?_
  filter_upwards [f.mesh.cofinal.eventually_ge_atTop (C.ref d)] with i hi o
  let j : Cutoffs := (f.mesh i,f.per a)
  change clothed _ _ _ (weight C d j.1 • C.O j.1 j.2 (v j) o) (c j) (u j)
  rw [charged]
  exact ⟨(section_bounds C _ _ _ h hi o (x j)).1,(section_bounds C _ _ _ h hi o (x j)).2,
    mul_nonneg (zero_le_one.trans hb) (coeff_pos ..), hB _ _ o⟩

/-- Visit at same/comparison height. No backward Wdff here. -/
theorem RawProtected.lift (h : RawProtected C f F d) (he : d ≤ e) : RawProtected C f F e := by
  obtain ⟨X,hX,c,b,hc,hb,H⟩ := h
  let w (j : Cutoffs) : ℂ := weight C (e-d) j.1
  have ht : Slow C f w := by
    have hj : ∀ j, ‖w j‖ ≤ 1 := fun j => by
      unfold w weight; rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (C.S.a_pos _).le]
      have ha := C.S.strictAnti.antitone (Nat.zero_le j.1)
      apply pow_le_one₀ (C.S.a_pos j.1).le (ha.trans_eq ?_)
      simp
    exact (Slow.const (C:=C) (1:ℝ)).reduce (Eventually.of_forall fun j => by simpa using hj j)
  refine ⟨X,hX,_,_,ht.norm.mul hc,ht.norm.mul hb,?_⟩
  exact H.mono fun u hh => hh.mono fun i hi o => by
    obtain ⟨ha,hA,hB,hb⟩ := hi o
    let N := f.mesh i
    let p := f.per u
    rw [show unpriced C F e N p o=w (N,p) • unpriced C F d N p o by
      unfold w unpriced weight; rw [smul_smul, ←pow_add,Nat.sub_add_cancel he]]
    exact ⟨regular_smul _ ha,bound_smul _ hA,mul_nonneg (norm_nonneg _) hB,
      fun U => (norm_smul_le (w (N,p)) _).trans (mul_le_mul_of_nonneg_left (hb U) (norm_nonneg _))⟩

theorem RawProtected.visits (h : C.Makes) (K : G.Simple) (y : C.label d) (hz : d ≤ e) :
    RawProtected C f (Bid.visits C d y) e :=
    (RawProtected.upper h K (fun _ => y) (Work.D01.answer C h d f _
      ⟨‖y‖,Eventually.of_forall fun _ => Eventually.of_forall fun _ => le_rfl⟩)).lift hz

/-- A pre/L-derived charge for moving the derivative stencil at the actual
purchased order + power. Needed here as a scheduling input; e.g. if capping
with an extra column reservation. No dependence on p. -/
def shiftCosts (C : Family G) (f : Extraction.Order) := Slow C f fun j => jump (C.path.levels.budget j.1)

theorem height_cancels (x : C.label d) (a : Axis) (o : Site (C.side N p)) :
    unpriced C (heighten C d x a) (d+1) N p o =
      unpriced C (Bid.visits C d x) d N p (o+step a)-unpriced C (Bid.visits C d x) d N p o := by
  dsimp only [unpriced,heighten,Bid.visits,Bid.upper,weight]
  have ht : (C.S.a N:ℂ) ≠ 0 := by exact_mod_cast (C.S.a_pos N).ne'
  rw [pow_succ,smul_smul, mul_assoc,mul_inv_cancel₀ ht,mul_one,smul_sub]

theorem RawProtected.heighten (h : C.Makes) (K : G.Simple) (x : C.label d) (hP : shiftCosts C f) (a : Axis) :
    RawProtected C f (heighten C d x a) (d+1) := by
  obtain ⟨X,hX,c,b,hc,hb,H⟩ := RawProtected.visits (f:=f) h K x le_rfl
  let D := X.image (fun x => x + step a) ∪ X
  let t (i : Cutoffs) := jump (C.path.levels.budget i.1)
  have ht : Slow C f t := hP
  refine ⟨D,Finset.mem_union_right _ hX,_,_,(ht.mul hc).add hc,hb.add hb,?_⟩
  exact H.mono fun j hh => hh.mono fun i hi o => by
    let N := f.mesh i; let p := f.per j
    obtain ⟨hx,hA,hB,hU⟩ := hi o
    obtain ⟨hy,hY,hQ,hv⟩ := hi (o+step a)
    have hD : regional X (o+step a) ⊆ regional D o := by
      rintro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨_,Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy), by rw [map_add,wrap_step]; abel⟩
    have hD' : regional X o ⊆ regional D o := Finset.image_subset_image Finset.subset_union_right
    have hm := regular_larger hy hD
    have hs := regular_larger hx hD'
    have ha : separation (o+step a) o ≤ 1 := by rw [separation, add_comm, add_sub_cancel_right]; exact pdist_step _
    rw [height_cancels]
    exact ⟨regular_sub hm hs, bound_sub hm hs (bound_larger (dir_shift _ _ _ _ _ ha hY) hD) (bound_larger hA hD'),
      add_nonneg hQ hB, fun U => (norm_sub_le ..).trans (add_le_add (hv U) (hU U))⟩
end YM.Push.RelayDifference
