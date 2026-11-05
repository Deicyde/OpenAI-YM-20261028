import YM.AnalyticNext.QUARTIC_MATCH.Cells.Boundary
import YM.AnalyticNext.QUARTIC_MATCH.Cells.Interval

/-!
# Cubical homotopy on an anchored axis

Carry all other arguments passively. Later iteration spends widths in native units.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Function Lattice Exterior Filter Topology
open scoped Topology BigOperators

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- `Sums` at one position; translations unchanged. -/
def sums (F : Cell ℤ → V) := ∀ S : Finset Axis, Summable fun i : Cover => F (i,S)

omit [NormedSpace ℝ V] [CompleteSpace V] in
lemma sums.add {F G : Cell ℤ → V} (h : sums F) (g : sums G) : sums (F+G) :=
    fun S => (h S).add (g S)
omit [NormedSpace ℝ V] [CompleteSpace V] in
lemma sums.sub {F G : Cell ℤ → V} (h : sums F) (g : sums G) : sums (F-G) :=
    fun S => (h S).sub (g S)

omit [CompleteSpace V] in
lemma sums.sects {F : Cell ℤ → V} (h : sums F) (i : Axis) : sums (sect i F) := by
  intro S; by_cases hi : i∈S
  · simp [sect_at,hi]
  have he := h (insert i S)
  simp_rw [sect_at, if_neg hi]; exact (((Equiv.subRight (step i : Cover)).summable_iff.mpr he).sub he).const_smul _
omit [CompleteSpace V] in
lemma sums.rims {F : Cell ℤ → V} (h : sums F) : sums (rim F) := by
  intro S; simp_rw [rim_at]; exact summable_sum (fun i _ => (h.sects i) S)
omit [CompleteSpace V] in
lemma totals {F : Cell ℤ → V} (h : sums F) : (∑' i : Cover, rim F (i,∅)) = 0 := by
  simp_rw [rim_at]
  rw [Summable.tsum_finsetSum]; swap
  · exact fun i _ => h.sects i _
  refine Finset.sum_eq_zero fun i _ => ?_
  simp_rw [sect_at, if_neg (Finset.notMem_empty _)]
  let S := insert i (∅ : Finset Axis)
  let v := fun i : Cover => F (i,S)
  let E := Equiv.subRight (step i : Cover)
  have he : Summable v := h _
  have hx : (∑' x,(v (E x)-v x))=0 := by rw [(show Summable (fun x => v (E x)) from E.summable_iff.mpr he).tsum_sub he, E.tsum_eq,sub_self]
  change (∑' x, sign ∅ i • (v (E x)-v x))=_
  rw [tsum_const_smul'', hx,smul_zero]

def along (i : Axis) (x : Cover) (S : Finset Axis) (F : Cell ℤ → V) (k : ℤ) :=
    F (update x i k,S)
omit [NormedSpace ℝ V] in
lemma sums.goes {F : Cell ℤ → V} (h : sums F) (S : Finset Axis) (x : Cover) (i : Axis) : Summable (along i x S F) :=
    (h S).comp_injective (i := fun k => update x i k) (fun b c g => by simpa using congr_fun g i)

def fillRay (b : Cover) (i : Axis) (f : Cell ℤ → V) (x : Cell ℤ) :=
    if i∈x.2 then sign x.2 i • Ray.solution (along i x.1 (x.2.erase i) f) (b i) (x.1 i) else 0

def squeezed (b : Cover) (i : Axis) (f : Cell ℤ → V) (x : Cell ℤ) :=
    if i∈x.2 then 0 else if x.1 i=b i then (∑' k, along i x.1 x.2 f k) else 0

omit [CompleteSpace V] in
lemma along_jump (i : Axis) (x : Cover) (S : Finset Axis) (F : Cell ℤ → V) :
    along i x S (sect i F) = if i∈S then 0 else sign S i • Ray.jumps (along i x (insert i S) F) := by
  split <;> rename_i hi
  · funext k; simp [along,sect_at,hi]
  funext k
  have he : update x i k - step i=update x i (k-1) := by
    funext j; by_cases h : i=j
    · subst i; simp
    simp [Ne.symm h]
  unfold along; rw [sect_at,if_neg hi,he]; rfl

omit [CompleteSpace V] [NormedSpace ℝ V] [NormedAddCommGroup V] in
lemma along_back (i : Axis) (x : Cover) (S : Finset Axis) (F : Cell ℤ → V) :
    along i (x-step i) S F=along i x S F := by
  funext k; simp only [along]; congr 2; funext j; by_cases h : i=j
  · subst i; simp
  simp [Ne.symm h]

/-- In dimension one of the cube. -/
theorem same_axis (b : Cover) (i : Axis) {F : Cell ℤ → V} (h : sums F) :
    sect i (fillRay b i F) + fillRay b i (sect i F) = F-squeezed b i F := by
  funext ⟨x,S⟩; by_cases hi : i∈S
  · have hh : ¬ i∈S.erase i := by simp
    simp only [Pi.add_apply,sect_at,hi,↓reduceIte,fillRay,along_jump,if_neg hh,sign_remove,
      Finset.insert_erase hi,squeezed,Pi.sub_apply,Ray.solution_scale,Ray.right (h.goes _ _ _),
      smul_smul,sign_sq,one_smul,sub_zero,zero_add]
    simp [along]
  have he := Ray.left (h.goes S x i) (x i) (b i)
  simp_rw [Pi.add_apply, Pi.sub_apply,sect_at,fillRay,squeezed]
  simp only [hi,↓reduceIte,Finset.mem_insert, true_or,add_zero,Finset.erase_insert hi,
    sign_insert _ _ hi,← smul_sub,smul_smul,sign_sq,one_smul, Pi.sub_apply,step_apply, ↓reduceIte,along_back]
  simpa [along] using he

lemma fillRay_add (b : Cover) (i : Axis) {F G : Cell ℤ → V} (h : sums F) (g : sums G) :
    fillRay b i (F+G)=fillRay b i F+fillRay b i G := by
  funext ⟨x,S⟩; by_cases hi : i∈S
  · simp only [fillRay,hi,↓reduceIte, Pi.add_apply]
    rw [show along i x (S.erase i) (F+G)=along i x (S.erase i) F + along i x (S.erase i) G from rfl,
      Ray.solution_add (h.goes _ x i) (g.goes _ x i), smul_add]
  simp [fillRay,hi]

omit [CompleteSpace V] in
lemma fillRay_scale (b : Cover) (i : Axis) (F : Cell ℤ → V) (r : ℝ) :
    fillRay b i (r • F)=r • fillRay b i F := by
  funext ⟨x,S⟩; by_cases hi : i∈S
  · simp only [fillRay,hi,↓reduceIte, Pi.smul_apply]; rw [show along i x (S.erase i) (r • F)=r • along i x _ F from rfl,
      Ray.solution_scale,smul_comm r]
  simp [fillRay,hi]
omit [CompleteSpace V] in
@[simp] lemma fillRay_zero (b : Cover) (i : Axis) : fillRay (V:=V) b i 0=0 := by
  funext ⟨x,S⟩; simp_rw [fillRay,show ∀ x S,along i x S (0:Cell ℤ→V)=0 from fun _ _ => rfl,Ray.solution_zero,smul_zero,ite_self]; rfl

omit [CompleteSpace V] in
private lemma along_transverse (i j : Axis) (x : Cover) (S : Finset Axis) (h : i≠j) (hj : j∉S)
    (F : Cell ℤ → V) :
    along i x S (sect j F)=sign S j • (along i (x-step j) (insert j S) F - along i x (insert j S) F) := by
  funext k; unfold along; rw [sect_at,if_neg hj]
  rw [show update x i k-step j=update (x-step j) i k by
    funext r; by_cases hi : r=i <;> simp [hi,h]]; rfl

/-- Anti-commutation with transverse incidences. -/
theorem other_axis (b : Cover) (i j : Axis) {F : Cell ℤ → V} (h : sums F) (hs : j≠i) :
    sect j (fillRay b i F) + fillRay b i (sect j F)=0 := by
  funext ⟨x,S⟩; by_cases hi : i∈S
  · by_cases hj : j∈S
    · have hm : j∈S.erase i := by simp [hj,hs]
      rw [Pi.add_apply,sect_at, if_pos hj]; simp only [fillRay, hi, ↓reduceIte,zero_add]
      have hh : along i x (S.erase i) (sect j F) = 0 := by funext k; simp [along,sect_at,hm]
      rw [hh,Ray.solution_zero,smul_zero]; rfl
    let T := S.erase i; have hg : j∉T := by simp [T,hj]
    have he : i∉T := by simp [T]
    have hc : insert i T = S := Finset.insert_erase hi
    have hp : (insert j S).erase i = insert j T := by ext; simp [T]; grind
    have hy := sign_neg T i j hs.symm he hg
    rw [hc] at hy
    have hz : sign (insert j S) i=sign (insert j T) i := by rw [← sign_remove (insert j S),hp]
    rw [show sign T i=sign S i from sign_remove S i] at hy
    have hw : sign S i * sign T j = -(sign S j*sign (insert j T) i) := by
      calc
        _ = (sign S i * sign S j)*(sign S j * sign T j) := by
          rw [show (sign S i*sign S j)*(sign S j*sign T j) = (sign S j*sign S j)*(sign S i*sign T j) from by ring, sign_sq,one_mul]
        _ = _ := by rw [hy]; have he := sign_sq T j; grind
    simp only [Pi.add_apply,sect_at,hj, ↓reduceIte,fillRay, hi,Finset.mem_insert,
      or_true, Pi.sub_apply, step_apply,hs.symm, ↓reduceIte, sub_zero, hp,hz]
    rw [along_transverse _ _ _ T hs.symm hg, Ray.solution_scale,Ray.solution_sub (h.goes _ _ i) (h.goes _ _ i),← smul_sub,
      smul_smul,smul_smul, hw,neg_smul,add_neg_cancel]; rfl
  simp only [Pi.add_apply,sect_at,fillRay]; split_ifs <;> simp_all

theorem slides (b : Cover) (i : Axis) {F : Cell ℤ → V} (h : sums F) :
    rim (fillRay b i F) + fillRay b i (rim F)= F-squeezed b i F := by
  have hh (s : Finset Axis) : fillRay b i (∑ j∈s,sect j F) = ∑ j∈s,fillRay b i (sect j F) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hd ih =>
      rw [Finset.sum_insert hd,Finset.sum_insert hd, fillRay_add b i (h.sects j) ?_, ih]
      intro x
      simp_rw [Finset.sum_apply]
      exact summable_sum fun j _ => (h.sects j) x
  rw [rim,LinearMap.sum_apply,LinearMap.sum_apply, hh,← Finset.sum_add_distrib]
  rw [Finset.sum_eq_single i (fun j _ hj => other_axis b i j h hj) (fun hj => (hj (Finset.mem_univ _)).elim),same_axis b i h]
end YM.AnalyticNext.QuarticMatch.BoxChain
