import YM.FullVolume.Sluggish

/-! Finite iterated literal variations ARE potential marks with full prices
unextracted. Normalize by the actual mesh. No claim here of analytic interpolation
in position; step and direction vectors are fixed before making the estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Lattice Labels Wilson RG Extraction Extraction.Lease Push Filter
open Push.RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {n : Side} {d : ℕ}

/-- one-site forward normalized difference on literal insertions -/
def farther (F : Trial C) (a : Axis) : Trial C:=
    fun N p o=> (C.S.a N:ℂ)⁻¹ • (F N p (o+step a)-F N p o)

def hops (F : Trial C) : List Axis → Trial C
  | [] => F
  | a::l => farther (hops F l) a

lemma hops_solid {F : Trial C} (h: ∀ᶠ i in mesh, ∀ o, Continuous (F i.1 i.2 o)) (l : List Axis) :
    ∀ᶠ i in mesh, ∀ o, Continuous ((hops F l) i.1 i.2 o):=by
  induction l with
  | nil=> exact h
  | cons a l ih=> exact ih.mono fun i hi o=> ((hi _).sub (hi o)).const_smul _

def Stencil (F : Trial C) := ∃ X : Finset Cover, ∀ᶠ i in mesh, RelayDifference.Local X (F i.1 i.2)

namespace Stencil
variable {F H:Trial C}

lemma visits (h:C.Makes)(p : Bid.Rowe C d) : Stencil (Bid.upper C p):=
    ⟨_,Eventually.of_forall fun _=>local_primary h _⟩
lemma sub (hp:Stencil F)(hq:Stencil H):Stencil (F-H):=by
  obtain ⟨X,h⟩:=hp; obtain ⟨Y,H⟩:=hq
  exact ⟨X ∪ Y,(h.and H).mono fun i hi=> hi.1.sub hi.2⟩
lemma farther (h : Stencil F)(a:Axis) : Stencil (FullVolume.farther F a):=by
  obtain ⟨X,hX⟩:=h; exact ⟨X.image (fun x => x+step a) ∪ X, hX.mono fun i hi => RelayDifference.Local.smul _ ((hi.step a).sub hi)⟩
lemma hops (h : Stencil F)(a:List Axis) : Stencil (FullVolume.hops F a):=by
  induction a with
  | nil => exact h
  | cons i a ih => exact ih.farther i
end Stencil

def Tucked (F : Trial C) (d : ℕ) :=
    ∃ X : Finset Cover, 0∈X ∧ ∃ c b : Cutoffs → ℝ, Sluggish C c ∧ Sluggish C b ∧
    ∀ᶠ i in mesh, ∀ o, clothed (C.path.levels.budget i.1) (regional X o) o (unpriced C F d i.1 i.2 o) (c i) (b i)

lemma funded {F:Trial C}{N p d:ℕ} (a : Axis) (o : Site (C.side N p)) :
    unpriced C (farther F a) (d+1) N p o =
      unpriced C F d N p (o+step a)-unpriced C F d N p o := by
  dsimp only [unpriced,farther,RelayDifference.weight]
  have ht : (C.S.a N:ℂ) ≠ 0 := by exact_mod_cast (C.S.a_pos N).ne'
  rw [pow_succ,smul_smul, mul_assoc,mul_inv_cancel₀ ht,mul_one,smul_sub]
namespace Tucked
variable {F : Trial C}

theorem up (h : C.Makes) (K : G.Simple) (v : Bid.Rowe C d) (hw : Coin C v) :
    Tucked (Bid.upper C v) d := by
  let T := C.localSection d
  let F := C.labels.level d
  let B (i : Cutoffs) := C.path.levels.budget i.1
  let x (i : Cutoffs) : C.label d := (C.factory d i.1 i.2).terminal.symm (v i)
  obtain ⟨b,hb,hB⟩ := offmask C d
  let c i := (C.path.levels.params (Prod.fst i)).columns * F.coeffSize (x i)
  let u i := b * F.coeffSize (F.scaled ((B i).threshold⁻¹) (x i))
  refine ⟨T.stencil,(h.sections d).anchored,c,u,
    (pillars (C:=C)).mul (carding x hw), (Sluggish.const (C:=C) b).mul (FullVolume.scaling x hw K),?_⟩
  filter_upwards [deepen.eventually_ge_atTop (C.ref d)] with j hi o
  change clothed _ _ _ (RelayDifference.weight C d j.1 • C.O j.1 j.2 (v j) o) (c j) (u j)
  rw [charged]
  exact ⟨(section_bounds C _ _ _ h hi o (x j)).1,(section_bounds C _ _ _ h hi o (x j)).2,
    mul_nonneg (zero_le_one.trans hb) (coeff_pos ..), hB _ _ o⟩

theorem farther (h : Tucked F d) (hP : Sluggish C (fun i=>jump (C.path.levels.budget i.1))) (a:Axis):
    Tucked (FullVolume.farther F a) (d+1):= by
  obtain ⟨X,hX,c,b,hc,hb,H⟩ := h
  let D := X.image (fun x => x + step a) ∪ X
  refine ⟨D,Finset.mem_union_right _ hX,_,_,(hP.mul hc).add hc,hb.add hb,?_⟩
  filter_upwards [H] with i hi o
  obtain ⟨hx,hA,hB,hU⟩ := hi o
  obtain ⟨hy,hY,hQ,hv⟩ := hi (o+step a)
  have hD : regional X (o+step a) ⊆ regional D o := by
    rintro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨_,Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy), by rw [map_add,wrap_step]; abel⟩
  have hD' : regional X o ⊆ regional D o := Finset.image_subset_image Finset.subset_union_right
  have hm := Next.Foundations.regular_larger hy hD
  have hs := Next.Foundations.regular_larger hx hD'
  have ha : separation (o+step a) o ≤ 1 := by rw [separation, add_comm, add_sub_cancel_right]; exact pdist_step _
  rw [funded a]; open Next.Foundations in
  exact ⟨regular_sub hm hs, bound_sub hm hs (bound_larger (dir_shift _ _ _ _ _ ha hY) hD) (bound_larger hA hD'),
    add_nonneg hQ hB, fun U => (norm_sub_le ..).trans (add_le_add (hv U) (hU U))⟩

theorem hops (h : Tucked F d) (hP : Sluggish C (fun i=>jump (C.path.levels.budget i.1)))(a:List Axis):
    Tucked (FullVolume.hops F a) (d+a.length):= by
  induction a with
  | nil=> exact h
  | cons i a ih=> simpa only [List.length_cons,← add_assoc] using! ih.farther hP i
end Tucked
end YM.FullVolume
