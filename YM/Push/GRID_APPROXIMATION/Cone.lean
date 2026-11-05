import YM.Next.EXTRACTION.Mixture
import YM.Ovens.Coffee
import YM.Work.C06

/-!
# Backward dependence cone geometry for the **actual** patches

Native sites. Bounds purposely loose, but of order `(J+1) L` fine
sites per step, also budgeting the frame choice and fallback tests. No
restriction on wrapping. Site-based locality including *both* endpoints.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open Function Lattice Wilson RG Cells
open scoped Topology BigOperators

variable {G : Gauge} {n c f : Side}

/-- Finite native torus ball (as a set). Allows periodic images. -/
def window (x : Site n) (r : ℕ) : Set (Site n) :=
  (fun y => wrap n y + x) '' (box r : Set Cover)

lemma box_larger {r R : ℕ} {x : Cover} (h : x∈box r) (he : r≤R) : x∈box R := by
  have ht := box_test.mp h
  rw [box_test]; constructor <;> intro i <;> specialize ht <;>
    have := ht.1 i <;> have := ht.2 i <;> omega

lemma window_home (x : Site n) (r : ℕ) : x ∈ window x r :=
  ⟨0, center_box _, by dsimp only; rw [map_zero,zero_add]⟩

lemma window_add {r R : ℕ} {x y z : Site n} (h : y∈window x r) (he : z∈window y R) :
    z∈window x (r+R) := by
  obtain ⟨a,ha,rfl⟩ := h; obtain ⟨b,hb,rfl⟩ := he
  refine ⟨b+a, ?_, by dsimp only; rw [map_add,add_assoc]⟩
  change b+a∈box _
  obtain ⟨ha,hA⟩ := box_test.mp (show a∈box _ from ha)
  obtain ⟨hb,hB⟩ := box_test.mp (show b∈box _ from hb)
  rw [box_test]; constructor <;> intro i <;> rw [Pi.add_apply]
  · have := ha i; have := hb i; omega
  have := hA i; have := hB i; omega

lemma window_affine {r : ℕ} (x t : Site n) (s : Signed) :
    Set.MapsTo (affine s t) (window x r) (window (affine s t x) r) := by
  rintro y ⟨a,ha,rfl⟩
  refine ⟨s.act a,?_,?_⟩
  · change _ ∈ box _; rw [← box_covariant r s]; exact Finset.mem_image_of_mem _ ha
  dsimp only; rw [← wrap_signed]
  simp [affine,s.act_add,add_assoc]

lemma window_embed {x y : Site c} {r : ℕ} (s : Ratio c f) (h : y∈window x r) :
    s.embed y∈window (s.embed x) (s.count.val*r) := by
  obtain ⟨a,ha,rfl⟩ := h
  obtain ⟨ha,hA⟩ := box_test.mp (show a∈box _ from ha)
  refine ⟨s.count.val • a,?_,by change wrap f _ + _ = s.root ((wrap c) a + x); rw [map_add,Ratio.root_embed,s.embed_wrap]; rfl⟩
  change _ ∈ box _
  rw [box_test]; constructor <;> intro i
  · have ht := mul_le_mul_of_nonneg_left (ha i) (by positivity : 0 ≤ (s.count.val:ℤ)); simpa using ht
  have ht := mul_le_mul_of_nonneg_left (hA i) (by positivity : 0 ≤ (s.count.val:ℤ)); simpa using ht

variable (P : Patch)

/-- Loose enough even counting whole coordinate routes. -/
def reach := 10 * P.radius

private lemma visits_bound {r : ℕ} (w : Walk) (x : Cover) (h : x∈box r) :
    ∀ y ∈ visits x w, y∈box (r+w.length) := by
  induction w generalizing r x with
  | nil => simpa only [List.length_nil,Nat.add_zero,visits,List.mem_singleton,forall_eq] using h
  | cons d w ih =>
    have he : x+d.vec ∈ box (r+1) := by
      obtain ⟨hh,hH⟩ := box_test.mp h
      have ht (i : Axis) : -1 ≤ (d.vec : Cover) i ∧ (d.vec : Cover) i ≤ 1 := by
        unfold Step.vec; split <;> simp only [Pi.neg_apply, step_apply] <;> split <;> decide
      rw [box_test]; constructor <;> intro i <;> rw [Pi.add_apply] <;> have := ht i
      · have := hh i; omega
      have := hH i; omega
    intro y hy
    rcases List.mem_cons.mp hy with e|e
    · subst y; exact box_larger h (by omega)
    refine box_larger (ih (x+d.vec) he _ e) ?_
    simp; omega

private lemma route_bound {r : ℕ} (x y : Cover) (hx : x∈box r) (hy : y∈box r)
    (l : Lattice.Order) : (route x y l).length ≤ 8*r := by
  have he (s : List Axis) : (axisRoute x y s).length ≤ s.length*(2*r) := by
    induction s with
    | nil => simp [axisRoute]
    | cons i s ih =>
      have ht : (straight i (y i-x i)).length ≤ 2*r := by
        simp only [straight,List.length_replicate]; obtain ⟨hx,hX⟩ := box_test.mp hx; obtain ⟨hy,hY⟩ := box_test.mp hy
        have := hx i; have := hX i; have := hy i; have := hY i; omega
      rw [show axisRoute x y (i::s) = straight i (y i-x i) ++ axisRoute x y s from rfl,
        List.length_append, List.length_cons,add_mul]; omega
  have hh := he (allAxes l)
  have hh' : (allAxes l).length=4 := by simp [allAxes]
  rw [hh'] at hh
  unfold route; omega

private lemma expand_agrees {U V : Config G n} (x : Site n) (r : ℕ) (h : Agrees (window x r) U V) :
    Agrees (box r : Set Cover) (expandAt x U) (expandAt x V) := by
  rintro ⟨i,j⟩ he ht
  apply h (wrap n i+x,j) ⟨i,he,rfl⟩
  exact ⟨i+step j, ht, by simp [add_right_comm]⟩

private lemma agrees_mono_cover {U W : CoverConfig G} {A B : Set Cover} (h : Agrees A U W) (he : B ⊆ A) : Agrees B U W :=
  fun i hi hx => h i (he hi) (he hx)

section patch
variable {K : KernelChoices}

/-- Backs up to *actual* frame and site tag reads. In particular, equality
in the minimizing branch test doesn't license skipping the fallback read. -/
lemma patch_dep (hB : P.Branches K G) (t : P.FrameTag) {U W : CoverConfig G}
    (hA : Agrees (box (reach P)) U W) : P.frame K U t = P.frame K W t ∧
      P.frameMass K U t = P.frameMass K W t := by
  have hr (x : P.Points) : x.val∈box (reach P) := box_larger x.property (by unfold reach; omega)
  have he (x y : P.Points) (l : Lattice.Order) : travel U x.val (route x.val y.val l) =
      travel W x.val (route x.val y.val l) := by
    apply travel_local _ _ U W
    apply agrees_mono_cover hA
    intro z hz
    exact box_larger (visits_bound _ _ x.property z hz) (by have := route_bound _ _ x.property y.property l; unfold reach; omega)
  have hx (x : P.FrameTag) : P.axial U x = P.axial W x := funext fun i => he _ _ _
  have hv (f : P.Frame G) : P.via f U = P.via f W := by funext x y l; rw [Patch.via,Patch.via,he]
  have hs : P.score U = P.score W := by funext r; simp only [Patch.score,hv]
  have hm : P.usesMin K U ↔ P.usesMin K W := by simp only [Patch.usesMin,hv,hx]
  classical
  unfold Patch.frame Patch.frameMass
  by_cases hh : P.usesMin K W
  · rw [if_pos hh, if_pos (hm.mpr hh), if_pos hh, if_pos (hm.mpr hh)]
    have h' : P.minimizing W (P.selected U) := by
      simp only [Patch.minimizing, ← hs]; exact (P.min_exists U).choose_spec
    exact ⟨(hB.frame_unique W hh).unique h' (P.min_exists W).choose_spec,rfl⟩
  have hh' : ¬ P.usesMin K U := fun h => hh (hm.mp h)
  rw [if_neg hh, if_neg hh', if_neg hh, if_neg hh', hx]
  suffices h : P.eligible K U = P.eligible K W by rw [h]; simp
  have hU : P.facesum U = P.facesum W := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    split
    next ht =>
      have h : faceValue U (x.val,i)=faceValue W (x.val,i) := by
        apply travel_local _ _ U W
        apply agrees_mono_cover hA
        intro y hy; exact hr ⟨y,ht y hy⟩
      rw [h]
    next ht => rfl
  have hW (x : P.FrameTag) : P.axialCost U x = P.axialCost W x := by
    unfold Patch.axialCost; rw [hx]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    split
    next ht => rw [hA (j.val,i) (hr j) (hr ⟨_,ht⟩)]
    next ht => rfl
  unfold Patch.eligible; simp only [hU,hW]
end patch

variable (S : StepData c f)

lemma site_dep (hB : S.patch.Branches S.kernel G) (x : Site c) {U W : Config G f}
    (h : Agrees (window (S.ratio.embed x) (reach S.patch)) U W) (r : S.patch.FrameTag) :
    S.patch.frame S.kernel (expandAt (S.ratio.embed x) U) r = S.patch.frame S.kernel (expandAt (S.ratio.embed x) W) r ∧
    S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) U) r = S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) W) r :=
  patch_dep S.patch hB r (expand_agrees _ _ h)

lemma connector_dep (hB : S.patch.Branches S.kernel G) (e : Edge (Site c)) (t l : S.SitesChoice)
    (ht : t e.1=l e.1) (hl : t (e.1+step e.2)=l (e.1+step e.2)) {U W : Config G f}
    (hp : Agrees (window (S.ratio.embed e.1) (reach S.patch)) U W)
    (hq : Agrees (window (S.ratio.embed (e.1+step e.2)) (reach S.patch)) U W) :
    S.connector U t e = S.connector W l e := by
  have hh (x : S.patch.Points) : travel (expandAt (S.ratio.embed e.1) U) x.val
      (List.replicate S.patch.L.val (posDir e.2)) = travel (expandAt (S.ratio.embed e.1) W) x.val
      (List.replicate S.patch.L.val (posDir e.2)) := by
    apply travel_local
    apply agrees_mono_cover (expand_agrees _ _ hp)
    intro y hy
    refine box_larger (visits_bound _ _ x.property y hy) ?_
    have hh : S.patch.L.val ≤ S.patch.radius := by
      unfold Patch.radius; exact le_mul_of_one_le_left (Nat.zero_le _) (by omega)
    rw [List.length_replicate]; unfold reach; omega
  funext x
  rw [StepData.connector,StepData.connector]
  unfold StepData.frames
  rw [ht,hl,(site_dep S hB _ hp _).1,(site_dep S hB _ hq _).1,hh]
end YM.Push.GridApprox
