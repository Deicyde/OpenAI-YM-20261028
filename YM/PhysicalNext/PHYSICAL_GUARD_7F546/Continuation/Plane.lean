import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Hop
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Stencil
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Reads
import YM.UVNext.PRICED_KERNELS.Read

/-!
# Slot and curvature loading in the common frame

First add m shift, then plant on the FREE register (including frozen
positions), by zero off the window, and take physical d₁ curls. Check
planting doesn't affect the occasion reads of a reference head taken
on the full tree. No claim about a pose not meeting X. All signs for the
Lattice basis as in E transfer/cutHead; in particular the restored slot on
a U uses its whole original path (possibly repeated, all reads must still obey
the same actual geometric hypotheses). No independence law for different SlotsW components.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Rows Tree Bid MomentBound
open YM.AnalyticBridge.LocalGaussianLaws Current Lift Remote Local
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff MeasureTheory

variable {G : Gauge} {c f n : Side} {S : StepData c f}
    {F : Forest S.ratio} {x β : ℝ} {A : Stores S} {g : ℝ}

open FreeResolvent (treeInverse flatten insertion plant)

/-- E: μ₀ along m's actual reads, compared after augmenting the fluctuation by *target minus
reference* (physical link means divided by g). -/
def rebase (T : Tube G S) (v : Dir G c) (a : Gaussian.Vec (In x A F (G:=G)))
    (g : ℝ) (W : Finset (Bond f)) (Z : Gaussian.Vec (In x A F (G:=G))) :=
  let e := accessing A F x W G; let l := loading A F x W G
  displacement a (portrait_head T F v) g e l + Z ∘ e
lemma rebase_equal (T : Tube G S) (v : Dir G c) (a : Gaussian.Vec (In x A F (G:=G)))
    (hg : g ≠ 0) (W : Finset (Bond f)) (Z : Gaussian.Vec (In x A F (G:=G))) :
    let e := accessing A F x W G; let l := loading A F x W G
    rebase T v a g W Z = inUnits (portrait_head T F v ∘ l) g (physicalRead a g e Z) :=
  (readUnits_target _ _ hg _ _ _).symm
lemma restore_window (T : Tube G S) (v : Dir G c) (a : Gaussian.Vec (In x A F (G:=G)))
    (hg : g ≠ 0) (W : Finset (Bond f)) (Z : Gaussian.Vec (In x A F (G:=G))) :
    let e := accessing A F x W G; let l := loading A F x W G
    physicalRead a g e Z=restore (portrait_head T F v ∘ l) g (rebase T v a g W Z) := by
  intro e l; rw [rebase_equal T v a hg]; exact (restore_inUnits _ hg _).symm

def vertical (S : StepData c f) {F : Forest S.ratio} (z : Gaussian.Vec (FreeResolvent.Active G F)) : Dir G f :=
  stretch (S:=S) F (0, tape z)

def plantW (S : StepData c f) {F : Forest S.ratio} {A : Stores S} {W : Finset (Bond f)}
    (z : Gaussian.Vec (SlotsW A F x W G)) : Gaussian.Vec (FreeResolvent.Active G F) :=
  insertion (loading A F x W G) *ᵥ z

def liftedCurl (z : Gaussian.Vec (FreeResolvent.Active G F)) := dColor G f 1 (vertical S z)
def sectionCurl {W : Finset (Bond f)} (z : Gaussian.Vec (SlotsW A F x W G)) := liftedCurl (S:=S) (F:=F) (plantW S z)

lemma authentic (z : Gaussian.Vec (FreeResolvent.Active G F)) :
    flatten (liftedCurl (S:=S) z) = Current.plane S F *ᵥ z := by
  unfold Current.plane; rw [← mulVec_mulVec]
  have he : insertion (plant F) *ᵥ z = flatten (vertical S z) := FreeResolvent.chart_flow S F (tape z)
  rw [he]; funext i
  exact (congr_fun (FreeResolvent.component_mul (d 1 f) (flatten (vertical S z)) i.2.2) (i.1,i.2.1)).symm

lemma curl_formula (v : Dir G n) (p : Cell n) :
    Work.F03.faceCurl p v=
      collect G v (p.1,p.2.val.1)+collect G v (p.1+step p.2.val.1,p.2.val.2)-
        collect G v (p.1+step p.2.val.2,p.2.val.1)-collect G v (p.1,p.2.val.2) := by
  rw [Work.F03.faceCurl,← Exterior.fundamental]
  let a := p.2.val.1; let b := p.2.val.2
  have h (x : Site n) (i j : Axis) : x + step i + step j - step i = x + step j := by abel
  have h' (x : Site n) (i j : Axis) : x + step i + step j + (- step i) = x + step j := by abel
  simp only [Lattice.square, linkSum, Step.used,Step.vec, negDir,posDir, Bool.false_eq_true, ↓reduceIte,
    collect, add_zero, h,h',add_sub_cancel_right]
  simp only [sub_eq_add_neg]; abel
lemma curl_price (v : Dir G n) (p : Cell n) {r : ℝ}
    (h : ∀ e∈bones p, ‖collect G v e‖ ≤ r) : ‖Work.F03.faceCurl p v‖ ≤ 4*r := by
  rw [curl_formula]
  exact (norm_sub_le ..).trans ((add_le_add ((norm_sub_le ..).trans (add_le_add
    ((norm_add_le ..).trans (add_le_add (h _ (first_bone p)) (h _ (second_bone p))))
    (h _ (third_bone p)))) (h _ (last_bone p))).trans_eq (by ring))

lemma plant_on {W : Finset (Bond f)} (z : Gaussian.Vec (SlotsW A F x W G)) (i : Window A F x W) :
    collect G (vertical S (plantW S z)) i.val.val.val = tape z i := by
  let j := i.val.val
  rw [vertical,Work.F01.collect_vertical,dif_neg i.val.val.property]; ext y
  change (plantW S z) (loading A F x W G (i,y)) = z (i,y)
  simp only [plantW,mulVec,dotProduct,insertion,of_apply, ite_mul, zero_mul, one_mul,
    (loading A F x W G).injective.eq_iff]
  rw [Finset.sum_eq_single (i,y)]
  · simp
  · intro x _ h
    rw [if_neg h]
  simp
lemma on_tree (z : Gaussian.Vec (FreeResolvent.Active G F)) (i) (h : i∈F.trunks) :
    collect G (vertical S z) i = 0 := (Work.F01.collect_vertical F (tape z) i).trans (dif_pos h)

/-- Reference z on all ideal coordinates. On a readable W planting a
restriction gives the same genuine curls. No claim of replacing z data
on the rest of the torus for any other simultaneous probe. -/
lemma reads_curl (z : Gaussian.Vec (FreeResolvent.Active G F)) {W : Finset (Bond f)}
    (p : Cell f) {o : Site c} (hx : Clears A x o (radiusB x))
    (h : bones p ⊆ W) (hu : Reachable S o x W) :
    sectionCurl (z ∘ loading A F x W G) (p.1,plaquette p.2) =
      liftedCurl (S:=S) z (p.1,plaquette p.2) := by
  have hh (e) (he : e∈bones p) :
      collect G (vertical S (plantW S (z ∘ loading A F x W G))) e = collect G (vertical S z) e := by
    by_cases hF : e∈F.trunks
    · rw [on_tree _ _ hF,on_tree _ _ hF]
    let j : F.Free := ⟨e,hF⟩
    let i : Active A x F := ⟨j,live_test A F hx j ((hu _ (h he)).trans (by omega))⟩
    let k : Window A F x W := ⟨i,h he⟩
    calc
      _ = tape (z ∘ loading A F x W G) k := plant_on _ k
      _ = _ := by rw [vertical,Work.F01.collect_vertical,dif_neg hF]; rfl
  change Work.F03.faceCurl p _ = Work.F03.faceCurl p _
  rw [curl_formula,curl_formula,hh _ (first_bone p),hh _ (second_bone p),hh _ (third_bone p),hh _ (last_bone p)]


lemma inputsCurl (P : Occasion G f) {W : Finset (Bond f)} (z : Gaussian.Vec (SlotsW A F x W G))
    {X : Support f} {o : Site c} (hx : Clears A x o (radiusB x)) (hP : P.place ⊆ X)
    (hp : Covers X W) (hu : Reachable S o x W) :
    ‖sectionCurl z P.coordFace‖ ≤ 4*((Fintype.card G.ColorIndex:ℝ)*‖z‖) := by
  have hv := hP P.face_mem
  refine curl_price _ P.face ?_
  intro e he; by_cases hF : e∈F.trunks
  · rw [on_tree _ _ hF,norm_zero]; positivity
  have He : e∈W := hp.flags P.face ⟨_,hv,Work.E01.base_touched _⟩ he
  let j : F.Free := ⟨e,hF⟩
  let i : Active A x F := ⟨j,live_test A F hx j ((hu _ He).trans (by omega))⟩
  let k : Window A F x W := ⟨i,He⟩
  have hk := plant_on z k
  change collect G _ e=_ at hk; rw [hk]
  exact UVNext.PricedKernels.color_count (norm_nonneg _) _ (fun i => norm_le_pi_norm z (k,i))

@[fun_prop]
lemma section_cont {W : Finset (Bond f)} (v : Occasion G f) : Continuous (fun z : Gaussian.Vec (SlotsW A F x W G) =>
    sectionCurl z v.coordFace v.color) := by
  have he z : sectionCurl z v.coordFace v.color =
      (Current.plane S F *ᵥ (insertion (loading A F x W G) *ᵥ z)) v.bead :=
    congr_fun (authentic (S:=S) (plantW S z)) v.bead
  simp_rw [he]; unfold Matrix.mulVec dotProduct; fun_prop

/-- On the assessed links, the *actual* comparison with shared field has
this exact factorization (two Lie exponentials, in order), harmless even
without a central guard. DON'T commute the factors on a crossing. -/
lemma link_frame (T : Tube G S) (v : Dir G c) (a Z : Gaussian.Vec (In x A F (G:=G)))
    (Y : LinkArray G (Frozen A x F)) (V : Config G c) {o W} (hv : AgreeNear id o (radiusB x) V (represent v))
    (h : Clears A x o (radiusB x)) (hw : Reachable S o x W) (hg : g≠0) :
    let u := physical A F V Y (tape (a+g • Z))
    let y := vertical S (plantW S (rebase T v a g W Z))
    ∀ e∈W,
      u e = G.lieExp (doc T F v e + g • collect G y e) * G.lieExp (collect G (blueprint S v) e) := by
  intro u y e he
  have Hi : replica S.ratio V e = G.lieExp (collect G (blueprint S v) e) := calc
    _ = replica S.ratio (represent v) e := copyAgree _ _ _ _ hv _ ((hw _ he).trans (by omega))
    _ = _ := by rw [replica_rep]; exact Work.F03.represent_link ..
  by_cases hF : e∈F.trunks
  · have hh : linearCopy S.ratio (collect G v) e = 0 := if_pos (F.trunk_internal (show (e.1,e.2) ∈ F.trunks from hF))
    rw [doc_trunk T F v e hF,on_tree _ _ hF,smul_zero,add_zero,blueprint,
      Flat.collected,hh]; simp only [G.mat_lieExp_zero,one_mul]
    exact F.on_tree _ ⟨e,hF⟩
  let j : F.Free := ⟨e,hF⟩
  let i : Active A x F := ⟨j,live_test A F h j ((hw _ he).trans (by omega))⟩
  let k : Window A F x W := ⟨i,he⟩
  let ζ := rebase T v a g W Z
  have ht : thaw F (chill A x F) (replica S.ratio V) Y (tape (a+g • Z)) i.val =
      G.lieExp (tape (a+g • Z) i) * replica S.ratio V e := freeze_regular ..
  rw [show u e= returned A F V Y (tape (a+g • Z)) i.val from F.off_tree _ i.val]; unfold Next.SectorChange.returned; rw [ht, Hi]
  have hk : collect G y e=tape ζ k := plant_on ζ k
  rw [hk]
  congr 2 -- want tape ... = _
  ext w
  exact congr_fun (restore_window T v a hg W Z) (k,w)


end YM.PhysicalNext.PhysicalGuard7f546.Curved
