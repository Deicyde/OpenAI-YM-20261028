import YM.WilsonBulk.Build.Clock
import YM.WilsonBulk.Slice.Planar
import YM.Work.F05.Measure
import YM.Push.FREE_RESOLVENT.Windows

/-!
# Branch REAL shifts at zero, reindexed to any common price frame

Use on finite tori only. Not a claim over horizon of paths yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Atelier
open Lattice Laurent RG Precision Exterior Stationary Audience Bloch FreeResolvent Sheet
open Function Filter Matrix Wilson
open scoped Classical Topology ContDiff BigOperators Matrix
variable {c f n : Side} {P : Patch} {G : Gauge} {S : StepData c f} {r : ℕ}

abbrev Interface (G : Gauge) (n : Side) := Vec G n 1
-- align named fields; Lean still needs resected coordinate.

def traces (G : Gauge) (n : Side) (r : ℕ) : Tabletop (FreeResolvent.Slot G n r) ≃L[ℝ] fieldDir G n r :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun v i=> WithLp.toLp 2 (fun j:G.ColorIndex=> v (ix i j))
    invFun := FreeResolvent.flatten
    left_inv:= fun _=>rfl
    right_inv:=fun _ =>rfl
    map_add' _ _:= rfl
    map_smul' _ _:= rfl }
lemma traces_at (v : Tabletop (FreeResolvent.Slot G n r)) (i : Body r n) (j) : traces G n r v i j=v (ix i j) := rfl -- r variable
lemma traces_symm (x : fieldDir G n r) : (traces G n r).symm x= FreeResolvent.flatten x := rfl
-- absolute production

def signal (G : Gauge) (n : Side) (x : Interface G n) := represent (traces G n 1 x)
lemma signal_at (x : Interface G n) (e : Edge (Site n)) : signal G n x e = G.lieExp (traces G n 1 x (e.1,coord e.2)) := mul_one _
lemma signal_zero : signal G n 0=1 := by unfold signal; rw [map_zero,link_one]
lemma signal_cont (G : Gauge) (n : Side) : Continuous (signal G n) := by
  apply continuous_pi; intro i; simp_rw [signal_at]; exact G.lieExp_cont.comp ((continuous_apply (A:=fun _:Body 1 n=> G.Color) (i.1,coord i.2)).comp (traces G n 1).continuous)

namespace Coursing
variable (G) {ι κ : Type} [Fintype ι]
variable (F L : Coursing ι S)
-- basis free real map, reindexed norm; not assuming chart basis matter

def dress : Tabletop (LegsT G ι) ≃L[ℝ] AxisChart G F.tree := LinearEquiv.toContinuousLinearEquiv {
    toFun x := FreeResolvent.profile F.tree (x ∘ (F.flag G).symm)
    invFun x:= FreeResolvent.active F.tree x ∘ F.flag G
    left_inv x:= by dsimp only; rw [active_profile,Function.comp_assoc, Equiv.symm_comp_self, comp_id]
    right_inv x:= by dsimp only; rw [Function.comp_assoc, Equiv.self_comp_symm,comp_id]; rfl
    map_add' _ _:= rfl
    map_smul' _ _:=rfl }
lemma dress_label (x : Tabletop (LegsT G ι)) (i : F.tree.Free) (k) : dress G F x i k=x (F.label.symm i,k):= rfl
lemma dress_coord (x : Tabletop (LegsT G ι)) (i : ι) (k) : dress G F x (F.label i) k=x (i,k):= by rw [dress_label,Equiv.symm_apply_apply]
lemma dress_reindex (x : Tabletop (LegsT G ι)) : dress G L x= Work.F05.index (F.label.symm.trans L.label) (dress G F x) := by
  ext1 i; obtain ⟨j,rfl⟩:= L.label.surjective i; ext k
  rw [dress_coord,show L.label j=(F.label.symm.trans L.label) (F.label j) by simp, Work.F05.index_apply,dress_coord]
-- shifted private chamber to full

def priceK (P : Bed) := (trunk G F).transpose * predictor G F.tree P
lemma widen (P : Bed) : trunk G F * priceK G F P = predictor G F.tree P := by rw [priceK,← Matrix.mul_assoc]; exact sticking ..
variable [Fintype κ]
variable {F}
-- lay in v:u(ξ) log-coarse chart, *absolute*; then pack private log x=y_A+priceK θ

def whitener (F : Coursing ι S) (P : Bed) (u : Tabletop κ→Interface G c) (v : Tabletop (Chamber (LegsT G ι) κ)) : Tabletop (LegsT G ι) :=
  upper _ _ v + quill (priceK G F P) (u (lower _ _ v))
def palace (F : Coursing ι S) (P : Bed) (u : Tabletop κ→Interface G c) (v : Tabletop (Chamber (LegsT G ι) κ)) := quill (F.trunk G) (whitener G F P u v)
def porch (F : Coursing ι S) (P : Bed) (u : Tabletop κ→Interface G c) (v : Tabletop (Chamber (LegsT G ι) κ)) := Sum.elim (palace G F P u v) (u (lower _ _ v))
lemma palace_at (z : Tabletop (Chamber (LegsT G ι) κ)) (P : Bed) (u : Tabletop κ→Interface G c) : palace G F P u z= quill (F.trunk G) (upper _ _ z)+quill (predictor G F.tree P) (u (lower _ _ z)) := by rw [palace, whitener, quill_add,quill_chain, widen]
variable {P : Bed} {u : Tabletop κ→Interface G c}
lemma whiten_zero (hu : u 0=0) : whitener G F P u 0=0:= by unfold whitener; rw [map_zero,map_zero,hu,quill_zero,add_zero]
lemma whiten_jet (h : ContDiffAt ℝ ω u 0) : ContDiffAt ℝ ω (whitener G F P u) 0:= by
  let U := upper (LegsT G ι) κ; let D := lower (LegsT G ι) κ; exact U.contDiff.contDiffAt.add ((quill_smooth _).contDiffAt.comp (f:=u ∘ D) (0:Tabletop (Chamber (LegsT G ι) κ)) ((D.map_zero.symm ▸ h).comp _ D.contDiff.contDiffAt))
lemma palace_zero (hu : u 0=0) : palace G F P u 0=0 := by rw [palace,whiten_zero _ hu,quill_zero]
lemma palace_jet (hu : ContDiffAt ℝ ω u 0) : ContDiffAt ℝ ω (palace G F P u) 0 := (quill_smooth _).contDiffAt.comp _ (whiten_jet _ hu)
lemma porch_zero (hu : u 0=0) : porch G F P u 0=0 := by rw [porch,palace_zero _ hu,map_zero,hu]; ext1 i; cases i <;> rfl
lemma porch_jet (hu : ContDiffAt ℝ ω u 0) : ContDiffAt ℝ ω (porch G F P u) 0 := assemble_jet (palace_jet G hu) ((show ContDiffAt ℝ ω u (lower (LegsT G ι) κ 0) by rw [map_zero]; exact hu).comp _ (lower (LegsT G ι) κ).contDiff.contDiffAt)
lemma porch_code (hu : ContDiffAt ℝ ω u 0) (h : u 0=0) : exposure (porch G F P u)= seating (predictor G F.tree P) (F.trunk G) (exposure u) := by
  let D := lower (LegsT G ι) κ; let U:= upper (LegsT G ι) κ; let W:= predictor G F.tree P; let T:= F.trunk G
  have he : ContDiffAt ℝ ω (u ∘ D) 0:= (show ContDiffAt ℝ ω u (D 0) by rw [map_zero]; exact hu).comp _ D.contDiff.contDiffAt
  have hx : (u ∘ D) 0=0 := by simp only [Function.comp_apply,map_zero,h]
  have hf : exposure (u ∘ D)= fun i=> boast (LegsT G ι) κ (exposure u i) := by rw [expose_assoc hu h D.contDiff.contDiffAt (map_zero _), show submit (exposure D) =_ from (boast_neat (α:=LegsT G ι) (β:=κ))]
  rw [show porch G F P u = fun z=>Sum.elim (palace G F P u z) ((u ∘ D) z) from rfl, expose_assemble (V:=u ∘ D)]
  have hp : palace G F P u = (quill T (A:=ℝ)) ∘ U + (quill W) ∘ (u ∘ D) := funext fun z=> palace_at ..
  rw [hp, exposure_plus (u:=(quill T (A:=ℝ)) ∘ U) (v:=(quill W) ∘ (u ∘ D))
    ((quill_smooth T).contDiffAt.comp _ U.contDiff.contDiffAt) ((quill_smooth W).contDiffAt.comp _ he) (by rw [Function.comp_apply,map_zero,quill_zero]) (by rw [Function.comp_apply,hx,quill_zero]),exposure_quill T U.contDiff.contDiffAt (map_zero _),exposure_quill W he hx,hf]; ext1 i; cases i with
  | inl i=> simp only [U,upper_code,Sum.elim_inl,T]; rfl
  | inr i=> simp only [Sum.elim_inr,Sheet.seating]
section
omit [Fintype κ]
-- actual links reached

def costumed (F : Coursing ι S) (x : Tabletop (LegsT G ι)) : AxisChart G F.tree := F.dress G x
lemma signal_trunk (F : Coursing ι S) (x : Tabletop (LegsT G ι)) : signal G f (quill (F.trunk G) x)= F.tree.drape (Work.F05.exposure F.tree 0 (costumed G F x)) := by
  funext e; rw [signal_at]; by_cases he : e∈ F.tree.trunks
  · rw [show F.tree.drape _ e=1 from F.tree.on_tree _ ⟨e,he⟩, show traces _ _ _ _ _=0 from ?_,G.mat_lieExp_zero]
    ext j; rw [traces_at]; apply insertion_misses (F.dock G) x (ix _ j)
    rintro ⟨w,hw⟩; unfold dock Function.comp at hw; unfold plant at hw
    apply (F.flag G w).1.property; rw [show (F.flag G w).1.val=e from Prod.ext (congr_arg (fun i:Pennant G f=> i.1) hw) ((coord_iff ..).mp (congr_arg (fun i:Pennant G f=> i.2.1) hw))]; exact he
  let k : F.tree.Free := ⟨e,he⟩
  rw [show F.tree.drape _ e= _ from F.tree.off_tree _ k]; simp only [Work.F05.exposure,link_one,replica_one,Pi.one_apply, mul_one]; congr 1; ext j; rw [traces_at, costumed, dress_label]
  have hz : (F.dock G) (F.label.symm k,j) = ix (e.1,coord e.2) j := by simp only [dock, Function.comp_apply,flag,Equiv.prodCongr_apply,Equiv.apply_symm_apply,Equiv.refl_apply,Prod.map]; rfl
  rw [← hz]; exact insertion_at (F.dock G) x ((plant_inj F.tree).comp (flag G F).injective) _
end
end Coursing
end YM.WilsonBulk.Atelier
