import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Agreements
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Channels
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Dollars
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Selection
import YM.Further.FREE_COVARIANCE_KP.KP.Core
import YM.Next.RANK.Flux.Chronicle
import YM.Next.RANK.Prepaid
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Ensemble
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Reoriented
import YM.Push.GRID_APPROXIMATION.AttachDefs



/-!
# Native Gaussian photo

Keep the native field and a single held law at given coarse field V.
For ignition on the same physical V the inputs actually have to use a
copy and **its** orientation, not just translate individual links. Do
this in one function of the field including
both live and thawed links. Prove on held tags. No assuming kernels of
candidate V obey the same push. The Rank tag law is NOT the density of
the interacting field! See Layout/Gallery for later use *reweighting*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     Next.Rank Tapes Perch Paint Spindle
    YM.PhysicalNext.PhysicalGuard7f546.Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x d g β : ℝ} {A : Stores S} {F : Forest S.ratio}

section vision
open SectorTools.PhysicalGaussianSwitch
abbrev RoomView (A : Stores S) (x : ℝ) (F : Forest S.ratio) (G : Gauge) := LinkArray G (Frozen A x F) × Gaussian.Vec (In x A F (G:=G))

def viewer (T : Tube G S) (A : Stores S) (x : ℝ) (F : Forest S.ratio) (k : S.Choices) (V : Config G c) : Measure (RoomView A x F G) :=
    (piHaar G (Frozen A x F)).prod (cloud (palette T A F k x V .endpoint))
instance (T : Tube G S) (k : S.Choices) (V : Config G c) : IsProbabilityMeasure (viewer T A x F k V) := by unfold viewer; infer_instance

def gazed (T : Tube G S) (k : S.Choices) (q : Chi) (V : Config G c) (x β d : ℝ) (Y : RoomView A x F G) : Config G f :=
    photo (coupling β) V (portrait T A F k x V .endpoint q d Y.1) Y.1 Y.2

lemma gazed_measible {T : Tube G S} (k : S.Choices) (V : Config G c) (q : Chi) {d : ℝ}
    (hd : 0<d) (hc : 2*d < firstRadius G) {Pt : Teller G} (hp : Pt.Funds S T) :
    Measurable (gazed T k q V x β d (F:=F) (A:=A)) := by
  let Q := portrait T A F k x V .endpoint q d; let g:=coupling β
  have hz : Continuous Q := portrait_sharp hp F A x V k q .endpoint d hd hc
  let K (i : RoomView A x F G) := (i.1,tape (Q i.1+g • i.2))
  have hK : Measurable K := measurable_fst.prodMk (tape.measurable.comp (hz.measurable.comp measurable_fst |>.add (by fun_prop)))
  change Measurable (uncurry (Next.SectorChange.physical A F V) ∘ K)
  exact (physical_meas A F V).comp hK

-- calls endpoint *precisely*. Even frozen readings agree.
lemma Q_endpoint (T : Tube G S) (x : ℝ) (k : S.Choices) (V : Config G c) :
    fog A F T x V k = palette T A F k x V .endpoint := (named_sector S A F x T k V Push.SectorMeasure.Chi.canonical 0).1
lemma mean_endpoint (T : Tube G S) (x : ℝ) (k : S.Choices) (V : Config G c) (q : Chi) (d : ℝ) : meanLog A F T x V k q d = portrait T A F k x V .endpoint q d := funext fun y => (named_sector S A F x T k V q d).2 y
end vision

section turned
open YM.AnalyticBridge.GaussianFieldAlignment Locations Channels Orthogonal Gauges Tensor Agreements
open Push.SectorMeasure.Oriented Presented GaugeRoute

variable (s : Signed) (t : Site c)
lemma turns_marks (A : Stores S) (V : Config G c) (u : ℝ) (h : A.flags=RG.flags u V) :
    (book s t A).flags=RG.flags u (pull s t V) := by
  ext i; unfold book
  change i ∈ A.flags.map _ ↔ _
  rw [Finset.mem_map_equiv, h]; change affine s t i∈RG.flags u V ↔ _
  rw [← Thirst.s_flags s t u V]; exact Thirst.stay ..



variable (F) (A)
def fan (x : ℝ) (V : Config G c) := Orthogonal.move (onBond (fiber s t V S)) (Locations.active s t A F x)

abbrev cusps (x : ℝ) (V : Config G c) (Y : RoomView A x F G) : RoomView (book s t A) x (Locations.forest s t F) G :=
    (rollY s t x A F Y.1, fan A F s t x V Y.2)

omit F A in
private lemma flipped_s (a b : G.El) (v : G.Color) (hv : b=G.lieExp v * a) : b⁻¹ = G.lieExp (-(G.adjoint a⁻¹ v))*a⁻¹ := by
  rw [exp_negative,exp_adjoint,hv]; group

lemma circulate (V : Config G c) (x g : ℝ) (Y : RoomView A x F G) (H : Prices G (Active A x F)) :
    let y:=cusps A F s t x V Y; let V':=pull s t V
    photo g V' (fan A F s t x V H) y.1 y.2 = pull s (S.ratio.embed t) (photo g V H Y.1 Y.2) := by
  intro y V'; let L:=Locations.book s t A; let M:=Locations.forest (S:=S) s t F; let e:=fan A F s t x V
  let z := H + g • Y.2; let a := tape z
  have hx : photo g V' (e H) y.1 y.2 = physical L M V' y.1 (tape (e z)) := by
    have H0 (u v : Gaussian.Vec (In x A F (G:=G))) : e (u+v)=e u+e v:= Matrix.mulVec_add ..
    have H1 : e (g • Y.2)=g • e Y.2 := Matrix.mulVec_smul ..
    unfold photo z; rw [H0,H1]
  change photo g V' (e H) y.1 y.2 = _
  rw [hx]
  funext i
  let f:=sendEdge s (S.ratio.embed t) i; let U:=photo g V H Y.1 Y.2
  let U':=physical L M V' y.1 (tape (e z))
  rw [Channels.read_back]
  change U' i = if s.flip i.2 then (U f)⁻¹ else U f
  by_cases ht : i∈M.trunks
  · have ht' : f ∈ F.trunks := (Locations.trunk_map s t F i).mp ht
    rw [show U' i=1 from M.on_tree _ ⟨i,ht⟩, show U f=1 from F.on_tree _ ⟨f,ht'⟩]; simp
  let j : M.Free:=⟨i,ht⟩
  let j':=Locations.free s t F j
  have hu : U f=returned A F V Y.1 a j' := F.off_tree _ j'
  have hv : U' i=returned L M V' y.1 (tape (e z)) j:= M.off_tree _ j
  by_cases hp : chill L x M j
  · let p : Frozen L x M:=⟨j,hp⟩
    rw [show U f=_ from hu.trans (show _= Y.1 (Locations.frozen s t A F x p) from freeze_held (j:=Locations.frozen s t A F x p) ..)]
    exact hv.trans (show _= y.1 p from freeze_held (j:=p) ..)
  let p : Active L x M:=⟨j,hp⟩; let r:= Locations.active s t A F x p
  let A0:=replica S.ratio V; let C:=A0 f
  have hU : U f=G.lieExp (a r)* C := hu.trans (freeze_regular (j:=r) ..)
  have hV : U' i=G.lieExp (tape (e z) p)*replica S.ratio V' i := hv.trans (freeze_regular (j:=p) ..)
  have ht' : tape (e z) p = fiber s t V S p.val.val (a r) := move_tape ..
  rw [hV,ht',replica_move, Channels.read_back]; unfold Channels.fiber scatter
  split
  · rename_i he
    change G.lieExp (-G.adjoint C⁻¹ _) * _ = _
    exact (flipped_s _ _ _ hU).symm
  exact hU.symm

-- V before payments. Compare arrays even of *every* theta. Use actual
-- oriented tag & cost data, no assumption from the comparator bit.
lemma fans {Pt : Teller G} (T : Tube G S) (h : Pt.Funds S T) (V : Config G c) (k : S.Choices) (q : Chi) (x d β : ℝ) (Y : RoomView A x F G) :
    gazed T (ticket s t k) q (pull s t V) x β d (cusps A F s t x V Y)=
      pull s (S.ratio.embed t) (gazed T k q V x β d Y) := by
  obtain ⟨c,b,hc,hb⟩:=h.feeds
  let L:=Locations.book s t A; let M:=Locations.forest (S:=S) s t F
  let V':=pull s t V
  let e:=fan A F s t x V; let y:=cusps A F s t x V Y
  let H := portrait T A F k x V .endpoint q d Y.1
  have he : portrait T L M (ticket s t k) x V' .endpoint q d y.1=e H := by
    rw [← mean_endpoint]; unfold e H;rw [← mean_endpoint]
    exact (turned_mean s t V k T x (h.knobs.symm ▸ h.kernel) A F (h.high.symm ▸ hc) q d Y.1).ends
  change photo _ _ (portrait T L M (ticket s t k) x V' .endpoint q d y.1) y.1 y.2=_
  rw [he]; exact circulate A F s t V x (coupling β) Y H

lemma fanMap {T : Tube G S} (k : S.Choices) {Pt : Teller G} (h : Pt.Funds S T) (x : ℝ) (V : Config G c) (he : (palette T A F k x V .endpoint).PosDef) :
    MeasurePreserving (fun y : RoomView A x F G => (cusps A F s t x V y).2) (viewer T A x F k V) (cloud (palette T (book s t A) (Locations.forest s t F) (ticket s t k) x (pull s t V) .endpoint)) := by
  obtain ⟨c,b,hc,hb⟩:=h.feeds
  let B := Locations.book s t A; let F':=Locations.forest s t F
  have ht : palette T B F' (ticket s t k) x (pull s t V) .endpoint=warp (onBond (fiber s t V S))
      (Locations.active s t A F x) (palette T A F k x V .endpoint) := by
    simp_rw [← Q_endpoint]; exact (turned_cov s t V k T x (h.knobs.symm ▸ h.kernel) A F (h.high.symm ▸ hc)).fog
  change MeasurePreserving _ _ (cloud (palette T B F' (ticket s t k) x (pull s t V) .endpoint))
  rw [ht]
  exact (warp_cloud _ _ _ he).comp measurePreserving_snd

-- radial guards on the native Room
lemma pepWeight (x : ℝ) (V : Config G c) (j : Site f) (w : ℕ) (Z : Gaussian.Vec (In x A F (G:=G))) (p : ℝ) :
    Guards (Room (affine s (S.ratio.embed t) j) w) Z p → Guards (Room j w) (fan A F s t x V Z) p := by
  intro h i
  let a:=Locations.active s t A F x; let y:= affine s (S.ratio.embed t); let v:=i.val.val.val
  have hp : pinPos v ⊆ Spindle.patch w j := by
    intro k hk
    have he := (Finset.mem_filter.mp i.2).2
    rcases Finset.mem_insert.mp hk with hz|hz; subst k;exact he.1;rw [Finset.mem_singleton.mp hz];exact he.2
  have ht (z) (hz : z∈pinPos (a i.val).val.val) : z∈Spindle.patch w (y j):= by
    rw [show (a i.val).val.val = sendEdge s (S.ratio.embed t) v from rfl,Locations.pin_map] at hz
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hz
    exact (Spindle.doors _).2 ((Thirst.s_sep ..).trans_le ((Spindle.doors _).1 (hp hb)))
  have H : (a i.val).val.val∈ Room (y j) w:= mem_filter.mpr ⟨mem_univ _,ht _ (by simp [pinPos]),ht _ (by simp [pinPos])⟩
  rw [fan,move_tape,LinearIsometry.norm_map]
  exact h ⟨a i.val,H⟩

lemma winding (x β d : ℝ) (V : Config G c) {Pt : Teller G} (T : Tube G S) (h : Pt.Funds S T) (f : Site c→G.El)
    (k : S.Choices) (q : Chi) (Y : RoomView A x F G) (hP : (palette T A F k x (Lattice.gauge f V) .endpoint).PosDef) :
    Lattice.gauge (constantGauge f S.ratio) (gazed T k q V x β d Y) =
      gazed T k q (Lattice.gauge f V) x β d (A:=A) (F:=F) (sendFrozen S f x A F Y.1, toGauge f A F x *ᵥ Y.2) := by
  unfold gazed
  rw [show portrait T A F k x (Lattice.gauge f V) _ _ _ _ = _ from (turned_law f A F x Pt T V k _ Y.1 q d h hP).1]
  exact (turning_photo ..).symm
end turned
end YM.PhysicalNext.InteractingRank
