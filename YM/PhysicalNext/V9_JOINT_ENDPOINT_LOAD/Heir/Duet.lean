import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Gondola
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Recite
import YM.Planned.ATOM_REGULAR_ESTIMATE.Sampled

/-!
# Actual reads of the principal term on the small and large charts

Seed data/broad placement by `Museum`; on hard-U test sets in *caller*
system (after pre-local authorization of these readings). Chart arguments
on bare and gatherings returned on the ORIGINAL arithmetic sector with fixed
Z even through the entire call. Reorientations may be per edge in `heard`
(global coherent gauge when invoked on a small hull). Derivative assertions
later on the indicated germs, not the literal masked expressions. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Tree Next Next.SectorChange Next.SectorChange.Rows Wisps
    Precision Next.Fluctuations Exterior Bloch Bid AnalyticBridge.LocalGaussianLaws Push.SectorMeasure
    ColorBook AnalyticBridge.SectorAffine.Offset GaugeRoute Matrix
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {p : Site c} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {x : ℝ} {X : Support f} {Y : Support c} {V W : Config G c} {k : S.Choices} {P : Teller G} {T : Tube G S} {q : Chi} {d u : ℝ}
    {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Museum
variable (M : Museum F x A X Y I) (g : Site c→G.El) (t : ℝ)
def extra : Prices G I →L[ℝ] Directions G f := LinearMap.toContinuousLinearMap {
  toFun w i := if h : ∃ j : I,i=M.address j then t • G.adjoint (M.badge g h.choose) (tape w h.choose) else 0
  map_add' a b := by
    funext i; simp only [Pi.add_apply]; split
    next h => change t • (G.adjoint _ (tape a h.choose + tape b h.choose)) = _; rw [map_add,smul_add]
    simp
  map_smul' r a := by
    funext i; simp only [Pi.smul_apply,RingHom.id_apply]; split
    next h => change t • (G.adjoint _ ((r:ℝ) • tape a h.choose)) = _; rw [map_smul,smul_comm t]
    simp }

omit [DecidableEq I] in
lemma extra_size (ht : 0≤t) (w : Prices G I) : ‖M.extra g t w‖ ≤ t*‖tape w‖ := by
  refine (pi_norm_le_iff_of_nonneg (show 0≤t*‖tape w‖ by positivity)).mpr fun i => ?_
  change ‖(if h : ∃ j : I,i=M.address j then t • _ else (0:G.Color))‖ ≤ _; split
  next h => rw [norm_smul_of_nonneg ht,G.norm_adjoint]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (tape w) _) ht
  simp; positivity
omit [DecidableEq I] in
lemma extra_read (i : I) (w : Prices G I) : M.extra g t w (M.address i) = t • G.adjoint (M.badge g i) (tape w i) := by
  have h : ∃ j,M.address i=M.address j := ⟨_,rfl⟩
  change (if h : ∃ j,M.address i=M.address j then _ else _)=_; rw [dif_pos h,M.address_inj h.choose_spec |>.symm]
omit [DecidableEq I] in
lemma extra_tree (w : Prices G I) {i : Bond f} (h : i∈F.trunks) : M.extra g t w i=0 := by
  exact dif_neg (show ¬∃ j,i=M.address j from fun ⟨j,hj⟩ => (M.seat j).val.property (show M.address j∈F.trunks from hj ▸ h))
lemma expand_tree (w : Prices G (clear S x F)) {i : Bond f} (h : i∈F.trunks) : expandBare F x w i=0 := dif_neg (not_not.mpr h)

variable (b : Folio.Bulletin x P T)
include b
lemma heard {i : Bond f} (hi : i.1∈inspected X) (hj : i.1+step i.2∈inspected X) (h : Station Y x p)
    (hr : separation p (S.ratio.parent i.1) ≤ 7*(1+radiusB x)) (sw : Bool) (w : Prices G I) (U : Config G f) {v : Directions G c}
    (hV : AgreeNear id p (reach x) (gauge g V) (increment 1 v)) :
    sounds T F x k sw (v,M.extra g t w) i = gauge (fun i => G.lieExp (φ T F sw v i)) (gauge (g ∘ S.ratio.parent) (M.received k T q d t V U w)) i := by
  let W' := gauge (g ∘ S.ratio.parent) U
  let R := M.received k T q d t (gauge g V) W' (M.toned g *ᵥ w)
  have he := M.received_gauge (k:=k) (u:=t) (d:=d) (q:=q) g b.priced V U w i hi hj
  suffices H : G.lieExp (expandBare F x (forecast T x F k v) i + M.extra g t w i)*G.lieExp (linearCopy S.ratio v i)=R i by
    exact congrArg (fun z => G.lieExp (φ T F sw v i.1)*z*(G.lieExp (φ T F sw v (i.1+step i.2)))⁻¹) (H.trans he)
  by_cases ht : i∈F.trunks
  · simp only [R,received,physical, F.on_tree _ (⟨i,ht⟩:↥F.trunks), M.extra_tree g t w ht,expand_tree _ ht,add_zero,G.mat_lieExp_zero]
    rw [linearCopy,if_pos (F.trunk_internal ht)]; simp
  let a : Active A x F := ⟨⟨i,ht⟩, M.admits hi hj⟩
  obtain ⟨j,Hj⟩ := M.covers a hi hj
  have hv := M.near_forecast (k:=k) (d:=d) (q:=q) b h v hV a hr W'
  have hZ := congr_fun (ascent_read (M.badge g) w) j
  have hm : R i = G.lieExp (M.deposited k T q d t (gauge g V) W' (M.toned g *ᵥ w) a)*replica S.ratio (gauge g V) i := by
    unfold R received physical SectorChange.returned thaw; change F.drape _ a.val.val = _; rw [F.off_tree,freeze_regular]; rfl
  have hq : replica S.ratio (gauge g V) i=replica S.ratio (increment 1 v) i := (Lift.copyAgree _ _ _ _ hV) _ (hr.trans (by unfold reach; omega))
  have hp : replica S.ratio (increment 1 v) i = G.lieExp (linearCopy S.ratio v i) := by
    unfold replica linearCopy; split
    · rw [G.mat_lieExp_zero]
    exact mul_one _
  rw [hm,hq,hp]; apply congrArg (fun y => G.lieExp y*_)
  unfold deposited; rw [hv,← Hj,M.seat.injective.extend_apply]
  rw [show i=M.address j from congrArg (fun j : Active A x F => j.val.val) Hj.symm, M.extra_read]
  exact congrArg (_+t • ·) hZ.symm

lemma unheard {i : Bond f} (hi : i.1∈inspected X) (hj : i.1+step i.2∈inspected X) (h : Station Y x p)
    (hr : separation p (S.ratio.parent i.1) ≤ 7*(1+radiusB x)) (w : Prices G I) (U : Config G f) {v : Directions G c}
    (hV : AgreeNear id p (reach x) (gauge g V) (increment 1 v)) :
    sounds T F x k false (v,M.extra g t w) i = gauge (g ∘ S.ratio.parent) (M.received k T q d t V U w) i := by
  rw [M.heard (d:=d) (q:=q) g t b hi hj h hr false w U hV,Lattice.gauge]; simp [φ]

end Museum
def reply (T : Tube G S) (F : Forest S.ratio) (x : ℝ) (k : S.Choices) (g : Site c→G.El) (i : Bond f) (u : Echo G c f) := G.adjoint ((g (S.ratio.parent i.1))⁻¹) (echo T F x k u i)
variable {r Q : ℝ}
lemma reply_self (g : Site c→G.El) (i : Bond f) (U : Deck G c f) : reply T F x k g i (U,U)=0 := by simp [reply, echo,grounds,decode,touch]

lemma Museum.relative_read (M : Museum F x A X Y I) (g : Site c→G.El) (t : ℝ) (b : Folio.Bulletin x P T) (hT : Act T F x k n r Q)
    {i : Bond f} (hi : i.1∈inspected X) (hj : i.1+step i.2∈inspected X) (h : Museum.Station Y x p)
    (hr : separation p (S.ratio.parent i.1) ≤ 7*(1+radiusB x)) (w w' : Prices G I) (U : Config G f) {v v' : Directions G c}
    (hV : AgreeNear id p (reach x) (gauge g V) (increment 1 v)) (hV' : AgreeNear id p (reach x) (gauge g W) (increment 1 v'))
    (ht : ‖(((v,M.extra g t w),(v',M.extra g t w')):Echo G c f)‖ ≤ r) :
    let Z (w : Prices G I) V := M.received k T q d t V U w
    let a := reply T F x k g i ((v,M.extra g t w),(v',M.extra g t w'))
    Z w V i=G.lieExp a * Z w' W i := by
  intro Z a; have he := congr_fun (hT.visits _ ht) i
  rw [increment,M.unheard (d:=d) (q:=q) g t b hi hj h hr w' U hV', M.unheard (d:=d) (q:=q) g t b hi hj h hr w U hV] at he
  let h := g (S.ratio.parent i.1); let H := g (S.ratio.parent (i.1+step i.2))
  let z := echo T F x k ((v,M.extra g t w),(v',M.extra g t w')) i
  change G.lieExp z*(h*Z w' W i*H⁻¹)=h*Z w V i*H⁻¹ at he
  dsimp only [a,reply]; rw [exp_adjoint]; change Z w V i=(h⁻¹*G.lieExp z*(h⁻¹)⁻¹)*Z w' W i
  calc
    _ = h⁻¹*(h*Z w V i*H⁻¹)*H := by group
    _ = _ := by rw [←he]; group
end YM.PhysicalNext.JointLoad.Heir
