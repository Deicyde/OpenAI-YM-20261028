import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.ColumnL

/-! # Natural rotor in each gauge, change inputs by *shared* Y,z. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Hues
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll  
open  Ursell Trees    Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {L : Side}

def pairs (_X : Coat T F) (z : Site c→G.El) : F.Slice G≃ᵐ F.Slice G :=
  let w := constantGauge z S.ratio
  MeasurableEquiv.piCongrRight (fun (p:F.Free)=> ((MeasurableEquiv.mulLeft (w p.val.1)).trans
      (MeasurableEquiv.mulRight (w (p.val.1+step p.val.2))⁻¹)))
def sluice (X : Coat T F) (z : Site c→G.El) : Coat T F := (X.rinse z).wrapY (pairs X z X.Y)

lemma drinking (X : Coat T F) (z : Site c → G.El) : MeasurePreserving (pairs X z) (F.order G) (F.order G) := by
  let w:= constantGauge z S.ratio
  exact measurePreserving_pi _ _ (fun p:F.Free=> (measurePreserving_mul_right G.probHaar (w (p.val.1+step p.val.2))⁻¹).comp
    (measurePreserving_mul_left G.probHaar (w p.val.1)))
lemma liquid (X : Coat T F) (z : Site c→ G.El) (a : F.Slice G) :
    F.drape (pairs X z a)=gauge (constantGauge z S.ratio) (F.drape a) := by
  let w:= constantGauge z S.ratio; funext i
  by_cases he : i ∈ F.trunks
  · have ht : w (i.1+step i.2)=w i.1 := congr_arg z (F.trunk_internal (by simpa using he))
    unfold w at ht; unfold Lattice.gauge; rw [show F.drape (pairs X z a) i=1 from F.on_tree _ ⟨i,he⟩,show F.drape a i=1 from F.on_tree _ ⟨i,he⟩,ht,mul_one,mul_inv_cancel]
  unfold Lattice.gauge; rw [F.off_tree (pairs X z a) ⟨i,he⟩,F.off_tree a ⟨i,he⟩]; rfl
lemma banks (X : Coat T F) (z : Site c → G.El) (u : Directions G f) :
    (sluice X z).input (spinRow S z u)= gauge (constantGauge z S.ratio) (X.input u) := by
  let k:= constantGauge z S.ratio
  have hp : (sluice X z).view (spinRow S z u)=pairs X z (X.view u) := by
    funext i
    by_cases h : X.Hot i.val
    · rw [view, if_pos (show (sluice X z).Hot i.val from h)]
      change G.lieExp (G.adjoint (k i.val.1) (u i.val)) * replica S.ratio (gauge z X.V) i.val = _ * X.view u i * _
      rw [view, if_pos h, increment,← copied S.ratio S.patch.odd_side,Channel.exp_adjoint]; change _= k i.val.1 *_ *(k _)⁻¹
      unfold Lattice.gauge; unfold k; group
    rw [view, if_neg (show ¬ (sluice X z).Hot i.val from h)]
    change _ = k i.val.1* (X.view u i)* (k _)⁻¹; rw [view, if_neg h]; rfl
  unfold input; rw [hp,liquid]
lemma pockets (X : Coat T F) (h : ShellAccess S G X.x W X.width C) (z : Site c→ G.El)
    (u : Directions G f) : (sluice X z).signal (spinRow S z u)=spinRow S z (X.signal u) := by
  let k:= constantGauge z S.ratio
  have hp : (sluice X z).saved=spinRow S z X.saved := by
    funext i; unfold saved spinRow
    split
    next ht => dsimp only; rw [if_pos (show i∈F.trunks ∨ X.Hot i from ht),map_zero]
    next ht =>
      dsimp only; rw [if_neg (show ¬(i∈F.trunks ∨ X.Hot i) from ht)]
      let U := F.drape X.Y; let V:= replica S.ratio X.V
      have hg : (F.drape (pairs X z X.Y)) i*(replica S.ratio (gauge z X.V) i)⁻¹=k i.1*(U i*(V i)⁻¹)*(k i.1)⁻¹ := by
        rw [liquid, ← copied S.ratio S.patch.odd_side]
        unfold k U V Lattice.gauge; group
      unfold small; change cutLog X.χ (X.width*X.t) (F.drape (pairs X z X.Y) i*_) =_
      rw [show (sluice X z).V=gauge z X.V from rfl,hg]; exact h.log.conjugate ..
  unfold Coat.signal; rw [hp];
  change spinRow S z X.saved+X.lens (spinRow S z u)=_
  rw [X.lenses]; funext i; unfold spinRow; simp only [Pi.add_apply,map_add]
lemma springs (X : Coat T F) (ht : P.Funds S T) (h : ShellAccess S G X.x W X.width C) (z : Site c→ G.El)
    (u : Directions G f) (s : Signed) (p : Rod c f) :
    (sluice X z).realPath s p (spinRow S z u)= G.adjoint (z (s.act (focus S p))) (X.realPath s p u) := by
  obtain ⟨_,_,H,-⟩:=ht.feeds
  let k : Site c→ G.El:= fun j=> z (s.act j)
  have he : pull s 0 (gauge z X.V)=gauge k (pull s 0 X.V) := by rw [Work.F05.pull_gauge_zero]; simp [k]
  unfold realPath; rw [pockets X h z u, map_add]
  change request T X.x (choice s X.k) (pull s 0 (gauge z X.V)) p + orientedRow _ X.R _ _ (gauge z X.V) _=_
  rw [he,oriented_under T H]; unfold request baseStroke; rw [map_sub, ← copied S.ratio S.patch.odd_side, entry_turn ht, guide_gauge ht]
end YM.ConnectedActivityE6.Hues
