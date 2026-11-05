import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Affine
import YM.Next.SCHEDULE.GridCost
import YM.Next.SCHEDULE.Postal
import YM.Next.SCHEDULE.Stadium

/-!
# Apply the array to true Lie coordinates

All truncations by the toll cutoff. No ghost diagonal. Under the supported
`Feeds` justify each row on the charts; never infer a kernel identity for
some separate predictions by just specifying their tangent columns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Matrix Lattice RG Wilson Pressure Pressure.Stores Precision Tree Exterior
open Turn Push.SectorMeasure Push.SectorMeasure.Oriented Work.F03
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

def curl (p : Cell n) (x : Directions G n) := faceCurl p (form x)

def chain (x : Directions G n) (p : Cell n) : G.Color := x (p.1+Lattice.step p.2.val.1,p.2.val.2) -
  x (p.1,p.2.val.2) - (x (p.1+Lattice.step p.2.val.2,p.2.val.1)-x (p.1,p.2.val.1))

lemma curl_chain (p : Cell n) (x : Directions G n) : curl p x = chain x p := by
  ext i; unfold curl chain faceCurl dColor
  simp only [PiLp.sub_apply, Exterior.d_plaquettes]
  unfold parts Aff.form; dsimp only; simp only [show ∀ u : Axis, axisEquiv.symm (Exterior.coord u)=u from
    fun u => axisEquiv.symm_apply_apply u]

lemma curl_add (p : Cell n) (x y : Directions G n) : curl p (x+y)=curl p x+curl p y := by
  simp only [curl_chain,chain,Pi.add_apply]; abel

lemma curl_smul (p : Cell n) (r : ℝ) (x : Directions G n) : curl p (r • x) = r • curl p x := by
  simp only [curl_chain,chain,Pi.smul_apply,smul_sub]

def bandTerm (T : Tube G S) (R : ℕ) (i : Cell f) (l : ℕ) (x : Directions G f) :=
    if (T.up.row i.2 l).2.length ≤ R then
      (T.up.row i.2 l).1 • curl (slotFace (T.up.row i.2 l).2 i.1) x else 0

lemma bandTerm_add (T : Tube G S) (R : ℕ) (i : Cell f) (l : ℕ) (x y : Directions G f) :
    bandTerm T R i l (x+y) = bandTerm T R i l x + bandTerm T R i l y := by
  unfold bandTerm; split <;> simp [*,curl_add]

lemma bandTerm_smul (T : Tube G S) (R : ℕ) (i : Cell f) (l : ℕ) (r : ℝ) (x : Directions G f) :
    bandTerm T R i l (r • x) = r • bandTerm T R i l x := by
  unfold bandTerm; split
  next h => rw [curl_smul,smul_comm]
  next h => rw [smul_zero]

lemma band_summable {P : Teller G} {T : Tube G S} (h : P.Funds S T) (R : ℕ) (i : Cell f) (x : Directions G f) :
    Summable fun l => bandTerm T R i l x := by
  obtain ⟨B,C,hB,hC⟩ := h.feeds
  have hh := ellLine_summable T.up hB i (form x)
  have hs := hh.indicator {l | (T.up.row i.2 l).2.length ≤ R}
  convert hs using 1 <;> first | rfl | (funext l; simp only [bandTerm, Set.indicator]; split <;> simp [*,curl])

section booked
variable (x : ℝ) (p : Pos S) (V : Config G c) {P : Teller G} {T : Tube G S} (h : P.Funds S T)

include h in
lemma level_add (R : ℕ) (i : Twin f) (z a : Directions G f) : level T R i (z+a) = level T R i z + level T R i a := by
  unfold level; split
  next e =>
    change (∑' j,bandTerm T R i.1 j (z+a)) = (∑' j,bandTerm T R i.1 j z) + ∑' j,bandTerm T R i.1 j a
    simp only [bandTerm_add]; exact (band_summable h ..).tsum_add (band_summable h ..)
  next e =>
    change Real.sqrt T.high.direct • curl i.1 (z+a) = _
    rw [curl_add, smul_add]; rfl

lemma level_smul (R : ℕ) (i : Twin f) (r : ℝ) (z : Directions G f) : level T R i (r • z) = r • level T R i z := by
  unfold level; split
  next e => change (∑' j,bandTerm T R i.1 j (r • z))=r • ∑' j,bandTerm T R i.1 j z
            simp_rw [bandTerm_smul]; rw [tsum_const_smul'']
  next e => change Real.sqrt T.high.direct • curl i.1 (r • z) = r • (Real.sqrt T.high.direct • curl i.1 z)
            rw [curl_smul,smul_comm]

lemma untwine_add (z a : Directions G f) : untwine S p V (z+a)=untwine S p V z+untwine S p V a := by
  funext i; simp [untwine,rotateG]

lemma untwine_smul (r : ℝ) (z : Directions G f) : untwine S p V (r • z)=r • untwine S p V z := by
  funext i; simp [untwine,rotateG]

/-- Array linear functional. Can be shown assuming only the path receipt;
uses `P.Funds` since every call later has it. -/
def elongate (p : Pos S) (h : P.Funds S T) : Directions G f →ₗ[ℝ] G.Color where
  toFun := fun a => derivative T (till x) p V a
  map_add' a b := by
    rcases p with ⟨s,i|i⟩
    · unfold derivative; dsimp only [Sum.elim_inl]; rw [untwine_add, level_add h]
    unfold derivative Next.Fluctuations.zLin; dsimp only [Sum.elim_inr]; rw [untwine_add]
    let u := untwine S (s,.inr i) V a; let v := untwine S (s,.inr i) V b
    have he j : parts G 1 (form (u+v)) j = parts G 1 (form u) j + parts G 1 (form v) j := rfl
    -- basis entry in a real counting matrix
    ext j
    simp only [PiLp.add_apply,PiLp.smul_apply, PiLp.sub_apply, Pi.zero_apply,PiLp.zero_apply,
      ← show u=untwine S (s,.inr i) V a from rfl, ← show v=untwine S (s,.inr i) V b from rfl, he,
      Matrix.mulVec_add, Pi.add_apply]
    simp [smul_eq_mul]; ring
  map_smul' r a := by
    rcases p with ⟨s,i|i⟩
    · unfold derivative; dsimp only [Sum.elim_inl]; rw [untwine_smul, level_smul]; rfl
    unfold derivative Next.Fluctuations.zLin; dsimp only [Sum.elim_inr]; rw [untwine_smul]
    let u := untwine S (s,.inr i) V a
    have he j : parts G 1 (form (r • u)) j = r • parts G 1 (form u) j := rfl
    ext j
    simp only [PiLp.smul_apply,PiLp.sub_apply, Pi.zero_apply,PiLp.zero_apply,
      ← show u=untwine S (s,.inr i) V a from rfl, he, Matrix.mulVec_smul,Pi.smul_apply]
    simp [smul_eq_mul]; ring

include h in
lemma as_applied (a : ArrayR G f) (i : Ix G S) :
    (scale T x V *ᵥ a) i = Real.sqrt weight * derivative T (till x) i.1 V (lie a) i.2 := by
  let L : ArrayR G f →ₗ[ℝ] Directions G f := { toFun := lie, map_add' _ _ := rfl,map_smul' _ _ := rfl }
  let W := (LinearMap.proj (R:=ℝ) i.2).comp (WithLp.linearEquiv 2 ℝ (G.ColorIndex→ℝ)).toLinearMap
  let K : ArrayR G f →ₗ[ℝ] ℝ := Real.sqrt weight • W.comp ((elongate x V i.1 h).comp L)
  change (∑ j, K (Pi.single j 1)* a j) = K a
  have hp : ∑ j,a j • (Pi.single j 1 : ArrayR G f)=a := by
    funext z
    rw [Finset.sum_apply]; simp [Pi.single_apply]
  calc
    _ = ∑ j, K (a j • (Pi.single j 1 : ArrayR G f)) := Finset.sum_congr rfl fun j _ => by rw [map_smul,mul_comm]; rfl
    _ = _ := by rw [← map_sum,hp]
end booked
end YM.AnalyticNext.ConnectedActivity.Aff
