import YM.Pert.Lattice.Difference
/-! Exact lattice tensor convention by hypercubic averaging of radial letters. -/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace YM.Pert.Bare
open Lattice Function Filter Orb
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

def motionLink (s : Signed) (l : Orb.Links n) := ((posDir l.2).rotate s).used (affine s 0 l.1)
lemma motion_image (s : Signed) (l : Orb.Links n) : motionLink s (Orb.image l) = Orb.image (motionLink s l) := by
  have hv := (posDir l.2).vec_rotate (R:=Per n) s
  rw [Step.vec_pos] at hv
  cases h : ((posDir l.2).rotate s).neg <;> simp_all [motionLink,Orb.image,Step.used,Step.vec,affine] <;> abel
  rw [← hv]; abel

def parity (s : Signed) (l : Orb.Links n) : ℝ := if ((posDir l.2).rotate s).neg then -1 else 1
def rotation (s : Signed) : Potential G n →ₗ[ℝ] Potential G n :=
  LinearMap.codRestrict (LinkP G n)
    (LinearMap.pi (fun l => parity s l • takeLink (motionLink s l)))
    (fun a l => by
      change parity s (Orb.image l) • a.val (motionLink s (Orb.image l))= -(parity s l • a.val (motionLink s l))
      rw [motion_image,a.property, smul_neg]; rfl)
lemma rotation_links (s : Signed) (a : Potential G n) : positiveLinks (rotation s a)=pull s 0 (positiveLinks a) := by
  funext l
  change G.lieExp (parity s l • a.val (motionLink s l)) = _
  cases e : ((posDir l.2).rotate s).neg <;> simp [pull, Step.read,e,parity, positiveLinks,motionLink,Work.F03.exp_neg_color]

section family
variable {R : Type*} [AddCommGroup R] [One R]
lemma switch_base (s : Signed) (U : Lattice.Links R G.El) (t : Four R → G.El) : pull s 0 (gauge t U) = gauge (t ∘ affine s 0) (pull s 0 U) := by funext l; simp [pull,Lattice.gauge,Step.gauge_read, comp_def,Step.vec_rotate,affine]
def oval (s : Signed) (h : ℝ) (U : Lattice.Links R G.El) (x : Four R) (j : ℕ) : Labels.Taylor G j :=
  Labels.Taylor.turn s.ortho (rawJet h (pull s 0 U) (affine s⁻¹ 0 x) j)
lemma lattice_oval (t q : Signed) (h : ℝ) (U : Lattice.Links R G.El) (x : Four R) (j : ℕ) :
     oval (t⁻¹ * q) h (pull t 0 U) x j = Labels.Taylor.turn t⁻¹.ortho (oval q h U (affine t 0 x) j) := by
  have he : (t⁻¹*q).ortho=t⁻¹.ortho*q.ortho := Signed.inclusionO.map_mul ..
  unfold oval; rw [pull_pull,he,Labels.Taylor.turn_mul]
  simp [affine,Signed.act_mul,mul_inv_rev]
lemma gauge_oval (t : Signed) (s : Four R → G.El) (h : ℝ) (U : Lattice.Links R G.El) (x : Four R) (j : ℕ) :
     oval t h (gauge s U) x j = Labels.Taylor.paint (s x) (oval t h U x j) := by simp [oval,switch_base,rawJet_gauge,Labels.Taylor.turn_paint,affine]

def tensorJet (h : ℝ) (U : Lattice.Links R G.El) (x : Four R) (j : ℕ) := (Fintype.card Signed : ℝ)⁻¹ • ∑ s : Signed, oval s h U x j
lemma tensor_gauge (s : Four R→G.El) (h : ℝ) (U : Lattice.Links R G.El) (x : Four R) (j : ℕ) : tensorJet h (gauge s U) x j = Labels.Taylor.paint (s x) (tensorJet h U x j) := by simp [tensorJet,gauge_oval]
lemma tensor_move (t : Signed) (h : ℝ) (U : Lattice.Links R G.El) (x : Four R) (j : ℕ) : tensorJet h (pull t 0 U) x j = Labels.Taylor.turn t⁻¹.ortho (tensorJet h U (affine t 0 x) j) := by
  unfold tensorJet; rw [map_smul,map_sum,← Equiv.sum_comp (Equiv.mulLeft t⁻¹) (fun s => oval s h (pull t 0 U) x j)]; congr 1
  simp only [← lattice_oval]; rfl
end family

@[simp] lemma tensor_flat (h : ℝ) (x : Site n) (j : ℕ) : tensorJet h (positiveLinks (0:Potential G n)) x j = 0 := by
  simp [tensorJet,oval,← rotation_links, rawJet_zero]
set_option maxHeartbeats 180000 in
lemma tensor_diff (h : ℝ) (x : Site n) (j : ℕ) : ContDiffAt ℝ ω (fun v : Potential G n => tensorJet h (positiveLinks v) x j) 0 := by
  have hs (s : Signed) : ContDiffAt ℝ ω (fun v : Potential G n => oval s h (positiveLinks v) x j) 0 := by
    simp_rw [oval,← rotation_links]
    let u := (Labels.Taylor.turn (G:=G) (j:=j) s.ortho).toContinuousLinearMap
    have ht := rawJet_smooth (G:=G) (j:=j) h (affine s⁻¹ 0 x)
    let rotate := (rotation (G:=G) (n:=n) s).toContinuousLinearMap
    rw [show (0:Potential G n) = rotate 0 from rotate.map_zero.symm] at ht
    exact (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Labels.Taylor G j) (F:=Labels.Taylor G j) u).contDiffAt.comp (0:Potential G n) (ht.comp (0:Potential G n) rotate.contDiff.contDiffAt)
  have hc := ContDiffAt.sum (s:=Finset.univ) (f:=fun s v=>oval s h (positiveLinks v) x j) (fun s _ => hs s)
  have H := ContDiffAt.const_smul (((Fintype.card Signed):ℝ)⁻¹) hc
  unfold tensorJet
  exact H
end YM.Pert.Bare
