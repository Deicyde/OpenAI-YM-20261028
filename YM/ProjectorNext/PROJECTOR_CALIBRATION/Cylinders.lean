import YM.ProjectorNext.PROJECTOR_CALIBRATION.Colors
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Empirical
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Telescope


/-! # Actual equation stencils on cover and regulator

`valve` multiplies each energy derivative; it doesn't see β or θ.
Packet will insert the `t_N^{-l}` (l of the column of course) and put
`β_N^{-1}` ONLY on the divergence. Complexify linearly across columns on the
actual frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice Wilson RG Source Source.Drops Function Filter Labels Next.Foundations Push.CutoffProjectors Tensor
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ}

namespace Machine
variable (M : Machine H d)

def estimate (U : CoverConfig G) := M.recover fun i => (M.loops i).eval U

lemma estimate_one : M.estimate (1:CoverConfig G) = 0 := by
  unfold estimate; rw [← map_zero (f:=M.recover)] -- syntax?
  apply congr_arg; funext i; simp [Slot.eval,faceValue,square,travel]

lemma estimate_gauge (U : CoverConfig G) (t : Cover → G.El) : M.estimate (gauge t U) = Cast (t 0) (M.estimate U) := by
  unfold estimate; simp_rw [Slot.eval,travel_gauge,face_gauge,G.curvature_conjugate,G.adjoint_mul]
  have hh (i) (y : G.Color) : G.adjoint (t (stop 0 (M.loops i).walk))⁻¹ (G.adjoint (t ((M.loops i).offset)) y)=y := by rw [← G.adjoint_mul]; simp [Slot.offset]
  simp_rw [hh]
  exact M.intertwine ..

abbrev Outlet := (k : Level d) × ↥((M.filters k).addresses)

/-- Associated positive link. No claim outlets are distinct as links. -/
def address (i : M.Outlet) : Position := i.2.val

/-- Filter a single link sample (already transported to o). -/
def tap (i : M.Outlet) : G.Color →ₗ[ℝ] Snap G d :=
    (firing i.1).comp (((M.filters i.1).Z).comp (LinearMap.single ℝ (fun _ => G.Color) i.2))

def channel (i : M.Outlet) (U : CoverConfig G) (c : G.Color) :=
    M.tap i (G.adjoint (travel U 0 (base (M.address i))) c)

lemma tap_natural (i : M.Outlet) (u : G.El) (c : G.Color) : M.tap i (G.adjoint u c)=Cast u (M.tap i c) := by
  let S := M.filters i.1
  have ht : (LinearMap.single ℝ _ i.2 (G.adjoint u c) : ↥S.addresses → G.Color) = colorAction u (LinearMap.single ℝ _ i.2 c) := by
    funext j; change (Pi.single i.2 (G.adjoint u c) : ↥S.addresses → G.Color) j = G.adjoint u ((Pi.single i.2 c : ↥S.addresses → G.Color) j)
    by_cases h : j=i.2 <;> simp [h]
  change firing i.1 (S.Z (LinearMap.single ℝ _ i.2 _))= _
  rw [ht,S.color,firing_natural]; rfl

lemma channel_gauge (i : M.Outlet) (c : G.Color) (U : CoverConfig G) (t : Cover → G.El) :
    M.channel i (gauge t U) (G.adjoint (t (M.address i).1) c)=Cast (t 0) (M.channel i U c) := by
  simp_rw [channel, travel_gauge,route_end,G.adjoint_mul, ← G.adjoint_mul ((t _)⁻¹) (t _), inv_mul_cancel,G.adjoint_one,tap_natural]

variable (F : Labels.Frame G d)

abbrev shade (m : F.Index) := palette (F.grades m).2 (F.basis m)

def valveL (m : F.Index) (i : M.Outlet) (U : CoverConfig G) : G.Color →ₗ[ℝ] ℂ :=
    (Cross.mix (shade F m) M.U (M.estimate U)).toLinearMap.comp
      ((M.tap i).comp (G.adjoint (travel U 0 (base (M.address i)))))

def valve (m : F.Index) (i : M.Outlet) (c : G.Color) (U : CoverConfig G) :=
    Cross.mix (shade F m) M.U (M.estimate U) (M.channel i U c)

lemma valveL_apply (m : F.Index) (i : M.Outlet) (c : G.Color) (U : CoverConfig G) :
    M.valveL F m i U c = M.valve F m i c U := rfl

lemma valve_gauge (m : F.Index) (i : M.Outlet) (c : G.Color) (U : CoverConfig G) (t : Cover → G.El) :
    M.valve F m i (G.adjoint (t (M.address i).1) c) (gauge t U)=M.valve F m i c U := by
  unfold valve; rw [estimate_gauge,channel_gauge]
  trans (1:ℝ) • Cross.mix (shade F m) M.U (M.estimate U) (M.channel i U c)
  · refine Cross.scaled_mix (shade F m) M.U (castAction (t 0) (d:=d)) _ ?_ ?_ _ _
    · intro x; rw [one_smul]; exact painting (F.grades m).2 (F.pure m) (t 0) x
    intro x; exact M.toSplit.comm ..
  exact one_smul ..

lemma small_estimate : Small G M.estimate :=
    (Small.vector (fun i => (M.loops i).eval) fun _ => Small.slot _).linear M.recover.toContinuousLinearMap

lemma small_channel (i : M.Outlet) (c : G.Color) : Small G (fun U => M.channel i U c) :=
    (Small.adjoint (T:=fun U => travel U _ _) (Small.path ..) (Small.constant c)).linear (M.tap i).toContinuousLinearMap

lemma small_valve (m : F.Index) (i : M.Outlet) (c : G.Color) : Small G (M.valve F m i c) :=
    (M.small_estimate).two (M.small_channel i c) (fun x y => Cross.mix (shade F m) M.U x y)
      (contDiff_iff_contDiffAt.mpr fun _ => Cross.mix_smooth _ _ contDiffAt_fst contDiffAt_snd)

/-- Deploy the coefficients on the torus, ignoring remainders and chains.
For chains to use these, they must really have these weights. Allow collisions
at tight sizes: add the functions on that physical link. -/
def port {n : Side} (o : Site n) (i : M.Outlet) : Edge (Site n) := (wrap n (M.address i).1+o,(M.address i).2)

def feed {n : Side} (o : Site n) (m : F.Index) : Vectors G n := fun U e j =>
    ∑ i : M.Outlet, if e=M.port o i then M.valve F m i (colors G j) (expandAt o U) else 0

def weights {n : Side} (o : Site n) : F.Coeff →ₗ[ℂ] Vectors G n :=
    ∑ i : F.Index, LinearMap.toSpanSingleton ℂ _ (M.feed F o i) ∘ₗ (LinearMap.proj i)

lemma weights_eval {n : Side} (o : Site n) (x : F.Coeff) (U : Config G n) (e : Edge (Site n)) (j : G.ColorIndex) :
    M.weights F o x U e j = ∑ i : F.Index, ∑ w : M.Outlet,
      if e=M.port o w then x i*M.valve F i w (colors G j) (expandAt o U) else 0 := by
  unfold weights
  rw [LinearMap.sum_apply]
  simp [Finset.sum_apply,feed,Finset.mul_sum,mul_ite]

end Machine
end YM.ProjectorNext.Calibration
