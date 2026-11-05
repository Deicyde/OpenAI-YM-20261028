import YM.ProjectorNext.PROJECTOR_CALIBRATION.Cylinders

/-! # Evaluate the finite equation cylinders unwrapped -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice Wilson RG Source Source.Drops Function Filter Labels Next.Foundations Push.CutoffProjectors Tensor
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ}
namespace Machine
variable (M : Machine H d) (F : Labels.Frame G d)

/-- all needed empirical reads on one fixed stencil. Also require both endpoints
of each valve link. θ and β and chain statuses do NOT enter this receipt. -/
structure Release (s : Finset Cover) : Prop where
  anchor : 0∈s
  start (i : M.Outlet) : (M.address i).1 ∈ s
  finish (i : M.Outlet) : (M.address i).1+step (M.address i).2∈s
  takes : Empirical s M.estimate
  routes (i : M.Outlet) (j : G.ColorIndex) : Empirical s (fun U => M.channel i U (colors G j))
  force (i : M.Outlet) : Empirical (G:=G) s (fun U => gradient U (M.address i).1 (M.address i).2)

lemma releases : ∃ s, M.Release s := by
  classical
  obtain ⟨K,hK⟩ := M.small_estimate
  -- don't use choose tactic when index possibly empty (functions from empty type still exist)
  let a (i : M.Outlet) (j : G.ColorIndex) := Exists.choose (M.small_channel i (colors G j))
  have ha (i : M.Outlet) (j : G.ColorIndex) : Empirical (a i j) _ := Exists.choose_spec (M.small_channel i (colors G j))
  let b (i : M.Outlet) := Exists.choose (Small.gradient (G:=G) (M.address i).1 (M.address i).2)
  have hb (i : M.Outlet) : Empirical (b i) _ := Exists.choose_spec (Small.gradient (G:=G) (M.address i).1 (M.address i).2)
  let c (i : M.Outlet) := insert (M.address i).1 (insert ((M.address i).1 + step (M.address i).2) (b i ∪ Finset.univ.biUnion (a i)))
  let S := insert 0 (K ∪ Finset.univ.biUnion c)
  have he (i : M.Outlet) : c i ⊆ S := fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_right K (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hx⟩))
  exact ⟨S,by simp [S],fun i => he i (by simp [c]),fun i => he i (by simp [c]),
    hK.enlarge (fun x hx => by simp [S,hx]),fun i j => (ha i j).enlarge (fun x hx => he i (by simp [c]; exact Or.inr (Or.inr (Or.inr ⟨j,hx⟩)))),
    fun i => (hb i).enlarge (fun x hx => he i (by simp [c,hx]))⟩

/-- A choice independent of torus. -/
def curtain := M.releases.choose
lemma served : M.Release M.curtain := M.releases.choose_spec

lemma released (i : M.Outlet) (m : F.Index) (j : G.ColorIndex) (s : Finset Cover) (h : M.Release s) :
    Empirical s (M.valve F m i (colors G j)) := (h.takes.pair (h.routes i j)).comp
      (L:=fun p => Cross.mix (shade F m) M.U p.1 p.2)
      (contDiff_iff_contDiffAt.mpr fun _ => Cross.mix_smooth _ _ contDiffAt_fst contDiffAt_snd)

/-- Equation split at fixed D and field basis slot, without the various
normalization scalars. -/
def energyLeg (m : F.Index) (U : CoverConfig G) :=
    ∑ i : M.Outlet, M.valve F m i (gradient U (M.address i).1 (M.address i).2) U

def divLeg (m : F.Index) (U : CoverConfig G) := ∑ i : M.Outlet, ∑ j : G.ColorIndex,
    left (M.valve F m i (colors G j)) (M.address i) (colors G j) U

lemma energyContract (U : CoverConfig G) (i : M.Outlet) (m : F.Index) :
    ∑ j : G.ColorIndex, M.valve F m i (colors G j) U *
      (↑(inner ℝ (colors G j) (gradient U (M.address i).1 (M.address i).2)) : ℂ) =
      M.valve F m i (gradient U (M.address i).1 (M.address i).2) U := by
  let L := M.valveL F m i U
  let y := gradient U (M.address i).1 (M.address i).2
  have h := congr_arg L ((colors G).sum_repr' y)
  rw [_root_.map_sum] at h
  simp_rw [map_smul, Complex.real_smul] at h
  simp_rw [mul_comm (M.valve ..) _]
  exact h

variable {n : Side}
/- Use on a period where stencil fits. -/
def Opened (s : Finset Cover) (n : Side) := Set.InjOn (wrap n) (s : Set Cover)

lemma opened (s : Finset Cover) (hn : ∀ x∈s, ∀ i : Axis, 20*((x i).natAbs+1) ≤ n.val) : Opened s n := by
  refine (wrap_injOn n).mono ?_
  intro x hx; change ∀ i, _ < _ ∧ _ ≤ _
  intro i; have := hn x hx i; omega

lemma Lifted (s : Finset Cover) (hn : ∀ x∈s, ∀ i : Axis, 20*((x i).natAbs+1) ≤ n.val) {x : Cover} (hx : x∈s) : lift (wrap n x) = x := by
  refine lift_eq_iff.mpr ⟨rfl,fun i => ?_⟩
  have := hn x hx i; omega

lemma nonwrap (s : Finset Cover) (hn : ∀ x∈s, ∀ i : Axis, 20*((x i).natAbs+1) ≤ n.val) :
    Nonwrapping (Packet.sites n s) 0 := by
  rintro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  simp only [separation, sub_zero,pdist,Lifted s hn hy]
  have hp := n.property
  have he : (Finset.univ.sup fun i : Axis => (y i).natAbs) ≤ (n.val-1)/10 := by
    refine Finset.sup_le fun i _ => ?_
    have := hn y hy i; omega
  exact (Nat.mul_le_mul_left 10 he).trans_lt ((mul_comm 10 _ ▸ Nat.div_mul_le_self (n.val-1) 10).trans_lt (Nat.sub_lt hp (by decide)))

theorem fitsTest {K : Type*} (s : Finset Cover) (f : CoverConfig G → K) (h : LocalOn s f)
    (hn : ∀ x∈s, ∀ i : Axis, 20*((x i).natAbs+1) ≤ n.val)
    (o : Site n) (H : Hol G) (d : ℕ) (J : Jet G) (t : ℝ) :
    f (expandAt o (H.testLinks d o J t))= f (H.links d J t) := by
  apply h; intro e he _
  unfold expandAt Hol.testLinks; rw [add_sub_cancel_right,Lifted s hn he]

set_option maxHeartbeats 400000 in
lemma matched_increment {K : Type*} {s : Finset Cover} (f : CoverConfig G → K) (h : LocalOn s f) 
    (hn : Opened s n) (o : Site n) (U : Config G n) (e : Edge Cover) (he : e.1∈s) (c : G.Color) (t : ℝ) :
    f (expandAt o (increment U (t • oneEdge ((wrap n e.1+o,e.2)) c))) =
      f (pushLink (expandAt o U) (Pi.single e c) t) := by
  apply h; intro i hi _
  let j : Edge (Site n) := (wrap n i.1+o,i.2)
  have hk : j=(wrap n e.1+o,e.2) ↔ i=e := by
    refine ⟨fun h => Prod.ext (hn hi he ?_) ((congr_arg Prod.snd h : j.2 = ((wrap n e.1+o,e.2):Edge _).2)), fun h => by simp [h,j]⟩
    exact add_right_cancel (congr_arg Prod.fst h : wrap n i.1+o = _)
  have ht : (Pi.single (wrap n e.1+o,e.2) c : Edge (Site n) → G.Color) j = (Pi.single e c : Edge Cover → G.Color) i := by
    by_cases hv : i=e
    · simp [hk.mpr hv, hv]
    simp [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne (mt hk.mp hv)]
  change G.lieExp (t • ((Pi.single ((wrap n e.1+o,e.2)) c : Edge (Site n) → G.Color) j)) * U j = G.lieExp (t • ((Pi.single e c : Edge Cover → G.Color) i)) * U j
  rw [ht]

/- For the actual Packet normalization: equation parameters are graded in
F; scaling is threshold^{slot}, before coefficients enter the valves. -/
def lined {C : Family G} (M : Machine C.params d) {N p} (E : Packet C d N p) :=
    E.weights = (M.weights (C.labels.level d) 0).comp (equationSpace (C.labels.level d)).subtype

lemma threaded {C : Family G} (M : Machine C.params d) {N p} (E : Packet C d N p) (h : M.lined E)
    (x : equationSpace (C.labels.level d)) :
    E.X x = M.weights (C.labels.level d) (0 : Site (C.side N p)) ((C.labels.level d).scaled (C.path.levels.clock.threshold N)⁻¹ x.val) := by rw [Packet.X,h]; rfl

end Machine
end YM.ProjectorNext.Calibration
