import YM.UVNext.PRICED_KERNELS.MatrixTip
import YM.UVNext.PRICED_KERNELS.Sector
import YM.UVNext.PRICED_KERNELS.TopLinear




set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Wilson top formulas and actual atoms

Install on delta-top (e.g. from Rewired). Addresses identical in linear layout to
Canonical, wind evaluations incl harmonic exact; kernel moving the correction
is also actually on the cover. Solid consumer of Permit for *nonlinear* data
generation: these are suitable Wilson choices in the whole PathInputs top
prices (Arranged in TipBilling), with all corrections seen by the Kin tester.
No positivity or error or continuity estimates on the masked remainder asserted.
Even at top, there will be deeper work in using these resources for vStep
(consumers hold beta etc fixed; assembly incl alter-threshold delay estimates).
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice RG RG.Supply Wilson Precision Craft Exterior Laurent Bloch
open Push.PriceCompiler Work.F03 Work.F08
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

/-- Reusable tensor basis to Atom converter. NOT averages of independent
legs: invariant only as a complete atom. -/
def singleAtom {k : ℕ} (d : G.Color [×k]→L[ℝ] ℝ) (s : PlaqAxes) : Atom G k := ⟨fun _ => Canonical.slot s 0,
    fun t => d fun i => EuclideanSpace.basisFun G.ColorIndex ℝ (t i)⟩

lemma AtomExact {k : ℕ} (d : G.Color [×k]→L[ℝ] ℝ) (s : PlaqAxes) (z : Fin k → G.Color) :
    (singleAtom d s).poly z=d z := by
  let B := EuclideanSpace.basisFun G.ColorIndex ℝ
  have he (x : G.Color) : ∑ i, x i • B i=x := by
    simpa [B,EuclideanSpace.basisFun_repr] using B.sum_repr x
  have hh := d.map_sum (fun i j => z i j • B j)
  simp_rw [he, d.map_smul_univ] at hh
  exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans hh.symm

/-- Finite tip at enumPath plaquette,0 addresses since reusing those Ns anyway. -/
def tipAtom (c : Clip) (k : ℕ) : Atom G 4 :=
    let i := Canonical.enumPath k
    if i.snd=0 then singleAtom (polish G (1-c.direct)) i.fst else dormant G 4

def choice (H : Bed) (c : Clip) : PathData G := { basePath G H with quartic:=tipAtom c }

def few : Finset ℕ := Finset.univ.image fun i : PlaqAxes => Canonical.enumPath.symm (i,0)
lemma mem_few (b : PlaqAxes) : Canonical.enumPath.symm (b,0)∈few := Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩
lemma active_few (i : ℕ) (h : i∉few) (p : Clip) : tipAtom (G:=G) p i=dormant G 4 := by
  refine if_neg fun he => h ?_
  have hh : Canonical.enumPath.symm ((Canonical.enumPath i).1,0)=i := by rw [← he,Prod.mk.eta,Equiv.symm_apply_apply]
  rw [← hh]; exact mem_few _
lemma few_sum {X : Type*} [AddCommMonoid X] (f : ℕ → X) : ∑ i ∈ few,f i = ∑ p : PlaqAxes,f (Canonical.enumPath.symm (p,0)) :=
  Finset.sum_image fun _ _ _ _ he => (Prod.ext_iff.mp (Canonical.enumPath.symm.injective he)).1

/-- Installed cover reader actually evaluates on the local plaquette here,
with exactly one based k(U) in the chosen orientation. -/
lemma center (s : PlaqAxes) (U : Config G n) (x : Site n) : (Canonical.slot s 0).atSite U x = G.curvature (faceValue U (x,s)) := by
  rw [atSite_path]
  have he : (Canonical.slot s 0).walk=[] := by simp [Canonical.slot, route,axisRoute,straight]
  rw [he]; change G.adjoint 1 _ = _; rw [G.adjoint_one]
  unfold slotFace; rw [Canonical.endSlot]; simp [Canonical.slot]

lemma tipExact (p : Clip) (U : Config G n) (x : Site n) :
    ∑' k : ℕ, (tipAtom p k).unmasked U x = ∑ s : PlaqAxes, homog (polish G (1-p.direct)) (G.curvature (faceValue U (x,s))) := by
  have hh (i : ℕ) (h : i∉few) : (tipAtom p i).unmasked U x=0 := by rw [active_few _ h]; simp [Atom.unmasked,dormant,Atom.poly]
  rw [tsum_eq_sum hh, few_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [tipAtom,Equiv.apply_symm_apply,if_true,Atom.unmasked,show ∀ c q, (singleAtom (polish G c) q).leg = fun _ => Canonical.slot q 0 from fun _ _ => rfl,center]
  rw [AtomExact]; rfl

lemma center_service {H : Bed} (p : Clip) (U : Config G n) (x : Site n) (b : PlaqAxes) (hr : H.roots=delta p) :
    (choice H p).ell U (x,b) = Real.sqrt (1-p.direct) • G.curvature (faceValue U (x,b)) := by
  classical
  unfold PathData.ell
  let j := Canonical.enumPath.symm (b,0)
  have hu (k : ℕ) (h : k≠j) : (choice H p).ellTerms (x,b) k U=0 := by
    unfold PathData.ellTerms
    have he : ((choice (G:=G) H p).row b k).1=0 := by
      dsimp [choice, basePath, Canonical.row]; rw [hr]; unfold delta scaleRows unitRow
      by_cases hz : (Canonical.enumPath k).2=0
      · have hg : b≠(Canonical.enumPath k).1 := fun E => h (Canonical.enumPath.injective (by simp [j,E,← hz]))
        simp [hz,plaq_iff b _,hg]
      simp [hz]
    rw [he,zero_smul]
  rw [tsum_eq_single j hu]
  simp [PathData.ellTerms,choice,basePath,Canonical.row,j,hr,delta,scaleRows,unitRow,center]

lemma paid_main {H : Bed} (p : Clip) (U : Config G n) (hr : H.roots=delta p) :
    mainTerm p (choice H p) U = Patch.average fun s : Signed => ∑ b : Face (Per n),
      (p.direct * G.price (faceValue (pull s 0 U) b)+‖Real.sqrt (1-p.direct) • G.curvature (faceValue (pull s 0 U) b)‖^2/2+
        homog (polish G (1-p.direct)) (G.curvature (faceValue (pull s 0 U) b))) := by
  unfold mainTerm; congr 1; funext s
  unfold quadratic uncut
  have hZ : ∀ u : Atom G 3, u=dormant G 3 → ∀ (i : Site n) (V : Config G n), u.unmasked V i=0 := by
    rintro a rfl i V; simp [Atom.unmasked,dormant,Atom.poly]
  have hh (i : ℕ) : (choice H p).cubic i=dormant G 3 := rfl
  have he (b : Face (Per n)) (V : Config G n) : (choice H p).ell V b=_ := center_service p V b.1 b.2 hr
  simp_rw [he,hZ _ (hh _) _ _,tsum_zero,Finset.sum_const_zero,add_zero]
  nth_rw 2 [Finset.sum_add_distrib]
  congr 1
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => tipExact p _ i

lemma hol_cont (s : Signed) (b : Face (Per n)) : ContDiffAt ℝ ω (fun a : Bid.Dir G n => G.mat (faceValue (pull s 0 (represent a)) b)) 0 := by
  rw [show (fun a : Bid.Dir G n => G.mat (faceValue (pull s 0 (represent a)) b)) = _ from funext fun i => congrArg G.mat
    (travel_pull (square b.2.val.1 b.2.val.2) (represent i) s b.1 0)] -- inspect
  exact Push.writes ..
lemma hol_zero (s : Signed) (b : Face (Per n)) : (faceValue (pull s 0 (represent (0:Bid.Dir G n))) b)=1 := by
  exact Eq.trans (travel_pull (square b.2.val.1 b.2.val.2) (represent _) s b.1 0) (Push.stroll_zero ..)

/-- Actual top clause of Loop.Kin etc on every side, SAME Q (retained from this
V, no choice to switch to l_{J(N)} later if proving also some E heuristics about l
repair). Doesn't even require bounds on (H,N,L) anymore nor Chart or radius.
Nonempty `Permit` supports these estimates because our ex ante floors give
this particular H.rooms, A0, delta, honoring exact Closure positivity etc. -/
theorem peak (H : Bed) (p : Clip) (hr : H.roots=delta p) (hv : p.direct ≤ 1) :
    ∀ j ≤ 4, SameJet j (fun x : Bid.Dir G n => mainTerm p (choice H p) (represent x)) (fun x => Wilson.energy (represent x)) := by
  let T (x : Bid.Dir G n) (s : Signed) (b : Face (Per n)) := faceValue (pull s 0 (represent x)) b
  let v := 1-p.direct
  let A (s : Signed) (b : Face (Per n)) (x : Bid.Dir G n) := G.price (T x s b)
  let C (s : Signed) (b : Face (Per n)) (x : Bid.Dir G n) := p.direct*A s b x+‖Real.sqrt v • G.curvature (T x s b)‖^2/2+
    homog (polish G v) (G.curvature (T x s b))
  have he (s : Signed) (b : Face (Per n)) : UpTo 4 (A s b) (C s b) :=
    price_jet G _ (hol_cont _ _) (hol_zero _ _) p.direct (sub_nonneg.mpr hv)
  have hh : UpTo 4 (fun x => ∑ s, ∑ b,A s b x) (fun x => ∑ s,∑ b,C s b x) :=
    UpTo.average fun s _ => UpTo.average fun b _ => he s b
  have hn : NeZero (Fintype.card Signed : ℝ) := by
    constructor; exact_mod_cast (by infer_instance : NeZero (Fintype.card Signed)) |>.out
  let q := (Fintype.card Signed : ℝ)
  have ha := hh.weight q⁻¹
  have hg (s : Signed) (x : Bid.Dir G n) : ∑ b, A s b x = Wilson.energy (represent x) :=
    Wilson.energy_pull (represent x) s 0
  have hb : q⁻¹ • (fun x => ∑ s, ∑ b, A s b x) = (fun x => Wilson.energy (represent x)) := by
    ext1 x; change q⁻¹ * ∑ s, ∑ b, A s b x = _
    simp_rw [hg,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; unfold q; simp [hn.out]
  have hz : q⁻¹ • (fun x => ∑ s, ∑ b, C s b x) = (fun x => mainTerm p (choice H p) (represent x)) := by
    ext1 x; rw [paid_main _ _ hr]; rfl
  rw [hb,hz] at ha
  exact fun j hj => ⟨ha.right,ha.left,(ha.jets j hj).symm⟩
end YM.UVNext.PricedKernels
