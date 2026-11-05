import YM.Further.GAUSSIAN_SCALAR_LEDGER.Consumers
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Afford

/-! # Investing the matching kernel papers into actual E uses -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir.Suite
open Filter Function Set Lattice Wilson Pressure RG Tree Precision Next Next.SectorChange Rows Exterior Bloch
    Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussian Push.PriceCompiler Supply Testing AnalyticBridge.LocalGaussianLaws
    AnalyticBridge.VerifiedReset.Time Push.AbsoluteSums Shoot Bid UVNext.PricedKernels Input
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {V : Rolls s} {Θ : Protection V} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {a : Levels G} {C : Programs s} {D : ℕ→ℕ→Record} {E t : ℕ→ℕ→ℝ} {r : ℕ→ℕ→ℕ} {m N : ℕ}

variable (p : ℕ) (H : Horizon a) (Q : ℕ→ℕ→PathData G) (hH : H.Suffices K)
    (hs : ∀ i∈({m,m+1}:Set ℕ),Sworn (H.H N i) (a.S.side i p) G) (hQ : ∀ i∈({m,m+1}:Set ℕ),Attached (H.H N i) (Q N i)) (hm : m<N)
include hH hm
lemma seam_of : Seam (Permit.tube H Q N m p) (wide K (fine a m) (coarse a m)) (scale K (fine a m) (coarse a m)) := by
  let S:=a.clock.op m p; let T := H.towers N m; let j:=fine a m; let i:=coarse a m; let L : ℝ := S.patch.L.val
  have ha : K.Ω i ≤ scale K j i ∧ K.Ω j ≤ scale K j i := by unfold scale; constructor <;> grind [le_abs_self]
  have hh := hH.costs N m hm |>.2.2.2 [] (by simp)
  change Seam _ (min (K.α j) (K.α i)) (scale K j i)
  exact ⟨strip_mono (show T.T.strip (K.α j) (K.Ω j / L^2) from hh.2) (min_le_left ..) (div_le_div_of_nonneg_right ha.2 (sq_nonneg _)),_,_, hH.crossings N m p hm,mul_eq_one_comm.mp (hH.all N (m+1) hm _).diagonalInv,strip_mono (hH.rows N _ hm).2.2.2.2 (min_le_left ..) ha.2,strip_mono (hH.rows N _ hm.le).1 (min_le_right ..) ha.1⟩
include hs hQ
lemma booths_of (hT : (query s K (fine a m) (coarse a m)).Funds (a.clock.op m p) (Permit.tube H Q N m p)) : Lift.Booth (query s K (fine a m) (coarse a m)) _ (Permit.tube H Q N m p) := by
  have he : m∈({m,m+1}:Set ℕ) ∧ m+1∈({m,m+1}:Set ℕ) := by simp
  exact ⟨hT,_,_,_,_,_,_,hH.all N (m+1) hm _,hH.all N m hm.le _,hQ _ he.2,hQ _ he.1,hs _ he.2,hs _ he.1,hH.crossings N m p hm,hH.stack N m p hm⟩

section installed
omit hs hQ hH
variable {P : Before} {f : ℕ → ℕ} {V : Rolls (P.sheet G f)} {Θ : Protection V} {W : Delays Θ} {Y : Bar W} {I : Wait Y} {M : Preparations P V}
    {C : Programs (P.sheet G f)}
include hm
lemma tickets (hP : Permit M I a) (hv : Motor P a H) (hq : Installed P a H Q) (h : Offers (P.frozen G) W C D r) (he : Earlier (P.sheet G f) (P.frozen G) C E t r) :
    Enabled (P.sheet G f) (P.frozen G) C D E t r a m p (Permit.tube H Q N m p) := by
  have hb := hv.finalCosts; apply enabled h he hP.paid _ _ (seam_of p H Q hb hm)
  exact booths_of p H Q hb (fun i hi => hv.swears _ _ _ (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega))
    (fun i hi => (hq.linear _ _ (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega)).placed) hm (ticket_to_measure hP hv hq N m p hm).1
end installed
omit hs hQ hH
/-- A `Directed` witness may have NEED of a separate signed-carrier
supplier (often from Wired, not in Directed by itself). Still pair with
ANY authenticated `Earliers` on this clock and CALLING (Clockwork.desk)
data. -/
lemma directed {Z : ChartRatio G} {P : PostCost V} (B : Directed G I Z K P) (hS : ∀ i∈({m,m+1}:Set ℕ), Sworn (B.M.H N i) (B.a.S.side i p) G) (h : Offers K W C D r) (he : Earlier s K C E t r) :
    Enabled s K C D E t r B.a m p (ships B N m p) := enabled h he B.valid _ (booths_of p B.M B.kin.path B.plan hS (fun i hi => B.support.links _ _ (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega)) hm (Testing.proceeds B N m p hm)) (seam_of p B.M B.kin.path B.plan hm)
end YM.PhysicalNext.JointLoad.Heir.Suite
