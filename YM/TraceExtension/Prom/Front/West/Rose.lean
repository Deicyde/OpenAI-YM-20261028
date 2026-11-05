import YM.MergeProof.West.Rose
import YM.TraceExtension.Prom.Front.West.Melt
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.MergeProof.West.Rose for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Set MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {V Ω : Type*}
variable {C : Family G} {i k l j m p q d D a n N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points n} {hk : i<k} {h : middleSky C.path.levels b k ≤ i}
variable {c : Course C N p k}
variable {U T τ ε g B Y L} (E : MuralSky (d:=d) c R x b hk h q T τ U ε)

variable (j : PatchPt x b C.path.levels p d (show i+1 ≤ k from hk))

variable (Q : poly (Chamber G C.S (i+1) p))

def e_leganceSky (s : ℝ) (c : Course C N p k) (x : Points n) (hk : i<k) (h : middleSky C.path.levels s k ≤ i) (v : BaleSky C k s p d x hk.le) (U) (Q : poly (Chamber G C.S i p)) :=
    let D:=basisFtSky c x s i c.allow hk.le h v.1 v.2.val U
    text (rigid D) Q

def traceFtSky : E.Θ →ℂ := fun t=>
    let V:= basisFtSky c x b (i+1) c.allow hk (h.trans (Nat.le_succ i)) T.1 j.val (E.V t)
    text (rigid V) Q

def c_hanceSky := E.Γ j

def d_meansSky (_E : MuralSky (d:=d) c R x b hk h q T τ U ε) (i') := (colorFtSky R c b x hk h T.1 T.2.val U i').re

def r_oseSky := carry E.η (d_meansSky E) Q

lemma primeFtSky :
    letI := E.M
    Measurable (traceFtSky E j Q) := by
  letI:=E.M; have hp := ((case_meas Q (anneals C c (i+1)) (core C.path.levels x b p (show i+1≤k from hk) (Head j.val))).comp
    (show Continuous (watchesSky C b p c.allow (i+1) (h.trans (Nat.le_succ _)) T.1) from continuous_pull ..)).measurable.comp E.census
  exact hp

section
variable (hx : roomTestSky C.path.levels b k p d q) (t : Metal b c R hk ε τ g B Y L) (He : 0 < ε) (hu : ε ≤ 1)
variable (hj : t_ests x b hk T.2.val j (C:=C))
include hx t He hu hj
lemma t_alentSky (hQ : Poetic Q) (hp : ∀ u∈Q.vars, spotFt b (i+1) d hk (C:=C) x j.val u) (hL : Q.totalDegree ≤ D) {w : ℝ} (hV : coin Q ≤ w) :
    ∀ W, 0< c_hanceSky E j W →
      ‖traceFtSky E j Q W‖ ≤ capZ B D w ∧
      ‖traceFtSky E j Q W - r_oseSky E Q W‖ ≤ defect B ε w D ∧
      ‖r_oseSky E Q W‖ ≤ capZ B D w := by
  intro W hW
  let S:= basisFtSky c x b (i+1) c.allow hk (h.trans (Nat.le_succ i)) T.1 j.val (E.V W)
  obtain ⟨Z,hZ⟩:= E.wraps j hj W hW
  let V:= rigid (coloring Z S); let F:= d_meansSky E+ E.η W
  rw [show traceFtSky E j Q W=text V Q by unfold V; rw [colours,hQ]; rfl]
  have ha i (H : i∈ Q.vars) : |V i| ≤ B-1:= (turn_ftSky (c:=c) (p:=p) hx (h.trans (Nat.le_succ _)) (show _≤_ from hk) T.1 i (hp i H) (E.field j hj W hW) Z).trans t.fine
  have hz i (H : i∈ Q.vars) : |V i-F i| ≤ ε:= hZ i (hp i H)
  have hv i (H : i∈ Q.vars) : |V i|≤ B:= (ha i H).trans (sub_le_self B zero_le_one)
  have ht i (H : i∈ Q.vars) : |F i|≤ B:= by
    refine le_trans (b:=|V i-F i|+|V i|) ?_ (by linarith only [hz i H,ha i H,hu])
    rw [abs_sub_comm]; exact le_trans (le_of_eq (congr_arg abs (sub_add_cancel ..).symm)) (abs_add_le ..)
  have hA := mul_le_mul_of_nonneg_right hV (zero_le_one.trans (priced_up D t.grain))
  have he:=t.grain
  exact ⟨(view_v _ _ hL he hv).trans hA, (spot_trial Q V F hL he hv ht He.le hz).trans (mul_le_mul_of_nonneg_right hV (show 0≤ (D:ℝ)*B^D*ε by positivity)), (view_v _ _ hL he ht).trans hA⟩
end

end YM.Next.Rank.Tapes.West
