import YM.MergeProof.West.Melt
import YM.Next.RANK.Cabal


/-!
# Guarded factors: one-tag scope
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Set MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {V Ω : Type*}
variable {C : Family G} {i k l j m p q d D a n N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points n} {hk : i<k} {h : middle C.path.levels b k ≤ i}
variable {c : Course C N p k}
variable {U T τ ε g B Y L} (E : Mural (d:=d) c R x b hk h q T τ U ε)


variable (j : PatchPt x b C.path.levels p d (show i+1 ≤ k from hk))

variable (Q : poly (Chamber G C.S (i+1) p))

def e_legance (s : ℝ) (c : Course C N p k) (x : Points n) (hk : i<k) (h : middle C.path.levels s k ≤ i) (v : Bale C k s p d x hk.le) (U) (Q : poly (Chamber G C.S i p)) :=
    let D:=basisFt c x s i c.allow hk.le h v.1 v.2.val U
    text (rigid D) Q

def traceFt : E.Θ →ℂ := fun t=>
    let V:= basisFt c x b (i+1) c.allow hk (h.trans (Nat.le_succ i)) T.1 j.val (E.V t)
    text (rigid V) Q

def c_hance := E.Γ j

def d_means (_E : Mural (d:=d) c R x b hk h q T τ U ε) (i') := (colorFt R c b x hk h T.1 T.2.val U i').re -- E for typing

def r_ose := carry E.η (d_means E) Q

lemma primeFt :
    letI := E.M
    Measurable (traceFt E j Q) := by
  letI:=E.M; have hp := ((case_meas Q (anneals C c (i+1)) (core C.path.levels x b p (show i+1≤k from hk) (Head j.val))).comp
    (show Continuous (watches C b p c.allow (i+1) (h.trans (Nat.le_succ _)) T.1) from continuous_pull ..)).measurable.comp E.census
  exact hp

section
variable (hx : roomTest C.path.levels b k p d q) (t : Metal b c R hk ε τ g B Y L) (He : 0 < ε) (hu : ε ≤ 1)
variable (hj : t_ests x b hk T.2.val j (C:=C))
include hx t He hu hj
lemma t_alent (hQ : Poetic Q) (hp : ∀ u∈Q.vars, spotFt b (i+1) d hk (C:=C) x j.val u) (hL : Q.totalDegree ≤ D) {w : ℝ} (hV : coin Q ≤ w) :
    ∀ W, 0< c_hance E j W →
      ‖traceFt E j Q W‖ ≤ capZ B D w ∧
      ‖traceFt E j Q W - r_ose E Q W‖ ≤ defect B ε w D ∧
      ‖r_ose E Q W‖ ≤ capZ B D w := by
  intro W hW
  let S:= basisFt c x b (i+1) c.allow hk (h.trans (Nat.le_succ i)) T.1 j.val (E.V W)
  obtain ⟨Z,hZ⟩:= E.wraps j hj W hW
  let V:= rigid (coloring Z S); let F:= d_means E+ E.η W
  rw [show traceFt E j Q W=text V Q by unfold V; rw [colours,hQ]; rfl]
  have ha i (H : i∈ Q.vars) : |V i| ≤ B-1:= (turn_ft (c:=c) (p:=p) hx (h.trans (Nat.le_succ _)) (show _≤_ from hk) T.1 i (hp i H) (E.field j hj W hW) Z).trans t.fine
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
