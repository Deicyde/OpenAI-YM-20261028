import YM.Pert.Bulk.Tails
import YM.PREC.Stacks

/-! Pre-length row/difference/column bounds on the prospective all-face predictor
`H^{-1} T H'` formed using the retained unmodified metric data of the exact kernel pipeline.
Here only quantitative estimates on the indicated exact cover kernel, not identifying any
positive-order stationary jets or Wilson transfer arrays. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bulk
open Lattice Laurent RG Bloch Function Precision Exterior
open scoped ENNReal Topology BigOperators Classical
variable {L:Side}{α β γ κ:Type}

def sandwich [Fintype β][Fintype α] (H:Row κ α)(T:Kernel α β)(J:Row β γ) := bind (bind (plain H) T) (plain J)
def pre (α β:Type) [Fintype β] [Fintype α] (p q r : ℝ) : ℝ := Fintype.card α * Fintype.card β * p*q*r
private lemma pco [Fintype α][Fintype β] (p q r h:ℝ) : (Fintype.card β : ℝ) * (((Fintype.card α:ℝ)*(p*(q*h)))*r) = pre α β p q r * h := by unfold pre; ring
lemma row_sandwich [Fintype β][Fintype α] {p q r θ τ σ:ℝ} {d:ℕ} {H:Row κ α}{T:Kernel α β}{J:Row β γ} (hK:H.strip θ p)(hJ:J.strip τ r)(hk:RowCost σ L T (q/(L.val:ℝ)^d))(hs:0≤σ)(hθ:σ≤θ)(hτ:σ≤τ)(hp:0≤p)(hq:0≤q)(hr:0≤r):
   RowCost σ L (sandwich H T J) ((pre α β p q r)/(L.val:ℝ)^d) := by
    rw [div_eq_mul_inv,← pco]
    apply row_right (hK:=hJ) ?_ hτ hs hr (by positivity : 0≤ (Fintype.card α:ℝ)*(p*(q*((L.val:ℝ)^d)⁻¹)))
    · simp_rw [← div_eq_mul_inv]; exact row_left hK hθ hk hs hp (by positivity)
lemma col_sandwich [Fintype β][Fintype α] {p q r θ τ σ:ℝ} {d:ℕ} {H:Row κ α}{T:Kernel α β}{J:Row β γ} (hK:H.strip θ p)(hJ:J.strip τ r)(hk:ColCost σ L T (q*(L.val:ℝ)^4/(L.val:ℝ)^d))(hs:0≤σ)(hθ:σ≤θ)(hτ:σ≤τ)(hp:0≤p)(hq:0≤q)(hr:0≤r):
   ColCost σ L (sandwich H T J) (pre α β p q r * (L.val:ℝ)^4/(L.val:ℝ)^d) := by
    rw [div_eq_mul_inv,mul_assoc _,← pco]
    apply col_right (hK:=hJ) ?_ hτ hs hr (by positivity : 0≤ (Fintype.card α:ℝ)*(p*(q*((L.val:ℝ)^4*((L.val:ℝ)^d)⁻¹))))
    · simp_rw [← mul_assoc q,← div_eq_mul_inv]; exact col_left hK hθ hk hs hp (by positivity)
lemma all_sandwich [Fintype β][Fintype α] {p q r θ τ σ:ℝ} {d:ℕ} {H:Row κ α}{T:Kernel α β}{J:Row β γ} (hK:H.strip θ p)(hJ:J.strip τ r)(hk:Atlas σ L d T q)(hθ:σ≤θ)(hτ:σ≤τ)(hp:0≤p)(hr:0≤r):
   Atlas σ L d (sandwich H T J) (pre α β p q r) := by
    have hq := hk.nonneg
    have hs := hk.width
    refine ⟨hs,by unfold pre; positivity,row_sandwich hK hJ hk.row hs hθ hτ hp hq hr,col_sandwich hK hJ hk.col hs hθ hτ hp hq hr, fun i=>?_⟩
    have ht' := plain_bind hK (hs.trans hθ) hk.row hs i
    have hR := row_left hK hθ hk.row hs hp (div_nonneg hq (by positivity))
    have he' := foot_bind hR hs (plain0 hJ hτ).1 hs i
    change RowCost σ L (foot i (bind _ _)) _
    rw [he',ht']; exact row_sandwich hK hJ (hk.step i) hs hθ hτ hp hq hr

abbrev Faces := TypeFace 2
def response (V : Towers L)(Hf Hc : Bed):Kernel Faces Faces := sandwich Hf.inverse (install V.T) Hc.metric
lemma predictor_atlas {V : Towers L} {H H' : Bed} {α θ σ C X:ℝ} {z:ℕ}
 (hOdd : Odd L.val) (hDepth:1≤z)(hV:V.Deep α C z)
 (hH:H.covered α C)(hH':H'.covered θ X)
 (hs:0≤σ)(hα:σ≤α)(hθ:σ≤θ)(hp:0≤C)(hr:0≤ X):
   Atlas σ L 2 (response V H H') (pre Faces Faces C (Real.exp (4*σ)*C) X) := by
    have hd := hV.2.2.2 [] (show ([] : List Axis).length ≤ z from by simp) |>.2
    have he : ∀ i,(forwardC L V.T i).strip α (C/(L.val:ℝ)^(2+1)) := fun i => (hV.2.2.2 [i] (by simpa using hDepth)).2
    have ht := cross_atlas hOdd (show V.T.strip α _ from hd) he hα hs hp
    apply all_sandwich hH.2.2.1 hH'.2.1 ht hα hθ hp hr

variable {G:Gauge}{a:Levels G}{P:MapPrices}{H : Horizon a}{N m:ℕ}{σ:ℝ}
lemma priced_atlas (h:H.Suffices P) (hk:m<N) (hOdd : Odd ((a.S.block m).val))(hDepth:3≤a.clock.J (m+1))
 (hs:0≤σ)(hα:σ≤ P.α (a.clock.J (m+1)))(hθ:σ≤P.α (a.clock.J m))(hf:0≤P.Ω (a.clock.J (m+1)))(hc:0≤P.Ω (a.clock.J m)) :
   Atlas σ (a.S.block m) 2 (response (H.towers N m) (H.H N (m+1)) (H.H N m))
     (pre Faces Faces (P.Ω (a.clock.J (m+1))) (Real.exp (4*σ)*P.Ω (a.clock.J (m+1))) (P.Ω (a.clock.J m))) := predictor_atlas hOdd (by omega) (h.costs N m hk) (h.rows N (m+1) hk) (h.rows N m hk.le) hs hα hθ hf hc
end YM.Pert.Bulk
