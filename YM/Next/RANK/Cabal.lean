import YM.Next.RANK.Payload

/-!
# Guarded factors: one-tag scope
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Set MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {V Ω : Type*}
variable {C : Family G} {i k l j m p q d D a n N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points n} {hk : i<k} {h : middle C.path.levels b k ≤ i}
variable {c : Course C N p k}
variable {U T τ ε g B Y L} (E : Emulator (d:=d) c R x b hk h q T τ U ε)


variable (j : Index x b C.path.levels p d (show i+1 ≤ k from hk))

variable (Q : poly (Chamber G C.S (i+1) p))

def elegance (s : ℝ) (c : Course C N p k) (x : Points n) (hk : i<k) (h : middle C.path.levels s k ≤ i) (v : Lane C k s p d x hk.le) (U) (Q : poly (Chamber G C.S i p)) :=
    let D:=basisK c x s i c.allow hk.le h v.1 v.2.val U
    text (rigid D) Q

def traceU : E.Θ →ℂ := fun t=>
    let V:= basisK c x b (i+1) c.allow hk (h.trans (Nat.le_succ i)) T.1 j.val (E.V t)
    text (rigid V) Q

def chance := E.Γ j

def means (_E : Emulator (d:=d) c R x b hk h q T τ U ε) (i') := (colorMean R c b x hk h T.1 T.2.val U i').re -- E for typing

def rose := carry E.η (means E) Q

def capZ (B : ℝ) (d : ℕ) (w : ℝ) := w*Common.priced B d
def defect (B ε w : ℝ) (d : ℕ) := w*((d:ℝ)*B^d*ε)

lemma prime_cont :
    letI := E.M
    Measurable (traceU E j Q) := by
  letI:=E.M; have hp := ((case_meas Q (anneals C c (i+1)) (core C.path.levels x b p (show i+1≤k from hk) (headMark j.val))).comp
    (show Continuous (watches C b p c.allow (i+1) (h.trans (Nat.le_succ _)) T.1) from continuous_pull ..)).measurable.comp E.census
  exact hp

section
variable (hx : roomTest C.path.levels b k p d q) (t : Metal b c R hk ε τ g B Y L) (He : 0 < ε) (hu : ε ≤ 1)
variable (hj : tests x b hk T.2.val j (C:=C))
include hx t He hu hj
lemma talent (hQ : Poetic Q) (hp : ∀ u∈Q.vars, spotP b (i+1) d hk (C:=C) x j.val u) (hL : Q.totalDegree ≤ D) {w : ℝ} (hV : coin Q ≤ w) :
    ∀ W, 0< chance E j W →
      ‖traceU E j Q W‖ ≤ capZ B D w ∧
      ‖traceU E j Q W - rose E Q W‖ ≤ defect B ε w D ∧
      ‖rose E Q W‖ ≤ capZ B D w := by
  intro W hW
  let S:= basisK c x b (i+1) c.allow hk (h.trans (Nat.le_succ i)) T.1 j.val (E.V W)
  obtain ⟨Z,hZ⟩:= E.wraps j hj W hW
  let V:= rigid (coloring Z S); let F:= means E+ E.η W
  rw [show traceU E j Q W=text V Q by unfold V; rw [colours,hQ]; rfl]
  have ha i (H : i∈ Q.vars) : |V i| ≤ B-1:= (turn_strength (c:=c) (p:=p) hx (h.trans (Nat.le_succ _)) (show _≤_ from hk) T.1 i (hp i H) (E.field j hj W hW) Z).trans t.fine
  have hz i (H : i∈ Q.vars) : |V i-F i| ≤ ε:= hZ i (hp i H)
  have hv i (H : i∈ Q.vars) : |V i|≤ B:= (ha i H).trans (sub_le_self B zero_le_one)
  have ht i (H : i∈ Q.vars) : |F i|≤ B:= by
    refine le_trans (b:=|V i-F i|+|V i|) ?_ (by linarith only [hz i H,ha i H,hu])
    rw [abs_sub_comm]; exact le_trans (le_of_eq (congr_arg abs (sub_add_cancel ..).symm)) (abs_add_le ..)
  have hA := mul_le_mul_of_nonneg_right hV (zero_le_one.trans (priced_up D t.grain))
  have he:=t.grain
  exact ⟨(view_v _ _ hL he hv).trans hA, (spot_trial Q V F hL he hv ht He.le hz).trans (mul_le_mul_of_nonneg_right hV (show 0≤ (D:ℝ)*B^D*ε by positivity)), (view_v _ _ hL he ht).trans hA⟩
end

section
variable [MeasurableSpace Ω] {μ : Measure Ω}
lemma release {w : ℝ} (r : Ω→ℝ) (z y : Ω→ ℂ) (u : Guarded r w μ) [IsProbabilityMeasure μ]
    (hx : Integrable y μ) (hy : Measurable z) (hp : ∃ L : ℝ, 0 ≤ L ∧ ∀ V, 0< r V→ ‖z V‖≤ L) {t : ℝ} (hz : 0 ≤ t) (H : ∀ U, 0< r U → ‖z U-y U‖ ≤ t) :
    Integrable (fun V=> (↑(r V):ℂ)*z V) μ ∧ ‖(∫ V, (↑(r V):ℂ)*z V∂μ)-∫ V, (↑(r V):ℂ)*y V ∂μ‖ ≤ t:= by
  let x (v):= (↑(r v):ℂ)*z v
  let l (v):= (↑(r v):ℂ)* y v
  have hs (v): ‖(↑(r v):ℂ)‖≤1:= (Complex.norm_real ..).trans_le (Real.norm_of_nonneg (u.lower v) |>.trans_le (u.up v))
  have hV : Integrable x μ:= by
    obtain ⟨A,hA,hp⟩:=hp; apply Integrable.of_bound (show AEStronglyMeasurable x μ from ((Complex.continuous_ofReal.measurable.comp u.meas).mul hy).aestronglyMeasurable) A; apply Eventually.of_forall; intro i
    unfold x; by_cases h:0 < r i; rw [norm_mul]; exact (mul_le_mul (hs i) (hp i h) (norm_nonneg _) zero_le_one).trans_eq (one_mul ..)
    rw [show r i=0 from le_antisymm (not_lt.mp h) (u.lower i),Complex.ofReal_zero, zero_mul,norm_zero];exact hA
  have hh(v): ‖(x-l) v‖≤ t:= by
    unfold x l; rw [Pi.sub_apply,← mul_sub];by_cases h:0 < r v; rw [norm_mul]; exact (mul_le_mul (hs v) (H v h) (norm_nonneg _) zero_le_one).trans_eq (one_mul ..)
    rw [show r v=0 from le_antisymm (not_lt.mp h) (u.lower v),Complex.ofReal_zero, zero_mul,norm_zero];exact hz
  refine ⟨hV,?_⟩; have ha:Integrable l μ:= affordable y u hx; rw [← integral_sub hV ha]; exact (norm_integral_le_integral_norm ..).trans ((integral_mono ((hV.sub ha).norm) (integrable_const t) hh).trans_eq (by simp))

lemma indiv {p u a b : ℂ} {δ β γ : ℝ} (h : ‖p-a‖ ≤ δ) (hq : ‖u-b‖≤δ) (hp : ‖p‖ ≤ β) (hb : ‖b‖ ≤ γ) : ‖p*u-a*b‖ ≤ β*δ+δ*γ:= by
  rw [show p*u-a*b=p*(u-b)+(p-a)*b by ring]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; exact add_le_add (mul_le_mul hp hq (norm_nonneg _) ((norm_nonneg _).trans hp)) (mul_le_mul h hb (norm_nonneg _) ((norm_nonneg _).trans h))
end

end YM.Next.Rank.Tapes
