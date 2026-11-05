import YM.Further.CURVED_GAUSSIAN_JETS.Perturb
import YM.Further.CURVED_GAUSSIAN_JETS.Weights
/-!
# Simultaneously pricing ordered left kernel jets through inversion (post-L)
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Jets
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Wilson RG Precision Progress.StationaryScenes
open Green (wt)
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
variable {n c : Side} {G : Gauge} {I : Type*} [Fintype I] {a : I → Site n}
    {U : Config G c} {A B : Field G c I} {s : Weights a} {r M C : ℝ} {l : Word G c} {k : ℕ}
    {Q : Directions G c → Prop} {p : Prices}


def Cash (s : Weights a) (r : ℝ) (k : ℕ) (Q : Directions G c → Prop) (U : Config G c) (A : Field G c I) (M : ℝ) :=
    ∀ l : Word G c, l.length≤k → (∀ i∈l,Q i) → s.Bank r l.length (jet l A U) M
lemma Cash.mono (h : Cash s r k Q U A M) {b : ℝ} (hc : b≤r) (hm : M≤C) : Cash s b k Q U A C := fun l hl hd => ((h l hl hd).slow hc).mono hm
lemma Cash.plus (ha : Cash s r k Q U A M) (hb : Cash s r k Q U B C) (ga : Good A k U) (gb : Good B k U) :
    Cash s r k Q U (fun V=> A V+B V) (M+C) := fun l hl hd => by rw [jet_plus ga gb hl]; exact (ha l hl hd).plus (hb l hl hd)
lemma Cash.neg (ha : Cash s r k Q U A M) : Cash s r k Q U (fun V=> -A V) M := fun l hl hd=>by rw [jet_neg]; exact (ha l hl hd).neg
lemma Cash.transpose (ha : Cash s r k Q U A M) : Cash s r k Q U (fun V => (A V).transpose) M := fun l hl hd=> (ha l hl hd).transpose
lemma Cash.symmetrize (ha : Cash s r k Q U A M) (ga : Good A k U) : Cash s r k Q U (fun V => (1/2:ℝ) • (A V + (A V).transpose)) M := by
  intro l hl hd
  have ht := ((ha.plus ha.transpose ga ga.transpose) l hl hd).scale (1/2)
  rw [jet_scale]; convert ht using 1; rw [abs_of_pos (by norm_num : 0<(1/2:ℝ))]; ring
lemma Cash.product (ha : Cash s r k Q U A M) (hb : Cash s r k Q U B C) (ga : Good A k U) (gb : Good B k U)
    (hr : 0≤s.width r k) (hm : 0≤M) (hc : 0≤C) : Cash s r k Q U (fun V => A V * B V) (s.pay k*M*C) := by
  intro v hl hd
  have he := Weights.product_bank (s:=s) (v:=v) (l:=0) (m:=0) ga gb hm hc hl hd (fun x hx he=> show s.Bank r (0+x.length) _ M ∧ s.Bank r (0+x.length) _ C from by rw [Nat.zero_add]; exact ⟨ha x (hx.trans hl) he,hb x (hx.trans hl) he⟩) (by omega : 0+0+v.length≤k) hr
  simpa only [Nat.zero_add] using he

def spare (p : Prices) := p.speed / 4
lemma spare_pos (p : Prices) : 0<spare p := by unfold spare; have := p.speed_pos; positivity
lemma four_spare (p : Prices) : 4*spare p=p.speed := by unfold spare; ring
/-- One position/sector charge at V. No position cost on 
undifferentiated inverse except through the counting/stencil/gap estimates
in `base`. No τ blowup attached per walk step. M can bound zeroth &
all derivatives, no cost-on-error hypotheses.
-/
structure Street (p : Prices) (s : Weights a) (k : ℕ) (Q : Directions G c → Prop) (A : Field G c I) (U : Config G c) (M : ℝ) : Prop where
  base : Fits a p (A U)
  cash : Cash s p.speed k Q U A M
  room : 0≤s.width (spare p) k
  good : Good A k U
  has : 0 ≤ M
namespace Street
variable (h : Street p s k Q A U M)
include h
lemma restrict {X : Type*} [Fintype X] (e : X ↪ I) : Street p (s.restrict e) k Q (fun V => (A V).submatrix e e) U M :=
    ⟨h.base.restrict _, fun l hl hd => (h.cash l hl hd).restrict e, h.room, h.good.restrict e, h.has⟩
lemma space {r : ℝ} (hr : spare p≤r) : 0 ≤ s.width r k := h.room.trans (by unfold Weights.width; linarith only [hr])
end Street

variable [DecidableEq I]
def raise (A : Field G c I) (u : ℝ) : Field G c I := fun V => shifted (A V) u
def eye (A : Field G c I) (u : ℝ) := fun V => (shifted (A V) u)⁻¹
lemma Good.raise (h : Good A k U) (u : ℝ) : Good (raise A u) k U := h.plus (Good.const (u • 1))
lemma Street.eye (h : Street p s k Q A U M) {u : ℝ} (hu : 0≤u) : Good (eye A u) k U := (h.good.raise u).inv (h.base.shift_pos hu).isUnit
lemma jet_raise (h : Good A k U) (u : ℝ) (hk : l.length≤k) (hl : l≠[]) : jet l (raise A u) U = jet l A U := by
  unfold raise shifted; rw [jet_plus h (Good.const (u•1)) hk,jet_const,if_neg hl, add_zero]
lemma jet_eye (h : Good A 1 U) (d : Directions G c) (u : ℝ) (hu : IsUnit (shifted (A U) u)) :
    jet (l++[d]) (eye A u) U = - jet l (fun V => eye A u V * jet [d] (raise A u) V * eye A u V) U := jet_inverse (h.raise u) hu d

def wheelCost (s : Weights a) (k : ℕ) (M : ℝ) := s.pay k * (s.pay k*M)
def discount (p : Prices) (s : Weights a) (k : ℕ) (M : ℝ) : ℕ → ℝ
  | 0 => p.reserve
  | j+1 => discount p s k M j + wheelCost s k M*(discount p s k M j)^2
lemma discount_step (p : Prices) (s : Weights a) (k : ℕ) {M : ℝ} (h : 0≤M) (j : ℕ) : discount p s k M j ≤ discount p s k M (j+1) := by
  rw [discount]; unfold wheelCost; have := s.pay_pos k; exact le_add_of_nonneg_right (by positivity)
lemma discount_pos (p : Prices) (s : Weights a) (k : ℕ) {M : ℝ} (h : 0≤M) (j : ℕ) : 0<discount p s k M j := by
  induction j with | zero => exact p.reserve_pos | succ j ih => exact ih.trans_le (discount_step p s k h j)

/-- Explicit jet price uniform even on every principal restriction
(apply `h.restrict`). -/
lemma eye_budget (h : Street p s k Q A U M) {u : ℝ} (hu : 0≤u) {j : ℕ} (hj : j≤k) : Cash s p.speed j Q U (eye A u) (discount p s k M j / (1+u)) := by
  have hspace := h.space (r:=p.speed) (by unfold spare; linarith [p.speed_pos])
  have hp := h.eye hu
  induction j with
  | zero =>
    intro l hl hd; have hi : l=[] := by simpa using hl
    subst l; exact Weights.zero_order (h.base.tender u hu)
  | succ j ih =>
    intro l hl hd
    let C := discount p s k M j / (1+u)
    specialize ih (Nat.le_of_succ_le hj)
    have hC : 0≤C := by have := discount_pos p s k h.has j; unfold C; positivity
    have hM := h.has; have hy := s.pay_pos k
    by_cases he : l.length ≤ j
    · exact (ih.mono le_rfl (by gcongr; exact discount_step p s k h.has j) l he hd)
    induction l using List.reverseRecOn with
    | nil => simp at he
    | append_singleton l d _ =>
      have hjd : Q d := hd _ (by simp)
      have hdl i (hi : i∈l) := hd i (by simp [hi])
      have he : l.length=j := by simp at he hl; omega
      have hD := (h.good.raise u).jet (l:=[d]) (m:=j) (by simpa only [List.length_cons,List.length_nil,Nat.zero_add,Nat.add_comm 1] using hj)
      let f := eye A u; let g := jet [d] (raise A u)
      rw [jet_eye (h.good.lower (by omega)) d u (h.base.shift_pos hu).isUnit]
      have hP : Good f j U := hp.lower (Nat.le_of_succ_le hj)
      have hh (x : Word G c) (hx : x.length≤j) (hy : ∀ i∈x,Q i) : s.Bank p.speed (1+x.length) (jet x g U) M := by
        have hl := h.cash (x++[d]) (by simp; omega) (by simpa only [List.mem_append,List.mem_singleton, or_imp, forall_and] using (show (∀ i∈x,Q i) ∧ ∀ i : Directions G c,i=d → Q i from ⟨hy, fun _ he => he ▸ hjd⟩))
        rw [show 1+x.length = (x++[d]).length by simp [Nat.add_comm]]
        unfold g; rw [iter,jet_raise h.good u (by simp; omega) (by simp)]; exact hl
      have hfg (x : Word G c) (hx : x.length≤j) (hy : ∀ i∈x,Q i) : s.Bank p.speed (1+x.length) (jet x (fun V => f V*g V) U) (s.pay k*C*M) :=
        Weights.product_bank (l:=0) (m:=1) hP hD hC hM hx hy (fun t ht ht' => ⟨by rw [Nat.zero_add]; exact ih t (ht.trans hx) ht',hh t (ht.trans hx) ht'⟩) (by omega) hspace
      rw [List.length_append, Nat.add_comm l.length];
      apply ((Weights.product_bank (l:=1) (m:=0) (hP.prod hD) hP (show 0≤s.pay k*C*M by positivity) hC he.le hdl
          (fun t ht ht'=> ⟨hfg t (ht.trans he.le) ht', by rw [Nat.zero_add]; exact ih t (ht.trans he.le) ht'⟩) (by omega) hspace).neg).mono
          (D:=discount p s k M (j+1)/(1+u)) ?_
      unfold C
      let d := discount p s k M j
      have hd := discount_pos p s k hM j
      calc
        _ ≤ (s.pay k*(s.pay k*d*M)*d)/(1+u) := by rw [← mul_div_assoc]; gcongr; exact div_le_self hd.le (by linarith only [hu])
        _ ≤ _ := by rw [discount]; gcongr; unfold wheelCost d; linarith only [hd]
end YM.Further.CurvedGaussianJets.Jets
