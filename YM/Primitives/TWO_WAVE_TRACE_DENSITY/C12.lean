import YM.CellFourier.Circulant
import YM.Laurent.Rune
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Routing
import YM.Work.F07.Read


/-!
# C12 kinematics & q estimate 

Entry strip version (includes nontrivial type/card costs, appropriate for
per-site fixed-L period errors). In this theorem external continuation is not
needed, test REAL momentum mesh waves with complex amplitudes. Sign in C12
is the analytic mixed precision sign right-hand side tested bilinearly, NOT a
square norm. There is no α input. For physical logdet calculus at zero and
real polarized wave use see later files; this gives the δ and explicit BZ
error on EACH independent insertion test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Laurent Bloch Matrix Complex
open scoped BigOperators Topology

abbrev Symbol (α β : Type*) := Momentum → Matrix α β ℂ

variable {α β γ : Type*} {η C D : ℝ}

/-- Strip bill on the *undephased* symbol. -/
structure Marked (F : Symbol α β) (η C : ℝ) : Prop where
  nn : 0≤C
  width : 0<η
  hol : ∀ i j, Vane (fun p => F p i j) η
  paid (p) (hp : p ∈ Laurent.strip η) : ∀ i j, ‖F p i j‖ ≤ C

def crossFee (β : Type*) [Fintype β] (C D : ℝ) := Fintype.card β*(C*D)

namespace Marked
variable {F : Symbol α β}
lemma walked {n : Side} (h : Marked F η C) (k : Site n) : Marked (fun q => F (q+mon k)) η C := by
  have hx q (hp : q∈Laurent.strip η) : q+mon k ∈ Laurent.strip η := by
    intro i; have he := congr_fun (real_frequency k) i
    change star (mon k i)=_ at he; rw [Complex.star_def, Complex.conj_eq_iff_im] at he
    simpa [he] using hp i
  exact ⟨h.nn,h.width,fun i j => ⟨h.width, fun p hp => ((h.hol i j).hol _ (hx p hp)).comp (f:=fun q : Momentum => q+mon k) p (by fun_prop),
    fun p hp z => by rw [add_right_comm p]; exact (h.hol i j).reset _ (hx p hp) z⟩, fun p hp => h.paid _ (hx p hp)⟩

lemma compose [Fintype β] {T : Symbol β γ} (h : Marked F η C) (hT : Marked T η D) : Marked (fun p => F p*T p) η (crossFee β C D) := by
  have := h.nn; have := hT.nn
  refine ⟨?_,h.width,fun i j => ?_,fun p hp i j => ?_⟩
  · unfold crossFee; positivity
  · simp_rw [Matrix.mul_apply]; exact ⟨h.width,
      fun p hp => DifferentiableAt.fun_sum (fun s _ => ((h.hol i s).hol _ hp).mul ((hT.hol _ j).hol _ hp)),
      fun p hp z => Finset.sum_congr rfl fun s _ => by rw [(h.hol i s).reset _ hp,(hT.hol s j).reset _ hp]⟩
  rw [Matrix.mul_apply]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (s:=Finset.univ) (g:=fun s : β => C*D) fun s _ => ?_).trans_eq ?_)
  · rw [norm_mul]; exact mul_le_mul (h.paid p hp i _) (hT.paid p hp _ j) (norm_nonneg _) h.nn
  simp [crossFee]

lemma less {T : Symbol α β} (h : Marked F η C) (hT : Marked T η D) : Marked (fun p => F p-T p) η (C+D) := by
  refine ⟨add_nonneg h.nn hT.nn,h.width,fun i j => ⟨h.width,fun p hp => ?_,fun p hp z=>?_⟩,fun p hp i j => ?_⟩
  · exact ((h.hol _ _).hol _ hp).sub ((hT.hol _ _).hol _ hp)
  · simp only [Matrix.sub_apply,(h.hol i j).reset p hp z,(hT.hol i j).reset p hp z]
  exact (norm_sub_le ..).trans (add_le_add (h.paid p hp i j) (hT.paid p hp i j))

lemma traced [Fintype α] {F : Symbol α α} (H : Marked F η C) :
    Vane (fun p => trace (F p)) η ∧ ∀ p∈Laurent.strip η, ‖trace (F p)‖ ≤ Fintype.card α*C := by
  simp_rw [Matrix.trace,Matrix.diag_apply]
  exact ⟨⟨H.width,fun p hp => DifferentiableAt.fun_sum (fun s _ => (H.hol s s).hol _ hp),fun p hp z=>
    Finset.sum_congr rfl fun s _ => (H.hol s s).reset _ hp _⟩, fun p hp => (norm_sum_le ..).trans ((Finset.sum_le_sum
      (s:=Finset.univ) (g:=fun i : α => C) fun i _ => H.paid p hp i i).trans_eq (by simp))⟩

lemma read (R : Row α β) (hs : R.strip η C) (hC : 0 ≤ C) {s : ℝ} (he : 0<s) (h : s<η) : Marked R.read s C :=
    ⟨hC,he,fun i j => ⟨he,fun _ hp => (Work.F07.readDeriv (R.constant_strip hs i j) he h hp).1, fun _ _ _ => Laurent.periodic .. ⟩,fun p hp i j =>
      (R.constant_strip hs i j).estimate p (fun a => (hp a).le.trans h.le)⟩


end Marked

variable {n : Side} [DecidableEq α] [Fintype α]
abbrev EndCell (α : Type*) := Matrix α α ℂ
abbrev EndTorus (n : Side) (α : Type*) := EndCell (Site n×α)

section ports



def quote (p : Momentum) (I F T U : Symbol α α) (q : Momentum) : ℂ :=
  -- Corresponding BZ expression only integrated for p+t=0
  trace (I q*U q)-trace (I q*T (q+p)*I (q+p)*F q)





variable {I F T U : Symbol α α} {X A B D₂ : EndTorus n α} {p t : Site n}





omit [DecidableEq α] [Fintype α] in
lemma update_mark (H : Marked I η C) (p t : Site n) : I (mon p+mon t)=I (mon (p+t)) := by
  obtain ⟨z,hz⟩:=mon_add p t
  ext i j
  rw [hz]; exact ((H.hol _ _).reset _ (Work.F07.realStrip _ H.width (by simp [star_add])) _).symm

/-- Crude entry sum budget, useful for post-L q errors; C for inverse,
J,K,L for the individual external jet prices. Track dimension here, don't
spend as pre-L L^0 for e.g. analytic ratio estimates on R^4 residues. -/
def siteCost (α : Type*) [Fintype α] (C J K L : ℝ) := Fintype.card α * (crossFee α C L + crossFee α (crossFee α (crossFee α C K) C) J)

omit [DecidableEq α] in
lemma quote_ready {J K L : ℝ} (hI : Marked I η C) (hF : Marked F η J) (hT : Marked T η K) (hU : Marked U η L) (p : Site n) :
    Vane (quote (mon p) I F T U : Momentum → ℂ) η ∧
    ∀ q∈Laurent.strip η, ‖quote (mon p) I F T U q‖ ≤ siteCost α C J K L := by
  have he := hI.compose hU
  have ht := ((hI.compose (hT.walked p)).compose (hI.walked p)).compose hF
  unfold quote
  simpa only [quote,siteCost,Matrix.trace_sub] using (he.less ht).traced


end ports
end YM.Primitives.TwoWave
