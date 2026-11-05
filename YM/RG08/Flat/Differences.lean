import YM.Next.FREE_KERNELS.Differences
import YM.Next.STATIONARY.Shape.SoftTransfers

/-!
# Difference division in the Wilson rooted coefficient norm

Factor through real forward-difference kernels using the order of a Taylor
zero in the independent momenta. All widths and costs here can be fixed
before the block size and period. We use the analytic division theorem of
`Stationary.layers`; we don't divide by the momentum norm squared.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG08

open Function Filter Finset Laurent Stationary Lattice Bloch Matrix Precision
open Next.Free Work.F08
open scoped Topology BigOperators

lemma readRealKernel_neg {I : Type} [Fintype I] (f : Shift I → ℝ) (p : Phase I)
    (hp : star p = p) :
    star (Laurent.read (fun x => (f x : ℂ)) (-p)) =
      Laurent.read (fun x => (f x : ℂ)) p := by
  unfold Laurent.read
  rw [tsum_star]
  apply tsum_congr
  intro b
  have h := mode_adjoint (-p) b
  rw [star_neg, hp, mode_opposite, mode_inverse, inv_inv] at h
  simp only [smul_eq_mul, star_mul, mode_inverse,h]
  rw [Complex.star_def, Complex.conj_ofReal, mul_comm]

lemma divZ_neg {I : Type} [Fintype I] [DecidableEq I]
    (i : I) (p : Phase I) (hp : star p = p) :
    star (divZ i (-p)) = divZ i p := by
  unfold divZ
  have hpi : star (p i) = p i := congr_fun hp i
  simp only [Complex.star_def] at *
  rw [map_sub, map_one, ← Complex.exp_conj]
  congr 1
  simp [hpi]

/-- `n` true differences with a pre-block loss of strip width. Real
    coefficient packets, `size` is the sum of the absolute values. -/
theorem real_difference_division (I : Type) [Fintype I] [DecidableEq I]
    (n : ℕ) (σ : ℝ) (hs : 0 < σ) :
    ∃ η K : ℝ, 0 < η ∧ η ≤ σ ∧ 0 ≤ K ∧
      ∀ (A : ℝ), 0 ≤ A → ∀ f : Shift I → ℝ, Width σ A f →
        Rays n (Laurent.read (fun x => (f x : ℂ)) ∘ axes) →
        ∃ g : (Fin n → I) → Shift I → ℝ,
          (∀ b, Width η (A*K) (g b)) ∧
          ∀ p : Phase I, star p = p →
            Laurent.read (fun x => (f x : ℂ)) p =
              ∑ b : Fin n → I, (∏ i, divZ (b i) p) *
                Laurent.read (fun x => (g b x : ℂ)) p := by
  obtain ⟨w,K,hw,hw',hK,H⟩ := layers I n hs
  let η := w/4
  have hη : 0 < η := by unfold η; positivity
  have he : η + η < w := by unfold η; linarith
  let D := (2*((1+η)/η))^(Fintype.card I)
  refine ⟨η,K*D,hη,by linarith,mul_nonneg hK (by unfold D; positivity),?_⟩
  intro A ha f hf hr
  let F (p : Phase I) := Laurent.read (fun x => (f x : ℂ)) p
  obtain ⟨g,hg,Hg⟩ := H A ha F (Firm.of_series
    (by simpa only [Width,Complex.norm_real] using hf) hs) hr
  let Q b := Laurent.market (g b) 0
  have hQ b : Width η (A*(K*D)) (Q b) := by
    rw [← mul_assoc]; exact (hg b).1.issues (hg b).2 η η hη.le hη he
  refine ⟨fun b x => (Q b x).re, fun b => Work.F07.widthRealPart (hQ b), fun p hp => ?_⟩
  have hn : star (-p) = -p := by rw [star_neg,hp]
  let d (b : Fin n → I) (p : Phase I) := ∏ i, divZ (b i) p
  have hh b : Laurent.read (fun i => ((Q b i).re : ℂ)) p =
      (g b p + star (g b (-p)))/2 := by
    rw [Work.F07.readRealPart (hQ b) hη hp]
    unfold Q
    rw [(hg b).1.paints (hg b).2 p ((hg b).in_range hp),
        (hg b).1.paints (hg b).2 _ ((hg b).in_range hn)]
  symm
  simp_rw [hh, ← mul_div_assoc, mul_add]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hr : ∀ b, star (d b (-p)) = d b p := by
    intro b
    simp only [d, star_prod, divZ_neg _ _ hp]
  have hy : (∑ b : Fin n → I, d b p * star (g b (-p))) = F p := by
    rw [show F p = star (F (-p)) from (readRealKernel_neg f p hp).symm,
        Hg _ (Work.F07.realStrip _ hw hn), star_sum]
    exact sum_congr rfl fun b _ => by
      change _ = star (d b (-p)*g b (-p)); rw [star_mul,hr b,mul_comm]
  change (_ + (∑ b : Fin n → I, d b p * star (g b (-p))))/2 = F p
  rw [hy, ← Hg p (Work.F07.realStrip _ hw hp)]
  ring

section Rows

variable {α β γ I : Type}

/-- Order of a zero of the Fourier matrix at zero momentum. -/
def ZeroOrder (n : ℕ) (R : Row α β) :=
    ∀ i j, Stationary.Rays n (fun p : Corn Axis => R.read (axes p) i j)

def differenceList {n : ℕ} (b : Fin n → Axis) := List.ofFn b
lemma difference_length {n : ℕ} (b : Fin n → Axis) : (differenceList b).length=n := by simp [differenceList]
lemma list_product {n : ℕ} (b : Fin n → Axis) (p : Momentum) :
    listChip p (differenceList b) = ∏ i, divZ (b i) p := by
  induction n with
  | zero => simp [listChip,differenceList]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    simp only [differenceList,List.ofFn_succ,listChip,List.map_cons,List.prod_cons]
    congr 1
    exact ih (fun i => b i.succ)

def rowSum [Fintype I] (R : I → Row α β) : Row α β := fun i j z => ∑ k, R k i j z

lemma rowSum_strip [Fintype I] {R : I → Row α β} {η A : ℝ} (h : ∀ i, (R i).strip η A) :
    (rowSum R).strip η (Fintype.card I * A) := fun i j => width_sum_finite fun k => h k i j
lemma rowSum_safe [Fintype I] {R : I → Row α β} (h : ∀ i, (R i).safe) :
    (rowSum R).safe := by
  intro i j
  exact (show Summable ((rowSum R) i j) from summable_sum fun k _ => (h k i j).of_norm).norm

lemma rowSum_acts [Fintype I] {R : I → Row α β} (h : ∀ i, (R i).safe) (c : Side) :
    (rowSum R).acts c = ∑ i, (R i).acts c := by
  ext ⟨x,i⟩ ⟨y,j⟩
  rw [Matrix.sum_apply]
  change sift (fun z => ∑ k, R k i j z) c x y = ∑ k, sift (R k i j) c x y
  exact sift_sum_finite (fun k => (h k i j).of_norm) ..

lemma rowSum_read [Fintype I] {R : I → Row α β} (h : ∀ i, (R i).safe) {p : Momentum} (hp : physical p) :
    (rowSum R).read p = ∑ i, (R i).read p := by
  ext i j
  rw [Matrix.sum_apply]
  exact Next.Free.real_sum (m:=I) Finset.univ (a:=fun k => R k i j) (fun k _ => h k i j) hp

theorem row_division (α β : Type) [Fintype α] [Fintype β] [DecidableEq β]
    (d : ℕ) (σ : ℝ) (hs : 0 < σ) :
    ∃ η K : ℝ, 0 < η ∧ η ≤ σ ∧ 0 ≤ K ∧
      ∀ (A : ℝ), 0 ≤ A → ∀ R : Row α β, R.strip σ A → ZeroOrder d R →
      ∃ T : (Fin d → Axis) → Row α β,
        (∀ i, (T i).strip η (A*K)) ∧
        R=rowSum (fun i => composeRows (T i) (pathJet β (differenceList i))) := by
  obtain ⟨η,K,he,hg,hK,H⟩ := real_difference_division Axis d σ hs
  refine ⟨η,K,he,hg,hK,fun A ha R hr hv => ?_⟩
  choose T hT H' using fun i j => H A ha (R i j) (hr i j) (hv i j)
  let Q (j) : Row α β := fun i k => T i k j
  have hQ p : Whole (Q p) := ⟨_,_,he,fun i j => hT i j p⟩
  let F (j) := composeRows (Q j) (pathJet β (differenceList j))
  have hF j : (F j).safe := ((hQ j).prod (jet_whole ..)).safe
  refine ⟨Q,fun p i j => hT i j p,?_⟩
  have hm : R.safe := Row.rights _ _ hr hs.le
  change R=rowSum F
  apply bank_injective hm (rowSum_safe hF)
  apply acts_of_cube hm (rowSum_safe hF)
  intro p hp
  rw [rowSum_read hF hp.1]
  ext i j
  rw [Matrix.sum_apply]
  refine (H' i j p hp.1).trans (sum_congr rfl ?_)
  intro a _
  unfold F
  rw [(hQ a).read (jet_whole ..) hp.1, jet_read _ _ hp.1,list_product,Matrix.mul_smul,Matrix.mul_one]
  rfl

end Rows
end YM.RG08
