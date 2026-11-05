import YM.Next.EXTRACTION.Detector
import YM.Next.FOUNDATIONS.Reorient
import YM.Next.FOUNDATIONS.Split
import YM.Next.FOUNDATIONS.TestBounds
import YM.Push.LOCAL_SPLITTING.Orientation
import YM.Work.G08

/-!
# Canonical extraction at an anchor before indicator compensation

One read (including on products), independent of the norm parameters. True left
jets on the original good domain. Signed pull, ordinary conjugation, linearity
on regular input families. Finite tested-direction sufficient estimates on the
weighted coordinates, to permit sharper estimates on the coordinate than are
needed on the bulk regular terms. No extraction from a masked Taylor fit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Labels Next.Foundations Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {n : Side} {d : ℕ}
section Size
variable (F : Labels.Frame G d)

theorem norm_le_size (x : F.Coeff) : ‖x‖ ≤ F.coeffSize x :=
  (pi_norm_le_iff_of_nonneg (size_nonneg F x)).mpr fun i => Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ i)

theorem size_le_norm (x : F.Coeff) : F.coeffSize x ≤ (F.extra+1:ℕ)*‖x‖ := by
  simpa only [Labels.Frame.coeffSize,nsmul_eq_mul,Fintype.card_fin] using Pi.sum_norm_apply_le_norm (G:=fun _ : F.Index => ℂ) x

theorem core_split (v : F.Coeff) : v = v 0 • F.e0 + F.core v := by
  funext i; by_cases he : i=0 <;> simp [Labels.Frame.e0, Labels.Frame.core,Function.update, he]

theorem core_star (v : F.Coeff) : F.core (star v) = star (F.core v) := by
  funext i; by_cases he : i=0 <;> simp [Labels.Frame.core,Function.update,he]

@[simp] theorem act_e0 (s : Ortho) : F.act s F.e0 = F.e0 := by
  rw [← F.coords_unit, F.act_coords]; congr 1; exact Subtype.ext (map_one (rotated s (G:=G)))

theorem act_at_zero (s : Ortho) (v : F.Coeff) : F.act s v 0 = v 0 := by
  have he (i : F.Index) (hi : i ≠ 0) : F.act s (F.coords (F.basis i)) 0 = 0 := by
    rw [F.act_coords]; apply F.power_coefficient _ (m:=F.grades i) (fun he => ?_)
    · have ht := gradePart_mem (F.grades i) (tensor s (F.basis i))
      rwa [gradePart_turn, gradePart_self _ _ (F.pure i)] at ht
    rw [F.zero_degree] at he
    have h := F.factors_pos i hi; simp [he] at h
  obtain ⟨p,rfl⟩ := F.coords.surjective v
  rw [← F.basis.sum_repr p, map_sum,map_sum, Finset.sum_apply,Finset.sum_apply]; simp only [map_smul,Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne i 0 with h|h
  · rw [h,F.starts_unit,F.coords_unit, act_e0]
  rw [he i h,F.coords_basis i,Pi.single_eq_of_ne h.symm]

theorem core_act (s : Ortho) (v : F.Coeff) : F.act s (F.core v) = F.core (F.act s v) := by
  have h := congr_arg (F.act s) (core_split F v)
  rw [map_add,map_smul,act_e0] at h
  exact add_left_cancel ((h.symm.trans (core_split F _)).trans (by rw [act_at_zero]))

theorem scaled_star (t : ℝ) (v : F.Coeff) : F.scaled t (star v) = star (F.scaled t v) := by
  ext i; simp [mul_comm]
end Size

section Projection
variable {A : Hol G} {o : Site n} {X : Support n} {f g : Config G n → ℂ} {B : BudgetPoint}

open scoped Classical in
/-- Totalized `Π_o`; statements on it will ensure existence (even on wrapping
supports with the specified constant test). No budget parameter or implicit torus
side change in the choice. -/
def project (A : Hol G) (o : Site n) (X : Support n) (f : Config G n → ℂ) (d : ℕ) : Label G d :=
  if h : ∃ p : Label G d, Reads A o X p f then h.choose else 0

theorem project_eq {p : Label G d} (h : Reads A o X p f) : project A o X f d = p := by
  classical
  have he : ∃ q : Label G d, Reads A o X q f := ⟨p,h⟩
  rw [project,dif_pos he]; exact Reads.unique he.choose_spec h

theorem project_reads (A : Hol G) (o : Site n) (h : B.Regular X f) (hk : d ≤ B.order) :
    Reads A o X (project A o X f d) f := by
  obtain ⟨p,hp,_⟩ := exists_read A d o B hk h
  rwa [project_eq hp]

@[simp] theorem project_zero (A : Hol G) (o : Site n) (X : Support n) (d : ℕ) : project A o X 0 d = 0 := by
  apply project_eq
  rw [reads_null_iff]; exact ⟨rfl,fun _ _ => ⟨contDiffAt_const,fun k _ => by simp⟩⟩

theorem project_add (A : Hol G) (o : Site n) (h : B.Regular X f) (hg : B.Regular X g) (hk : d ≤ B.order) :
    project A o X (f+g) d = project A o X f d + project A o X g d := by
  have he := reads_sub (project_reads A o (regular_add h hg) hk) (project_reads A o hg hk)
  simp only [add_sub_cancel_right] at he
  exact eq_add_of_sub_eq (Reads.unique he (project_reads A o h hk))

theorem project_smul (A : Hol G) (o : Site n) (z : ℂ) (h : B.Regular X f) (hk : d ≤ B.order) :
    project A o X (z • f) d = z • project A o X f d := by
  apply project_eq
  have he := project_reads A o h hk
  unfold Reads at *
  split at he <;> rename_i hX
  · rw [if_pos hX]
    intro J; simp only [Pi.smul_apply,SetLike.val_smul,map_smul]
    have ht := he J
    refine ⟨ht.1.const_smul _, ht.2.1.const_smul _, fun k hk => ?_⟩
    rw [iteratedDeriv_fun_const_smul (ht.1.of_le (Nat.cast_le.mpr hk)),iteratedDeriv_fun_const_smul (ht.2.1.of_le (Nat.cast_le.mpr hk)),ht.2.2 k hk]
  simp only [if_neg hX, he,Pi.smul_apply,smul_smul,smul_eq_mul]



variable {F : Labels.Frame G d}

def weighted (A : Hol G) (F : Labels.Frame G d) (o : Site n) (X : Support n) (t : ℝ) (f : Config G n → ℂ) :=
  F.scaled t (F.coords (project A o X f d))

theorem weighted_pull (A : Hol G) (F : Labels.Frame G d) (o b : Site n) (s : Signed) (t : ℝ) (h : B.Regular X f) (hk : d ≤ B.order) (hn : 2 ≤ n.val) :
    weighted A F (turnSites s b o) (X.image (turnSites s b)) t (f ∘ pull s b) = F.act s.ortho (weighted A F o X t f) := by
  unfold weighted
  rw [show ⇑(turnSites s b) = affine s b from rfl, project_eq (reads_pull (b:=b) (project_reads A o h hk) h.sites hn s),← F.act_coords,F.scaling]

theorem weighted_star (A : Hol G) (F : Labels.Frame G d) (o : Site n) (t : ℝ) (h : B.Regular X f) (hk : d ≤ B.order) :
    weighted A F o X t (star f) = star (weighted A F o X t f) := by
  unfold weighted; rw [project_eq (reads_bar (project_reads A o h hk))]
  let v := F.coords (project A o X f d)
  rw [← scaled_star]
  apply congr_arg; convert funext (F.conj_basis v) using 2
  · rw [LinearEquiv.symm_apply_apply]
  · rfl

def readPrice (A : Hol G) (F : Labels.Frame G d) := (price_of_readout A F).choose

theorem readPrice_pos (A : Hol G) (F : Labels.Frame G d) : 1 ≤ readPrice A F := (price_of_readout A F).choose_spec.1

theorem weighted_bound (A : Hol G) (F : Labels.Frame G d) (o : Site n) {c : ℝ} (h : B.Regular X f) (hk : d ≤ B.order) (hP : d ≤ B.power) (hc : B.supBounds o X f c) :
    F.coeffSize (weighted A F o X B.threshold f) ≤ readPrice A F * c :=
  (price_of_readout A F).choose_spec.2 n o X B f c hk hP h hc _ (project_reads A o h hk)
end Projection

section Detector
variable (F : Labels.Frame G d)

abbrev Probe (G : Gauge) (d : ℕ) := Jet G × Fin (d+1)
def runProbe (i : Probe G d) : F.Coeff →L[ℂ] ℂ :=
  (((i.2.val.factorial : ℂ) • ((read i.1).toLinearMap ∘ₗ (tier i.2.val) ∘ₗ (localFields G d).subtype ∘ₗ F.coords.symm.toLinearMap)) : F.Coeff →ₗ[ℂ] ℂ).toContinuousLinearMap

theorem runProbe_eq (i : Probe G d) (v : F.Coeff) :
    runProbe F i v = iteratedDeriv i.2.val (fun t => read (scaleJet i.1 t) (F.coords.symm v).val) 0 := by
  rw [deriv_read,Complex.real_smul]; change (i.2.val.factorial : ℂ) • read i.1 _ = _; simp

open scoped Classical in
def sample (H : Hol G) (o : Site n) (X : Support n) (θ : ℝ) (f : Config G n → ℂ) (i : Probe G d) :=
  if Nonwrapping X o then iteratedDeriv i.2.val (f ∘ H.testLinks d o (θ • i.1)) 0
  else if i.2.val = 0 then f 1 else 0

theorem sample_eq (H : Hol G) (o : Site n) {B : BudgetPoint} {X : Support n} (θ : ℝ) {f : Config G n → ℂ} (h : B.Regular X f) (hk : d ≤ B.order) (i : Probe G d) :
    sample H o X θ f i = runProbe F i (weighted H F o X θ f) := by
  have hp := project_reads H o h hk
  rw [runProbe_eq]; simp_rw [weighted,read_frame_scaled, LinearEquiv.symm_apply_apply]
  unfold sample; split <;> rename_i hx
  · rw [Reads,if_pos hx] at hp
    rw [show (fun t : ℝ => read (θ • scaleJet i.1 t) (project H o X f d).val) = fun t => read (scaleJet (θ • i.1) t) (project H o X f d).val from funext fun t => by
      rw [show θ • scaleJet i.1 t = scaleJet (θ • i.1) t from funext fun j => smul_comm θ (t^(j+2)) (i.1 j)]]
    exact (hp (θ • i.1)).2.2 _ (Nat.le_of_lt_succ i.2.isLt)
  rw [project_eq (by simp only [Reads,if_neg hx] : Reads H o X (f 1 • unit G d) f)]
  simp [unit,iteratedDeriv_const]

theorem probe_budget : ∃ (S : Finset (Probe G d)) (C : ℝ), 1 ≤ C ∧ ∀ (x : F.Coeff) (c : ℝ), 0 ≤ c →
    (∀ i∈S, ‖runProbe F i x‖ ≤ c) → F.coeffSize x ≤ C*c := by
  classical
  let U (i : Probe G d × ℕ) := {x : F.Coeff | ‖x‖ < (i.2 : ℝ)*‖runProbe F i.1 x‖}
  have ho (i) : IsOpen (U i) := isOpen_lt (by fun_prop) (by fun_prop)
  have he {x : F.Coeff} (hx : x ≠ 0) : ∃ i : Probe G d, runProbe F i x ≠ 0 := by
    contrapose! hx
    apply F.coords.symm.injective
    refine jet_test_ext _ _ fun J k hk => ?_
    rw [← show ((J,⟨k,Nat.lt_succ_of_le hk⟩) : Probe G d).2.val = k from rfl, ← runProbe_eq, ← runProbe_eq, hx,map_zero]
  have hS : Metric.sphere (0 : F.Coeff) 1 ⊆ ⋃ i, U i := by
    intro x hx
    have hne : x ≠ 0 := by intro ha; simp [ha] at hx
    obtain ⟨i,hi⟩ := he hne
    obtain ⟨m,hm⟩ := exists_nat_gt (‖x‖ / ‖runProbe F i x‖)
    exact Set.mem_iUnion.mpr ⟨(i,m), (div_lt_iff₀ (norm_pos_iff.mpr hi)).mp hm⟩
  obtain ⟨T,hT⟩ := (isCompact_sphere (0 : F.Coeff) 1).elim_finite_subcover U ho hS
  let C := T.sup Prod.snd
  refine ⟨T.image Prod.fst, 1+(F.extra+1:ℕ)*(C:ℝ), le_add_of_nonneg_right (by positivity),fun x c hc ht => ?_⟩
  apply (size_le_norm F x).trans
  have H : ‖x‖ ≤ (C:ℝ)*c := by
    by_cases hx : x = 0
    · rw [hx,norm_zero]; positivity
    let r : ℂ := ((‖x‖⁻¹ : ℝ) : ℂ)
    have hr : r • x ∈ Metric.sphere (0 : F.Coeff) 1 := by simp [norm_smul,r,hx]
    obtain ⟨i,hi,hx'⟩ := Set.mem_iUnion₂.mp (hT hr)
    change ‖r • x‖ < _ at hx'
    simp only [norm_smul,map_smul] at hx'
    apply (lt_of_mul_lt_mul_left (a:=‖r‖) (hx'.trans_eq (mul_left_comm ..)) (norm_nonneg _)).le.trans
    exact mul_le_mul (by exact_mod_cast Finset.le_sup (f:=Prod.snd) hi) (ht _ (Finset.mem_image_of_mem _ hi)) (norm_nonneg _) (by positivity)
  rw [add_mul,one_mul,mul_assoc]
  exact le_trans (mul_le_mul_of_nonneg_left H (by positivity)) (le_add_of_nonneg_left hc)
end Detector
end YM.Push.Local
