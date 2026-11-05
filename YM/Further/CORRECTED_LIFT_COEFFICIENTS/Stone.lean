import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Building
/-!
# Replay the actual native board, and pay for it!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Stone
open Filter Function Set Lattice Wilson Labels RG Cells Source Source.Drops WilsonStartup
open Work Push.Corrected Push.Uniform Push.CutoffProjectors Collapse PathCost Building Growth Fund Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side} {m l : ℕ}

variable (G) (h : distant n m)
abbrev Item := (i : nails n m) × Fin (sill G h i).length
def address (i : Item G h) := ((sill G h i.1).get i.2)
lemma dated (i : Item G h) : (address G h i).1.walk.length ≤ wall m := role G h i.1 _ (List.get_mem ..)

abbrev high := Fintype.card (Item G h)
abbrev Parse := Panel G (high G h)
def path (i : Fin (high G h)) := (address G h ((Fintype.equivFin _).symm i)).1

def seriesL (i : Item G h) : Parse G h →L[ℝ] G.Color :=
    (address G h i).2.val • ContinuousLinearMap.proj ((Fintype.equivFin _) i)
omit h in
private lemma series_cost {b : ℕ} (i : Fin b) (t : ℝ) (ht : t=1 ∨ t=-1) :
    ‖(t • ContinuousLinearMap.proj i : Panel G b →L[ℝ] G.Color)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  change ‖t • v i‖ ≤ _
  rw [norm_smul, show ‖t‖=1 by rcases ht with ht|ht <;> simp [ht],one_mul,one_mul]; exact norm_le_pi_norm ..
def layAt (A : nails n m) (x : Parse G h) :=
    (List.ofFn fun j => WilsonStartup.recover G (seriesL G h ⟨A,j⟩ x)).prod

lemma lays (A : nails n m) (U : Config G n) : layAt G h A (fun j => (path G h j).atSite U 0) =
    ((sill G h A).map (lay (expandAt 0 U))).prod := by
  unfold layAt; apply congr_arg List.prod
  conv_rhs => rhs; rw [← List.ofFn_get (sill G h A)] -- avoid dependent
  rw [List.map_ofFn]
  apply congr_arg List.ofFn; funext j
  let b : Item G h := ⟨A,j⟩
  change WilsonStartup.recover G ((address G h b).2.val • (path G h ((Fintype.equivFin _) b)).atSite U 0) = lay (expandAt 0 U) (address G h b)
  unfold path; rw [Equiv.symm_apply_apply]; rfl

private lemma ofPrices {ι : Type} (L : List ι) (u : ι→G.El) :
    G.mat (L.map u).prod = (L.map (G.mat ∘ u)).prod := by
  induction L <;> simp_all
@[simp] lemma lay_zero (A : nails n m) : layAt G h A 0=1 := by
  unfold layAt; simp_rw [map_zero]; simp

def window (x : Parse G h) : Config G n := fun i => if ha : i∈ nails n m then layAt G h ⟨i,ha⟩ x else 1
@[simp] lemma vacancy : window G h 0=1 := by
  funext i; unfold window; split_ifs <;> simp

def tally (x : Parse G h) : Directions G n := fun i => G.plog (G.mat (window G h x i))
@[simp] lemma cleared : tally G h 0=0 := by funext i; simp [tally]

private lemma hall (A : nails n m) (x : Parse G h) :
    let i j (x : Parse G h) := G.mat (WilsonStartup.recover G (seriesL G h ⟨A,j⟩ x))
    G.mat (layAt G h A x) = (List.ofFn i).prod x := by
  intro i; unfold layAt
  simp_rw [List.ofFn_eq_map]
  rw [ofPrices]; generalize List.finRange (sill G h A).length = L
  induction L with
  | nil => simp
  | cons z L ih => simp only [List.map_cons,List.prod_cons, Pi.mul_apply]; rw [ih]; rfl

-- Upper bound without Gauge.card leakage. Just needs M/l here, no
-- interaction with θ yet. Preserve all multilinear costs.
omit h in
private lemma lays_bound (l : ℕ) : ∃ b : Fund, ∀ R : ℝ, 1 ≤ R → ∀ n m, ∀ h : distant n m,
    wall m^2 ≤ R → ∀ A : nails n m, Allows l (fun x => G.mat (layAt G h A x)) 0 (b.rents R) := by
  obtain ⟨a,ha⟩ := limited (recover_analytic G) l
  obtain ⟨c,hc⟩ := combines l a (flat 1)
  obtain ⟨b,hb⟩ := series G.Mat l c
  refine ⟨b,fun R u n m h he A => ?_⟩
  have hh : ∀ i : Fin (sill G h A).length,
      Allows l (fun x => G.mat (WilsonStartup.recover G (seriesL G h ⟨A,i⟩ x))) 0 (c.rents R) := by
    intro i; let S := seriesL G h ⟨A,i⟩; apply Allows.mono _ (hc R u)
    apply Allows.comp (f:=S) (g:=fun x => G.mat (WilsonStartup.recover G x))
    · rw [map_zero]; exact ha R u
    exact allows_linear ((series_cost G _ _ (address G h ⟨A,i⟩).2.property).trans (cash ..)) (by rw [map_zero,norm_zero]; exact (gain _ u).le)
  let L := List.ofFn (fun j (x : Parse G h) => G.mat (WilsonStartup.recover G (seriesL G h ⟨A,j⟩ x)))
  rw [show (fun x => G.mat (layAt G h A x))=L.prod from funext (hall G h A)]
  have hv : ((sill G h A).length:ℝ) ≤ (wall m:ℝ)^2 := by exact_mod_cast load G h A
  refine hb _ R u L (by rw [show L.length=(sill G h A).length from List.length_ofFn]; exact hv.trans he) ?_
  intro f hf; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf; exact ⟨by simp, hh i⟩

omit h in
lemma white (l : ℕ) : ∃ b : Fund, ∀ R : ℝ, 1 ≤ R → ∀ n m, ∀ h : distant n m,
    (wall m:ℝ)^2 ≤ R → ∀ i, Allows l (fun x => G.mat (window G h x i)) 0 (b.rents R) := by
  obtain ⟨a,ha⟩ := lays_bound G l
  refine ⟨bump (flat ‖(1:G.Mat)‖) a,fun R u n m h he i => ?_⟩
  unfold window; split
  · exact (ha R u n m h he _).mono ((le_add_of_nonneg_left ((flat _).gain u).le).trans (daily _ _ R u))
  exact allows_const _ (show ‖G.mat 1‖ ≤ _ from (cash ‖(1:G.Mat)‖ R).trans ((le_add_of_nonneg_right (gain a u).le).trans (daily _ _ R u)))

omit h in
theorem account (l : ℕ) : ∃ b : Fund, ∀ R : ℝ, 1 ≤ R → ∀ n m, ∀ h : distant n m,
    (wall m:ℝ)^2 ≤ R → Allows l (tally G h) 0 (b.rents R) := by
  obtain ⟨a,ha⟩ := limited G.plog_diff l
  obtain ⟨b,hb⟩ := white G l
  obtain ⟨c,hc⟩ := combines l a b
  refine ⟨c,fun R u n m h he => allows_pi (gain c u).le fun i => ?_⟩
  apply Allows.mono _ (hc R u); refine Allows.comp (f:=fun x => G.mat (window G h x i)) (g:=G.plog) ?_ (hb R u n m h he i)
  rw [vacancy,Pi.one_apply,G.mat_one]; exact ha R u

lemma regular : ContDiffAt ℝ ω (tally G h) 0 := by
  obtain ⟨a,ha⟩ := account G 0
  exact (ha _ (le_max_left 1 ((wall m:ℝ)^2)) n m h (le_max_right ..)).analytic

lemma cleans : ∀ᶠ x in 𝓝 (0:Parse G h), increment 1 (tally G h x)=window G h x := by
  obtain ⟨a,ha⟩ := white G 0
  have hz i := (ha (max _ _) (le_max_left 1 _) n m h (le_max_right ..) i).analytic.continuousAt
  have hh i : Tendsto (fun x => window G h x i) (𝓝 0) (𝓝 1) := by
    have hp : ContinuousAt (fun x => window G h x i) 0 :=
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr (hz i)
    simpa only [vacancy,Pi.one_apply] using hp.tendsto
  filter_upwards [eventually_all.mpr fun i => (hh i).eventually G.plog_right] with x hx
  funext i; change G.lieExp _ * (1:G.El) = _; rw [mul_one]; exact hx i

private lemma stimulus : Continuous (fun U : Config G n => (show Parse G h from fun j => Slot.atSite (path G h j) U 0)) := by
  apply continuous_pi; intro i; exact ((path G h i).cont).comp (continuous_pi (fun i => continuous_apply _))

variable (P : BudgetPoint) (l)
def see : Board G n P l where
  size := high G h
  leg := path G h
  cube := lot n m
  replay X := P.threshold⁻¹ • tally G h (P.threshold • X)
  empty := by simp
  nice := by
    let L := P.threshold • ContinuousLinearMap.id ℝ (Parse G h)
    refine ((ContDiffAt.comp (f:=L) (g:=tally G h) _ ?_ L.contDiff.contDiffAt).const_smul P.threshold⁻¹)
    rw [map_zero]; exact (regular G h).of_le le_top
  fits i := vacancy_at h _ (by have := dated G h ((Fintype.equivFin _).symm i); unfold path; unfold limitsight; omega)
  authentic := by
    let I (U : Config G n) : Parse G h := fun i => (path G h i).atSite U 0
    have he : I 1=0 := by funext j; unfold I; rw [Slot.atSite,show expandAt 0 (1:Config G n)=1 from rfl]; exact G02_address _ -- helper below
    filter_upwards [hangs (G:=G) h,(show Tendsto I (𝓝 1) (𝓝 0) from he ▸ (stimulus G h).tendsto 1).eventually (cleans G h)] with U hu hx
    obtain ⟨T,hT⟩ := hu
    change ∃ T, Agrees _ _ (increment 1 (P.threshold • P.threshold⁻¹ • tally G h (P.threshold • P.threshold⁻¹ • I U)))
    simp_rw [smul_inv_smul₀ P.threshold_pos.ne']; rw [hx]
    refine ⟨T,fun i hi hj => ?_⟩
    let A : nails n m := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hj⟩⟩
    rw [show gauge T U i=_ from hT A, ← lays G h A U]
    unfold window; rw [dif_pos (show i∈nails n m from A.property)]
where
  G02_address (q : Slot) : q.eval (1:CoverConfig G)=0 := by simp [Slot.eval,faceValue,Pressure.one]
end YM.Further.CorrectedLift.Stone
