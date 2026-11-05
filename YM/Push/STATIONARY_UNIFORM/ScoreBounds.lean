import YM.Push.STATIONARY_UNIFORM.Entries
import YM.Push.STATIONARY_UNIFORM.Prediction

/-! # Actual unmasked block scores: analytic sup ball with sitewise derivative estimates

Keep the sums as sums (no dividing by volume). Pay a weaker rate (but still
with explicit L dependence and pre-L constants) in `Scatter`. Does not
assert estimates on the iteration sending these path coefficient arrays to
new path arrays or on determinant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior Work.F02
open Next.Fluctuations Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge} {c f : Side} {ratio : Ratio c f} {S : StepData c f} {μ C Λ Z Z' K D δ W η : ℝ} {n k : ℕ}
    {p : Clip} {R : PathData G}

section Main
variable (B : Forest ratio)

def SquarePay (G : Gauge) (n : ℕ) (Z μ C Z' : ℝ) := 0<Z' ∧ ∀ v : G.Color, ‖v‖ ≤ C * rootsCost G Z μ n →
  Allows n (fun z : G.Color => ‖z‖^2/2) v Z'
lemma square_pay (G : Gauge) (n : ℕ) (Z μ C : ℝ) : ∃ Z' : ℝ, SquarePay G n Z μ C Z' := by
  obtain ⟨A,hA,ha⟩ := exists_allows (isCompact_closedBall 0 (C*rootsCost G Z μ n))
    (fun i (_ : i∈closedBall (0:G.Color) _) => ((contDiff_norm_sq (𝕜:=ℝ) (E:=G.Color) (n:=ω)).div_const 2).contDiffAt (x:=i)) n
  exact ⟨1+A,by positivity,fun i hi => (ha i (by simpa using hi)).mono (le_add_of_nonneg_left zero_le_one)⟩

def quadCost (G : Gauge) (n : ℕ) (Z Z' μ C : ℝ) (p : Clip) (L : Side) :=
  let N := ∑ i∈Finset.range (n+1), (Fintype.card (OrderedFinpartition i):ℝ)
  |p.direct| * priceCost G (travelCost G n 4 (fineCost G n Z)) * Real.exp (entryWidth n L μ*((n*signedCost L 4:ℕ):ℝ)) +
    N * (Z'*(1+C*rootsCost G Z μ n)^n)

def quad (p : Clip) (R : PathData G) (s : Signed) (i : Face (Per f)) (x : Positions (Joint B G)) :=
  p.direct * G.price (faceValue (signedFine B x s) i)+‖R.ell (signedFine B x s) i‖^2 / 2



lemma eye (h : R.Bounds p μ C Λ) (hs : PaintSupply G n Z) (hQ : SquarePay G n Z μ C Z') (s : Signed)
    (i : Face (Per f)) (x : Positions (Joint B G)) (hx : x∈ball 0 1) :
    ContDiffAt ℝ ω (quad B p R s i) x ∧ Beacon (address B G) (entryWidth n ratio.count μ) n (quad B p R s i) (affine s 0 i.1) x
      (quadCost G n Z Z' μ C p ratio.count) := by
  let Q z := quad B p R s i z
  let F z := p.direct * G.price (faceValue (signedFine B z s) i)
  let A (z : Positions (Joint B G)) := signedFine B z s
  let H z := R.ell (A z) i
  have he : ‖x‖ ≤ 1 := (show ‖x‖ < 1 by simpa using hx).le
  have ha j := signed_supply B s hs x he j
  have hf : Allows n F x (|p.direct| * priceCost G (travelCost G n 4 (fineCost G n Z))) :=
    (Allows.price (f:=fun z => faceValue (signedFine B z s) i) (travel_jets (U:=A) ha (w:=square _ _) i.1 (a:=4) (by simp [square]))).smul _
  have hh : Requests univ F (address B G) (affine s 0 i.1) (signedCost ratio.count 4) := by
    intro u _ v _ hh; unfold F faceValue; rw [signed_read B s i.1 (square i.2.val.1 i.2.val.2) (le_refl _) hh]
  have hy := hf.beacon hh univ_mem (width_positive h.width n ratio.count).le
  have ht := ell_beacon B s p R h hs x hx i
  let M := C*rootsCost G Z μ n
  have hT := ht 0 (Nat.zero_le _) Fin.elim0
  simp only [entry,spanSites, Finset.univ_eq_empty,Finset.sum_empty,Nat.cast_zero, mul_zero, Real.exp_zero,mul_one,iteratedFDeriv_zero_apply] at hT
  have hM : 0≤M := (norm_nonneg _).trans hT
  have hH : ContDiffAt ℝ ω H x := Work.F02.ell_contDiffAt h _ (fun j => (ha j).analytic)
  have hz := (hQ.2 (H x) hT).analytic.comp x hH
  exact ⟨hf.analytic.add hz, hy.add hf.analytic hz (ht.comp (g:=fun v => ‖v‖^2/(2:ℝ)) hH hM (hQ.2 _ hT))⟩

lemma label_analytic (T : ℕ → Atom G k) (hm : 0<μ) (h : SumBudget (fun i => (T i).budget μ) C) (s : Signed)
    (hp : PaintSupply G n Z) (i : Site f) (x : Positions (Joint B G)) (he : x∈ball 0 1) :
    ContDiffAt ℝ ω (fun z => ∑' j, (T j).unmasked (signedFine B z s) i) x := by
  let A (z : Positions (Joint B G)) := signedFine B z s
  let F z := physical (A z)
  let L (M : Ambient G f) := ∑' j, atomExt (T j) i M
  have hh : ContDiffAt ℝ ω (fun z => Complex.reCLM (L (F z))) x :=
    Complex.reCLM.contDiff.contDiffAt.comp (f:=L ∘ F) x (((atomExt_series hm h i (A x)).contDiffAt.restrict_scalars ℝ).comp (f:=F) x
      (physical_contDiffAt (A:=A) (fun j => (signed_supply B s hp x (show ‖x‖ ≤ 1 from (show ‖x‖<1 by simpa using he).le) j).analytic)))
  have ht z : Complex.reCLM (L (F z)) = ∑' j, (T j).unmasked (signedFine B z s) i := by
    unfold L F; rw [atomExt_real hm h]; rfl
  simpa only [ht] using hh

def named (s : Signed) (p : Clip) (R : PathData G) (i : Site f) (z : Positions (Joint B G)) :=
  ((∑ j, quad B p R s (i,j) z) + ∑' j, (R.cubic j).unmasked (signedFine B z s) i)+
    ∑' j, (R.quartic j).unmasked (signedFine B z s) i

def faceBudget (G : Gauge) (n : ℕ) (Z Z' μ C : ℝ) (p : Clip) (L : Side) :=
  (Fintype.card PlaqAxes:ℝ)*quadCost G n Z Z' μ C p L + C*atomCost G Z μ n 3 + C*atomCost G Z μ n 4

lemma named_cost (h : R.Bounds p μ C Λ) (hs : PaintSupply G n Z) (hQ : SquarePay G n Z μ C Z') (s : Signed)
    (i : Site f) (x : Positions (Joint B G)) (hx : x∈ball 0 1) :
    ContDiffAt ℝ ω (named B s p R i) x ∧ Beacon (address B G) (entryWidth n ratio.count μ) n
      (named B s p R i) (affine s 0 i) x (faceBudget G n Z Z' μ C p ratio.count) := by
  have hE (j : PlaqAxes) := eye B h hs hQ s (i,j) x hx
  let F j := quad B p R s (i,j)
  let g (z) := ∑ j, F j z
  have hf : ContDiffAt ℝ ω g x := ContDiffAt.sum (s:=Finset.univ) (f:=F) fun j _ => (hE j).1
  let t (z : Positions (Joint B G)) := ∑' j, (R.cubic j).unmasked (signedFine B z s) i
  let u (z : Positions (Joint B G)) := ∑' j, (R.quartic j).unmasked (signedFine B z s) i
  have ht : ContDiffAt ℝ ω t x := label_analytic B R.cubic h.width h.three s hs i x hx
  have hu : ContDiffAt ℝ ω u x := label_analytic B R.quartic h.width h.four s hs i x hx
  let M := quadCost G n Z Z' μ C p ratio.count
  have he : Beacon (address B G) (entryWidth n ratio.count μ) n g (affine s 0 i) x ((Fintype.card PlaqAxes:ℝ)* M) := by
    have he := beacon_sum (f:=F) (s:=Finset.univ) (C:=fun _ => M) (y:=affine s 0 i)
      (fun j _ => (hE j).2) (fun j _ => (hE j).1)
    rwa [Finset.sum_const, Finset.card_univ,nsmul_eq_mul] at he
  exact ⟨(hf.add ht).add hu,(he.add hf ht (atom_beacon B s h.width h.three hs x hx i)).add (hf.add ht) hu (atom_beacon B s h.width h.four hs x hx i)⟩

lemma price_named (p : Clip) (R : PathData G) (x : Positions (Joint B G)) :
    mainTerm p R (fine G B x) = Patch.average fun s : Signed => ∑ i, named B s p R i x := by
  unfold mainTerm Patch.average named uncut quadratic; simp_rw [quad,Fintype.sum_prod_type, Finset.sum_add_distrib]
  rfl

def mainCost (G : Gauge) (n : ℕ) (Z Z' μ C : ℝ) (p : Clip) (L : Side) :=
  faceBudget G n Z Z' μ C p L * countCost (entryWidth n L μ/2)

lemma main_beacons (h : R.Bounds p μ C Λ) (hs : PaintSupply G n Z) (hQ : SquarePay G n Z μ C Z') (x : Positions (Joint B G))
    (hx : x∈ball 0 1) : ContDiffAt ℝ ω (fun z => mainTerm p R (fine G B z)) x ∧
    Scatter (address B G) (weaker n (entryWidth n ratio.count μ)) n (fun z => mainTerm p R (fine G B z)) x
      (mainCost G n Z Z' μ C p ratio.count) := by
  let L := address B G
  let a := entryWidth n ratio.count μ
  let M := faceBudget G n Z Z' μ C p ratio.count
  let F s z := ∑ i, named B s p R i z
  have hf (s i) := named_cost B h hs hQ s i x hx
  have he (s : Signed) : ContDiffAt ℝ ω (F s) x := ContDiffAt.sum (s:=Finset.univ) (fun i _ => (hf s i).1)
  have hM : 0≤M := by
    have hu := (hf 1 0).2 0 (Nat.zero_le _) Fin.elim0
    simp only [spanSites, Finset.univ_eq_empty, Finset.sum_empty,Nat.cast_zero, mul_zero, Real.exp_zero,mul_one] at hu; exact (norm_nonneg _).trans hu
  have hp := width_positive h.width n ratio.count
  have ht (s : Signed) : Scatter L (weaker n a) n (F s) x (M*countCost (a/2)) := by
    have hi : Injective (affine (R:=Per f) s 0) := fun i j h => by
      unfold affine at h
      have he := add_right_cancel h; simpa using congr_arg s⁻¹.act he
    have hh := scatter (Multiplicity.injective hi) (fun i => (hf s i).1) (fun i => (hf s i).2) hp hM
    rwa [Nat.cast_one,mul_one] at hh
  let q : ℝ := Fintype.card Signed; have hQ' : 0 < q := by unfold q; positivity
  have hy := ContDiffAt.sum (s:=Finset.univ) fun i _ => he i
  simp_rw [price_named, Patch.average]
  refine ⟨hy.const_smul q⁻¹,?_⟩
  have hb := (scatter_sum (s:=Finset.univ) (fun i _ => he i) (fun i _ => ht i)).smul hy q⁻¹
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul, abs_of_nonneg (inv_pos.mpr hQ').le,show (Fintype.card Signed:ℝ)=q from rfl, inv_mul_cancel_left₀ hQ'.ne'] at hb
  exact hb
end Main

section Actual
variable (B : Forest S.ratio) (t : S.Choices)

def priced (p : Clip) (R : PathData G) := uncurry (tested B t p R) ∘ paint B G

def noiseEntry (G : Gauge) (n : ℕ) (Z K W μ : ℝ) (P : Patch) :=
  priceCost G (2^n * outerCost G (n+1) Z *
    composeCost n W (connectorCost P G n K (fineCost G (n+1) Z))) *
      Real.exp (entryWidth n P.L μ * ((n * noiseCost P:ℕ):ℝ))

def allCost (G : Gauge) (n : ℕ) (Z Z' μ C K W : ℝ) (p : Clip) (P : Patch) (Q : KernelChoices) :=
  1+ |mainCost G n Z Z' μ C p P.L + |Q.penalty| *
    (noiseEntry G n Z K W μ P * (Fintype.card Axis:ℝ) * countCost (entryWidth n P.L μ/2))|

lemma penalized (hS : S.patch.Branches S.kernel G) (n : ℕ) (hn : 2 ≤ n) (hP : PaintSupply G (n+1) Z)
    (hE : ExpReceipt G (n+1) K) (hL : LogReceipt G D δ) (hF : FocusReceipt G n W η) (hμ : 0<μ)
    (x : Positions (Joint B G)) (hx : x∈ball 0 (predictionRadius S.patch G S.kernel n K (fineCost G (n+1) Z) D δ η)) :
    let a := entryWidth n S.patch.L μ
    let F z := noiseTaylor S (outer G B z) (fine G B z) t
    ContDiffAt ℝ ω F x ∧ Scatter (address B G) (weaker n a) n F x
      (|S.kernel.penalty| * (noiseEntry G n Z K W μ S.patch * (Fintype.card Axis:ℝ) * countCost (a/2))) := by
  let U := fine G B; let V := outer G B
  have hs := fine_supply B hP
  let g (i : Bond c) (z : Positions (Joint B G)) := G.price (V z i*(S.prediction (U z) t i)⁻¹)
  let M := 2^n * outerCost G (n+1) Z * composeCost n W (connectorCost S.patch G n K (fineCost G (n+1) Z))
  let y (i : Bond c) := S.ratio.embed i.1
  have hv : ‖x‖ ≤ 1 := le_trans (show ‖x‖ ≤ predictionRadius S.patch G S.kernel n K (fineCost G (n+1) Z) D δ η by
    exact (show ‖x‖<_ by simpa using hx).le)
    (le_trans (min_le_left ..) (le_trans (min_le_left ..) (min_le_left ..)))
  have h (i : Bond c) : Allows n (g i) x (priceCost G M) := by
    have he := prediction_pay S hs hn hE hL hF x hx t i
    exact Allows.price (f:=fun z => _) <|
      (((outer_supply B hP).2.2 i x hv).order (Nat.le_succ n)).times (he.inverse (f:=fun z => _))
  have hp := width_positive hμ n S.patch.L
  have ht (i : Bond c) := (h i).beacon (s:=Set.univ) (y:=y i) (r:=noiseCost S.patch) (l:=address B G) (by
    intro u _ v _ he; unfold g U V; rw [noise_read B hS t i he,co_read B he i]
    simp only [y,separation_self]; omega) univ_mem hp.le
  have hy : Multiplicity y (Fintype.card Axis) := by
    intro x
    let s := Finset.univ.filter fun i => y i=x
    have he : Set.InjOn (fun i : Bond c => i.2) ↑s := fun i hi j hj h => Prod.ext
      (S.ratio.embed_injective ((Finset.mem_filter.mp hi).2.trans ((Finset.mem_filter.mp hj).2.symm))) h
    simpa only [Finset.card_univ] using Finset.card_le_card_of_injOn (fun i : Bond c => i.2) (fun _ _ => Finset.mem_univ _) he
  have he := (h (Classical.arbitrary _)).nonneg
  have hh := scatter hy (fun i => (h i).analytic) ht hp (mul_nonneg he (Real.exp_pos _).le)
  have ha := ContDiffAt.sum (s:=Finset.univ) (f:=g) fun i _ => (h i).analytic
  exact ⟨ha.const_smul S.kernel.penalty,hh.smul ha S.kernel.penalty⟩

def paidRadius (G : Gauge) (n : ℕ) (Z K D δ η : ℝ) (P : Patch) (Q : KernelChoices) :=
  predictionRadius P G Q n K (fineCost G (n+1) Z) D δ η

lemma paid_ball (h : R.Bounds p μ C Λ) (hS : S.patch.Branches S.kernel G) (hn : 2 ≤ n)
    (hp : PaintSupply G (n+1) Z) (hQ : SquarePay G n Z μ C Z')
    (hE : ExpReceipt G (n+1) K) (hL : LogReceipt G D δ) (hF : FocusReceipt G n W η) :
    let s := paidRadius G n Z K D δ η S.patch S.kernel
    0 < s ∧ ∀ x∈ball 0 s,
      ContDiffAt ℝ ω (priced B t p R) x ∧ Scatter (address B G) (weaker n (entryWidth n S.patch.L μ)) n
        (priced B t p R) x (allCost G n Z Z' μ C K W p S.patch S.kernel) ∧
        ∀ t', priced B t p R x = priced B t' p R x := by
  have ht := prediction_radius_pos S (fine_supply B hp) hn hE hL hF
  refine ⟨ht,fun x hx => ?_⟩
  have he : x∈ball (0:Positions (Joint B G)) 1 := ball_subset_ball (le_trans (min_le_left ..) (le_trans (min_le_left ..) (min_le_left ..)))
    (show x∈ball 0 (predictionRadius S.patch G S.kernel n K (fineCost G (n+1) Z) D δ η) from hx)
  have hp' : PaintSupply G n Z := ⟨hp.1,fun x hx => (hp.2 x hx).order (Nat.le_succ n)⟩
  obtain ⟨hM,HM⟩ := main_beacons B h hp' hQ x he
  obtain ⟨hN,HN⟩ := penalized B t hS n hn hp hE hL hF h.width x hx
  refine ⟨hM.add hN,(HM.add hM hN HN).mono ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)), fun t' => ?_⟩
  change mainTerm _ _ _+noiseTaylor S (outer G B x) (fine G B x) t=mainTerm _ _ _+noiseTaylor S (outer G B x) (fine G B x) t'
  unfold noiseTaylor; rw [picked_tags S (fine_supply B hp) hn hE hL x hx t t']
end Actual
end YM.Push.Uniform
