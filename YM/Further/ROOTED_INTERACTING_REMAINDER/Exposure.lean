import YM.Push.SECTOR_MEASURE.Presented
import YM.SectorNext.VACUUM_NORMALIZATION.Covered
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped

/-!
# Uniform joint price of cutting (all winding costs stay in paths)

Useful also in comparing the exact normalized transfer to the conditional
Gaussian/first gas desk. Not using the finite envelope cost of `exposed` for
a volume-uniform result. These estimates can be used at intermediate scales;
see Serving for numerical eventualities in x. Path clip/path Bounds of the
very same antennas!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder
open Filter Function Lattice RG Wilson Finset Precision Tree
open Pressure Pressure.Stores Pressure.Teller Bid Next.Fluctuations
open Next.Fluctuations.Sector Push.SectorMeasure Oriented Presented
open SectorNext.Vacuum
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f n : Side}

def fringe (σ : ℝ) (R d : ℕ) := Real.exp (-σ * ((R:ℝ)/d))
lemma fringe_nonneg (σ : ℝ) (R d : ℕ) : 0 ≤ fringe σ R d := by unfold fringe; positivity

open Work.E04
private lemma remaining_ell {T : PathData G} {C : Clip} {σ r Λ : ℝ} (h : T.Bounds C σ r Λ)
    (R d : ℕ) (he : 1≤d) (p : Cell n) (U : Config G n) :
    ‖T.ell U p-shorten T R d U p‖ ≤ 2*r*fringe σ R d := by
  have hr := h.rows p.2
  let v := fun i => |(T.row p.2 i).1| * Real.exp (σ*(T.row p.2 i).2.length)
  let u := fun i => T.ellTerms p i U
  let w := fun i => shortenTerm T R d U p i
  have hg : Summable u := ((T.ell_dominated h p).absolute U).of_norm
  have hb : Summable w := by
    refine ((show Summable (fun i => ‖u i‖) from (T.ell_dominated h p).absolute U).of_nonneg_of_le
      (g:=fun i => ‖w i‖) (fun i => norm_nonneg _) ?_).of_norm
    intro i; unfold w shortenTerm; split; exact le_rfl; exact (norm_zero).le.trans (norm_nonneg _)
  have hs : Summable fun i=> v i*(2*fringe σ R d) := hr.2.1.mul_right _
  have hk (i : ℕ) : ‖u i-w i‖ ≤ v i*(2*fringe σ R d) := by
    let y := (T.row p.2 i).2
    let a := |(T.row p.2 i).1|
    unfold w shortenTerm; split; next => simp only [u,sub_self,norm_zero]; exact mul_nonneg (hr.1 i) (by unfold fringe; positivity)
    next hm =>
      unfold u v
      simp only [sub_zero,PathData.ellTerms,norm_smul,Real.norm_eq_abs]
      change a * ‖y.atSite U p.1‖ ≤ a * Real.exp (σ*y.length)*(2*fringe σ R d)
      calc
        _ ≤ a * 2 := mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (abs_nonneg _)
        _ ≤ a * 2 * (Real.exp (σ*y.length)*fringe σ R d) := by
          have hf : (R:ℝ)/d ≤ y.length := by
            rw [div_le_iff₀ (by exact_mod_cast he)] -- needs 0<d
            exact_mod_cast Nat.le_of_not_le hm
          refine le_mul_of_one_le_right (by unfold a; positivity) ?_
          unfold fringe; rw [←Real.exp_add]; apply Real.one_le_exp; nlinarith only [hf,h.width]
        _ = _ := by ring
  have hh := hs.of_nonneg_of_le (g:=fun i=>‖u i-w i‖) (fun _=>norm_nonneg _) hk
  change ‖(∑' i,u i)-∑' i,w i‖ ≤ _
  rw [← hg.tsum_sub hb]
  refine (norm_tsum_le_tsum_norm hh).trans ((hh.tsum_le_tsum hk hs).trans ?_)
  rw [tsum_mul_right]
  exact (mul_le_mul_of_nonneg_right hr.2.2 (mul_nonneg (by norm_num) (fringe_nonneg ..))).trans_eq (by ring)

/-- rho² cut price per real plaquette. Works even when kept mask not smooth
and at equality. `r` = native antenna exponential row sum. -/
def wound (σ r t : ℝ) (R d : ℕ) :=
    (2*r*fringe σ R d) * (r*t+r*fringe σ R d)

theorem cut_model {T : PathData G} (C : Stage) {Λ : ℝ} (h : T.Bounds C.clip C.width C.paths Λ)
    (R d : ℕ) (he : 1≤d) (p : Cell n) (U : Config G n) (b : BudgetPoint) :
    |crown T C.clip R d b.threshold U p - T.baseTerm C.clip b U p| ≤
      wound C.width C.paths b.threshold R d := by
  have hW : 0 ≤ wound C.width C.paths b.threshold R d := by
    unfold wound; have := fringe_nonneg C.width R d; have := C.paths_pos; have := b.threshold_pos; positivity
  unfold crown trunk PathData.baseTerm
  split <;> rename_i H
  · let u := ‖shorten T R d U p‖
    let v := ‖T.ell U p‖
    let g := 2*C.paths*fringe C.width R d
    have hu : 0 ≤ u := norm_nonneg _
    have hv : 0 ≤ v := norm_nonneg _
    have hr : |u-v| ≤ g := (abs_norm_sub_norm_le _ _).trans (by rw [norm_sub_rev]; exact remaining_ell h R d he p U)
    have hp : u ≤ C.paths*b.threshold := shorten_small R d h p b.threshold_pos.le U H
    change |u^2/2+_-(_+v^2/2)| ≤ _
    rw [show u^2/2+PathData.clipped _ _ (G.chord (faceValue U p))-(_+v^2/2) = (u-v)*(u+v)/2 by ring, abs_div,abs_mul, abs_of_nonneg (show (0:ℝ) ≤ u+v by linarith)]
    norm_num
    unfold wound
    change _ ≤ g * _
    have hh : u+v ≤ 2*C.paths*b.threshold+g := by linarith only [hp,(abs_le.mp hr).1]
    have hx := mul_le_mul hr hh (by linarith only [hv,hu] : 0 ≤ u+v) ((abs_nonneg _).trans hr)
    unfold g at *; linarith only [hx]
  · simp only [zero_add,add_zero,sub_self,abs_zero]; exact hW

/-- Sup over fine links & background V (not just chart). -/
theorem launched {R : Rep G f} (c : Stage) {Λ δ w : ℝ} (H : R.Lawful c.width c.paths Λ δ w)
    (hc : R.clip=c.clip) (hβ : 0 ≤ R.beta) (hw : w ≤ 1) (n : ℕ) (U : Config G f) :
    let L := R.exCost c.paths Λ δ + R.beta*(Fintype.card PlaqAxes*(wound c.width c.paths R.p.threshold n 1))
    ‖Real.exp (-R.scalar)*exposed R n U‖ ≤ Real.exp (sites f * L) := by
  intro L
  let e := sites f
  let b := Fintype.card PlaqAxes*(wound c.width c.paths R.p.threshold n 1)
  have ht := H.paths
  rw [hc] at ht
  have hk (s : Signed) (p : Cell f) :
      crown R.path R.clip n 1 R.p.threshold (pull s 0 U) p - R.path.baseTerm R.clip R.p (pull s 0 U) p
        ≤ wound c.width c.paths R.p.threshold n 1 := by
    rw [hc]; exact (abs_le.mp (cut_model c ht _ 1 le_rfl p _ _)).2
  let lp := PathData.loopsPrice R.p R.beta c.paths Λ
  let F := fun s : Signed => R.path.principal R.clip R.p R.beta (pull s 0 U)
  let g := fun s : Signed => ∑ i, crown R.path R.clip n 1 R.p.threshold (pull s 0 U) i
  have hj (s : Signed) : R.beta*g s - F s ≤ e*(lp + R.beta * b) := by
    let V := pull s 0 U
    have he : g s - ∑ p, R.path.baseTerm R.clip R.p V p ≤ e*b := by
      unfold g; rw [← sum_sub_distrib]
      apply (sum_le_sum (fun p _ => hk s p)).trans_eq
      simp only [sum_const,card_univ,nsmul_eq_mul,Cell,Face,Fintype.card_prod,Nat.cast_mul,mul_assoc]; rfl
    have hf := (abs_le.mp (R.path.volume_price _ R.p R.beta hβ V H.paths)).1
    unfold e V F lp sites at *; linarith only [mul_le_mul_of_nonneg_left he hβ,hf]
  have hm : R.beta * cutR R n U - R.path.inChannels R.clip R.p R.beta U ≤ e*(lp+R.beta*b) := by
    change R.beta*Branch.avg g - Branch.avg F ≤ _
    rw [Branch.avg_mul R.beta g|>.symm,← Branch.avg_sub]
    exact (Branch.avg_mono (g:=fun _ => (sites f:ℝ)*(lp+R.beta*b)) hj).trans_eq (Branch.avg_const ..)
  have he := (abs_le.mp (volumeE _ H.labels U)).1
  rw [expel,Rep.eval,show Real.exp (-R.scalar)*(Real.exp _*(Real.exp _*R.activities.gas R.p U)) =
      (Real.exp (-R.scalar)*Real.exp (R.beta*cutR R n U)*Real.exp (R.exponent U))*R.activities.gas R.p U by ring,
    ← Real.exp_add, ← Real.exp_add,Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_of_le_one_right (Real.exp_pos _).le (gas_le_one _ hw H.labels _)).trans
  refine Real.exp_le_exp.mpr ?_
  unfold L Rep.scalar Rep.exCost Rep.exponent; unfold e lp b sites at *
  linarith only [hm,he]

/-- Wounded outgoing sieve vs the FULL unmasked base cost (still not
loop/Hessian). -/
def girder (T : PathData G) (a : Clip) (b : BudgetPoint) (U : Config G f) :=
    Branch.avg fun s : Signed => ∑ p, T.baseTerm a b (pull s 0 U) p

theorem sieve_nonpositive (S : StepData c f) (T : Tube G S) (β x : ℝ) (hp : 0≤β) (V : Config G c) : sieve T β x V ≤ 1 := by
  refine Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) ?_)
  unfold averaged; apply mul_nonneg (by positivity)
  refine sum_nonneg (fun i _ => sum_nonneg (fun j _ => ?_))
  unfold crown; apply add_nonneg
  · unfold trunk; split <;> positivity
  unfold PathData.clipped; have := T.low.quadratic_pos; have := T.low.tail_pos
  have hz := Push.SectorMeasure.temp_nonneg x
  have := G.chord_nonneg (faceValue (pull i 0 V) j); split <;> positivity

theorem aligned {S : StepData c f} (T : Tube G S) (C : Stage) {Λ : ℝ} (hc : T.low = C.clip) (h : T.down.Bounds C.clip C.width C.paths Λ)
    (β x : ℝ) (hp : 0≤β) (b : BudgetPoint) (ht : b.threshold = temp x)
    (V : Config G c) :
    let K := (Fintype.card PlaqAxes:ℝ)*wound C.width C.paths b.threshold (till x) S.patch.L.val
    |Real.log (sieve T β x V) + β*girder T.down C.clip b V| ≤ sites c*(β*K) := by
  intro K
  let Q := fun (i : Signed) (j : Cell c) => crown T.down T.low (till x) S.patch.L.val (temp x) (pull i 0 V) j
  let D := fun (i : Signed) (j : Cell c) => T.down.baseTerm C.clip b (pull i 0 V) j
  have he (i : Signed) : |∑ j, Q i j - ∑ j,D i j| ≤ sites c*K := by
    rw [← sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    apply (sum_le_sum (g:=fun _ => wound C.width C.paths b.threshold (till x) S.patch.L.val) (fun j _ => by
      unfold Q D; rw [hc,←ht]; exact cut_model C h _ _ S.patch.L.property ..)).trans_eq
    simp only [K,sites,sum_const,card_univ,nsmul_eq_mul,Cell,Face,Fintype.card_prod,Nat.cast_mul,mul_assoc]
  unfold sieve; rw [Real.log_exp]
  change |-β*Branch.avg (fun i => ∑ j,Q i j)+β*Branch.avg (fun i=>∑ j,D i j)| ≤ _
  rw [show -β*Branch.avg (fun i=>∑ j,Q i j)+β*Branch.avg (fun i=>∑ j,D i j) = -β*(Branch.avg (fun i=>∑ j,Q i j)-Branch.avg (fun i=>∑ j,D i j)) by ring,abs_mul,abs_neg,abs_of_nonneg hp,← Branch.avg_sub,mul_left_comm]
  refine mul_le_mul_of_nonneg_left (abs_le.mpr ⟨?_,?_⟩) hp
  · exact (Branch.avg_const (n:=Signed) _).symm.le.trans (Branch.avg_mono fun j => (abs_le.mp (he j)).1)
  exact (Branch.avg_mono (g:=fun _ => sites c*K) fun j=> (abs_le.mp (he j)).2).trans_eq (Branch.avg_const ..)

end YM.Further.RootedInteractingRemainder
