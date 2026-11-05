import YM.UVExtension.Pier.Power
import YM.Push.LOCAL_SPLITTING.Budget
/-! # No large cutoff data in fixed-stop credit for loop and path principal. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Lattice Wilson RG MeasureTheory Push Push.AbsoluteSums
open RG.PathData Lamppost Rafter Copse
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable (G : Gauge) (n:Side)
variable (p : BudgetPoint) (c : Clip)(σ C Λ:ℝ)
variable {G} (R: PathData G) (h: R.Bounds c σ C Λ)
include h
lemma bread (U:Config G n) (x:Face (Per n)): ‖R.ell U x‖ ≤ C * 2:=by
   let f:= (fun i=> R.ellTerms x i U); have he:= h.rows x.2; let b(i):= |(R.row x.2 i).1| *Real.exp (σ*(R.row x.2 i).2.length); have hz: Summable (fun i=> b i*2):=he.2.1.mul_right _; have ht:= (R.ell_dominated h x).absolute U
   have hy i: ‖f i‖≤ b i*2:=by unfold f ellTerms; rw [norm_smul]; exact mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le (Nat.cast_nonneg _)))) (Slot.eval_norm ..) (norm_nonneg _) (he.1 i)
   exact (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum hy hz).trans ((tsum_mul_right).trans_le (mul_le_mul_of_nonneg_right he.2.2 zero_le_two)))
omit h
variable {n':ℕ}
lemma dough (F:ℕ→ Atom G n')(k:ℝ)(h:SumBudget (fun i=> (F i).budget σ) k)(hp:0 < σ)(U:Config G n)(x:Site n): |atomSeries F p U x|≤ k*(2:ℝ)^n':=by
   let b i:=(F i).budget σ; let z i:= b i*(2:ℝ)^n'; have hq: Summable z:=h.2.1.mul_right _; have hp': 0≤(2:ℝ)^n':= by positivity
   have hs i: ‖(F i).placed p U x‖≤ z i:= ((F i).placed_bound ..).trans (mul_le_mul_of_nonneg_right (Atom.lower_budget _ σ hp) hp')
   have ht:=(atom_dominated F p x hp h).absolute U; exact (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum hs hq).trans ((tsum_mul_right).trans_le (mul_le_mul_of_nonneg_right h.2.2 hp')))
-- fixed crop.
attribute [local instance] Classical.propDecidable
def crust (G: Gauge)(c:Clip)(p:BudgetPoint)(k:ℝ)(x:Face (Per n)):= ((PathData.clip_env p x (c:=c) (G:=G)|>.cost.choose))+ (2*k)^2/2
include h
lemma fruit (U:Config G n) (x:Face (Per n)): ‖R.baseTerm c p U x‖≤crust n G c p C x:=by
   unfold baseTerm; apply (norm_add_le ..).trans; refine add_le_add ((PathData.clip_env p x).cost.choose_spec U) ?_
   split; next ht=> rw [Real.norm_of_nonneg (by positivity), mul_comm 2]; exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (bread n c σ C Λ R h U x) _) zero_le_two
   rw [norm_zero]; positivity
variable {A Z:Type}[NormedAddCommGroup Z][NormedSpace ℂ Z] (T: Opening A Z){a b:ℝ}
-- estimates universal in R and U. no convergence issues. sign small path.Channel
lemma potion (u:A→ℝ) (hx:Sail T (fun i=> (u i:ℂ)) a) (ha:0≤a) (U:Config G n) : let v:= ∑ j:Face (Per n),crust n G c p C j; let r:=C*(2:ℝ)^3+C*2^4; let t:=a*(v+∑_j:Site n,r)+∑ _j:Site n,Λ*2^2
   Sail T (fun i=> (R.inChannels c p (u i) U:ℂ)) (t*(Fintype.card Signed:ℝ)*(Fintype.card Signed:ℝ)⁻¹):=by
    intro v r t; let z (V:Config G n):= (∑ f,R.baseTerm c p V f)+∑ x:Site n,(PathData.atomSeries R.cubic p V x+PathData.atomSeries R.quartic p V x); let y (V:Config G n):= ∑ x:Site n,PathData.atomSeries R.loop p V x
    have he(V:Config G n) : Sail T (fun i=>(R.principal c p (u i) V:ℂ)) t:= by
       have hZ:‖(z V:ℂ)‖≤ v+∑ _i:Site n,r:=by unfold z; rw [Complex.norm_real]; exact (norm_add_le ..).trans (add_le_add ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> fruit n p c σ C Λ R h _ i))) ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> (norm_add_le ..).trans (add_le_add (dough n p σ _ _ h.three h.width V i) (dough n p σ _ _ h.four h.width V i))))))
       have hy: ‖(y V:ℂ)‖ ≤ ∑ _i:Site n,Λ*2^2:=by rw [Complex.norm_real]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> dough n p σ _ _ h.two h.width V i)
       simp_rw [PathData.principal, Complex.ofReal_add (u _ * _),Complex.ofReal_mul]; exact ((hx.scaled (z V:ℂ)).plus (Sail.const (y V:ℂ))).mono (add_le_add (mul_le_mul_of_nonneg_left hZ ha) hy)
    let f s i:ℂ:= R.principal c p (u i) (pull s 0 U); have ht : Sail T (fun i=> ∑ j:Signed,f j i) (∑ _j:Signed,t):=Sail.list Finset.univ (fun i _=> he _); let q:ℝ:=(Fintype.card Signed:ℝ)⁻¹
    have hJ:= ht.scales (q:ℂ); have hv : ‖(q:ℂ)‖*(∑ _j:Signed,t)= t* (Fintype.card Signed:ℝ)*q:=by rw [Complex.norm_real,Real.norm_of_nonneg (by unfold q; positivity)]; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
    simp_rw [inChannels,Complex.ofReal_mul, Complex.ofReal_sum]; exact hv ▸ hJ
end YM.UVExtension.Pier
