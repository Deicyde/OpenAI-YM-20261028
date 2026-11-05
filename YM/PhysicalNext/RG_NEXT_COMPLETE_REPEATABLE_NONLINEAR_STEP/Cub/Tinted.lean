import YM.AnalyticNext.GRID_STOP_ATTENUATION.Annual
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Gala
/-! # Quantitative Band for normalized Gaussian ratio (center stationary). Uses V9.Dual = precision on BOTH. Even here not constant because covariance receives V, but derivatives small. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score
    AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
section propagate
variable {G:Gauge}{n:Side}{k:ℕ}{F:Config G n→ℂ}{r c:ℝ} {U:Config G n} {D:Directions G n→Prop}
lemma exp_seep (h:Slope k D U r c F)(hv:F U=0): Slope k D U ((k:ℝ)*(1+c)*r) c (fun x=> Complex.exp (F x)):=by
   cases k
   · exact ⟨into _ _ h.read.germ.cexp,by simp,h.nonneg,fun l hh hp hv=> by exfalso; simp_all⟩
   next k=>
   have hc:=h.nonneg; have hw:= h.starts
   let V:=fun x=>Complex.exp (F x)
   apply Slope.from_core (by positivity) hc (into _ _ h.read.germ.cexp) (fun i hi=> ?_)
   have he:i=k:=by omega
   subst i; intro A he
   have hy:= h.shorten.exp_band.multiply (h.core he); rw [hv] at hy; simp only [Complex.exp_zero,norm_one,one_mul] at hy
   apply band_rise (band_move hy ?_) _ _
   · filter_upwards [h.read.near] with x hx; have h:= ((hx.line [] (by simp) A).hasDerivAt.cexp).deriv; rw [zero_smul,Multi.Puff.inc_zero] at h; exact h
   · apply mul_le_mul_of_nonneg_left _ hc; push_cast; nlinarith [mul_nonneg (show 0≤(k:ℝ) by positivity) (show 0≤(1+c)*r by positivity)]
   push_cast; nlinarith
end propagate
variable {G : Gauge} {c : Side} {V : Config G c} {P : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {o : Site c}
    {K Z t : ℝ} {n R : ℕ} {J : Config G c → Matrix ι ι ℝ}
lemma ivory (h:Carillon J V n P o K Z t R)(ht:0≤t)(hk:t≤1)(hz:1≤Z)(z:Gaussian.Vec ι): Band n (P.dirBound o) V (Carillon.speed n Z t P.power R z) (t*Carillon.pitch n ι Z R P.power z) ((fun W=>(Carillon.vary V J z W:ℂ)) - (fun _=>1)):=by
  have he:=h.log_slope ht hk hz z; have hs:=exp_seep he (by simp [Carillon.value]); let A:= t*Carillon.pitch n ι Z R P.power z
  have hl : Slope n (P.dirBound o) V (Carillon.speed n Z t P.power R z) A (fun W=>(Carillon.vary V J z W:ℂ)):= hs.move (h.near.mono (fun W hW=>by dsimp only; rw [Carillon.vary_exp hW h.pos,Complex.ofReal_exp]))
  exact (hl.minus (Slope.fixed n 1 hl.starts)).band (by simp only [Pi.sub_apply,h.home z, Complex.ofReal_one,sub_self,norm_zero]; exact he.nonneg) (add_zero _|>.le)
end YM.PhysicalNext.Repeat.Cub
