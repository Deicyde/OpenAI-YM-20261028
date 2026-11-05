import YM.TraceExtension.Wicket.Lilac
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{R:Rep G n}{p:BudgetPoint}{U:Config G n}
variable (o:Edge (Site n)) (s:ℝ)(X:Support n)(m:ℕ) {σ A Λ ε δ w:ℝ}(hp:R.Lawful σ A Λ δ w)(hv:Geo.Width R.p R.clip σ)
def Below(R:Rep G n)(o:Edge (Site n))(r m:ℕ)(H:Finset (Badge n)):Prop :=∀ i∈H, o.1∈boothC R i∧ coverNumber R.p.B (boothC R i) ≤ m  ∧i.elim (fun i=> r< mote R i.2) (fun _=>True)
def ringsZ(R:Rep G n) (o:Edge (Site n))(m:ℕ)(r:ℕ):Prop:= ∀ i:Badge n,o.1∈ boothC R i→coverNumber R.p.B (boothC R i) ≤ m →boothC R i⊆halo r {0}
lemma wake_safe (R:Rep G n)(i:Barley):|Shepherd.wake R i| ≤ 1+|R.beta|:=by rcases i with i|(i|i); exact le_add_of_nonneg_left zero_le_one; exact le_add_of_nonneg_left zero_le_one; change |(1:ℝ)| ≤ _; rw[abs_one]; exact le_add_of_nonneg_right (abs_nonneg _)
-- ∑ weights per i.Raw.Long.Path labelled (so count unaffected by card paths)
abbrev beamAmt (R:Rep G n)(A σ Λ Z:ℝ)(r k:ℕ):= let T:= bankCost R.p.B; T*(Shepherd.wide G R.p.supportExponent*2*(1+|R.beta|)*Z*Real.exp (-(σ/4)*r))*(momentPrice (k+4) (σ/4)*(Geo.lowerSize R.clip A+(A+A+Λ)))
private abbrev wof (R:Rep G n)(Z:ℕ→ℝ)(r:ℕ)(p:Barley):= if r< mote R p then Real.exp (R.p.supportExponent*coverNumber R.p.B (fort R p))*(2*|Shepherd.wake R p| * (port R p*Z (mote R p))) else 0
include hp hv
private lemma blocks (f:ℕ→ℝ)(h:∀ i,0 ≤ f i)(C:ℝ)(ht:0≤ C)(k r:ℕ) (he:∀ i:ℕ,f i≤ C*(1+(i:ℝ))^k) : SumBudget (fun i=> wof R f r i*(1+rowL R id i)^4) ((Shepherd.wide G R.p.supportExponent*2*(1+|R.beta|)*C*Real.exp (-(σ/4)*r))*(momentPrice (k+4) (σ/4)*(Geo.lowerSize R.clip A+(A+A+Λ)))):=by
   let Z:=Geo.lowerSize R.clip A+(A+A+Λ); let Y:=Shepherd.wide G R.p.supportExponent; let W:=Y*2*(1+|R.beta|)*C; let B:= Real.exp (-(σ/4)*r); let p(i):= wof R f r i; have hy:0 ≤ Y:= (Real.exp_pos _).le; have hw:0 ≤W:=by positivity
   have H:= hp.paths.width; have hP:= Fen.purpose (I:=Barley) R id Z (Fen.offull R hp.paths) H (σ/4) (by positivity) (by linarith only[H]) (k+4)
   have hb:=Real.exp_pos (-(σ/4)*r); refine Cost.mono (Cost.scale hP (W*B) (mul_nonneg hw hb.le)) (fun i=> ?_) ?_
   · apply mul_nonneg _ (by positivity); unfold wof; split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (by positivity) (mul_nonneg (ports_n R _) (h _))); exact le_rfl
   intro i; unfold wof; let v:ℝ:= mote R i; have h₁:0 ≤ v:=by positivity
   split
   next hx=>
      have he₁: (r:ℝ) ≤ v :=Nat.cast_le.mpr hx.le; have h₂:= uniform_amt R hp hv i
      apply (mul_le_mul_of_nonneg_right (mul_le_mul h₂ (show 2*|Shepherd.wake R i| * (port R i*f (mote R i))≤2*(1+|R.beta|)*(port R i * (C*(1+v)^k)) from mul_le_mul (mul_le_mul_of_nonneg_left (wake_safe ..) zero_le_two) (mul_le_mul_of_nonneg_left (he _) (ports_n ..)) (mul_nonneg (ports_n ..) (h _)) (by positivity)) (mul_nonneg (by positivity) (mul_nonneg (ports_n ..) (h _))) (mul_nonneg hy (Real.exp_pos _).le)) (show 0 ≤(1+v)^4 by positivity)).trans
      have hG: Real.exp (σ/2*v) ≤ B*Real.exp ((σ-σ/4)*v):=by unfold B; rw[←Real.exp_add]; apply Real.exp_monotone; nlinarith only [H,he₁]
      change Y*Real.exp (σ/2*v)*(2*(1+|R.beta|)*(port R i * (C*(1+v)^k)))*(1+v)^4 ≤ W*B*(port R i*Real.exp ((σ-σ/4)*v)*(1+v)^(k+4))
      apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hy) (show 0≤ 2*(1+|R.beta|)*(port R i * (C*(1+v)^k)) by positivity[ports_n R i])) (show 0≤(1+v)^4 by positivity)).trans_eq
      rw[pow_add]; unfold W; ring
   next=> rw [zero_mul]; exact mul_nonneg (mul_nonneg hw hb.le) (hP.1 i)
lemma amount_beam (f:ℕ→ℝ)(h:∀ i,0 ≤ f i)(C:ℝ)(ht:0≤ C)(k r:ℕ)(he:∀ i:ℕ,f i≤ C*(1+(i:ℝ))^k)(B:Finset (Badge n)) (u:Below R o r m B): ∑ j∈ B.toLeft, R.p.mass (fabrics R j) (ladder R j f) ≤ beamAmt R A σ Λ C r k:=by
    have hs(i):0 ≤ wof R f r i:=by unfold wof; split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (by positivity) (mul_nonneg (ports_n ..) (h _))); rfl
    have hx:= Fen.centCost R (I:=Barley) id o.1 (wof R f r) hs (blocks hp hv f h C ht k r he)
    apply le_trans (b:=∑ i∈ B.toLeft, if o.1∈ metal R id i then wof R f r i.2 else 0) (sum_le_sum fun j hj=> ?_) ((Extra.Multi.Budget.cap hx _).trans_eq (by unfold beamAmt;ring))
    obtain ⟨h',hb,hE⟩:= u (.inl j) (mem_toLeft.mp hj); unfold BudgetPoint.mass; rw [show coverNumber R.p.B (fabrics R j)=_ from offt R _ _, if_pos (show o.1∈metal R id j from h'),wof,if_pos (show r < mote R j.2 from hE)]
section reg
omit hv
abbrev tower(r:ℕ):= (halo r {0}:Support n)
lemma amount_E (C:ℕ→ℝ) (ht:∀ i,R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (C i)) (he:∀ x:Site n, SumBudget (fun i=> if (R.activities.reg i).site=x then R.p.mass (R.activities.reg i).support (C i) else 0) δ) (r r':ℕ)(B:Finset (Badge n))(h:ringsZ R o m r')(u:Below R o r m B) : ∑ i∈ B.toRight, R.p.mass (boothC R (.inr i)) (C i) ≤ ((r'+r'+1)^ (4:ℕ):ℕ)*δ:=by
    have hy(i:ℕ)(hi:i∈ B.toRight) : (R.activities.reg i).site∈ tower r':=by obtain ⟨hx,hx',_⟩:=u _ (mem_toRight.mp hi); exact h (.inr _) hx hx' (R.activities.reg i).anchor
    let g(x:Site n)(i:ℕ):=if (R.activities.reg i).site=x then R.p.mass (R.activities.reg i).support (C i) else 0; let Z:= tower r' (n:=n)
    apply le_trans (b:=∑ i∈B.toRight,∑ x∈Z,g x i) (sum_le_sum (fun i hi=> ?_))
    · rw [sum_comm]; apply le_trans (sum_le_sum (fun j (_:j∈Z)=>Extra.Multi.Budget.cap (he j) _)); rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_trans (Corona.halo_size ..) (by simp))) (Cost.nonneg (he 0))
    exact le_trans (le_of_eq (show R.p.mass _ _=g (R.activities.reg i).site i from (if_pos rfl).symm)) (single_le_sum (s:=Z) (f:=fun j=> g j i) (fun j _=> (he j).1 i) (hy i hi))
end reg
end YM.Trace.Wicket
