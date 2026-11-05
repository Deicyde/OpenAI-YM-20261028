import YM.TraceExtension.Fen.Ski
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine AnalyticNext.QuarticMatch.Estimate
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} (R:Rep G n){I:Type} (b:I→Barley) {k:ℕ}{σ A D C:ℝ}
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] {x:X}
def wail(p:Seat n×GreenA)(U:Config G n)(e:Lines G n 1):=outD (seatP R legF p) e U
abbrev Main (R:Rep G n):= mainTerm R.clip R.path (n:=n)
lemma champagne (f:ℕ→ℝ)(hf: MarksP f)(h:SumBudget (Pointed R b σ) C)(hs:0<σ): Summable (fun i:Seat n × I=>port R (b i.2)*f (mote R (b i.2))):=by
    obtain ⟨hf,Z,u,hZ,hf'⟩:=hf; have hx:= purpose R b C h hs σ hs le_rfl u; let P(t:Seat n×I):=port R (b t.2)*f (mote R (b t.2)); have hp(i):0 ≤ P i:=mul_nonneg (ports_n R _) (hf _)
    refine (summable_prod_of_nonneg (f:=P) hp).2 ⟨fun i=>?_,Summable.of_finite⟩
    refine Summable.of_nonneg_of_le (fun j=> hp (i,j)) (fun j=> ?_) (hx.2.1.mul_left Z)
    unfold Pointed; dsimp only[P]; rw [sub_self,zero_mul,Real.exp_zero,mul_one]; exact (mul_le_mul_of_nonneg_left (hf' _) (ports_n R _)).trans_eq (by unfold rowL rowAm; ring)
lemma earnings(V:Config G n)(s:Link G n) (h:R.path.Bounds R.clip σ A C) : HasSum (fun i:Seat n×GreenA=> fderiv ℝ (fun y=>seatP R legF i (input G n y * V)) 0 s) (fderiv ℝ (fun y=> Main R (input G n y * V)) 0 s):=by
    let U(y):=input G n y*V; let f(i:Seat n×GreenA)(y):=seatP R legF i (U y); let Q(y):= Main R (U y)
    obtain ⟨D,hD,Hd⟩:= armsP 1 G 1 zero_le_one
    let C':= (2^ (1:ℕ):ℝ)*D*G.colorScale; have hC':0≤C':=mul_nonneg (by positivity) G.colorScale_pos.le
    obtain ⟨P,hP,H⟩:= black G C' 1 hC'
    let F(i:Seat n×GreenA):= port R (legF i.2)*P (mote R (legF i.2)); have hf': Summable F:= champagne R legF P hP (off_budget R h) h.width
    have hg i:ContDiff ℝ ω (f i):=contDiff_iff_contDiffAt.mpr fun x=> lick R legF i U x ((Army.powL (v:=id) contDiffAt_id).mul (Army.park _ _))
    have hv(i:Seat n×GreenA)(x:Link G n)(hp:x∈ Metric.ball 0 1) : Allows 1 (f i) x (F i):=by
        apply H (Link G n) R U x _ i.1 (legF i.2); intro j; apply (Hd n x (by simpa using (Metric.ball_subset_closedBall hp)) j).times (f:=fun y=>input G n y j) (g:=fun _=>V j)
        apply allows_const _; rw[SectorAffine.mat_paid]
    have hz := honorable hg hf' (Metric.ball (0:Link G n) 1) Metric.isOpen_ball (convex_ball .. |>.isPreconnected) (fun i x hp=>(hv i x hp).norm_le) (Metric.mem_ball_self zero_lt_one) 1 le_rfl
    have he:Q=fun x=>∑' i, f i x:=funext fun x=> (calibre R h (U x)).tsum_eq.symm
    rw [← he] at hz
    let L:=ContinuousMultilinearMap.apply ℝ (fun _:Fin 1=>Link G n) ℝ (![s])
    have hh:= L.hasSum hz; change HasSum (fun i=> (iteratedFDeriv ℝ 1 (f i) 0) ![s]) ((iteratedFDeriv ℝ 1 Q 0) ![s]) at hh; simp only[iteratedFDeriv_one_apply,cons_val_zero] at hh; exact hh
lemma lightsA (U:Config G n)(h:R.path.Bounds R.clip σ A C): ContDiffAt ℝ ω (fun y=> Main R (input G n y*U)) 0:= Work.F02.mainTerm_contDiffAt (A:=fun y=>input G n y*U) h ((Army.powL (v:=id) contDiffAt_id).mul (Army.park U _))
lemma earnW (e:Lines G n 1)(h:R.path.Bounds R.clip σ A C)(p:ℕ): HasSum (fun i: Seat n×GreenA=> iteratedFDeriv ℝ p (fun y=> wail R i (input G n y) e) 0)
   (iteratedFDeriv ℝ p (outD (Main R) e ∘ input G n) 0):=by
    let f(i): Link G n→ℝ:=fun y=> wail R i (input G n y) e; let Q:=outD (Main R) e ∘ input G n
    have hu : Q=fun x=> ∑' i,f i x:= funext fun x=> (earnings R (input G n x) (bolt e) h).tsum_eq.symm
    -- even if B=1 cannot out hearth, use wholesale for derivatives.
    have hp(D:ℝ)(hD:0 ≤ D):∃ F: Seat n × GreenA→ℝ,Summable F ∧ ∀ (x:Link G n), ‖x‖≤ D→∀ i, Allows p (f i) x (F i):=by
        obtain ⟨A₁,hA,H⟩:=armsP (p+1) G D hD; obtain ⟨B,hB,Hh⟩:= pie_roll G (p+1) A₁ hA; obtain ⟨C,hC,HZ⟩:= black G B (p+1) hB
        refine ⟨_,champagne R legF C hC (off_budget R h) h.width,fun x hx i=> ?_ ⟩
        let U(p:Link G n×Link G n):=input G n p.2*input G n p.1
        exact priced_partial (f:=seatP R legF i ∘ U) (HZ _ R U (x,0) (Hh _ (input G n) x (H n x hx)) i.1 (legF i.2)) _ (norm_bolt e).le
    have he(i): ContDiff ℝ ω (f i):= contDiff_iff_contDiffAt.mpr fun x=> ((hp ‖x‖ (norm_nonneg _)).choose_spec.2 x le_rfl i).analytic
    obtain ⟨F,hF,H⟩:= hp 1 zero_le_one
    change HasSum _ (iteratedFDeriv ℝ p Q _); rw [hu]; exact honorable he hF (Metric.ball (0:Link G n) 1) Metric.isOpen_ball (convex_ball .. |>.isPreconnected) (fun i x hp=> (H x (by simpa using Metric.ball_subset_closedBall hp) i).norm_le) (Metric.mem_ball_self zero_lt_one) p le_rfl
end YM.Trace.Fen
