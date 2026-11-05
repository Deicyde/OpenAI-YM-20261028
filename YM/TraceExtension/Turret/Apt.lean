import YM.TraceExtension.Turret.Eclet
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Turret
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Extra.Iteration
open WardBin Filch PhysicalNext.JointLoad AnalyticBridge.SectorAffine.Offset Planned.AtomRegular.Foliage Next.Fluctuations Next.SectorChange
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {X Y: Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {G:Gauge}{n:Side}{k:ℕ}{R C b a:ℝ}{F:X→Y}

private lemma topm {o:Site n}{A:Acr G n→ℝ}(h:Estate o A a (fun _=>C))(hp:A 0=0)(hx:fderiv ℝ A 0=0)(he:0≤ C) (k:ℕ)(hk:k≤4): cost (landW o) a 4 0 (Perfect.leaf A 0 k) ≤ C:=by
   match k with
   | 0=>simpa[Perfect.cost,Perfect.leaf,bank,iteratedFDeriv_zero_apply,hp] using he
   | 1=>simpa[Perfect.cost,Perfect.leaf,bank,iteratedFDeriv_one_apply,hx] using he
   | i+2=>exact h.values _ hk (by omega)
private lemma nail(G:Gauge)(k:ℕ)(n:Side)(x:Lines G n 1)(e:Edge (Site n)) (X:Type)[NormedAddCommGroup X] [NormedSpace ℝ X](u:X):
   let L: (G.ColorIndex→ℝ)→L[ℝ] G.Color:= (WithLp.linearEquiv 2 ℝ _).symm.toContinuousLinearMap
   Allows k (fun _:X=> edgeColor (bolt x) e) u (‖L‖*1):=by
    intro L; apply Allows.linear (L:=L) (f:=fun _:X=> fun j=> edgeColor (bolt x) e j); swap; · exact le_rfl
    apply allows_pi zero_le_one; intro j; exact allows_const u (by change ‖bolt x (e.1,coord e.2,j)‖≤1; simp[bolt,Pi.single_apply]; split <;> norm_num)
-- Inputs 1 here.FD future actual widths.
lemma entire(G:Gauge)(k:ℕ)(A:ℝ)(ha:0≤ A):∃ Z:ℕ→ℝ, MarksP Z ∧ ∀ (X:Type) [NormedAddCommGroup X] [NormedSpace ℝ X] (n:Side)(o:Site n)(C b:ℝ)(r:ℕ)(W:X→ Config G n)(x:X)(h:∀ i,Allows k (fun t=>G.mat (W t i)) x A),0≤ C→0≤ b→
  (∀ J:Peat G n,J∈loom G n→Estate o (ballX J) b (fun _=>C)→ Allows k (lakesC o r J ∘ W) x (Z r*C))∧∀ Y:Gal G n,Y∈ rains G n→Estate o (bottom Y) b (fun _=> C)→∀ i, Allows k (fun y=> lakesY o r Y (W y) i) x (Z r*C):=by
    let L:(G.ColorIndex→ℝ)→L[ℝ] G.Color:= (WithLp.linearEquiv 2 ℝ _).symm.toContinuousLinearMap; let E:=A+‖L‖*1; have hx:0 ≤ E:=by positivity
    obtain ⟨Z,hZ,H⟩:=stencilG G E k hx; refine ⟨Z,hZ,?_⟩; intro X _ _ n o C b r W x h he hp
    have hw(i): Allows k (fun t=>G.mat (W t i)) x E:= (h i).mono (le_add_of_nonneg_right (by positivity))
    constructor
    · intro J hJ hC; obtain ⟨ht,hu,hb⟩:=loom_read hJ
      exact H X hp (topm hC ht hu he) W (fun _=>0) x hw (fun i=> allows_const x (v:=edgeColor (0:Link G n) i) (by simpa using hx))
    intro Y hY hC i; obtain ⟨ht,hu,hb,hG⟩:= rain_read hY
    exact H X hp (topm hC ht hu he) W (fun _=>bolt i) x hw (fun j=> (nail G k n i j X x).mono (le_add_of_nonneg_left ha))
lemma incrementA (U:Config G n)(x:Directions G n): Army (increment U) x:=by
    intro i; let L:Directions G n→L[ℝ] G.Color:= ContinuousLinearMap.proj i; change ContDiffAt ℝ ω (fun z=>G.mat (G.lieExp (L z)* U i)) x; simp_rw [Gauge.mat_mul]; exact (G.exp_jet.contDiffAt.comp (f:=L) x L.contDiff.contDiffAt).mul contDiffAt_const
lemma atp (G:Gauge)(k:ℕ)(A:ℝ)(ha:0≤ A):∃ S:ℝ,0≤ S ∧∀ (n:Side)(U:Config G n)(x:Directions G n), ‖x‖ ≤ A→ ∀ i, Allows k (fun y=> G.mat (increment U y i)) x S:=by
    obtain ⟨B,hB,H⟩:= exists_allows (f:=G.mat ∘ G.lieExp) (s:=Metric.closedBall 0 A) (ProperSpace.isCompact_closedBall 0 A) (fun x _=> G.exp_jet.contDiffAt) k
    let D:= composeCost k B (1+A); have hd:0≤ D:= by unfold D composeCost; positivity
    have h':∃ T:ℝ,0≤ T∧∀ x:G.El,‖G.mat x‖≤T:=by
       obtain ⟨T,hT⟩:= (isCompact_range (f:=G.mat) G.continuous_mat).exists_bound_of_continuousOn (f:=id) continuousOn_id
       exact ⟨max 0 T,le_max_left ..,fun i=> le_trans (hT _ (Set.mem_range_self ..)) (le_max_right ..)⟩
    obtain ⟨T,hT,h⟩:=h'
    refine ⟨2^k*D*T,by positivity,fun n U x hx i=>?_⟩
    let L:Directions G n→L[ℝ] G.Color:=ContinuousLinearMap.proj i
    have hu:‖L x‖≤ A:=(norm_le_pi_norm x i).trans hx
    have hl:Allows k L x (1+A):= allows_linear ((L.opNorm_le_bound zero_le_one (fun v=>by rw[one_mul]; exact norm_le_pi_norm v i)).trans (le_add_of_nonneg_right ha)) (hu.trans (le_add_of_nonneg_left zero_le_one))
    exact ((H _ (show L x∈ Metric.closedBall 0 A by simpa using hu)).comp hl|>.times (f:=fun y=>G.lieExp (L y)) (g:=fun _=>U i) (allows_const x (h (U i))))
private lemma Ax_eq (F:Peat G n): (F ∘ input G n) ∘ edgeColor.symm=F ∘ increment 1:=by
    ext1 x; apply congr_arg F; funext i; rw[input_color]; simp[increment]
lemma roll_d {J:Peat G n}(h:J∈loom G n): braid (J ∘ increment 1) (fun _=>0) 0 1:=by
    obtain ⟨hc,h'⟩:=h; let L:Directions G n ≃L[ℝ] Link G n:= edgeColor.symm
    have h': braid (J ∘ input G n) (fun _=>0) 0 1:=h'
    rw[← Ax_eq]; exact wove (w:=L) ((map_zero L).symm ▸ h') ((map_zero L).symm ▸ (show Cleric J from hc).dye) contDiffAt_const (L.contDiff.contDiffAt)
lemma boundsP {P:BudgetPoint} {o:Site n}{r:ℕ}(T:Collar G P.order) (C:ℝ) (hC:0≤ C) (ht:Cube.Wire P r T) (hn:2*(r+1)<n.val){J:Peat G n}(he:J∈loom G n)(h:∀ x:Directions G n,‖x‖≤ Cube.fee T→ Allows P.order (J ∘ increment 1) x C) (hp:LocalOn (halo r {o}) J)(hf:P.Regular (halo (r+1) {o}) J):
   let s:=Cube.moduleBill P r; let r':=C*evenR 2 (Cube.fee T)*s^2; P.supBounds o (halo (r+1) {o}) J (composeCost P.order r' (Cube.fee T)):=by
    intro s r'; have hh:= Cube.fee_one T; have hh':0≤ Cube.fee T:=zero_le_one.trans hh; have hs:0 < s:= mul_pos P.threshold_pos (pow_pos (a:=1+(r:ℝ)) (by positivity) _); apply lends hf (r:=r) (fun _ h=>h) hp hn T ht (by unfold r' evenR; positivity)
    intro x hx; exact AnalyticBridge.SectorAffine.Offset.Through.control (heaven (f:=J ∘ increment 1) 2 (Cube.fee T) hh' hs.le ht.2 (fun y hy=> h y (hy.trans (mul_le_of_le_one_right hh' ht.2))) hC (by have hv:=P.order_ge; omega) (fun i hi=>by rw[roll_d he i (by omega),iteratedFDeriv_zero_fun,Pi.zero_apply,norm_zero]; positivity) x hx)
lemma regularAi {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][MeasurableSpace X][BorelSpace X]{P:BudgetPoint}{Q:Support n}{F:Config G n→X}(hp:GaugeInvariant F)(hf:LocalOn Q F)(hh:∀ U:Config G n, ContDiffAt ℝ P.order (F ∘ increment U) 0): P.Regular Q F:=by
    exact ⟨hf,(WardBin.left_cont F (fun U=> (hh U).continuousAt)).measurable, hp,fun U _=> hh U,fun U _ A l hl=> WardBin.Lies.Germ.has (m:=P.order) (hh U) l A hl⟩
end YM.Trace.Turret
