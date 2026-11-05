import YM.TraceExtension.Wicket.Tweed
import YM.Next.WARD_BIN.Wheels
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{R:Rep G n}{B:BudgetPoint}{s A C:ℝ}{k m q:ℕ}{U:Config G n}{i:Edge (Site n)}
private def puncAmt(k:ℕ)(G:Gauge)(A:ℝ):ℕ→ℝ
 | 0=> ‖(1:G.Mat)‖
 | j+1=> 2^k*puncAmt k G A j*A
private lemma plots {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]{p:X}(m:ℕ)(f:Fin m→X→G.El)(h:∀ i,Allows k (G.mat ∘ f i) p C) : Allows k (fun y=>G.mat (punct m (fun i=>f i y))) p (puncAmt k G C m):=by
   induction m with
   | zero=> exact allows_const _ le_rfl
   | succ m ih=> exact Allows.times (f:=fun y=>punct m (fun i:Fin m=> f i.succ y)) (g:=f 0) (ih _ (fun i:Fin m=>h i.succ)) (h 0)
lemma charter (k:ℕ)(G:Gauge) :∃ A:ℝ,0≤A∧∀ (n:Side)(U:Config G n)(m:ℕ)(j:Edge (Site n))(l:Slab G n m),m ≤ k → (∀ i,‖l i j‖≤ 1)→Allows k (fun x=>G.mat (journey U m l x j)) 0 A:=by
   obtain ⟨C,hC,H⟩:=exists_allows (s:={(0:G.Color)}) isCompact_singleton (f:=G.mat ∘ G.lieExp) (fun x hx=>G.exp_jet.contDiffAt) k
   let f(m):= puncAmt k G (composeCost k C 1) m
   let A:ℝ:=∑ j∈range (k+1),|f j|; have ha:0 ≤A:=sum_nonneg fun i _=>abs_nonneg _; refine ⟨2^k*A*G.colorScale,by positivity[G.colorScale_pos],fun n U m j l hm hl=>?_⟩
   let W(i:Fin m)(p:Panels m):= G.lieExp (p i • l i j); have hz(i:Fin m) : Allows k (G.mat ∘ W i) 0 (composeCost k C 1):=by
      let L:Panels m →L[ℝ] G.Color:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Fin m=>ℝ) i).smulRight (l i j); have he:‖L‖ ≤ 1:= L.opNorm_le_bound zero_le_one fun p=> (norm_smul (p i) (l i j)).trans_le ((mul_le_of_le_one_right (norm_nonneg _) (hl i)).trans ((norm_le_pi_norm p i).trans (one_mul _).symm.le))
      exact (H (L 0) (by rw[map_zero]; exact Set.mem_singleton 0)|>.comp (allows_linear he (by rw[map_zero,norm_zero]; exact zero_le_one)))
   simp_rw [journey_value]; apply Allows.times (f:=fun y=>punct m (fun i=>W i y)) (g:=fun _=>U j) ((plots m W hz).mono ?_)
   · exact allows_const _ ((SectorAffine.mat_paid ..).le)
   exact (le_abs_self (f m)).trans (single_le_sum (s:=range (k+1)) (f:=fun i=> |f i|) (fun i _=>abs_nonneg _) (mem_range.mpr (by omega)))
lemma scrolls {t:Peat G n}{P:Support n} (B:BudgetPoint)(U:Config G n)(C A:ℝ) (hp:LocalOn P t)(hx:Chart B.order t U)(hg:∀ m:ℕ,∀ l:Slab G n m, m≤ B.order→(∀ i:Edge (Site n),∀ j,‖l j i‖≤1)→ Allows B.order (t ∘ journey U m l) 0 C)(hh:∀ i:Edge (Site n),i.1∈P→B.threshold*(1+(separation i.1 0:ℝ))^B.power ≤ 1) : Clear B.order (B.dirBound (0:Site n)) U t C:=by
   refine ⟨hx,fun l he ht=>?_⟩; let d:=l.length; let V(j:Fin l.length)(i:Edge (Site n)):= if i.1∈P then l.get j i else 0; let W(j:Fin l.length):= l.get j
   have hf(j i):‖V j i‖≤1:=by unfold V; split; exact (ht _ (List.get_mem ..) i).trans (hh _ (by assumption)); simp
   have hz:= hg d V he (fun i j=>hf j i)
   have hu : t ∘ journey U l.length W=t ∘ journey U l.length V:=by
      refine funext (fun p=> hp _ _ (fun i hi hj=>?_)); simp_rw [journey_value,V,if_pos (show i.1∈ P from hi)];rfl
   rw [show leftDerivs t l U= iteratedFDeriv ℝ l.length (t ∘ journey U l.length W) 0 WardBin.Lies.cart from (by simpa only[List.ofFn_get] using Germ.ordered l.get ((show Germ B.order t U from hx).prod he)),hu]; refine le_trans (ContinuousMultilinearMap.le_opNorm ..) ?_; rw [prod_eq_one, mul_one]; exact hz.norm_le _ he; intro i _; rw [show WardBin.Lies.cart i=bolt i by ext1 j;simp [bolt, WardBin.Lies.cart,Pi.single_apply]]; exact norm_bolt i
lemma psaltery(G:Gauge)(k:ℕ):∃ f:ℕ→ℝ, MarksP f ∧ ∀ (n:Side)(R:Rep G n)(i:Barley)(s:Seat n)(U:Config G n) (P:Support n), R.p.B≥2→R.p.order=k→ (∀ v : Edge (Site n), v.1∈officeC R s i→ R.p.threshold*(1+(separation v.1 0:ℝ))^R.p.power ≤1)→
    Clear R.p.order (R.p.dirBound (0:Site n)) U (fer R s i) (port R i*f (mote R i)):=by
    obtain ⟨A,hA,H⟩:= charter k G
    obtain ⟨f,hf,H'⟩:= black G A k hA; refine ⟨f,hf,fun n R b s U P hB hp ht=>?_⟩; subst k; let K:= officeC R s b
    apply scrolls R.p U _ A (P:=K) (ferLocal R s b hB) (show ContDiffAt ℝ R.p.order _ _ from (lick R id (s,b) _ _ (incrementA U 0)).of_le le_top) _ ht
    intro m l hh hx; exact H' _ R _ _ (fun i=>H n U m i l hh (hx i)) s b
abbrev wick (s:ℝ)(o:Edge (Site n))(U:Config G n)(v:G.Color):= Tint o v s U
def saw (R:Rep G n)(s:ℝ)(o:Edge (Site n))(x:Seat n × Barley):Mellow G n:=fun U v=> Shepherd.wake R x.2*(fer R x.1 x.2 U-fer R x.1 x.2 (Tint o v s U))
abbrev fabrics (R:Rep G n)(j:Seat n × Barley):=officeC R j.1 j.2
lemma saw_cohort (s:ℝ)(o:Edge (Site n))(j:Seat n × Barley)(p:Support n){σ S A:ℝ}(H:R.path.Bounds R.clip σ S A)(hk:2≤ R.p.B)(hp:fabrics R j⊆ p) : Cohort R.p p o (saw R s o j):=by
   let F:= fer R j.1 j.2; have hf:= ferInv R j.1 j.2 H; have ht:= ferLocal R j.1 j.2 hk; refine ⟨fun w U V hv=>?_,fun x v G=>?_,?_,?_⟩
   · have hx := agrees_mono hv (coe_subset.mpr hp); exact congr_arg₂ (·*·) rfl (congr_arg₂ (·-·) (ht _ _ hx) (ht _ _ (Tint.holds _ _ _ _ _ w hx)))
   · unfold saw; rw[Tint.turn,hf,hf]
   · have h : Measurable F :=(WardBin.left_cont F (fun U=> (lick R id j _ _ (incrementA U 0)).continuousAt)).measurable
     have hh : Measurable (fun p:Config G n × G.Color=> Tint o p.2 s p.1):= Continuous.measurable (f:=fun p:Config G n × G.Color=> Tint o p.2 s p.1) ((tint_c o s).comp (f:=fun p:Config G n × G.Color=>(p.2,p.1)) (continuous_snd.prodMk continuous_fst))
     exact ((h.comp measurable_fst).sub (h.comp hh)).const_mul _
   intro X _ _ V x t hv he _ _; exact (((lick R id j V x hv).sub (lick R id j (fun y=>Tint o (t y) s (V y)) x (Tint.arm hv he))).const_smul (Shepherd.wake R j.2)).of_le le_top
abbrev ladder (R:Rep G n)(j:Seat n × Barley)(f:ℕ→ℝ):=2*|Shepherd.wake R j.2| * (port R j.2*f (mote R j.2))
lemma saws (G:Gauge)(k:ℕ):∃ f:ℕ→ℝ,MarksP f ∧∀ (n:Side)(P:Support n)(R:Rep G n)(j:Seat n × Barley)(s:ℝ)(o:Edge (Site n))(r:ℕ),fabrics R j⊆halo r {0}→R.p.order=k→2≤ R.p.B→ R.p.threshold*(1+(r:ℝ))^R.p.power ≤1→ Career R.p P (saw R s o j) (ladder R j f):=by
   obtain ⟨f,hf,H⟩:= psaltery G k; refine ⟨f,hf,fun n P R j s o r hr hk hB hp U hu v hv=>?_⟩
   have ht(U:Config G n):= H _ R j.2 j.1 U P hB hk (fun i hi=>?_); rotate_left
   · have hm:= hr hi; obtain ⟨x,hx,hs⟩:= halo_spec.mp hm; rw[mem_singleton.mp hx,separation_comm] at hs; apply le_trans _ hp; have h:=R.p.threshold_pos; gcongr
   exact (((ht U).sub (Tint.troop (B:=R.p) (ht (Tint o v s U)))).scale (Shepherd.wake R j.2)).weaken (le_of_eq (by unfold ladder; ring))
end YM.Trace.Wicket
