import YM.TraceExtension.Swift.Whet
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Matrix Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory
open PhysicalNext.JointLoad.Heir
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {n:Side} (m:ℕ){P' P:Support n}{F:Peat G n}{Y:Gal G n} {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
lemma lantern (s:ℝ)(hp:Drift _ F)(hh:Clouded Y P)(hy:LocalOn P F)(hInv:GaugeInvariant F) (B:BudgetPoint) (h:P⊆P'): B.Regular P' (atuneU m Y F s P):=by
    let f:= atuneU m Y F s P
    have hx(U:Config G n):ContDiffAt ℝ B.order (f ∘ increment U) 0:=by
        unfold f atuneU atune Function.comp; refine ContDiffAt.sum fun i _=>?_ ; let Z:= tuna i; let X(v:Directions G n)(x:G.Color):= rumba m Y F s (beaconR i) x (increment U v)
        have he (x:G.El):ContDiffAt ℝ B.order (uncurry X) (0,Z x):=by
            have hx (v:Directions G n×G.Color): Army (fun w:Directions G n×G.Color=> increment U w.1) v:= fun j=> ((incrementA U v.1) j).comp (g:=fun x:Directions G n=> G.mat (increment U x j)) (f:=Prod.fst) v contDiffAt_fst
            exact (leot m hp hh.wakes _ (V:=Prod.snd) _ (t:=s) _ (hx (0,Z x)) contDiffAt_snd).of_le le_top
        exact Planned.AtomRegular.Covered.leaves (Ebon.course G.probHaar X Z 0 he (tuneH _)) (EventuallyEq.refl ..)
    refine regularAi (fun k U=>?_) (fun U V hv=>?_) hx
    · unfold atuneU atune; apply sum_congr rfl; intro i _; let x:=beaconR i; let N(y:G.El):= rumba m Y F s x (tuna i y) (Lattice.gauge k U)
      change (∫ y,N y ∂G.probHaar)=_; rw [← integral_mul_left_eq_self N (k x.1)]
      refine integral_congr_ae (Eventually.of_forall fun y=> ?_); change rumba _ _ _ _ x (G.adjoint (k x.1*y) _) _=_; rw [Gauge.adjoint_mul]; exact rumba_r m hh hInv U x s _ k
    · unfold atuneU atune; apply sum_congr rfl; intro i _; refine integral_congr_ae (Eventually.of_forall fun y=>?_); unfold rumba; dsimp only; rw [show orbC Y F U (beaconR i) (tuna i y)=_ from funext fun v=> orb_local (beaconR i) (tuna i y) hy hh.stout U V (agrees_mono hv h) v]
lemma through_sum {I:Type}{k:ℕ} {f:I→X→ℝ}(S:Finset I)(c:I→ℝ)(x:X)(h:∀ i∈S,Through k (f i) x (c i)): Through k (fun x=>∑ i∈S,f i x) x (∑ i∈S,c i):=by
    refine ⟨ContDiffAt.sum (fun i hi=> (h i hi).1),fun j hj=>?_⟩; rw [iteratedFDeriv_fun_sum_apply (fun i hi=> ((h i hi).1.of_le (m:=j) (Nat.cast_le.mpr hj)))]; exact (norm_sum_le ..).trans (sum_le_sum fun i hi=> (h i hi).2 j hj)
abbrev tides(m:ℕ)(C h s:ℝ)(P:Support n):ℝ:= (P.card * Fintype.card (Loc G 1):ℕ)*(tome m*C*(h/s)^(m+1))
lemma heaps (m:ℕ)(J:BudgetPoint){C K s h:ℝ} {k:ℕ}(hm:1≤ m)(hp:0 < s)(hs:0<h)(hf:Drift _ F)(hY: Clouded Y P)
    (ht:∀ (o: Bond n),o.1∈P→∀ v:G.Color, ‖v‖≤1→∀ x:Rho G n,‖x.1‖ ≤ K→ 0 ≤ x.2→x.2 ≤ kettle m*(h/s) → Allows (k+m+1) (Orpus o v F Y s) x C) : ∀ x:Directions G n,‖x‖≤ K→ Through k (minor (atuneU m Y F h P) s) x (tides (G:=G) m C h s P):=by
    intro x hx; let U(y):= increment (1:Config G n) (s • y)
    let H:= P ×ˢ (@univ (Loc G 1) _)
    let F'(i:Lines G n 1)(z: Directions G n)(v:G.Color):= rumba m Y F h (beaconR i) v (U z); let B:= tome m*C*(h/s)^(m+1)
    have hh(i: Lines G n 1)(hi:i∈H):Through k (fun z=>∫ v,F' i z (tuna i v) ∂G.probHaar) x B:=by
        let f(y:Directions G n×G.Color):= U y.1
        apply Ebon.fond G.probHaar (F' i) (tuna i) x ?_ (tuneH _) _ ?_
        · intro u; let z:=(x,tuna i u); have ha: Army f z:=by
              intro j; exact (incrementA (1:Config G n) (s • z.1) j).comp (g:=fun w:Directions G n=> G.mat (increment (1:Config G n) w j)) (f:=fun y:Directions G n×G.Color=> s • y.1) z (ContDiffAt.const_smul (c:=s) contDiffAt_fst)
          exact (leot m hf hY.wakes f Prod.snd _ z h ha contDiffAt_snd).of_le le_top
        intro v; let b':=beaconR i
        exact Through.control (fringe J hm hp hs hf hY.wakes (ht b' ((Finset.mem_product.mp hi).1) (tuna i v) (litChrom i.2.2 v|>.le)) x hx)
    have he:= through_sum (f:=fun i z=>∫ v,F' i z (tuna i v) ∂G.probHaar) H (fun _=> B) x hh
    rw [sum_const,nsmul_eq_mul,show H.card=P.card*Fintype.card (Loc G 1) from (by simp[H])] at he; exact he
open Outer.Nodes
lemma merem (F:Peat G n)(Y:Gal G n)(o:Bond n)(m:ℕ)(x:G.Color)(t:ℝ)(U:Config G n): duel m t (orbC Y F U o x) = ∑ i∈range m,wage m i * (orbC Y F U o x (loc i*t)- clamor o Y x U):=by unfold duel; simp [orbC,rung,science]
def tDust(m:ℕ)(Y:Gal G n)(F:Peat G n)(P:Support n)(h:ℝ)(U:Config G n):= atune (fun e v U=>duel m h (orbC Y F U e v)) P U
lemma erum (f:Peat G n)(V:Gal G n)(p:Support n)(hp:Clouded V p)(h:Drift _ f)(hm:ℝ)(U:Config G n):
   tDust m V f p hm U= atuneU m V f hm p U+ hm*(lush V U+rill f V U):=by
    let S:= p ×ˢ (@univ (Loc G 1) _); let Z(i:Lines G n 1)(v:G.El):= orbC V f U (beaconR i) (tuna i v);
    have hh(i:Lines G n 1): Continuous fun v:G.Color=>duel m hm (orbC V f U (beaconR i) v):=by
         unfold duel; apply continuous_finsetSum; intro j _; refine Continuous.const_smul (c:=wage m j) ?_; apply Continuous.sub; all_goals refine continuous_iff_continuousAt.mpr (fun w=> (thunder h hp.wakes (fun _=>U) id (fun _=>_) w (Army.park U w) contDiffAt_id contDiffAt_const _).continuousAt)
    let T (i: Lines G n 1)(v:G.El):=duel m hm (Z i v); let D(i:Lines G n 1)(v:G.El):=rumba m V f hm (beaconR i) (tuna i v) U
    have ht(i): Integrable (T i) G.probHaar:= ((hh i).comp (tuneH i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hD(i): Integrable (D i) G.probHaar:= (((show Continuous (fun v:G.Color=>rumba m V f hm (beaconR i) v U) from continuous_iff_continuousAt.mpr (fun w=> (leot m h hp.wakes (fun _=>U) id _ w hm (Army.park U w) contDiffAt_id).continuousAt)).comp (tuneH i))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    change (∑ i∈ S,∫ x, T i x ∂G.probHaar)=(∑ i∈S,∫ x, D i x ∂G.probHaar)+_
    apply sub_eq_iff_eq_add'.mp; rw[← Finset.sum_sub_distrib]; simp_rw [← integral_sub (ht _) (hD _)]; rw[← integral_finsetSum]; rotate_left
    · intro i _; exact (ht i).sub (hD i)
    apply Eq.trans (integral_congr_ae (Eventually.of_forall (fun v:G.El=> ?_))) (show (∫ x:G.El,hm*(lush V U+rill f V U) ∂G.probHaar)=_ by simp)
    change ∑ i∈ S,_ =_; rw[← astrolabe V f U p hp h v, Finset.mul_sum]; apply sum_congr rfl fun i _=>?_ ; exact sub_sub_cancel ..
end YM.Trace.Swift
