import YM.TraceExtension.Quince.Grade
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Pieces
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson RG Pressure Pressure.Tube Precision Labels Source Push Local Planned.PrimaryIntegral295
open Next Next.Foundations Next.Scheduling Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Exterior Bloch JointLoad JointLoad.Heir
open Push.AbsoluteSums Gas Ovens ConnectedActivityE6 Coat Brim Cub Extra.Iteration Extra.Iteration.Scales Malachite
open Place PPX Carrier Next.Free
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{T:Teller G}{L:Side}{σ s:ℝ}{f:ℝ→ℝ}
def sprite (G:Gauge)(x:ℝ)(L:Side)(z:ℝ):= z/coinP G L x
lemma sprite_pos (x:ℝ)(hs:0<s):0<sprite G x L s:=div_pos hs (coinP_pos ..)
lemma sprited (h:fRate G L f) {a:ℝ}(hp:0<a):∀ᶠ x in atTop, |f x| ≤ sprite G x L a:=by filter_upwards [h.eventually (Metric.ball_mem_nhds 0 hp)] with x hx; have hb:=coinP_pos G L x; unfold sprite; rw [le_div_iff₀ hb,mul_comm]; have hx:= (show |coinP G L x*f x| <a from by simpa [Real.dist_eq] using Metric.mem_ball.mp hx); rw [abs_mul, abs_of_pos hb] at hx; exact hx.le
lemma cutRate (hs:0<σ)(C d:ℝ)(g) (p:Rate G L d g): Rate G L C (fun x=> Real.exp (-σ*(reach x))*g x):=by
    have hx : Rate G L (C-d) (fun x=> Real.exp (-σ*(reach x))) := (Rate.cutoff (G:=G) (L:=L) hs).compare (Eventually.of_forall (fun x=>by
        rw[abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; exact mul_le_mul_of_nonpos_left (by unfold Heir.reach Stores.till; exact_mod_cast (by omega : radiusB x/100000 ≤45*(1+radiusB x))) (by linarith)))
    simpa only [sub_add_cancel] using hx.mul p
lemma colorK (K M:ℝ) (hp:0<σ)(d:ℕ)(a:ℝ): Rate G L a (fun x=> εℓ σ d (radiusD x) (reach x) K M):=by
    unfold εℓ; apply rate_sum; intro i _; have hw:= widthCost_ge (half_pos hp) (d*i); let v(x:ℝ):=(K+K)*(1+4*(radiusD x:ℝ))^(d*i)
    have he : Rate G L 0 v:= by unfold v; simpa only [zero_mul] using ((((Rate.const 1).add ((spanDO G L).mul_left 4)).pow (d*i)).mul_left (K+K))
    let Z:=widthCost (σ/2) (d*i); exact (((cutRate (half_pos hp) a 0 v he).mul_right Z).mul_right M|>.mul_left 4).congr (Eventually.of_forall fun i=>by unfold δℓ v; ring)
lemma cornK (K M:ℝ)(d:ℕ): Rate G L 0 (fun x=> corn₀ d (radiusD x) L σ K M):=by
    unfold corn₀; apply Rate.add (Rate.const _); apply rate_sum; intro i _; unfold horn₀
    have hv: Rate G L 0 (fun x=> (depthW L (radiusD x):ℝ)):=by
        unfold depthW; simp_rw [Nat.cast_mul, show ∀ t:ℕ, ((↑(t+2):ℝ))=(t:ℝ)+2 from fun _=>by push_cast;rfl]; exact (((spanDO G L).add (Rate.const 2)).mul_left (L.val:ℝ))
    simpa only[zero_mul] using ((((Rate.const 1).add (hv.mul_left 4)).pow _).mul_left _)
lemma εGoal (K M:ℝ)(hp:0<σ)(N d:ℕ)(G':Rights G N): fRate G L (fun x=> let ℓ:=εℓ σ d (radiusD x) (reach x) K M; ∑ i∈Finset.range (d+1), (Fintype.card (OrderedFinpartition i):ℝ) * (2:ℝ)^i*(ℓ*(corn₀ d (radiusD x) L σ K M)^i * G'.fee)):=by
    apply fGood (a:=-(1:ℝ)) _ (by norm_num); apply rate_sum (w:=fun i x=> _*( _ * _^i * _ )); intro i _; have hx:= ((colorK (G:=G) (L:=L) K M hp d (-1)).mul ((cornK (σ:=σ) (G:=G) (L:=L) K M d).pow i))
    simpa only [zero_mul,add_zero] using ((hx.mul_right G'.fee).mul_left ((Fintype.card (OrderedFinpartition i):ℝ) * 2^i))
variable {d b n r:ℕ}
lemma fourrate (k:ℝ)(H:Hol G)(p:Probe G d) (G':Rights G n)(hp:0<k) (hq:4≤ b)(hv:4≤ r)(hd:d ≤ b) (hN:d ≤ n) (L:Side) (y:ℝ)(hy:0<y):∀ᶠ x:ℝ in atTop,∀ (u v:BudgetPoint), Blend 2 v.threshold u.threshold → n≤v.order →∀ (c f:Side)(S:StepData c f)(T:Tube G S)(X:Support f)(Y:Support c), S.patch.L=L→ (∀ i∈X,halo (Heir.reach x) {S.ratio.parent i}⊆Y) →(∀ i∈Y,separation 0 i ≤ Malachite.radiusD x)→ 20*(radiusD x+reach x+1)< c.val → ∀ (V:Flight b r),L=V.L → HEq T.R.A0 (Carrier.linesOf V k) → ∀ (f':Config G f→ℝ)(t:ℝ), v.Regular X f'→ v.supBounds 0 X f' t → Peak.lit 0 X f' d →
    ‖iteratedDeriv p.2.val (dimW 0 (Malachite.radiusD x) T f' ∘ H.testLinks d 0 (u.threshold • p.1)) 0‖ ≤ sprite G x L y*t:=by
    obtain ⟨σ,K,hσ,hK,Hk⟩:= Carrier.priced k hp hq hv
    choose fzz h hpz using fun i=> Ramble.gathered p 2 one_le_two i
    let a:=1+∑ i∈Finset.range (d+1), fzz i; have hA:1≤a:= le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>h i))
    have he : ∀ᶠ x in atTop, εℓ σ d (radiusD x) (Heir.reach x) a K ≤1:=(colorK (G:=G) (L:=L) a K hσ d (-1)|>.below (by norm_num) _ zero_lt_one).mono (fun x h=> (le_abs_self _).trans h)
    filter_upwards [he, sprited (εGoal (L:=L) a K hσ n d G') hy] with x he h u v hT h' c f S T X Y hL hx hX hx' V hℓ hΦ f' t hC hp' ht
    let s:= p.2.val; have hs : s≤ d:=Nat.le_of_lt_succ p.2.isLt
    have hh := corn_pos d (radiusD x) S.patch.L hσ (by positivity : 0≤a) hK.le
    have hσ : T.R.A0.strip σ K := by
       have ht (L:Side)(P:Lines L)(h:L=V.L)(he:HEq P (linesOf V k)) : P.strip σ K:=by subst L; rw[eq_of_heq he]; have he:= Hk V [] (by simp); exact Work.F08.strip_mono he le_rfl (by simpa using div_le_self hK.le (show 1≤(V.L.val:ℝ) by exact_mod_cast V.L.property))
       exact ht _ _ (hL.trans hℓ) hΦ
    have hψ (i:ℕ)(hi:i ≤ d):Carries (Ramble.lamina p i v.threshold u.threshold) (d*i) a:=by
        have hp:= hpz i u.threshold v.threshold hT|>.1; refine ⟨zero_le_one.trans hA,fun x j=> (hp.2 x j).trans ?_⟩; apply mul_le_mul_of_nonneg_right _ (liftCost_pos ..); exact (Finset.single_le_sum (s:=Finset.range (d+1)) (fun i hi=> (‹∀ i,0≤fzz i›) i) (Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)
    have hz := zert H hC hp' G' hσ ‹0<σ› hK.le hA hp hx' hx hX ht hN h' hψ s hs V hΦ (hL.trans hℓ) hv hd (he.trans hh)
    apply hz.trans; apply mul_le_mul_of_nonneg_right _ hp'.1
    let f i:= (Fintype.card (OrderedFinpartition i):ℝ)*2^i*((εℓ σ d (radiusD x) (reach x) a K)*(corn₀ d (radiusD x) L σ a K)^i * G'.fee)
    have hh:= hL ▸ hh; rw [hL]; refine LE.le.trans (?_ : f s ≤ ∑ i∈Finset.range (d+1), f i) ((le_abs_self _).trans h)
    apply Finset.single_le_sum (fun i _=> ?_) (Finset.mem_range.mpr (by omega))
    unfold f; have he := G'.large; positivity [εℓ_pos (reach x) (radiusD x) d ‹0<σ› (show 0≤a from by positivity) hK.le]
end YM.PhysicalNext.Repeat.Quince
