import YM.TraceExtension.Loft.Leaf
set_option autoImplicit false
/-!
# VIZ with Wilson specialization. No mollifier short distance assertion here;
formal coefficient test is local quadratic of exact Haar Jacobian rooted current.
Resource for physical control at that scale.
-/
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG RG.Supply Wilson Finset Push.Uniform Audience Metric Lamp Det Planned.PrimaryIntegral295 Next.Free Org Input Extra.Histories
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W:Type}{g:W→Side}{F:Filter W}{G:Gauge}{f:Side}{M: Metals G}{D:Rolls M.p}{A:Alloy M D}{α σ a C:ℝ}
lemma wire_mid (A:Alloy M D)(k:ℕ)(hG:G.Simple)(δ:ℝ)(hd:0 < δ)(ha:0 < a)(hc:0 ≤ C):∃ x:ℝ,0< x ∧ ∃ T:ℕ,∀ (N p:ℕ), k<N→ T≤ p→ let f:=A.B.a.S.side k p; let s:= A.B.a.params k; ∀ Q:Dart G f,Q.March → (Viz Q s.clip (A.B.kin.path N k) a (fun _=>C) (fun _=>x) x)→∀ q, |midPay q Q - landPay G| ≤ δ:=by
    classical
    by_contra! he
    let u(i:ℕ):ℝ:=1/(1+i)
    have hu(i):0<u i:=by unfold u; positivity
    have hx:Tendsto u atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_atTop_mono (f:=fun x:ℕ=>(x:ℝ)) (fun x=> le_add_of_nonneg_left (by norm_num : 0≤(1:ℝ))) tendsto_natCast_atTop_atTop)
    -- see normalized nnf
    simp only[not_forall,exists_prop,not_le] at he
    choose N p hn hp Q hQ hV b hy using fun i=> he (u i) (hu i) i
    let s:=A.B.a.params k; let g(i:ℕ):=A.B.a.S.side k (p i); let R(i):=A.B.kin.path (N i) k
    have hf:Tendsto (fun w=>(g w).val) atTop atTop:= (deep_n A.B.a.S k).comp (tendsto_atTop_mono hp tendsto_id)
    obtain ⟨H,Y,X,E,ε,σ,U,W,h⟩:=colorWire N p k hn hG A
    have ht:Scene g Q s.clip R a C u:= ⟨hV,hQ,ha,hc,fun i=> ⟨(hu i).le,div_le_self zero_le_one (le_add_of_nonneg_right (by positivity))⟩⟩
    have hv (q:G.ColorIndex):= midAwake q h ht hf s.width_pos hx H hG
    obtain ⟨i,hi⟩:= (eventually_all.mpr fun q=> (hv q).eventually (ball_mem_nhds _ hd)).exists
    exact not_lt_of_ge (le_of_lt (show |midPay (b i) (Q i)-landPay G|< δ by simpa [Real.dist_eq] using mem_ball.mp (hi (b i)))) (hy i)

include A
lemma dewWt (B:Bolt A)(V:Vigil A.B.a) (hG:G.Simple): ∀ᶠ k:ℕ in atTop,∀ ε:ℝ,0< ε → ∀ (F:Filter W)(N p:W→ℕ), Tendsto N F atTop → Tendsto p F atTop → ∀ᶠ w in F,
    let Z:=(Issue.trail B).rep (N w) (p w) k; let x:=A.B.a.clock.hatBeta k
    ∃ Q:Dart G (A.B.a.S.side k (p w)), Viz Q Z.clip Z.path (east x) (fun _=> trophy x) (fun _=> ε) ε ∧ Q.March ∧ ∀ q:G.ColorIndex, |midPay q Q- landPay G| ≤ ε:=by
    filter_upwards[treasury (W:=W) V B] with k hk ε hε F N p hN hp
    let φ:=A.B.a.clock.hatBeta k; have hh:0≤ trophy φ:=sum_nonneg fun i _=>abs_nonneg _; have he:0<east φ:=inv_pos.mpr (Real.log_pos (A.B.a.fits.delayed k))
    obtain ⟨x,hx,T,H⟩:= wire_mid A k hG ε hε he hh
    let y:=min ε x; have hz:0 < y:=lt_min hε hx
    filter_upwards [hk y hz F N p hN (fun i=> (deep_n A.B.a.S i).comp hp),hp.eventually_ge_atTop T,hN.eventually (eventually_gt_atTop k)] with w hw hv hw'
    intro R Y; let K:= A.B.kin.path (N w) k; let s:= A.B.a.params k
    have h1:R.clip=s.clip:= (B.choice.represents (N w) (p w) k hw'.le).clip; have h2:R.path=K:=(actual_path B (N w) k (p w) hw'.le).symm
    obtain ⟨Q,hQ⟩:=hw; change Viz Q R.clip R.path (east φ) _ _ _ at hQ;rw[h1,h2] at hQ ⊢
    have hx (i:ℕ)(hi:i ≤ 4):reed φ i+1≤ trophy φ:= (le_abs_self _).trans (single_le_sum (f:=fun i=>|reed φ i+1|) (fun i _=>abs_nonneg _) (mem_range.mpr (by omega)))
    have hh:=Q.gull (A.B.support.cap (N w) k hw'.le) hQ
    exact ⟨Q.sing,upsize hh (min_le_left ..) (fun i hi _=>hx i hi) (fun _ _ _=> min_le_left ..), Q.singed,H (N w) (p w) hw' hv Q.sing Q.singed (upsize hh (min_le_right ..) (fun i hi _=> hx i hi) (fun _ _ _=>min_le_right ..))⟩
end YM.Trace.Loft
#print axioms YM.Trace.Loft.dewWt
