import YM.TraceExtension.Margin.Bald
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Wicket Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
open Zn
variable {F:Frame G 4}{Z:Frame G 5}{n:Side}{t:ℝ}{R:Rep G n}{J:Dart G n}
open Lamp Turret Det Stationary Exterior Tree
lemma fee_in(v: loom G n)(x:Site n)(d:ℝ)(u z:Tit G)(a:ℝ)(hp:Estate x (ballX v.val) a (fun _=>d))(ha:0≤a): ‖loom₂ n G (ballad u x) (ballad z x) v‖ ≤16*d:=by
   let H:= iteratedFDeriv ℝ 2 (ballX v.val) 0; let T:Fin 2→ Acr G n:=![ballad u x,ballad z x]; let X:= landW x (G:=G)
   change ‖H T‖≤_; erw[many (.atomic 2) H T]
   apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_left (hp.values 2 (by norm_num) le_rfl) (by norm_num) : 16*cost X a 4 0 (Perfect.leaf _ _ _) ≤ 16*d)
   unfold Perfect.cost; rw [Finset.mul_sum]; apply sum_le_sum; intro i _; let r:ℝ:=limitN X i; let R:=(1+r)^2
   have hP(k:Fin 2)(t:Tit G): |ballad t x (i k)| ≤ 4*R:=by
      have ht:= ballad_bound t x (i k); apply ht.trans; unfold R r; gcongr; exact limitN_ge ..
   change ‖(∏ j:Fin 2,T j (i j)) • bank H i‖≤16*(Perfect.spot a 4 0 _*‖bank H i‖)
   rw[norm_smul,Real.norm_eq_abs,Fin.prod_univ_two,abs_mul,← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
   have hr:0≤r:=Nat.cast_nonneg _; apply (mul_le_mul (hP 0 u) (hP 1 z) (abs_nonneg _) (by unfold R; positivity)).trans
   unfold Perfect.spot Perfect.shelter; rw[sub_zero]; change _ ≤16*((1+ max 0 r)^4*Real.exp (a* max 0 r)); rw [max_eq_right hr]; apply le_trans (le_of_eq (b:=16*((1+r)^4)) (by unfold R; ring)); apply mul_le_mul_of_nonneg_left _ (by norm_num); exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (mul_nonneg ha hr))
lemma hi_cast(F:Frame G 4){E:Type}{L:Filter E}{f:E→ F.Coeff}{y:F.Coeff} (he:∀ J:Jet G, Tendsto (fun i=> Ask F J (f i)) L (𝓝 (Ask F J y))): Tendsto f L (𝓝 y):=by
    -- finite spanning Ask probes. compact norm argument
    let P(i:Jet G × ℕ): Set F.Coeff:= {z| ‖z‖ < (i.2 :ℝ)*‖Ask F i.1 z‖ }
    have ho(i) : IsOpen (P i):= isOpen_lt continuous_norm (continuous_const.mul ((Ask F i.1|>.continuous_of_finiteDimensional).norm))
    have hh : Metric.sphere (0:F.Coeff) 1 ⊆ ⋃ i,P i:=by
       intro x hx; have hN:x≠0:=by intro h; simp [h] at hx
       obtain ⟨J,hj⟩: ∃ J,Ask F J x≠0 :=by
           by_contra! hz; apply hN; apply F.coords.symm.injective; apply label_ext; intro J; calc
             _=0:=hz J
             _=_:=by simp
       obtain ⟨i,hi⟩:= exists_nat_gt (‖x‖/‖Ask F J x‖); exact Set.mem_iUnion.mpr ⟨(J,i), (div_lt_iff₀ (norm_pos_iff.mpr hj)).mp hi⟩
    obtain ⟨S,hS⟩:= (isCompact_sphere (0:F.Coeff) 1).elim_finite_subcover P ho hh; let Q:=fun i=>f i-y
    apply Metric.tendsto_nhds.mpr;intro e hE; have hv(i:Jet G×ℕ):Tendsto (fun j=>(i.2:ℝ)*‖Ask F i.1 (Q j)‖) L (𝓝 0):=by have ht:=( (he i.1).sub_const (Ask F i.1 y)).norm.const_mul (i.2:ℝ); simpa only[Q,map_sub,sub_self, norm_zero,mul_zero] using ht
    filter_upwards [(eventually_all_finset S).mpr (fun i hi=> (hv i).eventually (gt_mem_nhds hE))] with j hj
    rw[dist_eq_norm]; by_cases he':Q j=0
    · change ‖Q j‖<_; rw[he',norm_zero]; exact hE
    let v:ℝ:= ‖Q j‖⁻¹; have hu:0< v:=inv_pos.mpr (norm_pos_iff.mpr he')
    obtain ⟨i,hi,h₁⟩:= Set.mem_iUnion₂.mp (hS (show v • Q j∈_ by unfold v; simp[norm_smul,he']))
    change ‖v • Q j‖< (i.2:ℝ)*‖Ask F i.1 (v • Q j)‖ at h₁; rw [norm_smul,map_smul,norm_smul, Real.norm_of_nonneg hu.le, mul_left_comm] at h₁; exact lt_trans ((mul_lt_mul_iff_right₀ hu).mp h₁) (hj i hi)
section voyage
variable {W:Type}{n:W→Side}{t:W→ℝ}{L: Filter W}{R:∀ w:W, Rep G (n w)}{X:∀ w, Dart G (n w)}
variable (hn:Tendsto (fun w=>(n w).val) L atTop)(ht:Tendsto t L atTop)(hp:∀ w, Nonwrapping (tempQ (t w) (n:=n w)) 0)(hs:G.Simple)(hC:∀ w,Club (R w) (t w) (Meld (X w) (t w)))(hX:∀ w,Sight (t w) (R w) (X w))(he:∀ w,4 ≤(R w).p.order)
include hn ht hs hC hX
lemma conceive (i j:Axis) : Stoke L (fun w=>(0:Site (n w))) (fun w=>ballX (Meld (X w) (t w) i j 0)) (fun p q=>north p q 0 i j) 4:=by
   constructor;intro u v hv; let f(w):loom G (n w):=⟨(X w).J i j 0,(hX w).1.sound.heart ..⟩; let g(w):loom G (n w):=⟨Meld (X w) (t w) i j 0,((hC w).peek i j).silk⟩
   let F (w):loom G (n w) →ₗ[ℝ] ℝ:= loom₂ (n w) G (ballad u 0) (ballad v 0); have hz: Tendsto (fun x:ℝ=> shock x+16*calorie x) atTop (𝓝 0):=by
        have he(m:ℕ)(h:m≠0): Tendsto (fun x:ℝ=>(x^m)⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_pow_atTop h)
        simpa only[shock, calorie, mul_zero,add_zero] using! (he 100 (by decide)).add ((he 30 (by decide)).const_mul 16)
   refine Metric.tendsto_nhds.mpr (fun ε he=>?_); filter_upwards [ht.eventually (sense G 0 5 le_rfl),ht.eventually (Zn.eastP), (hz.comp ht).eventually (gt_mem_nhds he)] with w hw hx hp
   let y:=t w; let z:=north u v 0 i j; have ha:0 ≤ eastD y:= div_nonneg hx.1.le (by norm_num); have hu: ‖F w (f w-g w)‖ ≤16*calorie y:=fee_in (f w-g w) 0 (calorie y) u v (eastD y) ((hw _ _ _ (hX w)).1 i j|>.lid 0|>.pay) ha
   have hv:= ((hX w).1.ox i j 0).bill u v hv; rw [Real.dist_eq]; change |F w (g w)-z| < _; change |F w (f w)-z| ≤ shock y at hv; rw[_root_.map_sub] at hu; change |_ - _| ≤ _ at hu; rw [show F w (g w)-z=(F w (f w)-z)-(F w (f w)- F w (g w)) from by abel]; exact lt_of_le_of_lt ((abs_sub ..).trans (add_le_add hv hu)) hp
include hp he
lemma arch_p(F:Frame G 4)(H:Hol G)(b c: Axis) : Tendsto (fun w=> cardX F H (t w) (Meld (X w) (t w)) b c) L (𝓝 (F.coords (-raw G b c))):=by
    apply hi_cast; let V' (i):loom G (n i):=⟨Meld (X i) (t i) b c 0,((hC i).peek b c).silk⟩; let P i:= F.coords.symm (cardX F H (t i) (Meld (X i) (t i)) b c);intro J
    rw[show Ask F J (F.coords (-raw G b c))=prink J (-raw G b c) from (congr_arg (fun x=>prink J x) (F.coords.symm_apply_apply _))]
    exact peg (X:=V') (v:=P) hn (fun i=> (card_reads F (H:=H) (Real_regular (hC i|>.peek b c|>.puff.regular)) (he _) (hp i) : JetTest H 0 (P i) (filmR (V' i).val))) hs b c (conceive hn ht hs hC hX b c) J
end voyage
end YM.Trace.Margin
