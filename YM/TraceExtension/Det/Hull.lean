import YM.TraceExtension.Det.Koan
import YM.Next.STATIONARY.Spectral.AuxReferences
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open Next.SectorChange
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k l m n r:ℕ}{α a b τ A C D μ:ℝ}
    {I:Type*}[Fintype I][DecidableEq I]
lemma pet_fixed {I X:Type}[Fintype I][NormedAddCommGroup X][NormedSpace ℝ X] (t:X)(o:Site f)(l:I→Site f) (V:ℝ)(he: ‖t‖≤V): Pet l o (fun _=>t) a V n:=by
    refine ⟨contDiffAt_const,fun i hi q=>?_⟩; have hv:0 ≤ V:= (norm_nonneg _).trans he; match i with
    | 0=> simpa only [entry,spanSites,sum_of_isEmpty,iteratedFDeriv_zero_apply,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using he
    | k+1=> unfold entry; rw[iteratedFDeriv_const_of_ne (by simp)]; simp; positivity
lemma park_mass (g:Gauge)(n':Side)(a:ℝ)(u:ℝ)(k:ℕ)(hu:‖u‖≤C)(n:ℕ): Park (fun _:Link g n'=> (u • (1: Funds (Lines g n' k)))) a C n:=by
    have hv:0≤C:= (norm_nonneg _).trans hu; intro i j; refine pet_fixed _ _ _ _ ?_; by_cases h:i=j
    · subst j; simp only[Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,mul_one,Decay,separation_self,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one];exact hu
    simp only[Matrix.smul_apply, Matrix.one_apply_ne h, smul_zero,norm_zero]; exact mul_nonneg hv (decay_pos ..|>.le)
lemma body_charge (G:Gauge)(p:Clip)(k:ℕ)(α:ℝ)(hc:0<α)(A:ℝ)(μK:ℝ): ∃ η C, 0<η ∧ 0 ≤ C ∧ ∀ (n:Side)(R:PathData G)(D:ℝ), R.Bounds p α A D→ ∀ μ:ℝ,0≤μ→μ≤ μK→Park (stock p R μ ∘ input G n) η C k∧Park (ammo μ ∘ input G n) η C k:=by
    obtain ⟨a,C,ha,hC,h⟩:=H_park G p k hc A
    obtain ⟨B,hB,hL⟩:=mail_p G k a ha.le
    let u:= a/(k+1:ℝ); let t:= u/(k+2:ℝ); have hu:0 < u:=by unfold u; positivity
    have ht:0<t:=by unfold t; positivity
    let L(j:ℕ):=(2:ℝ)^k*‖ContinuousLinearMap.mul ℝ ℝ‖*B*B*((Fintype.card (Loc G j):ℝ)*countCost t); have hx(j):0 ≤ L j:=by unfold L; have hf:= count_pos ht; positivity
    have hp:=hx 1;have hw:=hx 0
    refine ⟨t,C+L 0+L 1+μK^2,ht,by positivity,fun n R D he μ hm hM=>?_⟩
    have hb:u≤a:=div_le_self ha.le (by simp); have hs:t≤u:=div_le_self hu.le (by linarith[Nat.cast_nonneg (α:=ℝ) k]); have hz:=hL n
    have hh:=hz.tiny hb hB le_rfl le_rfl; have hf:=hz.spins ha.le hB
    let F(z):=mail (input G n z); have H:‖μ^2‖ ≤ μK^2:=by rw[Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; gcongr
    have h0:=park_mass G n t _ 0 H k; have h1:= park_mass G n t _ 1 H k
    have he': Park (stock p R μ ∘ input G n) t (C+L 0+μK^2) k:= ((((h n R D he).tiny (hs.trans hb) hC le_rfl le_rfl).plus ((hh.cross_w hf hu hB hB)))|>.plus h1)
    have hi: Park (ammo μ ∘ input G n) t (L 1+μK^2) k:= (hf.cross_w hh hu hB hB)|>.plus h0
    exact ⟨he'.tiny le_rfl (by positivity) (by linarith only[hp]) le_rfl,hi.tiny le_rfl (by positivity) (by linarith only[hw,hC]) le_rfl⟩
variable {B:Bed}
lemma stock_bod (h:M.Bounds p α C D) (ht:Floor B p f a b)(hp:Attached B M)(he:Bid.Sworn B f G): (flare p M (1: Config G f)+ mail (1:Config G f)*(mail (1:Config G f))ᵀ).PosSemidef:=by
    have hh: (flare p M (1:Config G f)).PosSemidef:=by
        apply PosSemidef.of_dotProduct_mulVec_nonneg
        · have hp:= damage_symm (pocket (Lines G f 1)) (F:=burn p M (1: Config G f)) (burn_cov _ h); exact hp
        intro x; rw[star_trivial,flare_matches h ht hp he,bill_pay,dotKin,Work.F03.metric_pair B h hp _ _ ht]; refine Finset.sum_nonneg fun i _=>?_
        rw[real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]; have h:=p.quadratic_pos; positivity
    exact hh.add (posSemidef_self_mul_conjTranspose _)
lemma gapped_z {ι:Type}[Fintype ι][DecidableEq ι]{M:Funds ι}(t: M.PosSemidef)(ht:a≤b): Schur.Gapped (M+b • (1: Funds ι)) a:=by
    intro v; rw[add_mulVec,dotProduct_add,Matrix.smul_mulVec,one_mulVec,dotProduct_smul,smul_eq_mul]; apply le_trans (mul_le_mul_of_nonneg_right ht (Schur.sumSq_nn v)); rw[Schur.sumSq_dot]; exact le_add_of_nonneg_left (by simpa only[star_trivial] using t.dotProduct_mulVec_nonneg v)
lemma hull_m {a':ℝ}(ha:0<a')(hh:a'≤μ) (hc:M.Bounds p α C D)(ht:Floor B p f a b)(hp:Attached B M)(he:Bid.Sworn B f G): (stock p M μ (1:Config G f)).PosDef ∧ Schur.Gapped (stock p M μ (1:Config G f)) (a'^2) ∧ Schur.Gapped (ammo μ (1:Config G f)) (a'^2):=by
    have hμ:= ha.trans_le hh; have hy: a'^2≤ μ^2:= pow_le_pow_left₀ ha.le hh _
    have hp:= stock_bod hc ht hp he; exact ⟨PosDef.posSemidef_add hp (PosDef.one.smul (by positivity)),gapped_z hp hy,gapped_z (tonic_semi _) hy⟩
lemma hull_car (G:Gauge)(p:Clip)(n:ℕ)(h:0<α)(a b μK:ℝ)(hv:0<μ)(C:ℝ):∃ η C',0<η∧0 ≤ C' ∧∀ (f:Side)(M:PathData G)(D:ℝ)(B:Bed), M.Bounds p α C D → Floor B p f a b → Attached B M→ Bid.Sworn B f G →∀ x, μ≤x→ x≤μK →Park (shellB p M x ∘input G f) η C' n∧Park (shellG x ∘ input G f) η C' n:=by
    obtain ⟨a',N,ha,hN,H⟩:= body_charge G p n α h C μK
    obtain ⟨v,D,hp,hD,hB⟩:=Park.inverse_house (n:=n) G 1 ha hN (pow_pos hv 2)
    obtain ⟨w,E,hd,hE,hG⟩:=Park.inverse_house (n:=n) G 0 ha hN (pow_pos hv 2)
    refine ⟨min v w,D+E,lt_min hp hd,by positivity, fun f M Λ B hR hF he hf x h1 h2=>?_⟩
    obtain ⟨hy,hc⟩:= H _ _ _ hR _ (hv.trans_le h1|>.le) h2
    obtain ⟨hv',hh,hu⟩:= hull_m hv h1 hR hF he hf
    let A:=stock p M x ∘ input G f; let L:=ammo x ∘ input G f
    have he:A 0=stock p M x (1:Config G f):=by simp [A];
    have hL: L 0=ammo x (1:Config G f):=by simp [L]
    rw[← he] at hv' hh;rw[← hL] at hu
    have hs: (L 0).PosDef:=ammo_safe _ (hv.trans_le h1)
    have hQ := hB f A hy hv'.det_pos.ne'.isUnit hh (show (A 0).IsSymm from hv'.isHermitian)
    exact ⟨hQ.tiny (min_le_left ..) hD (le_add_of_nonneg_right hE) le_rfl, (hG f L hc hs.det_pos.ne'.isUnit hu hs.isHermitian).tiny (min_le_right ..) hE (le_add_of_nonneg_left hD) le_rfl⟩
end YM.Trace.Det
