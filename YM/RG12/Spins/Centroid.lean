import YM.RG12.Spins.Linette
/-! Abstract sym packing before any diagram cancellations.On
 list/ordered derivatives, not commuting by hand. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Spins
open Function Filter Set Lattice Wilson RG Push.SectorMeasure
open Multi Multi.Vacuum.Jets Multi.Puff WardBin.Lies ProofPorts.CommonComplexProduction.Score
open Pressure PhysicalNext.JointLoad.Heir Next Next.SectorChange AnalyticBridge.LocalGaussian
open Finset MeasureTheory AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussian.Moments AnalyticBridge.SectorAffine.Offset
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{A B:Type}[NormedAddCommGroup A][NormedSpace ℝ A]{c:Side}
variable {m:ℕ}{V:Directions G c→Prop}{M K γ t u R:ℝ}
local notation "e!" => Config G c→ℂ
section
set_option quotPrecheck false
variable (f:A→ℂ){m n:ℕ} (w:A) (curtail : (j:ℕ)→ (Fin j → Directions G c)→Panels j → A)
local notation "N!" => Planned.AtomRegular.patterns n
local notation "w!" k => Noise.half (k w) (k (-w)) - k 0
lemma attend (k:A→e!)(h:R≥0)(ht:0<t)(_hg:0≤ γ)(hm:n+2 ≤ m)(hh:∀ x,‖x‖≤R→ Through m f x M)(hw:‖w‖≤R)(hW:‖w‖≤γ*u)(_hu:0≤u)(hK:1≤K)(he:∀ x,x∈({w,-w,0}: Set A)→Crest n (k x) 1)
   (hφ:∀ j:ℕ,∀ v:Fin j→Directions G c,j ≤ n →(∀ i,V (v i))→
      curtail j v 0=0 ∧ ContDiffAt ℝ j (curtail j v) 0 ∧ (∀ i:ℕ, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i (curtail j v) 0‖ ≤ K*t^i) ∧ ∀ x, x∈({w,-w,0}: Set A) → (k x) ∘ journey 1 j v =ᶠ[𝓝 0] (fun z=> ((t^2)⁻¹:ℝ) • f (curtail j v z+x))) :
   Band n V 1 t (M*(N!)*K^n*((γ*u)^2)/t^2) (w! k):=by
     have hM:= hh _ hw |>.nonneg
     have hp:=he w (by simp); have hs:=he (-w) (by simp); have h0:=he 0 (by simp)
     have hf:Crest n (w! k) 1:=into n _ (((hp.germ.add hs.germ).const_smul (1/2:ℂ)).sub h0.germ)
     refine ⟨hf,ht.le,(by positivity [Planned.AtomRegular.patterns_nonneg n]),fun l hl hv=>?_⟩
     let j:=l.length; let v:=l.get
     obtain ⟨hT,hQ,hB,H⟩ := hφ j v hl (fun i=> hv _ (List.get_mem ..))
     let F (x:A):= iteratedFDeriv ℝ j (f ∘ (fun i=> curtail j v i+x)) 0 cart
     have hx(x:A)(hx:‖x‖≤R)(hP:x∈({w,-w,0}: Set A)):leftDerivs (k x) l 1=(t^2)⁻¹ • F x:=by
        have he0:= Germ.ordered v (f:=k x) (show Germ _ _ 1 from ((he x hP).germ.of_le (Nat.cast_le.mpr hl)))
        unfold v at he0; rw [List.ofFn_get] at he0
        let f₀ := f ∘ (fun z=>curtail j v z+x)
        rw [he0,show iteratedFDeriv ℝ l.length (k x ∘ journey 1 l.length l.get) 0= iteratedFDeriv ℝ j ((t^2)⁻¹ • f₀) 0 from ((H x hP).iteratedFDeriv (𝕜:=ℝ) j).eq_of_nhds, iteratedFDeriv_const_smul_apply ?_]; rfl
        apply ContDiffAt.comp; swap; · exact hQ.add contDiffAt_const
        rw [hT,zero_add]; exact (hh _ hx).smooth.of_le (Nat.cast_le.mpr (hl.trans (by omega)))
     rw [Noise.half,show (1/2:ℂ) • (k w+k (-w))-k 0=(1/2:ℂ) • (k w+k (-w))+(-1:ℂ) • (k 0) from by simp [sub_eq_add_neg], Crest.sum_at l hl _ (into n ((1/2:ℂ) • (k w+k (-w))) ((hp.germ.add hs.germ).const_smul (1/2:ℂ))) ((into n ((-1:ℂ) • k 0) (h0.germ.const_smul (-1:ℂ)))),scaled_left,scaled_left,Crest.sum_at l hl _ hp hs,hx w hw (by simp),hx (-w) (norm_neg w ▸ hw) (by simp),hx 0 (norm_zero.trans_le h) (by simp)]
     have hv':∀ i:Fin j,‖(@cart _ i)‖ ≤ 1:= fun i=> (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j=> by simp only [cart,Pi.single_apply]; split<;> norm_num)
     have hV := drift_skin (Nat.le_trans (Nat.add_le_add_right hl 2) hm) hh hw (curtail j v) hQ hT ht.le hK hB _ hv'
     let N:ℕ:= Fintype.card (OrderedFinpartition j)
     change ‖F w+F (-w)-(2:ℝ) • F 0‖ ≤ 2*M*N*K^j*‖w‖^2*t^j at hV
     rw [show (1/2:ℂ)*((t^2)⁻¹ • F w+(t^2)⁻¹ • F (-w))+ (-1:ℂ)*((t^2)⁻¹ • F 0) = ((t^2*2)⁻¹:ℝ) • (F w+F (-w)-(2:ℝ) • F 0) from ?_, norm_smul,Real.norm_of_nonneg (by positivity)]
     swap; · simp_rw [Complex.real_smul]; push_cast; field_simp
             ring
     apply (mul_le_mul_of_nonneg_left hV (by positivity)).trans; unfold N; field_simp [ht]; unfold j; have hz:= Planned.AtomRegular.card_le_patterns hl
     calc
       _ ≤ M*(N!)*K^n*(γ*u)^2*t^l.length:=by have hpp:= Planned.AtomRegular.patterns_nonneg n; gcongr
       _ = _:=by ring
end
end YM.RG12.Spins
