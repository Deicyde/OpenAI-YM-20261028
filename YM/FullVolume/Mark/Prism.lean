import YM.FullVolume.Mark.Booths
/-!
# Uniform-on-Gram cylinder calculations
Scale remainder currency according to the rung. Need ℓ¹ not anticipated
projection masks. `PlateXY` statement records even index preimage bounds
and payments of the primitive arrows. A packet reading in `Coin` still
means actual Level marks, not completed approximations. Assumes no finite-rank
property for convolution into real layouts. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Function Filter MeasureTheory Finset Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{Y: Hol G}{n:Side}{S:Desk G n}{v w:ℝ}
namespace Gram
variable {a:ℝ}{Q U R : Gram F Y S a}
lemma widen (h:Within Q U v) (hw: v≤w)(ha:0≤a): Within Q U w:= ⟨h.1.trans hw,fun i=> (h.2 i).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw ha) (Work.G08.size_nonneg ..))⟩
lemma two (Q U :Gram F Y S a) (h:0≤a):Within Q U 2:=by
    have hc(T:Gram F Y S a)(v):‖T.g v‖≤ a * F.coeffSize v:= (T.toll _).trans (mul_le_mul_of_nonneg_left (Work.G08.size_core ..) h)
    exact ⟨zero_le_two,fun v=> (norm_sub_le ..).trans ((add_le_add (hc Q v) (hc U v)).trans_eq (by ring))⟩
lemma Within.trans (ht:Within Q U v)(hw:Within U R w): Within Q R (v+w):=by
    refine ⟨add_nonneg ht.1 hw.1,fun i=>?_⟩; rw [show Q.g i-R.g i= Q.g i-U.g i +(U.g i-R.g i) from by abel]; exact (norm_add_le ..).trans ((add_le_add (ht.2 i) (hw.2 i)).trans_eq (by ring))
lemma Within.flip (h:Within Q U v): Within U Q v:= ⟨h.1,fun i=> (norm_sub_rev ..).trans_le (h.2 i)⟩
-- Generic ledger metrics
abbrev Costed (u v: F.Coeff →ₗ[ℂ] F.Coeff)(c:ℝ) : Prop:=∀ x,F.coeffSize (u x - v x)≤ c * F.coeffSize x
section eval
variable {E:Type}[SeminormedAddCommGroup E][NormedSpace ℂ E]
lemma line (V W:F.Coeff →ₗ[ℂ] E)(x:F.Coeff): V x-W x = ∑ i, x i • (V (Size.axis F i)- W (Size.axis F i)):=by
    simp_rw [smul_sub, sum_sub_distrib,←map_smul, ←map_sum, Size.sum_axes]
lemma scales (V W:F.Coeff →ₗ[ℂ] E)(t:ℝ)(h:∀ i, ‖V (Size.axis F i)-W (Size.axis F i)‖≤t) :∀ x, ‖V x-W x‖ ≤ t*F.coeffSize x:= by
    intro x; rw [line V W x]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=> ‖x i‖*t) ?_).trans_eq ?_)
    · intro i _; rw [norm_smul]; exact mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)
    rw [←sum_mul,mul_comm]; rfl
end eval
lemma booth {c:ℝ} {V W: F.Coeff→ₗ[ℂ] F.Coeff}(h:∀ i,F.coeffSize (V (Size.axis F i)-W (Size.axis F i))≤c): Costed V W c:=by
    intro x; rw [line]; refine (Size.finite ..).trans ((sum_le_sum (g:=fun i=>‖x i‖*c) ?_).trans_eq ?_)
    · intro i _; rw [Size.smul]; exact mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)
    rw [←sum_mul,mul_comm]; rfl
lemma cost_trans {c e:ℝ}{V W Q: F.Coeff→ₗ[ℂ] F.Coeff}(h:Costed V W c)(he:Costed W Q e): Costed V Q (c+e):= by
    intro x; rw [show V x - Q x= V x-W x + (W x-Q x) from by abel]; exact (Size.add ..).trans ((add_le_add (h x) (he x)).trans_eq (by ring))
lemma cost_raise {c e:ℝ}{V W:F.Coeff→ₗ[ℂ] F.Coeff}(h:Costed V W c)(ho:c≤e): Costed V W e:=fun x=> (h x).trans (mul_le_mul_of_nonneg_right ho (Work.G08.size_nonneg ..))
lemma ridge {g:Side}{D:Desk G g}{a b c ℓ :ℝ} (_ha:0<b)(he:0<a)
       (V W:F.Coeff≃ₗ[ℂ]F.Coeff)(T U : F.Coeff→ₗ[ℂ] Coin F Y D)(X Z:Gram F Y D a) (hV:∀ i,F.coeffSize i ≤ b* F.coeffSize (V i))(hx:∀ i,X.g (V i)=T i)(hz:∀ i,Z.g (W i)=U i)(hC:Costed V.toLinearMap W.toLinearMap c)(hT:∀ i, ‖T i-U i‖≤ c * F.coeffSize i) (hc: 0≤ c)(hM:0≤ℓ)(hΩ:(1+a)*c*b≤ ℓ*a): Within X Z ℓ:=by
     refine ⟨hM,fun i=>?_⟩; let k:= V.symm i; have hv : V k=i:=V.apply_symm_apply _
     have hF: F.coeffSize k≤ b*F.coeffSize i:=hv ▸ hV k
     have h₁: ‖X.g i-U k‖ ≤ c*(b* F.coeffSize i):= ((hv ▸ (hx k)) ▸ hT k : ‖X.g i-U k‖ ≤ _)|>.trans (mul_le_mul_of_nonneg_left hF hc)
     have h₂: ‖U k-Z.g i‖ ≤ a*(c*(b*F.coeffSize i)):=by
       rw [← hz,← map_sub]; have h: F.coeffSize (i-W k)≤ c*F.coeffSize k:=(by rw [← hv]; exact hC k)
       rw [Work.G08.size_sub_rev] at h; exact (Z.toll _).trans (mul_le_mul_of_nonneg_left ((Work.G08.size_core ..).trans (h.trans (mul_le_mul_of_nonneg_left hF hc))) he.le)
     rw [show X.g i-Z.g i=X.g i-U k+(U k-Z.g i) from by abel]; exact (norm_add_le ..).trans ((add_le_add h₁ h₂).trans ((by ring : _=(1+a)*c*b*F.coeffSize i).trans_le (mul_le_mul_of_nonneg_right hΩ (Work.G08.size_nonneg ..))))
variable {E:Type}[SeminormedAddCommGroup E][NormedSpace ℂ E]
lemma rcost {V W: ℕ→ F.Coeff≃ₗ[ℂ] F.Coeff}(h:∀ x, Tendsto (fun n=> V n x-W n x) atTop (𝓝 0))(c:ℝ) (hc:0<c): ∀ᶠ n in atTop,Costed (V n).toLinearMap (W n).toLinearMap c:=by
    let p i n:= F.coeffSize (V n (Size.axis F i)- W n (Size.axis F i)); have hh(i):Tendsto (p i) atTop (𝓝 0):= by
       rw [← show F.coeffSize 0=0 from (by simp [Frame.coeffSize])]; exact (Size.continuous F|>.continuousAt).tendsto.comp (h _)
    filter_upwards [eventually_all.mpr fun i=> (hh i).eventually (ge_mem_nhds hc)] with n hn; exact booth hn
lemma rnorm {V W:ℕ→ F.Coeff →ₗ[ℂ] E}(h:∀ x,Tendsto (fun n=> V n x-W n x) atTop (𝓝 0)) (c:ℝ) (hc:0<c): ∀ᶠ n in atTop, ∀ x, ‖V n x-W n x‖≤ c* F.coeffSize x:=by
    let p i n:=‖V n (Size.axis F i)- W n (Size.axis F i)‖; have he i:Tendsto (p i) atTop (𝓝 0):=by simpa only [p,norm_zero] using (h (Size.axis F i)).norm
    filter_upwards [eventually_all.mpr fun i=> (he i).eventually (ge_mem_nhds hc)] with n hn; exact scales _ _ c hn
end Gram
end YM.MergeProof.Matric
#print axioms YM.MergeProof.Matric.Gram.ridge
#print axioms YM.MergeProof.Matric.Gram.rcost
#print axioms YM.MergeProof.Matric.Gram.rnorm
