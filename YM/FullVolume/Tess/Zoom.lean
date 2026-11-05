import YM.FullVolume.Fares.Scrap
import YM.FullVolume.Dusk.Real
import YM.FullVolume.Tess.Pier
/-
 A real arc.Census preserving leases.W. Ambient in real diameter,
 extension reparam via dilation on chords. Radius here p only; eventually fine for fields.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp
open Function Filter Set MeasureTheory Lattice RG Ray Push.AbsoluteSums
open PhysicalNext.Repeat.Muse
open scoped Topology BigOperators NNReal Classical Matrix.Norms.Frobenius ContDiff
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X]
namespace Beam
abbrev scaleSun (v:sun) (s:sun):sun:= slash v.val v.property s
abbrev noon :sun := ⟨1,⟨by norm_num,le_rfl⟩⟩
lemma px (x y z:sun):scaleSun x (scaleSun y z)= scaleSun (scaleSun y x) z:=by ext; change (_*_)*_=_*(_*_); ring
lemma unitP (x:sun): scaleSun noon x=x:= Subtype.ext (mul_one _)
lemma incline (v:sun):Continuous fun X:Beam X=> fit v X:=by
    refine (LipschitzWith.of_dist_le_mul (K:=(1:ℝ≥0)) fun x y=>?_).continuous; rw [dist_eq_norm,← fitD,dist_eq_norm]; simpa using fitN v (x-y)
variable {P:ℕ→Beam X}{C:ℝ}
private lemma basic (v:sun)(hx:|v.val|<1) (p:ℕ→ Beam X)(h:∀ i, ‖p i‖≤C) (U:Beam X)(hU:‖U‖≤ C)(hP:∀ k,Tendsto (fun i=>p i k) atTop (𝓝 (U k))): Tendsto (fun i=>fit v (p i)) atTop (𝓝 (fit v U)):=by
   rw [tendsto_iff_norm_sub_tendsto_zero]; let B(i):= p i-U; let z(i k:ℕ):= ‖fit v (B i) k‖
   have hv(i:ℕ):‖fit v (p i)-fit v U‖=∑' k,z i k:=by rw [← fitD]; exact (paid (fit v (B i))).tsum_eq.symm
   have hw(k:ℕ):Tendsto (fun i=> z i k) atTop (𝓝 0):=by
       unfold z; simp_rw [lawn]; have htB : Tendsto (fun i=> B i k) atTop (𝓝 0):=by simpa only [sub_self] using! (hP k).sub_const (U k)
       simpa using (htB.norm.const_mul (|v.val|^k))
   have hi(i k:ℕ) : ‖z i k‖ ≤ |v.val|^k*(C+C):=by
       unfold z; rw [norm_norm,lawn]; refine mul_le_mul_of_nonneg_left ((budget_single (togg _) k).trans ?_) (pow_nonneg (abs_nonneg _) _); exact (norm_sub_le ..).trans (add_le_add (h i) hU)
   have hz:= tendsto_tsum_of_dominated_convergence ((summable_geometric_of_lt_one (abs_nonneg _) hx).mul_right (C+C)) hw (Eventually.of_forall hi)
   simpa only [tsum_zero, ← hv] using hz
lemma damp (v:sun) (hx:|v.val|<1)(h:∀ᶠ i in atTop, ‖P i‖ ≤ C)(Y:Beam X)(ht:∀ s:sun,Tendsto (fun i=> read X s (P i)) atTop (𝓝 (read X s Y))): Tendsto (fun i=> fit v (P i)) atTop (𝓝 (fit v Y)):=by
   obtain ⟨n,hN⟩:=eventually_atTop.mp h; apply PhysicalNext.Repeat.Lark.Pith.high n; let p(i:ℕ):=P (i+n); have h(i:ℕ):‖p i‖≤ C:=hN _ (by omega)
   have hs s:Tendsto (fun i=>read X s (p i)) atTop (𝓝 (read X s Y)):= by have hx:= (ht s).comp (tendsto_add_atTop_nat n); exact hx
   obtain ⟨U,hU,hP⟩:= issueR h fun i=> ⟨_, hs i⟩
   have ht(s:sun): Tendsto (fun i=>fit v (p i)|> read X s) atTop (𝓝 (read X s (fit v Y))):= by simp_rw [fitL]; exact hs (scaleSun v s)
   suffices H:Tendsto (fun i=>fit v (p i)) atTop (𝓝 (fit v U)) by
      suffices hh: fit v U=fit v Y by exact hh ▸ H
      exact soul (fit v U) _ (fun s=> tendsto_nhds_unique (((read X s).continuous.continuousAt.tendsto).comp H) (ht s))
   exact basic v hx p h U hU hP
-- variant Cauchy only
lemma dampBound {v:sun} (hx:|v.val| <1)(h:∀ᶠ i in atTop, ‖P i‖≤ C)(hp:∀ s:sun, CauchySeq (fun i=> read X s (P i))): CauchySeq (fun i=> fit v (P i)):=by
    obtain ⟨n,hN⟩:=eventually_atTop.mp h; let p(i:ℕ):=P (i+n); have h'(i:ℕ): ‖p i‖≤ C:= hN _ (by omega)
    choose U hU using fun s: sun=> cauchySeq_tendsto_of_complete (hp s)
    have hP' s:Tendsto (fun i=> read X s (p i)) atTop (𝓝 (U s)):=by have hp:=(hU s).comp (tendsto_add_atTop_nat n); exact hp
    obtain ⟨Y,hY,hT⟩:= issueR h' fun i=> ⟨_, hP' i⟩
    exact Tendsto.cauchySeq (show Tendsto _ atTop (𝓝 (fit v Y)) from (PhysicalNext.Repeat.Lark.Pith.high n (basic v hx p h' Y hY hT)))
end Beam
end YM.FullVolume.Amp
