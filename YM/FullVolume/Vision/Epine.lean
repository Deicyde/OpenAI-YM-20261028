import YM.FullVolume.Vision.Garter
/-! Output at equilibrium.FOO formal seed *composition affinity*, including tilt of stationary map. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Change.Reading
open Function Filter Precision Work
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]{n:ℕ}{w:ℝ}
variable {F G Z:X×Y→ℝ} {u v z:X→Y}
lemma ortho {x:X×Y}(h:ContDiffAt ℝ ω F x): F04.vert F =ᶠ[𝓝 x] vert F:=by
    filter_upwards [h.eventually (by simp)] with ⟨i,j⟩ h; exact (F04.hasFDerivAt_slice F i j (h.differentiableAt (by simp))).fderiv.symm
lemma portico (H: Station F u): arrow F ∘ graph u =ᶠ[𝓝 (0:X)] fun x=> (x,0):= H.law.mono fun x hx=> Prod.ext rfl hx
lemma braided [FiniteDimensional ℝ X][FiniteDimensional ℝ Y](hr: Definite F) (h:Knot F G Z 0 (n+1) w)(hf:Station F u)(hg:Station G v)(hw:Station Z z)(he:1≤n):
    Knot (graph u) (graph v) (graph z) 0 n w ∧ Knot (F ∘ graph u) (G∘ graph v) (Z ∘ graph z) 0 (n+1) w:=by
   obtain ⟨hx,hg'⟩:=Change.compare h.equal hf hg hr; obtain ⟨hX,hW⟩:=Change.compare h.credit hf hw hr; have hd:=h.advances
   have hz : Knot (vert F) (vert G) (vert Z) 0 n w:=
     ((Knot.constant (f:= fun v:(X× Y→L[ℝ]ℝ)=> v.comp (ContinuousLinearMap.inr ℝ X Y)) (contDiffAt_id.clm_comp contDiffAt_const)).comp hd he).dawn (ortho h.equal.left) (ortho h.equal.right) (ortho h.credit.right)
   have he' : Knot (arrow F) (arrow G) (arrow Z) (graph u 0) n w := hf.at0.symm ▸ Knot.pairs (Knot.constant contDiffAt_fst) hz
   have hK :Knot (graph u) (graph v) (graph z) 0 n w:=by
       refine ⟨hx,hX,sub_eq_zero.mp ?_⟩
       have ha i := ((portico hf).iteratedFDeriv ℝ i).self_of_nhds
       have ho i := ((portico hg).iteratedFDeriv ℝ i).self_of_nhds
       have hk i := ((portico hw).iteratedFDeriv ℝ i).self_of_nhds
       have hh := easel he' hx hX he; dsimp only [sign] at hh; rw [ha,ho,hk,sub_self, smul_zero,add_zero,sub_self,hf.at0] at hh
       obtain ⟨L,hL⟩:=Definite.equiv hr; rw [hL.fderiv] at hh
       apply ContinuousMultilinearMap.ext; intro v; exact L.injective ((DFunLike.congr_fun hh.symm v).trans (L.map_zero.symm))
   refine ⟨hK,Knot.promotes hg' hW ?_⟩
   have hh : Knot (horz F) (horz G) (horz Z) 0 n w:=
     (Knot.constant (f:= fun v:(X×Y→L[ℝ]ℝ)=> v.comp (ContinuousLinearMap.inl ℝ X Y)) (contDiffAt_id.clm_comp contDiffAt_const)).comp hd he
   rw [← hf.at0] at hh; exact (hh.comp hK he).dawn (hf.horizontal h.equal.left).symm (hg.horizontal h.equal.right).symm (hw.horizontal h.credit.right).symm
end YM.WilsonStartup.Change.Reading
