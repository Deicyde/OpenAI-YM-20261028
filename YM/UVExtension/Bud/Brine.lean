import YM.UVExtension.Tabernacle.Grit
import YM.UVExtension.Copse.Stooks
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Bud
open Function Filter Metric Lattice RG Wilson Finset Relation Push Push.AbsoluteSums Animals Ac Tabernacle Lamppost Concert Oriel Charted Guild
open scoped Topology BigOperators Classical ContDiff
variable {A K X Y D Z ξ R':Type}[NormedAddCommGroup Z][NormedSpace ℂ Z]
variable [NormedAddCommGroup X][NormedSpace ℝ X] [NormedSpace ℂ X][IsScalarTower ℝ ℂ X]
    [AddCommGroup R'][Module ℝ R'] -- add binder
-- data extension. cost per aperture.M dependent root.H.G cost static. Multiply two from separately.
variable (M:Meter A K)(w:R'→ₗ[ℝ] X)
structure Hues (f:R'→ M.Slot) (b:ℝ) : Prop where
   thrives : ∀ i:M.Finger, Charted w (fun u:R'=> ((Meter.Finger.effect M i (f u):ℝ):ℂ)) b
variable (U:Opening D Z) (a:Z→ X)(u:D→ R') (hp:Bumps U.span a)(hq:∀ d,a (U.call d)= w (u d))(he:Set.MapsTo a U.span Grip)
variable {f:R'→ M.Slot}{b:ℝ}(hx : Hues (R':=R') M w f b) (h:Firm w)
include hx h U a hp hq he
lemma cusp: Nonempty (Atlas M U (f∘u) (fun _=>b+b)):=by
   choose F HF Hg H' H using fun i:M.Finger => Oriel.conquest w h (hx.thrives i)
   have hv d i:F i (a (U.call d))=↑(Meter.Finger.effect M i (f (u d))):=by rw [hq,H i]; exact hq d ▸ he (U.within d)
   choose p hP using M.awake
   let g z i k:= F (M.single i k (p i)) (a z)/(↑(M.cost (p i) i):ℂ)
   have ht(d:D)i k:g (U.call d) i k=↑(f (u d) i k):=by unfold g; rw [hv,Meter.sel,Complex.ofReal_mul]; have hh := hP i; exact (div_eq_iff (Complex.ofReal_ne_zero.mpr hh.ne')).mpr (mul_comm ..)
   have hs i:Bumps U.span (fun z=> F i (a z)):=by intro Z t hZ hk h; exact HF i Z _ hZ (he.comp hk) (hp Z _ hZ hk h)
   have hV i k:Bumps U.span (fun z=>g z i k):=fun Z f h hz ht=> (hs _ Z f h hz ht).div_const _
   refine ⟨⟨g,ht,hV,fun z hz=>?_⟩⟩; apply M.c_clips; intro i; suffices H' : Meter.Finger.issue M i (g z)=F i (a z) by rw [H']; exact Hg i _ (he hz)
   exact U.agrees _ _ (M.pollen hV i) (hs i) (fun d=> Eq.symm ((hv d i).trans (M.income i (fun j k=>(ht d j k).symm)))) hz
section
-- receive at M.panel up to real mean probe μ. Radius.SpaceΩ Arbor.Health
variable {R:Type}[AddCommGroup R][Module ℝ R](f:(ℝ × R)→ M.Slot)(W:Fin 4→ ℝ × R)(fc:Arbor→ M.Slot)
omit hx h U a hp hq he
lemma rhomes (hv:∀ i,|(W i).1|≤1) (hF:∀ (t:Fin 4→ℝ) (ht:∀ i,|t i|<radiusU), f (tick W t)= fc (Tabernacle.Rhue (fun i=>(W i).1) t hv ht)) (H:Atlas M lever fc (fun _=>b)) (i:M.Finger):Nonempty (Reel (fun p=> ((Meter.Finger.effect M i (f p):ℝ):ℂ)) b W):=by
    apply Tabernacle.reed W (fun x=> ((Meter.Finger.effect M i (fc x):ℝ):ℂ)) (fun z=> Meter.Finger.issue M i (H.f z)) (M.pollen H.pulse i) (fun z hz=> M.spare (H.bounds z hz) i) _ hv _
    · exact fun x=> (M.income i (fun j k=>(H.exacts x j k).symm)).symm
    intro t ht; rw [hF t ht]
end
end YM.UVExtension.Bud
