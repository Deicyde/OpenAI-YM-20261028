import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Folio
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Weave
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Path
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Novas
/-! # PPX support exact: actual normalized V9 affine route on view=edge.TH, q `tape` test with nonlinear increment. Not identifying elsewhere on larger masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Function Filter Set Lattice Wilson RG Pressure Precision Labels Source Source.Drops
open Push Push.Local Planned.PrimaryIntegral295 PPX Flutes Place Bazaars Exterior Streets Postcards WardBin.Lies Cabins Bid
open Tree Next.Free Matrix Bloch Next Next.Foundations JointLoad JointLoad.Heir
open UVNext.PricedKernels MultiNext.SignedSource Next.Fluctuations Next.SectorChange
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f} {F:Forest S.ratio}{T:Tube G S}{P B:BudgetPoint}{x u t:ℝ} {n j d:ℕ}
variable {v: Probe G d}{A:Hol G}
-- True linear comparison.Volume.Stroke evaluated PERIODIC. Charges after.
section lines
variable {r:ℕ}
lemma shading (o:Site c)(R:ℕ)(V:Config G c) : Heir.crop o R (1:Site c→G.El) V = fun i=> if separation o i.1 ≤ R then G.plog (G.mat (V i)) else 0:= by funext i; unfold Heir.crop; simp [Lattice.gauge]
lemma stole {p:Probe G d}(t c':ℝ)(h:0<t)(x:ℝ) : Heir.crop 0 r (1:Site c→G.El) (Flutes.fare p A c c' x)= t • collect G (Flutes.lode p A c c' t r x):=by
    ext1 i; rw [shading, Pi.smul_apply]; unfold collect; let V:= Flutes.fare p A c c'
    change _ = t • Flutes.lode p A c c' t r x (Work.E03.poleEquiv c i);
    unfold Flutes.lode; rw [Cabins.symbolic, Cabins.room]; by_cases hh: separation 0 i.1≤r
    · simp only [if_pos hh,smul_inv_smul₀ h.ne']; simp [Lattice.gauge]
    simp only [if_neg hh,smul_zero]
-- linear maps confirmation strong exact route. no monitor. 
lemma walked (v:Streets.Dir G c) : Heir.route T (collect G v)= Streets.tapes S T.R.A0 v:=by
   funext e; ext i; change (_ *ᵥ parts G 1 (Flat.labels (collect G v)) i) (e.1,Exterior.coord e.2)  = pledge (installed S.ratio T.R.A0) v (e.1,Exterior.coord e.2) i
   rw [Streets.code]; have he: Flat.labels (collect G v)=v:=by funext i; unfold Flat.labels collect; apply congr_arg v; exact Prod.ext rfl (axisEquiv.apply_symm_apply i.2)
   rw [he]; rfl

variable {F₁: Labels.Frame G d}(F:SectionData F₁)
-- Fine forecast estimate since linear normalized input.Fit.Map.Teller
-- general complex deem
abbrev ocean (T:Tube G S)(f':Config G f→ℂ)(x:ℝ): Config G c → ℂ:=fun U=> f' (increment 1 (Heir.route T (Heir.crop (S.ratio.parent (0:Site f)) (reach x) 1 U)))
lemma terra (t c':ℝ)(h:0<t)(x:ℝ)(A:Hol G)(p:Probe G d)(i:F₁.Index) : ocean T (Local.presented F (0:Site f) t (Place.copy F₁ i)) x ∘ Flutes.fare p A c c' =
    Tones.tint F i t ∘ ((Bazaars.earth F.stencil S T.R.A0) ∘ Flutes.lode p A c c' t (reach x)):=by
   have he : F₁.scaled t⁻¹ (Place.copy F₁ i)= (((t^(F₁.grades i).2)⁻¹:ℝ):ℂ) • Place.copy F₁ i:=by
       ext1 j; by_cases h:j=i <;> simp [h,Place.copy]
   have hv (V:Config G f): Local.presented F (0:Site f) t (copy F₁ i) V= (t^(F₁.grades i).2)⁻¹ • F.places (copy F₁ i) 0 V:=by
       unfold Local.presented; change F.places _ _ _= _; rw [he]; unfold SectionData.places SectionData.evaluate; rw [map_smul,map_smul]; exact (Complex.real_smul ..).symm
   funext y; let X:= Flutes.lode p A c c' t (reach x) y; let W:= Streets.tapes S T.R.A0 X
   have h0:S.ratio.parent (0:Site f)=0:=by let g:=S.ratio; change g.parent 0=0; rw [← g.root.map_zero]; exact g.embed_parent _
   change Local.presented _ _ _ _ _=(t^(F₁.grades i).2)⁻¹ • Place.column F i (t • earth F.stencil S _ X)
   rw [hv,h0,stole _ _ h y,map_smul,walked]; refine congr_arg ((t^ (F₁.grades i).2)⁻¹ • ·) (F.cylinder_local _ _ _ ?_)
   intro e hi hj; unfold pore; split; swap; · next hh =>exact (hh ⟨hi,hj⟩).elim
   change increment 1 (t • W) _ = G.lieExp (t • W _); unfold increment; simp; rfl
end lines
end YM.PhysicalNext.Repeat.Cub
