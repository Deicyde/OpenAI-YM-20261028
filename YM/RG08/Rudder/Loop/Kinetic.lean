import YM.RG08.Rudder.Loop.Shock

/-! Scalar read and subtraction. Normalized relative to WHATEVER supplied H curvature
normalization (commonly 1 in Hessian use, 1/2 under Glyph parley convention in action use).
-/
noncomputable section
namespace YM.RG08.Rudder.Loop
open scoped Topology BigOperators Classical ENNReal InnerProductSpace
open Forms Packets Finset Function Lattice Laurent Pert.Bulk Exterior AnalyticNext.QuarticMatch.BoxChain Symmetry Filter
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
local notation "o"=> (0:Fin 2)
local notation "p"=> (Fin.succ (0:Fin 1))
variable {I:Type} {G:Gauge}{σ τ C B:ℝ}{F F':Raw G.ColorIndex 2}

def AxisK (G:Gauge)(β:ℝ)(i j:Tablet)(x:Tape 2 G.ColorIndex):ℝ:= if i=j∧x o=x p then β else 0
def Core (F: Raw G.ColorIndex 2)(β:ℝ):Prop:=∀ i j:Tablet,i.card=2→j.card=2→∀ y,spectrum F i j y=AxisK G β i j y

def b : Axis:=0
def d : Axis:=1
lemma lit_bd:d≠b:=by decide
private def plane:Tablet:= insert b {d}
lemma plane_card:plane.card=2:=by simp [plane,Ne.symm lit_bd]
private def well (G:Gauge)(hΓ:G.Simple): G.ColorIndex :=
 ⟨0,by
   letI := hΓ.nontrivial_color
   have h:(0:ℕ)<Module.finrank ℝ G.Color:=Module.finrank_pos
   -- G.Color finrank = card LieDim
   simpa [Gauge.Color] using h⟩

def measure (F:Raw G.ColorIndex 2)(hΓ:G.Simple):ℝ:=spectrum F plane plane (fun _=>well G hΓ)

lemma measured (β:ℝ)(hΓ:G.Simple)(H:Core F β):measure F hΓ=β:=by unfold measure; rw [H plane plane plane_card plane_card];exact if_pos ⟨rfl,rfl⟩

lemma bill_meter (hΓ:G.Simple)(hc:0≤C)(hs:0≤σ)(h:Held (carpet (Tone G.ColorIndex)) σ C F):|measure F hΓ|≤C:=spectrum_pence hc hs h _
lemma var_meter (hΓ:G.Simple)(hc:0≤C)(hb:0≤B)(hs:0≤σ)(h:Held (carpet (Tone G.ColorIndex)) σ C F)(H:Held (carpet (Tone G.ColorIndex)) σ B F'):measure (F-F') hΓ=measure F hΓ-measure F' hΓ:=spectrum_minus _ _ hc hb hs h H _
lemma plays (hΓ:G.Simple)(hs:0≤σ)(hc:0≤C)(h:Cloak (Symmetry.dressed G 2) 2 F)(hp:Held (carpet (Tone G.ColorIndex)) σ C F):Core F (measure F hΓ):=by
 obtain ⟨β,hv⟩:=stereo h hΓ hp hs hc plane plane_card
 rw [measured β hΓ hv];exact hv

/-- Compare lifting-independent kinetic orientation by momentum (single diagnostic jet). Can
use on even nonsymmetric U if the responses agree here, once they've appropriate bounds. -/
theorem recognizes (hΓ:G.Simple)(hf:Cohort F)(hf':Cohort F')(hs:0<σ)(hc:0≤C)(ht:0<τ)(hb:0≤B)
    (h:Held (carpet (Tone G.ColorIndex)) σ C F)(h':Held (carpet (Tone G.ColorIndex)) τ B F')(he:picture G.ColorIndex 2 F=picture G.ColorIndex 2 F'):
 measure F hΓ=measure F' hΓ:=by
 have he1:=picture_spark hc hs hf h b d (Ne.symm lit_bd) (fun _=>well G hΓ);have he2:=picture_spark hb ht hf' h' b d (Ne.symm lit_bd) (fun _=>well G hΓ)
 rw [he] at he1;unfold measure plane;linarith

lemma Cloak.smul {G:Gauge}{F:Raw G.ColorIndex 2}(h:Cloak (Symmetry.dressed G 2) 2 F)(a:ℝ): Cloak (Symmetry.dressed G 2) 2 (a • F):=by
 refine ⟨h.path.smul a,fun y i x hh=>?_,h.beam.smul a,fun s=>by rw [map_smul,h.firm s],fun x=> (Symmetry.dressed G 2).smul_mem a (h.hair x)⟩
 change a • hum F y x = 0;rw [h.field' y i x hh,smul_zero]

lemma Cloak.sub (h:Cloak (Symmetry.dressed G 2) 2 F)(H:Cloak (Symmetry.dressed G 2) 2 F'): Cloak (Symmetry.dressed G 2) 2 (F-F'):=by
 refine ⟨h.path.sub H.path, h.field'.sub H.field',?_,fun s=>by rw [map_sub,h.firm s,H.firm s],fun x=> sub_mem (h.hair x) (H.hair x)⟩
 exact fun e=>congrArg₂ (·-·) (h.beam e) (H.beam e)

/- A base carrying any nonzero scalar. Subtract this EACH time after readjusting.
Produces affine-null exact stencil and all-leg equations consume the same base subtraction. -/
def reading (F:Raw G.ColorIndex 2)(hΓ:G.Simple)(s:ℝ):=measure F hΓ/s
def patch (F F':Raw G.ColorIndex 2)(hΓ:G.Simple)(s:ℝ):=F - reading F hΓ s • F'
lemma meter_scale(hΓ:G.Simple)(s:ℝ):measure (s • F) hΓ=s*measure F hΓ:=tsum_mul_left

theorem canal (hΓ:G.Simple)(s:ℝ)(hz:s≠0)(hs:0<σ)(hc:0≤C)(hB:0≤B)(h:Cloak (Symmetry.dressed G 2) 2 F)(h':Cloak (Symmetry.dressed G 2) 2 F') (hf:Held (carpet (Tone G.ColorIndex)) σ C F)(hh:Held (carpet (Tone G.ColorIndex)) σ B F')(H:Core F' s):
 let X:=patch F F' hΓ s
 Cloak (Symmetry.dressed G 2) 2 X ∧ Held (carpet (Tone G.ColorIndex)) σ ((1+B/|s|)*C) X ∧ Core X 0 ∧ picture G.ColorIndex 2 F = picture G.ColorIndex 2 X + reading F hΓ s • picture G.ColorIndex 2 F':=by
 intro X
 let a:=reading F hΓ s;have Hx:X=F-a • F':=rfl
 have he:Held (carpet (Tone G.ColorIndex)) σ (|a| *B) (a • F'):=hh.smul _
 have hp:0≤|a| *B:=by positivity
 have ht:=Cloak.sub h (Cloak.smul h' a)
 have Hm: Held (carpet (Tone G.ColorIndex)) σ (C+|a| *B) X:=hf.sub he hc hp
 refine ⟨ht,Hm.mono le_rfl ?_ (fun _=>le_rfl),?_,?_⟩
 · rw [add_mul,one_mul];apply add_le_add_right
   change |measure F hΓ/s| *B ≤ _;rw [abs_div]; exact (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (bill_meter hΓ hc hs.le hf) (abs_nonneg s)) hB).trans_eq (by ring)
 · convert plays hΓ hs.le (by positivity) ht (Hm) using 1
   rw [var_meter hΓ hc hp hs.le hf he,meter_scale,measured s hΓ H];unfold a reading;field_simp;ring
 · change _=_+a • _;rw [Hx,map_sub,map_smul,sub_add_cancel]
end YM.RG08.Rudder.Loop
