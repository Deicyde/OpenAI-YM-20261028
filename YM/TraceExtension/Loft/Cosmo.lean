import YM.TraceExtension.Loft.Store
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience
open scoped BigOperators Topology ContDiff ComplexConjugate
section stars
variable {ι : Type} {G:Gauge}{r:ℝ}{T μ:ι→ℝ}
variable {X : Burst ι (Fslot G)} {F : KPath ι (Fslot G) (Fslot G) (Fslot G)}
abbrev Otway (G : Gauge) (μ : ι→ℝ) : KPath ι (Fslot G) (Foot G) (Foot G) := fun i=>icing (Foot G) _ (μ i)
abbrev Lensig (G : Gauge) (μ : ι→ℝ) : KPath ι (Fslot G) (Fslot G) (Fslot G) := fun i=>icing (Fslot G) _ (μ i)
structure Yeti (X : Burst ι (Fslot G)) (T μ : ι→ℝ) (F : ι→KindF G) (r : ℝ) (b : ι→ G.ColorIndex) : Prop where
    first : Fleet X T μ (fun i=>granary G (F i)) (Lensig G μ) (herr (G:=G)) r
    spare : Fleet X T μ (fun _=>quarry G) (Otway G μ) (hurr (G:=G)) r
    desires i : X.mark i=(coord 1,b i)
    upright i : X.boost i=step 0
variable {b : ι→G.ColorIndex} (h : Yeti X T μ F r b)
def Yeti.bait (G : Gauge) (F : ι→ KindF G) (μ : ι→ℝ) (i) := quick (μ i) G (F i)
include h
lemma Yeti.coin (i) : keelRay (Yeti.bait G F μ i) (b i) (X.lens i)= (1/2:ℂ)*((1/2:ℂ)*flareY 2 (rod X (fun i=> alp G (μ i) (F i)) i)-flareY 2 (rod X (fun i=>cinder G (μ i)) i)) := by
  let V i := alp G (μ i) (F i); let Y i := cinder G (μ i)
  let f := rod X V i; let g := rod X Y i; let c := (1/2:ℂ)
  have hf : AnalyticAt ℝ f 0 := rod_diff h.first _; have hg : AnalyticAt ℝ g 0 := rod_diff h.spare _
  unfold keelRay strolls; rw [show (fun t:ℝ=>Yeti.bait G F μ i (coord 1,b i) (coord 1,b i) (axes (t • step 0)) (axes (X.lens i)))=(fun t=> c*f t)-g from funext (fun t=> by
    unfold f g rod springM c V Y; rw [h.upright,h.desires]; simp only [bait,quick,Pi.sub_apply,Pi.smul_apply,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,smul_eq_mul]), flare_dec (x:=fun t => c*f t) (analyticAt_const.mul hf) hg, flare_scale hf c]

lemma Yeti.register : ∃ A : ℝ,0≤A ∧ ∀ i, ‖keelRay (Yeti.bait G F μ i) (b i) (X.lens i)‖≤ A/T i^4 := by
  obtain ⟨A,hA,h1⟩ := rod_bill h.first; obtain ⟨B,hB,h2⟩ := rod_bill h.spare
  let c := (1/2:ℂ); have ht (x : ℂ) : ‖c*x‖≤ ‖x‖ := by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (by unfold c; norm_num)
  refine ⟨A+B,by positivity,fun i=> ?_⟩; rw [h.coin i]
  exact (ht _).trans ((norm_sub_le ..).trans ((add_le_add ((ht _).trans (h1 i)) (h2 i)).trans_eq (by ring)))
lemma Yeti.shell (hG : G.Simple) (he : T=flay ∘ X.lens) (hr : 0≤r) :
    ∃ A : ℝ,0≤A ∧ ∀ i, ‖keelRay (Yeti.bait G F μ i) (b i) (X.lens i)- ↑(poleVec G (X.lens i))‖≤ A/ T i^3+ A*μ i^2/T i^6 := by
  obtain ⟨A,hA,hL⟩ := h.first.haloControl he; obtain ⟨B,hB,hG'⟩ := h.spare.haloControl he
  obtain ⟨u,v,hU,hV,f⟩ := h.first.tadControl; obtain ⟨x,y,hX,hY,g⟩ := h.spare.tadControl
  let P := max (u*r+x*r + A+B) (A+B+v+y)
  have hP : 0≤ P := (show 0≤u*r+x*r+A+B by positivity).trans (le_max_left ..)
  refine ⟨P,hP,fun i=>?_⟩
  let J := X.lens i; let V := atopY (fun i=>granary G (F i)) (Lensig G μ); let W:=atopY (fun _=>quarry G) (Otway G μ)
  let t := upperJet X V; let j := upperJet X W
  let L := lowerJet X V; let M := lowerJet X W
  let V' := haloC X (herr (G:=G)); let T' := haloC X (hurr (G:=G))
  let d := flareY 2 (fun z=> trace (L i z)); let c := flareY 2 (fun z=> trace (M i z)); let d' := flareY 2 (fun z=> trace (V' i z)); let c' := flareY 2 (fun z=> trace (T' i z))
  let D := flareY 2 (fun z=> trace (t i z)); let Y := flareY 2 (fun z=>trace (j i z))
  let a := T i; let w := μ i; let C := (1/2:ℂ)
  have hk : 0<a := h.first.2.2.2.lower _; have hp : a=flay J:=congr_fun he i
  have he : keelRay (Yeti.bait G F μ i) (b i) (X.lens i)-(poleVec G (X.lens i):ℂ) = C*(C*D-Y)+C*((c-c')- C*(d-d')) := by
    rw [h.coin]; change C*(C*flareY 2 (rod X V i)-flareY 2 (rod X W i))- _=_
    have ht : c' - C*d'= (2:ℂ)*(poleVec G J:ℂ) := haloRate (b i) hG i (hk.trans_eq hp) (h.upright i) (h.desires i)
    rw [show flareY 2 (rod X V i)=D-d from rod_plucked h.first i,show flareY 2 (rod X W i)= Y-c from rod_plucked h.spare i,show (poleVec G (X.lens i):ℂ)= C*(c'-C*d') from (by rw [ht]; unfold C J; ring)]
    unfold C; ring
  rw [he]; have ht (x : ℂ) : ‖C*x‖≤ ‖x‖ := by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (by unfold C; norm_num)
  let Q:= rimEdge T μ i
  have hl' : ‖C*D-Y‖≤ (u/a^2+ v*w^2/a^6) + (x/a^2 +y*w^2/a^6) := (norm_sub_le ..).trans (add_le_add ((ht _).trans (f i)) (g i))
  have hx' : ‖(c-c')-C*(d-d')‖ ≤ B*Q/a^4+A*Q/a^4 := (norm_sub_le ..).trans (add_le_add (hG' i) ((ht _).trans (hL i)))
  refine (norm_add_le ..).trans ((add_le_add ((ht _).trans hl') ((ht _).trans hx')).trans ?_)
  have hh : a≤r := h.first.2.2.2.upper _
  change _ ≤ P/a^3+P*w^2/a^6; calc
   _ = (u*a+x*a+A+B)/a^3+(A+B+v+y)*w^2/a^6 := by
     change _ + (B*(a+w^2*(a^2)⁻¹)/a^4+A*(a+w^2*(a^2)⁻¹)/a^4)=_; field_simp; ring
   _ ≤ _ := by
     have hx : u*a+x*a+A+B ≤ P := (show u*a+x*a+A+B ≤ u*r+x*r+A+B by nlinarith [mul_le_mul_of_nonneg_left hh hU,mul_le_mul_of_nonneg_left hh hX]).trans (le_max_left ..)
     apply add_le_add (div_le_div_of_nonneg_right hx (by positivity)); gcongr; exact le_max_right ..
end stars

end YM.Trace.Loft
